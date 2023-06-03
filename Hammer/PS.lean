-- Author: Alistair Geesing

import Lean

import Hammer.PS.PState

import Hammer.PS.Common
import Hammer.PS.MePo
import Hammer.PS.MaSh.Common
import Hammer.PS.MaSh.NB
import Hammer.PS.MaSh.KNN
import Hammer.PS.MeSh

namespace Hammer.PS

open Lean
open Lean.Elab.Command
open Lean.Elab.Tactic
open Lean.Elab.Term

open Hammer.PS.MaSh
open Hammer.PS.MeSh


def getPStateDir : IO System.FilePath :=
  return (←IO.currentDir) / "build"

def getPStatePath : IO System.FilePath :=
  return (←getPStateDir) / "Hammer.PS.PState.olean"

def getPStatePathLock : IO System.FilePath :=
  return (←getPStateDir) / "Hammer.PS.PState.olean.locked"


-- no references to objects in PState may be alive when this function returns
unsafe def withPState {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadFinally m] (f : PState → m α) : m α := do
  let pstatePath ← getPStatePath

  let (pstate, pstateCompactedRegion?) ←
    if ←pstatePath.pathExists then
      match ←readPState pstatePath with
      | .ok (pstate, pstateCompactedRegion) => pure (pstate, some pstateCompactedRegion)
      | .error .toolchainVersionChanged => pure (∅, none)
      | .error .pstateVersionChanged => pure (∅, none)
    else
      pure (∅, none)

  try f pstate
  finally
    if let some pstateCompactedRegion := pstateCompactedRegion? then
      pstateCompactedRegion.free


-- no references to objects in PState may be alive when this function returns
unsafe def tryWithLockedPState (f : PState → IO PUnit) : IO Bool := do
  try
    let pstatePathLock ← getPStatePathLock

    IO.FS.createDir pstatePathLock

    try withPState f
    finally IO.FS.removeDir pstatePathLock

    return true
  catch _ =>
    return false

unsafe def learnImportsOf (env : Environment) : IO PUnit := do
  -- don't care if we couldn't lock, user will eventually try again
  let _ ← tryWithLockedPState λpstate => do
    let imports := env.header.imports
      |>.foldl (λimports importt => imports.insert importt.module) (∅ : NameSet)

    let ((didUpdate, pstate), _) ←
      PStateM.updateImports imports
        |>.run pstate
        |>.run' default
        |>.run'
        |>.toIO
          {
            fileName := "<anonymous>"
            fileMap := FileMap.mk "" #[] #[]
            maxHeartbeats := 9999999999999999999
          }
          { env }

    if didUpdate then
      IO.FS.createDirAll (←getPStateDir)
      savePState (←getPStatePath) pstate

initialize learningEnvs : IO.Channel Environment ← IO.Channel.new
initialize learningExceptions : IO.Mutex (Array IO.Error) ← IO.Mutex.new ∅

unsafe def unsafeLearningTaskAct' : IO PUnit := do
  for env in learningEnvs.sync do
    learnImportsOf env
    env.freeRegions

@[implemented_by unsafeLearningTaskAct']
opaque learningTaskAct' : IO PUnit

def learningTaskAct : BaseIO PUnit := do
  while True do
    if let .error e ← learningTaskAct'.toBaseIO then
      learningExceptions.atomically do
        modify (Array.push . e)

initialize learningTask? : IO.Mutex (Option (Task PUnit)) ← IO.Mutex.new none

def ensureLearningTaskIsSpawned : IO PUnit := do
  learningTask?.atomically do
    if let none ← get then
      set $ some $ ←BaseIO.asTask learningTaskAct


def factIdxToConstant (pstate : PState) (factIdx : UInt64) : MetaM (Option ConstantInfo) :=
  return (←getEnv).find? pstate.factNames[factIdx.toNat]!

def suggestionToConstant (pstate : PState) : (UInt64 × Float) → TacticM (Option (ConstantInfo × Float))
| (factIdx, score) => do
  match ←factIdxToConstant pstate factIdx with
  | some c => return (c, score)
  | none => return none

unsafe def unsafeGetSuggestions (x : PState → Array UInt64 → TacticM (Array (UInt64 × Float))) : TacticM (Option (Array (ConstantInfo × Float)) ):= do
  ensureLearningTaskIsSpawned

  let backgroundExceptions ← learningExceptions.atomically $ modifyGet λes => (es, ∅)
  for e in backgroundExceptions do
    logWarning m!"An exception occurred during background learning: {e}"

  withPState λpstate => do
    let imports := (←getEnv).header.imports

    if ←pstate.haveModifiedImports imports then
      logInfo m!"Learning new facts in the background... This may take a while depending on how many modules have changed. Try again in a bit"
      learningEnvs.send $ ←importModules imports.toList .empty
      return none

    let constants := (←getEnv).constants.map₂.foldl (λconstants _ c => constants.push c) ∅
  
    let (pstate, mainModuleIdx) ← pstate.updateMainModule (←getMainModule) imports constants
    let candidateFacts := pstate.candidateFacts mainModuleIdx

    let suggestions ← x pstate candidateFacts
    let suggestions ← suggestions.filterMapM (suggestionToConstant pstate)
    return suggestions

@[implemented_by unsafeGetSuggestions]
opaque getSuggestions : (PState → Array UInt64 → TacticM (Array (UInt64 × Float))) → TacticM (Option (Array (ConstantInfo × Float)))


def getGoalSymbols (pstate : PState) : TacticM (Array UInt64) := do
  let goalSymbols ← getFactSymbols' (←getMainModule) (←getDeclName?) (←getMainTarget)
  let goalSymbols ← (←getMCtx).decls.foldlM
    (λgoalSymbols _ mdecl => return (←getFactSymbols' (←getMainModule) (←getDeclName?) mdecl.type).fold .insert goalSymbols)
    goalSymbols

  return goalSymbols.fold
    (λgoalSymbols goalSymbol => match pstate.symbolIdxs.find? goalSymbol with
      | some symbolIdx => goalSymbols.push symbolIdx
      | none => goalSymbols)
    ∅

def getGoalFeatures (pstate : PState) : TacticM (Array UInt64) := do
  let goalFeatures ← MaSh.getFactFeatures' (←getMainModule) (←getDeclName?) (←getMainTarget)
  let goalFeatures ← (←getMCtx).decls.foldlM
    (λgoalFeatures _ mdecl => return (goalFeatures.insertMany
      $ ←getFactFeatures' (←getMainModule) (←getDeclName?) mdecl.type))
    goalFeatures

  return goalFeatures.fold
    (λgoalFeatures goalFeature => match pstate.featureIdxs.find? goalFeature with
      | some featureIdx => goalFeatures.push featureIdx
      | none => goalFeatures)
    ∅

def maxFacts : UInt64 := 1024


def getMePoSuggestions'' (pstate : PState) (candidateFacts : Array UInt64) (goalSymbols : Array UInt64) : IO (Array (UInt64 × Float)) := do
  let ctx := {
    maxFacts
    pstate
  }
  let state := MePo.initState ctx candidateFacts goalSymbols
  MePo.mepo ctx |>.run' state

def getMePoSuggestions' (pstate : PState) (candidateFacts : Array UInt64) : TacticM (Array (UInt64 × Float)) := do
  getMePoSuggestions'' pstate candidateFacts (←getGoalSymbols pstate)

def getMePoSuggestions : TacticM (Option (Array (ConstantInfo × Float))) :=
  getSuggestions getMePoSuggestions'

elab "mepo" : tactic => do
  if let some suggestions ← getMePoSuggestions then
    for (suggestion, score) in suggestions do
      logInfo m!"{suggestion.name}: {score}"


def getMaShNBSuggestions'' (pstate : PState) (candidateFacts : Array UInt64) (goalFeatures : Array UInt64) : IO (Array (UInt64 × Float)) := do
  let ctx := {
    maxFacts

    pstate

    candidateFacts
    goalFeatures
  }
  MaSh.NB.naiveBayes ctx

def getMaShNBSuggestions' (pstate : PState) (candidateFacts : Array UInt64) : TacticM (Array (UInt64 × Float)) := do
  getMaShNBSuggestions'' pstate candidateFacts (←getGoalFeatures pstate)

def getMaShNBSuggestions : TacticM (Option (Array (ConstantInfo × Float))) :=
  getSuggestions getMaShNBSuggestions'

elab "mashnb" : tactic => do
  if let some suggestions ← getMaShNBSuggestions then
    for (suggestion, score) in suggestions do
      logInfo m!"{suggestion.name}: {score}"


def getMaShKNNSuggestions'' (pstate : PState) (candidateFacts : Array UInt64) (goalFeatures : Array UInt64) : IO (Array (UInt64 × Float)) := do
  let ctx := {
    maxFacts

    pstate

    candidateFacts
    goalFeatures
  }
  let state := MaSh.KNN.initState ctx
  MaSh.KNN.kNN ctx |>.run' state

def getMaShKNNSuggestions' (pstate : PState) (candidateFacts : Array UInt64) : TacticM (Array (UInt64 × Float)) := do
  getMaShKNNSuggestions'' pstate candidateFacts (←getGoalFeatures pstate)

def getMaShKNNSuggestions : TacticM (Option (Array (ConstantInfo × Float))) :=
  getSuggestions getMaShKNNSuggestions'

elab "mashknn" : tactic => do
  if let some suggestions ← getMaShKNNSuggestions then
    for (suggestion, score) in suggestions do
      logInfo m!"{suggestion.name}: {score}"


def getMeShSuggestions : TacticM (Option (Array (ConstantInfo × Float))) :=
  getSuggestions λpstate candidateFacts => do
    let goalSymbols ← getGoalSymbols pstate
    let goalFeatures ← getGoalFeatures pstate

    let mepoSuggestions ← IO.asTask $ getMePoSuggestions'' pstate candidateFacts goalSymbols
    let nbSuggestions ← IO.asTask $ getMaShNBSuggestions'' pstate candidateFacts goalFeatures
    let knnSuggestions ← IO.asTask $ getMaShKNNSuggestions'' pstate candidateFacts goalFeatures

    let mepoSuggestions ← ofExcept mepoSuggestions.get
    let nbSuggestions ← ofExcept nbSuggestions.get
    let knnSuggestions ← ofExcept knnSuggestions.get

    return mesh maxFacts [
      (0.5, mepoSuggestions),
      (0.5, mesh maxFacts [
        (0.5, nbSuggestions),
        (0.5, knnSuggestions)
      ])
    ]

elab "mesh" : tactic => do
  if let some suggestions ← getMeShSuggestions then
    for (suggestion, score) in suggestions do
      logInfo m!"{suggestion.name}: {score}"
