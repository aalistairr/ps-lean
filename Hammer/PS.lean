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


def withMaxHeartbeats (maxHeartbeats : Nat) (x : CommandElabM α) : CommandElabM α := do
  let oldMaxHeartbeats := (←getOptions).getNat `maxHearbeats
  let options := (←getOptions).setNat `maxHeartbeats maxHeartbeats
  modifyScope fun scope => { scope with opts := options }
  let a ← x
  let options := (←getOptions).setNat `maxHeartbeats oldMaxHeartbeats
  modifyScope fun scope => { scope with opts := options }
  return a


def getPStateDir : IO System.FilePath :=
  return (←IO.currentDir) / "build"

def getPStatePath : IO System.FilePath :=
  return (←getPStateDir) / "Hammer.PS.PState.olean"



unsafe def unsafeLearnCommand : CommandElabM PUnit := do
  withMaxHeartbeats 999999999999999 do
    let pstatePath ← getPStatePath

    let (pstate, pstateCompactedRegion?) ←
      if ←pstatePath.pathExists then
        match ←readPState pstatePath with
        | .ok (pstate, pstateCompactedRegion) => pure (pstate, some pstateCompactedRegion)
        | .error .toolchainVersionChanged => pure (∅, none)
        | .error .pstateVersionChanged => pure (∅, none)
      else
        pure (∅, none)

    let imports := (←getEnv).header.imports
      |>.foldl (λimports importt => imports.insert importt.module) (∅ : NameSet)
  
    let (didUpdate, pstate) ← liftCoreM $
      PStateM.updateImports imports
        |>.run pstate
        |>.run' default
        |>.run'

    if didUpdate then
      IO.FS.createDirAll (←getPStateDir)
      savePState (←getPStatePath) pstate

    -- no references to objects in pstate must be used beyond this point
    if let some pstateCompactedRegion := pstateCompactedRegion? then
      pstateCompactedRegion.free

@[implemented_by unsafeLearnCommand]
opaque learnCommand : CommandElabM PUnit

elab "Hammer.PS.learn" : command => learnCommand


elab "Hammer.PS.reset" : command => do
  resetPState (←getPStatePath)


def factIdxToConstant (pstate : PState) (factIdx : UInt64) : MetaM (Option ConstantInfo) :=
  return (←getEnv).find? pstate.factNames[factIdx.toNat]!

def suggestionToConstant (pstate : PState) : (UInt64 × Float) → TacticM (Option (ConstantInfo × Float))
| (factIdx, score) => do
  match ←factIdxToConstant pstate factIdx with
  | some c => return (c, score)
  | none => return none

unsafe def unsafeGetSuggestions (x : PState → Array UInt64 → TacticM (Array (UInt64 × Float))) : TacticM (Array (ConstantInfo × Float)) := do
  let pstatePath ← getPStatePath

  let (pstate, pstateCompactedRegion?) ←
    if ←pstatePath.pathExists then
      match ←readPState pstatePath with
      | .ok (pstate, pstateCompactedRegion) => pure (pstate, some pstateCompactedRegion)
      | .error .toolchainVersionChanged =>
          throwError m!"A different version of the Lean toolchain is being used than the one that created the premise selection state on disk. Place the {`Hammer.PS.learn} command at the top level of the current file (e.g. directly below the import commands) to rebuild the state."
      | .error .pstateVersionChanged =>
          throwError m!"A different version of the premise selection state is required than the one that is saved on disk. Place the {`Hammer.PS.learn} command at the top level of the current file (e.g. directly below the import commands) to rebuild the state."
    else
      pure (∅, none)
  
  let imports := (←getEnv).header.imports
  let constants := (←getEnv).constants.map₂.foldl (λconstants _ c => constants.push c) ∅
  
  let (pstate, mainModuleIdx) ← pstate.updateMainModule (←getMainModule) imports constants
  let candidateFacts := pstate.candidateFacts mainModuleIdx

  let suggestions ← x pstate candidateFacts
  let suggestions ← suggestions.filterMapM (suggestionToConstant pstate)
  
  -- no references to objects in pstate must be used beyond this point
  if let some pstateCompactedRegion := pstateCompactedRegion? then
    pstateCompactedRegion.free
  
  return suggestions

@[implemented_by unsafeGetSuggestions]
opaque getSuggestions : (PState → Array UInt64 → TacticM (Array (UInt64 × Float))) → TacticM (Array (ConstantInfo × Float))


def getGoalSymbols (pstate : PState) : TacticM (Array UInt64) := do
  let goalSymbols ← getFactSymbols' (←getMainModule) (←getMainTarget)
  let goalSymbols ← (←getMCtx).decls.foldlM
    (λgoalSymbols _ mdecl => return (←getFactSymbols' (←getMainModule) mdecl.type).fold .insert goalSymbols)
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

def getMePoSuggestions : TacticM (Array (ConstantInfo × Float)) :=
  getSuggestions getMePoSuggestions'

elab "mepo" : tactic => do
  let suggestions ← getMePoSuggestions
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

def getMaShNBSuggestions : TacticM (Array (ConstantInfo × Float)) :=
  getSuggestions getMaShNBSuggestions'

elab "mashnb" : tactic => do
  let suggestions ← getMaShNBSuggestions
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

def getMaShKNNSuggestions : TacticM (Array (ConstantInfo × Float)) :=
  getSuggestions getMaShKNNSuggestions'

elab "mashknn" : tactic => do
  let suggestions ← getMaShKNNSuggestions
  for (suggestion, score) in suggestions do
    logInfo m!"{suggestion.name}: {score}"


def getMeShSuggestions : TacticM (Array (ConstantInfo × Float)) :=
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
  let suggestions ← getMeShSuggestions
  for (suggestion, score) in suggestions do
    logInfo m!"{suggestion.name}: {score}"
