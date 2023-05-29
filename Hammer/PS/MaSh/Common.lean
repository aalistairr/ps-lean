-- Author: Alistair Geesing

import Lean
import Hammer.PS.Common
import Hammer.PS.Util

namespace Hammer.PS.MaSh

open IO
open Lean Meta Elab Tactic


abbrev Feature := String
abbrev FeatureSet := HashSet Feature
abbrev FeatureMap := HashMap Feature

def FeatureSet.intersect (fs₁ fs₂ : FeatureSet) : FeatureSet :=
  fs₁.fold
    (λr f₁ => if fs₂.contains f₁ then r.insert f₁ else r)
    ∅

def FeatureSet.subtract (fs₁ fs₂ : FeatureSet) : FeatureSet :=
  fs₁.fold
    (λr f₁ => if ¬fs₂.contains f₁ then r.insert f₁ else r)
    ∅


def subtermFeaturesDepth := 2
def typeFeaturesDepth := 1


-- Adapted from Isabelle source (https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Tools/Sledgehammer/sledgehammer_mash.ML)
-- Isabelle license found in ISABELLE.COPYRIGHT applies
-- Original author: Jasmin Blanchette, TU Muenchen
-- Original author: Cezary Kaliszyk, University of Innsbruck
def crudeType : Expr → MetaM (Option Feature)
| .app fn arg => do
  match (←crudeType fn, ←crudeType arg) with
  | (some fnT, some argT) => pure $ fnT ++ "_" ++ argT
  | (some fnT, none) => pure fnT
  | (none, some argT) => pure argT
  | (none, none) => pure none
| .letE _ _ _ body _ => crudeType body
| .const name _ => return (getUnaliased (←getEnv) name).toString
| .mvar _ => pure none
| .fvar _ => pure none
| .forallE _ _ _ _ => pure "fun"
| .lam _ _ _ _ => pure "fun"
| _ => pure none

partial def constantFeature : Expr → MetaM (Option Feature)
| x@(.letE _ _ _ _ _) => do
  let (_, _, body) ← letMetaTelescope x
  constantFeature body.getAppFn
| .const name _ => return (getUnaliased (←getEnv) name).toString
| .mvar mvarId => return ←crudeType (←mvarId.getType)
| .fvar fvarId => return ←crudeType (←fvarId.getType)
| .forallE _ _ _ _ => pure "fun"
| .lam _ _ _ _ => pure "fun"
| .sort _ => pure none
| .lit (.natVal n) => pure $ toString n
| .lit (.strVal s) => pure s
| .proj typeName idx _ => return (getUnaliased (←getEnv) typeName).toString ++ "." ++ (toString idx)
|   (.mdata _ _) => pure none
| x@(.bvar _) => throwError m!"constantFeature: don't know what to do with .bvar expression {x}"
| x@(.app _ _) => throwError m!"constantFeature: don't know what to do with .app expression {x}"

partial def featurePatternsOf (depth : Nat) (x : Expr) : MetaM (Option (FeatureSet × Option Feature)) := do
  if depth == 0 then
    return none
  
  let typeFeature ←
    try crudeType $ ←inferType x
    catch _ => return none
  let mut normalFeatures := ∅


  let fn := x.getAppFn
  let fnFeature ← match ←constantFeature fn with
  | .some fnFeature => pure fnFeature
  | .none => return some (∅, typeFeature)

  normalFeatures := normalFeatures.insert fnFeature
  
  let args ← getAppArgsUpToImplicitPrefix x
  let argsFeatures ← args.filterMapM (featurePatternsOf $ depth - 1)
  let (normalArgsFeatures, _) := argsFeatures.unzip
  for (argFeatures, argTypeFeature) in argsFeatures do
    if let some argTypeFeature := argTypeFeature then
      normalFeatures := normalFeatures.insert $ fnFeature ++ "(" ++ argTypeFeature ++ ")"
    if argFeatures.size > 0 then
      for argFeature in argFeatures do
        normalFeatures := normalFeatures.insert $ fnFeature ++ "(" ++ argFeature ++ ")"

  for argsFeatures in productN (normalArgsFeatures.toList.map HashSet.toList) do
    if argsFeatures.length == 0 then
      continue
    normalFeatures := normalFeatures.insert $ fnFeature ++ "(" ++ (argsFeatures.intersperse "," |>.foldl (.++.) "") ++ ")"

  return some (normalFeatures, typeFeature)

def fullyAppliedTypeOf (x : Expr) : MetaM (Option Expr) := do
  let type ←
    try inferType x
    catch _ => return none
  match type with
  | .const _ _ => return some type
  | .app _ _ => return some type
  | _ => return none

def getAppFnName (x : Expr) : Option Name :=
  match x.getAppFn with
  | .const name _ => some name
  | _ => none

def exprFeatures (x : Expr) : MetaM FeatureSet := do
  let mut features : FeatureSet := ∅
  let mut types : ExprSet := ∅

  for subterm in ←exprSubterms x do
    if let some (normalFeatures, _) ← featurePatternsOf subtermFeaturesDepth subterm then
      features := features.insertMany normalFeatures
  
    if let some type ← fullyAppliedTypeOf subterm then
      types := types.insert type
  
  let (mvarXs, _, _) ← forallMetaTelescope x
  for mvarX in mvarXs do
    if let some type ← fullyAppliedTypeOf mvarX then
      types := types.insert type

  for type in types do
    if let some (normalFeatures, _) ← featurePatternsOf typeFeaturesDepth type then
      features := features.insertMany normalFeatures

    if let some appFnName := getAppFnName type then
      if isStructure (←getEnv) appFnName then
        for parentStructure in getAllParentStructures (←getEnv) appFnName do
          features := features.insert (getUnaliased (←getEnv) parentStructure).toString

  return features

def prefixesOfName : Name → List Name
| .anonymous => []
| n@(.str p _) => n :: (prefixesOfName p)
| n@(.num p _) => n :: (prefixesOfName p)

def getFactFeatures' (moduleName : Name) (goalName? : Option Name) (goalType : Expr) : MetaM FeatureSet := do
  let mut features ← exprFeatures goalType
  features := features.insert moduleName.toString
  return features

def getFactFeatures (module : Name) (constantInfo : ConstantInfo) (fact : Expr) : MetaM FeatureSet :=
  getFactFeatures' module constantInfo.name fact


def extendedFeatures' (factFeatures : Array (Array UInt64)) (factInProofsOf : Array (Array UInt64)) (factI : Nat) : Array UInt64 := Id.run do
  let mut features := (∅ : HashSet UInt64)
  features := features.insertMany factFeatures[factI]!
  for proofFact in factInProofsOf[factI]! do
    features := features.insertMany $ factFeatures[proofFact.toNat]!
  return features.toArray


class MonadReaderOfClassifierContext (m : Type → Type) where
  readFactCount : m UInt64
  readFeatureFreqs : m (Array UInt64)

def w [Monad m] [MonadReaderOfClassifierContext m] (feature : UInt64) : m Float := do
  let factCount ← MonadReaderOfClassifierContext.readFactCount
  let featureFreqs ← MonadReaderOfClassifierContext.readFeatureFreqs
  let featureFreq := featureFreqs[feature.toNat]!
  return (factCount.toFloat / featureFreq.toFloat).log