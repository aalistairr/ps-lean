-- Ported from Isabelle (https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Tools/Sledgehammer/sledgehammer_mash.ML)
-- Isabelle license found in ISABELLE.COPYRIGHT applies
-- Original author: Jasmin Blanchette, TU Muenchen
-- Original author: Cezary Kaliszyk, University of Innsbruck
-- Port author: Alistair Geesing

import Lean
import Hammer.PS.Util
import Hammer.PS.MaSh.Common
import Hammer.PS.PState

namespace Hammer.PS.MaSh.KNN

open IO
open Lean Meta Elab Tactic


structure Fudge where
  τ₁ : Float
  τ₂ : Float
  initialK : UInt64

instance : Inhabited Fudge where
  default := {
    τ₁ := 6.0
    τ₂ := 2.7
    initialK := 0
  }


structure Context where
  fudge : Fudge := default
  maxFacts : UInt64

  pstate : PState

  candidateFacts : Array UInt64
  goalFeatures : Array UInt64


structure State where
  noRecommends : UInt64
  recommends : Array (UInt64 × Float)
  age : Float
  k : UInt64

def initState (ctx : Context) : State := {
  noRecommends := 0
  recommends := ctx.pstate.factNames.size.fold
    (λi recommends => recommends.push (i.toUInt64, 0.0))
    (Array.mkEmpty ctx.pstate.factNames.size)
  age := 500000000.0
  k := 0
}


abbrev KNNM := ReaderT Context $ StateT State IO

instance : MonadReaderOfClassifierContext KNNM where
  readFactCount := return (←read).pstate.factNames.size.toUInt64
  readFeatureFreqs := return (←read).pstate.featureFreqs

def readFudge : KNNM Fudge := return (←read).fudge


def getFeatureFactss : KNNM (Array (Array UInt64)) := do
  let mut featureFactss := (←read).pstate.featureValues.size.fold
    (λ_ featureFactss => featureFactss.push ∅)
    (∅ : Array (Array UInt64))
  
  for factI in (←read).candidateFacts do
    for factFeature in (←read).pstate.factFeaturess[factI.toNat]! do
      featureFactss := featureFactss.modify factFeature.toNat (Array.push . factI)

  return featureFactss

def getOverlapsSqr : KNNM (Array (UInt64 × Float)) := do
  let featureFactss ← getFeatureFactss

  let mut overlapsSqr := (∅ : Array (UInt64 × Float))
  let mut overlapsSqrIdxs := (←read).pstate.factNames.size.fold
    (λ_ overlapsSqrIdxs => overlapsSqrIdxs.push UInt64.max)
    (Array.mkEmpty (←read).pstate.factNames.size)

  for goalFeature in (←read).goalFeatures do
    let w := (←w goalFeature).pow (←readFudge).τ₁
    for factI in featureFactss[goalFeature.toNat]! do
      let overlapsSqrI := overlapsSqrIdxs[factI.toNat]!
      if overlapsSqrI == UInt64.max then
        let overlapsSqrI := overlapsSqr.size.toUInt64
        overlapsSqrIdxs := overlapsSqrIdxs.set! factI.toNat overlapsSqrI
        overlapsSqr := overlapsSqr.push (factI, w)
      else
        overlapsSqr := overlapsSqr.modify overlapsSqrI.toNat (Prod.map id (. + w))

  let zeros := (←read).pstate.factNames.size.fold
    (λi xs => if overlapsSqrIdxs[i]! == UInt64.max then xs.push (i.toUInt64, 0.0) else xs)
    (Array.mkEmpty (←read).pstate.factNames.size)
  return zeros ++ overlapsSqr.qsort (λ(_, a) (_, b) => a < b)

def incRecommend (j : UInt64) (v : Float) : KNNM PUnit := do
  modify λs =>
    let (_, ov) := s.recommends[j.toNat]!
    if ov <= 0.0
    then { s with
        noRecommends := s.noRecommends + 1
        recommends := s.recommends.set! j.toNat (j, ov + s.age)
      }
    else { s with
        recommends := s.recommends.set! j.toNat (j, ov + v)
      }

def doK (overlapsSqr : Array (UInt64 × Float)) : KNNM Bool := do
  let k := (←get).k
  let factCount := (←read).pstate.factNames.size.toUInt64
  if k >= factCount then
    return false

  let (j, o2) := overlapsSqr[(factCount - k - 1).toNat]!
  incRecommend j o2
  
  let deps := (←read).pstate.factDepss[j.toNat]!
  let l := deps.size.toFloat

  let v := (←readFudge).τ₂ * o2 / l
  for dep in deps do
    incRecommend dep v

  modify λs => { s with k := s.k + 1 }

  return true

partial def while1 (overlapsSqr : Array (UInt64 × Float)) : KNNM PUnit := do
  if (←get).k == (←readFudge).initialK + 1 then
    return

  if ←doK overlapsSqr then
    while1 overlapsSqr

partial def while2 (overlapsSqr : Array (UInt64 × Float)) : KNNM PUnit := do
  if (←get).noRecommends >= (←read).maxFacts then
    return
  
  if ←doK overlapsSqr then
    modify λs => { s with age := s.age - 10000.0 }
    while2 overlapsSqr

def resultGt : (UInt64 × Float) → (UInt64 × Float) → Bool
| (_, a), (_, b) => a > b

def kNN : KNNM (Array (UInt64 × Float)) := do
  let overlapsSqr ← getOverlapsSqr
  
  while1 overlapsSqr
  while2 overlapsSqr

  let mut results := Array.mkEmpty (←read).maxFacts.toNat
  for (i, ov) in (←get).recommends do
    let ov := ov + 1000000000.0
    if results.size.toUInt64 < (←read).maxFacts then
      results := sortedInsert resultGt results (i, ov)
    else if let some (_, lastOv) := results.back? then
      if ov > lastOv then
        results := sortedInsert resultGt results.pop (i, ov)
  return results
