-- Ported from Isabelle (https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Tools/Sledgehammer/sledgehammer_mash.ML)
-- Isabelle license found in ISABELLE.COPYRIGHT applies
-- Original author: Jasmin Blanchette, TU Muenchen
-- Original author: Cezary Kaliszyk, University of Innsbruck
-- Port author: Alistair Geesing

import Lean
import Hammer.PS.Util
import Hammer.PS.MaSh.Common
import Hammer.PS.PState

namespace Hammer.PS.MaSh.NB

open IO
open Lean Meta Elab Tactic


structure Fudge where
  σ₁ : Float
  σ₂ : Float
  σ₃ : Float
  σ₄ : Float

instance : Inhabited Fudge where
  default := {
    σ₁ := 30.0
    σ₂ := 5.0
    σ₃ := 0.2
    σ₄ := -18.0
  }

structure Context where
  fudge : Fudge := default
  maxFacts : UInt64

  pstate : PState
  candidateFacts : Array UInt64

  goalFeatures : Array UInt64

abbrev MashNBM := ReaderT Context IO

instance : MonadClassifierContext MashNBM where
  readFactCount := return (←read).pstate.factCount.toUInt64
  readFeatureFreqs := return (←read).pstate.featureFreqs

def readFudge : MashNBM Fudge := return (←read).fudge
def σ₁ : MashNBM Float := return (←readFudge).σ₁
def σ₂ : MashNBM Float := return (←readFudge).σ₂
def σ₃ : MashNBM Float := return (←readFudge).σ₃
def σ₄ : MashNBM Float := return (←readFudge).σ₄

def goalFeatures : MashNBM (Array UInt64) := return (←read).goalFeatures

def s (factI : Nat) : MashNBM (HashMap UInt64 UInt64) := do
  return (←read).pstate.factAsDepOfFeatureFreqss[factI]!

def t (factI : Nat) : MashNBM Float :=
  return (←read).pstate.factAsDepFreqs[factI]! |>.toFloat

def features (factI : Nat) : MashNBM (Array UInt64) :=
  return (←read).pstate.factFeaturess[factI]!

def factScore (factI : Nat) : MashNBM Float := do
  let t ← t factI
  let s ← s factI

  let (s, res) ← (←goalFeatures).foldlM
    (λ(s, res) feature => do
      match s.find? feature with
      | some sf => return (s.erase feature, res + (←w feature) * ((←σ₂) * (sf.toFloat / t)).log)
      | none => return (s, res + (←w feature) * (←σ₄)))
    (s, (←σ₁) * t.log)

  let sumOfWeights ← s.foldM
    (λsow feature featureFreq => return sow + (←w feature) * (1.0 - (featureFreq - 1).toFloat / t).log)
    0.0

  return res + (←σ₃) * sumOfWeights

def resultGt : (UInt64 × Float) → (UInt64 × Float) → Bool
| (_, s₀), (_, s₁) => s₀ > s₁

def naiveBayes : MashNBM (Array (UInt64 × Float)) :=
  return ←(←read).candidateFacts.foldlM
    (λresults factI => do
      let score ← factScore factI.toNat
      if results.size.toUInt64 < (←read).maxFacts then
        return sortedInsert resultGt results (factI, score)
      else if let some (_, lastScore) := results.back? then
        if score > lastScore then
          return sortedInsert resultGt results.pop (factI, score)
      return results
      )
    (Array.mkEmpty (←read).maxFacts.toNat)
