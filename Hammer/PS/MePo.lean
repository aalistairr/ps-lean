-- ported from Isabelle (https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Tools/Sledgehammer/sledgehammer_mepo.ML)
-- Isabelle license found in ISABELLE.COPYRIGHT applies
-- Original author: Jia Meng, Cambridge University Computer Laboratory and NICTA
-- Original author: Jasmin Blanchette, TU Muenchen
-- Port author: Alistair Geesing

import Lean
import Hammer.PS.Common
import Hammer.PS.Util
import Hammer.PS.PState

namespace Hammer.PS.MePo

open Lean
open IO

structure Fudge where
  maxImperfect : Float
  maxImperfectExp : Float
  kickOutHopelessRound : UInt64
  worseIrrelFreq : UInt64
  targetSymMultiplier : Float
  moduleSymRelWeight : Float
  moduleSymIrrelWeight : Float
  higherOrderIrrelWeight : Float

instance : Inhabited Fudge where
  default := {
    maxImperfect := 100
    maxImperfectExp := 0.2
    kickOutHopelessRound := 5
    worseIrrelFreq := 100
    targetSymMultiplier := 100
    moduleSymRelWeight := 0.5
    moduleSymIrrelWeight := 0.25
    higherOrderIrrelWeight := 1.05
  }

structure Context where
  fudge : Fudge := default
  p0 : Float := 0.45
  p1 : Float := 0.85
  maxFacts : UInt64

  decay : Float := ((1.0 - p1) / (1.0 - p0)).pow (1.0 / (maxFacts + 1).toFloat)

  pstate : PState

structure State where
  round : UInt64
  p : Float

  rSyms : HashSet UInt64
  rFacts : Array (UInt64 × Float)
  iFacts : Array UInt64

def initState (ctx : Context) (candidateFacts : Array UInt64) (goalFeatures : Array UInt64) : State := {
    round := 0
    p := ctx.p0
    rSyms := goalFeatures.foldl HashSet.insert ∅
    rFacts := #[]
    iFacts := candidateFacts
  }

abbrev MepoM := ReaderT Context $ StateRefT State IO


private def fudge : MepoM Fudge := return (←read).fudge
private def symFreq (sym : UInt64) : MepoM UInt64 := return (←read).pstate.symbolFreqs[sym.toNat]!
private def rSyms : MepoM (HashSet UInt64) := return (←get).rSyms
private def rFacts : MepoM (Array (UInt64 × Float)) := return (←get).rFacts
private def iFacts : MepoM (Array UInt64) := return (←get).iFacts
private def remainingFacts : MepoM UInt64 := do
  let maxFacts := (←read).maxFacts
  let rFactsSize := (←rFacts).size.toUInt64
  if rFactsSize > maxFacts
    then return 0
    else return maxFacts - rFactsSize


private def maxImperfect : MepoM UInt64 := do
  return (←fudge).maxImperfect.toUInt64


private def getIsModulifiedSymbol (sym : UInt64) : MepoM Bool := do
  let symValue := (←read).pstate.symbolValues[sym.toNat]!
  return isModulifiedSymbol symValue

private def getSymbolOrder (sym : UInt64) : MepoM UInt8 := do
  return (←read).pstate.symbolOrders[sym.toNat]!


private def genericSymScore (freq : UInt64) : Float :=
  1 + 2 / Float.log ((freq + 1).toFloat)

private def rSymScore (sym : UInt64) : MepoM Float := do
  if ←getIsModulifiedSymbol sym then
    return (←fudge).moduleSymRelWeight

  return genericSymScore (←symFreq sym)

private def powNat (x : Float) : Nat → Float
| 0 => 1.0
| 1 => x
| n + 1 => x * (powNat x n)

private def powUInt8 (x : Float) (p : UInt8) : Float := powNat x p.toNat

private def iSymScore (sym : UInt64) : MepoM Float := do
  if ←getIsModulifiedSymbol sym then
    return (←fudge).moduleSymIrrelWeight

  let freq ← symFreq sym
  let worseIrrelFreq := (←fudge).worseIrrelFreq
  return (if freq < worseIrrelFreq
    then Float.log $ ((freq + 1).toFloat) / Float.log worseIrrelFreq.toFloat
    else (genericSymScore freq) / (genericSymScore worseIrrelFreq)
  ) * (powUInt8 (←fudge).higherOrderIrrelWeight (←getSymbolOrder sym))

private def factScore : UInt64 → MepoM Float
| factI => do
  let mut m := 0.0
  let mut i := 0.0
  for sym in (←read).pstate.factSymbolss[factI.toNat]! do
    if (←rSyms).contains sym then
      m := m + (←rSymScore sym)
    else
      i := i + (←iSymScore sym)

  return m / (m + i)


private def factGt : (UInt64 × Float) → (UInt64 × Float) → Bool
| (_, a), (_, b) => a > b

private def evalFacts : MepoM (Array (UInt64 × Float) × Array UInt64) := do
  let mut candidates := ∅
  let mut rejects := ∅
  for factI in (←get).iFacts do
    let score := ←factScore factI
    if score > (←get).p then
      candidates := sortedInsert factGt candidates (factI, score)
    else
      rejects := rejects.push factI
  return (candidates, rejects)

partial def mepo : MepoM (Array (UInt64 × Float)) := do
  let mut (candidates, rejects) ← evalFacts
  let mut accepts := Array.empty

  let mut remainingAccepts ← remainingFacts 
  let mut remainingImperfect ← maxImperfect
  let mut acceptedPerfect := 0
  for candidate@(fact, score) in candidates do
    let isPerfect := (score > 0.99999)
    if isPerfect || (remainingAccepts > 0 && remainingImperfect > 0) then
      accepts := accepts.push candidate

      if isPerfect then
        acceptedPerfect := acceptedPerfect + 1
      else
        remainingImperfect := remainingImperfect - 1

      if remainingAccepts > 0 then
          remainingAccepts := remainingAccepts - 1
    else
      if ¬(score < 0.001 && (←get).round == (←fudge).kickOutHopelessRound) then
        rejects := rejects.push fact

  let decay := (←read).decay

  let mut rSyms := (←get).rSyms
  for (factI, _) in accepts do
    let factSyms := (←read).pstate.factSymbolss[factI.toNat]!
    for factSym in factSyms do
      if ¬rSyms.contains factSym then
        rSyms := rSyms.insert factSym

  modify (λs => {
      round := s.round + 1
      p := 1.0 - (1.0 - s.p) * (decay.pow accepts.size.toFloat)
      rSyms
      rFacts := accepts.foldl (λrFacts (fact, score) => rFacts.push (fact, score)) s.rFacts
      iFacts := rejects
    })

  if accepts.size == 0 || (←remainingFacts) == 0
    then rFacts
    else mepo
