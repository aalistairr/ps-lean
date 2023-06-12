-- Ported from Isabelle (https://github.com/isabelle-prover/mirror-isabelle/blob/master/src/HOL/Tools/Sledgehammer/sledgehammer_mash.ML)
-- Isabelle license found in ISABELLE.COPYRIGHT applies
-- Original author: Jasmin Blanchette, TU Muenchen
-- Original author: Cezary Kaliszyk, University of Innsbruck
-- Port author: Alistair Geesing

import Lean

import Hammer.PS.MePo
import Hammer.PS.MaSh.NB
import Hammer.PS.MaSh.KNN

namespace Hammer.PS.MeSh

open Lean
open IO

def steepWeightOfFact (rank : Nat) : Float :=
  (0.62).pow (rank + 1).toFloat.log2

def weightFactsSteeply [Inhabited α] (suggestions : Array (α × Float)) : Array (α × Float) :=
  suggestions.mapIdx
    (λi suggestion => (suggestion.fst, steepWeightOfFact i))

def normalize (maxFacts : UInt64) : Array (α × Float) → Array (α × Float)
| #[] => #[]
| suggestions =>
  let suggestions' := suggestions[:maxFacts.toNat]
  let avg := suggestions'.foldl (· + ·.snd) 0.0 / suggestions'.size.toFloat
  suggestions.map (Prod.map id (. / avg))

def mesh [Inhabited α] [BEq α] [Hashable α] (maxFacts : UInt64) (suggestionss : List (Float × Array (α × Float))) : Array (α × Float) :=
  let suggestionss := suggestionss.map $ Prod.map id (normalize maxFacts ∘ weightFactsSteeply)
  let facts := suggestionss.foldl
    (λfacts (_, suggestions) => suggestions.foldl
      (λfacts (fact, _) => facts.insert fact)
      facts)
    (∅ : HashSet α)
  
  let suggestionss := suggestionss.map $ Prod.map id (λsuggestions => suggestions.foldl (λsuggestions (fact, score) => suggestions.insert fact score) (∅ : HashMap α Float))

  let scoreIn := λfact (globalWeight, suggestions) =>
    suggestions.find? fact |>.map (. * globalWeight)
  let weightOf := λfact =>
    let scores := suggestionss.filterMap (scoreIn fact)
    scores.foldl (.+.) 0.0 / scores.length.toFloat

  facts.toArray
    |>.map (λfact => (fact, weightOf fact))
    |>.qsort (λ(_, a) (_, b) => a > b)
    |>.toSubarray (stop := maxFacts.toNat)
    |>.toArray
