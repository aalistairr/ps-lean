-- Author: Alistair Geesing

import Lean

namespace Hammer.PS

open Lean


def excludeConstantName : Name → Bool
| .str _ s => s.startsWith "_cstage" -- type inference fails on these constants
| _ => false

def excludeModule : Name → Bool
| `Mathlib.Data.TypeVec => true -- feature extraction fails on this module
| _ => false

def boringSymbols := [``True, ``False, ``And, ``Or, ``Not, ``Eq, ``HEq, ``Ne, `Iff, ``Exists, ``ite, ``Decidable, ``dite]
  |>.foldl NameSet.insert ∅

def dealbreakingSymbols : List Name := []

def isBoringOrDealbreakingFact (c : ConstantInfo) : Bool :=
  let syms := Lean.Expr.getUsedConstants c.type
  syms.all boringSymbols.contains || syms.any dealbreakingSymbols.contains

def isAlias (c : ConstantInfo) : Bool := match c.value? with
| some (.const _ _) => true
| _ => false

def excludeConstant (module : Name) (c : ConstantInfo) : Bool :=
     excludeModule module
  || excludeConstantName c.name
  || isAlias c
  || isBoringOrDealbreakingFact c