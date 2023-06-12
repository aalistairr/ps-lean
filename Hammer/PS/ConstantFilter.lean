-- Author: Alistair Geesing

import Lean

namespace Hammer.PS

open Lean


def isExcludedConstantName : Name → Bool
| .str _ s => s.startsWith "_cstage" -- type inference fails on these constants
| _ => false

def isExcludeModule : Name → Bool
| `Mathlib.Data.TypeVec => true -- feature extraction fails on this module
| _ => false

def boringSymbols := [``True, ``False, ``And, ``Or, ``Not, ``Eq, ``HEq, ``Ne, `Iff, ``Exists, ``ite, ``Decidable, ``dite]
  |>.foldl NameSet.insert ∅

def dealbreakingSymbols : NameSet := ∅

def isBoringOrDealbreakingFact (c : ConstantInfo) : Bool :=
  let typeSyms := c.type.getUsedConstants
  let valueSyms := c.value?.map (. |>.getUsedConstants) |>.getD ∅

  typeSyms.all boringSymbols.contains
  || typeSyms.any dealbreakingSymbols.contains
  || valueSyms.any dealbreakingSymbols.contains

def isAlias (c : ConstantInfo) : Bool :=
  if let some (.const _ _) := c.value?
    then true
    else false

def excludeConstant (module : Name) (c : ConstantInfo) : Bool :=
     isExcludeModule module
  || isExcludedConstantName c.name
  || isAlias c
  || isBoringOrDealbreakingFact c
