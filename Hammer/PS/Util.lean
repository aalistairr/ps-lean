-- Author: Alistair Geesing

import Lean
import Hammer.PS.Util.Graph
import Hammer.PS.Util.UsedConstants

namespace Hammer.PS

open Lean


private partial def sortedFindInsertionIndexAux [Inhabited α] (lt : α → α → Bool) (xs : Array α) (x : α) (i₀ i₁ : Nat) : Nat :=
  let size := i₁ - i₀
  if size == 0 then
    0
  else if size == 1 then
    if ¬lt (xs.get! i₀) x
      then i₀
      else i₁
  else
    let m := i₀ + size / 2
    if lt x (xs.get! m)
      then sortedFindInsertionIndexAux lt xs x i₀ m
      else sortedFindInsertionIndexAux lt xs x m i₁

def sortedFindInsertionIndex [Inhabited α] (lt : α → α → Bool) (xs : Array α) (x : α) : Nat :=
  sortedFindInsertionIndexAux lt xs x 0 xs.size

def sortedInsert [Inhabited α] (lt : α → α → Bool) (xs : Array α) (x : α) : Array α :=
  xs.insertAt! (sortedFindInsertionIndex lt xs x) x


def cmpFloat (f₁ f₂ : Float) : Ordering :=
  if f₁ < f₂ then
    .lt
  else if f₁ > f₂ then
    .gt
  else
    .eq

def floatLt (f₁ f₂ : Float) : Bool := f₁ < f₂


def letMetaTelescope (e : Expr) : MetaM (Array Expr × Array BinderInfo × Expr) := do
  if let .letE declName type value body _ := e then
    let mvar ← Meta.mkFreshExprMVar type
    match mvar with
    | .mvar mvarId => mvarId.define declName type value
    | _ => unreachable!
    let body := body.instantiate1 mvar
    return (#[mvar], #[.default], body)
  else
    return (∅, ∅, e)


structure Counter where
  limits : Array Nat
  values : Array Nat
  deriving Repr

def mkCounter (ls : List (List α)) : Counter := {
  limits := ls.map List.length |>.toArray
  values := List.replicate ls.length 0 |>.toArray
}

def Counter.inc (c : Counter) : (Bool × Counter) := Id.run do
  let mut values := c.values
  let mut carry := 1
  let mut i := values.size
  for (value, limit) in Array.zip c.values c.limits |>.reverse do
    i := i - 1
    if value + carry < limit then
      values := values.swapAt! i (value + carry) |>.snd
      carry := 0
    else
      values := values[:i].toArray.appendList (List.replicate (values.size - i) 0)
      carry := 1

  let rollover := values.all (.== 0)
  return (rollover, {
    limits := c.limits,
    values
  })


partial def productNAux [Inhabited α] (ls : List (List α)) (c : Counter) : StateM (List (List α)) PUnit := do
  let mut r := ∅
  for (l, i) in List.zip ls c.values.toList do
    if i < l.length then
      r := r ++ [l.get! i] 
  modify λrs => rs ++ [r]

  let (rollover, c') := c.inc
  if rollover
    then return
    else productNAux ls c'

def productN [Inhabited α] (ls : List (List α)) : List (List α) :=
  productNAux ls (mkCounter ls) |>.run [] |>.snd


def _root_.Array.count (xs : Array α) (p : α → Bool) : Nat := Id.run do
  let mut n := 0
  for x in xs do
    if p x then
      n := n + 1
  return n


abbrev ModuleMap := NameMap ModuleData

def getModuleMap (env : Environment) : ModuleMap :=
  env.header.moduleNames.size.fold
    (λi moduleMap => moduleMap.insert env.header.moduleNames[i]! env.header.moduleData[i]!)
    ∅


def getModuleDAG (moduleMap : ModuleMap) : NameDiGraph := Id.run do
  let mut dag := ∅

  for (module, _) in moduleMap do
    dag := dag.insertNode module
    assert! dag.containsNode module
  
  for (module, moduleData) in moduleMap do
    for importt in moduleData.imports do
      if dag.containsEdge module importt.module then
        continue
      dag := dag.insertEdge module importt.module

  return dag


partial def getUnaliased (env : Environment) (name : Name) : Name :=
  match env.find? name with
  | some c => match c.value? with
    | some (.const unaliased _) => getUnaliased env unaliased
    | _ => match Lean.Compiler.getImplementedBy? env name with
      | some unaliased => getUnaliased env unaliased
      | none => name
  | none => name


def liftMetaM (env : Environment) (m : MetaM α) : IO α := do
  let (r, _) ← m
    |>.run'
    |>.toIO
      {
        fileName := "<anonymous>"
        fileMap := FileMap.mk "" #[] #[]
        maxHeartbeats := 9999999999999999999
      }
      { env }
  return r

def UInt64.max : UInt64 := 0xffffffffffffffff

def prefixesOfName : Name → List Name
| .anonymous => []
| n@(.str p _) => n :: (prefixesOfName p)
| n@(.num p _) => n :: (prefixesOfName p)
