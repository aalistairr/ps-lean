-- Author: Alistair Geesing

import Lean

namespace Hammer.PS

open Lean


-- Adapted from Lean.Util.FoldConsts
namespace FoldConstsTRImpl

abbrev cacheSize : USize := 8192 - 1

structure State where
  visitedTerms  : Array Expr  -- Remark: cache based on pointer address. Our "unsafe" implementation relies on the fact that `()` is not a valid Expr
  visitedConsts : NameHashSet -- cache based on structural equality
  acc           : Array Name
  pending       : Array Expr

abbrev FoldM := StateM State

unsafe def visited (e : Expr) (size : USize) : FoldM Bool := do
  let s ← get
  let h := ptrAddrUnsafe e
  let i := h % size
  let k := s.visitedTerms.uget i lcProof
  if ptrAddrUnsafe k == h then pure true
  else do
    modify fun s => { s with visitedTerms := s.visitedTerms.uset i e lcProof }
    pure false

unsafe def addPending (e : Expr) (size : USize) : FoldM PUnit := do
  if ←visited e size then
    return
  modify λs => { s with pending := s.pending.push e }

def addSym (sym : Name) : FoldM PUnit := do
  if (←get).visitedConsts.contains sym then
    return
  modify λs => { s with
    visitedConsts := s.visitedConsts.insert sym
    acc := s.acc.push sym
  }

unsafe def foldIter (size : USize) : FoldM (Option (Array Name)) := do
  let e ← match ←modifyGet λs => (s.pending.back?, { s with pending := s.pending.pop }) with
  | none => return (←get).acc
  | some e => pure e

  match e with
  | .forallE _ d b _ => do
    addPending d size
    addPending b size
  | .lam _ d b _ => do
    addPending d size
    addPending b size
  | .mdata _ b => do
    addPending b size
  | .letE _ t v b _ => do
    addPending t size
    addPending v size
    addPending b size
  | .app f a => do
    addPending f size
    addPending a size
  | .proj _ _ b => do
    addPending b size
  | .const c _ => do
    addSym c
  | _ => pure ()

  return none

unsafe def foldAux (size : USize) : FoldM (Array Name) := do
  match ←foldIter size with
  | some acc => return acc
  | none => foldAux size

unsafe def foldCore (size : USize) (e : Expr) : FoldM (Array Name) := do
  addPending e size
  foldAux size

unsafe def initState : State :=
  { visitedTerms  := mkArray cacheSize.toNat (cast lcProof ()),
    visitedConsts := {},
    acc           := {},
    pending       := {}}

@[inline] unsafe def foldUnsafe (e : Expr) : Array Name :=
  (foldCore cacheSize e).run' initState

end FoldConstsTRImpl

/-- Apply `f` to every constant occurring in `e` once. -/
@[implemented_by FoldConstsTRImpl.foldUnsafe]
opaque foldConstsTR (e : Expr) : Array Name

def getUsedConstantsTR (e : Expr) : Array Name :=
  foldConstsTR e
