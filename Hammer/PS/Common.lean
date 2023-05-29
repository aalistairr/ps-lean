-- Author: Alistair Geesing

import Lean
import Hammer.PS.Util
import Hammer.PS.ConstantFilter

namespace Hammer.PS

open Lean Meta


structure ExprSubtermsState where
  subterms : ExprSet
  pending : Array Expr

abbrev ExprSubtermsM := StateRefT ExprSubtermsState MetaM

def excludeTermRoot : Expr → Bool
| .const ``Iff _    => true
| .const ``Eq _     => true
| .const ``HEq _    => true
| .const ``And _    => true
| .const ``Or _     => true
| .const ``Exists _ => true
| .const ``Ne _     => true
| .const ``Not _    => true
| _ => false

def ExprSubtermsM.admit (x : Expr) : ExprSubtermsM PUnit := do
  if ¬(x.isApp && excludeTermRoot x.getAppFn) && ¬x.isForall && ¬x.isLambda && ¬x.isLet then
    modify λs => { s with subterms := s.subterms.insert x }

def getAppNumImplicitPrefixArgsAux (acc : Nat) : Expr → Nat
| .forallE _ _ b .implicit => getAppNumImplicitPrefixArgsAux (acc + 1) b
| .forallE _ _ b .instImplicit => getAppNumImplicitPrefixArgsAux (acc + 1) b
| .forallE _ _ b .strictImplicit => getAppNumImplicitPrefixArgsAux (acc + 1) b
| _ => acc

def getAppNumImplicitPrefixArgs (x : Expr) : MetaM Nat := do
  if ¬x.isApp then
    return 0
  
  match x.getAppFn with
  | .const n _ => do
    let c ← match (←getEnv).find? n with
    | some c => pure c
    | none => throwError "Couldn't find constant {n}"
    
    return getAppNumImplicitPrefixArgsAux 0 c.type
  | _ => return 0

def isFullyImplicitlyInstantiatedApp (x : Expr) : MetaM Bool :=
  return x.isApp && x.getAppNumArgs == (←getAppNumImplicitPrefixArgs x)

def getAppArgsUpToImplicitPrefix (x : Expr) : MetaM (Array Expr) :=
  return x.getAppArgs[←getAppNumImplicitPrefixArgs x:]

def ExprSubtermsM.queue (x : Expr) : ExprSubtermsM PUnit := do
  if ¬(←isFullyImplicitlyInstantiatedApp x) then
    modify λs => { s with pending := s.pending.push x }

def ExprSubtermsM.visit : Expr → ExprSubtermsM PUnit
| .app fn arg => do
  admit arg
  queue arg
  queue fn
| x@(.forallE _ _ _ _) => do
  let (_, _, x) ← forallMetaTelescope x
  admit x
  queue x
| x@(.lam _ _ _ _) => do
  let (_, _, x) ← lambdaMetaTelescope x
  admit x
  queue x
| x@(.letE _ _ value _ _) => do
  let (_, _, body) ← letMetaTelescope x
  admit value
  queue value
  admit body
  queue body
| _ => pure ()

partial def ExprSubtermsM.aux : ExprSubtermsM ExprSet := do
  let next? ← modifyGet λs => (s.pending.back?, { s with pending := s.pending.pop })
  if let some next := next? then
    visit next
    aux
  else
    return (←get).subterms

def exprSubterms (x : Expr) : MetaM ExprSet :=
  (do
    ExprSubtermsM.admit x
    ExprSubtermsM.queue x
    ExprSubtermsM.aux
  ).run' { subterms := ∅, pending := ∅ }


abbrev Sym := Name
abbrev SymMap := NameMap

def simpleExprSymbols (x : Expr) : NameSet := Id.run do
    let mut syms := NameSet.empty
    for sym in Lean.Expr.getUsedConstants x do
      if sym == `_neutral ∨ sym == `_obj ∨ sym == `_unreachable ∨ sym == `outParam ∨ sym == `namedPattern then
        continue
      else if sym == `Ne then
        syms := syms.insert `Not
        syms := syms.insert `Eq
      else
        syms := syms.insert sym
    return syms

def exprSymbols (x : Expr) : MetaM NameSet := do
  let mut syms := simpleExprSymbols x

  for sym in syms do
    if isStructure (←getEnv) sym then
      for parent in getAllParentStructures (←getEnv) sym do
        syms := syms.insert parent

  for subterm in ←exprSubterms x do
    let type ← inferType (←whnfD subterm)
    for sym in simpleExprSymbols type do
      syms := syms.insert sym

  return syms


def getPropifiedDef (c : ConstantInfo) : MetaM (Option Expr) := do
  let rhs ← match c.value? with
  | some value => pure value
  | none => return none

  forallTelescope c.type λxs eqType => do
    let lhs := Expr.const c.name $ c.levelParams.map .param

    let level ← match ←whnfD $ ←inferType eqType with
    | .sort u => pure u
    | x => throwError "getPropifiedDef {c.name} type of {eqType} is not a sort: {x}"

    let eq := Expr.const ``Eq [level] |>.app eqType |>.app lhs |>.app rhs
    mkForallFVars xs eq

def getFact (module : Name) (c : ConstantInfo) : MetaM (Option (Expr × Bool)) := do
  if excludeConstant module c then
    return none
  else if ←isProp c.type then
    return some (c.type, true)
  else
    match ←getPropifiedDef c with
    | some x => return some (x, false)
    | none => return some (c.type, false)
