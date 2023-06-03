-- Author: Alistair Geesing

import Lean
import Hammer.PS.Common
import Hammer.PS.MaSh.Common
import Hammer.PS.ConstantFilter

namespace Hammer.PS

open Lean
open Hammer.PS.MaSh


structure PState where
  moduleIdxs : HashMap Name UInt64
  moduleNames : Array Name
  moduleMtimes : Array IO.FS.SystemTime
  moduleImportss : Array (Array UInt64)
  moduleFactss : Array (Array UInt64)

  factIdxs : HashMap (UInt64 × Name) UInt64
  factNames : Array Name

  symbolIdxs : HashMap Sym UInt64
  symbolValues : Array Sym
  symbolOrders : Array UInt8
  symbolFreqs : Array UInt64

  featureIdxs : HashMap Feature UInt64
  featureValues : Array Feature
  featureFreqs : Array UInt64

  factDepss : Array (Array UInt64)
  factSymbolss : Array (Array UInt64)
  factFeaturess : Array (Array UInt64)
  factAsDepFreqs : Array UInt64
  factAsDepOfFeatureFreqss : Array (HashMap UInt64 UInt64)

-- bump the version whenever the fields of PState are changed
def PState.version : UInt64 := 0

instance : EmptyCollection PState where
  emptyCollection := {
    moduleIdxs := ∅
    moduleNames := ∅
    moduleMtimes := ∅
    moduleImportss := ∅
 
    factIdxs := ∅
    factNames := ∅
    moduleFactss := ∅

    symbolIdxs := ∅
    symbolValues := ∅
    symbolOrders := ∅
    symbolFreqs := ∅

    featureIdxs := ∅
    featureValues := ∅
    featureFreqs := ∅

    factDepss := ∅
    factSymbolss := ∅
    factFeaturess := ∅

    factAsDepFreqs := ∅
    factAsDepOfFeatureFreqss := ∅
  }


def PState.factCount (pstate : PState) : Nat := pstate.factNames.size
def PState.featureCount (pstate : PState) : Nat := pstate.featureValues.size


structure FactExtendedFeaturessCache where
  factExtendedFeaturessCache? : Option (Array (RBTree UInt64 Ord.compare))

instance : Inhabited FactExtendedFeaturessCache where
  default := { factExtendedFeaturessCache? := none }

abbrev PStateM := StateRefT PState $ StateRefT FactExtendedFeaturessCache MetaM

def getPState [MonadLiftT PStateM m] : m PState := liftM (get : PStateM PState)


namespace ModifiedModulesImpl

structure Context where
  moduleMap : ModuleMap

structure State where
  modifiedModules : NameSet
  pending : NameSet

abbrev ModifiedModulesM := ReaderT Context $ StateRefT State PStateM

def popNext? : ModifiedModulesM (Option Name) := do
  match (←get).pending.min with
  | none => return none
  | some next => do
    modify λs => { s with pending := s.pending.erase next }
    return next

def isModified (module : Name) : ModifiedModulesM Bool := do
  match (←getPState).moduleIdxs.find? module with
  | none => return true
  | some moduleIdx => do
    -- These calls should not fail. When modules are imported their olean files are created.
    -- If creation of olean files fails we should not be able to reach this point.
    let oleanPath ← findOLean module
    let mdata ← oleanPath.metadata
    return mdata.modified > (←getPState).moduleMtimes[moduleIdx.toNat]!

partial def aux : ModifiedModulesM NameSet := do
  let module ← match ←popNext? with
  | some module => pure module
  | none => return (←get).modifiedModules

  if ←isModified module then
    let moduleData := (←read).moduleMap.find! module
    modify λs => { s with
      modifiedModules := s.modifiedModules.insert module
      pending := moduleData.imports.foldl
        (λpending importt => if s.modifiedModules.contains importt.module
          then pending
          else pending.insert importt.module)
        s.pending
    }

  aux

end ModifiedModulesImpl

def getModifiedImports (moduleMap : ModuleMap) (imports : NameSet) : PStateM NameSet := do
  ModifiedModulesImpl.aux { moduleMap }
    |>.run' { modifiedModules := ∅, pending := imports }


def getExprSymbols [Monad m] [MonadEnv m] (x : Expr) : m NameSet := do
  let mut syms := ∅
  
  for sym in getUsedConstantsTR x do
    if sym == `_neutral ∨ sym == `_obj ∨ sym == `_unreachable ∨ sym == `outParam ∨ sym == `namedPattern then
      continue
    else if sym == `Ne then
      syms := syms.insert `Not
      syms := syms.insert `Eq
    else
      syms := syms.insert $ getUnaliased (←getEnv) sym

  return syms


def PState.findFactIdx? (env : Environment) (pstate : PState) (factName : Name) : Option UInt64 := Id.run $ OptionT.run do
  let moduleEnvIdx ← env.const2ModIdx.find? factName
  let moduleName := env.header.moduleNames[moduleEnvIdx.toNat]!
  let moduleIdx ← pstate.moduleIdxs.find? moduleName
  pstate.factIdxs.find? (moduleIdx, factName)

def PStateM.findFactIdx? (factName : Name) : PStateM (Option UInt64) :=
  return (←getPState).findFactIdx? (←getEnv) factName


def getFactDeps [Monad m] [MonadEnv m] (constantInfo : ConstantInfo) (isProp : Bool) : m NameSet := do
  if !isProp then
    return ∅

  let value ← match constantInfo.value? with
  | some value => pure value
  | none => return ∅

  let symbols ← getExprSymbols value
  let symbols := symbols.toArray
  let symbols := symbols.filter (. != constantInfo.name)
  return symbols.foldl .insert ∅


def PStateM.consolidateFactDeps (factDeps : NameSet) : PStateM (Array UInt64) := do
  factDeps.foldM
    (λfactDeps factDep => do
      match ←findFactIdx? factDep with
      | some factIdx => return factDeps.push factIdx
      | none => return factDeps
      )
    ∅


def modulifiedSuffix : String := "$$HammerPSModulified"

def modulifySymbol (moduleName : Name) : Name :=
  .str moduleName modulifiedSuffix

def isModulifiedSymbol : Name → Bool
| .str _ s => s == modulifiedSuffix
| _ => false


def getTypeOrder' : Expr → Nat
| .forallE _ a b _ => Nat.max (getTypeOrder' a + 1) (getTypeOrder' b)
| .app a b => Nat.max (getTypeOrder' a) (getTypeOrder' b)
| .lam _ a b _ => Nat.max (getTypeOrder' a) (getTypeOrder' b)
| .letE _ a b c _ => Nat.max (Nat.max (getTypeOrder' a) (getTypeOrder' b)) (getTypeOrder' c)
| .proj _ _ a => getTypeOrder' a
| _ => 0

def getTypeOrder (sym : Name) : PStateM UInt8 := do
  if isModulifiedSymbol sym then
    return 0

  let type ← match (←getEnv).find? sym with
  | some c => pure c.type
  | none => do panic! (←m!"Couldn't find constant for symbol {sym}".toString)

  let order := getTypeOrder' type
  if order >= 256 then
    panic! (←m!"Order of symbol {sym} type `{type}` does not fit in a UInt8".toString)
  return order.toUInt8


def getFactSymbols' (moduleName : Name) (goalName? : Option Name) (factType : Expr) : MetaM NameSet := do
  let mut syms ← getExprSymbols factType

  syms := syms.insert $ modulifySymbol moduleName
  if let some goalName := goalName? then
    for prefixx in prefixesOfName goalName.getPrefix do
      syms := syms.insert $ modulifySymbol prefixx

  for sym in syms do
    if isStructure (←getEnv) sym then
      for parent in getAllParentStructures (←getEnv) sym do
        syms := syms.insert parent

  for subterm in ←exprSubterms factType do
    let type ← try
      Lean.Meta.inferType subterm
    catch _ =>
      try
        Lean.Meta.inferType $ ←Lean.Meta.whnfD subterm
      catch _ =>
        continue
    for sym in simpleExprSymbols type do
      syms := syms.insert sym

  let env ← getEnv
  return syms
    |>.toArray
    |>.filter env.contains
    |>.foldl NameSet.insert ∅

def getFactSymbols (moduleName : Name) (goalName? : Option Name) (fact : Expr) : MetaM NameSet :=
  getFactSymbols' moduleName goalName? fact


def PStateM.findOrAddSymbol (sym : Sym) : PStateM UInt64 := do
  if let some symbolIdx := (←getPState).symbolIdxs.find? sym then
    return symbolIdx
  
  let symbolOrder ← getTypeOrder sym

  let symbolIdx := (←getPState).symbolValues.size.toUInt64
  modify λs => { s with
    symbolIdxs := s.symbolIdxs.insert sym symbolIdx
    symbolValues := s.symbolValues.push sym
    symbolOrders := s.symbolOrders.push symbolOrder
    symbolFreqs := s.symbolFreqs.push 0
  }
  return symbolIdx

def PStateM.consolidateFactSymbols (factSymbols : NameSet) : PStateM (Array UInt64) :=
  factSymbols.foldM
    (λfactSymbols sym => return factSymbols.push $ ←findOrAddSymbol sym)
    ∅


def PStateM.findOrAddFeature (feature : Feature) : PStateM UInt64 := do
  if let some featureIdx := (←getPState).featureIdxs.find? feature then
    return featureIdx
  
  let featureIdx := (←getPState).featureValues.size.toUInt64
  modify λs => { s with
    featureIdxs := s.featureIdxs.insert feature featureIdx
    featureValues := s.featureValues.push feature
    featureFreqs := s.featureFreqs.push 0
  }
  return featureIdx

def PStateM.consolidateFactFeatures (factFeatures : FeatureSet) : PStateM (Array UInt64) :=
  factFeatures.foldM
    (λfactFeatures feature => return factFeatures.push $ ←findOrAddFeature feature)
    ∅


def PStateM.addFact
  (moduleName : Name)
  (moduleIdx : UInt64)
  (c : ConstantInfo)
  : PStateM (Option (ConstantInfo × UInt64 × Option (Expr × Bool)))
:= do
  if let some factIdx := (←get).factIdxs.find? (moduleIdx, c.name) then
    return some (c, factIdx, none)
  
  let (fact, isProp) ← match ←getFact moduleName c with
  | some fact => pure fact
  | none => return none

  let factIdx := (←get).factNames.size.toUInt64
  modify λs => { s with
    factIdxs := s.factIdxs.insert (moduleIdx, c.name) factIdx
  }
  modify λs => { s with
    factNames := s.factNames.push c.name
  }
  modify λs => { s with
    factDepss := s.factDepss.push ∅
  }
  modify λs => { s with
    factSymbolss := s.factSymbolss.push ∅
  }
  modify λs => { s with
    factFeaturess := s.factFeaturess.push ∅
  }
  modify λs => { s with
    factAsDepFreqs := s.factAsDepFreqs.push 0
  }
  modify λs => { s with
    factAsDepOfFeatureFreqss := s.factAsDepOfFeatureFreqss.push ∅
  }
  return some (c, factIdx, (fact, isProp))


def PState.addFact
  (pstate : PState)
  (moduleName : Name)
  (moduleIdx : UInt64)
  (c : ConstantInfo)
  : MetaM (PState × Option (ConstantInfo × UInt64 × Option (Expr × Bool)))
:= do
  let (r, pstate) ← PStateM.addFact moduleName moduleIdx c |>.run pstate |>.run' default
  return (pstate, r)


def PStateM.addFacts
  (moduleName : Name)
  (moduleIdx : UInt64)
  (constants : Array ConstantInfo)
  : PStateM (Array (ConstantInfo × UInt64 × Option (Expr × Bool)))
:= constants.filterMapM $ addFact moduleName moduleIdx


def PStateM.learnFact
  (moduleName : Name)
  (constantInfo : ConstantInfo)
  (isProp : Bool)
  (fact : Expr)
  (factIdx : UInt64)
  (factSymbols : Option NameSet := none)
  (factFeatures : Option FeatureSet := none)
  : PStateM PUnit
:= do
  let factDeps ← getFactDeps constantInfo isProp
  let factDeps ← consolidateFactDeps factDeps

  let factSymbols ← match factSymbols with
  | some factSymbols => pure factSymbols
  | none => getFactSymbols moduleName constantInfo.name fact
  let factSymbols ← consolidateFactSymbols factSymbols

  -- let factProofSymbols? ← match (isProp, constantInfo.value?) with
  -- | (true, some proof) => pure $ some $ ←consolidateFactSymbols $ ←getFactSymbols moduleName proof
  -- | _ => pure none

  let factFeatures ← match factFeatures with
  | some factFeatures => pure factFeatures
  | none => getFactFeatures moduleName constantInfo fact
  let factFeatures ← consolidateFactFeatures factFeatures

  -- field updates are split between separate modifies
  -- to ensure that field values are exclusive (/not unnecessarily copied)
  modify λs => { s with
    factDepss := s.factDepss.set! factIdx.toNat factDeps
  }
  modify λs => { s with
    factSymbolss := s.factSymbolss.set! factIdx.toNat factSymbols
  }
  modify λs => { s with
    factFeaturess := s.factFeaturess.set! factIdx.toNat factFeatures
  }
  modify λs => { s with
    factAsDepFreqs := Id.run do
      let mut factAsDepFreqs := s.factAsDepFreqs

      factAsDepFreqs := factAsDepFreqs.set! factIdx.toNat 1

      for factDep in factDeps do
        factAsDepFreqs := factAsDepFreqs.modify factDep.toNat (. + 1)

      return factAsDepFreqs
  }
  modify λs => { s with
    factAsDepOfFeatureFreqss := Id.run do
      let mut factAsDepOfFeatureFreqss := s.factAsDepOfFeatureFreqss

      factAsDepOfFeatureFreqss := factAsDepOfFeatureFreqss.set! factIdx.toNat
        $ factFeatures.foldl (.insert . . 1) ∅
      
      for factDep in factDeps do
        factAsDepOfFeatureFreqss := factAsDepOfFeatureFreqss.modify factDep.toNat
          $ factFeatures.foldl (λdepAsDepOfFeatureFreqs factFeature =>
            depAsDepOfFeatureFreqs.insert factFeature
              $ depAsDepOfFeatureFreqs.findD factFeature 0 + 1)

      return factAsDepOfFeatureFreqss
  }
  modify λs => { s with
    symbolFreqs := Id.run do
      let mut symbolFreqs := s.symbolFreqs

      for factSymbol in factSymbols do
        symbolFreqs := symbolFreqs.modify factSymbol.toNat (. + 1)
      
      -- if let some factProofSymbols := factProofSymbols? then
      --   for proofSymbol in factProofSymbols do
      --     symbolFreqs := symbolFreqs.modify proofSymbol.toNat (. + 1)

      return symbolFreqs
  }
  modify λs => { s with
    featureFreqs := Id.run do
      let mut proofFeatures := (∅ : HashSet UInt64)
      proofFeatures := factFeatures.foldl .insert proofFeatures
      for factDep in factDeps do
        let depFeatures := s.factFeaturess[factDep.toNat]!
        proofFeatures := depFeatures.foldl .insert proofFeatures
      
      proofFeatures.fold
        (λfeatureFreqs proofFeature => featureFreqs.modify proofFeature.toNat (. + 1))
        s.featureFreqs
  }

def PState.learnFact
  (pstate : PState)
  (moduleName : Name)
  (constantInfo : ConstantInfo)
  (isProp : Bool)
  (fact : Expr)
  (factIdx : UInt64)
  (factSymbols : Option NameSet := none)
  (factFeatures : Option FeatureSet := none)
  : MetaM PState
:= do
  let ((), pstate) ← PStateM.learnFact moduleName constantInfo isProp fact factIdx factSymbols factFeatures |>.run pstate |>.run' default
  return pstate


def PStateM.freshModule (moduleName : Name) (moduleMtime : IO.FS.SystemTime) (moduleImports : Array Import) (strictImports : Bool := true) : PStateM UInt64 := do
  let moduleImports ← moduleImports
    |>.filterMapM (λimportt => do
      match (←get).moduleIdxs.find? importt.module with
      | some importIdx => return importIdx
      | none =>
          if strictImports then
            throwError "Couldn't find module index for import {importt.module} of module {moduleName}"
          else
            return none)

   match (←get).moduleIdxs.find? moduleName with
  | some moduleIdx => do
      modify λs => { s with
        moduleMtimes := s.moduleMtimes.set! moduleIdx.toNat moduleMtime
        moduleImportss := s.moduleImportss.set! moduleIdx.toNat moduleImports
        moduleFactss := s.moduleFactss.set! moduleIdx.toNat ∅
      }
      pure moduleIdx
  | none => modifyGet λs => 
      let moduleIdx := s.moduleNames.size.toUInt64
      (moduleIdx, { s with
        moduleIdxs := s.moduleIdxs.insert moduleName moduleIdx
        moduleNames := s.moduleNames.push moduleName
        moduleMtimes := s.moduleMtimes.push moduleMtime
        moduleImportss := s.moduleImportss.push moduleImports
        moduleFactss := s.moduleFactss.push ∅
      })


def PStateM.freshImportedModule (moduleName : Name) (moduleData : ModuleData) : PStateM UInt64 := do
  let moduleOLean ← findOLean moduleName
  let moduleOLeanMetadata ← moduleOLean.metadata
  let moduleMtime := moduleOLeanMetadata.modified

  freshModule moduleName moduleMtime moduleData.imports

def PState.freshImportedModule (pstate : PState) (moduleName : Name) (moduleData : ModuleData) : MetaM (PState × UInt64) := do
  let (moduleIdx, pstate) ← PStateM.freshImportedModule moduleName moduleData |>.run pstate |>.run' default
  return (pstate, moduleIdx)

def PStateM.updateModuleConstants
  (moduleName : Name)
  (moduleIdx : UInt64)
  (moduleConstants : Array ConstantInfo)
  (moduleSymbolss? : Option (NameMap NameSet) := none)
  (moduleFeaturess? : Option (NameMap FeatureSet) := none)
  : PStateM PUnit
:= do
  let moduleFacts ← addFacts moduleName moduleIdx moduleConstants

  for (c, factIdx, fact?) in moduleFacts do
    let (fact, isProp) ← match fact? with
    | some fact => pure fact
    | none => continue

    let factSymbols? ← moduleSymbolss?.mapM λmoduleSymbolss => do
      match moduleSymbolss.find? c.name with
      | some r => pure r
      | none => throwError "Couldn't find cached symbols for {c.name} in module {moduleName}"
    let factFeatures? ← moduleFeaturess?.mapM λmoduleFeaturess => do
      match moduleFeaturess.find? c.name with
      | some r => pure r
      | none => throwError "Couldn't find cached features for {c.name} in module {moduleName}"
    learnFact moduleName c isProp fact factIdx factSymbols? factFeatures?

  modify λs => { s with
    moduleFactss := s.moduleFactss.set! moduleIdx.toNat $ moduleFacts.map λ(_, factIdx, _) => factIdx
  }

def PStateM.updateImportedModule
  (moduleName : Name)
  (moduleData : ModuleData)
  (moduleSymbolss : Option (NameMap NameSet) := none)
  (moduleFeaturess : Option (NameMap FeatureSet) := none)
  : PStateM PUnit
:= do
  let moduleIdx ← PStateM.freshImportedModule moduleName moduleData
  updateModuleConstants moduleName moduleIdx moduleData.constants moduleSymbolss moduleFeaturess

def PState.updateImportedModule
  (pstate : PState)
  (moduleName : Name)
  (moduleData : ModuleData)
  (moduleSymbolss : Option (NameMap NameSet) := none)
  (moduleFeaturess : Option (NameMap FeatureSet) := none)
  : MetaM PState
:= do
  let ((), pstate) ← PStateM.updateImportedModule moduleName moduleData moduleSymbolss moduleFeaturess |>.run pstate |>.run' default
  return pstate

def PStateM.updateImports (imports : NameSet) : PStateM Bool := do
  let moduleMap := getModuleMap (←getEnv)
  let sortedModules ← ofExcept $ topologicalSort $ getModuleDAG moduleMap
  let modifiedImports ← getModifiedImports moduleMap imports

  for moduleName in sortedModules do
    if ¬modifiedImports.contains moduleName then
      continue
    let moduleData := moduleMap.find! moduleName
    updateImportedModule moduleName moduleData

  return !modifiedImports.isEmpty


def fakeMtime := IO.FS.SystemTime.mk 0 0


def PStateM.haveModifiedImports (moduleImports : Array Import) : PStateM Bool := do
  let moduleImportsSet := moduleImports
    |>.map Import.module
    |>.foldl .insert (∅ : NameSet)

  let moduleMap := getModuleMap (←getEnv)
  let modifiedImports ← getModifiedImports moduleMap moduleImportsSet

  return !modifiedImports.isEmpty

def PState.haveModifiedImports (pstate : PState) (moduleImports : Array Import) : MetaM Bool := do
  PStateM.haveModifiedImports moduleImports |>.run' pstate |>.run' default


def PStateM.updateMainModule
  (moduleName : Name)
  (moduleImports : Array Import)
  (moduleConstants : Array ConstantInfo)
  : PStateM UInt64
:= do
  let moduleImportsSet := moduleImports
    |>.map Import.module
    |>.foldl .insert (∅ : NameSet)

  let moduleMap := getModuleMap (←getEnv)
  let modifiedImports ← getModifiedImports moduleMap moduleImportsSet

  if !modifiedImports.isEmpty then
    logWarning m!"Some imported modules have changed. Not all facts may have been learned. To incorporate the changes in the premise selection state, place the {`Hammer.PS.learn} command at the top level of the current file (e.g. directly below the import commands). Changes to the current module are automatically incorporated."

  let moduleIdx ← freshModule moduleName fakeMtime moduleImports (strictImports := false)
  updateModuleConstants moduleName moduleIdx moduleConstants
  return moduleIdx

def PState.updateMainModule
  (pstate : PState)
  (moduleName : Name)
  (moduleImports : Array Import)
  (moduleConstants : Array ConstantInfo)
  : MetaM (PState × UInt64)
:= do
  let (moduleIdx, pstate) ← PStateM.updateMainModule moduleName moduleImports moduleConstants |>.run pstate |>.run' default
  return (pstate, moduleIdx)


namespace CandidateFacts

structure State where
  acc : Array UInt64
  visitedModuleIdxs : HashSet UInt64
  pendingModuleIdxs : Array UInt64

abbrev CandidateFactsM := ReaderT PState $ StateM State

def candidateFactsIter : CandidateFactsM (Option (Array UInt64)) := do
  let moduleIdx ← match ←modifyGet λs => (s.pendingModuleIdxs.back?, { s with pendingModuleIdxs := s.pendingModuleIdxs.pop }) with
  | some moduleIdx => pure moduleIdx
  | none => return (←get).acc

  let moduleFacts := (←read).moduleFactss[moduleIdx.toNat]!
  modify λs => { s with acc := s.acc ++ moduleFacts }
  let moduleImports := (←read).moduleImportss[moduleIdx.toNat]!
  let moduleImports := moduleImports.filter (!(←get).visitedModuleIdxs.contains .)
  modify λs => { s with pendingModuleIdxs := s.pendingModuleIdxs ++ moduleImports }
  modify λs => { s with visitedModuleIdxs := moduleImports.foldl .insert s.visitedModuleIdxs }

  return none

partial def candidateFactsAux : CandidateFactsM (Array UInt64) := do
  match ←candidateFactsIter with
  | some r => return r
  | none => candidateFactsAux

end CandidateFacts


def PState.candidateFacts (pstate : PState) (mainModuleIdx : UInt64) : Array UInt64 :=
  CandidateFacts.candidateFactsAux pstate |>.run' { acc := ∅, visitedModuleIdxs := ∅, pendingModuleIdxs := #[mainModuleIdx] }


namespace DiskPersistence

inductive Error
| toolchainVersionChanged
| pstateVersionChanged

private unsafe def castPStateVersionToEnvExtensionEntry : UInt64 → EnvExtensionEntry := unsafeCast
private unsafe def castEnvExtensionEntryToPStateVersion : EnvExtensionEntry → UInt64 := unsafeCast

private unsafe def castPStateToEnvExtensionEntry : PState → EnvExtensionEntry := unsafeCast
private unsafe def castEnvExtensionEntryToPState : EnvExtensionEntry → PState := unsafeCast

def leanToolchainPath (pstatePath : System.FilePath) : System.FilePath :=
  pstatePath.withFileName $ pstatePath.fileName.get! ++ ".lean-toolchain"

unsafe def savePState (path : System.FilePath) (pstate : PState) : IO PUnit := do
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile (leanToolchainPath path) Lean.versionString
  saveModuleData path `PState {
    imports := ∅
    constNames := ∅
    constants := ∅
    extraConstNames := ∅
    entries := #[
      (`PState.version, #[castPStateVersionToEnvExtensionEntry PState.version]),
      (`PState, #[castPStateToEnvExtensionEntry pstate])
    ]
  } 

unsafe def readPState (path : System.FilePath) : IO (Except Error (PState × CompactedRegion)) := do
  let leanToolchainVersion ← IO.FS.readFile (leanToolchainPath path)
  if leanToolchainVersion != Lean.versionString then
    return .error .toolchainVersionChanged

  let (moduleData, compactedRegion) ← readModuleData path
  match moduleData.entries with
  | #[(`PState.version, #[version]), (`PState, #[pstate])] => do
    let version := castEnvExtensionEntryToPStateVersion version
    if version == PState.version then
      return .ok (castEnvExtensionEntryToPState pstate, compactedRegion)
    else
      return .error .pstateVersionChanged
  | _ => throw $ .userError (←m!"Expected PState in olean file at `{path}`".toString)

def resetPState (path : System.FilePath) : IO PUnit := do
  if ←path.pathExists then
    IO.FS.removeFile path
  if ←(leanToolchainPath path).pathExists then
    IO.FS.removeFile (leanToolchainPath path)

end DiskPersistence

@[implemented_by DiskPersistence.savePState]
opaque savePState : System.FilePath → PState → IO PUnit

@[implemented_by DiskPersistence.readPState]
opaque readPState : System.FilePath → IO (Except DiskPersistence.Error (PState × CompactedRegion))

@[implemented_by DiskPersistence.resetPState]
opaque resetPState : System.FilePath → IO PUnit
