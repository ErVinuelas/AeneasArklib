import Lean
import Generated

/-!
Kernel-checked, definition-by-definition preservation of an extracted model.

Run with the candidate's Lake environment and HACHI_BASELINE_LEAN_PATH pointing
to the baseline project's .lake/build/lib/lean directory. Both Generated.olean
files must have been built from the retained extractor outputs using identical
dependencies. The command imports the baseline into a separate environment and
uses its compiled expressions directly; it does not reconstruct Rust semantics.

The equality for each definition uses the candidate's names for its dependencies.
Checking every definition and identical data declarations establishes preservation
by substitution through Lean's definition dependency graph. This proves neither
new ArkLib refinement claims nor physical allocation/OOM behaviour.
-/

open Lean Meta Elab Command

deriving instance BEq for Lean.InductiveVal

namespace HachiAllocationAudit

private def ownedByGenerated (env : Environment) (declName : Name) : Bool :=
  match env.getModuleIdxFor? declName with
  | some index => env.header.moduleNames[index]! == `Generated
  | none => false

private def generated (env : Environment) : List (Name × ConstantInfo) :=
  env.constants.toList.filter (fun (declName, _) => ownedByGenerated env declName)

private def sameFoundation : ConstantInfo → ConstantInfo → Bool
  | .axiomInfo a, .axiomInfo b => a == b
  | .defnInfo a, .defnInfo b => a == b
  | .thmInfo a, .thmInfo b => a == b
  | .opaqueInfo a, .opaqueInfo b => a == b
  | .inductInfo a, .inductInfo b => a == b
  | .ctorInfo a, .ctorInfo b => a == b
  | .recInfo a, .recInfo b => a == b
  | .quotInfo a, .quotInfo b =>
    a.toConstantVal == b.toConstantVal && match a.kind, b.kind with
      | .type, .type | .ctor, .ctor | .lift, .lift | .ind, .ind => true
      | _, _ => false
  | _, _ => false

elab "check_allocation_preservation" : command => do
  let some path ← IO.getEnv "HACHI_BASELINE_LEAN_PATH"
    | throwError "HACHI_BASELINE_LEAN_PATH must name the compiled baseline directory"
  unless ← (System.FilePath.mk path / "Generated.olean").pathExists do
    throwError "Baseline Generated.olean does not exist in {path}"
  let searchPath ← searchPathRef.get
  let baseline ← try
    searchPathRef.set (System.FilePath.mk path :: searchPath)
    importModules #[{ module := `Generated }] {} (trustLevel := 0)
  finally
    searchPathRef.set searchPath
  let candidate ← getEnv
  let oldItems := generated baseline
  let newItems := generated candidate
  unless !oldItems.isEmpty && oldItems.length == newItems.length do
    throwError "Generated declaration counts differ or baseline is empty"
  let mut definitions : Nat := 0
  let mut dataDeclarations : Nat := 0
  let mut theorems : Nat := 0
  let mut foundations : Nat := 0
  for (declName, info) in baseline.constants.toList do
    unless ownedByGenerated baseline declName do
      let some current := candidate.find? declName
        | throwError "Imported foundation is missing: {declName}"
      unless sameFoundation info current do
        throwError "Imported kernel declaration changed: {declName}"
      foundations := foundations + 1
  for (declName, oldInfo) in oldItems do
    let some newInfo := candidate.find? declName
      | throwError "Candidate is missing baseline declaration {declName}"
    unless ownedByGenerated candidate declName do
      throwError "Declaration ownership changed: {declName}"
    unless oldInfo.levelParams == newInfo.levelParams do
      throwError "Declaration universe parameters changed: {declName}"
    liftTermElabM do
      let signatureEq ← mkEq oldInfo.type newInfo.type
      let signatureProof ← mkEqRefl oldInfo.type
      addDecl (.thmDecl {
        «name» := `HachiAllocationAudit.signature ++ declName
        levelParams := oldInfo.levelParams
        type := signatureEq
        value := signatureProof
      })
    match oldInfo, newInfo with
    | .defnInfo old, .defnInfo new =>
      unless old.safety == .safe && new.safety == .safe do
        throwError "Non-safe definition: {declName}"
      liftTermElabM do
        let lhs := mkConst declName (old.levelParams.map Level.param)
        let proposition ← mkEq lhs old.value
        let proof ← mkEqRefl lhs
        -- addDecl sends the proposed Eq.refl proof to the kernel. A changed
        -- function that is not definitionally equal to its old body fails here.
        addDecl (.thmDecl {
          «name» := `HachiAllocationAudit.preserved ++ declName
          levelParams := old.levelParams
          type := proposition
          value := proof
        })
      definitions := definitions + 1
    | .inductInfo old, .inductInfo new =>
      unless old == new do throwError "Inductive declaration changed: {declName}"
      dataDeclarations := dataDeclarations + 1
    | .ctorInfo old, .ctorInfo new =>
      unless old == new do throwError "Constructor changed: {declName}"
      dataDeclarations := dataDeclarations + 1
    | .recInfo old, .recInfo new =>
      unless old == new do throwError "Recursor changed: {declName}"
      dataDeclarations := dataDeclarations + 1
    | .thmInfo old, .thmInfo new =>
      liftTermElabM do
        addDecl (.thmDecl {
          «name» := `HachiAllocationAudit.preservedTheorem ++ declName
          levelParams := old.levelParams
          type := old.type
          value := mkConst declName (new.levelParams.map Level.param)
        })
      theorems := theorems + 1
    | _, _ => throwError "Unexpected declaration kind (including axiom/opaque): {declName}"
  logInfo (m!"Kernel checked {definitions} definition-preservation equations; " ++
    m!"{dataDeclarations} identical data declarations; {theorems} preserved theorem types; " ++
    m!"{oldItems.length} declarations audited; " ++
    m!"{foundations} imported kernel declarations identical.")

end HachiAllocationAudit

check_allocation_preservation
