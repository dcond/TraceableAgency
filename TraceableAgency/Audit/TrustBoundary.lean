import TraceableAgency.Audit.TrustBoundaryImports
import Lean.Util.FoldConsts

/-! # Exhaustive project trust boundary

The inventory is by defining module, not by declaration namespace. We reload
all project modules at the private .olean level with environment extensions
disabled, and inspect raw declaration types and bodies. In particular, this
check does not consult the imported axiom-summary extension.

This is an executable audit, not an additional mathematical assumption.
Separate fresh kernel replay remains the proof-checking step.
-/

open Lean Elab Command

namespace TraceableAgency.Audit.TrustBoundary

def declarationModule? (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

def isProjectModule (name : Name) : Bool :=
  name == `TraceableAgency || (`TraceableAgency).isPrefixOf name

def isAuditModule (name : Name) : Bool :=
  (`TraceableAgency.Audit).isPrefixOf name ||
  name == `TraceableAgency.Section3.Audit ||
  name == `TraceableAgency.Section4.Audit ||
  name == `TraceableAgency.Theorem1.MaterialCalibration.Audit ||
  name == `TraceableAgency.Theorem1.MaterialCalibration.RepresentationAudit

def allowedKernelAxioms : List Name :=
  [ ``propext, ``Classical.choice, ``Quot.sound ]

/-- Read the raw constants in both type and body, including opaque bodies.
Recursor rule bodies are included as an additional conservative check. -/
def directConstants (info : ConstantInfo) : NameSet :=
  let base := info.getUsedConstantsAsSet
  match info with
  | .recInfo val => val.rules.foldl (fun acc rule => acc ++ rule.rhs.getUsedConstantsAsSet) base
  | _ => base

/-- One traversal shared across every mathematical root. Missing constants
are errors; they are never silently treated as completed leaves. -/
def rawClosure (env : Environment) (roots : List Name) : IO NameSet := do
  let mut todo := roots
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    match todo with
    | [] => pure ()
    | name :: rest =>
      todo := rest
      if !seen.contains name then
        seen := seen.insert name
        let some info := env.checked.get.find? name
          | throw (IO.userError s!"missing raw kernel declaration: {name}")
        todo := (directConstants info).toList ++ todo
  return seen

private def sortedNames (xs : List Name) : List Name :=
  xs.mergeSort (fun a b => a.toString < b.toString)

/-- Audit every originating project declaration, including private helpers,
foreign namespaces, proof-valued definitions, and unused axiom declarations. -/
def report (env : Environment) : IO String := do
  let expected := TrustBoundaryImports.sourceModules
  for moduleName in expected do
    unless env.header.moduleNames.contains moduleName do
      throw (IO.userError s!"missing inventory module: {moduleName}")
  let mut projectCount := 0
  let mut theoremCount := 0
  let mut privateTheorems := 0
  let mut foreignTheorems := 0
  let mut roots : List Name := []
  let mut unsafeAudit : List Name := []
  let mut partialAudit : List Name := []
  let mut opaqueProject : List Name := []
  for (name, info) in env.constants do
    if let some moduleName := declarationModule? env name then
      if isProjectModule moduleName then
        projectCount := projectCount + 1
        if let .axiomInfo _ := info then
          throw (IO.userError s!"project axiom declaration, even if unused: {name} in {moduleName}")
        if info.isUnsafe then
          unless isAuditModule moduleName do
            throw (IO.userError s!"unsafe mathematical project declaration: {name} in {moduleName}")
          unsafeAudit := name :: unsafeAudit
        if info.isPartial then
          unless isAuditModule moduleName do
            throw (IO.userError s!"partial mathematical project declaration: {name} in {moduleName}")
          partialAudit := name :: partialAudit
        if let .opaqueInfo _ := info then
          opaqueProject := name :: opaqueProject
        if let .thmInfo _ := info then
          theoremCount := theoremCount + 1
          if name.isInternal then privateTheorems := privateTheorems + 1
          if !(`TraceableAgency).isPrefixOf name && !name.isInternal then
            foreignTheorems := foreignTheorems + 1
          roots := name :: roots
        else if !isAuditModule moduleName then
          roots := name :: roots
  let closure ← rawClosure env roots
  let mut axioms : List Name := []
  let mut quotients : List Name := []
  for name in closure do
    let some info := env.checked.get.find? name
      | throw (IO.userError s!"missing closure declaration: {name}")
    if info.isUnsafe || info.isPartial then
      throw (IO.userError s!"unsafe or partial declaration in mathematical closure: {name}")
    match info with
    | .axiomInfo _ =>
      axioms := name :: axioms
      unless allowedKernelAxioms.contains name do
        throw (IO.userError s!"unexpected raw axiom in mathematical closure: {name}")
    | .quotInfo _ => quotients := name :: quotients
    | _ => pure ()
  let modules := env.header.moduleNames.filter isProjectModule
  return s!"TRUST_BOUNDARY sources={expected.size} loadedProjectModules={modules.size} projectDeclarations={projectCount} theoremRoots={theoremCount} internalTheorems={privateTheorems} foreignNamespaceTheorems={foreignTheorems} mathematicalRoots={roots.length} closure={closure.size}\n" ++
    s!"TRUST_BOUNDARY_RAW_AXIOMS {sortedNames axioms}\n" ++
    s!"TRUST_BOUNDARY_QUOTIENT_PRIMITIVES {sortedNames quotients}\n" ++
    s!"TRUST_BOUNDARY_PROJECT_OPAQUE {sortedNames opaqueProject}\n" ++
    s!"TRUST_BOUNDARY_AUDIT_ONLY_UNSAFE {sortedNames unsafeAudit}\n" ++
    s!"TRUST_BOUNDARY_AUDIT_ONLY_PARTIAL {sortedNames partialAudit}\n"

run_cmd do
  -- withImportModules defaults to private .olean data and loadExts=false.
  -- Consequently imported proof bodies are present, and cached axiom metadata
  -- is not used by the inspection above.
  let result ← liftIO <| withImportModules
    #[{module := `TraceableAgency.Audit.TrustBoundaryImports}] {} report
  logInfo result

end TraceableAgency.Audit.TrustBoundary
