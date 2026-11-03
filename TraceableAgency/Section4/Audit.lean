import TraceableAgency.Section4
import TraceableAgency.Section3.Audit

/-! # Recursive foundation and dependency audit for Section 4

Every theorem in the public Section4 namespace is a root, not only selected
headline statements. Fresh kernel replay also checks all imported declarations.
-/

open Lean Elab Command

namespace TraceableAgency.Section4.Audit

run_cmd do
  let env ← getEnv
  let mut roots : List Name := []
  for (name, info) in env.constants do
    if (`TraceableAgency.Section4).isPrefixOf name &&
        !((`TraceableAgency.Section4.Audit).isPrefixOf name) then
      if let .thmInfo _ := info then
        roots := name :: roots
  unless roots.length ≥ 200 do
    throwError m!"Section 4 audit unexpectedly found only {roots.length} theorems"
  let closure := Section3.Audit.declarationClosure env roots
  let old := Section3.Audit.excludedOldRoots.filter closure.contains
  logInfo m!"SECTION4_DEPENDENCIES roots={roots.length} closure={closure.size} oldRepresentationRoots={old.length}"
  unless old.isEmpty do
    throwError m!"Section 4 unexpectedly uses old representation endpoints: {old}"
  for root in roots do
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.toList.filter fun name =>
      !(Section3.Audit.allowedKernelAxioms.contains name)
    logInfo m!"SECTION4_AXIOMS root={root} axioms={axioms.toList} unexpected={unexpected.length}"
    unless unexpected.isEmpty do
      throwError m!"Section 4 foundation audit failed at {root}: {unexpected}"

end TraceableAgency.Section4.Audit

#check TraceableAgency.Section4.optimization_of_axioms
#check TraceableAgency.Section4.behavioral_elicitation_existsUnique_iff
#check TraceableAgency.Section4.BernoulliTechnology.exists_signal_compensation_bounds
