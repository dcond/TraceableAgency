import TraceableAgency.Section3
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

/-! # Recursive foundation and dependency audit for Section 3 -/

open Lean Elab Command

namespace TraceableAgency.Section3.Audit

partial def declarationClosure
    (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
      if seen.contains name then declarationClosure env rest seen
      else
        let seen := seen.insert name
        match env.find? name with
        | none => declarationClosure env rest seen
        | some info => declarationClosure env (info.getUsedConstantsAsSet.toList ++ rest) seen

def allowedKernelAxioms : List Name :=
  [ ``propext, ``Classical.choice, ``Quot.sound ]

def roots : List Name :=
  [ ``TraceableAgency.Section3.uniqueness_for_representation
  , ``TraceableAgency.Section3.uniqueness_of_axioms
  , ``TraceableAgency.Section3.traceTempered_parameters_unique
  , ``TraceableAgency.Section3.traceTempered_parameters_unique_of_common_anchors
  , ``TraceableAgency.Section3.normalized_trace_coefficient_unique
  , ``TraceableAgency.Section3.valueIndex_range
  , ``TraceableAgency.Theorem1.Section3.sign_trichotomy
  , ``TraceableAgency.Theorem1.Section3.negative_axioms_of_representation
  , ``TraceableAgency.Theorem1.Section3.neutral_axioms_of_representation
  , ``TraceableAgency.Theorem1.Section3.positive_trace_incompatible_negative_record
  , ``TraceableAgency.Section3.axioms_independent
  , ``TraceableAgency.Section3.no_axiom_implied_by_other_seven
  , ``TraceableAgency.Section3.Independence.noise_counterexample
  , ``TraceableAgency.Section3.Independence.noiseScore_eq
  , ``TraceableAgency.Section3.Independence.gini_counterexample
  , ``TraceableAgency.Section3.Independence.giniInformation_eq_gini_reduction
  , ``TraceableAgency.Section3.Independence.giniMerge_information
  , ``TraceableAgency.Section3.Independence.giniFair_reveal_information
  , ``TraceableAgency.Section3.Independence.satiation_counterexample
  ]

/-- The new results may reuse generic lemmas and the benchmark direction,
but the old preference-to-representation endpoints are not used. -/
def excludedOldRoots : List Name :=
  [ `TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1
  , `TraceableAgency.Theorem1.theorem1StatementV10
  , `TraceableAgency.Theorem1.theorem1V10Clauses
  , `TraceableAgency.pureTraceRepresentation_of_conditions
  , `TraceableAgency.provedPureTraceCharacterization
  , `TraceableAgency.provedPureTraceSufficiency
  ]

run_cmd do
  let env ← getEnv
  let closure := declarationClosure env roots
  let old := excludedOldRoots.filter closure.contains
  logInfo m!"SECTION3_DEPENDENCIES roots={roots.length} closure={closure.size} oldRepresentationRoots={old.length}"
  unless old.isEmpty do
    throwError m!"Section 3 unexpectedly uses old representation endpoints: {old}"
  for root in roots do
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.toList.filter fun name => !(allowedKernelAxioms.contains name)
    logInfo m!"SECTION3_AXIOMS root={root} axioms={axioms.toList} unexpected={unexpected.length}"
    unless unexpected.isEmpty do
      throwError m!"Section 3 foundation audit failed at {root}: {unexpected}"

end TraceableAgency.Section3.Audit

#check TraceableAgency.Section3.uniqueness_for_representation
#check TraceableAgency.Theorem1.Section3.sign_trichotomy
#check TraceableAgency.Section3.axioms_independent
#check TraceableAgency.Section3.Independence.gini_counterexample
#check TraceableAgency.Section3.Independence.satiation_counterexample
