/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.Proof
import TraceableAgency.External.GenericFaddeev
import Lean.Util.CollectAxioms

/-!
# Kernel axiom report for the paper-faithful public route

This module is intentionally part of the verification target.  It recursively
collects the kernel axioms of each listed public endpoint and fails the build
if an axiom outside the explicit Lean/Mathlib foundation whitelist appears.  The
`#print axioms` commands retain a human-readable report in the build log.
-/

open Lean Elab Command

namespace TraceTemperedChoiceVerification.PaperFaithfulAxiomAudit

def allowedKernelAxioms : List Name :=
  [ ``propext
  , ``Classical.choice
  , ``Quot.sound
  ]

def auditedRoots : List Name :=
  [ ``TraceableAgency.GenericFaddeev.provedClassicalFaddeevTheoremAssumptions
  , ``TraceableAgency.MIRep_of_TraceAxioms_paperReduction
  , ``TraceableAgency.SufficiencyStatement_of_Faddeev
  , ``TraceableAgency.provedMainCharacterizationWithMoreover
  , ``TraceTemperedChoiceVerification.trace_tempered_choice_v3_theorem1
  ]

run_cmd do
  for root in auditedRoots do
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.toList.filter fun name =>
      !(allowedKernelAxioms.contains name)
    logInfo m!"AXIOM_AUDIT root={root} axioms={axioms.toList} unexpected={unexpected.length}"
    unless unexpected.isEmpty do
      for name in unexpected do
        logError m!"UNEXPECTED_KERNEL_AXIOM root={root} axiom={name}"
      throwError m!"paper-faithful axiom audit failed at {root}"

end TraceTemperedChoiceVerification.PaperFaithfulAxiomAudit

#print axioms TraceableAgency.GenericFaddeev.provedClassicalFaddeevTheoremAssumptions
#print axioms TraceableAgency.MIRep_of_TraceAxioms_paperReduction
#print axioms TraceableAgency.SufficiencyStatement_of_Faddeev
#print axioms TraceableAgency.provedMainCharacterizationWithMoreover
#print axioms TraceTemperedChoiceVerification.trace_tempered_choice_v3_theorem1
