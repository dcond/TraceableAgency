/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.Proof

/-!
# Kernel axiom report for the paper-faithful public route

These commands are intentionally part of the verification target.  They print
the kernel assumptions of the direct pure-trace endpoint, the public main
characterization, and the exact formalization of Theorem 1.
-/

#print axioms TraceableAgency.MIRep_of_TraceAxioms_paperReduction
#print axioms TraceableAgency.provedMainCharacterizationWithMoreover
#print axioms TraceTemperedChoiceVerification.trace_tempered_choice_v3_theorem1
