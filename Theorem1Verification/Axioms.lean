/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.MainTheorem
import TraceableAgency.External.Relabeling

/-!
# Axiom audit boundary for trace-tempered choice, Theorem 1

This file deliberately declares no axiom, constant, theorem-interface parameter,
or other mathematical assumption.  The pure-record characterization used by the
paper is imported through the closed, kernel-checked theorem
`TraceableAgency.provedMainCharacterizationWithMoreover`.

The behavioral conditions A1--A8 of the trace-tempered theorem are predicates
on the primitive preference family.  They are formalized in `Statements.lean`;
they are hypotheses of the result, not Lean axioms.
-/

namespace TraceTemperedChoiceVerification

-- Intentionally empty: there are no extra axioms.

end TraceTemperedChoiceVerification
