/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.Axioms
import TraceableAgency.Theorem1.PositiveBranchIncrement
import TraceableAgency.Theorem1.TheoremClosure

/-!
# Kernel proof of Trace-Tempered Choice, Theorem 1

All mathematical assumptions are the eight behavioral hypotheses;
`Axioms.lean` declares no extra axiom.
-/

/-! The stable public verification namespace used by the certificate. -/
namespace TraceTemperedChoiceVerification

universe u

/-- Theorem 1 of `trace_tempered_choice_v10`, including its same-witness
finite-block moreover clause. -/
theorem trace_tempered_choice_v10_theorem1 :
    TraceableAgency.Theorem1.Theorem1StatementV10.{u} := by
  exact TraceableAgency.Theorem1.theorem1StatementV10

end TraceTemperedChoiceVerification
