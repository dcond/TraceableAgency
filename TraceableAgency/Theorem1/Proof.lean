/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.Axioms
import TraceableAgency.Theorem1.PositiveBranchIncrement
import TraceableAgency.Theorem1.TheoremClosure

/-!
# Kernel proof of Trace-Tempered Choice v4, Theorem 1

All mathematical assumptions are the eight v4 behavioral hypotheses;
`Axioms.lean` declares no extra axiom.  The historical v3 entry point is kept
as a compatibility corollary.
-/

namespace TraceableAgency.Theorem1

universe u

/-- Historical v3 compatibility theorem. -/
theorem trace_tempered_choice_v3_theorem1 : Theorem1Statement.{u} := by
  exact theorem1StatementV3

end TraceableAgency.Theorem1

/-! The stable public v4 verification namespace used by the certificate. -/
namespace TraceTemperedChoiceVerification

universe u

/-- Theorem 1 of `trace_tempered_choice_v4`, including its same-witness
finite-block moreover clause. -/
theorem trace_tempered_choice_v4_theorem1 :
    TraceableAgency.Theorem1.Theorem1StatementV4.{u} := by
  exact TraceableAgency.Theorem1.theorem1StatementV4

end TraceTemperedChoiceVerification
