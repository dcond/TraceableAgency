/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.PositiveBranchIncrement
import Theorem1Verification.TheoremClosure

/-!
# Kernel proof of Trace-Tempered Choice, Theorem 1

This file contains the single final theorem corresponding to
`trace_tempered_choice_v3`, Theorem 1.  All mathematical assumptions are the
behavioral hypotheses packaged in `TraceTemperedAxioms`; `Axioms.lean`
declares no extra axiom.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

universe u

/-- Theorem 1 of `trace_tempered_choice_v3`, including the same-witness finite
block moreover clause. -/
theorem trace_tempered_choice_v3_theorem1 : Theorem1Statement.{u} := by
  apply theorem1Statement_of_positiveBranchPayoffIncrement
  intro O _instFintype _instDecidableEq _hcard F h
  exact positiveBranchPayoffIncrementFormula F h

end TraceTemperedChoiceVerification
