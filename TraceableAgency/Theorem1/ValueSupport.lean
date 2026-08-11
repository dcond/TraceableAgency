/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.Benchmark
import TraceableAgency.Basic.SupportRestriction

/-!
# Numerical invariance under support restriction

Deleting null action rows preserves both terms in the trace-tempered value.
These identities are the numerical half of the boundary-prior reduction; the
behavioral half is proved in `SupportDummy`.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

theorem expectedPayoffUtility_restrictToSupport
    {O A R : Type u}
    [Fintype O] [Fintype A] [DecidableEq A] [Nonempty A] [Fintype R]
    (u : O → ℝ) (q : TraceableAgency.Dist A)
    (K : Channel A (O × R)) :
    expectedPayoffUtility u q.restrictToSupport
        (Channel.restrictToSupport K q) =
      expectedPayoffUtility u q K := by
  rw [expectedPayoffUtility_eq_marginal,
    expectedPayoffUtility_eq_marginal,
    Channel.outcomeMarginal_restrictToSupport]

theorem traceTemperedValue_restrictToSupport
    {O A R : Type u}
    [Fintype O] [Fintype A] [DecidableEq A] [Nonempty A] [Fintype R]
    (u : O → ℝ) (lambda : ℝ)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    traceTemperedValue u lambda q.restrictToSupport
        (Channel.restrictToSupport K q) =
      traceTemperedValue u lambda q K := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_restrictToSupport,
    mutualInfo_restrictToSupport]

end TraceableAgency.Theorem1
