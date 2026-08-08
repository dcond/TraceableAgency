/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.GlobalTraceScale
import Theorem1Verification.Benchmark

/-!
# The normalized value on a singleton action alphabet

When the action type is a subsingleton, every posterior is the prior and every
channel carries zero mutual information.  Its marked terminal law therefore
reduces exactly to the induced payoff lottery.  This file records that
degenerate case separately from the nontrivial branch-scale argument.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

variable {O A R : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- The payoff marginal induced by a joint payoff-record channel. -/
noncomputable def inducedPayoffLottery
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    TraceableAgency.Dist O where
  prob := fun o ↦ ∑ r : R, Channel.outcomeMarginal K q (o, r)
  nonneg := by
    intro o
    exact Finset.sum_nonneg fun r _ ↦ (Channel.outcomeMarginal K q).nonneg (o, r)
  sum_eq_one := by
    rw [← Fintype.sum_prod_type]
    exact (Channel.outcomeMarginal K q).sum_eq_one

@[simp]
theorem inducedPayoffLottery_apply
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) (o : O) :
    inducedPayoffLottery q K o =
      ∑ r : R, Channel.outcomeMarginal K q (o, r) :=
  rfl

/-- On a singleton action alphabet, the whole marked law is just its payoff
marginal with the unchanged prior attached to every payoff. -/
theorem sameMarkedTerminalLaw_inducedPayoffLottery_of_subsingleton
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    SameMarkedTerminalLaw q (markedExperimentOfChannel K)
      (markedPayoffLotteryExperiment (inducedPayoffLottery q K)) := by
  classical
  intro phi
  change markedChannelIntegral q K phi = _
  rw [markedTerminalIntegral_markedPayoffLottery]
  unfold markedChannelIntegral payoffLotteryExpected
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro o _ho
  simp only [inducedPayoffLottery_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _hr
  have hpost : Channel.posterior K q (o, r) = q :=
    TraceableAgency.Dist.eq_of_subsingleton _ _
  rw [hpost]

/-- Mutual information is zero when the action alphabet is a subsingleton. -/
theorem mutualInfo_eq_zero_of_subsingleton
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    mutualInfo q K = 0 := by
  classical
  let a : A := Classical.choice (inferInstance : Nonempty A)
  have hq : q = TraceableAgency.Dist.pure a :=
    TraceableAgency.Dist.eq_of_subsingleton _ _
  rw [mutualInfo_eq_entropy_sub_posteriorLawIntegral]
  have hpost : ∀ z : O × R, Channel.posterior K q z = q := by
    intro z
    exact TraceableAgency.Dist.eq_of_subsingleton _ _
  unfold posteriorLawIntegral
  simp_rw [hpost]
  rw [← Finset.sum_mul, (Channel.outcomeMarginal K q).sum_eq_one,
    one_mul, sub_self]

/-- Expected payoff under the channel equals expected payoff under its induced
payoff lottery. -/
theorem expectedPayoffUtility_inducedPayoffLottery
    (v : O → ℝ) (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    expectedPayoffUtility v q
        (payoffLotteryChannel (A := A) (inducedPayoffLottery q K)) =
      expectedPayoffUtility v q K := by
  rw [expectedPayoffUtility_payoffLotteryChannel,
    expectedPayoffUtility_eq_marginal]
  unfold payoffLotteryExpected
  simp only [inducedPayoffLottery_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro o _ho
  rw [Finset.sum_mul]

/-- The target normalized trace-tempered formula in the degenerate action
case. -/
theorem normalizedMarkedUtility_eq_traceTemperedValue_of_subsingleton
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (K : Channel A (O × R)) :
    normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) =
      traceTemperedValue (materialPayoffUtility F h)
        (globalTraceLambda F h) q K := by
  calc
    normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) =
        normalizedMarkedUtility F h q hq
          (markedPayoffLotteryExperiment (inducedPayoffLottery q K)) :=
      normalizedMarkedUtility_respects_sameMarkedTerminalLaw
        F h q hq _ _
          (sameMarkedTerminalLaw_inducedPayoffLottery_of_subsingleton q K)
    _ = expectedPayoffUtility (materialPayoffUtility F h) q
          (payoffLotteryChannel (inducedPayoffLottery q K)) :=
      normalizedMarkedUtility_payoffLottery F h q hq
        (inducedPayoffLottery q K)
    _ = expectedPayoffUtility (materialPayoffUtility F h) q K :=
      expectedPayoffUtility_inducedPayoffLottery _ q K
    _ = traceTemperedValue (materialPayoffUtility F h)
          (globalTraceLambda F h) q K := by
      unfold traceTemperedValue
      rw [mutualInfo_eq_zero_of_subsingleton q K, mul_zero, add_zero]

end TraceTemperedChoiceVerification
