/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Info.Entropy
import TraceableAgency.Basic.Channel

/-!
# Mutual Information

Mutual information I(A;O) = H(O) - Σ_a q(a) * H(P(·|a))
                          = H(q) - E[H(posterior)]

This is the information about the action A contained in the outcome O.
-/

namespace TraceableAgency

variable {A O : Type*} [Fintype A] [Fintype O]

/-- Mutual information I_{q,P}(A;O) using the noise form:
    I = H(outcome marginal) - Σ_a q(a) * H(P(·|a))

    This equals H(q) - E[H(posterior)] by standard identities. -/
noncomputable def mutualInfo (q : Dist A) (P : Channel A O) : ℝ :=
  H(Channel.outcomeMarginal P q) - ∑ a, q a * H(P a)

notation "I(" q ", " P ")" => mutualInfo q P

/-- One summand in the paper's finite likelihood-ratio formula.  A zero joint
mass contributes zero, so the likelihood ratio is evaluated only on the
positive-mass branch. -/
noncomputable def mutualInfoLikelihoodRatioTerm
    (joint conditional marginal : ℝ) : ℝ :=
  if joint = 0 then 0 else joint * Real.log (conditional / marginal)

/-- The paper-form finite likelihood-ratio sum
`Σ_a Σ_o q(a) P(o|a) log(P(o|a) / m(o))`, with every zero-joint-mass
summand defined to be zero. -/
noncomputable def mutualInfoLikelihoodRatio
    (q : Dist A) (P : Channel A O) : ℝ :=
  ∑ a, ∑ o, mutualInfoLikelihoodRatioTerm
    (q a * P a o) (P a o) ((Channel.outcomeMarginal P q) o)

private theorem entropyTerm_eq_neg_mul_log_of_nonneg
    {p : ℝ} (hp : 0 ≤ p) :
    entropyTerm p = -p * Real.log p := by
  rcases hp.eq_or_lt with rfl | hp
  · simp [entropyTerm_zero]
  · exact entropyTerm_eq_neg_mul_log hp

private theorem mutualInfoLikelihoodRatioTerm_eq
    (q p m : ℝ) (hq : 0 ≤ q) (hp : 0 ≤ p) (hjoint_le : q * p ≤ m) :
    mutualInfoLikelihoodRatioTerm (q * p) p m =
      -(q * entropyTerm p) - (q * p) * Real.log m := by
  by_cases hjoint : q * p = 0
  · rcases mul_eq_zero.mp hjoint with hq0 | hp0
    · simp [mutualInfoLikelihoodRatioTerm, hq0]
    · simp [mutualInfoLikelihoodRatioTerm, hp0, entropyTerm_zero]
  · have hq_ne : q ≠ 0 := fun h ↦ hjoint (by simp [h])
    have hp_ne : p ≠ 0 := fun h ↦ hjoint (by simp [h])
    have hq_pos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq_ne)
    have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp_ne)
    have hjoint_pos : 0 < q * p := mul_pos hq_pos hp_pos
    have hm_pos : 0 < m := lt_of_lt_of_le hjoint_pos hjoint_le
    rw [mutualInfoLikelihoodRatioTerm, if_neg hjoint,
      Real.log_div hp_ne (ne_of_gt hm_pos),
      entropyTerm_eq_neg_mul_log hp_pos]
    ring

/-- The paper's finite likelihood-ratio sum equals the entropy-difference
definition used by `mutualInfo`. -/
theorem mutualInfoLikelihoodRatio_eq_mutualInfo
    [DecidableEq A] (q : Dist A) (P : Channel A O) :
    mutualInfoLikelihoodRatio q P = mutualInfo q P := by
  classical
  have hjoint_le : ∀ a o, q a * P a o ≤ (Channel.outcomeMarginal P q) o := by
    intro a o
    rw [Channel.outcomeMarginal_apply]
    exact Finset.single_le_sum
      (fun b _ ↦ mul_nonneg (q.nonneg b) ((P b).nonneg o))
      (Finset.mem_univ a)
  unfold mutualInfoLikelihoodRatio mutualInfo entropy
  simp_rw [mutualInfoLikelihoodRatioTerm_eq _ _ _
    (q.nonneg _) ((P _).nonneg _) (hjoint_le _ _)]
  have hrow :
      (∑ a, ∑ o, -(q a * entropyTerm (P a o))) =
        -(∑ a, q a * ∑ o, entropyTerm (P a o)) := by
    simp_rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
  have hmarginal :
      (∑ a, ∑ o, (q a * P a o) *
          Real.log ((Channel.outcomeMarginal P q) o)) =
        -(∑ o, entropyTerm ((Channel.outcomeMarginal P q) o)) := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro o _
    rw [← Finset.sum_mul,
      ← Channel.outcomeMarginal_apply,
      entropyTerm_eq_neg_mul_log_of_nonneg
        ((Channel.outcomeMarginal P q).nonneg o)]
    ring
  simp_rw [Finset.sum_sub_distrib]
  rw [hrow, hmarginal]
  ring

end TraceableAgency
