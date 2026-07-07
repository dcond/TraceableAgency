/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Dist

/-!
# Shannon Entropy

Finite Shannon entropy H(q), taking the zero-probability contribution to be `0`.
-/

set_option linter.style.header false

namespace TraceableAgency

variable {A : Type*} [Fintype A]

open Real in
/-- The entropy contribution from a single probability: `-p * log p`.
    At `p = 0`, the contribution is defined as `0`. -/
noncomputable def entropyTerm (p : ℝ) : ℝ :=
  if p ≤ 0 then 0 else -p * log p

theorem entropyTerm_zero : entropyTerm 0 = 0 := by simp [entropyTerm]

theorem entropyTerm_one : entropyTerm 1 = 0 := by simp [entropyTerm, Real.log_one]

theorem entropyTerm_nonneg (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : 0 ≤ entropyTerm p := by
  unfold entropyTerm
  split_ifs with h
  · exact le_refl 0
  · push_neg at h
    have hlog : Real.log p ≤ 0 := Real.log_nonpos hp hp1
    nlinarith

/-!
## Continuity of Entropy Term

The function entropyTerm p = if p ≤ 0 then 0 else -p * log(p) is continuous on ℝ.
Mathlib provides `Real.continuous_negMulLog` for x ↦ -x log x on nonneg reals.
-/

open Filter Topology

/-- The entropy term function restricted to positive reals agrees with -x log x. -/
theorem entropyTerm_eq_neg_mul_log {p : ℝ} (hp : 0 < p) :
    entropyTerm p = -p * Real.log p := by
  unfold entropyTerm
  rw [if_neg (not_le.mpr hp)]

/-- entropyTerm agrees with negMulLog on nonnegative reals. -/
theorem entropyTerm_eq_negMulLog {p : ℝ} (hp : 0 ≤ p) :
    entropyTerm p = Real.negMulLog p := by
  unfold entropyTerm Real.negMulLog
  by_cases hp0 : p ≤ 0
  · have hp_eq : p = 0 := le_antisymm hp0 hp
    simp [hp_eq]
  · push_neg at hp0
    rw [if_neg (not_le.mpr hp0)]

/-- Continuity of entropyTerm: the map p ↦ entropyTerm(p) is continuous.
    Uses mathlib's `Real.continuous_negMulLog`. -/
theorem continuous_entropyTerm : Continuous entropyTerm := by
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hp : 0 < p
  · have h_negMulLog_cont := Real.continuous_negMulLog.continuousAt (x := p)
    apply h_negMulLog_cont.congr
    filter_upwards [eventually_ge_nhds hp] with q hq
    exact (entropyTerm_eq_negMulLog hq).symm
  · push_neg at hp
    have hp_eq : entropyTerm p = 0 := by unfold entropyTerm; simp [hp]
    have h_negMulLog_0 : Real.negMulLog 0 = 0 := Real.negMulLog_zero
    rw [Metric.continuousAt_iff]
    intro ε hε
    have h_negMulLog_cont := Real.continuous_negMulLog.continuousAt (x := 0)
    rw [Metric.continuousAt_iff] at h_negMulLog_cont
    obtain ⟨δ₁, hδ₁, hball₁⟩ := h_negMulLog_cont ε hε
    by_cases hp_eq0 : p = 0
    · use δ₁, hδ₁
      intro q hdist
      by_cases hq : 0 ≤ q
      · rw [hp_eq, entropyTerm_eq_negMulLog hq]
        have hdist_q_0 : dist q 0 < δ₁ := by rw [hp_eq0] at hdist; exact hdist
        specialize hball₁ hdist_q_0
        simp only [h_negMulLog_0] at hball₁
        exact hball₁
      · push_neg at hq
        have hq_eq : entropyTerm q = 0 := by unfold entropyTerm; simp [le_of_lt hq]
        rw [hp_eq, hq_eq, Real.dist_eq, sub_zero, abs_zero]
        exact hε
    · have hp_neg : p < 0 := lt_of_le_of_ne hp hp_eq0
      use min δ₁ (-p), by simp only [lt_min_iff]; exact ⟨hδ₁, neg_pos.mpr hp_neg⟩
      intro q hdist
      by_cases hq : 0 ≤ q
      · rw [hp_eq, entropyTerm_eq_negMulLog hq]
        have h1 : dist q p < min δ₁ (-p) := hdist
        have hdist_q_p_lt_delta : dist q p < δ₁ := lt_of_lt_of_le h1 (min_le_left _ _)
        have hdist_q_0 : dist q 0 < δ₁ := by
          simp only [Real.dist_eq, sub_zero] at hdist_q_p_lt_delta ⊢
          rw [abs_of_nonneg hq]
          have hq_sub_p_pos : q - p > 0 := by linarith
          have habs_qp : |q - p| = q - p := abs_of_pos hq_sub_p_pos
          rw [habs_qp] at hdist_q_p_lt_delta
          linarith
        specialize hball₁ hdist_q_0
        simp only [h_negMulLog_0] at hball₁
        exact hball₁
      · push_neg at hq
        have hq_eq : entropyTerm q = 0 := by unfold entropyTerm; simp [le_of_lt hq]
        rw [hp_eq, hq_eq, Real.dist_eq, sub_zero, abs_zero]
        exact hε

/-- Shannon entropy of a finite distribution: H(q) = -Σ_a q(a) * log(q(a)). -/
noncomputable def entropy (q : Dist A) : ℝ :=
  ∑ a, entropyTerm (q a)

notation "H(" q ")" => entropy q

theorem entropy_nonneg (q : Dist A) : 0 ≤ H(q) := by
  apply Finset.sum_nonneg
  intro a _
  exact entropyTerm_nonneg (q a) (q.nonneg a) (q.prob_le_one a)

/-!
## Continuity of Entropy

Entropy is continuous as a function on Dist A (with induced topology).
-/

variable [DecidableEq A]

/-- Entropy is continuous: q ↦ H(q) is a continuous function on Dist A. -/
theorem continuous_entropy : Continuous (entropy : Dist A → ℝ) := by
  unfold entropy
  apply continuous_finset_sum
  intro a _
  exact continuous_entropyTerm.comp (Dist.continuous_prob_apply a)

end TraceableAgency
