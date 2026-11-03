import TraceableAgency.Section4.OptimizationFace

/-! # Disjoint output supports and the unique multinomial logit optimum -/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1
universe u

/-- Every output with positive probability identifies its generating action. -/
def DisjointRows {A Z : Type u} [Fintype Z] (K : Channel A Z) : Prop :=
  ∀ a b, b ≠ a → ∀ z, 0 < K a z → K b z = 0

 theorem mutualInfo_eq_entropy_of_disjoint {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z] [DecidableEq Z]
    (K : Channel A Z) (hd : DisjointRows K) (q : Dist A) :
    mutualInfo q K = entropy q := by
  rw [mutualInfo_entropyReduction]
  suffices (∑ z, Channel.outcomeMarginal K q z * entropy (Channel.posterior K q z)) = 0 by
    rw [this, sub_zero]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hm : 0 < Channel.outcomeMarginal K q z
  · have hex : ∃ a, 0 < q a * K a z := by
      by_contra! hh
      have hs : Channel.outcomeMarginal K q z ≤ 0 :=
        Finset.sum_nonpos fun a _ => hh a
      linarith
    obtain ⟨a,ha⟩ := hex
    have hka : 0 < K a z := by nlinarith [q.nonneg a,(K a).nonneg z]
    have hsingle : Channel.outcomeMarginal K q z = q a * K a z := by
      rw [Channel.outcomeMarginal_apply, Finset.sum_eq_single a]
      · intro b _ hb; rw [hd a b hb z hka, mul_zero]
      · simp
    have hpost : Channel.posterior K q z = Dist.pure a := by
      apply Dist.ext
      intro b
      simp only [Channel.posterior, dif_pos hm, Dist.pure_apply]
      by_cases hb : b = a
      · subst b
        simp only [ite_true]
        rw [hsingle, div_self (ne_of_gt ha)]
      · simp [hb, hd a b hb z hka]
    rw [hpost, entropy_pure', mul_zero]
  · have hz : Channel.outcomeMarginal K q z = 0 :=
      le_antisymm (le_of_not_gt hm) ((Channel.outcomeMarginal K q).nonneg z)
    rw [hz, zero_mul]

noncomputable def logitNormalizer {A : Type u} [Fintype A]
    (r : A → ℝ) (lambda : ℝ) : ℝ := ∑ a, Real.exp (r a / lambda)

 theorem logitNormalizer_pos {A : Type u} [Fintype A] [Nonempty A]
    (r : A → ℝ) (lambda : ℝ) : 0 < logitNormalizer r lambda := by
  classical
  exact lt_of_lt_of_le (Real.exp_pos (r (Classical.arbitrary A) / lambda))
    (Finset.single_le_sum (fun a _ => (Real.exp_pos (r a / lambda)).le)
      (Finset.mem_univ (Classical.arbitrary A)))

noncomputable def logitDist {A : Type u} [Fintype A] [Nonempty A]
    (r : A → ℝ) (lambda : ℝ) : Dist A where
  prob a := Real.exp (r a / lambda) / logitNormalizer r lambda
  nonneg a := (div_pos (Real.exp_pos _) (logitNormalizer_pos r lambda)).le
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (logitNormalizer_pos r lambda))

 theorem logitDist_pos {A : Type u} [Fintype A] [Nonempty A]
    (r : A → ℝ) (lambda : ℝ) (a : A) : 0 < logitDist r lambda a :=
  div_pos (Real.exp_pos _) (logitNormalizer_pos r lambda)

 theorem log_logitDist {A : Type u} [Fintype A] [Nonempty A]
    (r : A → ℝ) (lambda : ℝ) (a : A) :
    Real.log (logitDist r lambda a) = r a / lambda - Real.log (logitNormalizer r lambda) := by
  change Real.log (Real.exp (r a / lambda) / logitNormalizer r lambda) = _
  rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt (logitNormalizer_pos r lambda)),
    Real.log_exp]

/-- The Gibbs identity, with all boundary probabilities included. -/
 theorem reward_entropy_gibbs {A : Type u} [Fintype A] [Nonempty A]
    (r : A → ℝ) {lambda : ℝ} (hlambda : lambda ≠ 0) (q : Dist A) :
    (∑ a, q a * r a) + lambda * entropy q =
      lambda * Real.log (logitNormalizer r lambda) - lambda * finiteKL q (logitDist r lambda) := by
  have hs : (∑ a, q a * Real.log (logitDist r lambda a)) =
      (∑ a, q a * r a) / lambda - Real.log (logitNormalizer r lambda) := by
    simp_rw [log_logitDist, mul_sub, ← mul_div_assoc]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul, q.sum_eq_one, one_mul]
  rw [finiteKL_eq_entropy, hs]
  field_simp [hlambda]
  ring

 theorem rowRewardValue_disjoint_gibbs {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : lambda ≠ 0)
    (K : Channel A Z) (hd : DisjointRows K) (q : Dist A) :
    rowRewardValue r lambda q K = lambda * Real.log (logitNormalizer r lambda) -
      lambda * finiteKL q (logitDist r lambda) := by
  unfold rowRewardValue
  rw [mutualInfo_eq_entropy_of_disjoint K hd q]
  exact reward_entropy_gibbs r hlambda q

/-- Pairwise disjoint row supports yield exactly the multinomial logit lottery. -/
 theorem disjoint_optimal_iff_logit {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (K : Channel A Z) (hd : DisjointRows K) (q : Dist A) :
    IsOptimal r lambda K q ↔ q = logitDist r lambda := by
  have hs (p : Dist A) : SupportIncluded p (logitDist r lambda) :=
    fun a _ => logitDist_pos r lambda a
  have hopt : IsOptimal r lambda K (logitDist r lambda) := by
    intro p
    rw [rowRewardValue_disjoint_gibbs r (ne_of_gt hlambda) K hd,
      rowRewardValue_disjoint_gibbs r (ne_of_gt hlambda) K hd, finiteKL_self]
    nlinarith [finiteKL_nonneg p (logitDist r lambda) (hs p)]
  constructor
  · intro hq
    have hh := hq (logitDist r lambda)
    rw [rowRewardValue_disjoint_gibbs r (ne_of_gt hlambda) K hd,
      rowRewardValue_disjoint_gibbs r (ne_of_gt hlambda) K hd, finiteKL_self] at hh
    apply (finiteKL_eq_zero_iff q (logitDist r lambda) (hs q)).mp
    nlinarith [finiteKL_nonneg q (logitDist r lambda) (hs q)]
  · rintro rfl
    exact hopt

end TraceableAgency.Section4
