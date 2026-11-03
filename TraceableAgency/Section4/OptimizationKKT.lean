import TraceableAgency.Section4.OptimizationKL
import TraceableAgency.Section4.OptimizationSupport
import TraceableAgency.Section4.OptimizationGeometry
import TraceableAgency.Section4.Binary.Entropy

/-! # Necessary and sufficient finite-action optimality conditions

The support clause is explicit. Thus the theorem never interprets a missing
reachable output using the artificial real value of `log 0`.
-/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1 Set Filter Topology
universe u

 theorem mixEntropySlope_zero_eq {Z : Type u} [Fintype Z] (p s : Dist Z) :
    mixEntropySlope p s 0 = finiteKL s p + entropy s - entropy p := by
  simp_rw [finiteKL_eq_entropy, entropy_eq_neg_sum_mul_log]
  simp only [mixEntropySlope, mixMass, zero_mul, add_zero]
  simp_rw [mul_sub, sub_mul, mul_neg, mul_one, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, s.sum_eq_one, p.sum_eq_one]
  ring

noncomputable def actionPathValue {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) (q : Dist A) (a : A) (t : ℝ) : ℝ :=
  lambda * mixEntropy (Channel.outcomeMarginal K q) (K a) t +
    (1-t) * (∑ b, q b * (r b-lambda*entropy (K b))) +
    t * (r a-lambda*entropy (K a))

 theorem actionPathValue_eq {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) (q : Dist A) (a : A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    actionPathValue r lambda K q a t = rowRewardValue r lambda (Dist.mix t ht0 ht1 (Dist.pure a) q) K := by
  rw [rowRewardValue_entropy, outcomeMarginal_mix, outcomeMarginal_pure_action,
    ← mixEntropy_eq_distMix _ _ ht0 ht1]
  unfold actionPathValue
  simp only [Dist.mix_apply, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum, Dist.pure_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

 theorem actionPathValue_zero {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) (q : Dist A) (a : A) :
    actionPathValue r lambda K q a 0 = rowRewardValue r lambda q K := by
  rw [actionPathValue_eq r lambda K q a 0 (by norm_num) (by norm_num)]
  congr 1
  apply Dist.ext
  intro b
  simp [Dist.mix_apply]

 theorem hasDerivAt_actionPathValue_zero {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) (q : Dist A) (a : A)
    (hc : CoversRows K (Channel.outcomeMarginal K q)) :
    HasDerivAt (actionPathValue r lambda K q a)
      (rowScore r lambda K (Channel.outcomeMarginal K q) a - rowRewardValue r lambda q K) 0 := by
  have hs (z : Z) (hz : Channel.outcomeMarginal K q z = 0) : K a z = 0 := by
    apply le_antisymm _ ((K a).nonneg z)
    apply le_of_not_gt
    intro hh
    have hp := hc a z hh
    rw [hz] at hp
    exact lt_irrefl 0 hp
  have hh := (((hasDerivAt_mixEntropy_zero (Channel.outcomeMarginal K q) (K a) hs).const_mul lambda).add
    (((hasDerivAt_const (0:ℝ) 1).sub (hasDerivAt_id 0)).mul_const
      (∑ b, q b * (r b-lambda*entropy (K b))))).add
    ((hasDerivAt_id (0:ℝ)).mul_const (r a-lambda*entropy (K a)))
  convert! hh using 1
  rw [mixEntropySlope_zero_eq, rowRewardValue_entropy]
  unfold rowScore
  ring

private theorem deriv_nonpos_of_right_max {f : ℝ → ℝ} {d : ℝ}
    (hd : HasDerivAt f d 0) (hm : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ f 0) : d ≤ 0 := by
  apply le_of_tendsto hd.tendsto_slope_zero_right
  have he : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [self_mem_nhdsWithin, he] with t ht ht1
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht))
    (sub_nonpos.mpr (hm t ⟨ht.le,ht1.le⟩))

 theorem optimal_rowScore_le {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (q : Dist A) (hq : IsOptimal r lambda K q) (a : A) :
    rowScore r lambda K (Channel.outcomeMarginal K q) a ≤ rowRewardValue r lambda q K := by
  have hd := hasDerivAt_actionPathValue_zero r lambda K q a (optimal_coversRows r hlambda K q hq)
  apply sub_nonpos.mp
  apply deriv_nonpos_of_right_max hd
  intro t ht
  rw [actionPathValue_eq r lambda K q a t ht.1 ht.2, actionPathValue_zero]
  exact hq _

 theorem weightedAverage_eq_iff {A : Type u} [Fintype A]
    (q : Dist A) (f : A → ℝ) (c : ℝ) (hf : ∀ a, f a ≤ c) :
    (∑ a, q a * f a) = c ↔ ∀ a, 0 < q a → f a = c := by
  have hn : ∀ a, 0 ≤ q a * (c-f a) := fun a => mul_nonneg (q.nonneg a) (sub_nonneg.mpr (hf a))
  have hsum : (∑ a, q a * (c-f a)) = c - ∑ a, q a * f a := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, q.sum_eq_one, one_mul]
  constructor
  · intro h a ha
    have hz : (∑ a, q a * (c-f a)) = 0 := by rw [hsum,h]; ring
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hn a)).mp hz a (Finset.mem_univ a)
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt ha))).symm
  · intro h
    calc
      (∑ a, q a * f a) = ∑ a, q a * c := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : 0 < q a
        · rw [h a ha]
        · have hz : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
          simp [hz]
      _ = c := by rw [← Finset.sum_mul,q.sum_eq_one,one_mul]

 theorem optimal_rowScore_eq_on_support {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (q : Dist A) (hq : IsOptimal r lambda K q) (a : A) (ha : 0 < q a) :
    rowScore r lambda K (Channel.outcomeMarginal K q) a = rowRewardValue r lambda q K := by
  exact (weightedAverage_eq_iff q _ _ (optimal_rowScore_le r hlambda K q hq)).mp
    (rowRewardValue_eq_weighted_scores r lambda q K).symm a ha

 theorem optimal_of_rowScore_le {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 ≤ lambda) (K : Channel A Z) (q : Dist A)
    (hc : CoversRows K (Channel.outcomeMarginal K q))
    (hscore : ∀ a, rowScore r lambda K (Channel.outcomeMarginal K q) a ≤ rowRewardValue r lambda q K) :
    IsOptimal r lambda K q := by
  intro p
  rw [rowRewardValue_reference r lambda p K (Channel.outcomeMarginal K q)]
  have hkl := mul_nonneg hlambda (finiteKL_nonneg _ _
    (supportIncluded_outcome_of_covers p K _ hc))
  have hw := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hscore a) (p.nonneg a))
  rw [← Finset.sum_mul, p.sum_eq_one, one_mul] at hw
  linarith

/-- The complete support-aware KKT condition. `CoversRows` is the assertion
that every extended-real row divergence appearing in the paper is finite. -/
 theorem optimal_iff_kkt {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z) (q : Dist A) :
    IsOptimal r lambda K q ↔ CoversRows K (Channel.outcomeMarginal K q) ∧
      ∃ c : ℝ, (∀ a, rowScore r lambda K (Channel.outcomeMarginal K q) a ≤ c) ∧
        (∀ a, 0 < q a → rowScore r lambda K (Channel.outcomeMarginal K q) a = c) := by
  constructor
  · intro hq
    exact ⟨optimal_coversRows r hlambda K q hq, rowRewardValue r lambda q K,
      optimal_rowScore_le r hlambda K q hq, optimal_rowScore_eq_on_support r hlambda K q hq⟩
  · rintro ⟨hc,c,hle,heq⟩
    have hvalue : rowRewardValue r lambda q K = c := by
      rw [rowRewardValue_eq_weighted_scores]
      exact (weightedAverage_eq_iff q _ c hle).mpr heq
    apply optimal_of_rowScore_le r hlambda.le K q hc
    intro a
    rw [hvalue]
    exact hle a

 theorem pure_optimal_iff {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z) (a : A) :
    IsOptimal r lambda K (Dist.pure a) ↔ CoversRows K (K a) ∧
      ∀ b, r b + lambda * finiteKL (K b) (K a) ≤ r a := by
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · simpa only [outcomeMarginal_pure_action] using optimal_coversRows r hlambda K (Dist.pure a) hq
    · intro b
      simpa only [rowScore, outcomeMarginal_pure_action, rowRewardValue_pure_action] using
        optimal_rowScore_le r hlambda K (Dist.pure a) hq b
  · rintro ⟨hc,hs⟩
    apply optimal_of_rowScore_le r hlambda.le K (Dist.pure a)
    · simpa only [outcomeMarginal_pure_action] using hc
    · simpa only [outcomeMarginal_pure_action, rowRewardValue_pure_action, rowScore] using hs

 theorem optimal_fullSupport_of_private_outputs {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (hprivate : ∀ a, ∃ z, 0 < K a z ∧ ∀ b, b ≠ a → K b z = 0)
    (q : Dist A) (hq : IsOptimal r lambda K q) : q.FullSupport := by
  intro a
  obtain ⟨z,hz,hothers⟩ := hprivate a
  have hm := optimal_coversRows r hlambda K q hq a z hz
  have heq : Channel.outcomeMarginal K q z = q a * K a z := by
    rw [Channel.outcomeMarginal_apply, Finset.sum_eq_single a]
    · intro b _ hb
      simp [hothers b hb]
    · simp
  rw [heq] at hm
  exact (mul_pos_iff.mp hm).resolve_right (fun h => (not_lt_of_ge (q.nonneg a)) h.1) |>.1

end TraceableAgency.Section4
