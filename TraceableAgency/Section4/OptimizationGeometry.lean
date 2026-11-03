import TraceableAgency.Section4.OptimizationBasic

/-! # Strict concavity in the induced output distribution -/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1
universe u

 theorem entropy_mix_strict {Z : Type u} [Fintype Z]
    (q p : Dist Z) (hne : q ≠ p) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    t * entropy q + (1-t) * entropy p < entropy (Dist.mix t ht0.le ht1.le q p) := by
  have hex : ∃ z, q z ≠ p z := by
    by_contra hh
    push Not at hh
    exact hne (Dist.ext hh)
  obtain ⟨z,hz⟩ := hex
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro y _
    exact entropyTerm_mix_le _ _ (q.nonneg y) (p.nonneg y) t ht0.le ht1.le
  · refine ⟨z, Finset.mem_univ z, ?_⟩
    simp only [Dist.mix_apply]
    rw [entropyTerm_eq_negMulLog (q.nonneg z), entropyTerm_eq_negMulLog (p.nonneg z),
      entropyTerm_eq_negMulLog (add_nonneg (mul_nonneg ht0.le (q.nonneg z))
        (mul_nonneg (sub_nonneg.mpr ht1.le) (p.nonneg z)))]
    exact Real.strictConcaveOn_negMulLog.2 (q.nonneg z) (p.nonneg z) hz ht0
      (sub_pos.mpr ht1) (by ring)

 theorem rowRewardValue_strictConcave_output
    {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (q p : Dist A) (hne : Channel.outcomeMarginal K q ≠ Channel.outcomeMarginal K p)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    t * rowRewardValue r lambda q K + (1-t) * rowRewardValue r lambda p K <
      rowRewardValue r lambda (Dist.mix t ht0.le ht1.le q p) K := by
  rw [rowRewardValue_mix_gap]
  have h := entropy_mix_strict (Channel.outcomeMarginal K q) (Channel.outcomeMarginal K p)
    hne t ht0 ht1
  nlinarith

 theorem optimal_output_unique {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (q p : Dist A) (hq : IsOptimal r lambda K q) (hp : IsOptimal r lambda K p) :
    Channel.outcomeMarginal K q = Channel.outcomeMarginal K p := by
  by_contra hn
  have heq : rowRewardValue r lambda q K = rowRewardValue r lambda p K :=
    le_antisymm (hp q) (hq p)
  have h := rowRewardValue_strictConcave_output r hlambda K q p hn (1/2)
    (by norm_num) (by norm_num)
  have hmax := hq (Dist.mix (1/2) (by norm_num) (by norm_num) q p)
  rw [heq] at h
  linarith

/-- Injectivity of the output-mixture map is sufficient for a unique input
optimum; affine independence of channel rows implies this injectivity. -/
 theorem optimal_unique_of_output_injective {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (hinj : Function.Injective (Channel.outcomeMarginal K))
    (q p : Dist A) (hq : IsOptimal r lambda K q) (hp : IsOptimal r lambda K p) : q = p :=
  hinj (optimal_output_unique r hlambda K q p hq hp)

end TraceableAgency.Section4
