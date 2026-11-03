import TraceableAgency.Section4.Binary.Choice

/-! The interior first-order equation and comparative statics of the unique
binary optimum, including boundary solutions and zero payoff gap. -/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1 Set
universe u
variable {Z : Type u} [Fintype Z]

 theorem binary_value_dist (p r : Dist Z) (gap lambda : ℝ) (q : Dist RelevanceBit.{u}) :
    rowRewardValue (binaryRewards gap) lambda q (binaryChannel p r) =
      binaryValue p r gap lambda (q (ULift.up true)) := by
  conv_lhs => rw [bit_dist_eq_publicCoin q]
  exact binary_value_eq p r gap lambda _ _ _

 theorem binaryGain_eq_KL_difference (p r : Dist Z) (q : Dist RelevanceBit.{u}) :
    binaryGain p r (q (ULift.up true)) =
      finiteKL r (Channel.outcomeMarginal (binaryChannel p r) q) -
        finiteKL p (Channel.outcomeMarginal (binaryChannel p r) q) := by
  rw [finiteKL_eq_entropy,finiteKL_eq_entropy]
  simp only [binary_outcomeMarginal]
  unfold binaryGain mixEntropySlope
  simp_rw [mul_sub,mul_neg,mul_one,sub_mul,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  rw [r.sum_eq_one,p.sum_eq_one]
  rw [Finset.sum_sub_distrib]
  ring

 theorem binaryGain_strictAnti (p r : Dist Z) (hne : p ≠ r) :
    StrictAntiOn (binaryGain p r) (Ioo (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hh := mixEntropySlope_strictAnti p r hne hx hy hxy
  dsimp [binaryGain]
  linarith

 theorem binary_interior_equation (p r : Dist Z) {gap lambda : ℝ} (hl : 0 < lambda)
    (q : Dist RelevanceBit.{u}) (hq : IsOptimal (binaryRewards gap) lambda (binaryChannel p r) q)
    (hx : q (ULift.up true) ∈ Ioo (0 : ℝ) 1) :
    gap = lambda*binaryGain p r (q (ULift.up true)) := by
  classical
  have hs := q.sum_eq_one
  rw [Section3.sum_relevanceBit] at hs
  have hfalse : 0 < q (ULift.up false) := by linarith [hx.2]
  obtain ⟨_,c,_,he⟩ := (optimal_iff_kkt (binaryRewards gap) hl (binaryChannel p r) q).mp hq
  have h0 := he (ULift.up false) hfalse
  have h1 := he (ULift.up true) hx.1
  change 0+lambda*finiteKL p (Channel.outcomeMarginal (binaryChannel p r) q) = c at h0
  change -gap+lambda*finiteKL r (Channel.outcomeMarginal (binaryChannel p r) q) = c at h1
  rw [binaryGain_eq_KL_difference]
  nlinarith

 theorem binary_gap_monotone (p r : Dist Z) (hne : p ≠ r)
    {gap1 gap2 lambda : ℝ} (hg : gap1 ≤ gap2) (hl : 0 < lambda)
    (q s : Dist RelevanceBit.{u})
    (hq : IsOptimal (binaryRewards gap1) lambda (binaryChannel p r) q)
    (hs : IsOptimal (binaryRewards gap2) lambda (binaryChannel p r) s) :
    s (ULift.up true) ≤ q (ULift.up true) := by
  rcases hg.eq_or_lt with he | hg
  · subst gap2
    have hh := optimal_unique_of_output_injective (binaryRewards gap1) hl
      (binaryChannel p r) (binary_output_injective p r hne) s q hs hq
    exact (congrArg (fun d : Dist RelevanceBit => d (ULift.up true)) hh).le
  · have h1 := hq s
    have h2 := hs q
    rw [binary_value_dist,binary_value_dist] at h1 h2
    dsimp [binaryValue] at h1 h2
    by_contra hn
    have hxy := lt_of_not_ge hn
    have hprod := mul_pos (sub_pos.mpr hg) (sub_pos.mpr hxy)
    nlinarith

 theorem binary_capacity_independent_lambda (p r : Dist Z)
    {lambda mu : ℝ} (hl : 0 < lambda) (hm : 0 < mu) (q : Dist RelevanceBit.{u}) :
    IsOptimal (binaryRewards 0) lambda (binaryChannel p r) q ↔
      IsOptimal (binaryRewards 0) mu (binaryChannel p r) q := by
  unfold IsOptimal
  simp only [binary_value_dist,binaryValue,mul_zero,neg_zero,zero_add]
  constructor <;> intro h s
  · have hs := h s
    have hi : binaryInformation p r (s (ULift.up true)) ≤ binaryInformation p r (q (ULift.up true)) := by nlinarith
    exact mul_le_mul_of_nonneg_left hi hm.le
  · have hs := h s
    have hi : binaryInformation p r (s (ULift.up true)) ≤ binaryInformation p r (q (ULift.up true)) := by nlinarith
    exact mul_le_mul_of_nonneg_left hi hl.le

 theorem binary_lambda_monotone (p r : Dist Z) (hne : p ≠ r)
    {gap lambda mu : ℝ} (hg : 0 ≤ gap) (hl : 0 < lambda) (hm : lambda ≤ mu)
    (q s : Dist RelevanceBit.{u})
    (hq : IsOptimal (binaryRewards gap) lambda (binaryChannel p r) q)
    (hs : IsOptimal (binaryRewards gap) mu (binaryChannel p r) s) :
    q (ULift.up true) ≤ s (ULift.up true) := by
  by_cases hg0 : gap = 0
  · subst gap
    have hq' := (binary_capacity_independent_lambda p r hl (hl.trans_le hm) q).mp hq
    have he := optimal_unique_of_output_injective (binaryRewards 0) (hl.trans_le hm)
      (binaryChannel p r) (binary_output_injective p r hne) q s hq' hs
    exact (congrArg (fun d : Dist RelevanceBit => d (ULift.up true)) he).le
  rcases hm.eq_or_lt with he | hm
  · subst mu
    have hh := optimal_unique_of_output_injective (binaryRewards gap) hl
      (binaryChannel p r) (binary_output_injective p r hne) q s hq hs
    exact (congrArg (fun d : Dist RelevanceBit => d (ULift.up true)) hh).le
  have hg' : 0 < gap := lt_of_le_of_ne hg (Ne.symm hg0)
  have h1 := hq s
  have h2 := hs q
  rw [binary_value_dist,binary_value_dist] at h1 h2
  dsimp [binaryValue] at h1 h2
  by_contra hn
  have hxy : s (ULift.up true) < q (ULift.up true) := lt_of_not_ge hn
  have hIdiff : binaryInformation p r (s (ULift.up true)) < binaryInformation p r (q (ULift.up true)) := by
    by_contra hnot
    have hnonneg := le_of_not_gt hnot
    have hprod := mul_pos hg' (sub_pos.mpr hxy)
    nlinarith
  have hprod := mul_pos (sub_pos.mpr hm) (sub_pos.mpr hIdiff)
  nlinarith

 theorem binary_gap_strict_interior (p r : Dist Z) (hne : p ≠ r)
    {gap1 gap2 lambda : ℝ} (hg : gap1 < gap2) (hl : 0 < lambda)
    (q s : Dist RelevanceBit.{u})
    (hq : IsOptimal (binaryRewards gap1) lambda (binaryChannel p r) q)
    (hs : IsOptimal (binaryRewards gap2) lambda (binaryChannel p r) s)
    (hqint : q (ULift.up true) ∈ Ioo (0 : ℝ) 1)
    (hsint : s (ULift.up true) ∈ Ioo (0 : ℝ) 1) :
    s (ULift.up true) < q (ULift.up true) := by
  have hw := binary_gap_monotone p r hne hg.le hl q s hq hs
  apply lt_of_le_of_ne hw
  intro he
  have h1 := binary_interior_equation p r hl q hq hqint
  have h2 := binary_interior_equation p r hl s hs hsint
  rw [he] at h2
  linarith

 theorem binary_lambda_strict_interior (p r : Dist Z) (hne : p ≠ r)
    {gap lambda mu : ℝ} (hg : 0 < gap) (hl : 0 < lambda) (hm : lambda < mu)
    (q s : Dist RelevanceBit.{u})
    (hq : IsOptimal (binaryRewards gap) lambda (binaryChannel p r) q)
    (hs : IsOptimal (binaryRewards gap) mu (binaryChannel p r) s)
    (hqint : q (ULift.up true) ∈ Ioo (0 : ℝ) 1)
    (hsint : s (ULift.up true) ∈ Ioo (0 : ℝ) 1) :
    q (ULift.up true) < s (ULift.up true) := by
  have hw := binary_lambda_monotone p r hne hg.le hl hm.le q s hq hs
  apply lt_of_le_of_ne hw
  intro he
  have h1 := binary_interior_equation p r hl q hq hqint
  have h2 := binary_interior_equation p r (hl.trans hm) s hs hsint
  rw [he] at h1
  have hpos : 0 < binaryGain p r (s (ULift.up true)) := by nlinarith
  nlinarith

end TraceableAgency.Section4
