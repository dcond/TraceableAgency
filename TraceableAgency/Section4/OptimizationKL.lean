import TraceableAgency.Section4.OptimizationBasic
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-! # Finite relative entropy and the exact reference-output identity -/
namespace TraceableAgency.Section4

open TraceableAgency Theorem1

universe u

 theorem entropy_eq_neg_sum_mul_log {Z : Type u} [Fintype Z] (p : Dist Z) :
    entropy p = -(∑ z, p z * Real.log (p z)) := by
  calc
    entropy p = ∑ z, -(p z * Real.log (p z)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [entropyTerm_eq_negMulLog (p.nonneg z)]
      unfold Real.negMulLog
      ring
    _ = _ := by rw [Finset.sum_neg_distrib]


 theorem finiteKL_eq_entropy {Z : Type u} [Fintype Z] (p s : Dist Z) :
    finiteKL p s = -entropy p - ∑ z, p z * Real.log (s z) := by
  rw [entropy_eq_neg_sum_mul_log]
  simp [finiteKL, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem finiteKL_self {Z : Type u} [Fintype Z] (p : Dist Z) : finiteKL p p = 0 := by
  simp [finiteKL]

 theorem finiteKL_gap_sum {Z : Type u} [Fintype Z] (p s : Dist Z) :
    finiteKL p s = ∑ z, (p z * (Real.log (p z) - Real.log (s z)) - p z + s z) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, p.sum_eq_one, s.sum_eq_one]
  unfold finiteKL
  ring

private theorem gap_identity (x y : ℝ) (hx : 0 ≤ x) (hy : 0 < y) :
    x * (Real.log x - Real.log y) - x + y = y * InformationTheory.klFun (x/y) := by
  by_cases hx0 : x = 0
  · simp [hx0, InformationTheory.klFun]
  · rw [InformationTheory.klFun, Real.log_div hx0 (ne_of_gt hy)]
    field_simp
    ring

private theorem gap_nonneg (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 < x → 0 < y) : 0 ≤ x * (Real.log x - Real.log y) - x + y := by
  by_cases hp : 0 < y
  · rw [gap_identity x y hx hp]
    exact mul_nonneg hy (InformationTheory.klFun_nonneg (div_nonneg hx hy))
  · have hy0 : y = 0 := le_antisymm (le_of_not_gt hp) hy
    have hx0 : x = 0 := le_antisymm (le_of_not_gt fun hh => hp (hs hh)) hx
    simp [hx0, hy0]

private theorem gap_eq_zero_iff (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hs : 0 < x → 0 < y) : x * (Real.log x - Real.log y) - x + y = 0 ↔ x = y := by
  by_cases hp : 0 < y
  · rw [gap_identity x y hx hp, mul_eq_zero]
    simp only [ne_of_gt hp, false_or]
    rw [InformationTheory.klFun_eq_zero_iff (div_nonneg hx hy), div_eq_one_iff_eq (ne_of_gt hp)]
  · have hy0 : y = 0 := le_antisymm (le_of_not_gt hp) hy
    have hx0 : x = 0 := le_antisymm (le_of_not_gt fun hh => hp (hs hh)) hx
    simp [hx0, hy0]

 theorem finiteKL_nonneg {Z : Type u} [Fintype Z] (p s : Dist Z)
    (hs : SupportIncluded p s) : 0 ≤ finiteKL p s := by
  rw [finiteKL_gap_sum]
  exact Finset.sum_nonneg fun z _ => gap_nonneg _ _ (p.nonneg z) (s.nonneg z) (hs z)

 theorem finiteKL_eq_zero_iff {Z : Type u} [Fintype Z] (p s : Dist Z)
    (hs : SupportIncluded p s) : finiteKL p s = 0 ↔ p = s := by
  constructor
  · intro h
    rw [finiteKL_gap_sum] at h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => gap_nonneg _ _ (p.nonneg z) (s.nonneg z) (hs z))).mp h
    exact Dist.ext fun z => (gap_eq_zero_iff _ _ (p.nonneg z) (s.nonneg z) (hs z)).mp
      (hz z (Finset.mem_univ z))
  · rintro rfl
    exact finiteKL_self p

 theorem supportIncluded_outcome_of_pos {A Z : Type u} [Fintype A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) (a : A) (ha : 0 < q a) :
    SupportIncluded (K a) (Channel.outcomeMarginal K q) := by
  classical
  intro z hz
  exact lt_of_lt_of_le (mul_pos ha hz)
    (Finset.single_le_sum (fun b _ => mul_nonneg (q.nonneg b) ((K b).nonneg z)) (Finset.mem_univ a))

 theorem supportIncluded_outcome_of_covers {A Z : Type u} [Fintype A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) (p : Dist Z) (hp : CoversRows K p) :
    SupportIncluded (Channel.outcomeMarginal K q) p := by
  classical
  intro z hz
  by_contra hn
  have hzero (a : A) : K a z = 0 :=
    le_antisymm (le_of_not_gt fun ha => hn (hp a z ha)) ((K a).nonneg z)
  have h : Channel.outcomeMarginal K q z = 0 := by simp [Channel.outcomeMarginal_apply, hzero]
  linarith

/-- The algebraic reference identity. Its use as a KL inequality requires
`CoversRows K p`, as imposed in the optimality results. -/
 theorem rowRewardValue_reference {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (q : Dist A) (K : Channel A Z) (p : Dist Z) :
    rowRewardValue r lambda q K = (∑ a, q a * rowScore r lambda K p a) -
      lambda * finiteKL (Channel.outcomeMarginal K q) p := by
  simp only [rowRewardValue_entropy, rowScore, finiteKL_eq_entropy]
  have hcross : (∑ a, q a * ∑ z, K a z * Real.log (p z)) =
      ∑ z, Channel.outcomeMarginal K q z * Real.log (p z) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Channel.outcomeMarginal_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    ring
  simp_rw [mul_add, mul_sub, mul_neg, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib]
  have hh : (∑ a, q a * (lambda * ∑ z, (K a).prob z * Real.log (p.prob z))) =
      lambda * ∑ z, (Channel.outcomeMarginal K q).prob z * Real.log (p.prob z) := by
    rw [← hcross, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hh]
  ring

 theorem rowRewardValue_eq_weighted_scores {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (q : Dist A) (K : Channel A Z) :
    rowRewardValue r lambda q K = ∑ a, q a * rowScore r lambda K (Channel.outcomeMarginal K q) a := by
  rw [rowRewardValue_reference r lambda q K (Channel.outcomeMarginal K q), finiteKL_self]
  ring

end TraceableAgency.Section4
