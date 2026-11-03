import TraceableAgency.Section4.MoralHazard.Basic
import Mathlib.Analysis.Convex.Deriv

/-! The binary entropy inequality used by Proposition 30's counterexample. -/
namespace TraceableAgency.Section4.MoreCapable
open Set

noncomputable def gap (x : ℝ) : ℝ :=
  (1/2 : ℝ) * Real.binEntropy x - Real.binEntropy (1/5+3/5*x) + Real.binEntropy (1/5)

noncomputable def gapSlope (x : ℝ) : ℝ :=
  (1/2 : ℝ) * (Real.log (1-x)-Real.log x) -
    (3/5 : ℝ) * (Real.log (1-(1/5+3/5*x))-Real.log (1/5+3/5*x))

noncomputable def gapCurvature (x : ℝ) : ℝ :=
  -(1/2 : ℝ) / (x*(1-x)) + (9/25 : ℝ) / ((1/5+3/5*x)*(1-(1/5+3/5*x)))

theorem hasDerivAt_gap {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt gap (gapSlope x) x := by
  have hm0 : 0 < (1/5 : ℝ)+3/5*x := by linarith [hx.1]
  have hm1 : (1/5 : ℝ)+3/5*x < 1 := by linarith [hx.2]
  have hm : HasDerivAt (fun t : ℝ => (1/5 : ℝ)+3/5*t) (3/5) x := by
    convert! ((hasDerivAt_id x).const_mul (3/5 : ℝ)).const_add (1/5) using 1 <;> norm_num
  convert! (((Real.hasDerivAt_binEntropy (ne_of_gt hx.1) (ne_of_lt hx.2)).const_mul
    (1/2 : ℝ)).sub ((Real.hasDerivAt_binEntropy (ne_of_gt hm0) (ne_of_lt hm1)).comp x hm)).add_const
      (Real.binEntropy (1/5)) using 1 <;>
    simp only [gap, gapSlope, Function.comp_def] <;> ring

theorem hasDerivAt_gapSlope {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt gapSlope (gapCurvature x) x := by
  have hx0 := ne_of_gt hx.1
  have hx1 := ne_of_gt (sub_pos.mpr hx.2)
  have hm0 : 0 < (1/5 : ℝ)+3/5*x := by linarith [hx.1]
  have hm1 : 0 < 1-((1/5 : ℝ)+3/5*x) := by linarith [hx.2]
  have hm : HasDerivAt (fun t : ℝ => (1/5 : ℝ)+3/5*t) (3/5) x := by
    convert! ((hasDerivAt_id x).const_mul (3/5 : ℝ)).const_add (1/5) using 1 <;> norm_num
  have hleft := (((Real.hasDerivAt_log hx1).comp x
    ((hasDerivAt_const x 1).sub (hasDerivAt_id x))).sub
      (Real.hasDerivAt_log hx0)).const_mul (1/2 : ℝ)
  have hright := (((Real.hasDerivAt_log (ne_of_gt hm1)).comp x
    ((hasDerivAt_const x 1).sub hm)).sub
      ((Real.hasDerivAt_log (ne_of_gt hm0)).comp x hm)).const_mul (3/5 : ℝ)
  convert! hleft.sub hright using 1
  dsimp [gapCurvature]
  generalize hmval : ((1/5 : ℝ)+3/5*x) = m at hm0 hm1 ⊢
  field_simp [hx0, hx1, ne_of_gt hm0, ne_of_gt hm1]
  <;> ring

theorem gapCurvature_nonpos {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    gapCurvature x ≤ 0 := by
  have hxprod : 0 < x*(1-x) := mul_pos hx.1 (sub_pos.mpr hx.2)
  have hmprod : 0 < ((1/5 : ℝ)+3/5*x)*(1-((1/5 : ℝ)+3/5*x)) :=
    mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hquad : x*(1-x) ≤ (1/4 : ℝ) := by nlinarith [sq_nonneg (x-1/2)]
  have hh : (9/25 : ℝ) / ((1/5+3/5*x)*(1-(1/5+3/5*x))) ≤
      (1/2 : ℝ) / (x*(1-x)) :=
    (div_le_div_iff₀ hmprod hxprod).mpr (by nlinarith)
  unfold gapCurvature
  rw [neg_div]
  linarith

theorem gap_concave : ConcaveOn ℝ (Icc (0 : ℝ) 1) gap := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := gapSlope) (f'' := gapCurvature)
    (convex_Icc 0 1)
  · unfold gap
    fun_prop
  · intro x hx
    exact (hasDerivAt_gap (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_gapSlope (by simpa only [interior_Icc] using hx)).hasDerivWithinAt
  · intro x hx
    exact gapCurvature_nonpos (by simpa only [interior_Icc] using hx)

theorem binary_entropy_comparison {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    Real.binEntropy (1/5+3/5*x) - Real.binEntropy (1/5) ≤
      (1/2 : ℝ)*Real.binEntropy x := by
  have h0 : gap 0 = 0 := by norm_num [gap]
  have h1 : gap 1 = 0 := by
    have hh : Real.binEntropy (4/5 : ℝ) = Real.binEntropy (1/5) := by
      convert Real.binEntropy_one_sub (1/5 : ℝ) using 1 <;> norm_num
    norm_num [gap, hh]
  have h := gap_concave.2 (by norm_num : (0 : ℝ) ∈ Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Icc 0 1) (sub_nonneg.mpr hx.2) hx.1 (by ring : (1-x)+x=1)
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add, h0, h1] at h
  dsimp [gap] at h
  linarith

end TraceableAgency.Section4.MoreCapable
