import TraceableAgency.Section4.MoralHazard.Optimization

/-! Endpoint incentive inequalities and the zero-effort side of the flat-wage
classification. All comparisons concern the same Bernoulli effort problem. -/
namespace TraceableAgency.Section4.BernoulliTechnology
open TraceableAgency Set
variable (t : BernoulliTechnology)

 theorem hasDerivAt_valueSlope (bonus cost lambda : ℝ) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (t.valueSlope bonus cost lambda) (lambda*t.informationCurvature q) q := by
  convert! ((t.hasDerivAt_informationSlope hq).const_mul lambda).const_add
    (t.gap*bonus-cost) using 1

 theorem value_curvature_neg (bonus cost : ℝ) {lambda q : ℝ}
    (hl : 0 < lambda) (hq : q ∈ Icc (0 : ℝ) 1) :
    deriv (t.valueSlope bonus cost lambda) q < 0 := by
  rw [(t.hasDerivAt_valueSlope bonus cost lambda hq).deriv]
  exact mul_neg_of_pos_of_neg hl (t.informationCurvature_neg hq)

 theorem interval_high_optimal_iff_slope (w0 bonus cost lambda : ℝ) (hl : 0 < lambda) :
    IsIntervalOptimal (t.value w0 bonus cost lambda) 1 ↔
      0 ≤ t.valueSlope bonus cost lambda 1 := by
  rw [t.interval_high_optimal_iff w0 bonus cost lambda hl]
  unfold valueSlope
  rw [t.informationSlope_one]
  rw [div_le_iff₀ t.gap_pos]
  constructor <;> intro hh <;> nlinarith

 theorem interval_low_optimal_iff_slope (w0 bonus cost lambda : ℝ) (hl : 0 < lambda) :
    IsIntervalOptimal (t.value w0 bonus cost lambda) 0 ↔
      t.valueSlope bonus cost lambda 0 ≤ 0 := by
  rw [t.interval_low_optimal_iff w0 bonus cost lambda hl]
  unfold valueSlope
  rw [t.informationSlope_zero]

 theorem flat_wage_zero_iff (w0 cost lambda : ℝ) (hl : 0 < lambda) :
    IsIntervalOptimal (t.value w0 0 cost lambda) 0 ↔
      lambda*bernoulliKL t.high t.low ≤ cost := by
  rw [t.interval_low_optimal_iff w0 0 cost lambda hl]
  constructor <;> intro hh <;> simp only [mul_zero,zero_sub] at * <;> linarith

 theorem flat_wage_unique_zero (w0 cost lambda : ℝ) (hl : 0 < lambda)
    (hc : lambda*bernoulliKL t.high t.low ≤ cost) {q : ℝ}
    (hq : IsIntervalOptimal (t.value w0 0 cost lambda) q) : q = 0 := by
  have hzero := (t.flat_wage_zero_iff w0 cost lambda hl).mpr hc
  obtain ⟨x,hx,hu⟩ := t.exists_unique_intervalOptimal w0 0 cost lambda hl
  exact (hu q hq).trans (hu 0 hzero).symm

end TraceableAgency.Section4.BernoulliTechnology
