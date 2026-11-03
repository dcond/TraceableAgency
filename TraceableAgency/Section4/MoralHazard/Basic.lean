import TraceableAgency.Section4.Binary.Entropy
import TraceableAgency.Info.MutualInfo
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Binary production and the moral-hazard value in natural-log units. -/
namespace TraceableAgency.Section4
open TraceableAgency Set

noncomputable def bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Dist Bool where
  prob b := if b then p else 1-p
  nonneg b := by cases b <;> simp <;> linarith
  sum_eq_one := by simp [Fintype.sum_bool]

@[simp] theorem bernoulli_true (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    bernoulli p h0 h1 true = p := rfl
@[simp] theorem bernoulli_false (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    bernoulli p h0 h1 false = 1-p := rfl

 theorem entropy_bernoulli (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    entropy (bernoulli p h0 h1) = Real.binEntropy p := by
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp only [entropy, Fintype.sum_bool, bernoulli_true, bernoulli_false]
  rw [entropyTerm_eq_negMulLog h0, entropyTerm_eq_negMulLog (sub_nonneg.mpr h1)]

structure BernoulliTechnology where
  low : ℝ
  high : ℝ
  low_pos : 0 < low
  productive : low < high
  high_lt_one : high < 1

namespace BernoulliTechnology
variable (t : BernoulliTechnology)

def gap : ℝ := t.high-t.low
 theorem gap_pos : 0 < t.gap := sub_pos.mpr t.productive
noncomputable def channel : Channel Bool Bool := fun a =>
  if a then bernoulli t.high (t.low_pos.trans t.productive).le t.high_lt_one.le
  else bernoulli t.low t.low_pos.le (t.productive.trans t.high_lt_one).le
noncomputable def mean (q : ℝ) : ℝ := t.low+q*t.gap

 theorem mean_bounds {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    t.low ≤ t.mean q ∧ t.mean q ≤ t.high := by
  have hg := t.gap_pos
  obtain ⟨hq0,hq1⟩ := hq
  dsimp [mean, gap] at *
  constructor <;> nlinarith
 theorem mean_mem {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) : t.mean q ∈ Ioo (0 : ℝ) 1 :=
  ⟨t.low_pos.trans_le (t.mean_bounds hq).1,
    (t.mean_bounds hq).2.trans_lt t.high_lt_one⟩

 theorem outcomeMarginal_eq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Channel.outcomeMarginal t.channel (bernoulli q hq0 hq1) =
      bernoulli (t.mean q) (t.mean_mem ⟨hq0,hq1⟩).1.le (t.mean_mem ⟨hq0,hq1⟩).2.le := by
  ext b
  cases b <;> simp [Channel.outcomeMarginal_apply, channel, Fintype.sum_bool,
    bernoulli, mean, gap] <;> ring

noncomputable def information (q : ℝ) : ℝ :=
  Real.binEntropy (t.mean q) - (1-q)*Real.binEntropy t.low - q*Real.binEntropy t.high
noncomputable def informationSlope (q : ℝ) : ℝ :=
  t.gap*(Real.log (1-t.mean q)-Real.log (t.mean q)) +
    Real.binEntropy t.low - Real.binEntropy t.high
noncomputable def informationCurvature (q : ℝ) : ℝ :=
  -(t.gap)^2/(t.mean q*(1-t.mean q))
noncomputable def value (w0 bonus cost lambda q : ℝ) : ℝ :=
  w0 + t.mean q * bonus - q*cost + lambda*t.information q
noncomputable def valueSlope (bonus cost lambda q : ℝ) : ℝ :=
  t.gap*bonus-cost+lambda*t.informationSlope q

 theorem mutualInfo_eq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    mutualInfo (bernoulli q hq0 hq1) t.channel = t.information q := by
  unfold mutualInfo
  rw [t.outcomeMarginal_eq, entropy_bernoulli]
  simp only [Fintype.sum_bool, bernoulli_true, bernoulli_false, channel,
    Bool.false_eq_true, Bool.true_eq, if_false, if_true, entropy_bernoulli,
    information]
  ring

 theorem hasDerivAt_mean (q : ℝ) : HasDerivAt t.mean t.gap q := by
  convert! ((hasDerivAt_id q).mul_const t.gap).const_add t.low using 1 <;> simp [mean]

 theorem hasDerivAt_information {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    HasDerivAt t.information (t.informationSlope q) q := by
  have hm := t.mean_mem hq
  have hh := ((Real.hasDerivAt_binEntropy (ne_of_gt hm.1) (ne_of_lt hm.2)).comp q
    (t.hasDerivAt_mean q)).sub
      (((hasDerivAt_const q 1).sub (hasDerivAt_id q)).mul_const (Real.binEntropy t.low))
  have hh' := hh.sub ((hasDerivAt_id q).mul_const (Real.binEntropy t.high))
  convert! hh' using 1 <;> simp [information, informationSlope, Function.comp_def] <;> ring

 theorem hasDerivAt_informationSlope {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    HasDerivAt t.informationSlope (t.informationCurvature q) q := by
  have hm := t.mean_mem hq
  have hlog0 := (Real.hasDerivAt_log (ne_of_gt hm.1)).comp q (t.hasDerivAt_mean q)
  have hlog1 := (Real.hasDerivAt_log (ne_of_gt (sub_pos.mpr hm.2))).comp q
    ((hasDerivAt_const q 1).sub (t.hasDerivAt_mean q))
  have hh := (((hlog1.sub hlog0).const_mul t.gap).add_const (Real.binEntropy t.low)).sub_const
    (Real.binEntropy t.high)
  convert! hh using 1
  dsimp [informationCurvature]
  field_simp [ne_of_gt hm.1, ne_of_gt (sub_pos.mpr hm.2)]
  <;> ring

 theorem informationCurvature_neg {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    t.informationCurvature q < 0 := by
  have hm := t.mean_mem hq
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (sq_pos_of_pos t.gap_pos))
    (mul_pos hm.1 (sub_pos.mpr hm.2))

 theorem hasDerivAt_value (w0 bonus cost lambda : ℝ) {q : ℝ}
    (hq : q ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (t.value w0 bonus cost lambda) (t.valueSlope bonus cost lambda q) q := by
  have hh := (((t.hasDerivAt_mean q).mul_const bonus).const_add w0).sub
    ((hasDerivAt_id q).mul_const cost)
  have hh' := hh.add ((t.hasDerivAt_information hq).const_mul lambda)
  convert! hh' using 1 <;> simp [value, valueSlope, Function.comp_def] <;> ring

end BernoulliTechnology

/-- Bernoulli divergence, written with log differences for transparent derivatives. -/
noncomputable def bernoulliKL (p r : ℝ) : ℝ :=
  p*(Real.log p-Real.log r)+(1-p)*(Real.log (1-p)-Real.log (1-r))

 theorem bernoulliKL_self (p : ℝ) : bernoulliKL p p = 0 := by simp [bernoulliKL]

 theorem BernoulliTechnology.informationSlope_zero (t : BernoulliTechnology) :
    t.informationSlope 0 = bernoulliKL t.high t.low := by
  simp only [BernoulliTechnology.informationSlope, BernoulliTechnology.mean, zero_mul,
    add_zero, BernoulliTechnology.gap, Real.binEntropy, Real.log_inv, bernoulliKL]
  ring

 theorem BernoulliTechnology.informationSlope_one (t : BernoulliTechnology) :
    t.informationSlope 1 = -bernoulliKL t.low t.high := by
  have hm : t.mean 1 = t.high := by dsimp [BernoulliTechnology.mean, BernoulliTechnology.gap]; ring
  rw [BernoulliTechnology.informationSlope, hm]
  simp only [BernoulliTechnology.gap, Real.binEntropy, Real.log_inv, bernoulliKL]
  ring

end TraceableAgency.Section4
