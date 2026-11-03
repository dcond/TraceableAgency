import TraceableAgency.Section4.MeasurementGini
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3
open Section3.Independence

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

noncomputable def fairMeasurementPrior : Dist RelevanceBit.{u} := Dist.uniform
noncomputable def quarterMeasurementPrior : Dist RelevanceBit.{u} := publicCoin (1/4) (by norm_num) (by norm_num)

theorem fairMeasurement_entropy : entropy fairMeasurementPrior.{u} = Real.log 2 := by
  simp [fairMeasurementPrior,entropy_uniform_eq_log_card]

theorem quarterMeasurement_entropy : entropy quarterMeasurementPrior.{u} =
    (1/4:ℝ)*Real.log 4+(3/4:ℝ)*Real.log (4/3) := by
  have h4 : Real.log (1/4:ℝ) = -Real.log 4 := by simpa using Real.log_inv (4:ℝ)
  have h43 : Real.log (3/4:ℝ) = -Real.log (4/3:ℝ) := by
    convert Real.log_inv (4/3:ℝ) using 1; norm_num
  norm_num [entropy,Section3.sum_relevanceBit,quarterMeasurementPrior,
    publicCoin_true,publicCoin_false,entropyTerm,h4,h43]

theorem quarterMeasurement_entropy_log23 : entropy quarterMeasurementPrior.{u} =
    2*Real.log 2-(3/4:ℝ)*Real.log 3 := by
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    convert Real.log_pow (2:ℝ) 2 using 1 <;> norm_num
  rw [quarterMeasurement_entropy,Real.log_div (by norm_num) (by norm_num),h4]
  ring

theorem quarterMeasurement_entropy_pos : 0 < entropy quarterMeasurementPrior.{u} := by
  apply entropy_pos_of_fullSupport_nontrivial
  intro a
  cases a with
  | up b => cases b <;> norm_num [quarterMeasurementPrior,publicCoin_true,publicCoin_false]

theorem fairMeasurement_gini : gini fairMeasurementPrior.{u} = 1/2 := by
  norm_num [gini,squareMass,fairMeasurementPrior,Dist.uniform_apply,Section3.sum_relevanceBit]

theorem quarterMeasurement_gini : gini quarterMeasurementPrior.{u} = 3/8 := by
  norm_num [gini,squareMass,quarterMeasurementPrior,Section3.sum_relevanceBit,publicCoin_true,publicCoin_false]

theorem elicitation_two_prior_ratio
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda) (q : Dist A) (p : Dist B)
    (hHp : 0 < entropy p) (eps : DilutionRate) (he : 0 < eps.1)
    (op om baselineQ baselineP : O) (hp : v op = 1) (hm : v om = 0)
    (bQ bP : CompensationProbability)
    (hQ : ElicitationIndifferent v lambda q eps op om baselineQ bQ)
    (hP : ElicitationIndifferent v lambda p eps op om baselineP bP) :
    bQ.1/bP.1 = entropy q/entropy p := by
  have hq := (elicitation_indifferent_iff v lambda q eps op om baselineQ hp hm bQ).mp hQ
  have hp' := (elicitation_indifferent_iff v lambda p eps op om baselineP hp hm bP).mp hP
  have hbP : 0 < bP.1 := by
    have hprod : 0 < eps.1*bP.1 := by
      rw [← hp']
      exact mul_pos (mul_pos (sub_pos.mpr eps.2.2) hl) hHp
    exact (mul_pos_iff_of_pos_left he).mp hprod
  apply (div_eq_div_iff (ne_of_gt hbP) (ne_of_gt hHp)).mpr
  have hcross : eps.1*(bQ.1*entropy p-entropy q*bP.1) = 0 := by
    nlinarith [congrArg (fun x : ℝ => x*entropy p) hq,
      congrArg (fun x : ℝ => x*entropy q) hp']
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcross).resolve_left (ne_of_gt he))

theorem shannon_two_prior_prediction
    (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (eps : DilutionRate) (he : 0 < eps.1) (op om baselineQ baselineP : O)
    (hp : v op = 1) (hm : v om = 0) (bQ bP : CompensationProbability)
    (hQ : ElicitationIndifferent v lambda fairMeasurementPrior.{u} eps op om baselineQ bQ)
    (hP : ElicitationIndifferent v lambda quarterMeasurementPrior.{u} eps op om baselineP bP) :
    bQ.1/bP.1 = Real.log 2/((1/4:ℝ)*Real.log 4+(3/4:ℝ)*Real.log (4/3)) := by
  have hh := elicitation_two_prior_ratio v hl _ _ quarterMeasurement_entropy_pos
    eps he op om baselineQ baselineP hp hm bQ bP hQ hP
  simpa only [fairMeasurement_entropy,quarterMeasurement_entropy] using hh

/-- The exact Shannon ratio rounds to 1.23 at two decimal places. -/
theorem shannon_two_prior_ratio_approx :
    |Real.log 2/((1/4:ℝ)*Real.log 4+(3/4:ℝ)*Real.log (4/3))-(1.23:ℝ)| < 0.005 := by
  have hden : (1/4:ℝ)*Real.log 4+(3/4:ℝ)*Real.log (4/3) =
      2*Real.log 2-(3/4:ℝ)*Real.log 3 :=
    quarterMeasurement_entropy.{0}.symm.trans quarterMeasurement_entropy_log23.{0}
  rw [hden]
  have hd : 0 < 2*Real.log 2-(3/4:ℝ)*Real.log 3 := by
    linarith [Real.log_two_gt_d9,Real.log_three_lt_d9]
  have hlo : (1.225:ℝ) < Real.log 2/(2*Real.log 2-(3/4:ℝ)*Real.log 3) := by
    apply (lt_div_iff₀ hd).mpr
    linarith [Real.log_two_lt_d9,Real.log_three_gt_d9]
  have hhi : Real.log 2/(2*Real.log 2-(3/4:ℝ)*Real.log 3) < (1.235:ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    linarith [Real.log_two_gt_d9,Real.log_three_lt_d9]
  rw [abs_lt]
  constructor <;> linarith

theorem gini_elicitation_two_prior_ratio
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (v : O → ℝ) (q : Dist A) (p : Dist B) (hGp : 0 < gini p)
    (eps : DilutionRate) (he : 0 < eps.1)
    (op om baselineQ baselineP : O) (hp : v op = 1) (hm : v om = 0)
    (bQ bP : CompensationProbability)
    (hQ : GiniElicitationIndifferent v q eps op om baselineQ bQ)
    (hP : GiniElicitationIndifferent v p eps op om baselineP bP) :
    bQ.1/bP.1 = gini q/gini p := by
  have hq := (gini_elicitation_indifferent_iff v q eps op om baselineQ hp hm bQ).mp hQ
  have hp' := (gini_elicitation_indifferent_iff v p eps op om baselineP hp hm bP).mp hP
  have hbP : 0 < bP.1 := by
    have hprod : 0 < eps.1*bP.1 := by
      rw [← hp']
      exact mul_pos (sub_pos.mpr eps.2.2) hGp
    exact (mul_pos_iff_of_pos_left he).mp hprod
  apply (div_eq_div_iff (ne_of_gt hbP) (ne_of_gt hGp)).mpr
  have hcross : eps.1*(bQ.1*gini p-gini q*bP.1) = 0 := by
    nlinarith [congrArg (fun x : ℝ => x*gini p) hq,
      congrArg (fun x : ℝ => x*gini q) hp']
  exact sub_eq_zero.mp ((mul_eq_zero.mp hcross).resolve_left (ne_of_gt he))

theorem gini_two_prior_prediction
    (v : O → ℝ) (eps : DilutionRate) (he : 0 < eps.1) (op om baselineQ baselineP : O)
    (hp : v op = 1) (hm : v om = 0) (bQ bP : CompensationProbability)
    (hQ : GiniElicitationIndifferent v fairMeasurementPrior.{u} eps op om baselineQ bQ)
    (hP : GiniElicitationIndifferent v quarterMeasurementPrior.{u} eps op om baselineP bP) :
    bQ.1/bP.1 = 4/3 := by
  have hh := gini_elicitation_two_prior_ratio v _ _ (by rw [quarterMeasurement_gini]; norm_num)
    eps he op om baselineQ baselineP hp hm bQ bP hQ hP
  norm_num [fairMeasurement_gini,quarterMeasurement_gini] at hh ⊢
  exact hh

section Capped
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def cappedMarkedValue (v : O → ℝ) (c : ℝ) (q : Dist A)
    (E : MarkedTerminalExperiment O A) : ℝ :=
  markedMaterial v q E+min (markedInformation q E) c

def CappedElicitationIndifferent (v : O → ℝ) (c : ℝ) (q : Dist A)
    (eps : DilutionRate) (op om baseline : O) (b : CompensationProbability) : Prop :=
  cappedMarkedValue v c q (dilutionExperiment eps op om (revealExperiment baseline) compensationZero) =
    cappedMarkedValue v c q (dilutionExperiment eps op om (silentExperiment baseline) b)

theorem capped_elicitation_indifferent_iff (v : O → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (q : Dist A) (eps : DilutionRate) (op om baseline : O)
    (hp : v op = 1) (hm : v om = 0) (b : CompensationProbability) :
    CappedElicitationIndifferent v c q eps op om baseline b ↔
      eps.1*b.1 = min ((1-eps.1)*entropy q) c := by
  unfold CappedElicitationIndifferent cappedMarkedValue
  rw [dilution_material,dilution_material,dilution_information,dilution_information]
  unfold markedMaterial markedInformation
  rw [markedValue_reveal,markedValue_silent,markedValue_reveal,markedValue_silent]
  simp only [zero_mul,add_zero,zero_add,one_mul,mul_zero,min_eq_left hc,
    sideUtility,compensationZero,hp,hm,mul_one]
  constructor <;> intro h <;> nlinarith

theorem capped_recovered_coefficient (v : O → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (q : Dist A) (hH : 0 < entropy q) (eps : DilutionRate) (op om baseline : O)
    (hp : v op = 1) (hm : v om = 0) (b : CompensationProbability)
    (hb : CappedElicitationIndifferent v c q eps op om baseline b) :
    eps.1/(1-eps.1)*b.1/entropy q = min 1 (c/((1-eps.1)*entropy q)) := by
  have hd : 0 < (1-eps.1)*entropy q := mul_pos (sub_pos.mpr eps.2.2) hH
  have he := (capped_elicitation_indifferent_iff v hc q eps op om baseline hp hm b).mp hb
  have hr : eps.1/(1-eps.1)*b.1/entropy q = (eps.1*b.1)/((1-eps.1)*entropy q) := by
    field_simp [ne_of_gt (sub_pos.mpr eps.2.2),ne_of_gt hH]
  rw [hr,he]
  by_cases hdc : (1-eps.1)*entropy q ≤ c
  · rw [min_eq_left hdc,div_self (ne_of_gt hd),min_eq_left ((le_div_iff₀ hd).mpr (by simpa using hdc))]
  · have hcd := le_of_not_ge hdc
    rw [min_eq_right hcd,min_eq_right ((div_le_one hd).mpr hcd)]

end Capped

end TraceableAgency.Section4
