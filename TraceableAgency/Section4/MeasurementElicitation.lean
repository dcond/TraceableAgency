import TraceableAgency.Section4.MeasurementDilution
import TraceableAgency.Section4.TraceTestQualitative

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3

universe u

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

def ElicitationIndifferent (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (eps : DilutionRate) (op om baseline : O) (b : CompensationProbability) : Prop :=
  markedValue v lambda q (dilutionExperiment eps op om (revealExperiment baseline) compensationZero) =
    markedValue v lambda q (dilutionExperiment eps op om (silentExperiment baseline) b)

theorem elicitation_gap (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (eps : DilutionRate) (op om baseline : O) (hp : v op = 1) (hm : v om = 0)
    (b : CompensationProbability) :
    markedValue v lambda q (dilutionExperiment eps op om (revealExperiment baseline) compensationZero) -
      markedValue v lambda q (dilutionExperiment eps op om (silentExperiment baseline) b) =
      (1-eps.1)*lambda*entropy q-eps.1*b.1 := by
  rw [dilution_value,dilution_value,markedValue_reveal,markedValue_silent]
  simp only [sideUtility,compensationZero,hp,hm,mul_one,mul_zero,zero_add,add_zero]
  ring

theorem elicitation_indifferent_iff (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (eps : DilutionRate) (op om baseline : O) (hp : v op = 1) (hm : v om = 0)
    (b : CompensationProbability) :
    ElicitationIndifferent v lambda q eps op om baseline b ↔
      (1-eps.1)*lambda*entropy q = eps.1*b.1 := by
  unfold ElicitationIndifferent
  rw [← sub_eq_zero,elicitation_gap v lambda q eps op om baseline hp hm b,sub_eq_zero]

theorem elicitation_probability_eq (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (eps : DilutionRate) (he : 0 < eps.1) (op om baseline : O)
    (hp : v op = 1) (hm : v om = 0) (b : CompensationProbability) :
    ElicitationIndifferent v lambda q eps op om baseline b ↔
      b.1 = (1-eps.1)*lambda*entropy q/eps.1 := by
  rw [elicitation_indifferent_iff v lambda q eps op om baseline hp hm]
  rw [eq_div_iff (ne_of_gt he)]
  constructor <;> intro h <;> nlinarith

/-- Exact existence and uniqueness in the allowed probability interval. -/
theorem elicitation_existsUnique_iff (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (q : Dist A) (hH : 0 < entropy q) (eps : DilutionRate) (he : 0 < eps.1)
    (op om baseline : O) (hp : v op = 1) (hm : v om = 0) :
    (∃! b : CompensationProbability, ElicitationIndifferent v lambda q eps op om baseline b) ↔
      lambda*entropy q ≤ eps.1/(1-eps.1) := by
  have hd : 0 < 1-eps.1 := sub_pos.mpr eps.2.2
  have hbound : ((1-eps.1)*lambda*entropy q/eps.1 ≤ 1) ↔
      lambda*entropy q ≤ eps.1/(1-eps.1) := by
    rw [div_le_one he,le_div_iff₀ hd]
    ring_nf
  constructor
  · rintro ⟨b,hb,_⟩
    apply hbound.mp
    rw [← (elicitation_probability_eq v lambda q eps he op om baseline hp hm b).mp hb]
    exact b.2.2
  · intro hb
    let b : CompensationProbability :=
      ⟨(1-eps.1)*lambda*entropy q/eps.1, (div_pos (mul_pos (mul_pos hd hl) hH) he).le,
        hbound.mpr hb⟩
    refine ⟨b,?_,?_⟩
    · exact (elicitation_probability_eq v lambda q eps he op om baseline hp hm b).mpr rfl
    · intro b' hb'
      apply Subtype.ext
      exact (elicitation_probability_eq v lambda q eps he op om baseline hp hm b').mp hb'

theorem elicitation_strict_infeasible (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (eps : DilutionRate) (op om baseline : O) (hp : v op = 1) (hm : v om = 0)
    (hinf : eps.1/(1-eps.1) < lambda*entropy q) (b : CompensationProbability) :
    markedValue v lambda q (dilutionExperiment eps op om (silentExperiment baseline) b) <
      markedValue v lambda q (dilutionExperiment eps op om (revealExperiment baseline) compensationZero) := by
  apply sub_pos.mp
  rw [elicitation_gap v lambda q eps op om baseline hp hm]
  have hh := (div_lt_iff₀ (sub_pos.mpr eps.2.2)).mp hinf
  have hb := mul_le_mul_of_nonneg_left b.2.2 eps.2.1
  nlinarith

theorem elicited_price (v : O → ℝ) (lambda : ℝ) (q : Dist A) (hH : 0 < entropy q)
    (eps : DilutionRate) (op om baseline : O) (hp : v op = 1) (hm : v om = 0)
    (b : CompensationProbability) (hb : ElicitationIndifferent v lambda q eps op om baseline b) :
    lambda = eps.1/(1-eps.1)*b.1/entropy q := by
  have hh := (elicitation_indifferent_iff v lambda q eps op om baseline hp hm b).mp hb
  field_simp [ne_of_gt (sub_pos.mpr eps.2.2),ne_of_gt hH]
  nlinarith

theorem uniform_elicited_price (v : O → ℝ) (lambda : ℝ)
    (hcard : 2 ≤ Fintype.card A) (eps : DilutionRate) (op om baseline : O)
    (hp : v op = 1) (hm : v om = 0) (b : CompensationProbability)
    (hb : ElicitationIndifferent v lambda (Dist.uniform (A := A)) eps op om baseline b) :
    lambda = eps.1*b.1/((1-eps.1)*Real.log (Fintype.card A)) := by
  have hlog : 0 < Real.log (Fintype.card A) := Real.log_pos (by exact_mod_cast (by omega : 1 < Fintype.card A))
  have hh := elicited_price v lambda Dist.uniform
    (by simpa [entropy_uniform_eq_log_card] using hlog) eps op om baseline hp hm b hb
  rw [entropy_uniform_eq_log_card] at hh
  rw [hh]
  field_simp [ne_of_gt (sub_pos.mpr eps.2.2),ne_of_gt hlog]

theorem maximal_compensation_information_bound (v : O → ℝ) (lambda : ℝ)
    (q : Dist A) (hH : 0 < entropy q) (eps : DilutionRate) (op om baseline : O)
    (hp : v op = 1) (hm : v om = 0) :
    (markedValue v lambda q (dilutionExperiment eps op om (silentExperiment baseline) compensationOne) <
      markedValue v lambda q (dilutionExperiment eps op om (revealExperiment baseline) compensationZero)) ↔
      eps.1/((1-eps.1)*entropy q) < lambda := by
  rw [← sub_pos,elicitation_gap v lambda q eps op om baseline hp hm]
  change 0 < (1-eps.1)*lambda*entropy q-eps.1*1 ↔ _
  rw [div_lt_iff₀ (mul_pos (sub_pos.mpr eps.2.2) hH)]
  constructor <;> intro h <;> nlinarith

theorem eventually_feasible_dilution (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (q : Dist A) (hH : 0 < entropy q) (op om baseline : O) (hp : v op = 1) (hm : v om = 0) :
    ∃ eps : DilutionRate, 0 < eps.1 ∧
      ∃! b : CompensationProbability, ElicitationIndifferent v lambda q eps op om baseline b := by
  let x := lambda*entropy q
  have hx : 0 < x := mul_pos hl hH
  let eps : DilutionRate := ⟨x/(1+x), (div_pos hx (by linarith)).le,
    (div_lt_one (by linarith : 0 < 1+x)).mpr (by linarith)⟩
  have he : 0 < eps.1 := div_pos hx (by linarith)
  refine ⟨eps,he,(elicitation_existsUnique_iff v hl q hH eps he op om baseline hp hm).mpr ?_⟩
  change x ≤ (x/(1+x))/(1-x/(1+x))
  have hh : (x/(1+x))/(1-x/(1+x)) = x := by field_simp; ring
  rw [hh]

theorem material_utility_elicitation (v : O → ℝ) (lambda : ℝ) (op om o : O)
    (hp : v op = 1) (hm : v om = 0) (b : CompensationProbability) :
    markedValue v lambda (Dist.pure (PUnit.unit : PUnit.{u+1})) (silentExperiment o) =
      markedValue v lambda (Dist.pure (PUnit.unit : PUnit.{u+1})) (materialLotteryExperiment op om b) ↔
        v o = b.1 := by
  rw [markedValue_silent,markedValue_materialLottery]
  simp [sideUtility,hp,hm]

theorem revelation_strictly_beats_silence (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (q : Dist A) (hH : 0 < entropy q) (o : O) :
    markedValue v lambda q (silentExperiment o) < markedValue v lambda q (revealExperiment o) := by
  rw [markedValue_silent,markedValue_reveal]
  linarith [mul_pos hl hH]

theorem erasing_revelation_gives_silence (o : O) :
    recordPostprocess (fullRevealAtPayoff (A := A) o) eraseAllRecordsProcessor =
      uninformativeAtPayoff o := by
  rw [← constantPayoffLift_idChannel]
  exact constantPayoffLift_erase o _

end TraceableAgency.Section4
