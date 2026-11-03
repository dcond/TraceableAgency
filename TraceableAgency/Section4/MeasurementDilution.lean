import TraceableAgency.Section4.MeasurementRange

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3

universe u

abbrev CompensationProbability := Set.Icc (0 : ℝ) 1
abbrev DilutionRate := Set.Ico (0 : ℝ) 1

def compensationZero : CompensationProbability := ⟨0,by constructor <;> norm_num⟩
def compensationOne : CompensationProbability := ⟨1,by constructor <;> norm_num⟩

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def materialLotteryExperiment (op om : O) (b : CompensationProbability) :
    MarkedTerminalExperiment O A where
  RecordType := PUnit.{u+1}
  recordFintype := inferInstance
  recordDecEq := inferInstance
  recordNonempty := inferInstance
  channel := payoffLotteryChannel (binaryPayoffLaw op om b b.2.1 b.2.2)

def sideUtility (v : O → ℝ) (op om : O) (b : CompensationProbability) : ℝ :=
  b.1*v op+(1-b.1)*v om

theorem markedValue_materialLottery (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (op om : O) (b : CompensationProbability) :
    markedValue v lambda q (materialLotteryExperiment op om b) = sideUtility v op om b := by
  change expectedPayoffUtility v q (payoffLotteryChannel _) + lambda*mutualInfo q (payoffLotteryChannel _) = _
  have hz : mutualInfo q (payoffLotteryChannel (A := A) (binaryPayoffLaw op om b b.2.1 b.2.2)) = 0 :=
    mutualInfo_constant _ _
  rw [expectedPayoffUtility_payoffLotteryChannel,hz,expected_binaryPayoffLaw]
  simp [sideUtility]

/-- The side branch occurs with probability `eps`. At zero its unused tag is omitted. -/
noncomputable def dilutionExperiment (eps : DilutionRate) (op om : O)
    (E : MarkedTerminalExperiment O A) (b : CompensationProbability) : MarkedTerminalExperiment O A :=
  if h0 : eps.1 = 0 then E else
    markedPublicMixExperiment eps.1 (lt_of_le_of_ne eps.2.1 (Ne.symm h0)) eps.2.2
      (materialLotteryExperiment op om b) E

theorem dilution_value (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (eps : DilutionRate) (op om : O) (E : MarkedTerminalExperiment O A)
    (b : CompensationProbability) :
    markedValue v lambda q (dilutionExperiment eps op om E b) =
      (1-eps.1)*markedValue v lambda q E + eps.1*sideUtility v op om b := by
  unfold dilutionExperiment
  split_ifs with h0
  · simp [h0]
  · rw [markedValue_publicMix,markedValue_materialLottery]
    ring

noncomputable def markedInformation (q : Dist A) (E : MarkedTerminalExperiment O A) : ℝ :=
  markedValue (fun _ : O => 0) 1 q E

noncomputable def markedMaterial (v : O → ℝ) (q : Dist A) (E : MarkedTerminalExperiment O A) : ℝ :=
  markedValue v 0 q E

theorem markedInformation_eq (q : Dist A) (E : MarkedTerminalExperiment O A) :
    markedInformation q E = @mutualInfo A (O × E.RecordType) _
      (by letI := E.recordFintype; infer_instance) q E.K := by
  letI := E.recordFintype
  simp [markedInformation,markedValue,traceTemperedValue,Independence.expectedPayoffUtility_zero]

theorem markedValue_decomposition (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (E : MarkedTerminalExperiment O A) :
    markedValue v lambda q E = markedMaterial v q E + lambda*markedInformation q E := by
  letI := E.recordFintype
  simp [markedValue,markedMaterial,markedInformation,traceTemperedValue,
    Independence.expectedPayoffUtility_zero]

theorem dilution_information (q : Dist A) (eps : DilutionRate) (op om : O)
    (E : MarkedTerminalExperiment O A) (b : CompensationProbability) :
    markedInformation q (dilutionExperiment eps op om E b) = (1-eps.1)*markedInformation q E := by
  unfold markedInformation
  rw [dilution_value]
  simp [sideUtility]

theorem dilution_material (v : O → ℝ) (q : Dist A) (eps : DilutionRate) (op om : O)
    (E : MarkedTerminalExperiment O A) (b : CompensationProbability) :
    markedMaterial v q (dilutionExperiment eps op om E b) =
      (1-eps.1)*markedMaterial v q E + eps.1*sideUtility v op om b := dilution_value v 0 q eps op om E b

theorem dilution_indifference_iff (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B] (p : Dist B)
    (eps : DilutionRate) (he : 0 < eps.1) (op om : O)
    (E : MarkedTerminalExperiment O A) (D : MarkedTerminalExperiment O B)
    (b b' : CompensationProbability) :
    markedValue v lambda q (dilutionExperiment eps op om E b) =
      markedValue v lambda p (dilutionExperiment eps op om D b') ↔
      eps.1/(1-eps.1)*(sideUtility v op om b-sideUtility v op om b') =
        markedValue v lambda p D-markedValue v lambda q E := by
  have hd : 1-eps.1 ≠ 0 := ne_of_gt (sub_pos.mpr eps.2.2)
  rw [dilution_value,dilution_value]
  field_simp
  constructor <;> intro h <;> nlinarith

theorem equalMaterial_value_gap (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B] (p : Dist B)
    (E : MarkedTerminalExperiment O A) (D : MarkedTerminalExperiment O B)
    (hm : markedMaterial v q E = markedMaterial v p D) :
    markedValue v lambda p D-markedValue v lambda q E =
      lambda*(markedInformation p D-markedInformation q E) := by
  rw [markedValue_decomposition,markedValue_decomposition,hm]
  ring

theorem compensation_difference_range (v : O → ℝ) (op om : O)
    (hu : v om < v op) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    (∃ b b' : CompensationProbability, c*(sideUtility v op om b-sideUtility v op om b') = x) ↔
      |x| ≤ c*(v op-v om) := by
  have hd : 0 < c*(v op-v om) := mul_pos hc (sub_pos.mpr hu)
  constructor
  · rintro ⟨b,b',rfl⟩
    rw [abs_le]
    unfold sideUtility
    constructor <;> nlinarith [b.2.1,b.2.2,b'.2.1,b'.2.2]
  · intro hx
    rcases abs_le.mp hx with ⟨hlo,hhi⟩
    by_cases hx0 : 0 ≤ x
    · let b : CompensationProbability :=
        ⟨x/(c*(v op-v om)),div_nonneg hx0 hd.le,(div_le_one hd).mpr hhi⟩
      refine ⟨b,compensationZero,?_⟩
      dsimp [sideUtility,b,compensationZero]
      field_simp [ne_of_gt hc, ne_of_gt (sub_pos.mpr hu)]
      ring
    · have hn : 0 ≤ -x := by linarith
      let b : CompensationProbability :=
        ⟨(-x)/(c*(v op-v om)),div_nonneg hn hd.le,(div_le_one hd).mpr (by linarith)⟩
      refine ⟨compensationZero,b,?_⟩
      dsimp [sideUtility,b,compensationZero]
      field_simp [ne_of_gt hc, ne_of_gt (sub_pos.mpr hu)]
      ring

theorem dilution_compensation_feasible_iff (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B] (p : Dist B)
    (eps : DilutionRate) (he : 0 < eps.1) (op om : O) (hu : v om < v op)
    (E : MarkedTerminalExperiment O A) (D : MarkedTerminalExperiment O B) :
    (∃ b b' : CompensationProbability,
      markedValue v lambda q (dilutionExperiment eps op om E b) =
        markedValue v lambda p (dilutionExperiment eps op om D b')) ↔
      |markedValue v lambda p D-markedValue v lambda q E| ≤ eps.1/(1-eps.1)*(v op-v om) := by
  simp_rw [dilution_indifference_iff v lambda q p eps he]
  exact compensation_difference_range v op om hu _ (div_pos he (sub_pos.mpr eps.2.2)) _

theorem dilution_max_compensation_bound (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B] (p : Dist B)
    (eps : DilutionRate) (op om : O)
    (E : MarkedTerminalExperiment O A) (D : MarkedTerminalExperiment O B) :
    markedValue v lambda q (dilutionExperiment eps op om E compensationOne) <
      markedValue v lambda p (dilutionExperiment eps op om D compensationZero) ↔
      eps.1/(1-eps.1)*(v op-v om) < markedValue v lambda p D-markedValue v lambda q E := by
  have hd := sub_pos.mpr eps.2.2
  rw [dilution_value,dilution_value]
  simp only [sideUtility,compensationOne,compensationZero,one_mul,sub_self,zero_mul,add_zero,sub_zero,zero_add]
  rw [div_mul_eq_mul_div,div_lt_iff₀ hd]
  constructor <;> intro h <;> nlinarith

end TraceableAgency.Section4
