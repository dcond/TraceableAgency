import TraceableAgency.Section4.MeasurementElicitation
import TraceableAgency.Section3.Independence.Gini

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3
open Section3.Independence

universe u

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

theorem giniInformation_constant {Z : Type u} [Fintype Z]
    (q : Dist A) (d : Dist Z) : giniInformation q (fun _ : A => d) = 0 := by
  rw [giniInformation_eq_posterior]
  unfold posteriorLawIntegral
  rw [outcomeMarginal_constant]
  have ht (z : Z) : d z*squareMass (Channel.posterior (fun _ : A => d) q z) = d z*squareMass q := by
    by_cases hz : 0 < d z
    · rw [show Channel.posterior (fun _ : A => d) q z = q from posterior_constant_of_pos q d z hz]
    · have h0 : d z = 0 := le_antisymm (le_of_not_gt hz) (d.nonneg z)
      simp [h0]
  simp_rw [ht]
  rw [← Finset.sum_mul,d.sum_eq_one,one_mul,sub_self]

theorem giniInformation_fullReveal (q : Dist A) (o : O) :
    giniInformation q (fullRevealAtPayoff o) = gini q := by
  rw [← constantPayoffLift_idChannel,giniInformation_constantPayoffLift]
  unfold giniInformation
  rw [outcomeMarginal_idChannel']
  simp [Channel.idChannel,Dist.pure_apply,sq,mul_self_div_self,q.sum_eq_one,gini]

noncomputable def markedGiniInformation (q : Dist A) (E : MarkedTerminalExperiment O A) : ℝ := by
  letI := E.recordFintype
  exact giniInformation q E.K

noncomputable def markedGiniValue (v : O → ℝ) (q : Dist A) (E : MarkedTerminalExperiment O A) : ℝ :=
  markedMaterial v q E+markedGiniInformation q E

theorem markedGiniInformation_publicMix (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E D : MarkedTerminalExperiment O A) :
    markedGiniInformation q (markedPublicMixExperiment t ht0 ht1 E D) =
      t*markedGiniInformation q E+(1-t)*markedGiniInformation q D := by
  letI := E.recordFintype
  letI := E.recordDecEq
  letI := D.recordFintype
  letI := D.recordDecEq
  change giniInformation q (Relabeling.relabelChannel (Equiv.refl A)
    (sumPayoffRecordEquiv O E.RecordType D.RecordType) (publicMixChannel t ht0 ht1 E.K D.K)) = _
  rw [giniInformation_relabelOutcome,giniInformation_eq_posterior,
    hm_posteriorLawIntegral_publicMixChannel]
  unfold markedGiniInformation
  rw [giniInformation_eq_posterior,giniInformation_eq_posterior]
  ring

theorem markedGiniInformation_materialLottery (q : Dist A) (op om : O) (b : CompensationProbability) :
    markedGiniInformation q (materialLotteryExperiment op om b) = 0 := by
  change giniInformation q (payoffLotteryChannel (binaryPayoffLaw op om b b.2.1 b.2.2) :
    Channel A (O × PUnit.{u+1})) = 0
  exact giniInformation_constant _ _

theorem markedGiniInformation_dilution (q : Dist A) (eps : DilutionRate) (op om : O)
    (E : MarkedTerminalExperiment O A) (b : CompensationProbability) :
    markedGiniInformation q (dilutionExperiment eps op om E b) = (1-eps.1)*markedGiniInformation q E := by
  unfold dilutionExperiment
  split_ifs with h0
  · simp [h0]
  · rw [markedGiniInformation_publicMix,markedGiniInformation_materialLottery]
    ring

theorem markedGiniValue_dilution (v : O → ℝ) (q : Dist A) (eps : DilutionRate) (op om : O)
    (E : MarkedTerminalExperiment O A) (b : CompensationProbability) :
    markedGiniValue v q (dilutionExperiment eps op om E b) =
      (1-eps.1)*markedGiniValue v q E+eps.1*sideUtility v op om b := by
  unfold markedGiniValue
  rw [dilution_material,markedGiniInformation_dilution]
  ring

theorem markedGiniValue_reveal (v : O → ℝ) (q : Dist A) (o : O) :
    markedGiniValue v q (revealExperiment o) = v o+gini q := by
  unfold markedGiniValue markedMaterial
  rw [markedValue_reveal]
  have hg : markedGiniInformation q (revealExperiment (A := A) o) = gini q :=
    giniInformation_fullReveal q o
  rw [hg]
  ring

theorem markedGiniValue_silent (v : O → ℝ) (q : Dist A) (o : O) :
    markedGiniValue v q (silentExperiment o) = v o := by
  unfold markedGiniValue markedMaterial
  rw [markedValue_silent]
  have hg : markedGiniInformation q (silentExperiment (A := A) o) = 0 := by
    change giniInformation q (uninformativeAtPayoff o : Channel A (O × PUnit.{u+1})) = 0
    exact giniInformation_constant _ _
  rw [hg,add_zero]

def GiniElicitationIndifferent (v : O → ℝ) (q : Dist A)
    (eps : DilutionRate) (op om baseline : O) (b : CompensationProbability) : Prop :=
  markedGiniValue v q (dilutionExperiment eps op om (revealExperiment baseline) compensationZero) =
    markedGiniValue v q (dilutionExperiment eps op om (silentExperiment baseline) b)

theorem gini_elicitation_indifferent_iff (v : O → ℝ) (q : Dist A)
    (eps : DilutionRate) (op om baseline : O) (hp : v op = 1) (hm : v om = 0)
    (b : CompensationProbability) :
    GiniElicitationIndifferent v q eps op om baseline b ↔ (1-eps.1)*gini q = eps.1*b.1 := by
  unfold GiniElicitationIndifferent
  rw [markedGiniValue_dilution,markedGiniValue_dilution,markedGiniValue_reveal,markedGiniValue_silent]
  simp only [sideUtility,compensationZero,hp,hm,mul_one,mul_zero,zero_add,add_zero]
  constructor <;> intro h <;> nlinarith

end TraceableAgency.Section4
