import TraceableAgency.Section4.MeasurementTests

/-! Implementation controls and the translation of numerical indifferences
into the paper's actual cross-channel preference comparisons. -/

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

section Values
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

theorem material_utility_elicitation_existsUnique
    (v : O → ℝ) (lambda : ℝ) (op om o : O)
    (hp : v op = 1) (hm : v om = 0) (ho0 : 0 ≤ v o) (ho1 : v o ≤ 1) :
    ∃! b : CompensationProbability,
      markedValue v lambda (Dist.pure (PUnit.unit : PUnit.{u+1})) (silentExperiment o) =
        markedValue v lambda (Dist.pure (PUnit.unit : PUnit.{u+1}))
          (materialLotteryExperiment op om b) := by
  refine ⟨⟨v o,ho0,ho1⟩,?_,?_⟩
  · exact (material_utility_elicitation v lambda op om o hp hm _).mpr rfl
  · intro b hb
    apply Subtype.ext
    exact ((material_utility_elicitation v lambda op om o hp hm b).mp hb).symm

theorem erasing_silence_gives_silence (o : O) :
    recordPostprocess (uninformativeAtPayoff (A := A) o) eraseAllRecordsProcessor =
      uninformativeAtPayoff o := by
  have h := constantPayoffLift_erase o (fun _ : A => Dist.pure (PUnit.unit : PUnit.{u+1}))
  have hs : constantPayoffLift o (fun _ : A => Dist.pure (PUnit.unit : PUnit.{u+1})) =
      uninformativeAtPayoff (A := A) o := by
    ext a z
    rcases z with ⟨o',r⟩
    simp [constantPayoffLift,uninformativeAtPayoff,Dist.pure_apply]
  simpa only [hs] using h

theorem erasing_revelation_and_silence_agree (o : O) :
    recordPostprocess (fullRevealAtPayoff (A := A) o) eraseAllRecordsProcessor =
      recordPostprocess (uninformativeAtPayoff (A := A) o) eraseAllRecordsProcessor := by
  rw [erasing_revelation_gives_silence,erasing_silence_gives_silence]

/-- Successful reports return the same coefficient even when the prior,
number of actions, baseline payoff and dilution rate all change. -/
theorem elicited_prices_agree
    {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B]
    (v : O → ℝ) (lambda : ℝ) (q : Dist A) (p : Dist B)
    (hq : 0 < entropy q) (hp' : 0 < entropy p)
    (epsQ epsP : DilutionRate) (op om baselineQ baselineP : O)
    (hp : v op = 1) (hm : v om = 0) (bQ bP : CompensationProbability)
    (hQ : ElicitationIndifferent v lambda q epsQ op om baselineQ bQ)
    (hP : ElicitationIndifferent v lambda p epsP op om baselineP bP) :
    epsQ.1/(1-epsQ.1)*bQ.1/entropy q = epsP.1/(1-epsP.1)*bP.1/entropy p :=
  (elicited_price v lambda q hq epsQ op om baselineQ hp hm bQ hQ).symm.trans
    (elicited_price v lambda p hp' epsP op om baselineP hp hm bP hP)

end Values

section Preferences
variable {F : FixedPayoffPrefFamily O} {v : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F v lambda)
include hrep

theorem markedPairWeak_iff_markedValue
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q p : Dist A) (E D : MarkedTerminalExperiment O A) :
    MarkedPairWeak F q E p D ↔ markedValue v lambda q E ≥ markedValue v lambda p D := by
  letI := E.recordFintype
  letI := E.recordDecEq
  letI := E.recordNonempty
  letI := D.recordFintype
  letI := D.recordDecEq
  letI := D.recordNonempty
  exact pairWeak_iff_value_ge hrep q E.K p D.K

theorem markedPairIndifferent_iff_markedValue
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E D : MarkedTerminalExperiment O A) :
    MarkedPairIndifferent F q E D ↔ markedValue v lambda q E = markedValue v lambda q D := by
  change (MarkedPairWeak F q E q D ∧ MarkedPairWeak F q D q E) ↔ _
  rw [markedPairWeak_iff_markedValue hrep,markedPairWeak_iff_markedValue hrep]
  exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩

theorem pairIndiff_iff_valueIndex (E D : FiniteExperiment O) :
    pairIndiff F E.prior E.channel D.prior D.channel ↔
      valueIndex v lambda E = valueIndex v lambda D := by
  unfold pairIndiff
  dsimp only
  rw [hrep,hrep,traceTemperedValue_commonBlock_left,traceTemperedValue_commonBlock_right]
  exact ⟨fun h => le_antisymm h.2 h.1,fun h => ⟨h.ge,h.le⟩⟩

theorem behavioral_information_price (E D : FiniteExperiment O)
    (hind : pairIndiff F E.prior E.channel D.prior D.channel)
    (hne : informationIndex E ≠ informationIndex D) :
    (materialIndex v D-materialIndex v E)/(informationIndex E-informationIndex D) = lambda :=
  indifference_information_price v lambda E D ((pairIndiff_iff_valueIndex hrep E D).mp hind) hne

theorem behavioral_elicitation_iff
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (eps : DilutionRate) (op om baseline : O) (b : CompensationProbability) :
    MarkedPairIndifferent F q
      (dilutionExperiment eps op om (revealExperiment baseline) compensationZero)
      (dilutionExperiment eps op om (silentExperiment baseline) b) ↔
        ElicitationIndifferent v lambda q eps op om baseline b :=
  markedPairIndifferent_iff_markedValue hrep q _ _

theorem behavioral_elicitation_existsUnique_iff
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (hl : 0 < lambda) (q : Dist A) (hH : 0 < entropy q) (eps : DilutionRate)
    (he : 0 < eps.1) (op om baseline : O) (hp : v op = 1) (hm : v om = 0) :
    (∃! b : CompensationProbability, MarkedPairIndifferent F q
      (dilutionExperiment eps op om (revealExperiment baseline) compensationZero)
      (dilutionExperiment eps op om (silentExperiment baseline) b)) ↔
        lambda*entropy q ≤ eps.1/(1-eps.1) := by
  simp_rw [behavioral_elicitation_iff hrep]
  exact elicitation_existsUnique_iff v hl q hH eps he op om baseline hp hm

theorem behavioral_elicited_price
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hH : 0 < entropy q) (eps : DilutionRate) (op om baseline : O)
    (hp : v op = 1) (hm : v om = 0) (b : CompensationProbability)
    (hb : MarkedPairIndifferent F q
      (dilutionExperiment eps op om (revealExperiment baseline) compensationZero)
      (dilutionExperiment eps op om (silentExperiment baseline) b)) :
    lambda = eps.1/(1-eps.1)*b.1/entropy q :=
  elicited_price v lambda q hH eps op om baseline hp hm b
    ((behavioral_elicitation_iff hrep q eps op om baseline b).mp hb)

theorem erased_trace_controls_indifferent
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) (o : O) :
    pairIndiff F q (recordPostprocess (fullRevealAtPayoff (A := A) o) eraseAllRecordsProcessor)
      q (recordPostprocess (uninformativeAtPayoff (A := A) o) eraseAllRecordsProcessor) := by
  apply (pairIndiff_iff_valueIndex hrep (.ofChannel q _) (.ofChannel q _)).mpr
  exact congrArg (traceTemperedValue v lambda q) (erasing_revelation_and_silence_agree (A := A) o)

end Preferences

end TraceableAgency.Section4
