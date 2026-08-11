/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.GlobalTraceScale

/-!
# Constant-low marked experiments

Any marked experiment whose payoff coordinate is surely the chosen material
low outcome is exactly the constant-payoff lift of the pure experiment carried
by its record coordinate.  Consequently its normalized marked utility is the
global trace coefficient times the mutual information of its original joint
channel.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A R : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype R]

/-! ## Extracting the pure record experiment -/

/-- The record channel obtained by taking the row of a marked channel at a
payoff that occurs surely. -/
noncomputable def surePayoffRecordChannel
    (o0 : O) (K : Channel A (O × R))
    (hOff : ∀ (a : A) (o : O) (r : R), o ≠ o0 → K a (o, r) = 0) :
    Channel A R :=
  fun a ↦
    { prob := fun r ↦ K a (o0, r)
      nonneg := fun r ↦ (K a).nonneg (o0, r)
      sum_eq_one := by
        calc
          (∑ r : R, K a (o0, r)) =
              ∑ o : O, ∑ r : R, K a (o, r) := by
            symm
            rw [Finset.sum_eq_single o0]
            · intro o _ho hne
              apply Finset.sum_eq_zero
              intro r _hr
              exact hOff a o r hne
            · simp
          _ = 1 := by
            simpa only [Fintype.sum_prod_type] using (K a).sum_eq_one }

@[simp]
theorem surePayoffRecordChannel_apply
    (o0 : O) (K : Channel A (O × R))
    (hOff : ∀ (a : A) (o : O) (r : R), o ≠ o0 → K a (o, r) = 0)
    (a : A) (r : R) :
    surePayoffRecordChannel o0 K hOff a r = K a (o0, r) :=
  rfl

/-- The extracted record channel, bundled as an ordinary finite experiment. -/
noncomputable abbrev surePayoffRecordExperiment
    (o0 : O) (E : MarkedTerminalExperiment O A)
    (hOff : ∀ (a : A) (o : O) (r : E.RecordType),
      o ≠ o0 → E.K a (o, r) = 0) :
    FiniteExperimentOn A where
  OutcomeType := E.RecordType
  outFintype := E.recordFintype
  outDecEq := E.recordDecEq
  channel := by
    letI : Fintype E.RecordType := E.recordFintype
    exact surePayoffRecordChannel o0 E.K hOff

/-- Reattaching the sure payoff to the extracted record experiment recovers
the original joint channel pointwise. -/
theorem constantPayoffLift_surePayoffRecordExperiment
    (o0 : O) (E : MarkedTerminalExperiment O A)
    (hOff : ∀ (a : A) (o : O) (r : E.RecordType),
      o ≠ o0 → E.K a (o, r) = 0) :
    @constantPayoffLift O A
        (surePayoffRecordExperiment o0 E hOff).OutcomeType
        inferInstance inferInstance
        (surePayoffRecordExperiment o0 E hOff).outFintype
        o0 (surePayoffRecordExperiment o0 E hOff).P = E.K := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  funext a
  apply TraceableAgency.Dist.ext
  rintro ⟨o, r⟩
  by_cases ho : o = o0
  · subst o
    rw [constantPayoffLift_apply_same]
    change surePayoffRecordChannel o0 E.K hOff a r = E.K a (o0, r)
    rfl
  · rw [constantPayoffLift_apply, if_neg ho, hOff a o r ho]

/-! ## Entropy and marked-law transport -/

/-- Adding a deterministic payoff coordinate to an outcome does not change
the entropy of a channel row. -/
theorem entropy_constantPayoffLift_row
    (o0 : O) (P : Channel A R) (a : A) :
    entropy (constantPayoffLift o0 P a) = entropy (P a) := by
  classical
  unfold entropy
  rw [Fintype.sum_prod_type, Finset.sum_eq_single o0]
  · simp
  · intro o _ho hne
    simp [constantPayoffLift, hne, entropyTerm_zero]
  · simp

/-- The outcome marginal of a constant-payoff lift is the corresponding
constant-payoff lift of the original outcome marginal. -/
theorem outcomeMarginal_constantPayoffLift_apply
    (o0 : O) (P : Channel A R) (q : TraceableAgency.Dist A)
    (o : O) (r : R) :
    Channel.outcomeMarginal (constantPayoffLift o0 P) q (o, r) =
      if o = o0 then Channel.outcomeMarginal P q r else 0 := by
  classical
  simp only [Channel.outcomeMarginal_apply]
  by_cases ho : o = o0
  · subst o
    simp
  · simp [constantPayoffLift, ho]

/-- Adding a deterministic payoff coordinate to an experiment leaves mutual
information unchanged. -/
theorem mutualInfo_constantPayoffLift
    (o0 : O) (q : TraceableAgency.Dist A) (P : Channel A R) :
    mutualInfo q (constantPayoffLift o0 P) = mutualInfo q P := by
  classical
  unfold mutualInfo
  have hmarg :
      entropy (Channel.outcomeMarginal (constantPayoffLift o0 P) q) =
        entropy (Channel.outcomeMarginal P q) := by
    unfold entropy
    rw [Fintype.sum_prod_type, Finset.sum_eq_single o0]
    · simp [outcomeMarginal_constantPayoffLift_apply]
    · intro o _ho hne
      simp [outcomeMarginal_constantPayoffLift_apply, hne, entropyTerm_zero]
    · simp
  rw [hmarg]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  rw [entropy_constantPayoffLift_row]

/-- The original marked experiment and the constant-payoff lift of its
extracted record experiment have exactly the same marked terminal law. -/
theorem sameMarkedTerminalLaw_surePayoffRecordExperiment
    (q : TraceableAgency.Dist A) (o0 : O)
    (E : MarkedTerminalExperiment O A)
    (hOff : ∀ (a : A) (o : O) (r : E.RecordType),
      o ≠ o0 → E.K a (o, r) = 0) :
    SameMarkedTerminalLaw q E
      (constantPayoffMarkedExperiment o0
        (surePayoffRecordExperiment o0 E hOff)) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  let EP := surePayoffRecordExperiment o0 E hOff
  letI : Fintype EP.OutcomeType := EP.outFintype
  letI : DecidableEq EP.OutcomeType := EP.outDecEq
  intro phi
  have hK : constantPayoffLift o0 EP.P = E.K := by
    exact constantPayoffLift_surePayoffRecordExperiment o0 E hOff
  change
    (∑ z : O × E.RecordType,
      Channel.outcomeMarginal E.K q z *
        phi (z.1, Channel.posterior E.K q z)) =
      ∑ z : O × E.RecordType,
        Channel.outcomeMarginal
            (constantPayoffLift o0
              EP.P) q z *
          phi (z.1, Channel.posterior
            (constantPayoffLift o0
              EP.P) q z)
  rw [hK]

/-! ## Global constant-low formula -/

/-- A pointwise sure-low marked experiment has normalized value equal to the
single global trace coefficient times the mutual information of its original
joint payoff-record channel. -/
theorem normalizedMarkedUtility_eq_globalTraceLambda_mul_mutualInfo_of_sureLow
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (E : MarkedTerminalExperiment O A)
    (hLow : ∀ (a : A) (o : O) (r : E.RecordType),
      o ≠ materialLowOutcome F h → E.K a (o, r) = 0) :
    normalizedMarkedUtility F h q hq E =
      globalTraceLambda F h *
        @mutualInfo A (O × E.RecordType) inferInstance
          (@instFintypeProd O E.RecordType inferInstance E.recordFintype)
          q E.K := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  let EP := surePayoffRecordExperiment (materialLowOutcome F h) E hLow
  letI : Fintype EP.OutcomeType := EP.outFintype
  letI : DecidableEq EP.OutcomeType := EP.outDecEq
  have hsame := sameMarkedTerminalLaw_surePayoffRecordExperiment q
    (materialLowOutcome F h) E hLow
  calc
    normalizedMarkedUtility F h q hq E =
        normalizedMarkedUtility F h q hq
          (constantPayoffMarkedExperiment (materialLowOutcome F h) EP) :=
      normalizedMarkedUtility_respects_sameMarkedTerminalLaw
        F h q hq _ _ hsame
    _ = globalTraceLambda F h * mutualInfo q EP.P := by
      exact normalizedMarkedUtility_constantLow_eq_globalTraceLambda_mul_mutualInfo
        F h q hq EP
    _ = globalTraceLambda F h * mutualInfo q E.K := by
      congr 1
      calc
        mutualInfo q EP.P =
            mutualInfo q (constantPayoffLift (materialLowOutcome F h) EP.P) :=
          (mutualInfo_constantPayoffLift
            (materialLowOutcome F h) q EP.P).symm
        _ = mutualInfo q E.K := by
          rw [constantPayoffLift_surePayoffRecordExperiment
            (materialLowOutcome F h) E hLow]

end TraceableAgency.Theorem1
