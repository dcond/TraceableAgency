/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TraceableAgency.Theorem1.MaterialCalibration.Calibration
import TraceableAgency.Theorem1.PayoffBranchTelescope

/-!
# Material payoff separation before information is identified

Material calibration identifies the coefficient of each reached continuation
with its probability.  Applied to deterministic payoffs, this gives expected
material utility plus the value of the original record at a constant payoff.
The record value is left unidentified throughout this file.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- A deterministic, action-independent payoff has its normalized material
utility at every full-support prior. -/
theorem normalizedMarkedUtility_purePayoff_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (o : O) :
    normalizedMarkedUtility F h q hq
        (markedPayoffLotteryExperiment (Dist.pure o)) =
      materialPayoffUtility F h o := by
  rw [normalizedMarkedUtility_payoffLottery,
    expectedPayoffUtility_payoffLotteryChannel]
  simp [payoffLotteryExpected, Dist.pure_apply]

/-- Changing a deterministic payoff on a reached branch has its probability
as coefficient, for any constant baseline payoff. -/
theorem normalizedMarkedUtility_payoffBranch_increment_of_positive_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o o0 : O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ o0) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (fun _ ↦ o0)) =
      Channel.outcomeMarginal P q target *
        (materialPayoffUtility F h o - materialPayoffUtility F h o0) := by
  have hnum := normalizedMarkedUtility_supportInsertion_difference_material
    F h q hq P target htarget o0
      (markedPayoffLotteryExperiment
        (A := supportSubtype (branchPosterior P q target)) (Dist.pure o))
      (markedPayoffLotteryExperiment
        (A := supportSubtype (branchPosterior P q target)) (Dist.pure o0))
  rw [materialCalibration_normalizedMarkedUtility_supportInsertion_purePayoff,
    materialCalibration_normalizedMarkedUtility_supportInsertion_purePayoff,
    normalizedMarkedUtility_purePayoff_material,
    normalizedMarkedUtility_purePayoff_material] at hnum
  have hbase : updateBranchPayoff (fun _ : Y ↦ o0) target o0 =
      (fun _ : Y ↦ o0) := by
    funext y
    simp [updateBranchPayoff]
  simpa only [hbase] using hnum

/-- The same payoff increment for every branch.  At a null branch, equality
of marked terminal laws makes both sides zero. -/
theorem normalizedMarkedUtility_payoffBranch_increment_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (o o0 : O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ o0) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (fun _ ↦ o0)) =
      Channel.outcomeMarginal P q target *
        (materialPayoffUtility F h o - materialPayoffUtility F h o0) := by
  by_cases hpos : 0 < Channel.outcomeMarginal P q target
  · exact normalizedMarkedUtility_payoffBranch_increment_of_positive_material
      F h q hq P target hpos o o0
  · have hzero : Channel.outcomeMarginal P q target = 0 :=
      le_antisymm (le_of_not_gt hpos) ((Channel.outcomeMarginal P q).nonneg target)
    have hbase : updateBranchPayoff (fun _ : Y ↦ o0) target o0 =
        (fun _ : Y ↦ o0) := by
      funext y
      simp [updateBranchPayoff]
    have hlaw : SameMarkedTerminalLaw q
        (payoffBranchExperiment P (updateBranchPayoff (fun _ ↦ o0) target o))
        (payoffBranchExperiment P (fun _ ↦ o0)) := by
      intro phi
      have hdir := markedTerminalIntegral_payoffBranch_update_difference
        q P target o o0 (fun _ ↦ o0) phi
      rw [hbase, hzero, zero_mul] at hdir
      exact sub_eq_zero.mp hdir
    have hvalue := normalizedMarkedUtility_respects_sameMarkedTerminalLaw
      F h q hq _ _ hlaw
    rw [hvalue, sub_self, hzero, zero_mul]

/-- Deterministic terminal payoffs separate from the record's value.  This
formula is independent of how that record value will subsequently be identified. -/
theorem normalizedMarkedUtility_payoffBranch_separation_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (g : Y → O) (o0 : O) :
    normalizedMarkedUtility F h q hq (payoffBranchExperiment P g) =
      normalizedMarkedUtility F h q hq (payoffBranchExperiment P (fun _ ↦ o0)) +
        ∑ y, Channel.outcomeMarginal P q y *
          (materialPayoffUtility F h (g y) - materialPayoffUtility F h o0) := by
  exact normalizedMarkedUtility_payoffBranch_sum
    F h q hq P o0 g (materialPayoffUtility F h)
    (fun y ↦ normalizedMarkedUtility_payoffBranch_increment_material
      F h q hq P y (g y) o0)

/-- Difference form of the payoff separation identity. -/
theorem normalizedMarkedUtility_payoffBranch_difference_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (g : Y → O) (o0 : O) :
    normalizedMarkedUtility F h q hq (payoffBranchExperiment P g) -
        normalizedMarkedUtility F h q hq (payoffBranchExperiment P (fun _ ↦ o0)) =
      ∑ y, Channel.outcomeMarginal P q y *
        (materialPayoffUtility F h (g y) - materialPayoffUtility F h o0) := by
  rw [normalizedMarkedUtility_payoffBranch_separation_material
    F h q hq P g o0]
  ring

/-- With the normalized low payoff as baseline, only expected material utility
remains in the payoff-dependent part. -/
theorem normalizedMarkedUtility_payoffBranch_difference_from_low_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (g : Y → O) :
    normalizedMarkedUtility F h q hq (payoffBranchExperiment P g) -
        normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P (fun _ ↦ materialLowOutcome F h)) =
      ∑ y, Channel.outcomeMarginal P q y * materialPayoffUtility F h (g y) := by
  simpa only [materialPayoffUtility_low, sub_zero] using
    normalizedMarkedUtility_payoffBranch_difference_material F h q hq P g
      (materialLowOutcome F h)

/-- Comparing any two payoff profiles on the same record experiment depends
only on their expected material utilities. -/
theorem normalizedMarkedUtility_payoffBranch_profiles_difference_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (g g' : Y → O) :
    normalizedMarkedUtility F h q hq (payoffBranchExperiment P g) -
        normalizedMarkedUtility F h q hq (payoffBranchExperiment P g') =
      ∑ y, Channel.outcomeMarginal P q y *
        (materialPayoffUtility F h (g y) - materialPayoffUtility F h (g' y)) := by
  have hg := normalizedMarkedUtility_payoffBranch_difference_from_low_material
    F h q hq P g
  have hg' := normalizedMarkedUtility_payoffBranch_difference_from_low_material
    F h q hq P g'
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  linarith

end TraceableAgency.Theorem1.MaterialCalibration
