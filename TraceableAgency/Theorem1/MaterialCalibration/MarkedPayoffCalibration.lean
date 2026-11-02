/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MaterialCalibration.MarkedSupportCalibration
import TraceableAgency.Theorem1.BranchPayoffLaw

/-!
# Reading the insertion scale from a material payoff upgrade

Replacing the low material anchor by the high anchor on one reached branch
has value exactly equal to the positive affine insertion scale.  This result
does not identify that scale with the branch mass and uses no trace formula.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- A constant payoff channel remains the same channel when extended from a
posterior support; inserting it therefore gives the corresponding payoff
profile.  This law identity is independent of any information calibration. -/
theorem materialCalibration_sameMarkedTerminalLaw_supportInsertion_purePayoff
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (background o : O) :
    SameMarkedTerminalLaw q
      (supportBranchInsertionExperiment q P target background
        (markedPayoffLotteryExperiment
          (A := supportSubtype (branchPosterior P q target))
          (TraceableAgency.Dist.pure o)))
      (payoffBranchExperiment P
        (updateBranchPayoff (fun _ ↦ background) target o)) := by
  let r := branchPosterior P q target
  have hext : SameMarkedTerminalLaw r
      (supportExtendMarkedExperiment r
        (markedPayoffLotteryExperiment
          (A := supportSubtype r) (TraceableAgency.Dist.pure o)))
      (markedPayoffLotteryExperiment (A := A) (TraceableAgency.Dist.pure o)) := by
    intro phi
    rfl
  have hins := sameMarkedTerminalLaw_branchInsertion
    q P target background _ _ hext
  have hpay := sameMarkedTerminalLaw_branchInsertion_purePayoff
    q P target background o
  intro phi
  exact (hins phi).trans (hpay phi)

/-- Numerical transport of a pure payoff insertion to a deterministic payoff
profile, using only marked-law equality. -/
theorem materialCalibration_normalizedMarkedUtility_supportInsertion_purePayoff
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (background o : O) :
    normalizedMarkedUtility F h q hq
        (supportBranchInsertionExperiment q P target background
          (markedPayoffLotteryExperiment
            (A := supportSubtype (branchPosterior P q target))
            (TraceableAgency.Dist.pure o))) =
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ background) target o)) := by
  exact normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _
    (materialCalibration_sameMarkedTerminalLaw_supportInsertion_purePayoff
      q P target background o)

/-- The material high-minus-low payoff increment measures the insertion
scale, with any fixed deterministic background payoff. -/
theorem normalizedMarkedUtility_materialBranchUpgrade_eq_insertionScale
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (background : O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ background) target (materialHighOutcome F h))) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ background) target (materialLowOutcome F h))) =
      supportBranchInsertionScale F h q hq P target htarget background := by
  let r := branchPosterior P q target
  have hhigh := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget background
      (markedMaterialHighExperiment (A := supportSubtype r) F h)
  have hlow := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget background
      (markedMaterialLowExperiment (A := supportSubtype r) F h)
  rw [normalizedMarkedUtility_high, mul_one] at hhigh
  rw [normalizedMarkedUtility_low, mul_zero, zero_add] at hlow
  rw [materialCalibration_normalizedMarkedUtility_supportInsertion_purePayoff] at hhigh hlow
  linarith

/-- With the low material outcome as baseline, the unmodified profile is
constant and the high payoff upgrade directly equals the insertion scale. -/
theorem normalizedMarkedUtility_materialBranchUpgradeFromLow_eq_insertionScale
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ materialLowOutcome F h) target
            (materialHighOutcome F h))) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (fun _ ↦ materialLowOutcome F h)) =
      supportBranchInsertionScale F h q hq P target htarget (materialLowOutcome F h) := by
  have hbase : updateBranchPayoff
      (fun _ : Y ↦ materialLowOutcome F h) target (materialLowOutcome F h) =
      (fun _ : Y ↦ materialLowOutcome F h) := by
    funext y
    simp [updateBranchPayoff]
  simpa only [hbase] using
    normalizedMarkedUtility_materialBranchUpgrade_eq_insertionScale
      F h q hq P target htarget (materialLowOutcome F h)

end TraceableAgency.Theorem1
