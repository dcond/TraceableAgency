/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MaterialCalibration.MarkedSupportCalibration
import TraceableAgency.Theorem1.MaterialCalibration.Units
import TraceableAgency.Theorem1.MaterialCalibration.FullRevelationValue

/-!
# Insertion slopes and the constructed material units

The conditional material-direction calibration is instantiated with the
full-revelation units already constructed from the behavioural axioms.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- The identity-stage implementation of one anchor upgrade has the same
value difference as the direct full-revelation implementation. -/
theorem markedRevealPayoff_material_difference_eq_revealUpgrade
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) (a : A) :
    normalizedMarkedUtility F h q hq
        (markedRevealPayoffExperiment (materialLowOutcome F h) (materialHighOutcome F h) a) -
      normalizedMarkedUtility F h q hq
        (markedRevealPayoffExperiment (materialLowOutcome F h) (materialLowOutcome F h) a) =
      MaterialCalibration.revealUpgrade F h q hq a := by
  simp only [markedRevealPayoffExperiment, MaterialCalibration.revealUpgrade,
    MaterialCalibration.normalizedMarkedUtility_fullRevealWithPayoff_eq_payoffBranch,
    MaterialCalibration.updateBranchPayoff_eq_update, Function.update_eq_self]

/-- The full-support insertion slope obeys the material-unit ratio with the
actual units constructed from the axioms. -/
theorem branchInsertionAffineSlope_mul_revealMaterialUnit
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport) (background : O) :
    branchInsertionAffineSlope F h q hq P target htarget hr background *
        MaterialCalibration.revealMaterialUnit F h (branchPosterior P q target) hr =
      Channel.outcomeMarginal P q target * MaterialCalibration.revealMaterialUnit F h q hq := by
  classical
  let a : A := Classical.arbitrary A
  apply branchInsertionAffineSlope_mul_materialUnit F h q hq P target htarget hr
    background (materialLowOutcome F h) (materialHighOutcome F h) a
  · rw [markedRevealPayoff_material_difference_eq_revealUpgrade]
    exact MaterialCalibration.revealUpgrade_eq_probability_mul_unit F h q hq a
  · rw [markedRevealPayoff_material_difference_eq_revealUpgrade]
    exact MaterialCalibration.revealUpgrade_eq_probability_mul_unit
      F h (branchPosterior P q target) hr a

/-- The ratio formula holds on every reached support face, including
singletons, for the actual material units constructed from the axioms. -/
theorem supportBranchInsertionScale_mul_revealMaterialUnit
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (background : O) :
    supportBranchInsertionScale F h q hq P target htarget background *
        MaterialCalibration.revealMaterialUnit F h
          (branchPosterior P q target).restrictToSupport
          (TraceableAgency.Dist.restrictToSupport_fullSupport
            (branchPosterior P q target)) =
      Channel.outcomeMarginal P q target * MaterialCalibration.revealMaterialUnit F h q hq := by
  classical
  let r := branchPosterior P q target
  let a : supportSubtype r := Classical.arbitrary (supportSubtype r)
  apply supportBranchInsertionScale_mul_materialUnit F h q hq P target htarget
    background (materialLowOutcome F h) (materialHighOutcome F h) a
  · rw [markedRevealPayoff_material_difference_eq_revealUpgrade]
    exact MaterialCalibration.revealUpgrade_eq_probability_mul_unit F h q hq a.1
  · rw [markedRevealPayoff_material_difference_eq_revealUpgrade]
    exact MaterialCalibration.revealUpgrade_eq_probability_mul_unit
      F h r.restrictToSupport (TraceableAgency.Dist.restrictToSupport_fullSupport r) a

end TraceableAgency.Theorem1
