import TraceableAgency.Theorem1.MaterialCalibration.PartitionCalibration
import TraceableAgency.Theorem1.MaterialCalibration.UnitAnchors
import TraceableAgency.Theorem1.MaterialCalibration.MarkedPayoffCalibration
import TraceableAgency.Theorem1.MaterialCalibration.MarkedUnitRatio

/-!
# Material-based calibration of branch insertion

Place an arbitrary full-support prior beside a singleton, each with mass one
half. A7 merges this partition into its binary cell experiment without changing
any cell-dependent material payoff comparison. The singleton cell equates the
outer and binary material units. The other cell then forces the arbitrary
prior's unit to be one. Consequently A8's positive affine insertion coefficient
is exactly the reached branch probability, before information is identified.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- The material unit is one at every full-support prior. This is the two-cell
calibration argument and does not use a representation of information value. -/
theorem revealMaterialUnit_eq_one
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport) :
    revealMaterialUnit F h r hr = 1 := by
  classical
  let t : ℝ := 1 / 2
  have ht0 : 0 < t := by norm_num [t]
  have ht1 : t < 1 := by norm_num [t]
  let q := partitionPrior r t (le_of_lt ht0) (le_of_lt ht1)
  have hq : q.FullSupport := partitionPrior_fullSupport r hr t ht0 ht1
  let p := partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1)
  have hp : p.FullSupport := partitionCellPrior_fullSupport t ht0 ht1
  let P := partitionRecordChannel (A := A)
  have hfalse : BranchPositive P q (ULift.up false) :=
    partitionRecord_positive_false r t (le_of_lt ht0) ht1
  have htrue : BranchPositive P q (ULift.up true) :=
    partitionRecord_positive_true r t ht0 (le_of_lt ht1)
  have hscale (cell : RelevanceBit.{u}) (hc : BranchPositive P q cell) :
      supportBranchInsertionScale F h q hq P cell hc (materialLowOutcome F h) =
        p cell * revealMaterialUnit F h p hp := by
    have hv := partitionPayoff_upgrade_value F h r hr t ht0 ht1 cell
    rw [normalizedMarkedUtility_materialBranchUpgradeFromLow_eq_insertionScale
      F h q hq P cell hc] at hv
    exact hv
  letI := partitionRecord_false_support_subsingleton r t (le_of_lt ht0) ht1
  have hsingleton := supportBranchInsertionScale_mul_revealMaterialUnit
    F h q hq P (ULift.up false) hfalse (materialLowOutcome F h)
  rw [revealMaterialUnit_eq_one_of_subsingleton, mul_one,
    hscale (ULift.up false) hfalse] at hsingleton
  have hmassFalse : Channel.outcomeMarginal P q (ULift.up false) = p (ULift.up false) :=
    congrArg (fun d => d (ULift.up false))
      (partitionRecord_marginal r t (le_of_lt ht0) (le_of_lt ht1))
  rw [hmassFalse] at hsingleton
  have hcommon : revealMaterialUnit F h p hp = revealMaterialUnit F h q hq :=
    mul_left_cancel₀ (ne_of_gt (hp (ULift.up false))) hsingleton
  have hcell := supportBranchInsertionScale_mul_revealMaterialUnit
    F h q hq P (ULift.up true) htrue (materialLowOutcome F h)
  rw [hscale (ULift.up true) htrue] at hcell
  have hlocal := revealMaterialUnit_partitionRecord_true
    F h r hr t ht0 (le_of_lt ht1)
  rw [hlocal] at hcell
  have hmassTrue : Channel.outcomeMarginal P q (ULift.up true) = p (ULift.up true) :=
    congrArg (fun d => d (ULift.up true))
      (partitionRecord_marginal r t (le_of_lt ht0) (le_of_lt ht1))
  rw [hmassTrue, ← hcommon, mul_assoc] at hcell
  have hunit := mul_left_cancel₀ (ne_of_gt (hp (ULift.up true))) hcell
  apply mul_left_cancel₀ (ne_of_gt (revealMaterialUnit_pos F h p hp))
  simpa only [mul_one] using hunit

/-- Under full revelation, a single low-to-high material upgrade has value
exactly equal to the probability of the upgraded action. -/
theorem revealUpgrade_eq_probability
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (a : A) :
    revealUpgrade F h q hq a = q a := by
  rw [revealUpgrade_eq_probability_mul_unit, revealMaterialUnit_eq_one, mul_one]

/-- Material calibration identifies every reached support-face insertion
scale with its branch probability, including singleton posterior supports. -/
theorem supportBranchInsertionScale_eq_branchMass_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (background : O) :
    supportBranchInsertionScale F h q hq P target htarget background =
      Channel.outcomeMarginal P q target := by
  have hv := supportBranchInsertionScale_mul_revealMaterialUnit
    F h q hq P target htarget background
  simpa only [revealMaterialUnit_eq_one, mul_one] using hv

/-- The same probability coefficient for the original full-support insertion. -/
theorem branchInsertionAffineSlope_eq_branchMass_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport) (background : O) :
    branchInsertionAffineSlope F h q hq P target htarget hr background =
      Channel.outcomeMarginal P q target := by
  have hv := branchInsertionAffineSlope_mul_revealMaterialUnit
    F h q hq P target htarget hr background
  simpa only [revealMaterialUnit_eq_one, mul_one] using hv

/-- Exact cardinal branch separability in material units: changing a reached
continuation changes ex ante value by its conditional value difference times
the probability of reaching that branch. -/
theorem normalizedMarkedUtility_supportInsertion_difference_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (background : O)
    (E G : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target))) :
    normalizedMarkedUtility F h q hq
        (supportBranchInsertionExperiment q P target background E) -
      normalizedMarkedUtility F h q hq
        (supportBranchInsertionExperiment q P target background G) =
      Channel.outcomeMarginal P q target *
        (normalizedMarkedUtility F h
            (branchPosterior P q target).restrictToSupport
            (Dist.restrictToSupport_fullSupport _) E -
          normalizedMarkedUtility F h
            (branchPosterior P q target).restrictToSupport
            (Dist.restrictToSupport_fullSupport _) G) := by
  rw [normalizedMarkedUtility_supportBranchInsertion F h q hq P target htarget,
    normalizedMarkedUtility_supportBranchInsertion F h q hq P target htarget,
    supportBranchInsertionScale_eq_branchMass_material]
  ring

end TraceableAgency.Theorem1.MaterialCalibration
