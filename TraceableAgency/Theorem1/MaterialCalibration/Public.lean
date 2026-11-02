import TraceableAgency.Theorem1.MaterialCalibration.Calibration
import TraceableAgency.Theorem1.RelevanceBridge

/-!
# Material branch calibration from the paper's eight axioms

This entry point uses the exact paper-facing axiom bundle. The existing
relevance bridge supplies common material anchors and the finite-branch form
of A8; the new material argument then identifies every insertion scale.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

/-- A1--A8 imply exact probability weights in the common material normalization,
simultaneously across all finite action and first-stage record alphabets. -/
theorem branchCalibration_of_axioms
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (hV10 : TraceTemperedAxiomsV10 F) :
    ∃ traceAnchor : O, ∃ h : TraceTemperedBridgeAxioms F traceAnchor,
      ∀ {A Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype Y] [DecidableEq Y] [Nonempty Y]
        (q : Dist A) (hq : q.FullSupport) (P : Channel A Y) (target : Y)
        (htarget : BranchPositive P q target) (background : O),
        supportBranchInsertionScale F h q hq P target htarget background =
          Channel.outcomeMarginal P q target := by
  obtain ⟨traceAnchor, h⟩ := traceTemperedBridgeAxioms_of_v10 F hV10
  refine ⟨traceAnchor, h, ?_⟩
  intro A Y _ _ _ _ _ _ q hq P target htarget background
  exact supportBranchInsertionScale_eq_branchMass_material
    F h q hq P target htarget background

end TraceableAgency.Theorem1.MaterialCalibration
