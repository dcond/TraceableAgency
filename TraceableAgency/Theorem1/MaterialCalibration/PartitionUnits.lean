import TraceableAgency.Theorem1.MaterialCalibration.PartitionSupport
import TraceableAgency.Theorem1.MaterialCalibration.Units

/-!
# Material upgrades on the reached partition support

Support identification preserves every fully revealed payoff upgrade and
therefore its sum, the material unit used by the calibration argument.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {A O : Type u}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype O] [DecidableEq O]

theorem revealUpgrade_inlSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport) (a : A) :
    revealUpgrade F h
        (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport
        (Dist.restrictToSupport_fullSupport _)
        ((inlSupportEquiv r hr).symm a) =
      revealUpgrade F h r hr a := by
  classical
  let g : A → O := Function.update (fun _ ↦ materialLowOutcome F h) a
    (materialHighOutcome F h)
  have hg : (fun s => g (inlSupportEquiv r hr s)) =
      Function.update (fun _ => materialLowOutcome F h)
        ((inlSupportEquiv r hr).symm a) (materialHighOutcome F h) := by
    funext s
    simp [g, Function.update, (inlSupportEquiv r hr).apply_eq_iff_eq_symm_apply]
  have hv := normalizedMarkedUtility_fullReveal_inlSupport F h r hr g
  rw [hg] at hv
  have hv0 := normalizedMarkedUtility_fullReveal_inlSupport F h r hr
    (fun _ => materialLowOutcome F h)
  unfold revealUpgrade
  exact congrArg₂ (fun x y : ℝ => x - y) hv hv0

/-- Summing the upgrades is invariant under the canonical support relabeling. -/
theorem sum_revealUpgrade_inlSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport) :
    (∑ a, revealUpgrade F h
      (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport
      (Dist.restrictToSupport_fullSupport _) a) =
      ∑ a, revealUpgrade F h r hr a := by
  rw [← (inlSupportEquiv r hr).symm.sum_comp]
  apply Finset.sum_congr rfl
  intro a _ha
  exact revealUpgrade_inlSupport F h r hr a

/-- The unit itself is unchanged by identifying the reached support with `A`. -/
theorem revealMaterialUnit_inlSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport) :
    revealMaterialUnit F h
        (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport
        (Dist.restrictToSupport_fullSupport _) =
      revealMaterialUnit F h r hr :=
  sum_revealUpgrade_inlSupport F h r hr

/-- The reached non-singleton posterior has exactly the material unit of `r`. -/
theorem revealMaterialUnit_partitionRecord_true
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    revealMaterialUnit F h
        (branchPosterior (partitionRecordChannel (A := A))
          (partitionPrior r t (le_of_lt ht0) ht1) (ULift.up true)).restrictToSupport
        (Dist.restrictToSupport_fullSupport _) =
      revealMaterialUnit F h r hr := by
  have hp := partitionRecord_posterior_true r t ht0 ht1
  have hv := congrArg (fun p : Dist (A ⊕ PUnit.{u+1}) =>
    revealMaterialUnit F h p.restrictToSupport
      (Dist.restrictToSupport_fullSupport p)) hp
  exact hv.trans (revealMaterialUnit_inlSupport F h r hr)

end TraceableAgency.Theorem1.MaterialCalibration
