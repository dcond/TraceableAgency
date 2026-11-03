import TraceableAgency.Theorem1.MaterialCalibration.EntropyGrouping
import TraceableAgency.Theorem1.MaterialCalibration.EntropyContinuity
import TraceableAgency.Theorem1.MaterialCalibration.EntropyPositive

/-! Shannon identification after material calibration.

Every input to the preference-free finite Faddeev theorem is derived from
the new material-normalized utility. Trace relevance excludes zero scale.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency
universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

theorem materialEntropy_faddeev_hypotheses
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    FiniteFaddeevStandardHypotheses
      (fun {_} _ _ _ q ↦ materialEntropy F h q) where
  nonnegative := fun q ↦ materialEntropy_nonneg F h q
  pointMass_zero := fun a ↦ materialEntropy_pure F h a
  fullSupport_relabel := fun e q hq ↦ materialEntropy_fullSupport_relabel F h e q hq
  support_restriction := fun q ↦ materialEntropy_support_restriction F h q
  binary_continuous := materialEntropy_binary_continuous F h
  strong_additivity := materialEntropy_strong_additivity F h

/-- The material-normalized entropy candidate is one positive multiple of
Shannon entropy, uniformly over all finite action sets and all priors. -/
theorem exists_pos_materialEntropy_eq_entropy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A), materialEntropy F h q = lambda * entropy q := by
  obtain ⟨lambda, hlambda, hformula⟩ := GenericFaddeev.finiteFaddeev_characterization
    (fun {_} _ _ _ q ↦ materialEntropy F h q) (materialEntropy_faddeev_hypotheses F h)
  refine ⟨lambda, ?_, hformula⟩
  apply lt_of_le_of_ne hlambda
  intro hz
  have hp := materialEntropy_pos F h (Dist.uniform (A := ULift.{u, 0} Bool))
    Dist.uniform_fullSupport
  rw [hformula, ← hz, zero_mul] at hp
  exact (lt_irrefl 0) hp

end TraceableAgency.Theorem1.MaterialCalibration
