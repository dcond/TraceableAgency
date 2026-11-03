import TraceableAgency.Theorem1.MaterialCalibration.EntropyProperties
import TraceableAgency.Theorem1.MaterialCalibration.SupportedValue
import TraceableAgency.Theorem1.MaterialCalibration.TraceEntropySupport

/-! A7 identifies coarse revelation with full revelation of the cell lottery.
Combined with the material-calibrated continuation identity, this gives
Faddeev grouping, including boundary priors. -/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency
universe u

variable {O K : Type u} [Fintype O] [DecidableEq O]
variable [Fintype K] [DecidableEq K] [Nonempty K]
variable (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
variable [∀ k, Nonempty (Act k)] [Nonempty (Sigma Act)]

theorem supportedMarkedValue_coarseReveal_eq_materialEntropy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    supportedMarkedValue F h (sigmaDist p q)
      (constantPayoffLift (materialLowOutcome F h) (coarseRevealChannel Act)) =
        materialEntropy F h p := by
  have hf := h.a5 (constantPayoffLift (materialLowOutcome F h)
    (coarseRevealChannel Act)) (sigmaDist p q) (coarseProjectKernel Act)
    (constantPayoffLift (materialLowOutcome F h) (Channel.idChannel : Channel K K))
    (constantPayoffLift_actionCompletion (materialLowOutcome F h) _ _ _ _
      (coarseReveal_isBayesPushforwardCompletion_project Act p q))
  rw [actionPushforward_sigmaDist_coarseProject, constantPayoffLift_idChannel] at hf
  have hb := h.a5 (constantPayoffLift (materialLowOutcome F h)
    (Channel.idChannel : Channel K K)) p (coarseRefineKernel Act q)
    (constantPayoffLift (materialLowOutcome F h) (coarseRevealChannel Act))
    (constantPayoffLift_actionCompletion (materialLowOutcome F h) _ _ _ _
      (coarseReveal_isBayesPushforwardCompletion_refine Act p q))
  rw [actionPushforward_coarseRefine, constantPayoffLift_idChannel] at hb
  rw [← supportedMarkedValue_fullReveal_eq_materialEntropy F h p]
  exact supportedMarkedValue_eq_of_pairWeak_both F h _ _ _ _ hf hb

theorem materialEntropy_sigmaDist
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    materialEntropy F h (sigmaDist p q) =
      materialEntropy F h p + ∑ k, p k * materialEntropy F h (q k) := by
  have hv := supportedMarkedValue_constantPayoffLift_eq_entropy_sub_expected
    F h (sigmaDist p q) (coarseRevealChannel Act)
  rw [supportedMarkedValue_coarseReveal_eq_materialEntropy] at hv
  have hsum := posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
    (fun {_} _ _ _ q ↦ materialEntropy F h q) Act p q
    (fun k ↦ materialEntropy_blockEmbed Act F h k (q k))
  change (∑ k, Channel.outcomeMarginal (coarseRevealChannel Act) (sigmaDist p q) k *
    materialEntropy F h (branchPosterior (coarseRevealChannel Act) (sigmaDist p q) k)) =
      ∑ k, p k * materialEntropy F h (q k) at hsum
  rw [hsum] at hv
  linarith

theorem materialEntropy_strong_additivity
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    SatisfiesFiniteFaddeevRecursion
      (fun {_} _ _ _ q ↦ materialEntropy F h q) := by
  intro K _ _ _ Act _ _ _ _ p q
  exact materialEntropy_sigmaDist Act F h p q

end TraceableAgency.Theorem1.MaterialCalibration
