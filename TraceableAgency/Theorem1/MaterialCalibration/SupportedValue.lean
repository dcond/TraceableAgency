import TraceableAgency.Theorem1.MaterialCalibration.TraceEntropy
import TraceableAgency.Theorem1.SupportDummy

/-!
# Common material-normalized values at arbitrary priors

Deleting null action rows gives a global cardinal scale for pair comparisons.
No information representation is used in this extension.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A B R S : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype S] [DecidableEq S] [Nonempty S]

noncomputable def supportedMarkedValue
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (K : Channel A (O × R)) : ℝ :=
  normalizedMarkedUtility F h q.restrictToSupport
    (Dist.restrictToSupport_fullSupport q)
    (markedExperimentOfChannel (Channel.restrictToSupport K q))

theorem pairWeak_iff_supportedMarkedValue
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (K : Channel A (O × R))
    (p : Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔ supportedMarkedValue F h q K ≥ supportedMarkedValue F h p L := by
  rw [pairWeak_iff_supportRestriction F h q K p L]
  exact pairWeak_markedExperiments_iff_normalizedMarkedUtility F h
    q.restrictToSupport p.restrictToSupport
    q.restrictToSupport_fullSupport p.restrictToSupport_fullSupport
    (markedExperimentOfChannel (Channel.restrictToSupport K q))
    (markedExperimentOfChannel (Channel.restrictToSupport L p))

theorem supportedMarkedValue_eq_of_pairWeak_both
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (K : Channel A (O × R))
    (p : Dist B) (L : Channel B (O × S))
    (hforward : pairWeak F q K p L) (hbackward : pairWeak F p L q K) :
    supportedMarkedValue F h q K = supportedMarkedValue F h p L :=
  le_antisymm
    ((pairWeak_iff_supportedMarkedValue F h p L q K).mp hbackward)
    ((pairWeak_iff_supportedMarkedValue F h q K p L).mp hforward)

theorem supportedMarkedValue_eq_normalized_of_fullSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (K : Channel A (O × R)) :
    supportedMarkedValue F h q K =
      normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) := by
  have hf := (pairWeak_markedExperiments_iff_normalizedMarkedUtility F h
    q q.restrictToSupport hq q.restrictToSupport_fullSupport
    (markedExperimentOfChannel K)
    (markedExperimentOfChannel (Channel.restrictToSupport K q))).mp
      (pairWeak_ambient_to_support F h K q)
  have hb := (pairWeak_markedExperiments_iff_normalizedMarkedUtility F h
    q.restrictToSupport q q.restrictToSupport_fullSupport hq
    (markedExperimentOfChannel (Channel.restrictToSupport K q))
    (markedExperimentOfChannel K)).mp
      (pairWeak_support_to_ambient F h K q)
  exact le_antisymm hf hb

theorem supportedMarkedValue_fullReveal_eq_materialEntropy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (q : Dist A) :
    supportedMarkedValue F h q (fullRevealAtPayoff (materialLowOutcome F h)) =
      materialEntropy F h q := by
  exact normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h
    q.restrictToSupport q.restrictToSupport_fullSupport _ _
    (sameMarkedTerminalLaw_restrict_fullReveal q (materialLowOutcome F h))

end TraceableAgency.Theorem1.MaterialCalibration
