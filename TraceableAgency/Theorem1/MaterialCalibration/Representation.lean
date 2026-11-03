import TraceableAgency.Theorem1.MaterialCalibration.ValueAssembly
import TraceableAgency.Theorem1.SupportDummy
import TraceableAgency.Theorem1.ValueSupport

/-!
# Representation assembly with the material-first coefficient

Support restriction handles arbitrary boundary priors. A5 then gives both
within-channel representation and the same-witness finite-block clause.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

theorem pairWeak_iff_traceTemperedValue_material
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ)
    (hvalue : MaterialNormalizedValueFormula F h lambda)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R))
    (p : Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      traceTemperedValue (materialPayoffUtility F h) lambda q K ≥
        traceTemperedValue (materialPayoffUtility F h) lambda p L := by
  rw [pairWeak_iff_supportRestriction F h q K p L]
  have hmarked := pairWeak_markedExperiments_iff_normalizedMarkedUtility F h
    q.restrictToSupport p.restrictToSupport
    q.restrictToSupport_fullSupport p.restrictToSupport_fullSupport
    (markedExperimentOfChannel (Channel.restrictToSupport K q))
    (markedExperimentOfChannel (Channel.restrictToSupport L p))
  change pairWeak F q.restrictToSupport (Channel.restrictToSupport K q)
    p.restrictToSupport (Channel.restrictToSupport L p) ↔ _ at hmarked
  rw [hmarked]
  rw [hvalue q.restrictToSupport q.restrictToSupport_fullSupport
      (Channel.restrictToSupport K q),
    hvalue p.restrictToSupport p.restrictToSupport_fullSupport
      (Channel.restrictToSupport L p),
    traceTemperedValue_restrictToSupport, traceTemperedValue_restrictToSupport]

theorem representationClauses_of_materialNormalizedValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ)
    (hvalue : MaterialNormalizedValueFormula F h lambda) :
    WithinChannelRepresentation F (materialPayoffUtility F h) lambda ∧
      SameWitnessBlockRepresentation F (materialPayoffUtility F h) lambda := by
  constructor
  · intro A R _ _ _ _ _ _ K q p
    rw [h.a3.duplication K q p]
    exact pairWeak_iff_traceTemperedValue_material F h lambda hvalue q K p K
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    rw [h.a3.irrelevant_blocks Act Rec K i j hij qi qj]
    exact pairWeak_iff_traceTemperedValue_material
      F h lambda hvalue qi (K i) qj (K j)

end TraceableAgency.Theorem1.MaterialCalibration
