/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.GlobalTraceScale
import TraceableAgency.Theorem1.SupportDummy
import TraceableAgency.Theorem1.ValueSupport
import TraceableAgency.Theorem1.Benchmark

/-!
# Assembly of the trace-tempered representation

This module isolates the final order-theoretic assembly.  Its sole numerical
input is the full-support formula for the normalized marked utility.  Support
restriction then removes boundary priors, while A3 turns cross-channel pair
comparisons into the within-channel and finite-block conclusions of Theorem 1.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-- The single numerical input needed by the final representation assembly:
on every full-support finite action simplex, the normalized marked-terminal
utility is exactly expected material utility plus the common trace multiple of
mutual information. -/
def FullSupportNormalizedValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor) : Prop :=
  ∀ {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (K : Channel A (O × R)),
    normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) =
      traceTemperedValue (materialPayoffUtility F h)
        (globalTraceLambda F h) q K

/-- The full-support normalized-value formula represents every cross-channel
comparison, including boundary priors. -/
theorem pairWeak_iff_traceTemperedValue_of_fullSupportNormalizedValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (hvalue : FullSupportNormalizedValueFormula F h)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      traceTemperedValue (materialPayoffUtility F h)
          (globalTraceLambda F h) q K ≥
        traceTemperedValue (materialPayoffUtility F h)
          (globalTraceLambda F h) p L := by
  rw [pairWeak_iff_supportRestriction F h q K p L]
  have hmarked :
      pairWeak F q.restrictToSupport (Channel.restrictToSupport K q)
          p.restrictToSupport (Channel.restrictToSupport L p) ↔
        normalizedMarkedUtility F h q.restrictToSupport
            q.restrictToSupport_fullSupport
            (markedExperimentOfChannel (Channel.restrictToSupport K q)) ≥
          normalizedMarkedUtility F h p.restrictToSupport
            p.restrictToSupport_fullSupport
            (markedExperimentOfChannel (Channel.restrictToSupport L p)) := by
    simpa [markedExperimentOfChannel] using
      (pairWeak_markedExperiments_iff_normalizedMarkedUtility F h
        q.restrictToSupport p.restrictToSupport
        q.restrictToSupport_fullSupport p.restrictToSupport_fullSupport
        (markedExperimentOfChannel (Channel.restrictToSupport K q))
        (markedExperimentOfChannel (Channel.restrictToSupport L p)))
  rw [hmarked]
  rw [hvalue q.restrictToSupport q.restrictToSupport_fullSupport
      (Channel.restrictToSupport K q),
    hvalue p.restrictToSupport p.restrictToSupport_fullSupport
      (Channel.restrictToSupport L p),
    traceTemperedValue_restrictToSupport,
    traceTemperedValue_restrictToSupport]

/-- A5 duplication converts the cross-channel representation into the
within-channel clause, with the same material index and trace multiplier. -/
theorem withinChannelRepresentation_of_fullSupportNormalizedValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (hvalue : FullSupportNormalizedValueFormula F h) :
    WithinChannelRepresentation F (materialPayoffUtility F h)
      (globalTraceLambda F h) := by
  intro A R _ _ _ _ _ _ K q p
  rw [h.a3.duplication K q p]
  exact pairWeak_iff_traceTemperedValue_of_fullSupportNormalizedValueFormula
    F h hvalue q K p K

/-- A5 irrelevant-block coherence converts the cross-channel representation
directly into the theorem's finite-block "moreover" clause. -/
theorem sameWitnessBlockRepresentation_of_fullSupportNormalizedValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (hvalue : FullSupportNormalizedValueFormula F h) :
    SameWitnessBlockRepresentation F (materialPayoffUtility F h)
      (globalTraceLambda F h) := by
  intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
  rw [h.a3.irrelevant_blocks Act Rec K i j hij qi qj]
  exact pairWeak_iff_traceTemperedValue_of_fullSupportNormalizedValueFormula
    F h hvalue qi (K i) qj (K j)

/-- The two representation clauses obtained from one full-support numerical
formula, retaining exactly the same witnesses. -/
theorem representationClauses_of_fullSupportNormalizedValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (hvalue : FullSupportNormalizedValueFormula F h) :
    WithinChannelRepresentation F (materialPayoffUtility F h)
        (globalTraceLambda F h) ∧
      SameWitnessBlockRepresentation F (materialPayoffUtility F h)
        (globalTraceLambda F h) :=
  ⟨withinChannelRepresentation_of_fullSupportNormalizedValueFormula F h hvalue,
    sameWitnessBlockRepresentation_of_fullSupportNormalizedValueFormula F h hvalue⟩

end TraceableAgency.Theorem1
