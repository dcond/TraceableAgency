/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MarkedDummyMaps
import TraceableAgency.Theorem1.NormalizedMarked

/-!
# A common normalized scale across full-support action alphabets

Independent dummy-action embeddings preserve the normalized marked utility
exactly.  Both sides of an arbitrary cross-alphabet comparison can therefore
be moved to their common product alphabet and evaluated on one numerical
scale.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A B : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]

/-! ## Material anchors commute with dummy maps -/

/-- Adjoining an independent right action coordinate does not change the
marked law of an action-independent payoff lottery. -/
theorem independentDummyMarkedMixtureMap_payoffLottery
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (ell : TraceableAgency.Dist O) :
    independentDummyMarkedMixtureMap q r
        (markedPayoffLotteryEmbedding q ell) =
      markedPayoffLotteryEmbedding (prodDist q r) ell := by
  apply Quotient.sound
  change SameMarkedTerminalLaw (prodDist q r)
    (independentDummyMarkedExperiment (B := B)
      (markedPayoffLotteryExperiment (A := A) ell))
    (markedPayoffLotteryExperiment (A := A × B) ell)
  intro phi
  change markedTerminalIntegral (independentDummyPrior q r)
      (independentDummyMarkedExperiment (B := B)
        (markedPayoffLotteryExperiment (A := A) ell)) phi =
    markedTerminalIntegral (prodDist q r)
      (markedPayoffLotteryExperiment (A := A × B) ell) phi
  rw [markedTerminalIntegral_independentDummy,
    markedTerminalIntegral_markedPayoffLottery,
    markedTerminalIntegral_markedPayoffLottery]

/-- Adjoining an independent left action coordinate does not change the
marked law of an action-independent payoff lottery. -/
theorem rightIndependentDummyMarkedMixtureMap_payoffLottery
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (ell : TraceableAgency.Dist O) :
    rightIndependentDummyMarkedMixtureMap q r
        (markedPayoffLotteryEmbedding r ell) =
      markedPayoffLotteryEmbedding (prodDist q r) ell := by
  apply Quotient.sound
  change SameMarkedTerminalLaw (prodDist q r)
    (rightIndependentDummyMarkedExperiment (A := A)
      (markedPayoffLotteryExperiment (A := B) ell))
    (markedPayoffLotteryExperiment (A := A × B) ell)
  intro phi
  rw [markedTerminalIntegral_rightIndependentDummy,
    markedTerminalIntegral_markedPayoffLottery,
    markedTerminalIntegral_markedPayoffLottery]

/-! ## Exact cardinal preservation -/

/-- The normalized quotient utility is preserved exactly by a right dummy
extension.  Affine uniqueness and the common material anchors eliminate the
otherwise arbitrary positive affine change of scale. -/
theorem normalizedMarkedAffineUtility_independentDummy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)).utility
        (independentDummyMarkedMixtureMap q r x) =
      (normalizedMarkedAffineUtilityRepresentation F h q hq).utility x := by
  let high := TraceableAgency.Dist.pure (materialHighOutcome F h)
  let low := TraceableAgency.Dist.pure (materialLowOutcome F h)
  have htargetLow :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (independentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding q low)) = 0 := by
    rw [independentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_low F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  have htargetHigh :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (independentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding q high)) = 1 := by
    rw [independentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_high F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  exact normalizedAffineUtility_eq_along_embedding
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
    (markedTerminalAbstractConvexMixtureSpace
      (O := O) (A := A × B) (prodDist q r))
    (markedTerminalMixtureRel (O := O) (A := A) F h q hq)
    (markedTerminalMixtureRel (O := O) (A := A × B) F h
      (prodDist q r) (markedDummy_prodDist_fullSupport q r hq hr))
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr))
    (independentDummyMarkedMixtureMap q r)
    (independentDummyMarkedMixtureMap_rel_iff F h q r hq hr)
    (independentDummyMarkedMixtureMap_affine q r)
    (markedPayoffLotteryEmbedding q high)
    (markedPayoffLotteryEmbedding q low)
    (markedMaterialAnchors_HMStrict F h q hq)
    (normalizedMarkedAffineUtility_low F h q hq)
    (normalizedMarkedAffineUtility_high F h q hq)
    htargetLow htargetHigh x

/-- The normalized quotient utility is preserved exactly by a left dummy
extension. -/
theorem normalizedMarkedAffineUtility_rightIndependentDummy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x : MarkedTerminalMixtureSpace (O := O) (A := B) r) :
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)).utility
        (rightIndependentDummyMarkedMixtureMap q r x) =
      (normalizedMarkedAffineUtilityRepresentation F h r hr).utility x := by
  let high := TraceableAgency.Dist.pure (materialHighOutcome F h)
  let low := TraceableAgency.Dist.pure (materialLowOutcome F h)
  have htargetLow :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (rightIndependentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding r low)) = 0 := by
    rw [rightIndependentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_low F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  have htargetHigh :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (rightIndependentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding r high)) = 1 := by
    rw [rightIndependentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_high F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  exact normalizedAffineUtility_eq_along_embedding
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := B) r)
    (markedTerminalAbstractConvexMixtureSpace
      (O := O) (A := A × B) (prodDist q r))
    (markedTerminalMixtureRel (O := O) (A := B) F h r hr)
    (markedTerminalMixtureRel (O := O) (A := A × B) F h
      (prodDist q r) (markedDummy_prodDist_fullSupport q r hq hr))
    (normalizedMarkedAffineUtilityRepresentation F h r hr)
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr))
    (rightIndependentDummyMarkedMixtureMap q r)
    (rightIndependentDummyMarkedMixtureMap_rel_iff F h q r hq hr)
    (rightIndependentDummyMarkedMixtureMap_affine q r)
    (markedPayoffLotteryEmbedding r high)
    (markedPayoffLotteryEmbedding r low)
    (markedMaterialAnchors_HMStrict F h r hr)
    (normalizedMarkedAffineUtility_low F h r hr)
    (normalizedMarkedAffineUtility_high F h r hr)
    htargetLow htargetHigh x

/-- Raw normalized marked utility is invariant under adjoining an independent
right dummy action. -/
theorem normalizedMarkedUtility_independentDummy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (E : MarkedTerminalExperiment O A) :
    normalizedMarkedUtility F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (independentDummyMarkedExperiment (B := B) E) =
      normalizedMarkedUtility F h q hq E := by
  simpa [normalizedMarkedUtility] using
    normalizedMarkedAffineUtility_independentDummy F h q r hq hr
      (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q)

/-- Raw normalized marked utility is invariant under adjoining an independent
left dummy action. -/
theorem normalizedMarkedUtility_rightIndependentDummy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (E : MarkedTerminalExperiment O B) :
    normalizedMarkedUtility F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (rightIndependentDummyMarkedExperiment (A := A) E) =
      normalizedMarkedUtility F h r hr E := by
  simpa [normalizedMarkedUtility] using
    normalizedMarkedAffineUtility_rightIndependentDummy F h q r hq hr
      (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := B) r)

/-! ## Cross-alphabet representation -/

/-- Every full-support cross-alphabet comparison of bundled marked
experiments is represented by the same normalized numerical utility. -/
theorem pairWeak_markedExperiments_iff_normalizedMarkedUtility
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hp : p.FullSupport)
    (E : MarkedTerminalExperiment O A)
    (G : MarkedTerminalExperiment O B) :
    @pairWeak O A B E.RecordType G.RecordType
        inferInstance inferInstance
        inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance
        E.recordFintype E.recordDecEq E.recordNonempty
        G.recordFintype G.recordDecEq G.recordNonempty
        F q E.channel p G.channel ↔
      normalizedMarkedUtility F h q hq E ≥
        normalizedMarkedUtility F h p hp G := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  rw [pairWeak_iff_commonProductLifts F h q E.K p G.K]
  change MarkedPairWeak F (prodDist q p)
      (independentDummyMarkedExperiment (B := B) E) (prodDist q p)
      (rightIndependentDummyMarkedExperiment (A := A) G) ↔ _
  rw [normalizedMarkedUtility_represents F h (prodDist q p)
      (markedDummy_prodDist_fullSupport q p hq hp),
    normalizedMarkedUtility_independentDummy F h q p hq hp E,
    normalizedMarkedUtility_rightIndependentDummy F h q p hq hp G]

end TraceableAgency.Theorem1
