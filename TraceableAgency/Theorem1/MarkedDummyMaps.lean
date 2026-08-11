/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MarkedHM
import TraceableAgency.Theorem1.MarkedTransport

/-!
# Dummy-action maps on marked-terminal mixture spaces

The maps in this file adjoin an independent action coordinate on the left or
right.  They are defined directly on the marked-law quotients, preserve the
public mixture operation, and embed the quotient order exactly.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A B : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]

/-- Local name for the elementary full-support product fact used by both
order embeddings. -/
theorem markedDummy_prodDist_fullSupport
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport) :
    (prodDist q r).FullSupport :=
  prodDist_fullSupport q r hq hr

/-! ## Left-coordinate experiments -/

/-- Adjoin an independent right dummy coordinate to every representative of
a marked-terminal law. -/
noncomputable def independentDummyMarkedMixtureMap
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    MarkedTerminalMixtureSpace (O := O) (A := A) q →
      MarkedTerminalMixtureSpace (O := O) (A := A × B) (prodDist q r) :=
  Quotient.map
    (fun E => independentDummyMarkedExperiment (B := B) E)
    (fun {_ _} hsame =>
      sameMarkedTerminalLaw_independentDummy q r hsame)

@[simp]
theorem independentDummyMarkedMixtureMap_mk
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O A) :
    independentDummyMarkedMixtureMap q r
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) =
      (⟦independentDummyMarkedExperiment (B := B) E⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A × B) (prodDist q r)) :=
  rfl

/-- Dummy lifting commutes with the concrete public-coin experiment at the
level of marked terminal laws. -/
theorem sameMarkedTerminalLaw_independentDummy_publicMix
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E G : MarkedTerminalExperiment O A) :
    SameMarkedTerminalLaw (prodDist q r)
      (independentDummyMarkedExperiment (B := B)
        (markedPublicMixExperiment t ht0 ht1 E G))
      (markedPublicMixExperiment t ht0 ht1
        (independentDummyMarkedExperiment (B := B) E)
        (independentDummyMarkedExperiment (B := B) G)) := by
  intro phi
  change
    markedTerminalIntegral (independentDummyPrior q r)
        (independentDummyMarkedExperiment (B := B)
          (markedPublicMixExperiment t ht0 ht1 E G)) phi =
      markedTerminalIntegral (independentDummyPrior q r)
        (markedPublicMixExperiment t ht0 ht1
          (independentDummyMarkedExperiment (B := B) E)
          (independentDummyMarkedExperiment (B := B) G)) phi
  rw [markedTerminalIntegral_independentDummy,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_independentDummy,
    markedTerminalIntegral_independentDummy]

theorem independentDummyMarkedMixtureMap_mix
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    independentDummyMarkedMixtureMap q r
        (markedTerminalMixture q t x y) =
      markedTerminalMixture (prodDist q r) t
        (independentDummyMarkedMixtureMap q r x)
        (independentDummyMarkedMixtureMap q r y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      apply Quotient.sound
      exact sameMarkedTerminalLaw_independentDummy_publicMix
        q r t.1 t.2.1 t.2.2 E G

/-- The same statement in the abstract mixture-space API used by normalized
affine-utility transport. -/
theorem independentDummyMarkedMixtureMap_affine
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    independentDummyMarkedMixtureMap q r
        ((markedTerminalAbstractConvexMixtureSpace q).mix t x y) =
      (markedTerminalAbstractConvexMixtureSpace (prodDist q r)).mix t
        (independentDummyMarkedMixtureMap q r x)
        (independentDummyMarkedMixtureMap q r y) :=
  independentDummyMarkedMixtureMap_mix q r t x y

/-- The left dummy map is an exact order embedding of marked-law quotient
orders. -/
theorem independentDummyMarkedMixtureMap_rel_iff
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y ↔
      markedTerminalMixtureRel F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (independentDummyMarkedMixtureMap q r x)
        (independentDummyMarkedMixtureMap q r y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      letI : Fintype E.RecordType := E.recordFintype
      letI : DecidableEq E.RecordType := E.recordDecEq
      letI : Nonempty E.RecordType := E.recordNonempty
      letI : Fintype G.RecordType := G.recordFintype
      letI : DecidableEq G.RecordType := G.recordDecEq
      letI : Nonempty G.RecordType := G.recordNonempty
      simpa [markedTerminalMixtureRel_mk, MarkedPairWeak,
        independentDummyMarkedExperiment, independentDummyPrior] using
          (pairWeak_iff_independentDummy F h q E.K r q G.K r)

/-! ## Right-coordinate experiments -/

/-- Adjoin an independent left dummy coordinate to a law on the right
action alphabet. -/
noncomputable def rightIndependentDummyMarkedMixtureMap
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    MarkedTerminalMixtureSpace (O := O) (A := B) r →
      MarkedTerminalMixtureSpace (O := O) (A := A × B) (prodDist q r) :=
  Quotient.map
    (fun E => rightIndependentDummyMarkedExperiment (A := A) E)
    (fun {_ _} hsame =>
      sameMarkedTerminalLaw_rightIndependentDummy q r hsame)

@[simp]
theorem rightIndependentDummyMarkedMixtureMap_mk
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O B) :
    rightIndependentDummyMarkedMixtureMap q r
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := B) r) =
      (⟦rightIndependentDummyMarkedExperiment (A := A) E⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A × B) (prodDist q r)) :=
  rfl

theorem sameMarkedTerminalLaw_rightIndependentDummy_publicMix
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E G : MarkedTerminalExperiment O B) :
    SameMarkedTerminalLaw (prodDist q r)
      (rightIndependentDummyMarkedExperiment (A := A)
        (markedPublicMixExperiment t ht0 ht1 E G))
      (markedPublicMixExperiment t ht0 ht1
        (rightIndependentDummyMarkedExperiment (A := A) E)
        (rightIndependentDummyMarkedExperiment (A := A) G)) := by
  intro phi
  rw [markedTerminalIntegral_rightIndependentDummy,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_rightIndependentDummy,
    markedTerminalIntegral_rightIndependentDummy]

theorem rightIndependentDummyMarkedMixtureMap_mix
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := B) r) :
    rightIndependentDummyMarkedMixtureMap q r
        (markedTerminalMixture r t x y) =
      markedTerminalMixture (prodDist q r) t
        (rightIndependentDummyMarkedMixtureMap q r x)
        (rightIndependentDummyMarkedMixtureMap q r y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      apply Quotient.sound
      exact sameMarkedTerminalLaw_rightIndependentDummy_publicMix
        q r t.1 t.2.1 t.2.2 E G

theorem rightIndependentDummyMarkedMixtureMap_affine
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := B) r) :
    rightIndependentDummyMarkedMixtureMap q r
        ((markedTerminalAbstractConvexMixtureSpace r).mix t x y) =
      (markedTerminalAbstractConvexMixtureSpace (prodDist q r)).mix t
        (rightIndependentDummyMarkedMixtureMap q r x)
        (rightIndependentDummyMarkedMixtureMap q r y) :=
  rightIndependentDummyMarkedMixtureMap_mix q r t x y

/-- The right dummy map is an exact order embedding of marked-law quotient
orders. -/
theorem rightIndependentDummyMarkedMixtureMap_rel_iff
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := B) r) :
    markedTerminalMixtureRel F h r hr x y ↔
      markedTerminalMixtureRel F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (rightIndependentDummyMarkedMixtureMap q r x)
        (rightIndependentDummyMarkedMixtureMap q r y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      letI : Fintype E.RecordType := E.recordFintype
      letI : DecidableEq E.RecordType := E.recordDecEq
      letI : Nonempty E.RecordType := E.recordNonempty
      letI : Fintype G.RecordType := G.recordFintype
      letI : DecidableEq G.RecordType := G.recordDecEq
      letI : Nonempty G.RecordType := G.recordNonempty
      have hE := rightIndependentDummy_pairWeak_neutrality
        F h E.K q r
      have hG := rightIndependentDummy_pairWeak_neutrality
        F h G.K q r
      simpa [markedTerminalMixtureRel_mk, MarkedPairWeak,
        rightIndependentDummyMarkedExperiment] using
          (pairWeak_iff_of_pairwiseWeakEquiv F h.a1 h.a3
            E.K (rightIndependentDummyChannel (A := A) E.K)
            G.K (rightIndependentDummyChannel (A := A) G.K)
            r (prodDist q r) r (prodDist q r)
            hE.1 hE.2 hG.1 hG.2)

end TraceableAgency.Theorem1
