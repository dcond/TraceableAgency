/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MarkedTerminal
import TraceableAgency.Theorem1.PairOrder
import TraceableAgency.PureTrace.Support.GenericHersteinMilnor

/-!
# Full-support marked-terminal Herstein--Milnor cardinalization

At one fixed full-support prior, marked terminal laws form a convex mixture
space.  The relation induced by the paper's block comparisons is a
calibratable independent weak order, hence admits an affine utility.
-/

namespace TraceableAgency.Theorem1

open Filter Set Topology
open TraceableAgency

universe u

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## Public-coin mixtures and marked-law affinity -/

/-- Publicly choose the first experiment with probability `t`; the public
branch tag is retained in the explicit record and the payoff remains
untagged. -/
noncomputable abbrev markedPublicMixExperiment
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A) :
    MarkedTerminalExperiment O A := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  exact
    { RecordType := E.RecordType ⊕ R.RecordType
      recordFintype := inferInstance
      recordDecEq := inferInstance
      recordNonempty := inferInstance
      channel :=
        Relabeling.relabelChannel (Equiv.refl A)
          (sumPayoffRecordEquiv O E.RecordType R.RecordType)
          (publicMixChannel t ht0 ht1 E.K R.K) }

theorem markedPublicMix_outcomeMarginal_inl
    (q : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A)
    (o : O) (r : E.RecordType) :
    (markedPublicMixExperiment t ht0 ht1 E R).outcomeMarginal
        q (o, Sum.inl r) =
      t * E.outcomeMarginal q (o, r) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  change Channel.outcomeMarginal
      (publicMixChannel t ht0 ht1 E.K R.K) q (Sum.inl (o, r)) = _
  exact hm_outcomeMarginal_publicMixChannel_inl
    q t ht0 ht1 E.K R.K (o, r)

theorem markedPublicMix_outcomeMarginal_inr
    (q : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A)
    (o : O) (r : R.RecordType) :
    (markedPublicMixExperiment t ht0 ht1 E R).outcomeMarginal
        q (o, Sum.inr r) =
      (1 - t) * R.outcomeMarginal q (o, r) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  change Channel.outcomeMarginal
      (publicMixChannel t ht0 ht1 E.K R.K) q (Sum.inr (o, r)) = _
  exact hm_outcomeMarginal_publicMixChannel_inr
    q t ht0 ht1 E.K R.K (o, r)

theorem markedPublicMix_posterior_inl
    (q : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A)
    (o : O) (r : E.RecordType) :
    (markedPublicMixExperiment t ht0 ht1 E R).posterior
        q (o, Sum.inl r) = E.posterior q (o, r) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  change Channel.posterior (publicMixChannel t ht0 ht1 E.K R.K) q
      (Sum.inl (o, r)) = Channel.posterior E.K q (o, r)
  exact hm_posterior_publicMixChannel_inl
    q t ht0 ht1 E.K R.K (o, r)

theorem markedPublicMix_posterior_inr
    (q : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A)
    (o : O) (r : R.RecordType) :
    (markedPublicMixExperiment t ht0 ht1 E R).posterior
        q (o, Sum.inr r) = R.posterior q (o, r) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  change Channel.posterior (publicMixChannel t ht0 ht1 E.K R.K) q
      (Sum.inr (o, r)) = Channel.posterior R.K q (o, r)
  exact hm_posterior_publicMixChannel_inr
    q t ht0 ht1 E.K R.K (o, r)

/-- The marked terminal law of a public mixture is the corresponding convex
combination, for every real test function. -/
theorem markedTerminalIntegral_publicMix
    (q : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q
        (markedPublicMixExperiment t ht0 ht1 E R) phi =
      t * markedTerminalIntegral q E phi +
        (1 - t) * markedTerminalIntegral q R phi := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  change
    (∑ z : O × (E.RecordType ⊕ R.RecordType),
      (markedPublicMixExperiment t ht0 ht1 E R).outcomeMarginal q z *
        phi (z.1,
          (markedPublicMixExperiment t ht0 ht1 E R).posterior q z)) =
      t * (∑ z : O × E.RecordType,
        E.outcomeMarginal q z * phi (z.1, E.posterior q z)) +
      (1 - t) * (∑ z : O × R.RecordType,
        R.outcomeMarginal q z * phi (z.1, R.posterior q z))
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _ho
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [markedPublicMix_outcomeMarginal_inl,
      markedPublicMix_posterior_inl]
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _ho
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _hr
    rw [markedPublicMix_outcomeMarginal_inr,
      markedPublicMix_posterior_inr]
    ring

/-- Public mixing respects marked-terminal-law equality. -/
theorem markedPublicMix_respects_sameMarkedTerminalLaw
    (q : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    {E E' R R' : MarkedTerminalExperiment O A}
    (hE : SameMarkedTerminalLaw q E E')
    (hR : SameMarkedTerminalLaw q R R') :
    SameMarkedTerminalLaw q
      (markedPublicMixExperiment t ht0 ht1 E R)
      (markedPublicMixExperiment t ht0 ht1 E' R') := by
  intro phi
  rw [markedTerminalIntegral_publicMix,
    markedTerminalIntegral_publicMix, hE phi, hR phi]

/-! ## Quotient mixture space -/

/-- Attainable marked terminal laws at the fixed prior. -/
abbrev MarkedTerminalMixtureSpace (q : TraceableAgency.Dist A) :=
  Quotient (markedTerminalSetoid (O := O) (A := A) q)

/-- All real tests are used as separating coordinates. -/
abbrev MarkedTerminalTest := O × TraceableAgency.Dist A → ℝ

/-- Marked-law integration descends to the quotient. -/
noncomputable def markedTerminalMixtureCoordinate
    (q : TraceableAgency.Dist A) :
    MarkedTerminalMixtureSpace (O := O) (A := A) q →
      MarkedTerminalTest (O := O) (A := A) → ℝ :=
  Quotient.lift (s := markedTerminalSetoid (O := O) (A := A) q)
    (fun E phi => markedTerminalIntegral q E phi)
    (by
      intro E E' hsame
      funext phi
      exact hsame phi)

@[simp]
theorem markedTerminalMixtureCoordinate_mk
    (q : TraceableAgency.Dist A) (E : MarkedTerminalExperiment O A)
    (phi : MarkedTerminalTest (O := O) (A := A)) :
    markedTerminalMixtureCoordinate q
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) phi =
      markedTerminalIntegral q E phi := by
  rfl

/-- Convex mixing of marked terminal laws. -/
noncomputable def markedTerminalMixture
    (q : TraceableAgency.Dist A) (t : Set.Ioo (0 : ℝ) 1) :
    MarkedTerminalMixtureSpace (O := O) (A := A) q →
      MarkedTerminalMixtureSpace (O := O) (A := A) q →
      MarkedTerminalMixtureSpace (O := O) (A := A) q :=
  Quotient.map₂
    (sa := markedTerminalSetoid (O := O) (A := A) q)
    (sb := markedTerminalSetoid (O := O) (A := A) q)
    (sc := markedTerminalSetoid (O := O) (A := A) q)
    (markedPublicMixExperiment t.1 t.2.1 t.2.2)
    (fun {_ _} hE {_ _} hR =>
      markedPublicMix_respects_sameMarkedTerminalLaw
        q t.1 t.2.1 t.2.2 hE hR)

@[simp]
theorem markedTerminalMixture_mk
    (q : TraceableAgency.Dist A) (t : Set.Ioo (0 : ℝ) 1)
    (E R : MarkedTerminalExperiment O A) :
    markedTerminalMixture q t
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q)
        (⟦R⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) =
      (⟦markedPublicMixExperiment t.1 t.2.1 t.2.2 E R⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) q) := by
  rfl

/-- The marked-law quotient as a separating affine-coordinate mixture
space. -/
noncomputable def markedTerminalAbstractConvexMixtureSpace
    (q : TraceableAgency.Dist A) :
    AbstractConvexMixtureSpace
      (MarkedTerminalMixtureSpace (O := O) (A := A) q) where
  Coordinate := ULift.{u + 1} (MarkedTerminalTest (O := O) (A := A))
  coordinate := fun x phi => markedTerminalMixtureCoordinate q x phi.down
  coordinate_ext := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ E =>
      induction y using Quotient.inductionOn with
      | _ G =>
        apply Quotient.sound
        intro phi
        exact hxy ⟨phi⟩
  mix := markedTerminalMixture q
  coordinate_mix := by
    intro t x y phi
    induction x using Quotient.inductionOn with
    | _ E =>
      induction y using Quotient.inductionOn with
      | _ R =>
        exact markedTerminalIntegral_publicMix
          q t.1 t.2.1 t.2.2 E R phi.down

/-! ## Quotient preference relation -/

/-- Block preference descended to marked terminal laws. -/
def markedTerminalMixtureRel
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    MarkedTerminalMixtureSpace (O := O) (A := A) q →
      MarkedTerminalMixtureSpace (O := O) (A := A) q → Prop :=
  fun x y =>
    Quotient.liftOn₂ x y
      (fun E G => MarkedPairWeak F q E q G)
      (by
        intro E G E' G' hE hG
        exact propext
          (pairWeak_respects_sameMarkedTerminalLaw
            F h.a1 h.a3 h.a4 q q hq hq E E' G G' hE hG))

@[simp]
theorem markedTerminalMixtureRel_mk
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    markedTerminalMixtureRel F h q hq
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦G⟧ ↔
      MarkedPairWeak F q E q G := by
  rfl

theorem markedTerminalMixtureRel_out
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y ↔
      MarkedPairWeak F q x.out q y.out := by
  change markedTerminalMixtureRel F h q hq x y ↔
    markedTerminalMixtureRel F h q hq ⟦x.out⟧ ⟦y.out⟧
  rw [Quotient.out_eq x, Quotient.out_eq y]

theorem markedTerminalMixtureRel_complete
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y ∨
      markedTerminalMixtureRel F h q hq y x := by
  let E := x.out
  let G := y.out
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  rcases pairWeak_complete F h q E.K q G.K with hEG | hGE
  · left
    exact (markedTerminalMixtureRel_out F h q hq x y).2 hEG
  · right
    exact (markedTerminalMixtureRel_out F h q hq y x).2 hGE

theorem markedTerminalMixtureRel_transitive
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y z : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y →
    markedTerminalMixtureRel F h q hq y z →
    markedTerminalMixtureRel F h q hq x z := by
  intro hxy hyz
  let E := x.out
  let G := y.out
  let H := z.out
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  letI : Fintype H.RecordType := H.recordFintype
  letI : DecidableEq H.RecordType := H.recordDecEq
  letI : Nonempty H.RecordType := H.recordNonempty
  apply (markedTerminalMixtureRel_out F h q hq x z).2
  exact pairWeak_transitive_sameAction F h q E.K q G.K q H.K
    ((markedTerminalMixtureRel_out F h q hq x y).1 hxy)
    ((markedTerminalMixtureRel_out F h q hq y z).1 hyz)

/-! ## Tagged-record padding for public independence -/

/-- Deterministically inject records into the left summand. -/
noncomputable def markedTagLeftProcessor
    {R S : Type u} [Fintype R] [Fintype S]
    [DecidableEq R] [DecidableEq S] : RecordProcessor O R (R ⊕ S) :=
  fun z => TraceableAgency.Dist.pure (Sum.inl z.2)

/-- Deterministically inject records into the right summand. -/
noncomputable def markedTagRightProcessor
    {R S : Type u} [Fintype R] [Fintype S]
    [DecidableEq R] [DecidableEq S] : RecordProcessor O S (R ⊕ S) :=
  fun z => TraceableAgency.Dist.pure (Sum.inr z.2)

/-- Pad an experiment into the left side of a common record alphabet. -/
noncomputable abbrev markedPadLeftExperiment
    (E : MarkedTerminalExperiment O A)
    (S : Type u) [Fintype S] [DecidableEq S] [Nonempty S] :
    MarkedTerminalExperiment O A := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  exact
    { RecordType := E.RecordType ⊕ S
      recordFintype := inferInstance
      recordDecEq := inferInstance
      recordNonempty := inferInstance
      channel := fun a =>
        { prob := fun z => match z.2 with
            | Sum.inl r => E.K a (z.1, r)
            | Sum.inr _ => 0
          nonneg := fun z => by
            cases z.2 with
            | inl r => exact (E.K a).nonneg (z.1, r)
            | inr s => exact le_rfl
          sum_eq_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [Fintype.sum_sum_type]
            simp only [Finset.sum_const_zero, add_zero]
            rw [← Fintype.sum_prod_type]
            exact (E.K a).sum_eq_one } }

/-- Pad an experiment into the right side of a common record alphabet. -/
noncomputable abbrev markedPadRightExperiment
    (R : Type u) [Fintype R] [DecidableEq R] [Nonempty R]
    (G : MarkedTerminalExperiment O A) :
    MarkedTerminalExperiment O A := by
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  exact
    { RecordType := R ⊕ G.RecordType
      recordFintype := inferInstance
      recordDecEq := inferInstance
      recordNonempty := inferInstance
      channel := fun a =>
        { prob := fun z => match z.2 with
            | Sum.inl _ => 0
            | Sum.inr s => G.K a (z.1, s)
          nonneg := fun z => by
            cases z.2 with
            | inl r => exact le_rfl
            | inr s => exact (G.K a).nonneg (z.1, s)
          sum_eq_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [Fintype.sum_sum_type]
            simp only [Finset.sum_const_zero, zero_add]
            rw [← Fintype.sum_prod_type]
            exact (G.K a).sum_eq_one } }

theorem markedPadLeft_channel_apply_inl
    {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    (E : MarkedTerminalExperiment O A) (a : A) (o : O)
    (r : E.RecordType) :
    (markedPadLeftExperiment E S).K a (o, Sum.inl r) = E.K a (o, r) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  rfl

theorem markedPadLeft_channel_apply_inr
    {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    (E : MarkedTerminalExperiment O A) (a : A) (o : O) (s : S) :
    (markedPadLeftExperiment E S).K a (o, Sum.inr s) = 0 := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  rfl

theorem markedPadRight_channel_apply_inl
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (G : MarkedTerminalExperiment O A) (a : A) (o : O) (r : R) :
    (markedPadRightExperiment R G).K a (o, Sum.inl r) = 0 := by
  classical
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  rfl

theorem markedPadRight_channel_apply_inr
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (G : MarkedTerminalExperiment O A) (a : A) (o : O)
    (s : G.RecordType) :
    (markedPadRightExperiment R G).K a (o, Sum.inr s) = G.K a (o, s) := by
  classical
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  rfl

/-- Left padding preserves the entire marked terminal law. -/
theorem sameMarkedTerminalLaw_markedPadLeft
    (q : TraceableAgency.Dist A)
    {S : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    (E : MarkedTerminalExperiment O A) :
    SameMarkedTerminalLaw q E (markedPadLeftExperiment E S) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  intro phi
  unfold markedTerminalIntegral
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type]
  have hmargInl : ∀ o r,
      (markedPadLeftExperiment E S).outcomeMarginal q (o, Sum.inl r) =
        E.outcomeMarginal q (o, r) := by
    intro o r
    simp only [MarkedTerminalExperiment.outcomeMarginal,
      Channel.outcomeMarginal_apply]
  have hmargInr : ∀ o s,
      (markedPadLeftExperiment E S).outcomeMarginal q (o, Sum.inr s) = 0 := by
    intro o s
    simp [MarkedTerminalExperiment.outcomeMarginal,
      Channel.outcomeMarginal_apply, markedPadLeft_channel_apply_inr]
  have hpostInl : ∀ o r,
      (markedPadLeftExperiment E S).posterior q (o, Sum.inl r) =
        E.posterior q (o, r) := by
    intro o r
    have hm :
        Channel.outcomeMarginal (markedPadLeftExperiment E S).K q
            (o, Sum.inl r) =
          Channel.outcomeMarginal E.K q (o, r) := by
      simpa [MarkedTerminalExperiment.outcomeMarginal] using hmargInl o r
    apply TraceableAgency.Dist.ext
    intro a
    unfold MarkedTerminalExperiment.posterior Channel.posterior
    by_cases hp : Channel.outcomeMarginal E.K q (o, r) > 0
    · have hp' :
          Channel.outcomeMarginal (markedPadLeftExperiment E S).K q
              (o, Sum.inl r) > 0 := by
        simpa [hm] using hp
      simp only [dif_pos hp, dif_pos hp']
      simp only [hm, markedPadLeft_channel_apply_inl]
    · have hp' : ¬
          Channel.outcomeMarginal (markedPadLeftExperiment E S).K q
              (o, Sum.inl r) > 0 := by
        simpa [hm] using hp
      simp only [dif_neg hp, dif_neg hp']
  simp only [hmargInl, hmargInr, hpostInl, zero_mul,
    Finset.sum_const_zero, add_zero]

/-- Right padding preserves the entire marked terminal law. -/
theorem sameMarkedTerminalLaw_markedPadRight
    (q : TraceableAgency.Dist A)
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (G : MarkedTerminalExperiment O A) :
    SameMarkedTerminalLaw q G (markedPadRightExperiment R G) := by
  classical
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  intro phi
  unfold markedTerminalIntegral
  simp_rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_sum_type]
  have hmargInl : ∀ o r,
      (markedPadRightExperiment R G).outcomeMarginal q (o, Sum.inl r) = 0 := by
    intro o r
    simp [MarkedTerminalExperiment.outcomeMarginal,
      Channel.outcomeMarginal_apply, markedPadRight_channel_apply_inl]
  have hmargInr : ∀ o s,
      (markedPadRightExperiment R G).outcomeMarginal q (o, Sum.inr s) =
        G.outcomeMarginal q (o, s) := by
    intro o s
    simp only [MarkedTerminalExperiment.outcomeMarginal,
      Channel.outcomeMarginal_apply]
  have hpostInr : ∀ o s,
      (markedPadRightExperiment R G).posterior q (o, Sum.inr s) =
        G.posterior q (o, s) := by
    intro o s
    have hm :
        Channel.outcomeMarginal (markedPadRightExperiment R G).K q
            (o, Sum.inr s) =
          Channel.outcomeMarginal G.K q (o, s) := by
      simpa [MarkedTerminalExperiment.outcomeMarginal] using hmargInr o s
    apply TraceableAgency.Dist.ext
    intro a
    unfold MarkedTerminalExperiment.posterior Channel.posterior
    by_cases hp : Channel.outcomeMarginal G.K q (o, s) > 0
    · have hp' :
          Channel.outcomeMarginal (markedPadRightExperiment R G).K q
              (o, Sum.inr s) > 0 := by
        simpa [hm] using hp
      simp only [dif_pos hp, dif_pos hp']
      simp only [hm, markedPadRight_channel_apply_inr]
    · have hp' : ¬
          Channel.outcomeMarginal (markedPadRightExperiment R G).K q
              (o, Sum.inr s) > 0 := by
        simpa [hm] using hp
      simp only [dif_neg hp, dif_neg hp']
  simp only [hmargInl, hmargInr, hpostInr, zero_mul,
    Finset.sum_const_zero, zero_add]

/-! ## Marked terminal laws of compound experiments -/

/-- The marked terminal integral written directly for a channel with a fixed
record alphabet. -/
noncomputable def markedChannelIntegral
    {R : Type u} [Fintype R]
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (phi : O × TraceableAgency.Dist A → ℝ) : ℝ :=
  ∑ z : O × R,
    Channel.outcomeMarginal K q z * phi (z.1, Channel.posterior K q z)

theorem commonPayoffCompound_outcomeMarginal
    {Y : Type u} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × Rec y))
    (y : Y) (o : O) (r : Rec y) :
    Channel.outcomeMarginal (commonPayoffCompound Rec P K) q
        (o, ⟨y, r⟩) =
      Channel.outcomeMarginal
        (seqComposeDep P (fun y => O × Rec y) K) q ⟨y, (o, r)⟩ := by
  classical
  simp [commonPayoffCompound, Channel.outcomeMarginal_apply,
    Relabeling.relabelChannel, compoundPayoffRecordEquiv,
    sigmaPayoffRecordEquiv]

theorem commonPayoffCompound_posterior
    {Y : Type u} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × Rec y))
    (y : Y) (o : O) (r : Rec y) :
    Channel.posterior (commonPayoffCompound Rec P K) q (o, ⟨y, r⟩) =
      Channel.posterior
        (seqComposeDep P (fun y => O × Rec y) K) q ⟨y, (o, r)⟩ := by
  classical
  apply TraceableAgency.Dist.ext
  intro a
  unfold Channel.posterior
  have hm := commonPayoffCompound_outcomeMarginal Rec q P K y o r
  by_cases hp :
      Channel.outcomeMarginal
        (seqComposeDep P (fun y => O × Rec y) K) q ⟨y, (o, r)⟩ > 0
  · have hp' :
        Channel.outcomeMarginal (commonPayoffCompound Rec P K) q
            (o, ⟨y, r⟩) > 0 := by
      rw [hm]
      exact hp
    simp only [dif_pos hp, dif_pos hp']
    simp [commonPayoffCompound, Relabeling.relabelChannel,
      compoundPayoffRecordEquiv, sigmaPayoffRecordEquiv, hm]
  · have hp' : ¬
        Channel.outcomeMarginal (commonPayoffCompound Rec P K) q
            (o, ⟨y, r⟩) > 0 := by
      rw [hm]
      exact hp
    simp only [dif_neg hp, dif_neg hp']

/-- Marked terminal integration obeys the finite tower law for the paper's
dependent compound environment. -/
theorem markedChannelIntegral_commonPayoffCompound
    {Y : Type u} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × Rec y))
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral q (commonPayoffCompound Rec P K) phi =
      ∑ y : Y, Channel.outcomeMarginal P q y *
        markedChannelIntegral (Channel.posterior P q y) (K y) phi := by
  classical
  unfold markedChannelIntegral
  rw [← Equiv.sum_comp (compoundPayoffRecordEquiv Y O Rec)]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _hz
  rcases z with ⟨o, r⟩
  rw [commonPayoffCompound_outcomeMarginal,
    commonPayoffCompound_posterior]
  change
    Channel.outcomeMarginal
        (seqComposeDep P (fun y => O × Rec y) K) q ⟨y, (o, r)⟩ *
        phi (o, Channel.posterior
          (seqComposeDep P (fun y => O × Rec y) K) q ⟨y, (o, r)⟩) =
      Channel.outcomeMarginal P q y *
        (Channel.outcomeMarginal (K y) (Channel.posterior P q y) (o, r) *
          phi (o, Channel.posterior (K y) (Channel.posterior P q y) (o, r)))
  have hmarg := outcomeMarginal_seqComposeDep_apply
    q P (fun y => O × Rec y) K ⟨y, (o, r)⟩
  by_cases hpos :
      Channel.outcomeMarginal
        (seqComposeDep P (fun y => O × Rec y) K) q
          ⟨y, (o, r)⟩ > 0
  · rw [posterior_seqComposeDep_of_pos
      q P (fun y => O × Rec y) K y (o, r) hpos, hmarg]
    ring
  · have hzero :
        Channel.outcomeMarginal
          (seqComposeDep P (fun y => O × Rec y) K) q
            ⟨y, (o, r)⟩ = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        ((Channel.outcomeMarginal
          (seqComposeDep P (fun y => O × Rec y) K) q).nonneg
            ⟨y, (o, r)⟩)
    have hprod :
        Channel.outcomeMarginal P q y *
          Channel.outcomeMarginal (K y) (Channel.posterior P q y) (o, r) = 0 := by
      rw [hmarg] at hzero
      exact hzero
    rw [hzero, zero_mul]
    calc
      0 =
          (Channel.outcomeMarginal P q y *
            Channel.outcomeMarginal (K y) (Channel.posterior P q y) (o, r)) *
              phi (o, Channel.posterior (K y) (Channel.posterior P q y) (o, r)) := by
            rw [hprod, zero_mul]
      _ = Channel.outcomeMarginal P q y *
          (Channel.outcomeMarginal (K y) (Channel.posterior P q y) (o, r) *
            phi (o, Channel.posterior (K y) (Channel.posterior P q y) (o, r))) := by
            ring

/-! ## Finite-branch A8 implies public-mixture independence -/

/-- Public-coin independence of the marked pair order.  The common record
alphabet in the informative branch is supplied by deterministic sum padding;
the strict direction is exactly the strict finite-branch clause derived from A8. -/
theorem markedPairWeak_publicMix_independence
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G R : MarkedTerminalExperiment O A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    MarkedPairWeak F q E q G ↔
      MarkedPairWeak F q
        (markedPublicMixExperiment t ht0 ht1 E R) q
        (markedPublicMixExperiment t ht0 ht1 G R) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  let Y := PUnit.{u + 1} ⊕ PUnit.{u + 1}
  letI : Fintype Y := inferInstance
  letI : DecidableEq Y := inferInstance
  letI : Nonempty Y := inferInstance
  let U : Channel A PUnit.{u + 1} := Channel.uninformativeChannelU A
  let C : Channel A Y := publicMixChannel t ht0 ht1 U U
  let Epad := markedPadLeftExperiment E G.RecordType
  let Gpad := markedPadRightExperiment E.RecordType G
  let Rec : Y → Type u
    | Sum.inl _ => E.RecordType ⊕ G.RecordType
    | Sum.inr _ => R.RecordType
  let recFintype : ∀ y, Fintype (Rec y)
    | Sum.inl _ => inferInstance
    | Sum.inr _ => R.recordFintype
  let recDecEq : ∀ y, DecidableEq (Rec y)
    | Sum.inl _ => inferInstance
    | Sum.inr _ => R.recordDecEq
  let recNonempty : ∀ y, Nonempty (Rec y)
    | Sum.inl _ => inferInstance
    | Sum.inr _ => R.recordNonempty
  letI : ∀ y, Fintype (Rec y) := recFintype
  letI : ∀ y, DecidableEq (Rec y) := recDecEq
  letI : ∀ y, Nonempty (Rec y) := recNonempty
  let QE : ∀ y, Channel A (O × Rec y)
    | Sum.inl _ => Epad.K
    | Sum.inr _ => R.K
  let QG : ∀ y, Channel A (O × Rec y)
    | Sum.inl _ => Gpad.K
    | Sum.inr _ => R.K
  let compFintype : Fintype ((y : Y) × Rec y) := inferInstance
  let compDecEq : DecidableEq ((y : Y) × Rec y) := inferInstance
  let compNonempty : Nonempty ((y : Y) × Rec y) := inferInstance
  letI : Fintype ((y : Y) × Rec y) := compFintype
  letI : DecidableEq ((y : Y) × Rec y) := compDecEq
  letI : Nonempty ((y : Y) × Rec y) := compNonempty
  let Ecomp : MarkedTerminalExperiment O A :=
    { RecordType := (y : Y) × Rec y
      recordFintype := compFintype
      recordDecEq := compDecEq
      recordNonempty := compNonempty
      channel := commonPayoffCompound Rec C QE }
  let Gcomp : MarkedTerminalExperiment O A :=
    { RecordType := (y : Y) × Rec y
      recordFintype := compFintype
      recordDecEq := compDecEq
      recordNonempty := compNonempty
      channel := commonPayoffCompound Rec C QG }
  let Emix := markedPublicMixExperiment t ht0 ht1 E R
  let Gmix := markedPublicMixExperiment t ht0 ht1 G R
  have hEpad : SameMarkedTerminalLaw q E Epad := by
    exact sameMarkedTerminalLaw_markedPadLeft q E
  have hGpad : SameMarkedTerminalLaw q G Gpad := by
    exact sameMarkedTerminalLaw_markedPadRight q G
  have hU_marginal : Channel.outcomeMarginal U q default = 1 := by
    simp [U, Channel.outcomeMarginal_apply,
      Channel.uninformativeChannelU, q.sum_eq_one]
  have hU_posterior : Channel.posterior U q default = q := by
    apply TraceableAgency.Dist.ext
    intro a
    simp [U, Channel.posterior, Channel.outcomeMarginal_apply,
      Channel.uninformativeChannelU, q.sum_eq_one]
  have hC_left_marginal :
      Channel.outcomeMarginal C q (Sum.inl default) = t := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_outcomeMarginal_publicMixChannel_inl, hU_marginal, mul_one]
  have hC_right_marginal :
      Channel.outcomeMarginal C q (Sum.inr default) = 1 - t := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_outcomeMarginal_publicMixChannel_inr, hU_marginal, mul_one]
  have hC_left_posterior :
      Channel.posterior C q (Sum.inl default) = q := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_posterior_publicMixChannel_inl, hU_posterior]
  have hC_right_posterior :
      Channel.posterior C q (Sum.inr default) = q := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_posterior_publicMixChannel_inr, hU_posterior]
  have hEcomp : SameMarkedTerminalLaw q Ecomp Emix := by
    intro phi
    change markedChannelIntegral q (commonPayoffCompound Rec C QE) phi =
      markedTerminalIntegral q
        (markedPublicMixExperiment t ht0 ht1 E R) phi
    rw [markedChannelIntegral_commonPayoffCompound,
      markedTerminalIntegral_publicMix]
    simp only [Y, Fintype.sum_sum_type, Fintype.sum_unique]
    rw [hC_left_marginal, hC_right_marginal,
      hC_left_posterior, hC_right_posterior]
    change
      t * markedTerminalIntegral q Epad phi +
          (1 - t) * markedTerminalIntegral q R phi =
        t * markedTerminalIntegral q E phi +
          (1 - t) * markedTerminalIntegral q R phi
    rw [← hEpad phi]
  have hGcomp : SameMarkedTerminalLaw q Gcomp Gmix := by
    intro phi
    change markedChannelIntegral q (commonPayoffCompound Rec C QG) phi =
      markedTerminalIntegral q
        (markedPublicMixExperiment t ht0 ht1 G R) phi
    rw [markedChannelIntegral_commonPayoffCompound,
      markedTerminalIntegral_publicMix]
    simp only [Y, Fintype.sum_sum_type, Fintype.sum_unique]
    rw [hC_left_marginal, hC_right_marginal,
      hC_left_posterior, hC_right_posterior]
    change
      t * markedTerminalIntegral q Gpad phi +
          (1 - t) * markedTerminalIntegral q R phi =
        t * markedTerminalIntegral q G phi +
          (1 - t) * markedTerminalIntegral q R phi
    rw [← hGpad phi]
  have hpad :
      MarkedPairWeak F q E q G ↔ MarkedPairWeak F q Epad q Gpad :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 q q hq hq E Epad G Gpad hEpad hGpad
  have hcomp :
      MarkedPairWeak F q Ecomp q Gcomp ↔
        MarkedPairWeak F q Emix q Gmix :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 q q hq hq Ecomp Emix Gcomp Gmix hEcomp hGcomp
  constructor
  · intro hEG
    have hbranch : ∀ y, BranchPositive C q y →
        pairWeak F (branchPosterior C q y) (QE y)
          (branchPosterior C q y) (QG y) := by
      intro y _hy
      rcases y with (_ | _)
      · simpa [QE, QG, Epad, Gpad, branchPosterior,
          hC_left_posterior, MarkedPairWeak] using hpad.mp hEG
      · simpa [QE, QG, branchPosterior, hC_right_posterior] using
          (pairWeak_refl F h q R.K)
    have hraw := h.a6.1 Rec C QE QG q hbranch
    have hbundled : MarkedPairWeak F q Ecomp q Gcomp := by
      simpa [MarkedPairWeak, Ecomp, Gcomp] using hraw
    exact hcomp.mp hbundled
  · intro hmix
    have hbundled : MarkedPairWeak F q Ecomp q Gcomp := hcomp.mpr hmix
    have hraw : pairWeak F q (commonPayoffCompound Rec C QE)
        q (commonPayoffCompound Rec C QG) := by
      simpa [MarkedPairWeak, Ecomp, Gcomp] using hbundled
    by_contra hnot
    have hGE : MarkedPairWeak F q G q E := by
      rcases pairWeak_complete F h q E.K q G.K with hEG | hGE
      · exact False.elim (hnot (by simpa [MarkedPairWeak] using hEG))
      · simpa [MarkedPairWeak] using hGE
    have hGpadEpad : MarkedPairWeak F q Gpad q Epad := by
      exact (pairWeak_respects_sameMarkedTerminalLaw
        F h.a1 h.a3 h.a4 q q hq hq G Gpad E Epad hGpad hEpad).mp hGE
    have hnotEpadGpad : ¬ MarkedPairWeak F q Epad q Gpad := by
      intro hp
      exact hnot (hpad.mpr hp)
    have hstrictPad : pairStrict F q Gpad.K q Epad.K := by
      exact (pairStrict_iff_pairWeak_not_swap
        F h.a1 h.a3 h.a4 h.a5 q Gpad.K q Epad.K).2
          ⟨by simpa [MarkedPairWeak] using hGpadEpad,
            by simpa [MarkedPairWeak] using hnotEpadGpad⟩
    have hbranchRev : ∀ y, BranchPositive C q y →
        pairWeak F (branchPosterior C q y) (QG y)
          (branchPosterior C q y) (QE y) := by
      intro y _hy
      rcases y with (_ | _)
      · simpa [QE, QG, Epad, Gpad, branchPosterior,
          hC_left_posterior, MarkedPairWeak] using hGpadEpad
      · simpa [QE, QG, branchPosterior, hC_right_posterior] using
          (pairWeak_refl F h q R.K)
    have hleftPositive : BranchPositive C q (Sum.inl default) := by
      change Channel.outcomeMarginal C q (Sum.inl default) > 0
      rw [hC_left_marginal]
      exact ht0
    have hstrictRaw := h.a6.2 Rec C QG QE q hbranchRev
      ⟨Sum.inl default, hleftPositive, by
        simpa [QG, QE, branchPosterior, hC_left_posterior] using hstrictPad⟩
    have hstrictParts := (pairStrict_iff_pairWeak_not_swap
      F h.a1 h.a3 h.a4 h.a5 q
        (commonPayoffCompound Rec C QG) q
        (commonPayoffCompound Rec C QE)).1 hstrictRaw
    exact hstrictParts.2 hraw

/-- Public-mixture independence descended to the marked-law quotient. -/
theorem markedTerminalMixtureRel_independence
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y z : MarkedTerminalMixtureSpace (O := O) (A := A) q)
    (t : Set.Ioo (0 : ℝ) 1) :
    markedTerminalMixtureRel F h q hq x y ↔
      markedTerminalMixtureRel F h q hq
        ((markedTerminalAbstractConvexMixtureSpace q).mix t x z)
        ((markedTerminalAbstractConvexMixtureSpace q).mix t y z) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      induction z using Quotient.inductionOn with
      | _ R =>
        simpa [markedTerminalAbstractConvexMixtureSpace,
          markedTerminalMixtureRel_mk] using
            markedPairWeak_publicMix_independence
              F h q hq E G R t.1 t.2.1 t.2.2

/-! ## A fixed-alphabet closed public segment -/

/-- The closed public segment, including its zero and one endpoints, on the
single record alphabet `E.RecordType ⊕ L.RecordType`. -/
noncomputable abbrev markedClosedSegmentExperiment
    (t : HMUnitInterval) (E L : MarkedTerminalExperiment O A) :
    MarkedTerminalExperiment O A := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  exact
    { RecordType := E.RecordType ⊕ L.RecordType
      recordFintype := inferInstance
      recordDecEq := inferInstance
      recordNonempty := inferInstance
      channel := fun a =>
        { prob := fun z => match z.2 with
            | Sum.inl r => t.1 * E.K a (z.1, r)
            | Sum.inr s => (1 - t.1) * L.K a (z.1, s)
          nonneg := fun z => by
            rcases z with ⟨o, r | s⟩
            · exact mul_nonneg t.2.1 ((E.K a).nonneg (o, r))
            · exact mul_nonneg (sub_nonneg.mpr t.2.2)
                ((L.K a).nonneg (o, s))
          sum_eq_one := by
            rw [Fintype.sum_prod_type]
            simp_rw [Fintype.sum_sum_type]
            rw [Finset.sum_add_distrib]
            simp_rw [← Finset.mul_sum]
            rw [← Fintype.sum_prod_type, ← Fintype.sum_prod_type,
              (E.K a).sum_eq_one, (L.K a).sum_eq_one]
            ring } }

@[simp]
theorem markedClosedSegment_channel_inl
    (t : HMUnitInterval) (E L : MarkedTerminalExperiment O A)
    (a : A) (o : O) (r : E.RecordType) :
    (markedClosedSegmentExperiment t E L).K a (o, Sum.inl r) =
      t.1 * E.K a (o, r) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  rfl

@[simp]
theorem markedClosedSegment_channel_inr
    (t : HMUnitInterval) (E L : MarkedTerminalExperiment O A)
    (a : A) (o : O) (s : L.RecordType) :
    (markedClosedSegmentExperiment t E L).K a (o, Sum.inr s) =
      (1 - t.1) * L.K a (o, s) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  rfl

/-- The fixed-alphabet segment channel varies pointwise continuously in its
coefficient. -/
theorem markedClosedSegment_channelConverges
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (𝓝 t))
    (E L : MarkedTerminalExperiment O A) :
    ∀ a (z : O × (E.RecordType ⊕ L.RecordType)),
      Tendsto
        (fun n => (markedClosedSegmentExperiment (tseq n) E L).K a z)
        atTop (𝓝 ((markedClosedSegmentExperiment t E L).K a z)) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  have hval : Tendsto (fun n => (tseq n).1) atTop (𝓝 t.1) :=
    (continuous_subtype_val.tendsto t).comp ht
  intro a z
  rcases z with ⟨o, r | s⟩
  · simpa only [markedClosedSegment_channel_inl] using
      hval.mul tendsto_const_nhds
  · simpa only [markedClosedSegment_channel_inr] using
      (tendsto_const_nhds.sub hval).mul tendsto_const_nhds

/-- Every real test integrates affinely along the fixed-alphabet closed
segment, including the two zero-mass endpoint branches. -/
theorem markedTerminalIntegral_closedSegment
    (q : TraceableAgency.Dist A) (t : HMUnitInterval)
    (E L : MarkedTerminalExperiment O A)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q (markedClosedSegmentExperiment t E L) phi =
      t.1 * markedTerminalIntegral q E phi +
        (1 - t.1) * markedTerminalIntegral q L phi := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  by_cases h0 : t.1 = 0
  · have hK : (markedClosedSegmentExperiment t E L).K =
        (markedPadRightExperiment E.RecordType L).K := by
      funext a
      apply TraceableAgency.Dist.ext
      intro z
      rcases z with ⟨o, r | s⟩
      · simp [h0]
      · simp [h0]
    change markedChannelIntegral q
      (markedClosedSegmentExperiment t E L).K phi = _
    rw [hK]
    change markedTerminalIntegral q
      (markedPadRightExperiment E.RecordType L) phi = _
    rw [← (sameMarkedTerminalLaw_markedPadRight
      (O := O) q L phi)]
    simp [h0]
  · by_cases h1 : t.1 = 1
    · have hK : (markedClosedSegmentExperiment t E L).K =
          (markedPadLeftExperiment E L.RecordType).K := by
        funext a
        apply TraceableAgency.Dist.ext
        intro z
        rcases z with ⟨o, r | s⟩
        · simp [h1]
        · simp [h1]
      change markedChannelIntegral q
        (markedClosedSegmentExperiment t E L).K phi = _
      rw [hK]
      change markedTerminalIntegral q
        (markedPadLeftExperiment E L.RecordType) phi = _
      rw [← (sameMarkedTerminalLaw_markedPadLeft
        (O := O) q E phi)]
      simp [h1]
    · have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm h0)
      have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 h1
      have hK : (markedClosedSegmentExperiment t E L).K =
          (markedPublicMixExperiment t.1 ht0 ht1 E L).K := by
        funext a
        apply TraceableAgency.Dist.ext
        intro z
        rcases z with ⟨o, r | s⟩
        · rfl
        · rfl
      change markedChannelIntegral q
        (markedClosedSegmentExperiment t E L).K phi = _
      rw [hK]
      change markedTerminalIntegral q
        (markedPublicMixExperiment t.1 ht0 ht1 E L) phi = _
      exact markedTerminalIntegral_publicMix
        q t.1 ht0 ht1 E L phi

/-- The fixed-alphabet representative is exactly the generic closed segment
in the marked-law quotient. -/
theorem markedClosedSegment_quotient_eq_hmSegment
    (q : TraceableAgency.Dist A) (t : HMUnitInterval)
    (E L : MarkedTerminalExperiment O A) :
    (⟦markedClosedSegmentExperiment t E L⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) q) =
      hmSegment (markedTerminalAbstractConvexMixtureSpace q) t
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦L⟧ := by
  apply (markedTerminalAbstractConvexMixtureSpace q).coordinate_ext
  intro phi
  change markedTerminalIntegral q
      (markedClosedSegmentExperiment t E L) phi.down = _
  rw [markedTerminalIntegral_closedSegment,
    hmSegment_coordinate]
  rfl

/-- A2 closes the upper contour of a fixed target along the fixed-alphabet
marked segment. -/
theorem markedPairWeak_closedSegment_limit_left
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A)
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (𝓝 t))
    (E L T : MarkedTerminalExperiment O A)
    (hrel : ∀ n,
      MarkedPairWeak F q (markedClosedSegmentExperiment (tseq n) E L) q T) :
    MarkedPairWeak F q (markedClosedSegmentExperiment t E L) q T := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  letI : Fintype T.RecordType := T.recordFintype
  letI : DecidableEq T.RecordType := T.recordDecEq
  letI : Nonempty T.RecordType := T.recordNonempty
  let Kseq := fun n => commonPayoffBlockChannel
    (markedClosedSegmentExperiment (tseq n) E L).K T.K
  let K := commonPayoffBlockChannel
    (markedClosedSegmentExperiment t E L).K T.K
  have hK : ChannelConverges Kseq K := by
    intro a z
    rcases a with a | a
    · rcases z with ⟨o, rs⟩
      rcases rs with (r | s) | u
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inl r)
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inr s)
      · exact tendsto_const_nhds
    · rcases z with ⟨o, rs⟩
      rcases rs with (r | s) | u
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
  have hleft : DistConverges
      (fun _ => (leftBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (leftBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  have hright : DistConverges
      (fun _ => (rightBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (rightBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  change F.rel K (leftBlockDist q) (rightBlockDist q)
  exact h.a2 Kseq K
    (fun _ => leftBlockDist q) (fun _ => rightBlockDist q)
    (leftBlockDist q) (rightBlockDist q)
    hK hleft hright (by
      intro n
      change F.rel (Kseq n) (leftBlockDist q) (rightBlockDist q)
      simpa [Kseq, MarkedPairWeak, pairWeak] using hrel n)

/-- A2 closes the lower contour of a fixed target along the same segment. -/
theorem markedPairWeak_closedSegment_limit_right
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A)
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (𝓝 t))
    (T E L : MarkedTerminalExperiment O A)
    (hrel : ∀ n,
      MarkedPairWeak F q T q (markedClosedSegmentExperiment (tseq n) E L)) :
    MarkedPairWeak F q T q (markedClosedSegmentExperiment t E L) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  letI : Fintype T.RecordType := T.recordFintype
  letI : DecidableEq T.RecordType := T.recordDecEq
  letI : Nonempty T.RecordType := T.recordNonempty
  let Kseq := fun n => commonPayoffBlockChannel T.K
    (markedClosedSegmentExperiment (tseq n) E L).K
  let K := commonPayoffBlockChannel T.K
    (markedClosedSegmentExperiment t E L).K
  have hK : ChannelConverges Kseq K := by
    intro a z
    rcases a with a | a
    · rcases z with ⟨o, rs⟩
      rcases rs with u | (r | s)
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
    · rcases z with ⟨o, rs⟩
      rcases rs with u | (r | s)
      · exact tendsto_const_nhds
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inl r)
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inr s)
  have hleft : DistConverges
      (fun _ => (leftBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (leftBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  have hright : DistConverges
      (fun _ => (rightBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (rightBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  change F.rel K (leftBlockDist q) (rightBlockDist q)
  exact h.a2 Kseq K
    (fun _ => leftBlockDist q) (fun _ => rightBlockDist q)
    (leftBlockDist q) (rightBlockDist q)
    hK hleft hright (by
      intro n
      change F.rel (Kseq n) (leftBlockDist q) (rightBlockDist q)
      simpa [Kseq, MarkedPairWeak, pairWeak] using hrel n)

/-- Direct calibration on a marked-law segment.  Only A2 on the two fixed
common-block alphabets is used for closedness. -/
theorem markedTerminalMixtureRel_segment_calibration
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (high target low : MarkedTerminalMixtureSpace (O := O) (A := A) q)
    (hhigh : markedTerminalMixtureRel F h q hq high target)
    (hlow : markedTerminalMixtureRel F h q hq target low) :
    ∃ t : HMUnitInterval,
      HMIndiff (markedTerminalMixtureRel F h q hq) target
        (hmSegment (markedTerminalAbstractConvexMixtureSpace q)
          t high low) := by
  induction high using Quotient.inductionOn with
  | _ E =>
    induction target using Quotient.inductionOn with
    | _ T =>
      induction low using Quotient.inductionOn with
      | _ L =>
        let M := markedTerminalAbstractConvexMixtureSpace
          (O := O) (A := A) q
        let Rel := markedTerminalMixtureRel
          (O := O) (A := A) F h q hq
        let upper : Set HMUnitInterval :=
          {t | Rel (hmSegment M t
            (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦L⟧) ⟦T⟧}
        let lower : Set HMUnitInterval :=
          {t | Rel ⟦T⟧ (hmSegment M t
            (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦L⟧)}
        have hupperClosed : IsClosed upper := by
          apply IsSeqClosed.isClosed
          intro tseq t htmem htt
          have hraw : ∀ n,
              MarkedPairWeak F q
                (markedClosedSegmentExperiment (tseq n) E L) q T := by
            intro n
            apply (markedTerminalMixtureRel_mk F h q hq
              (markedClosedSegmentExperiment (tseq n) E L) T).1
            rw [markedClosedSegment_quotient_eq_hmSegment]
            exact htmem n
          have hlim := markedPairWeak_closedSegment_limit_left
            F h q htt E L T hraw
          change Rel (hmSegment M t ⟦E⟧ ⟦L⟧) ⟦T⟧
          rw [← markedClosedSegment_quotient_eq_hmSegment]
          exact (markedTerminalMixtureRel_mk F h q hq
            (markedClosedSegmentExperiment t E L) T).2 hlim
        have hlowerClosed : IsClosed lower := by
          apply IsSeqClosed.isClosed
          intro tseq t htmem htt
          have hraw : ∀ n,
              MarkedPairWeak F q T q
                (markedClosedSegmentExperiment (tseq n) E L) := by
            intro n
            apply (markedTerminalMixtureRel_mk F h q hq T
              (markedClosedSegmentExperiment (tseq n) E L)).1
            rw [markedClosedSegment_quotient_eq_hmSegment]
            exact htmem n
          have hlim := markedPairWeak_closedSegment_limit_right
            F h q htt T E L hraw
          change Rel ⟦T⟧ (hmSegment M t ⟦E⟧ ⟦L⟧)
          rw [← markedClosedSegment_quotient_eq_hmSegment]
          exact (markedTerminalMixtureRel_mk F h q hq T
            (markedClosedSegmentExperiment t E L)).2 hlim
        have honeUpper : hmUnitOne ∈ upper := by
          simpa [upper, M, Rel] using hhigh
        have hzeroLower : hmUnitZero ∈ lower := by
          simpa [lower, M, Rel] using hlow
        by_contra hinter
        have hdisjoint : upper ∩ lower = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hinter ⟨t, ht.2, ht.1⟩
        have hcover :
            (Set.univ : Set HMUnitInterval) ⊆ upperᶜ ∪ lowerᶜ := by
          intro t _ht
          by_cases hu : t ∈ upper
          · right
            intro hl
            have : t ∈ upper ∩ lower := ⟨hu, hl⟩
            rw [hdisjoint] at this
            exact this
          · exact Or.inl hu
        have hleftNonempty :
            ((Set.univ : Set HMUnitInterval) ∩ upperᶜ).Nonempty := by
          refine ⟨hmUnitZero, Set.mem_univ _, ?_⟩
          intro hzUpper
          have : hmUnitZero ∈ upper ∩ lower := ⟨hzUpper, hzeroLower⟩
          rw [hdisjoint] at this
          exact this
        have hrightNonempty :
            ((Set.univ : Set HMUnitInterval) ∩ lowerᶜ).Nonempty := by
          refine ⟨hmUnitOne, Set.mem_univ _, ?_⟩
          intro hoLower
          have : hmUnitOne ∈ upper ∩ lower := ⟨honeUpper, hoLower⟩
          rw [hdisjoint] at this
          exact this
        have hboth :=
          isPreconnected_univ upperᶜ lowerᶜ
            hupperClosed.isOpen_compl hlowerClosed.isOpen_compl
            hcover hleftNonempty hrightNonempty
        rcases hboth with ⟨t, _htuniv, hnotUpper, hnotLower⟩
        rcases markedTerminalMixtureRel_complete F h q hq
            (hmSegment M t ⟦E⟧ ⟦L⟧) ⟦T⟧ with hST | hTS
        · exact hnotUpper hST
        · exact hnotLower hTS

/-! ## Generic Herstein--Milnor and the exposed affine utility -/

/-- The fixed-prior marked-law order supplies exactly the hypotheses consumed
by the generic Herstein--Milnor theorem. -/
theorem markedTerminalHMCalibratableWeakOrder
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    HMCalibratableWeakOrder
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq) where
  complete := markedTerminalMixtureRel_complete F h q hq
  transitive := markedTerminalMixtureRel_transitive F h q hq
  independence := markedTerminalMixtureRel_independence F h q hq
  segment_calibration :=
    markedTerminalMixtureRel_segment_calibration F h q hq

/-- The affine utility representation on the quotient of attainable marked
terminal laws. -/
noncomputable def markedTerminalAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq) :=
  Classical.choice
    (genericHersteinMilnorAffineUtility_of_calibratable
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq)
      (markedTerminalHMCalibratableWeakOrder F h q hq))

/-- Representation specialized to quotient constructors. -/
theorem markedTerminalAffineUtility_represents_mk
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    MarkedPairWeak F q E q G ↔
      (markedTerminalAffineUtilityRepresentation F h q hq).utility
          (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ≥
        (markedTerminalAffineUtilityRepresentation F h q hq).utility
          (⟦G⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) := by
  rw [← markedTerminalMixtureRel_mk F h q hq E G]
  exact (markedTerminalAffineUtilityRepresentation F h q hq).represents _ _

/-- Affinity specialized to quotient constructors and the concrete public
mixture representative. -/
theorem markedTerminalAffineUtility_affine_mk
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (t : Set.Ioo (0 : ℝ) 1) (E R : MarkedTerminalExperiment O A) :
    (markedTerminalAffineUtilityRepresentation F h q hq).utility
        (⟦markedPublicMixExperiment t.1 t.2.1 t.2.2 E R⟧ :
          MarkedTerminalMixtureSpace (O := O) (A := A) q) =
      t.1 * (markedTerminalAffineUtilityRepresentation F h q hq).utility
          (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) +
        (1 - t.1) *
          (markedTerminalAffineUtilityRepresentation F h q hq).utility
            (⟦R⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) := by
  simpa [markedTerminalAbstractConvexMixtureSpace] using
    (markedTerminalAffineUtilityRepresentation F h q hq).affine t
      (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦R⟧

/-- The same utility evaluated on a raw bundled experiment. -/
noncomputable def markedAffineUtility
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E : MarkedTerminalExperiment O A) : ℝ :=
  (markedTerminalAffineUtilityRepresentation F h q hq).utility
    (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q)

/-- The raw utility depends only on the full marked terminal law. -/
theorem markedAffineUtility_respects_sameMarkedTerminalLaw
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E') :
    markedAffineUtility F h q hq E = markedAffineUtility F h q hq E' := by
  unfold markedAffineUtility
  congr 1
  exact Quotient.sound hsame

/-- The raw utility represents the paper's marked pair comparison. -/
theorem markedAffineUtility_represents
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    MarkedPairWeak F q E q G ↔
      markedAffineUtility F h q hq E ≥ markedAffineUtility F h q hq G := by
  exact markedTerminalAffineUtility_represents_mk F h q hq E G

/-- The raw utility is affine under the concrete public-coin experiment. -/
theorem markedAffineUtility_publicMix
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A) :
    markedAffineUtility F h q hq
        (markedPublicMixExperiment t ht0 ht1 E R) =
      t * markedAffineUtility F h q hq E +
        (1 - t) * markedAffineUtility F h q hq R := by
  let ti : Set.Ioo (0 : ℝ) 1 := ⟨t, ht0, ht1⟩
  exact markedTerminalAffineUtility_affine_mk F h q hq ti E R

end TraceableAgency.Theorem1
