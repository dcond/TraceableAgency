/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.GenericHersteinMilnor

/-!
# The posterior-law quotient for the paper-faithful HM route

This file contains the first, preference-specific part of the pure-trace
argument.  At a fixed full-support prior, experiments are quotiented by equality
of their finite posterior laws.  The induced comparison is defined using only
the proved posterior-law replacement theorem.  In particular, none of the
declarations below consumes the stronger global `PosteriorLawContinuity`
interface.

The second half constructs one concrete, fixed-outcome-alphabet realization of
every *closed* segment in the quotient.  This is the realization to which the
primitive fixed-alphabet continuity axiom A2 is applied in `Affine.lean`.
-/

set_option linter.style.header false

namespace TraceableAgency

open Filter Topology

universe u

/-! ## The quotient order -/

/-- The fixed-prior comparison descended directly to the posterior-law
quotient.  Well-definedness uses posterior-law replacement and no continuity
hypothesis. -/
def directPosteriorLawMixtureRel
    (F : PrefFamily.{u}) (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    PosteriorLawMixtureSpace q → PosteriorLawMixtureSpace q → Prop :=
  fun x y =>
    Quotient.liftOn₂ x y
      (posteriorLawHMRel F q)
      (by
        intro E G E' G' hE hG
        exact propext (hpls q hq E G E' G' hE hG))

@[simp]
theorem directPosteriorLawMixtureRel_mk
    (F : PrefFamily.{u}) (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (E G : FiniteExperimentOn A) :
    directPosteriorLawMixtureRel F hpls q hq ⟦E⟧ ⟦G⟧ ↔
      posteriorLawHMRel F q E G := by
  rfl

theorem directPosteriorLawMixtureRel_out
    (F : PrefFamily.{u}) (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (x y : PosteriorLawMixtureSpace q) :
    directPosteriorLawMixtureRel F hpls q hq x y ↔
      posteriorLawHMRel F q x.out y.out := by
  change directPosteriorLawMixtureRel F hpls q hq x y ↔
    directPosteriorLawMixtureRel F hpls q hq ⟦x.out⟧ ⟦y.out⟧
  rw [Quotient.out_eq x, Quotient.out_eq y]

/-- Completeness of the quotient comparison, inherited from A1/A3 through the
proved common-block construction. -/
theorem directPosteriorLawMixtureRel_complete
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (x y : PosteriorLawMixtureSpace q) :
    directPosteriorLawMixtureRel F hpls q hq x y ∨
      directPosteriorLawMixtureRel F hpls q hq y x := by
  rcases posteriorLawHMRel_complete_of_axioms F hax q x.out y.out with hxy | hyx
  · exact Or.inl ((directPosteriorLawMixtureRel_out F hpls q hq x y).2 hxy)
  · exact Or.inr ((directPosteriorLawMixtureRel_out F hpls q hq y x).2 hyx)

/-- Transitivity of the quotient comparison, inherited from the proved
three-block argument. -/
theorem directPosteriorLawMixtureRel_transitive
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (x y z : PosteriorLawMixtureSpace q)
    (hxy : directPosteriorLawMixtureRel F hpls q hq x y)
    (hyz : directPosteriorLawMixtureRel F hpls q hq y z) :
    directPosteriorLawMixtureRel F hpls q hq x z := by
  apply (directPosteriorLawMixtureRel_out F hpls q hq x z).2
  exact posteriorLawHMRel_transitive_of_axioms F hax q x.out y.out z.out
    ((directPosteriorLawMixtureRel_out F hpls q hq x y).1 hxy)
    ((directPosteriorLawMixtureRel_out F hpls q hq y z).1 hyz)

/-- Public-mixture independence on the quotient.  The underlying channel
statement is the already proved consequence of A6 and posterior-law
replacement. -/
theorem directPosteriorLawMixtureRel_independence
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (x y z : PosteriorLawMixtureSpace q)
    (t : Set.Ioo (0 : ℝ) 1) :
    directPosteriorLawMixtureRel F hpls q hq x y ↔
      directPosteriorLawMixtureRel F hpls q hq
        ((posteriorLawAbstractConvexMixtureSpace q).mix t x z)
        ((posteriorLawAbstractConvexMixtureSpace q).mix t y z) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      induction z using Quotient.inductionOn with
      | _ R =>
        simpa [posteriorLawAbstractConvexMixtureSpace,
          directPosteriorLawMixtureRel_mk] using
            posteriorLawHMRel_public_mix_independence_of_axioms
              F hax hpls q hq E G R t.1 t.2.1 t.2.2

/-! ## A single fixed-alphabet realization of a closed segment -/

/-- A publicly tagged mixture of `E` and `L` defined for every coefficient in
the closed unit interval.  Its outcome alphabet is the same
`E.OutcomeType ⊕ L.OutcomeType` at both endpoints and throughout the
segment. -/
noncomputable abbrev posteriorClosedSegmentExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (t : HMUnitInterval) (E L : FiniteExperimentOn A) :
    FiniteExperimentOn A := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype L.OutcomeType := L.outFintype
  letI : DecidableEq L.OutcomeType := L.outDecEq
  exact
    { OutcomeType := E.OutcomeType ⊕ L.OutcomeType
      outFintype := inferInstance
      outDecEq := inferInstance
      channel := fun a =>
        { prob := fun z => match z with
            | Sum.inl e => t.1 * E.P a e
            | Sum.inr l => (1 - t.1) * L.P a l
          nonneg := fun z => by
            rcases z with e | l
            · exact mul_nonneg t.2.1 ((E.P a).nonneg e)
            · exact mul_nonneg (sub_nonneg.mpr t.2.2) ((L.P a).nonneg l)
          sum_eq_one := by
            rw [Fintype.sum_sum_type, ← Finset.mul_sum, ← Finset.mul_sum,
              (E.P a).sum_eq_one, (L.P a).sum_eq_one]
            ring } }

@[simp]
theorem posteriorClosedSegment_channel_inl
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (t : HMUnitInterval) (E L : FiniteExperimentOn A)
    (a : A) (e : E.OutcomeType) :
    (posteriorClosedSegmentExperiment t E L).P a (Sum.inl e) =
      t.1 * E.P a e := by
  classical
  rfl

@[simp]
theorem posteriorClosedSegment_channel_inr
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (t : HMUnitInterval) (E L : FiniteExperimentOn A)
    (a : A) (l : L.OutcomeType) :
    (posteriorClosedSegmentExperiment t E L).P a (Sum.inr l) =
      (1 - t.1) * L.P a l := by
  classical
  rfl

/-- The concrete segment channel varies pointwise continuously in its scalar
coefficient, on one fixed finite outcome alphabet. -/
theorem posteriorClosedSegment_channelConverges
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (nhds t))
    (E L : FiniteExperimentOn A) :
    ∀ a z,
      Tendsto
        (fun n => (posteriorClosedSegmentExperiment (tseq n) E L).P a z)
        atTop (nhds ((posteriorClosedSegmentExperiment t E L).P a z)) := by
  classical
  have hval : Tendsto (fun n => (tseq n).1) atTop (nhds t.1) :=
    (continuous_subtype_val.tendsto t).comp ht
  intro a z
  rcases z with e | l
  · simpa only [posteriorClosedSegment_channel_inl] using
      hval.mul tendsto_const_nhds
  · simpa only [posteriorClosedSegment_channel_inr] using
      (tendsto_const_nhds.sub hval).mul tendsto_const_nhds

/-- Posterior-law integration is affine along the concrete closed segment,
including the zero-mass tagged branch at either endpoint. -/
theorem posteriorLawIntegral_closedSegment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (t : HMUnitInterval)
    (E L : FiniteExperimentOn A) (phi : Dist A → ℝ) :
    posteriorLawIntegralExp q (posteriorClosedSegmentExperiment t E L) phi =
      t.1 * posteriorLawIntegralExp q E phi +
        (1 - t.1) * posteriorLawIntegralExp q L phi := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype L.OutcomeType := L.outFintype
  letI : DecidableEq L.OutcomeType := L.outDecEq
  change posteriorLawIntegral q
      (posteriorClosedSegmentExperiment t E L).P phi =
    t.1 * posteriorLawIntegral q E.P phi +
      (1 - t.1) * posteriorLawIntegral q L.P phi
  by_cases h0 : t.1 = 0
  · have hP : (posteriorClosedSegmentExperiment t E L).P =
        outcomePadRight (O := E.OutcomeType) L.P := by
      funext a
      apply Dist.ext
      intro z
      rcases z with e | l
      · simp [h0, outcomePadRight]
      · simp [h0, outcomePadRight]
    rw [hP, posteriorLawIntegral_outcomePadRight]
    simp [h0]
  · by_cases h1 : t.1 = 1
    · have hP : (posteriorClosedSegmentExperiment t E L).P =
          outcomePadLeft (Y := L.OutcomeType) E.P := by
        funext a
        apply Dist.ext
        intro z
        rcases z with e | l
        · simp [h1, outcomePadLeft]
        · simp [h1, outcomePadLeft]
      rw [hP, posteriorLawIntegral_outcomePadLeft]
      simp [h1]
    · have ht0 : 0 < t.1 := lt_of_le_of_ne t.2.1 (Ne.symm h0)
      have ht1 : t.1 < 1 := lt_of_le_of_ne t.2.2 h1
      have hP : (posteriorClosedSegmentExperiment t E L).P =
          publicMixChannel t.1 ht0 ht1 E.P L.P := by
        funext a
        apply Dist.ext
        intro z
        rcases z with e | l <;> rfl
      rw [hP]
      exact hm_posteriorLawIntegral_publicMixChannel
        q t.1 ht0 ht1 E.P L.P phi

/-- The concrete experiment realizes exactly the generic HM closed segment in
the posterior-law quotient. -/
theorem posteriorClosedSegment_quotient_eq_hmSegment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (t : HMUnitInterval)
    (E L : FiniteExperimentOn A) :
    (⟦posteriorClosedSegmentExperiment t E L⟧ : PosteriorLawMixtureSpace q) =
      hmSegment (posteriorLawAbstractConvexMixtureSpace q) t
        (⟦E⟧ : PosteriorLawMixtureSpace q) ⟦L⟧ := by
  apply (posteriorLawAbstractConvexMixtureSpace q).coordinate_ext
  intro phi
  change posteriorLawIntegralExp q
      (posteriorClosedSegmentExperiment t E L) phi.down.1 = _
  rw [posteriorLawIntegral_closedSegment,
    hmSegment_coordinate]
  rfl

end TraceableAgency
