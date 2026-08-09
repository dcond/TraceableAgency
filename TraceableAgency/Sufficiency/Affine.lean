/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Sufficiency.Posterior

/-!
# Direct fixed-prior affine representation

This file proves the paper's direct Herstein--Milnor step.  Primitive A2 is
applied only to the fixed finite block alphabets realizing one chosen closed
public-mixture segment.  Closed upper and lower cuts on `[0,1]` then intersect,
which supplies the exact `segment_calibration` field consumed by
`HMCalibratableWeakOrder`.

Consequently the exported affine representative does not pass through global
posterior-law sequential continuity, and it does not choose a pointwise
posterior integrand.  Its only analytic input is the primitive fixed-alphabet
closed-graph axiom already contained in `TraceAxioms`.
-/

set_option linter.style.header false

namespace TraceableAgency

open Filter Set Topology

universe u

/-! ## Primitive A2 closes the two segment contours -/

/-- A2 closes the upper contour of a fixed target along the concrete
fixed-alphabet posterior-law segment. -/
theorem posteriorLawHMRel_closedSegment_limit_left
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A)
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (nhds t))
    (E L T : FiniteExperimentOn A)
    (hrel : ∀ n,
      posteriorLawHMRel F q
        (posteriorClosedSegmentExperiment (tseq n) E L) T) :
    posteriorLawHMRel F q (posteriorClosedSegmentExperiment t E L) T := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype L.OutcomeType := L.outFintype
  letI : DecidableEq L.OutcomeType := L.outDecEq
  letI : Fintype T.OutcomeType := T.outFintype
  letI : DecidableEq T.OutcomeType := T.outDecEq
  let Kseq := fun n => blockExperimentChannel
    (posteriorClosedSegmentExperiment (tseq n) E L) T
  let K := blockExperimentChannel (posteriorClosedSegmentExperiment t E L) T
  have hK : ChannelConverges Kseq K := by
    intro a z
    rcases a with a | a
    · rcases z with (e | l) | y
      · simpa [Kseq, K, blockExperimentChannel, blockChannel] using
          posteriorClosedSegment_channelConverges ht E L a (Sum.inl e)
      · simpa [Kseq, K, blockExperimentChannel, blockChannel] using
          posteriorClosedSegment_channelConverges ht E L a (Sum.inr l)
      · exact tendsto_const_nhds
    · rcases z with (e | l) | y <;> exact tendsto_const_nhds
  have hleft : DistConverges
      (fun _ => (inlDist q : Dist (A ⊕ A))) (inlDist q) := by
    intro a
    exact tendsto_const_nhds
  have hright : DistConverges
      (fun _ => (inrDist q : Dist (A ⊕ A))) (inrDist q) := by
    intro a
    exact tendsto_const_nhds
  change F.rel K (inlDist q) (inrDist q)
  exact hax.a2 Kseq K
    (fun _ => inlDist q) (fun _ => inrDist q)
    (inlDist q) (inrDist q)
    hK hleft hright (by
      intro n
      change F.rel (Kseq n) (inlDist q) (inrDist q)
      simpa [Kseq, posteriorLawHMRel, ExperimentPairPref] using hrel n)

/-- A2 closes the lower contour of a fixed target along the same concrete
segment. -/
theorem posteriorLawHMRel_closedSegment_limit_right
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A)
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (nhds t))
    (T E L : FiniteExperimentOn A)
    (hrel : ∀ n,
      posteriorLawHMRel F q T
        (posteriorClosedSegmentExperiment (tseq n) E L)) :
    posteriorLawHMRel F q T (posteriorClosedSegmentExperiment t E L) := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype L.OutcomeType := L.outFintype
  letI : DecidableEq L.OutcomeType := L.outDecEq
  letI : Fintype T.OutcomeType := T.outFintype
  letI : DecidableEq T.OutcomeType := T.outDecEq
  let Kseq := fun n => blockExperimentChannel T
    (posteriorClosedSegmentExperiment (tseq n) E L)
  let K := blockExperimentChannel T (posteriorClosedSegmentExperiment t E L)
  have hK : ChannelConverges Kseq K := by
    intro a z
    rcases a with a | a
    · rcases z with y | (e | l) <;> exact tendsto_const_nhds
    · rcases z with y | (e | l)
      · exact tendsto_const_nhds
      · simpa [Kseq, K, blockExperimentChannel, blockChannel] using
          posteriorClosedSegment_channelConverges ht E L a (Sum.inl e)
      · simpa [Kseq, K, blockExperimentChannel, blockChannel] using
          posteriorClosedSegment_channelConverges ht E L a (Sum.inr l)
  have hleft : DistConverges
      (fun _ => (inlDist q : Dist (A ⊕ A))) (inlDist q) := by
    intro a
    exact tendsto_const_nhds
  have hright : DistConverges
      (fun _ => (inrDist q : Dist (A ⊕ A))) (inrDist q) := by
    intro a
    exact tendsto_const_nhds
  change F.rel K (inlDist q) (inrDist q)
  exact hax.a2 Kseq K
    (fun _ => inlDist q) (fun _ => inrDist q)
    (inlDist q) (inrDist q)
    hK hleft hright (by
      intro n
      change F.rel (Kseq n) (inlDist q) (inrDist q)
      simpa [Kseq, posteriorLawHMRel, ExperimentPairPref] using hrel n)

/-! ## Direct segment calibration -/

/-- Every ordered triple on the fixed-prior quotient has an indifferent point
on its closed anchor segment.  This is precisely the segment-continuity form of
Herstein--Milnor used in the paper. -/
theorem directPosteriorLawMixtureRel_segment_calibration
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (high target low : PosteriorLawMixtureSpace q)
    (hhigh : directPosteriorLawMixtureRel F hpls q hq high target)
    (hlow : directPosteriorLawMixtureRel F hpls q hq target low) :
    ∃ t : HMUnitInterval,
      HMIndiff (directPosteriorLawMixtureRel F hpls q hq) target
        (hmSegment (posteriorLawAbstractConvexMixtureSpace q)
          t high low) := by
  induction high using Quotient.inductionOn with
  | _ E =>
    induction target using Quotient.inductionOn with
    | _ T =>
      induction low using Quotient.inductionOn with
      | _ L =>
        let M := posteriorLawAbstractConvexMixtureSpace q
        let Rel := directPosteriorLawMixtureRel F hpls q hq
        let upper : Set HMUnitInterval :=
          {t | Rel (hmSegment M t
            (⟦E⟧ : PosteriorLawMixtureSpace q) ⟦L⟧) ⟦T⟧}
        let lower : Set HMUnitInterval :=
          {t | Rel ⟦T⟧ (hmSegment M t
            (⟦E⟧ : PosteriorLawMixtureSpace q) ⟦L⟧)}
        have hupperClosed : IsClosed upper := by
          apply IsSeqClosed.isClosed
          intro tseq t htmem htt
          have hraw : ∀ n,
              posteriorLawHMRel F q
                (posteriorClosedSegmentExperiment (tseq n) E L) T := by
            intro n
            apply (directPosteriorLawMixtureRel_mk F hpls q hq
              (posteriorClosedSegmentExperiment (tseq n) E L) T).1
            rw [posteriorClosedSegment_quotient_eq_hmSegment]
            exact htmem n
          have hlim := posteriorLawHMRel_closedSegment_limit_left
            F hax q htt E L T hraw
          change Rel (hmSegment M t ⟦E⟧ ⟦L⟧) ⟦T⟧
          rw [← posteriorClosedSegment_quotient_eq_hmSegment]
          exact (directPosteriorLawMixtureRel_mk F hpls q hq
            (posteriorClosedSegmentExperiment t E L) T).2 hlim
        have hlowerClosed : IsClosed lower := by
          apply IsSeqClosed.isClosed
          intro tseq t htmem htt
          have hraw : ∀ n,
              posteriorLawHMRel F q T
                (posteriorClosedSegmentExperiment (tseq n) E L) := by
            intro n
            apply (directPosteriorLawMixtureRel_mk F hpls q hq T
              (posteriorClosedSegmentExperiment (tseq n) E L)).1
            rw [posteriorClosedSegment_quotient_eq_hmSegment]
            exact htmem n
          have hlim := posteriorLawHMRel_closedSegment_limit_right
            F hax q htt T E L hraw
          change Rel ⟦T⟧ (hmSegment M t ⟦E⟧ ⟦L⟧)
          rw [← posteriorClosedSegment_quotient_eq_hmSegment]
          exact (directPosteriorLawMixtureRel_mk F hpls q hq T
            (posteriorClosedSegmentExperiment t E L)).2 hlim
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
        rcases directPosteriorLawMixtureRel_complete
            F hax hpls q hq (hmSegment M t ⟦E⟧ ⟦L⟧) ⟦T⟧ with hST | hTS
        · exact hnotUpper hST
        · exact hnotLower hTS

/-- The direct posterior-law quotient supplies exactly the minimal order input
used by the generic HM construction. -/
theorem directPosteriorLawHMCalibratableWeakOrder
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    HMCalibratableWeakOrder
      (posteriorLawAbstractConvexMixtureSpace q)
      (directPosteriorLawMixtureRel F hpls q hq) where
  complete := directPosteriorLawMixtureRel_complete F hax hpls q hq
  transitive := directPosteriorLawMixtureRel_transitive F hax hpls q hq
  independence := directPosteriorLawMixtureRel_independence F hax hpls q hq
  segment_calibration :=
    directPosteriorLawMixtureRel_segment_calibration F hax hpls q hq

/-! ## The selected affine representative -/

/-- The affine utility obtained directly from fixed-segment calibration. -/
noncomputable def directPosteriorLawAffineUtilityRepresentation
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (posteriorLawAbstractConvexMixtureSpace q)
      (directPosteriorLawMixtureRel F hpls q hq) :=
  Classical.choice
    (genericHersteinMilnorAffineUtility_of_calibratable
      (posteriorLawAbstractConvexMixtureSpace q)
      (directPosteriorLawMixtureRel F hpls q hq)
      (directPosteriorLawHMCalibratableWeakOrder F hax hpls q hq))

/-- Shift the selected affine utility so that no information has value zero. -/
noncomputable def directNormalizedPosteriorLawAffineUtility
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (x : PosteriorLawMixtureSpace q) : ℝ :=
  let rep := directPosteriorLawAffineUtilityRepresentation F hax hpls q hq
  rep.utility x - rep.utility ⟦uninformativeExperiment A⟧

/-- The direct HM value on experiments.  Boundary priors are temporarily sent
to zero; the separate support-face stage replaces this harmless placeholder. -/
noncomputable def directHMPosteriorValue
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) : ℝ := by
  classical
  exact if hq : q.FullSupport then
    directNormalizedPosteriorLawAffineUtility F hax hpls q hq ⟦E⟧
  else
    0

/-- Paper Stage 1, packaged in the existing downstream HM interface.  Every
field is derived from direct segment calibration; no global posterior-law
continuity theorem is used. -/
noncomputable def finiteHersteinMilnorConclusion_of_directSegment
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F) :
    FiniteHersteinMilnorConclusionFor F hpls where
  V := directHMPosteriorValue F hax hpls
  V_respects_same_posterior_law := by
    intro A _ _ _ q E E' hsame
    classical
    by_cases hq : q.FullSupport
    · simp only [directHMPosteriorValue, hq, dite_true]
      exact congrArg
        (directNormalizedPosteriorLawAffineUtility F hax hpls q hq)
        (Quotient.sound hsame)
    · simp [directHMPosteriorValue, hq]
  V_represents_block_comparisons := by
    intro A _ _ _ q hq E₁ E₂
    classical
    let rep := directPosteriorLawAffineUtilityRepresentation F hax hpls q hq
    have hrep := rep.represents
      (⟦E₁⟧ : PosteriorLawMixtureSpace q) ⟦E₂⟧
    change posteriorLawHMRel F q E₁ E₂ ↔
      directHMPosteriorValue F hax hpls q E₁ ≥
        directHMPosteriorValue F hax hpls q E₂
    simpa [directHMPosteriorValue, hq,
      directNormalizedPosteriorLawAffineUtility, rep] using hrep
  V_affine_of_posteriorLawIntegral_mix := by
    intro A _ _ _ q hq t ht0 ht1 E_mix E₁ E₂ hmix
    classical
    let rep := directPosteriorLawAffineUtilityRepresentation F hax hpls q hq
    let ti : Set.Ioo (0 : ℝ) 1 := ⟨t, ht0, ht1⟩
    have hsame :
        SamePosteriorLawExp q E_mix
          (hmPublicMixExperiment t ht0 ht1 E₁ E₂) := by
      intro phi hphi
      exact (hmix phi hphi).trans
        (hm_posteriorLawIntegral_publicMixExperiment
          q t ht0 ht1 E₁ E₂ phi).symm
    have hquot :
        (⟦E_mix⟧ : PosteriorLawMixtureSpace q) =
          (posteriorLawAbstractConvexMixtureSpace q).mix ti ⟦E₁⟧ ⟦E₂⟧ := by
      exact Quotient.sound hsame
    have haff := rep.affine ti
      (⟦E₁⟧ : PosteriorLawMixtureSpace q) ⟦E₂⟧
    change directHMPosteriorValue F hax hpls q E_mix =
      t * directHMPosteriorValue F hax hpls q E₁ +
        (1 - t) * directHMPosteriorValue F hax hpls q E₂
    simp only [directHMPosteriorValue, hq, dite_true,
      directNormalizedPosteriorLawAffineUtility]
    rw [hquot, haff]
    ring
  V_zero_normalized := by
    intro A _ _ _ q hq
    simp [directHMPosteriorValue, hq,
      directNormalizedPosteriorLawAffineUtility]

/-- Closed Stage-1 constructor from the primitive trace axioms.  Posterior-law
sufficiency is supplied by the proved finite Blackwell matching theorem. -/
noncomputable def finiteHersteinMilnorConclusion_direct_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F) :
    FiniteHersteinMilnorConclusionFor F
      (posteriorLawSufficiency_of_axioms F hax) :=
  finiteHersteinMilnorConclusion_of_directSegment F hax
    (posteriorLawSufficiency_of_axioms F hax)

end TraceableAgency
