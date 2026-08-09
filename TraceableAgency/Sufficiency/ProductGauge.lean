/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.EntropyReduction

/-!
# Product normalization before branch scales

This file isolates the product argument at the level at which it appears in
the paper.  Its primitive cardinal object is a bare
`PosteriorValueRepresentation`; no branch coefficient, chain scale, face
scale, or entropy-reduction structure occurs in the exported interfaces.

For full-support, nondegenerate factors the argument has four parts.

1. Derived background inertness identifies each product slice with the base
   weak order.
2. Posterior-law affinity and finite affine-utility uniqueness make every
   slice a positive affine transform of the corresponding base value.
3. Product swap and the two intercept normalizations give the pairwise
   bilinear formula.
4. A positive prior gauge transports the three coefficients by the usual
   coboundary formulas.  After normalizing the two linear coefficients,
   product associativity identifies a common interaction coefficient.

Singleton factors are deliberately kept outside the coefficient-identification
statements: their posterior value is identically zero, so an interaction
coefficient is not identified there.  Downstream formulas may discharge those
cases by the existing singleton-value-zero theorem.
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-! ## Bare product values and structural affinity -/

/-- Exact relabeling coherence of one selected posterior-value
representative.  Unlike `FinitePosteriorValueRelabelingAssumptions`, this
does not quantify over every possible representative. -/
structure PosteriorValueRelabeling
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F) : Prop where
  V_relabel_eq :
    ∀ {A B O Y : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (eA : A ≃ B) (eO : O ≃ Y)
      (q : Dist A) (P : Channel A O),
      hV.V (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        hV.V q (experimentOfChannel P)

/-- A coherent prior gauge preserves exact relabeling of the selected
representative. -/
theorem posteriorValueRelabeling_positiveGaugeTransform
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    PosteriorValueRelabeling
      (posteriorValueRepresentation_positiveGaugeTransform
        hV hgauge.toPositive) where
  V_relabel_eq := by
    intro A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    dsimp [posteriorValueRepresentation_positiveGaugeTransform,
      CoherentFaceScaleGauge.toPositive]
    rw [hgauge.gauge_relabel_eq eA q]
    rw [hrelV.V_relabel_eq eA eO q P]

/-- Drop a subsingleton right coordinate. -/
noncomputable def posteriorProductDropRightEquiv
    (A B : Type u) [Nonempty B] [Subsingleton B] : A × B ≃ A where
  toFun x := x.1
  invFun a := (a, Classical.choice (inferInstance : Nonempty B))
  left_inv x := by
    apply Prod.ext
    · rfl
    · exact Subsingleton.elim _ _
  right_inv _ := rfl

theorem posteriorProduct_relabelDist_dropRight
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    (q : Dist A) (r : Dist B) :
    Relabeling.relabelDist (posteriorProductDropRightEquiv A B)
        (prodDist q r) = q := by
  classical
  let b₀ : B := Classical.choice (inferInstance : Nonempty B)
  have hr : r = Dist.pure b₀ := Dist.eq_of_subsingleton _ _
  rw [hr]
  ext a
  simp [Relabeling.relabelDist_apply, posteriorProductDropRightEquiv,
    prodDist_apply_pair, b₀]

theorem posteriorProduct_relabelChannel_dropRight
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) :
    Relabeling.relabelChannel
        (posteriorProductDropRightEquiv A B)
        (posteriorProductDropRightEquiv O PUnit.{u + 1})
        (prodChannel P (Channel.uninformativeChannelU B)) = P := by
  classical
  ext a o
  simp [Relabeling.relabelChannel, posteriorProductDropRightEquiv,
    prodChannel_apply_pair, Channel.uninformativeChannelU]

/-- Value of an independent product experiment for a bare posterior-value
representative. -/
noncomputable def posteriorProductValue
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) : ℝ :=
  hV.V (prodDist q r) (experimentOfChannel (prodChannel P R))

/-- A subsingleton right factor contributes zero information, and exact
selected-value relabeling identifies the product scale with the left scale. -/
theorem posteriorProductValue_eq_left_of_subsingleton_right
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) :
    posteriorProductValue hV q r P R =
      hV.V q (experimentOfChannel P) := by
  have hconst :
      posteriorProductValue hV q r P R =
        posteriorProductValue hV q r P
          (Channel.uninformativeChannelU B) :=
    hV.respects_same_posterior_law (prodDist q r) _ _
      (samePosteriorLawExp_prodChannel_singleton_snd q r P R)
  have hcov := hrelV.V_relabel_eq
    (posteriorProductDropRightEquiv A B)
    (posteriorProductDropRightEquiv O PUnit.{u + 1})
    (prodDist q r)
    (prodChannel P (Channel.uninformativeChannelU B))
  rw [posteriorProduct_relabelDist_dropRight q r,
    posteriorProduct_relabelChannel_dropRight P] at hcov
  exact hconst.trans hcov.symm

/-- Public mixing is affine for the selected bare posterior representative. -/
theorem posteriorValue_publicMix_affine
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A O Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Z) :
    hV.V q (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
      t * hV.V q (experimentOfChannel P) +
        (1 - t) * hV.V q (experimentOfChannel Q) := by
  exact hV.affine_of_posteriorLawIntegral_mix
    q t ht0 ht1
    (experimentOfChannel (publicMixChannel t ht0 ht1 P Q))
    (experimentOfChannel P) (experimentOfChannel Q)
    (by
      intro phi _hphi
      exact hm_posteriorLawIntegral_publicMixExperiment
        q t ht0 ht1 (experimentOfChannel P) (experimentOfChannel Q) phi)

/-- A first-coordinate product slice is affine under public mixing. -/
theorem posteriorProductValue_publicMix_left
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A B O Z Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Z) :
    posteriorProductValue hV q r
        (publicMixChannel t ht0 ht1 P Q) R =
      t * posteriorProductValue hV q r P R +
        (1 - t) * posteriorProductValue hV q r Q R := by
  have hsame :=
    samePosteriorLaw_prod_publicMix_left_of_postprocess
      q r R t ht0 ht1 P Q
  have hvalue := hV.respects_same_posterior_law
    (prodDist q r)
    (experimentOfChannel
      (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
    (experimentOfChannel
      (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R)))
    hsame
  calc
    posteriorProductValue hV q r (publicMixChannel t ht0 ht1 P Q) R =
        hV.V (prodDist q r)
          (experimentOfChannel
            (publicMixChannel t ht0 ht1 (prodChannel P R)
              (prodChannel Q R))) := by
          simpa [posteriorProductValue] using hvalue
    _ = t * hV.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) +
        (1 - t) * hV.V (prodDist q r)
          (experimentOfChannel (prodChannel Q R)) :=
      posteriorValue_publicMix_affine hV (prodDist q r)
        t ht0 ht1 (prodChannel P R) (prodChannel Q R)
    _ = t * posteriorProductValue hV q r P R +
        (1 - t) * posteriorProductValue hV q r Q R := rfl

/-- A second-coordinate product slice is affine under public mixing. -/
theorem posteriorProductValue_publicMix_right
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A B O Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (P : Channel A O)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    posteriorProductValue hV q r P
        (publicMixChannel t ht0 ht1 R S) =
      t * posteriorProductValue hV q r P R +
        (1 - t) * posteriorProductValue hV q r P S := by
  have hsame :=
    samePosteriorLaw_prod_publicMix_right_of_postprocess
      q r P t ht0 ht1 R S
  have hvalue := hV.respects_same_posterior_law
    (prodDist q r)
    (experimentOfChannel
      (prodChannel P (publicMixChannel t ht0 ht1 R S)))
    (experimentOfChannel
      (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S)))
    hsame
  calc
    posteriorProductValue hV q r P (publicMixChannel t ht0 ht1 R S) =
        hV.V (prodDist q r)
          (experimentOfChannel
            (publicMixChannel t ht0 ht1 (prodChannel P R)
              (prodChannel P S))) := by
          simpa [posteriorProductValue] using hvalue
    _ = t * hV.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) +
        (1 - t) * hV.V (prodDist q r)
          (experimentOfChannel (prodChannel P S)) :=
      posteriorValue_publicMix_affine hV (prodDist q r)
        t ht0 ht1 (prodChannel P R) (prodChannel P S)
    _ = t * posteriorProductValue hV q r P R +
        (1 - t) * posteriorProductValue hV q r P S := rfl

/-! ## Background cancellation at the ordinal level -/

/-- Derived background inertness cancels a common independent right
background from product-value comparisons. -/
theorem posteriorProductValue_left_order_iff
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) (P Q : Channel A O) :
    posteriorProductValue hV q r P R ≥
        posteriorProductValue hV q r Q R ↔
      hV.V q (experimentOfChannel P) ≥
        hV.V q (experimentOfChannel Q) := by
  have hprodSupport : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  have hprod := hV.represents_block_comparisons
    (prodDist q r) hprodSupport
    (experimentOfChannel (prodChannel P R))
    (experimentOfChannel (prodChannel Q R))
  have hbase := hV.represents_block_comparisons
    q hq (experimentOfChannel P) (experimentOfChannel Q)
  change
    F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      posteriorProductValue hV q r P R ≥
        posteriorProductValue hV q r Q R at hprod
  change
    F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hV.V q (experimentOfChannel P) ≥
        hV.V q (experimentOfChannel Q) at hbase
  exact hprod.symm.trans
    ((derived_background_inertness_left F hax q r P Q R).trans hbase)

/-- Coordinate-swapped background cancellation. -/
theorem posteriorProductValue_right_order_iff
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R S : Channel B Y) :
    posteriorProductValue hV q r P R ≥
        posteriorProductValue hV q r P S ↔
      hV.V r (experimentOfChannel R) ≥
        hV.V r (experimentOfChannel S) := by
  have hprodSupport : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  have hprod := hV.represents_block_comparisons
    (prodDist q r) hprodSupport
    (experimentOfChannel (prodChannel P R))
    (experimentOfChannel (prodChannel P S))
  have hbase := hV.represents_block_comparisons
    r hr (experimentOfChannel R) (experimentOfChannel S)
  change
    F.rel (blockChannel (prodChannel P R) (prodChannel P S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      posteriorProductValue hV q r P R ≥
        posteriorProductValue hV q r P S at hprod
  change
    F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hV.V r (experimentOfChannel R) ≥
        hV.V r (experimentOfChannel S) at hbase
  exact hprod.symm.trans
    ((derived_background_inertness_right F hax q r P R S).trans hbase)

/-- A1 makes the full-revelation and no-information anchors distinct for the
bare representative. -/
theorem posteriorValue_id_ne_uninformative_of_A1
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
      hV.V q
        (experimentOfChannel (Channel.uninformativeChannelU A)) := by
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
  exact branch_value_ne_of_strict_experiment_pref
    F hV q hq
    (experimentOfChannel (Channel.idChannel : Channel A A))
    (experimentOfChannel (Channel.uninformativeChannelU A))
    hstrict.1 hstrict.2

/-- In particular the full-revelation anchor is nonzero under the selected
zero normalization. -/
theorem posteriorValue_id_ne_zero_of_A1
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
  have hne := posteriorValue_id_ne_uninformative_of_A1 hax hV q hq hA
  rw [hV.zero_normalized q hq] at hne
  exact hne

/-- Zero normalization orients the A1 comparison: full revelation has
strictly positive posterior value on every nondegenerate full-support prior. -/
theorem posteriorValue_id_pos_of_A1
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    0 < hV.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) := by
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
  have hge :=
    (hV.represents_block_comparisons q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))).mp hstrict.1
  have hnrev : ¬
      hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) ≥
        hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) := by
    intro h
    exact hstrict.2
      ((hV.represents_block_comparisons q hq
        (experimentOfChannel (Channel.uninformativeChannelU A))
        (experimentOfChannel (Channel.idChannel : Channel A A))).mpr h)
  rw [hV.zero_normalized q hq] at hge hnrev
  linarith

/-! ## Positive affine product slices -/

/-- Chosen positive affine coefficients for nondegenerate first-coordinate
product slices.  This is the direct output of finite affine-utility
uniqueness, before any branch scale has been introduced. -/
structure PosteriorProductLeftSliceAffine
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F) where
  leftSlope :
    TraceAxioms F →
      {A B Y : Type u} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftIntercept :
    TraceAxioms F →
      {A B Y : Type u} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftSlope_pos :
    ∀ (hax : TraceAxioms F)
      {A B Y : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A) (R : Channel B Y),
      0 < leftSlope hax q r R
  left_slice_affine :
    ∀ (hax : TraceAxioms F)
      {A B O Y : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A)
      (P : Channel A O) (R : Channel B Y),
      posteriorProductValue hV q r P R =
        leftSlope hax q r R * hV.V q (experimentOfChannel P) +
          leftIntercept hax q r R

/-- Existence of the positive affine transform for one fixed nondegenerate
slice. -/
theorem exists_posteriorProduct_leftSlice_positiveAffine
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (R : Channel B Y) :
    ∃ a b : ℝ, 0 < a ∧
      ∀ {O : Type u} [Fintype O] [DecidableEq O]
        (P : Channel A O),
        posteriorProductValue hV q r P R =
          a * hV.V q (experimentOfChannel P) + b := by
  let base :
      {O : Type u} → [Fintype O] → [DecidableEq O] →
        Channel A O → ℝ :=
    fun {O} [Fintype O] [DecidableEq O] P =>
      hV.V q (experimentOfChannel P)
  let target :
      {O : Type u} → [Fintype O] → [DecidableEq O] →
        Channel A O → ℝ :=
    fun {O} [Fintype O] [DecidableEq O] P =>
      posteriorProductValue hV q r P R
  obtain ⟨a, b, ha, hab⟩ :=
    classicalFiniteAffineUtilityUniquenessAssumptions.positive_affine_transform
      base target
      (by
        intro O Z _ _ _ _ t ht0 ht1 P Q
        exact posteriorValue_publicMix_affine hV q t ht0 ht1 P Q)
      (by
        intro O Z _ _ _ _ t ht0 ht1 P Q
        exact posteriorProductValue_publicMix_left
          hV q r R t ht0 ht1 P Q)
      (posteriorValue_id_ne_uninformative_of_A1 hax hV q hq hA)
      (by
        intro O _ _ P Q
        exact posteriorProductValue_left_order_iff
          hax hV q r hq hr R P Q)
  exact ⟨a, b, ha, by
    intro O _ _ P
    exact hab P⟩

/-- Select the paper's slice coefficients from the preceding uniqueness
theorem.  Values outside the full-support nondegenerate domain are harmless
defaults and are never used by the specification fields. -/
noncomputable def posteriorProductLeftSliceAffine_of_axioms
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F) :
    PosteriorProductLeftSliceAffine hV where
  leftSlope := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r R
    classical
    exact if h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A then
      Classical.choose
        (exists_posteriorProduct_leftSlice_positiveAffine
          hax hV q r h.1 h.2.1 h.2.2 R)
    else 1
  leftIntercept := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r R
    classical
    exact if h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A then
      Classical.choose (Classical.choose_spec
        (exists_posteriorProduct_leftSlice_positiveAffine
          hax hV q r h.1 h.2.1 h.2.2 R))
    else 0
  leftSlope_pos := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr hA R
    classical
    have hcond : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A :=
      ⟨hq, hr, hA⟩
    have hpos :=
      (Classical.choose_spec
        (Classical.choose_spec
          (exists_posteriorProduct_leftSlice_positiveAffine
            hax hV q r hq hr hA R))).1
    simpa [hcond] using hpos
  left_slice_affine := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr hA P R
    classical
    have hcond : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A :=
      ⟨hq, hr, hA⟩
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (exists_posteriorProduct_leftSlice_positiveAffine
            hax hV q r hq hr hA R))).2 (P := P)
    simpa [hcond] using hspec

/-! ## Intercept normalization and pairwise bilinearity -/

/-- The slice intercept is the product value when the first coordinate is
uninformative. -/
theorem posteriorProduct_leftIntercept_eq_noInfo
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hslice : PosteriorProductLeftSliceAffine hV)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (R : Channel B Y) :
    hslice.leftIntercept hax q r R =
      posteriorProductValue hV q r (Channel.uninformativeChannelU A) R := by
  have h := hslice.left_slice_affine hax q r hq hr hA
    (Channel.uninformativeChannelU A) R
  rw [hV.zero_normalized q hq, mul_zero, zero_add] at h
  exact h.symm

/-- The intercept at a no-information second coordinate is zero. -/
theorem posteriorProduct_leftIntercept_uninformative_eq_zero
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hslice : PosteriorProductLeftSliceAffine hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) :
    hslice.leftIntercept hax q r (Channel.uninformativeChannelU B) = 0 := by
  rw [posteriorProduct_leftIntercept_eq_noInfo
    hslice hax q r hq hr hA (Channel.uninformativeChannelU B)]
  exact V_eq_zero_of_subsingleton_outcome F hV
    (prodDist q r) (prodDist_fullSupport q r hq hr)
    (prodChannel (Channel.uninformativeChannelU A)
      (Channel.uninformativeChannelU B))

/-- The intercept is public-mixture affine in the second coordinate. -/
theorem posteriorProduct_leftIntercept_publicMix
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hslice : PosteriorProductLeftSliceAffine hV)
    (hax : TraceAxioms F)
    {A B Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    hslice.leftIntercept hax q r (publicMixChannel t ht0 ht1 R S) =
      t * hslice.leftIntercept hax q r R +
        (1 - t) * hslice.leftIntercept hax q r S := by
  rw [posteriorProduct_leftIntercept_eq_noInfo
    hslice hax q r hq hr hA (publicMixChannel t ht0 ht1 R S)]
  rw [posteriorProduct_leftIntercept_eq_noInfo
    hslice hax q r hq hr hA R]
  rw [posteriorProduct_leftIntercept_eq_noInfo
    hslice hax q r hq hr hA S]
  exact posteriorProductValue_publicMix_right hV q r
    (Channel.uninformativeChannelU A) t ht0 ht1 R S

/-- The intercept represents the base second-coordinate weak order. -/
theorem posteriorProduct_leftIntercept_order_iff
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hslice : PosteriorProductLeftSliceAffine hV)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (R S : Channel B Y) :
    hslice.leftIntercept hax q r R ≥ hslice.leftIntercept hax q r S ↔
      hV.V r (experimentOfChannel R) ≥
        hV.V r (experimentOfChannel S) := by
  rw [posteriorProduct_leftIntercept_eq_noInfo
    hslice hax q r hq hr hA R]
  rw [posteriorProduct_leftIntercept_eq_noInfo
    hslice hax q r hq hr hA S]
  exact posteriorProductValue_right_order_iff hax hV q r hq hr
    (Channel.uninformativeChannelU A) R S

/-- The intercept is a positive linear multiple of the second-coordinate
posterior value. -/
theorem exists_posteriorProduct_leftIntercept_positiveLinear
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hslice : PosteriorProductLeftSliceAffine hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    ∃ b : ℝ, 0 < b ∧
      ∀ {Y : Type u} [Fintype Y] [DecidableEq Y]
        (R : Channel B Y),
        hslice.leftIntercept hax q r R =
          b * hV.V r (experimentOfChannel R) := by
  let base :
      {Y : Type u} → [Fintype Y] → [DecidableEq Y] →
        Channel B Y → ℝ :=
    fun {Y} [Fintype Y] [DecidableEq Y] R =>
      hV.V r (experimentOfChannel R)
  let target :
      {Y : Type u} → [Fintype Y] → [DecidableEq Y] →
        Channel B Y → ℝ :=
    fun {Y} [Fintype Y] [DecidableEq Y] R =>
      hslice.leftIntercept hax q r R
  obtain ⟨b, c, hb, hbc⟩ :=
    classicalFiniteAffineUtilityUniquenessAssumptions.positive_affine_transform
      base target
      (by
        intro Y Z _ _ _ _ t ht0 ht1 R S
        exact posteriorValue_publicMix_affine hV r t ht0 ht1 R S)
      (by
        intro Y Z _ _ _ _ t ht0 ht1 R S
        exact posteriorProduct_leftIntercept_publicMix
          hslice hax q r hq hr hA t ht0 ht1 R S)
      (posteriorValue_id_ne_uninformative_of_A1 hax hV r hr hB)
      (by
        intro Y _ _ R S
        exact posteriorProduct_leftIntercept_order_iff
          hslice hax q r hq hr hA R S)
  have hc : c = 0 := by
    have hzero := hbc (Channel.uninformativeChannelU B)
    dsimp [base, target] at hzero
    rw [hV.zero_normalized r hr, mul_zero, zero_add] at hzero
    rw [posteriorProduct_leftIntercept_uninformative_eq_zero
      hslice hax q r hq hr hA] at hzero
    exact hzero.symm
  refine ⟨b, hb, ?_⟩
  intro Y _ _ R
  have h := hbc R
  rw [hc, add_zero] at h
  exact h

/-- Product values commute with swapping the two independent coordinates,
assuming only exact relabeling coherence of the selected posterior values. -/
theorem posteriorProductValue_swap
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV) (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) :
    posteriorProductValue hV q r P R =
      posteriorProductValue hV r q R P := by
  have hrel := hrelV.V_relabel_eq
    (Equiv.prodComm A B) (Equiv.prodComm O Y)
    (prodDist q r) (prodChannel P R)
  have hrel' :
      posteriorProductValue hV r q R P =
        posteriorProductValue hV q r P R := by
    simpa [posteriorProductValue, relabelDist_prodComm q r,
      relabelChannel_prodComm P R] using hrel
  exact hrel'.symm

/-- Symmetric singleton collapse for the left coordinate. -/
theorem posteriorProductValue_eq_right_of_subsingleton_left
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV) (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) :
    posteriorProductValue hV q r P R =
      hV.V r (experimentOfChannel R) := by
  calc
    posteriorProductValue hV q r P R =
        posteriorProductValue hV r q R P :=
      posteriorProductValue_swap hrelV hax q r P R
    _ = hV.V r (experimentOfChannel R) :=
      posteriorProductValue_eq_left_of_subsingleton_right
        hrelV r q R P

/-- Paper-style pairwise bilinearity for two nondegenerate full-support
factors.  Both linear coefficients are strictly positive. -/
theorem exists_posteriorProduct_pairwiseBilinear
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV) (hax : TraceAxioms F)
    (hslice : PosteriorProductLeftSliceAffine hV)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧
      ∀ {O Y : Type u}
        [Fintype O] [DecidableEq O]
        [Fintype Y] [DecidableEq Y]
        (P : Channel A O) (R : Channel B Y),
        posteriorProductValue hV q r P R =
          a * hV.V q (experimentOfChannel P) +
          b * hV.V r (experimentOfChannel R) +
          c * hV.V q (experimentOfChannel P) *
            hV.V r (experimentOfChannel R) := by
  classical
  obtain ⟨b, hb, hb_spec⟩ :=
    exists_posteriorProduct_leftIntercept_positiveLinear
      hslice hax q r hq hr hA hB
  obtain ⟨a, ha, ha_spec⟩ :=
    exists_posteriorProduct_leftIntercept_positiveLinear
      hslice hax r q hr hq hB hA
  let Hq : ℝ :=
    hV.V q (experimentOfChannel (Channel.idChannel : Channel A A))
  have hHq : Hq ≠ 0 := by
    simpa [Hq] using posteriorValue_id_ne_zero_of_A1 hax hV q hq hA
  let c : ℝ :=
    (hslice.leftSlope hax r q (Channel.idChannel : Channel A A) - b) / Hq
  have hslope :
      ∀ {Y : Type u} [Fintype Y] [DecidableEq Y]
        (R : Channel B Y),
        hslice.leftSlope hax q r R =
          a + c * hV.V r (experimentOfChannel R) := by
    intro Y _ _ R
    have h1 := hslice.left_slice_affine hax q r hq hr hA
      (Channel.idChannel : Channel A A) R
    have h2 := posteriorProductValue_swap hrelV hax
      q r (Channel.idChannel : Channel A A) R
    have h3 := hslice.left_slice_affine hax r q hr hq hB
      R (Channel.idChannel : Channel A A)
    have hIqr := hb_spec R
    have hIrq := ha_spec (Channel.idChannel : Channel A A)
    have hkey :
        hslice.leftSlope hax q r R * Hq =
          hslice.leftSlope hax r q (Channel.idChannel : Channel A A) *
              hV.V r (experimentOfChannel R) +
            a * Hq - b * hV.V r (experimentOfChannel R) := by
      have hchain := h1.symm.trans (h2.trans h3)
      rw [hIqr, hIrq] at hchain
      dsimp [Hq] at hchain ⊢
      linarith [hchain]
    dsimp [c]
    field_simp [hHq]
    linear_combination hkey
  refine ⟨a, b, c, ha, hb, ?_⟩
  intro O Y _ _ _ _ P R
  rw [hslice.left_slice_affine hax q r hq hr hA P R]
  rw [hslope R, hb_spec R]
  ring

/-- Predicate saying that a triple is a valid nondegenerate product
coefficient triple at `(q,r)`.  Keeping the witness in one product type makes
the global classical selection below transparent. -/
def PosteriorProductCoefficientsValid
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (coeff : ℝ × ℝ × ℝ) : Prop :=
  0 < coeff.1 ∧ 0 < coeff.2.1 ∧
    ∀ {O Y : Type u}
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (P : Channel A O) (R : Channel B Y),
      posteriorProductValue hV q r P R =
        coeff.1 * hV.V q (experimentOfChannel P) +
        coeff.2.1 * hV.V r (experimentOfChannel R) +
        coeff.2.2 * hV.V q (experimentOfChannel P) *
          hV.V r (experimentOfChannel R)

/-- Package the pointwise bilinear theorem as a single coefficient triple. -/
theorem exists_posteriorProduct_coefficientsValid
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV) (hax : TraceAxioms F)
    (hslice : PosteriorProductLeftSliceAffine hV)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    ∃ coeff : ℝ × ℝ × ℝ,
      PosteriorProductCoefficientsValid hV q r coeff := by
  obtain ⟨a, b, c, ha, hb, hformula⟩ :=
    exists_posteriorProduct_pairwiseBilinear
      hrelV hax hslice q r hq hr hA hB
  exact ⟨(a, b, c), ha, hb, hformula⟩

/-- Global classical selection of the pointwise coefficient triple.  The
singleton/boundary defaults are explicit and harmless because the exported
coefficient-identification fields use only the full-support nondegenerate
domain. -/
noncomputable def selectedPosteriorProductCoefficients
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hslice : PosteriorProductLeftSliceAffine hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ × ℝ × ℝ := by
  classical
  exact if h : q.FullSupport ∧ r.FullSupport ∧
      ¬ Subsingleton A ∧ ¬ Subsingleton B then
    Classical.choose
      (exists_posteriorProduct_coefficientsValid
        hrelV hax hslice q r h.1 h.2.1 h.2.2.1 h.2.2.2)
  else (1, 1, 0)

theorem selectedPosteriorProductCoefficients_valid
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hslice : PosteriorProductLeftSliceAffine hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    PosteriorProductCoefficientsValid hV q r
      (selectedPosteriorProductCoefficients hrelV hslice hax q r) := by
  classical
  have hcond : q.FullSupport ∧ r.FullSupport ∧
      ¬ Subsingleton A ∧ ¬ Subsingleton B := ⟨hq, hr, hA, hB⟩
  simpa [selectedPosteriorProductCoefficients, hcond] using
    (Classical.choose_spec
      (exists_posteriorProduct_coefficientsValid
        hrelV hax hslice q r hq hr hA hB))

/-! ## Bare coefficient, gauge, and common-interaction interfaces -/

/-- A globally selected nondegenerate pairwise product formula.  This is the
consumer-facing Stage-3 interface; its only cardinal input is `hV`. -/
structure PosteriorProductPairwiseBilinearity
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F) where
  leftCoeff :
    TraceAxioms F →
      {A B : Type u} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff :
    TraceAxioms F →
      {A B : Type u} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    TraceAxioms F →
      {A B : Type u} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A)
      (_hB : ¬ Subsingleton B),
      0 < leftCoeff hax q r
  rightCoeff_pos :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A)
      (_hB : ¬ Subsingleton B),
      0 < rightCoeff hax q r
  product_pair_bilinear :
    ∀ (hax : TraceAxioms F)
      {A B O Y : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A)
      (_hB : ¬ Subsingleton B)
      (P : Channel A O) (R : Channel B Y),
      posteriorProductValue hV q r P R =
        leftCoeff hax q r * hV.V q (experimentOfChannel P) +
        rightCoeff hax q r * hV.V r (experimentOfChannel R) +
        interactionCoeff hax q r * hV.V q (experimentOfChannel P) *
          hV.V r (experimentOfChannel R)

/-- Assemble the globally selected pairwise-bilinearity interface directly
from the bare posterior representative, axioms, and exact relabeling. -/
noncomputable def posteriorProductPairwiseBilinearity_of_axioms
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hslice : PosteriorProductLeftSliceAffine hV) :
    PosteriorProductPairwiseBilinearity hV where
  leftCoeff := fun hax {_ _} _ _ _ _ _ _ q r =>
    (selectedPosteriorProductCoefficients hrelV hslice hax q r).1
  rightCoeff := fun hax {_ _} _ _ _ _ _ _ q r =>
    (selectedPosteriorProductCoefficients hrelV hslice hax q r).2.1
  interactionCoeff := fun hax {_ _} _ _ _ _ _ _ q r =>
    (selectedPosteriorProductCoefficients hrelV hslice hax q r).2.2
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    exact (selectedPosteriorProductCoefficients_valid
      hrelV hslice hax q r hq hr hA hB).1
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    exact (selectedPosteriorProductCoefficients_valid
      hrelV hslice hax q r hq hr hA hB).2.1
  product_pair_bilinear := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr hA hB P R
    exact (selectedPosteriorProductCoefficients_valid
      hrelV hslice hax q r hq hr hA hB).2.2 P R

/-- Left coefficient after multiplying each prior's representative by a
positive gauge. -/
noncomputable def posteriorGaugeTransformedLeftCoeff
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.leftCoeff hax q r *
    (hgauge.gauge (prodDist q r) / hgauge.gauge q)

/-- Right coefficient after a positive prior gauge. -/
noncomputable def posteriorGaugeTransformedRightCoeff
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.rightCoeff hax q r *
    (hgauge.gauge (prodDist q r) / hgauge.gauge r)

/-- Interaction coefficient after a positive prior gauge. -/
noncomputable def posteriorGaugeTransformedInteractionCoeff
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.interactionCoeff hax q r *
    (hgauge.gauge (prodDist q r) /
      (hgauge.gauge q * hgauge.gauge r))

/-- Bare pairwise bilinearity is stable under a positive prior gauge. -/
noncomputable def posteriorProductPairwiseBilinearity_gaugeTransform
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hgauge : PositiveFaceScaleGauge.{u}) :
    PosteriorProductPairwiseBilinearity
      (posteriorValueRepresentation_positiveGaugeTransform hV hgauge) where
  leftCoeff := fun hax {_ _} _ _ _ _ _ _ q r =>
    posteriorGaugeTransformedLeftCoeff hpair hgauge hax q r
  rightCoeff := fun hax {_ _} _ _ _ _ _ _ q r =>
    posteriorGaugeTransformedRightCoeff hpair hgauge hax q r
  interactionCoeff := fun hax {_ _} _ _ _ _ _ _ q r =>
    posteriorGaugeTransformedInteractionCoeff hpair hgauge hax q r
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    exact mul_pos (hpair.leftCoeff_pos hax q r hq hr hA hB)
      (div_pos (hgauge.gauge_pos (prodDist q r)) (hgauge.gauge_pos q))
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    exact mul_pos (hpair.rightCoeff_pos hax q r hq hr hA hB)
      (div_pos (hgauge.gauge_pos (prodDist q r)) (hgauge.gauge_pos r))
  product_pair_bilinear := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr hA hB P R
    have hbil := hpair.product_pair_bilinear
      hax q r hq hr hA hB P R
    change hV.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) = _ at hbil
    dsimp [posteriorProductValue,
      posteriorValueRepresentation_positiveGaugeTransform,
      posteriorGaugeTransformedLeftCoeff,
      posteriorGaugeTransformedRightCoeff,
      posteriorGaugeTransformedInteractionCoeff]
    rw [hbil]
    have hgq : hgauge.gauge q ≠ 0 := ne_of_gt (hgauge.gauge_pos q)
    have hgr : hgauge.gauge r ≠ 0 := ne_of_gt (hgauge.gauge_pos r)
    field_simp [hgq, hgr]

/-- Product-gauge normalization of the two positive linear coefficients. -/
structure PosteriorProductGaugeNormalization
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV) : Prop where
  leftCoeff_eq_one :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A)
      (_hB : ¬ Subsingleton B),
      hpair.leftCoeff hax q r = 1
  rightCoeff_eq_one :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A)
      (_hB : ¬ Subsingleton B),
      hpair.rightCoeff hax q r = 1

/-- Normalized pairwise product formula, before proving that the interaction
coefficient is common. -/
theorem posteriorProductPairBilinear_normalized
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hnorm : PosteriorProductGaugeNormalization hpair)
    (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (P : Channel A O) (R : Channel B Y) :
    hV.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hV.V q (experimentOfChannel P) +
      hV.V r (experimentOfChannel R) +
      hpair.interactionCoeff hax q r *
        hV.V q (experimentOfChannel P) *
        hV.V r (experimentOfChannel R) := by
  change posteriorProductValue hV q r P R = _
  rw [hpair.product_pair_bilinear hax q r hq hr hA hB P R]
  rw [hnorm.leftCoeff_eq_one hax q r hq hr hA hB]
  rw [hnorm.rightCoeff_eq_one hax q r hq hr hA hB]
  ring

/-- Exact product associativity for the bare value representative. -/
structure PosteriorProductValueAssociativity
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F) : Prop where
  triple_value_assoc :
    ∀ (hax : TraceAxioms F)
      {A B C O Y Z : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      [Fintype Z] [DecidableEq Z]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (P : Channel A O) (R : Channel B Y) (S : Channel C Z),
      posteriorProductValue hV (prodDist q r) s (prodChannel P R) S =
        posteriorProductValue hV q (prodDist r s) P (prodChannel R S)

/-- Relabeling coherence supplies value associativity, with no branch-scale
input. -/
theorem posteriorProductValueAssociativity_of_relabeling
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV) :
    PosteriorProductValueAssociativity hV where
  triple_value_assoc := by
    intro hax A B C O Y Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      q r s _hq _hr _hs P R S
    have hrel := hrelV.V_relabel_eq
      (Equiv.prodAssoc A B C) (Equiv.prodAssoc O Y Z)
      (prodDist (prodDist q r) s) (prodChannel (prodChannel P R) S)
    have hrel' :
        posteriorProductValue hV q (prodDist r s) P (prodChannel R S) =
          posteriorProductValue hV (prodDist q r) s (prodChannel P R) S := by
      simpa [posteriorProductValue, relabelDist_prodAssoc q r s,
        relabelChannel_prodAssoc P R S] using hrel
    exact hrel'.symm

/-! ## Product-coefficient cocycle and its coboundary gauge -/

theorem posteriorProduct_bilinear_right_uninformative
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (P : Channel A O) :
    posteriorProductValue hV q r P (Channel.uninformativeChannelU B) =
      hpair.leftCoeff hax q r * hV.V q (experimentOfChannel P) := by
  rw [hpair.product_pair_bilinear hax q r hq hr hA hB P
    (Channel.uninformativeChannelU B)]
  rw [hV.zero_normalized r hr]
  ring

theorem posteriorProduct_bilinear_left_uninformative
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (R : Channel B Y) :
    posteriorProductValue hV q r (Channel.uninformativeChannelU A) R =
      hpair.rightCoeff hax q r * hV.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear hax q r hq hr hA hB
    (Channel.uninformativeChannelU A) R]
  rw [hV.zero_normalized q hq]
  ring

/-- Associativity identity for the first linear coefficient. -/
theorem posteriorProduct_leftCoeff_assoc
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (htriple : PosteriorProductValueAssociativity hV)
    (hax : TraceAxioms F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hs : s.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (hC : ¬ Subsingleton C) :
    hpair.leftCoeff hax (prodDist q r) s * hpair.leftCoeff hax q r =
      hpair.leftCoeff hax q (prodDist r s) := by
  have hqr := prodDist_fullSupport q r hq hr
  have hrs := prodDist_fullSupport r s hr hs
  have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
  have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
  have hVnz := posteriorValue_id_ne_zero_of_A1 hax hV q hq hA
  have hleft := posteriorProduct_bilinear_right_uninformative
    hpair hax q r hq hr hA hB (Channel.idChannel : Channel A A)
  have hleft' :
      hV.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel A A)
              (Channel.uninformativeChannelU B))) =
        hpair.leftCoeff hax q r *
          hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) := by
    simpa [posteriorProductValue] using hleft
  have hzero :
      hV.V (prodDist r s)
        (experimentOfChannel
          (prodChannel (Channel.uninformativeChannelU B)
            (Channel.uninformativeChannelU C))) = 0 :=
    V_prod_uninformative_uninformative_eq_zero F hV r s hr hs
  have hval := htriple.triple_value_assoc hax q r s hq hr hs
    (Channel.idChannel : Channel A A)
    (Channel.uninformativeChannelU B)
    (Channel.uninformativeChannelU C)
  rw [hpair.product_pair_bilinear hax (prodDist q r) s hqr hs hAB hC
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear hax q (prodDist r s) hq hrs hA hBC
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.uninformativeChannelU B)
        (Channel.uninformativeChannelU C))] at hval
  rw [hleft', hV.zero_normalized s hs, hzero] at hval
  have hcancel :
      hpair.leftCoeff hax (prodDist q r) s * hpair.leftCoeff hax q r *
          hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) =
        hpair.leftCoeff hax q (prodDist r s) *
          hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) := by
    nlinarith [hval]
  exact mul_right_cancel₀ hVnz hcancel

/-- Mixed associativity identity for the two linear coefficients. -/
theorem posteriorProduct_coeff_assoc_mixed
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (htriple : PosteriorProductValueAssociativity hV)
    (hax : TraceAxioms F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hs : s.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (hC : ¬ Subsingleton C) :
    hpair.leftCoeff hax (prodDist q r) s * hpair.rightCoeff hax q r =
      hpair.rightCoeff hax q (prodDist r s) *
        hpair.leftCoeff hax r s := by
  have hqr := prodDist_fullSupport q r hq hr
  have hrs := prodDist_fullSupport r s hr hs
  have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
  have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
  have hVnz := posteriorValue_id_ne_zero_of_A1 hax hV r hr hB
  have hleft := posteriorProduct_bilinear_left_uninformative
    hpair hax q r hq hr hA hB (Channel.idChannel : Channel B B)
  have hright := posteriorProduct_bilinear_right_uninformative
    hpair hax r s hr hs hB hC (Channel.idChannel : Channel B B)
  have hleft' :
      hV.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (Channel.idChannel : Channel B B))) =
        hpair.rightCoeff hax q r *
          hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    simpa [posteriorProductValue] using hleft
  have hright' :
      hV.V (prodDist r s)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel B B)
              (Channel.uninformativeChannelU C))) =
        hpair.leftCoeff hax r s *
          hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    simpa [posteriorProductValue] using hright
  have hval := htriple.triple_value_assoc hax q r s hq hr hs
    (Channel.uninformativeChannelU A)
    (Channel.idChannel : Channel B B)
    (Channel.uninformativeChannelU C)
  rw [hpair.product_pair_bilinear hax (prodDist q r) s hqr hs hAB hC
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear hax q (prodDist r s) hq hrs hA hBC
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C))] at hval
  rw [hleft', hright', hV.zero_normalized s hs,
    hV.zero_normalized q hq] at hval
  have hcancel :
      hpair.leftCoeff hax (prodDist q r) s * hpair.rightCoeff hax q r *
          hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) =
        (hpair.rightCoeff hax q (prodDist r s) *
          hpair.leftCoeff hax r s) *
          hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    nlinarith [hval]
  exact mul_right_cancel₀ hVnz hcancel

/-- Swap identifies the first coefficient with the swapped second
coefficient. -/
theorem posteriorProduct_leftCoeff_eq_swapped_rightCoeff
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.leftCoeff hax q r = hpair.rightCoeff hax r q := by
  have hVnz := posteriorValue_id_ne_zero_of_A1 hax hV q hq hA
  have hval := posteriorProductValue_swap hrelV hax q r
    (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)
  rw [posteriorProduct_bilinear_right_uninformative
    hpair hax q r hq hr hA hB (Channel.idChannel : Channel A A)] at hval
  rw [posteriorProduct_bilinear_left_uninformative
    hpair hax r q hr hq hB hA (Channel.idChannel : Channel A A)] at hval
  exact mul_right_cancel₀ hVnz
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- The corresponding swapped identity for the right coefficient. -/
theorem posteriorProduct_rightCoeff_eq_swapped_leftCoeff
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.rightCoeff hax q r = hpair.leftCoeff hax r q := by
  exact (posteriorProduct_leftCoeff_eq_swapped_rightCoeff
    hrelV hpair hax r q hr hq hB hA).symm

/-- Fixed nondegenerate reference alphabet for coefficient integration and
the common interaction. -/
abbrev posteriorProductInteractionReferenceType : Type u := ULift.{u, 0} Bool

noncomputable def posteriorProductInteractionReferencePrior :
    Dist posteriorProductInteractionReferenceType :=
  Dist.uniform

theorem posteriorProductInteractionReferencePrior_fullSupport :
    posteriorProductInteractionReferencePrior.FullSupport :=
  Dist.uniform_fullSupport (A := posteriorProductInteractionReferenceType)

theorem posteriorProductInteractionReference_not_subsingleton :
    ¬ Subsingleton posteriorProductInteractionReferenceType := by
  intro hsub
  have htf : (true : Bool) = false := congrArg ULift.down
    (Subsingleton.elim
      (ULift.up true : posteriorProductInteractionReferenceType)
      (ULift.up false : posteriorProductInteractionReferenceType))
  cases htf

/-- Raw coboundary value `rho(q0,x)=B(q0,x)/A(q0,x)` at the fixed two-point
reference prior. -/
noncomputable def posteriorProductCobGauge
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : ℝ :=
  hpair.rightCoeff hax posteriorProductInteractionReferencePrior x /
    hpair.leftCoeff hax posteriorProductInteractionReferencePrior x

theorem posteriorProductCobGauge_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) (hx : x.FullSupport) (hA : ¬ Subsingleton A) :
    0 < posteriorProductCobGauge hpair hax x := by
  exact div_pos
    (hpair.rightCoeff_pos hax posteriorProductInteractionReferencePrior x
      posteriorProductInteractionReferencePrior_fullSupport hx
      posteriorProductInteractionReference_not_subsingleton hA)
    (hpair.leftCoeff_pos hax posteriorProductInteractionReferencePrior x
      posteriorProductInteractionReferencePrior_fullSupport hx
      posteriorProductInteractionReference_not_subsingleton hA)

/-- Cocycle integrability: the first linear coefficient is the coboundary of
`posteriorProductCobGauge`. -/
theorem posteriorProductCobGauge_coboundary
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (htriple : PosteriorProductValueAssociativity hV)
    (hax : TraceAxioms F)
    {B C : Type u}
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (r : Dist B) (s : Dist C) (hr : r.FullSupport) (hs : s.FullSupport)
    (hB : ¬ Subsingleton B) (hC : ¬ Subsingleton C) :
    hpair.leftCoeff hax r s =
      posteriorProductCobGauge hpair hax r /
        posteriorProductCobGauge hpair hax (prodDist r s) := by
  let q0 : Dist posteriorProductInteractionReferenceType :=
    posteriorProductInteractionReferencePrior
  have hq0 := posteriorProductInteractionReferencePrior_fullSupport
  have hq0nd := posteriorProductInteractionReference_not_subsingleton
  have hrs := prodDist_fullSupport r s hr hs
  have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
  have hAqr := hpair.leftCoeff_pos hax q0 r hq0 hr hq0nd hB
  have hArs := hpair.leftCoeff_pos hax q0 (prodDist r s)
    hq0 hrs hq0nd hBC
  have hBqr := hpair.rightCoeff_pos hax q0 r hq0 hr hq0nd hB
  have hBrs := hpair.rightCoeff_pos hax q0 (prodDist r s)
    hq0 hrs hq0nd hBC
  have hii := posteriorProduct_leftCoeff_assoc hpair htriple hax
    q0 r s hq0 hr hs hq0nd hB hC
  have hi := posteriorProduct_coeff_assoc_mixed hpair htriple hax
    q0 r s hq0 hr hs hq0nd hB hC
  have hcross :
      hpair.leftCoeff hax r s * hpair.leftCoeff hax q0 r *
          hpair.rightCoeff hax q0 (prodDist r s) =
        hpair.rightCoeff hax q0 r *
          hpair.leftCoeff hax q0 (prodDist r s) := by
    nlinarith [hii, hi, hAqr, hArs, hBqr, hBrs]
  have hkey :
      hpair.leftCoeff hax r s =
        (hpair.rightCoeff hax q0 r / hpair.leftCoeff hax q0 r) /
          (hpair.rightCoeff hax q0 (prodDist r s) /
            hpair.leftCoeff hax q0 (prodDist r s)) := by
    rw [div_div_div_comm, div_div_div_comm]
    rw [eq_div_iff (by positivity)]
    field_simp
    nlinarith [hcross, hAqr, hArs, hBqr, hBrs,
      mul_pos hAqr hBrs, mul_pos hArs hBqr]
  simpa [posteriorProductCobGauge, q0] using hkey

/-- Relabeling the second prior leaves the first product coefficient
unchanged. -/
theorem posteriorProduct_leftCoeff_relabel_right
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A B B' : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype B'] [DecidableEq B'] [Nonempty B']
    (q : Dist A) (r : Dist B) (e : B ≃ B')
    (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.leftCoeff hax q (Relabeling.relabelDist e r) =
      hpair.leftCoeff hax q r := by
  have hVnz := posteriorValue_id_ne_zero_of_A1 hax hV q hq hA
  have hr' := Relabeling.relabelDist_fullSupport e r hr
  have hB' : ¬ Subsingleton B' := by
    intro hsub
    apply hB
    exact ⟨fun b b' => e.injective (Subsingleton.elim (e b) (e b'))⟩
  have h1 := posteriorProduct_bilinear_right_uninformative
    hpair hax q (Relabeling.relabelDist e r) hq hr' hA hB'
      (Channel.idChannel : Channel A A)
  have h2 := posteriorProduct_bilinear_right_uninformative
    hpair hax q r hq hr hA hB (Channel.idChannel : Channel A A)
  have hcov :
      posteriorProductValue hV q (Relabeling.relabelDist e r)
          (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B') =
        posteriorProductValue hV q r
          (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B) := by
    have hc := hrelV.V_relabel_eq
      ((Equiv.refl A).prodCongr e)
      ((Equiv.refl A).prodCongr (Equiv.refl PUnit.{u+1}))
      (prodDist q r)
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B))
    rw [Relabeling.relabelDist_prodCongr,
      Relabeling.relabelChannel_prodCongr] at hc
    rw [show Relabeling.relabelDist (Equiv.refl A) q = q from
      Relabeling.relabelDist_refl q] at hc
    rw [show Relabeling.relabelChannel (Equiv.refl A) (Equiv.refl A)
        (Channel.idChannel : Channel A A) =
          (Channel.idChannel : Channel A A) from by
      ext a o
      simp [Relabeling.relabelChannel, Channel.idChannel]] at hc
    rw [show Relabeling.relabelChannel e (Equiv.refl PUnit.{u+1})
        (Channel.uninformativeChannelU B) =
          (Channel.uninformativeChannelU B') from by
      ext b o
      cases o
      simp [Relabeling.relabelChannel, Channel.uninformativeChannelU]] at hc
    simpa [posteriorProductValue] using hc
  rw [h1, h2] at hcov
  exact mul_right_cancel₀ hVnz hcov

theorem posteriorProduct_relabelChannel_id_eq
    {B B' : Type u}
    [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B'] (e : B ≃ B') :
    Relabeling.relabelChannel e e (Channel.idChannel : Channel B B) =
      (Channel.idChannel : Channel B' B') := by
  ext b o
  simp only [Relabeling.relabelChannel, Channel.idChannel,
    Relabeling.relabelDist_apply]
  simp only [Dist.pure_apply, e.symm.injective.eq_iff]

/-- Relabeling the second prior leaves the right product coefficient
unchanged. -/
theorem posteriorProduct_rightCoeff_relabel_right
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A B B' : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype B'] [DecidableEq B'] [Nonempty B']
    (q : Dist A) (r : Dist B) (e : B ≃ B')
    (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.rightCoeff hax q (Relabeling.relabelDist e r) =
      hpair.rightCoeff hax q r := by
  have hVnz := posteriorValue_id_ne_zero_of_A1 hax hV r hr hB
  have hr' := Relabeling.relabelDist_fullSupport e r hr
  have hB' : ¬ Subsingleton B' := by
    intro hsub
    apply hB
    exact ⟨fun b b' => e.injective (Subsingleton.elim (e b) (e b'))⟩
  have h1 := posteriorProduct_bilinear_left_uninformative
    hpair hax q (Relabeling.relabelDist e r) hq hr' hA hB'
      (Channel.idChannel : Channel B' B')
  have h2 := posteriorProduct_bilinear_left_uninformative
    hpair hax q r hq hr hA hB (Channel.idChannel : Channel B B)
  have hVe :
      hV.V (Relabeling.relabelDist e r)
          (experimentOfChannel (Channel.idChannel : Channel B' B')) =
        hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    have hc := hrelV.V_relabel_eq e e r
      (Channel.idChannel : Channel B B)
    rw [posteriorProduct_relabelChannel_id_eq e] at hc
    exact hc
  have hcov :
      posteriorProductValue hV q (Relabeling.relabelDist e r)
          (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B' B') =
        posteriorProductValue hV q r
          (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B) := by
    have hc := hrelV.V_relabel_eq
      ((Equiv.refl A).prodCongr e)
      ((Equiv.refl PUnit.{u+1}).prodCongr e)
      (prodDist q r)
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B))
    rw [Relabeling.relabelDist_prodCongr,
      Relabeling.relabelChannel_prodCongr] at hc
    rw [show Relabeling.relabelDist (Equiv.refl A) q = q from
      Relabeling.relabelDist_refl q] at hc
    rw [show Relabeling.relabelChannel (Equiv.refl A)
        (Equiv.refl PUnit.{u+1}) (Channel.uninformativeChannelU A) =
          (Channel.uninformativeChannelU A) from by
      ext a o
      cases o
      simp [Relabeling.relabelChannel, Channel.uninformativeChannelU]] at hc
    rw [posteriorProduct_relabelChannel_id_eq e] at hc
    simpa [posteriorProductValue] using hc
  rw [h1, h2, hVe] at hcov
  exact mul_right_cancel₀ hVnz hcov

/-- The positive support of a relabeled prior, as an equivalence with the
original positive support.  Kept local to the bare product API. -/
noncomputable def posteriorProductRelabelSupportEquiv
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (r : Dist A) :
    supportSubtype (Relabeling.relabelDist e r) ≃ supportSubtype r where
  toFun b := ⟨e.symm b.1, by
    have hb := b.2
    rw [show (Relabeling.relabelDist e r) b.1 = r (e.symm b.1) from
      Relabeling.relabelDist_apply e r b.1] at hb
    exact hb⟩
  invFun a := ⟨e a.1, by
    rw [show (Relabeling.relabelDist e r) (e a.1) =
        r (e.symm (e a.1)) from
      Relabeling.relabelDist_apply e r (e a.1), Equiv.symm_apply_apply]
    exact a.2⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

theorem posteriorProduct_restrictToSupport_relabelDist
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (r : Dist A) :
    (Relabeling.relabelDist e r).restrictToSupport =
      Relabeling.relabelDist
        (posteriorProductRelabelSupportEquiv e r).symm
        r.restrictToSupport := by
  ext b
  rw [Dist.restrictToSupport_apply, Relabeling.relabelDist_apply,
    Relabeling.relabelDist_apply, Dist.restrictToSupport_apply]
  simp [posteriorProductRelabelSupportEquiv]

/-- A full-support prior's support subtype is canonically equivalent to its
ambient alphabet. -/
noncomputable def posteriorProductFullSupportRestrictEquiv
    {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) (hr : r.FullSupport) : supportSubtype r ≃ A where
  toFun x := x.1
  invFun a := ⟨a, hr a⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv _ := rfl

theorem posteriorProduct_restrictToSupport_fullSupport_eq_relabel
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) :
    r.restrictToSupport =
      Relabeling.relabelDist
        (posteriorProductFullSupportRestrictEquiv r hr).symm r := by
  ext x
  rw [Dist.restrictToSupport_apply, Relabeling.relabelDist_apply]
  rfl

/-- Support-completed coboundary gauge.  Singleton support faces use the
explicit neutral default `1`. -/
noncomputable def posteriorProductCobGaugeSF
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : ℝ := by
  classical
  exact if Subsingleton (supportSubtype x) then 1 else
    hpair.rightCoeff hax posteriorProductInteractionReferencePrior
        x.restrictToSupport /
      hpair.leftCoeff hax posteriorProductInteractionReferencePrior
        x.restrictToSupport

theorem posteriorProductCobGaugeSF_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : 0 < posteriorProductCobGaugeSF hpair hax x := by
  classical
  unfold posteriorProductCobGaugeSF
  by_cases h : Subsingleton (supportSubtype x)
  · rw [if_pos h]
    exact one_pos
  · rw [if_neg h]
    have hfs := Dist.restrictToSupport_fullSupport x
    exact div_pos
      (hpair.rightCoeff_pos hax posteriorProductInteractionReferencePrior
        x.restrictToSupport posteriorProductInteractionReferencePrior_fullSupport
        hfs posteriorProductInteractionReference_not_subsingleton h)
      (hpair.leftCoeff_pos hax posteriorProductInteractionReferencePrior
        x.restrictToSupport posteriorProductInteractionReferencePrior_fullSupport
        hfs posteriorProductInteractionReference_not_subsingleton h)

/-- The support-completed coboundary is invariant under support restriction
on nondegenerate support faces. -/
theorem posteriorProductCobGaugeSF_support_restrict
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    posteriorProductCobGaugeSF hpair hax r =
      posteriorProductCobGaugeSF hpair hax r.restrictToSupport := by
  classical
  have hnd : ¬ Subsingleton (supportSubtype r) := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    rw [not_subsingleton_iff_nontrivial]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩,
      fun h => hab (congrArg Subtype.val h)⟩
  have hrsfs := Dist.restrictToSupport_fullSupport r
  have hnd2 : ¬ Subsingleton (supportSubtype r.restrictToSupport) := by
    rw [not_subsingleton_iff_nontrivial] at hnd ⊢
    obtain ⟨a, b, hab⟩ := hnd
    refine ⟨⟨a, by rw [Dist.restrictToSupport_apply]; exact a.2⟩,
      ⟨b, by rw [Dist.restrictToSupport_apply]; exact b.2⟩, ?_⟩
    intro h
    exact hab (congrArg Subtype.val h)
  unfold posteriorProductCobGaugeSF
  rw [if_neg hnd, if_neg hnd2]
  set rs := r.restrictToSupport
  rw [posteriorProduct_restrictToSupport_fullSupport_eq_relabel rs hrsfs]
  rw [posteriorProduct_leftCoeff_relabel_right hrelV hpair hax
    posteriorProductInteractionReferencePrior rs
    (posteriorProductFullSupportRestrictEquiv rs hrsfs).symm
    posteriorProductInteractionReferencePrior_fullSupport hrsfs
    posteriorProductInteractionReference_not_subsingleton hnd]
  rw [posteriorProduct_rightCoeff_relabel_right hrelV hpair hax
    posteriorProductInteractionReferencePrior rs
    (posteriorProductFullSupportRestrictEquiv rs hrsfs).symm
    posteriorProductInteractionReferencePrior_fullSupport hrsfs
    posteriorProductInteractionReference_not_subsingleton hnd]

/-- The support-completed coboundary commutes with support restriction on
every prior.  On a singleton support both sides are the explicit neutral
default `1`; the preceding theorem handles a nondegenerate support. -/
theorem posteriorProductCobGaugeSF_support_restrict_all
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) :
    posteriorProductCobGaugeSF hpair hax r =
      posteriorProductCobGaugeSF hpair hax r.restrictToSupport := by
  classical
  by_cases hsub : Subsingleton (supportSubtype r)
  · have hsub' : Subsingleton (supportSubtype r.restrictToSupport) := by
      constructor
      intro a b
      apply Subtype.ext
      exact Subsingleton.elim a.1 b.1
    unfold posteriorProductCobGaugeSF
    rw [if_pos hsub, if_pos hsub']
  · have hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      rw [not_subsingleton_iff_nontrivial] at hsub
      obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := hsub
      exact ⟨a, b, fun h => hab (Subtype.ext h), ha, hb⟩
    exact posteriorProductCobGaugeSF_support_restrict
      hrelV hpair hax r hrnd

/-- The support-completed coboundary is invariant under finite relabeling. -/
theorem posteriorProductCobGaugeSF_relabel
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) :
    posteriorProductCobGaugeSF hpair hax (Relabeling.relabelDist e q) =
      posteriorProductCobGaugeSF hpair hax q := by
  classical
  have hequiv :
      Subsingleton (supportSubtype (Relabeling.relabelDist e q)) ↔
        Subsingleton (supportSubtype q) :=
    Equiv.subsingleton_congr (posteriorProductRelabelSupportEquiv e q)
  unfold posteriorProductCobGaugeSF
  by_cases hnd : Subsingleton (supportSubtype q)
  · rw [if_pos (hequiv.mpr hnd), if_pos hnd]
  · rw [if_neg (fun h => hnd (hequiv.mp h)), if_neg hnd]
    have hface :
        (Relabeling.relabelDist e q).restrictToSupport =
          Relabeling.relabelDist
            (posteriorProductRelabelSupportEquiv e q).symm
            q.restrictToSupport :=
      posteriorProduct_restrictToSupport_relabelDist e q
    rw [hface]
    have hqfs := Dist.restrictToSupport_fullSupport q
    rw [posteriorProduct_leftCoeff_relabel_right hrelV hpair hax
      posteriorProductInteractionReferencePrior q.restrictToSupport
      (posteriorProductRelabelSupportEquiv e q).symm
      posteriorProductInteractionReferencePrior_fullSupport hqfs
      posteriorProductInteractionReference_not_subsingleton hnd]
    rw [posteriorProduct_rightCoeff_relabel_right hrelV hpair hax
      posteriorProductInteractionReferencePrior q.restrictToSupport
      (posteriorProductRelabelSupportEquiv e q).symm
      posteriorProductInteractionReferencePrior_fullSupport hqfs
      posteriorProductInteractionReference_not_subsingleton hnd]

/-- On a full-support nondegenerate prior the support-completed and raw
coboundaries agree. -/
theorem posteriorProductCobGaugeSF_eq_raw
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) (hA : ¬ Subsingleton A) :
    posteriorProductCobGaugeSF hpair hax r =
      posteriorProductCobGauge hpair hax r := by
  have hndsupp : ¬ Subsingleton (supportSubtype r) := by
    rw [not_subsingleton_iff_nontrivial] at hA ⊢
    obtain ⟨a, b, hab⟩ := hA
    exact ⟨⟨a, hr a⟩, ⟨b, hr b⟩,
      fun h => hab (congrArg Subtype.val h)⟩
  unfold posteriorProductCobGaugeSF posteriorProductCobGauge
  rw [if_neg hndsupp]
  rw [posteriorProduct_restrictToSupport_fullSupport_eq_relabel r hr]
  rw [posteriorProduct_leftCoeff_relabel_right hrelV hpair hax
    posteriorProductInteractionReferencePrior r
    (posteriorProductFullSupportRestrictEquiv r hr).symm
    posteriorProductInteractionReferencePrior_fullSupport hr
    posteriorProductInteractionReference_not_subsingleton hA]
  rw [posteriorProduct_rightCoeff_relabel_right hrelV hpair hax
    posteriorProductInteractionReferencePrior r
    (posteriorProductFullSupportRestrictEquiv r hr).symm
    posteriorProductInteractionReferencePrior_fullSupport hr
    posteriorProductInteractionReference_not_subsingleton hA]

/-- The paper's coboundary is an actually constructed coherent positive
prior gauge. -/
noncomputable def posteriorProductCoboundaryGauge
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F) : CoherentFaceScaleGauge.{u} where
  gauge := fun {_} _ _ _ q => posteriorProductCobGaugeSF hpair hax q
  gauge_pos := by
    intro A _ _ _ q
    exact posteriorProductCobGaugeSF_pos hpair hax q
  gauge_relabel_eq := by
    intro A B _ _ _ _ _ _ e q
    exact posteriorProductCobGaugeSF_relabel hrelV hpair hax e q
  gauge_support_restrict_eq := by
    intro A _ _ _ r _ _hr_nonempty hrnd _hr_boundary
    exact posteriorProductCobGaugeSF_support_restrict
      hrelV hpair hax r hrnd

/-- Selected support-face value transport is preserved by the constructed
coboundary gauge, including singleton support faces. -/
theorem posteriorProduct_boundaryValueTransport_gaugeTransform
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax₀ : TraceAxioms F)
    (hboundary : FiniteBranchBoundaryValueTransportFor F hax₀ hV) :
    FiniteBranchBoundaryValueTransportFor F hax₀
      (posteriorValueRepresentation_positiveGaugeTransform hV
        (posteriorProductCoboundaryGauge hrelV hpair hax₀).toPositive) where
  boundary_value_transport := by
    intro A O _ _ _ _ _ r _ P
    dsimp [posteriorValueRepresentation_positiveGaugeTransform,
      CoherentFaceScaleGauge.toPositive, posteriorProductCoboundaryGauge]
    rw [hboundary.boundary_value_transport r P]
    rw [posteriorProductCobGaugeSF_support_restrict_all
      hrelV hpair hax₀ r]

/-- The constructed coboundary gauge normalizes the first linear product
coefficient. -/
theorem posteriorProductCoboundaryGauge_left_normalized
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (htriple : PosteriorProductValueAssociativity hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    posteriorGaugeTransformedLeftCoeff hpair
      (posteriorProductCoboundaryGauge hrelV hpair hax).toPositive
      hax q r = 1 := by
  have hprod := prodDist_fullSupport q r hq hr
  have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
  have hgq := ne_of_gt (posteriorProductCobGauge_pos hpair hax q hq hA)
  have hgp := ne_of_gt
    (posteriorProductCobGauge_pos hpair hax (prodDist q r) hprod hAB)
  dsimp [posteriorGaugeTransformedLeftCoeff,
    posteriorProductCoboundaryGauge, CoherentFaceScaleGauge.toPositive]
  rw [posteriorProductCobGaugeSF_eq_raw hrelV hpair hax q hq hA]
  rw [posteriorProductCobGaugeSF_eq_raw hrelV hpair hax
    (prodDist q r) hprod hAB]
  rw [posteriorProductCobGauge_coboundary
    hpair htriple hax q r hq hr hA hB]
  field_simp [hgq, hgp]

/-- The same gauge normalizes the second linear coefficient by swap and
relabeling coherence. -/
theorem posteriorProductCoboundaryGauge_right_normalized
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (htriple : PosteriorProductValueAssociativity hV)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    posteriorGaugeTransformedRightCoeff hpair
      (posteriorProductCoboundaryGauge hrelV hpair hax).toPositive
      hax q r = 1 := by
  have hprod_rq := prodDist_fullSupport r q hr hq
  have hBA : ¬ Subsingleton (B × A) := not_subsingleton_prod_left hB
  have hgprod :
      posteriorProductCobGaugeSF hpair hax (prodDist q r) =
        posteriorProductCobGaugeSF hpair hax (prodDist r q) := by
    have hrel := posteriorProductCobGaugeSF_relabel hrelV hpair hax
      (Equiv.prodComm A B) (prodDist q r)
    simpa [relabelDist_prodComm q r] using hrel.symm
  have hgr := ne_of_gt (posteriorProductCobGauge_pos hpair hax r hr hB)
  have hgp := ne_of_gt
    (posteriorProductCobGauge_pos hpair hax (prodDist r q) hprod_rq hBA)
  dsimp [posteriorGaugeTransformedRightCoeff,
    posteriorProductCoboundaryGauge, CoherentFaceScaleGauge.toPositive]
  rw [posteriorProduct_rightCoeff_eq_swapped_leftCoeff
    hrelV hpair hax q r hq hr hA hB]
  rw [hgprod]
  rw [posteriorProductCobGaugeSF_eq_raw hrelV hpair hax r hr hB]
  rw [posteriorProductCobGaugeSF_eq_raw hrelV hpair hax
    (prodDist r q) hprod_rq hBA]
  rw [posteriorProductCobGauge_coboundary
    hpair htriple hax r q hr hq hB hA]
  field_simp [hgr, hgp]

/-- Package the two coboundary normalizations.  The gauge is selected using
one proof of the behavioral axioms; proof irrelevance makes the result
independent of that proof argument. -/
noncomputable def posteriorProductCoboundaryGaugeNormalization
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (htriple : PosteriorProductValueAssociativity hV)
    (hax₀ : TraceAxioms F) :
    PosteriorProductGaugeNormalization
      (posteriorProductPairwiseBilinearity_gaugeTransform hpair
        (posteriorProductCoboundaryGauge hrelV hpair hax₀).toPositive) where
  leftCoeff_eq_one := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hp : hax = hax₀ := Subsingleton.elim _ _
    cases hp
    exact posteriorProductCoboundaryGauge_left_normalized
      hrelV hpair htriple hax₀ q r hq hr hA hB
  rightCoeff_eq_one := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hp : hax = hax₀ := Subsingleton.elim _ _
    cases hp
    exact posteriorProductCoboundaryGauge_right_normalized
      hrelV hpair htriple hax₀ q r hq hr hA hB

/-- The three coefficient identities extracted from normalized product
associativity. -/
structure PosteriorProductInteractionAssociativity
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV) : Prop where
  interaction_assoc_xy :
    ∀ (hax : TraceAxioms F)
      {A B C : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax q r =
        hpair.interactionCoeff hax q (prodDist r s)
  interaction_assoc_xz :
    ∀ (hax : TraceAxioms F)
      {A B C : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax q (prodDist r s)
  interaction_assoc_yz :
    ∀ (hax : TraceAxioms F)
      {A B C : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax r s

/-- Extract the three interaction-coefficient identities from normalized
triple-product value associativity. -/
theorem posteriorProductInteractionAssociativity_of_valueAssociativity
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    {hpair : PosteriorProductPairwiseBilinearity hV}
    (hnorm : PosteriorProductGaugeNormalization hpair)
    (htriple : PosteriorProductValueAssociativity hV) :
    PosteriorProductInteractionAssociativity hpair where
  interaction_assoc_xy := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
    have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
    have hxne :
        hV.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      posteriorValue_id_ne_zero_of_A1 hax hV q hq hA
    have hyne :
        hV.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      posteriorValue_id_ne_zero_of_A1 hax hV r hr hB
    have hxyne :
        hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) *
          hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      mul_ne_zero hxne hyne
    have hval := htriple.triple_value_assoc hax q r s hq hr hs
      (Channel.idChannel : Channel A A)
      (Channel.idChannel : Channel B B)
      (Channel.uninformativeChannelU C)
    dsimp [posteriorProductValue] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.idChannel : Channel B B))
        (Channel.uninformativeChannelU C)] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.uninformativeChannelU C))] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        q r hq hr hA hB
        (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B)] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        r s hr hs hB hC
        (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C)] at hval
    rw [hV.zero_normalized s hs] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxyne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_xz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
    have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
    have hxne :
        hV.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      posteriorValue_id_ne_zero_of_A1 hax hV q hq hA
    have hzne :
        hV.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      posteriorValue_id_ne_zero_of_A1 hax hV s hs hC
    have hxzne :
        hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) *
          hV.V s (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      mul_ne_zero hxne hzne
    have hval := htriple.triple_value_assoc hax q r s hq hr hs
      (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU B)
      (Channel.idChannel : Channel C C)
    dsimp [posteriorProductValue] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (Channel.idChannel : Channel C C)] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.uninformativeChannelU B)
          (Channel.idChannel : Channel C C))] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        q r hq hr hA hB
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        r s hr hs hB hC
        (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hV.zero_normalized r hr] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_yz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
    have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
    have hyne :
        hV.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      posteriorValue_id_ne_zero_of_A1 hax hV r hr hB
    have hzne :
        hV.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      posteriorValue_id_ne_zero_of_A1 hax hV s hs hC
    have hyzne :
        hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) *
          hV.V s (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      mul_ne_zero hyne hzne
    have hval := htriple.triple_value_assoc hax q r s hq hr hs
      (Channel.uninformativeChannelU A)
      (Channel.idChannel : Channel B B)
      (Channel.idChannel : Channel C C)
    dsimp [posteriorProductValue] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (Channel.idChannel : Channel C C)] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.uninformativeChannelU A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.idChannel : Channel C C))] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        q r hq hr hA hB
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)] at hval
    rw [posteriorProductPairBilinear_normalized hpair hnorm hax
        r s hr hs hB hC
        (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hV.zero_normalized q hq] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hyzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Common interaction coefficient on all nondegenerate full-support product
pairs. -/
structure PosteriorProductCommonInteraction
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV) where
  kappa : TraceAxioms F → ℝ
  interactionCoeff_common :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport)
      (_hr : r.FullSupport) (_hA : ¬ Subsingleton A)
      (_hB : ¬ Subsingleton B),
      hpair.interactionCoeff hax q r = kappa hax

noncomputable def posteriorProductReferenceKappa
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hax : TraceAxioms F) : ℝ :=
  hpair.interactionCoeff hax
    posteriorProductInteractionReferencePrior
    posteriorProductInteractionReferencePrior

/-- K1--K3 identify every nondegenerate interaction coefficient with the
fixed reference coefficient. -/
theorem posteriorProductInteractionCoeff_eq_reference
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hassoc : PosteriorProductInteractionAssociativity hpair)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.interactionCoeff hax q r =
      posteriorProductReferenceKappa hpair hax := by
  let q0 : Dist posteriorProductInteractionReferenceType :=
    posteriorProductInteractionReferencePrior
  have hq0 : q0.FullSupport :=
    posteriorProductInteractionReferencePrior_fullSupport
  have hRef : ¬ Subsingleton posteriorProductInteractionReferenceType :=
    posteriorProductInteractionReference_not_subsingleton
  have h_qr_to_r_ref :
      hpair.interactionCoeff hax q r =
        hpair.interactionCoeff hax r q0 := by
    calc
      hpair.interactionCoeff hax q r =
          hpair.interactionCoeff hax q (prodDist r q0) :=
        hassoc.interaction_assoc_xy hax q r q0 hq hr hq0 hA hB hRef
      _ = hpair.interactionCoeff hax (prodDist q r) q0 :=
        (hassoc.interaction_assoc_xz hax q r q0 hq hr hq0 hA hB hRef).symm
      _ = hpair.interactionCoeff hax r q0 :=
        hassoc.interaction_assoc_yz hax q r q0 hq hr hq0 hA hB hRef
  have h_r_ref_to_ref_ref :
      hpair.interactionCoeff hax r q0 =
        hpair.interactionCoeff hax q0 q0 := by
    calc
      hpair.interactionCoeff hax r q0 =
          hpair.interactionCoeff hax r (prodDist q0 q0) :=
        hassoc.interaction_assoc_xy hax r q0 q0 hr hq0 hq0 hB hRef hRef
      _ = hpair.interactionCoeff hax (prodDist r q0) q0 :=
        (hassoc.interaction_assoc_xz hax r q0 q0 hr hq0 hq0 hB hRef hRef).symm
      _ = hpair.interactionCoeff hax q0 q0 :=
        hassoc.interaction_assoc_yz hax r q0 q0 hr hq0 hq0 hB hRef hRef
  calc
    hpair.interactionCoeff hax q r =
        hpair.interactionCoeff hax r q0 := h_qr_to_r_ref
    _ = posteriorProductReferenceKappa hpair hax := by
      simpa [posteriorProductReferenceKappa, q0] using h_r_ref_to_ref_ref

/-- Package the common interaction coefficient. -/
noncomputable def posteriorProductCommonInteraction_of_associativity
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpair : PosteriorProductPairwiseBilinearity hV)
    (hassoc : PosteriorProductInteractionAssociativity hpair) :
    PosteriorProductCommonInteraction hpair where
  kappa := posteriorProductReferenceKappa hpair
  interactionCoeff_common := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    exact posteriorProductInteractionCoeff_eq_reference
      hpair hassoc hax q r hq hr hA hB

/-! ## Consumer-facing normalized product package -/

/-- End product of the bare Stage-3 reduction.  Its value representative is
definitionally the positive transform of the input `hV` by the displayed
coherent gauge. -/
structure PosteriorProductGaugeData
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F) where
  gauge : CoherentFaceScaleGauge.{u}
  relabeling : PosteriorValueRelabeling
    (posteriorValueRepresentation_positiveGaugeTransform hV gauge.toPositive)
  pairwise : PosteriorProductPairwiseBilinearity
    (posteriorValueRepresentation_positiveGaugeTransform hV gauge.toPositive)
  normalization : PosteriorProductGaugeNormalization pairwise
  valueAssociativity : PosteriorProductValueAssociativity
    (posteriorValueRepresentation_positiveGaugeTransform hV gauge.toPositive)
  interactionAssociativity :
    PosteriorProductInteractionAssociativity pairwise
  commonInteraction : PosteriorProductCommonInteraction pairwise
  boundaryValueTransport :
    ∀ hax : TraceAxioms F,
      FiniteBranchBoundaryValueTransportFor F hax
        (posteriorValueRepresentation_positiveGaugeTransform
          hV gauge.toPositive)

/-- The gauged representative carried by `PosteriorProductGaugeData`.
This is an abbreviation, hence unfolds definitionally. -/
noncomputable abbrev PosteriorProductGaugeData.gaugedValue
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hdata : PosteriorProductGaugeData hV) :
    PosteriorValueRepresentation F :=
  posteriorValueRepresentation_positiveGaugeTransform
    hV hdata.gauge.toPositive

/-- Construct the complete normalized product package from one selected
relabel-natural, support-coherent posterior representative. -/
noncomputable def posteriorProductGaugeData_of_axioms
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hrelV : PosteriorValueRelabeling hV)
    (hax₀ : TraceAxioms F)
    (hboundary₀ : FiniteBranchBoundaryValueTransportFor F hax₀ hV) :
    PosteriorProductGaugeData hV := by
  let hslice : PosteriorProductLeftSliceAffine hV :=
    posteriorProductLeftSliceAffine_of_axioms hV
  let hpair₀ : PosteriorProductPairwiseBilinearity hV :=
    posteriorProductPairwiseBilinearity_of_axioms hrelV hslice
  let htriple₀ : PosteriorProductValueAssociativity hV :=
    posteriorProductValueAssociativity_of_relabeling hrelV
  let hgauge : CoherentFaceScaleGauge.{u} :=
    posteriorProductCoboundaryGauge hrelV hpair₀ hax₀
  let hpair : PosteriorProductPairwiseBilinearity
      (posteriorValueRepresentation_positiveGaugeTransform
        hV hgauge.toPositive) :=
    posteriorProductPairwiseBilinearity_gaugeTransform
      hpair₀ hgauge.toPositive
  let hnorm : PosteriorProductGaugeNormalization hpair := by
    dsimp [hpair, hgauge]
    exact posteriorProductCoboundaryGaugeNormalization
      hrelV hpair₀ htriple₀ hax₀
  let hrel : PosteriorValueRelabeling
      (posteriorValueRepresentation_positiveGaugeTransform
        hV hgauge.toPositive) :=
    posteriorValueRelabeling_positiveGaugeTransform hrelV hgauge
  let htriple : PosteriorProductValueAssociativity
      (posteriorValueRepresentation_positiveGaugeTransform
        hV hgauge.toPositive) :=
    posteriorProductValueAssociativity_of_relabeling hrel
  let hinter : PosteriorProductInteractionAssociativity hpair :=
    posteriorProductInteractionAssociativity_of_valueAssociativity
      hnorm htriple
  let hcommon : PosteriorProductCommonInteraction hpair :=
    posteriorProductCommonInteraction_of_associativity hpair hinter
  let hboundary : FiniteBranchBoundaryValueTransportFor F hax₀
      (posteriorValueRepresentation_positiveGaugeTransform
        hV hgauge.toPositive) := by
    dsimp [hgauge]
    exact posteriorProduct_boundaryValueTransport_gaugeTransform
      hrelV hpair₀ hax₀ hboundary₀
  exact
    { gauge := hgauge
      relabeling := hrel
      pairwise := hpair
      normalization := hnorm
      valueAssociativity := htriple
      interactionAssociativity := hinter
      commonInteraction := hcommon
      boundaryValueTransport := by
        intro hax
        have hp : hax = hax₀ := Subsingleton.elim _ _
        cases hp
        exact hboundary }

/-- The normalized common-κ product formula for every full-support pair.
Nondegenerate pairs use the coefficient theorem; singleton factors collapse
by exact relabeling and their own value is zero. -/
theorem PosteriorProductGaugeData.product_quasi_add
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hdata : PosteriorProductGaugeData hV)
    (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hdata.gaugedValue.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hdata.gaugedValue.V q (experimentOfChannel P) +
      hdata.gaugedValue.V r (experimentOfChannel R) +
      hdata.commonInteraction.kappa hax *
        hdata.gaugedValue.V q (experimentOfChannel P) *
        hdata.gaugedValue.V r (experimentOfChannel R) := by
  classical
  by_cases hsubA : Subsingleton A
  · letI : Subsingleton A := hsubA
    have hqzero := branchValue_channel_eq_zero_of_subsingleton
      F hdata.gaugedValue q hq P
    have hcollapse := posteriorProductValue_eq_right_of_subsingleton_left
      hdata.relabeling hax q r P R
    dsimp [posteriorProductValue] at hcollapse
    rw [hcollapse, hqzero]
    ring
  · by_cases hsubB : Subsingleton B
    · letI : Subsingleton B := hsubB
      have hrzero := branchValue_channel_eq_zero_of_subsingleton
        F hdata.gaugedValue r hr R
      have hcollapse := posteriorProductValue_eq_left_of_subsingleton_right
        hdata.relabeling q r P R
      dsimp [posteriorProductValue] at hcollapse
      rw [hcollapse, hrzero]
      ring
    · rw [posteriorProductPairBilinear_normalized
        hdata.pairwise hdata.normalization hax
        q r hq hr hsubA hsubB P R]
      rw [hdata.commonInteraction.interactionCoeff_common
        hax q r hq hr hsubA hsubB]

/-- Full revelation stays strictly positive under the constructed positive
gauge on every nondegenerate full-support prior. -/
theorem PosteriorProductGaugeData.fullRevelation_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hdata : PosteriorProductGaugeData hV)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    0 < hdata.gaugedValue.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) :=
  posteriorValue_id_pos_of_A1 hax hdata.gaugedValue q hq hA

/-- Direct paper POS inequality.  In fact it holds at every second-coordinate
slice value, not only at full revelation. -/
theorem PosteriorProductGaugeData.productSliceFactor_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hdata : PosteriorProductGaugeData hV)
    (hax : TraceAxioms F)
    {B Y : Type u}
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (r : Dist B) (hr : r.FullSupport) (R : Channel B Y) :
    0 < 1 + hdata.commonInteraction.kappa hax *
      hdata.gaugedValue.V r (experimentOfChannel R) := by
  classical
  by_cases hsubB : Subsingleton B
  · letI : Subsingleton B := hsubB
    rw [branchValue_channel_eq_zero_of_subsingleton
      F hdata.gaugedValue r hr R]
    norm_num
  · let q₀ : Dist posteriorProductInteractionReferenceType :=
      posteriorProductInteractionReferencePrior
    have hq₀ : q₀.FullSupport :=
      posteriorProductInteractionReferencePrior_fullSupport
    have hRef : ¬ Subsingleton posteriorProductInteractionReferenceType :=
      posteriorProductInteractionReference_not_subsingleton
    let a₀ : posteriorProductInteractionReferenceType :=
      Classical.choice
        (inferInstance : Nonempty posteriorProductInteractionReferenceType)
    let U₀ : Channel posteriorProductInteractionReferenceType
        posteriorProductInteractionReferenceType :=
      fun _ => Dist.pure a₀
    have hU₀law : SamePosteriorLawExp q₀
        (experimentOfChannel U₀)
        (experimentOfChannel
          (Channel.uninformativeChannelU
            posteriorProductInteractionReferenceType)) := by
      intro φ _hφ
      change posteriorLawIntegral q₀ U₀ φ =
        posteriorLawIntegral q₀
          (Channel.uninformativeChannelU
            posteriorProductInteractionReferenceType) φ
      rw [posteriorLawIntegral_uninformativeChannelU_eq_prior]
      unfold posteriorLawIntegral
      rw [Fintype.sum_eq_single a₀]
      · have hm : Channel.outcomeMarginal U₀ q₀ a₀ = 1 := by
          simp [Channel.outcomeMarginal, U₀, q₀.sum_eq_one]
        have hp : Channel.posterior U₀ q₀ a₀ = q₀ := by
          ext a
          simp [Channel.posterior, Channel.outcomeMarginal, U₀,
            q₀.sum_eq_one]
        rw [hm, hp]
        ring
      · intro b hba
        have hm : Channel.outcomeMarginal U₀ q₀ b = 0 := by
          simp [Channel.outcomeMarginal, U₀, hba]
        rw [hm, zero_mul]
    have hU₀zero :
        hdata.gaugedValue.V q₀ (experimentOfChannel U₀) = 0 := by
      rw [hdata.gaugedValue.respects_same_posterior_law
        q₀ (experimentOfChannel U₀)
        (experimentOfChannel
          (Channel.uninformativeChannelU
            posteriorProductInteractionReferenceType)) hU₀law]
      exact hdata.gaugedValue.zero_normalized q₀ hq₀
    have hH₀pos :
        0 < hdata.gaugedValue.V q₀
          (experimentOfChannel
            (Channel.idChannel : Channel
              posteriorProductInteractionReferenceType
              posteriorProductInteractionReferenceType)) :=
      hdata.fullRevelation_pos hax q₀ hq₀ hRef
    have hnrev : ¬
        posteriorProductValue hdata.gaugedValue q₀ r
            U₀ R ≥
          posteriorProductValue hdata.gaugedValue q₀ r
            (Channel.idChannel : Channel
              posteriorProductInteractionReferenceType
              posteriorProductInteractionReferenceType) R := by
      intro hrev
      have hbase :=
        (posteriorProductValue_left_order_iff hax hdata.gaugedValue
          q₀ r hq₀ hr R
          U₀
          (Channel.idChannel : Channel
            posteriorProductInteractionReferenceType
            posteriorProductInteractionReferenceType)).mp hrev
      rw [hU₀zero] at hbase
      linarith
    have hstrict :
        posteriorProductValue hdata.gaugedValue q₀ r
            U₀ R <
          posteriorProductValue hdata.gaugedValue q₀ r
            (Channel.idChannel : Channel
              posteriorProductInteractionReferenceType
              posteriorProductInteractionReferenceType) R :=
      lt_of_not_ge hnrev
    have hid := hdata.product_quasi_add hax q₀ r hq₀ hr
      (Channel.idChannel : Channel
        posteriorProductInteractionReferenceType
        posteriorProductInteractionReferenceType) R
    have hno := hdata.product_quasi_add hax q₀ r hq₀ hr
      U₀ R
    dsimp [posteriorProductValue] at hstrict
    rw [hid, hno, hU₀zero] at hstrict
    have hmul :
        0 < hdata.gaugedValue.V q₀
            (experimentOfChannel
              (Channel.idChannel : Channel
                posteriorProductInteractionReferenceType
                posteriorProductInteractionReferenceType)) *
          (1 + hdata.commonInteraction.kappa hax *
            hdata.gaugedValue.V r (experimentOfChannel R)) := by
      nlinarith
    exact pos_of_mul_pos_right hmul (le_of_lt hH₀pos)

/-- Thin adapter from the bare normalized product package to the historical
face-scale consumer interface.  For a face-scale package constructed with
`hdata.gaugedValue`, the equality argument is `rfl`. -/
noncomputable def PosteriorProductGaugeData.toProductQuasiAdditivityForFaceScales
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hdata : PosteriorProductGaugeData hV)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hvalue : hfaces.branch_result.branch_agg.value_rep =
      hdata.gaugedValue) :
    FiniteProductQuasiAdditivityForFaceScales hfaces where
  kappa := hdata.commonInteraction.kappa
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hvalue]
    exact hdata.product_quasi_add hax q r hq hr P R

/-- Direct adapter for the historical full-revelation `Z > 0` package. -/
noncomputable def PosteriorProductGaugeData.toProductScaleZPositiveForFaceScales
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hdata : PosteriorProductGaugeData hV)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hvalue : hfaces.branch_result.branch_agg.value_rep =
      hdata.gaugedValue) :
    FiniteProductScaleZPositiveAssumptionsFor hfaces
      (hdata.toProductQuasiAdditivityForFaceScales hfaces hvalue) where
  Z_pos := by
    intro hax A _ _ _ q hq
    change 0 < 1 + hdata.commonInteraction.kappa hax *
      hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A))
    rw [hvalue]
    exact hdata.productSliceFactor_pos hax q hq
      (Channel.idChannel : Channel A A)

end TraceableAgency
