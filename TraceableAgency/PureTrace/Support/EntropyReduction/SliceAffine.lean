/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.SingletonCollapse

namespace TraceableAgency

universe u

/--
**Product Slice Slope Assumptions**

Paper-specific content identifying the first-coordinate slice slope as affine
in the second-coordinate value:

`α_R = A_{q,r} + C_{q,r} V_r(R)`.
-/
structure FiniteProductSliceSlopeAssumptions.{v}
    (hslice : FiniteProductLeftSliceAffineAssumptions.{v}) where
  leftCoeff :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff F hax hs q r
  leftSliceSlope_value :
    ∀ (F : PrefFamily.{v})
      (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      hslice.leftSliceSlope F hax hs q r R =
        leftCoeff F hax hs q r +
        interactionCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Difference-quotient identity for a first-coordinate affine slice. This is
the formal version of the paper's comparison of the slice value at two
first-coordinate experiments: the product-value gap is the slice slope times
the base-value gap. -/
theorem leftSliceSlope_mul_value_gap_eq_product_value_gap
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Z Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel A Z) (R : Channel B Y) :
    hslice.leftSliceSlope F hax hs q r R *
        (hs.branch_agg.value_rep.V q (experimentOfChannel P) -
          hs.branch_agg.value_rep.V q (experimentOfChannel Q)) =
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) -
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q R)) := by
  rw [hslice.left_slice_affine F hax hs q r hq hr P R,
      hslice.left_slice_affine F hax hs q r hq hr Q R]
  ring

/--
**Second-Coordinate Slope Affine Uniqueness**

Paper-specific affine-utility uniqueness conclusion for the slope function in
Step 2 of Lemma `coherentnorm`. After the paper compares a nonconstant
first-coordinate witness with the intercept identity, the first-coordinate
slice slope has the form

`α_R = A_{q,r} + C_{q,r} V_r(R)`, with `A_{q,r} > 0`.

Stage 10R keeps this as the live narrow slope obligation and derives the
previous `FiniteProductSliceSlopeAssumptions` compatibility package from it.
-/
structure ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{v}
    (hslice : FiniteProductLeftSliceAffineAssumptions.{v}) where
  slope_affine_in_second_value :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      ∃ Acoeff Ccoeff : ℝ, 0 < Acoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceSlope F hax hs q r R =
            Acoeff +
              Ccoeff * hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- The positive constant term in the slope-affine theorem. It is only used
under full-support guards; the fallback value is irrelevant. -/
noncomputable def leftSliceSlopeLeftCoeff
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{u} hslice)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (huniq.slope_affine_in_second_value F hax hs q r h.1 h.2)
    else 1

/-- The interaction coefficient in the slope-affine theorem. It is only used
under full-support guards; the fallback value is irrelevant. -/
noncomputable def leftSliceSlopeInteractionCoeff
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{u} hslice)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (Classical.choose_spec
          (huniq.slope_affine_in_second_value F hax hs q r h.1 h.2))
    else 0

/-- Recover the previous slope compatibility package from the narrower
second-coordinate slope-affine uniqueness interface. -/
noncomputable def productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{u} hslice) :
    FiniteProductSliceSlopeAssumptions.{u} hslice where
  leftCoeff := by
    intro F hax hs A B _ _ _ _ _ _ q r
    exact leftSliceSlopeLeftCoeff hslice huniq F hax hs q r
  interactionCoeff := by
    intro F hax hs A B _ _ _ _ _ _ q r
    exact leftSliceSlopeInteractionCoeff hslice huniq F hax hs q r
  leftCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    classical
    have hpos :=
      (Classical.choose_spec
        (Classical.choose_spec
          (huniq.slope_affine_in_second_value F hax hs q r hq hr))).1
    simpa [leftSliceSlopeLeftCoeff, hq, hr] using hpos
  leftSliceSlope_value := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (huniq.slope_affine_in_second_value F hax hs q r hq hr))).2 (R := R)
    simpa [leftSliceSlopeLeftCoeff, leftSliceSlopeInteractionCoeff, hq, hr]
      using hspec

/--
**Pairwise Product Bilinear Assumptions**

Compatibility package for the conclusion of Step 2 of Lemma `coherentnorm`.
Stage 10F no longer keeps this as the live external assumption; it is derived
from left-slice affinity plus the intercept and slope identifications.
-/
structure FinitePairwiseProductBilinearAssumptions.{v} where
  leftCoeff :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff F hax hs q r
  rightCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff F hax hs q r
  product_pair_bilinear :
    ∀ (F : PrefFamily.{v})
      (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        rightCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r (experimentOfChannel R) +
        interactionCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Assemble pairwise bilinear product form from the three Step 2 slice-affine
components isolated in Stage 10F. -/
def pairwiseProductBilinear_of_sliceAffine
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hintercept : FiniteProductSliceInterceptAssumptions.{u} hslice)
    (hslope : FiniteProductSliceSlopeAssumptions.{u} hslice) :
    FinitePairwiseProductBilinearAssumptions.{u} where
  leftCoeff := hslope.leftCoeff
  rightCoeff := hintercept.rightCoeff
  interactionCoeff := hslope.interactionCoeff
  leftCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hslope.leftCoeff_pos F hax hs q r hq hr
  rightCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hintercept.rightCoeff_pos F hax hs q r hq hr
  product_pair_bilinear := by
    intro F hax hs A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hslice.left_slice_affine F hax hs q r hq hr P R]
    rw [hslope.leftSliceSlope_value F hax hs q r hq hr R]
    rw [hintercept.leftSliceIntercept_value F hax hs q r hq hr R]
    ring

/-- The product of two no-information channels has zero value. Its outcome
space is a product of two `PUnit` spaces, hence subsingleton. -/
theorem V_prod_uninformative_uninformative_eq_zero
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hV.V (prodDist q r)
      (experimentOfChannel
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.uninformativeChannelU B))) = 0 := by
  exact V_eq_zero_of_subsingleton_outcome F hV
    (prodDist q r) (prodDist_fullSupport q r hq hr)
    (prodChannel (Channel.uninformativeChannelU A)
      (Channel.uninformativeChannelU B))

/-- Full revelation has nonzero value at full-support non-singleton priors. -/
theorem V_idChannel_ne_zero_of_A1
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hnot_subsingleton : ¬ Subsingleton A) :
    hs.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
  have hne :=
    (valueNonconstancy_of_A1_experiment_strictness
      a1ExperimentPairStrictness_of_axioms).base_value_nonconstant
      F hax hs q hq hnot_subsingleton
  have hzero :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hs.branch_agg.value_rep.zero_normalized q hq
  intro hid_zero
  exact hne (hid_zero.trans hzero.symm)

/-- Pairwise bilinear form with no information in the right coordinate. -/
theorem product_pair_bilinear_right_uninformative
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel
          (prodChannel P (Channel.uninformativeChannelU B))) =
      hpair.leftCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P
    (Channel.uninformativeChannelU B)]
  rw [hs.branch_agg.value_rep.zero_normalized r hr]
  ring

/-- Pairwise bilinear form with no information in the left coordinate. -/
theorem product_pair_bilinear_left_uninformative
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel
          (prodChannel (Channel.uninformativeChannelU A) R)) =
      hpair.rightCoeff F hax hs q r *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr
    (Channel.uninformativeChannelU A) R]
  rw [hs.branch_agg.value_rep.zero_normalized q hq]
  ring

/-- If the left action set is singleton, the pairwise bilinear identity cannot
read the left or interaction coefficients: all left-coordinate values are zero. -/
theorem product_pair_bilinear_subsingleton_left
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hpair.rightCoeff F hax hs q r *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P]
  ring

/-- If the right action set is singleton, the pairwise bilinear identity cannot
read the right or interaction coefficients: all right-coordinate values are zero. -/
theorem product_pair_bilinear_subsingleton_right
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hpair.leftCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep r hr R]
  ring

/-- If the left action set is singleton, the interaction term in the pairwise
bilinear formula is identically zero. Thus product values cannot identify the
interaction coefficient in this degenerate coordinate. -/
theorem product_pair_bilinear_subsingleton_left_interaction_drops_out
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hpair.interactionCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) = 0 := by
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P]
  ring

/-- If the right action set is singleton, the interaction term in the pairwise
bilinear formula is identically zero. Thus product values cannot identify the
interaction coefficient in this degenerate coordinate. -/
theorem product_pair_bilinear_subsingleton_right_interaction_drops_out
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hpair.interactionCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) = 0 := by
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep r hr R]
  ring

/-- Product priors are symmetric up to the canonical product-label swap. -/
theorem relabelDist_prodComm
    {A B : Type u} [Fintype A] [Fintype B]
    (q : Dist A) (r : Dist B) :
    Relabeling.relabelDist (Equiv.prodComm A B) (prodDist q r) =
      prodDist r q := by
  ext x
  rcases x with ⟨b, a⟩
  simp [Relabeling.relabelDist, prodDist_apply_pair, mul_comm]

/-- Product channels are symmetric up to the canonical product-label swap on
actions and outcomes. -/
theorem relabelChannel_prodComm
    {A B O Y : Type u}
    [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (P : Channel A O) (R : Channel B Y) :
    Relabeling.relabelChannel (Equiv.prodComm A B) (Equiv.prodComm O Y)
        (prodChannel P R) =
      prodChannel R P := by
  ext x o
  rcases x with ⟨b, a⟩
  rcases o with ⟨y, o⟩
  simp [Relabeling.relabelChannel, prodChannel_apply_pair, mul_comm]

/-- Outcome marginals are transported by simultaneous action/outcome relabeling. -/
theorem outcomeMarginal_relabelChannel
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) (y : Y) :
    Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y =
      Channel.outcomeMarginal P q (eO.symm y) := by
  simp only [Channel.outcomeMarginal_apply, Relabeling.relabelDist_apply,
    Relabeling.relabelChannel_apply]
  rw [Equiv.sum_comp eA.symm (fun a : A => q a * P a (eO.symm y))]

/-- At positive outcomes, posteriors are transported by simultaneous
action/outcome relabeling. Zero-marginal outcomes are irrelevant to posterior
laws and are therefore left out of this statement. -/
theorem posterior_relabelChannel_of_pos
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) (y : Y)
    (hpos : Channel.outcomeMarginal P q (eO.symm y) > 0) :
    Channel.posterior (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y =
      Relabeling.relabelDist eA (Channel.posterior P q (eO.symm y)) := by
  have hpos' : Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y > 0 := by
    rw [outcomeMarginal_relabelChannel eA eO q P y]
    exact hpos
  ext b
  unfold Channel.posterior
  rw [dif_pos hpos', dif_pos hpos]
  change (Relabeling.relabelDist eA q b *
        Relabeling.relabelChannel eA eO P b y) /
        Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
          (Relabeling.relabelDist eA q) y =
      q (eA.symm b) * P (eA.symm b) (eO.symm y) /
        Channel.outcomeMarginal P q (eO.symm y)
  rw [outcomeMarginal_relabelChannel eA eO q P y]
  rfl

/-- Posterior-law integrals are transported by simultaneous action/outcome
relabeling. This is the structural posterior-law form of exact relabeling:
test functions on the relabeled action simplex are pulled back by the action
relabeling. -/
theorem posteriorLawIntegral_relabelChannel
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) (φ : Dist B → ℝ) :
    posteriorLawIntegral (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel eA eO P) φ =
      posteriorLawIntegral q P (fun d => φ (Relabeling.relabelDist eA d)) := by
  unfold posteriorLawIntegral
  let f : O → ℝ := fun o =>
    Channel.outcomeMarginal P q o *
      φ (Relabeling.relabelDist eA (Channel.posterior P q o))
  let g : Y → ℝ := fun y =>
    Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y *
      φ (Channel.posterior (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y)
  change (∑ y : Y, g y) = ∑ o : O, f o
  exact (Fintype.sum_equiv eO f g (by
    intro o
    dsimp [f, g]
    change Channel.outcomeMarginal P q o *
        φ (Relabeling.relabelDist eA (Channel.posterior P q o)) =
      Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
          (Relabeling.relabelDist eA q) (eO o) *
        φ (Channel.posterior (Relabeling.relabelChannel eA eO P)
          (Relabeling.relabelDist eA q) (eO o))
    rw [outcomeMarginal_relabelChannel eA eO q P (eO o)]
    simp only [Equiv.symm_apply_apply]
    by_cases hpos : Channel.outcomeMarginal P q o > 0
    · rw [posterior_relabelChannel_of_pos eA eO q P (eO o)]
      · simp
      · simpa
    · have hmarg_nonneg : 0 ≤ Channel.outcomeMarginal P q o :=
        (Channel.outcomeMarginal P q).nonneg o
      have hmarg_zero : Channel.outcomeMarginal P q o = 0 := by
        exact le_antisymm (le_of_not_gt hpos) hmarg_nonneg
      rw [hmarg_zero]
      simp)).symm

/-- Posterior-law integrals for the two product parenthesizations agree after
pulling test functions back along the canonical product associativity
relabeling. This is structural posterior-law plumbing; it is not yet the
cardinal value equality needed for coefficient comparison. -/
theorem posteriorLawIntegral_prodAssoc
    {A B C O Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (P : Channel A O) (R : Channel B Y) (S : Channel C Z)
    (φ : Dist (A × (B × C)) → ℝ) :
    posteriorLawIntegral (prodDist q (prodDist r s))
        (prodChannel P (prodChannel R S)) φ =
      posteriorLawIntegral (prodDist (prodDist q r) s)
        (prodChannel (prodChannel P R) S)
        (fun d => φ (Relabeling.relabelDist (Equiv.prodAssoc A B C) d)) := by
  have h := posteriorLawIntegral_relabelChannel
    (eA := Equiv.prodAssoc A B C)
    (eO := Equiv.prodAssoc O Y Z)
    (q := prodDist (prodDist q r) s)
    (P := prodChannel (prodChannel P R) S)
    (φ := φ)
  simpa [relabelDist_prodAssoc q r s, relabelChannel_prodAssoc P R S] using h

/-- Normalized branch values are exactly invariant under relabelling once the
chosen value representatives and the chosen chain scales are both coherent
under relabelling. -/
theorem branchNormalizedValue_relabel_eq_of_valueRelabeling_and_faceScales
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    branchNormalizedValue hfaces.chain
        (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel eA eO P) =
      branchNormalizedValue hfaces.chain q P := by
  unfold branchNormalizedValue
  unfold CoherentRelabelingFaceScalesStructure.chain
  unfold BranchAggregationCocycleNormalizedChainRuleStructure.chain
  unfold branchChainStructure_of_scaleFactorization
  have hVeq :=
    exactRelabelingInvariance_of_valueRelabeling
      hrelV F hax hfaces.branch_result.branch_agg.value_rep
      eA eO q P
  have hscale :=
    CoherentRelabelingFaceScalesStructure.scale_relabel_eq
      hfaces eA q hq
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) /
      hfaces.branch_result.scale_factorization.scale
        (Relabeling.relabelDist eA q)
    =
    hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel P) /
      hfaces.branch_result.scale_factorization.scale q
  rw [hVeq, hscale]

/-- The cardinal value-level triple-product associativity statement needed by
paper Step 3. It says that the two parenthesizations of a product experiment
have the same value after canonical product associativity is accounted for. -/
def TripleProductValueAssociates
    (F : PrefFamily.{u}) (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C) : Prop :=
  ∀ {O Y Z : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (P : Channel A O) (R : Channel B Y) (S : Channel C Z),
      hs.branch_agg.value_rep.V (prodDist (prodDist q r) s)
          (experimentOfChannel (prodChannel (prodChannel P R) S)) =
        hs.branch_agg.value_rep.V (prodDist q (prodDist r s))
          (experimentOfChannel (prodChannel P (prodChannel R S)))

/--
Value-level triple-product associativity. This isolates the exact cardinal
upgrade from the structural posterior-law transport theorem
`posteriorLawIntegral_prodAssoc` to equality of the chosen value
representatives across the two product action types.
-/
structure FiniteTripleProductValueAssociativityAssumptions.{v} where
  triple_value_assoc :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s

/-- Product-parenthesization value associativity follows from the coherent
value-relabeling interface and the structural product associativity relabeling
facts. -/
theorem tripleProductValueAssociates_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport) :
    TripleProductValueAssociates F hs q r s := by
  intro O Y Z _ _ _ _ _ _ P R S
  have hrel :=
    hrelV.V_relabel_eq F hax hs.branch_agg.value_rep
      (Equiv.prodAssoc A B C) (Equiv.prodAssoc O Y Z)
      (prodDist (prodDist q r) s) (prodChannel (prodChannel P R) S)
  have hrel' :
      hs.branch_agg.value_rep.V (prodDist q (prodDist r s))
          (experimentOfChannel (prodChannel P (prodChannel R S))) =
        hs.branch_agg.value_rep.V (prodDist (prodDist q r) s)
          (experimentOfChannel (prodChannel (prodChannel P R) S)) := by
    simpa [relabelDist_prodAssoc q r s, relabelChannel_prodAssoc P R S] using hrel
  exact hrel'.symm

/-- Reconstruct value-level triple-product associativity from coherent
value-relabeling of the chosen posterior representatives. -/
theorem tripleProductValueAssociativity_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u}) :
    FiniteTripleProductValueAssociativityAssumptions.{u} where
  triple_value_assoc := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact tripleProductValueAssociates_of_value_relabeling
      hrelV F hax hs q r s hq hr hsupp

/--
**Product Gauge Coherence Assumptions**

Paper-specific content from Steps 3-5 of Lemma `coherentnorm`: after coherent
positive rescaling of the zero-normalized representatives, the pair-specific
linear coefficients are both one and the interaction coefficient is a common
scalar `κ`, including singleton compatibility.
-/
structure FiniteProductGaugeCoherenceAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  kappa : ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F → ℝ
  leftCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff F hax hs q r = 1
  rightCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff F hax hs q r = 1
  interactionCoeff_common :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.interactionCoeff F hax hs q r = kappa F hax hs

/-- Ratio of the two linear coefficients before Step 3 gauge normalization:
`rho(p,r) = B_{p,r}/A_{p,r}` in the paper. -/
noncomputable def linearCoeffRho
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.rightCoeff F hax hs q r / hpair.leftCoeff F hax hs q r

/-- The coefficient ratio is positive at full-support priors. -/
theorem linearCoeffRho_pos
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    0 < linearCoeffRho hpair F hax hs q r := by
  unfold linearCoeffRho
  exact div_pos (hpair.rightCoeff_pos F hax hs q r hq hr)
    (hpair.leftCoeff_pos F hax hs q r hq hr)

/-- Product-swap value equality from coherent value relabeling and the
structural product-swap relabeling facts. -/
theorem product_value_swap_eq_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hs.branch_agg.value_rep.V (prodDist r q)
        (experimentOfChannel (prodChannel R P)) := by
  have hrel :=
    hrelV.V_relabel_eq F hax hs.branch_agg.value_rep
      (Equiv.prodComm A B) (Equiv.prodComm O Y)
      (prodDist q r) (prodChannel P R)
  have hrel' :
      hs.branch_agg.value_rep.V (prodDist r q)
          (experimentOfChannel (prodChannel R P)) =
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) := by
    simpa [relabelDist_prodComm q r, relabelChannel_prodComm P R] using hrel
  exact hrel'.symm

/--
Paper Step 3 coefficient associativity equations C1-C3, obtained by comparing
the two parenthesizations of a triple product after identifying product types by
the canonical associativity relabeling.
-/
structure FiniteProductLinearCoeffAssociativityAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/-- Nondegenerate C1 coefficient extraction. Vary the first coordinate and set
the second and third coordinates to no information. -/
theorem coeff_assoc_A_from_triple_of_nontrivial_left
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton A)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.leftCoeff F hax hs (prodDist q r) s *
        hpair.leftCoeff F hax hs q r =
      hpair.leftCoeff F hax hs q (prodDist r s) := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hVnonzero :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hnot_subsingleton
  have hleft_inner :
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel A A)
              (Channel.uninformativeChannelU B))) =
        hpair.leftCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q
            (experimentOfChannel (Channel.idChannel : Channel A A)) :=
    product_pair_bilinear_right_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel A A)
  have hright_inner_zero :
      hs.branch_agg.value_rep.V (prodDist r s)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU B)
              (Channel.uninformativeChannelU C))) = 0 :=
    V_prod_uninformative_uninformative_eq_zero F hs.branch_agg.value_rep
      r s hr hsupp
  have hval := htriple
    (P := (Channel.idChannel : Channel A A))
    (R := (Channel.uninformativeChannelU B))
    (S := (Channel.uninformativeChannelU C))
  rw [hpair.product_pair_bilinear F hax hs (prodDist q r) s hqr hsupp
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear F hax hs q (prodDist r s) hq hrs
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.uninformativeChannelU B)
        (Channel.uninformativeChannelU C))] at hval
  rw [hleft_inner, hs.branch_agg.value_rep.zero_normalized s hsupp,
      hright_inner_zero] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate C2 coefficient extraction. Vary the middle coordinate and
set the first and third coordinates to no information. -/
theorem coeff_assoc_mixed_from_triple_of_nontrivial_middle
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton B)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.leftCoeff F hax hs (prodDist q r) s *
        hpair.rightCoeff F hax hs q r =
      hpair.rightCoeff F hax hs q (prodDist r s) *
        hpair.leftCoeff F hax hs r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hVnonzero :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hnot_subsingleton
  have hleft_inner :
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (Channel.idChannel : Channel B B))) =
        hpair.rightCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) :=
    product_pair_bilinear_left_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel B B)
  have hright_inner :
      hs.branch_agg.value_rep.V (prodDist r s)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel B B)
              (Channel.uninformativeChannelU C))) =
        hpair.leftCoeff F hax hs r s *
          hs.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) :=
    product_pair_bilinear_right_uninformative hpair F hax hs r s hr hsupp
      (Channel.idChannel : Channel B B)
  have hval := htriple
    (P := (Channel.uninformativeChannelU A))
    (R := (Channel.idChannel : Channel B B))
    (S := (Channel.uninformativeChannelU C))
  rw [hpair.product_pair_bilinear F hax hs (prodDist q r) s hqr hsupp
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear F hax hs q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C))] at hval
  rw [hleft_inner, hright_inner, hs.branch_agg.value_rep.zero_normalized s hsupp,
      hs.branch_agg.value_rep.zero_normalized q hq] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate C3 coefficient extraction. Vary the third coordinate and set
the first and second coordinates to no information. -/
theorem coeff_assoc_B_from_triple_of_nontrivial_right
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.rightCoeff F hax hs (prodDist q r) s =
      hpair.rightCoeff F hax hs q (prodDist r s) *
        hpair.rightCoeff F hax hs r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hVnonzero :
      hs.branch_agg.value_rep.V s
        (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs s hsupp hnot_subsingleton
  have hleft_inner_zero :
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (Channel.uninformativeChannelU B))) = 0 :=
    V_prod_uninformative_uninformative_eq_zero F hs.branch_agg.value_rep
      q r hq hr
  have hright_inner :
      hs.branch_agg.value_rep.V (prodDist r s)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU B)
              (Channel.idChannel : Channel C C))) =
        hpair.rightCoeff F hax hs r s *
          hs.branch_agg.value_rep.V s
            (experimentOfChannel (Channel.idChannel : Channel C C)) :=
    product_pair_bilinear_left_uninformative hpair F hax hs r s hr hsupp
      (Channel.idChannel : Channel C C)
  have hval := htriple
    (P := (Channel.uninformativeChannelU A))
    (R := (Channel.uninformativeChannelU B))
    (S := (Channel.idChannel : Channel C C))
  rw [hpair.product_pair_bilinear F hax hs (prodDist q r) s hqr hsupp
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B))
      (Channel.idChannel : Channel C C)] at hval
  rw [hpair.product_pair_bilinear F hax hs q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C))] at hval
  rw [hleft_inner_zero, hright_inner,
      hs.branch_agg.value_rep.zero_normalized q hq] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/--
Coefficient extraction from value-level triple-product associativity. This is
the remaining elementary algebra/uniqueness step in paper Step 3: once the two
triple-product parenthesizations have the same value, comparing the
pair-specific bilinear expansions yields C1-C3.
-/
structure FiniteTripleProductCoeffExtractionAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A_from_triple :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed_from_triple :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B_from_triple :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s →
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/--
The remaining degenerate branches for coefficient extraction. Stage 10V proves
C1, C2, and C3 whenever the coordinate whose value is varied is
non-subsingleton. These fields isolate exactly the singleton cases where the
paper's nondegenerate interval argument cannot be reproduced by cancellation.
-/
structure FiniteTripleProductCoeffExtractionSingletonAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A_of_subsingleton :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton A →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed_of_subsingleton :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton B →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B_of_subsingleton :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton C →
      TripleProductValueAssociates F hs q r s →
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/--
Singleton coefficient gauge normalization. On singleton fibres the relevant
coordinate value is identically zero, so the corresponding linear coefficient
is not identified by product values. These equations are therefore classified
as a singleton/gauge normalization, not as an extracted coefficient comparison.
-/
structure FiniteSingletonCoefficientGaugeNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A_singleton_normalization :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton A →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed_singleton_normalization :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton B →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B_singleton_normalization :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton C →
      TripleProductValueAssociates F hs q r s →
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/-- Convert the singleton gauge normalization into the old singleton coefficient
extraction compatibility package. -/
theorem tripleProductCoeffExtractionSingleton_of_gaugeNormalization
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hgauge :
      FiniteSingletonCoefficientGaugeNormalizationAssumptions.{u} hpair) :
    FiniteTripleProductCoeffExtractionSingletonAssumptions.{u} hpair where
  coeff_assoc_A_of_subsingleton := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hsub htriple
    exact hgauge.coeff_assoc_A_singleton_normalization
      F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_mixed_of_subsingleton := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hsub htriple
    exact hgauge.coeff_assoc_mixed_singleton_normalization
      F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_B_of_subsingleton := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hsub htriple
    exact hgauge.coeff_assoc_B_singleton_normalization
      F hax hs q r s hq hr hsupp hsub htriple

/-- Reconstruct full coefficient extraction from the internally proved
nondegenerate C1-C3 cases and the remaining singleton branches. -/
theorem tripleProductCoeffExtraction_of_nondegenerate_and_singleton
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hsingle :
      FiniteTripleProductCoeffExtractionSingletonAssumptions.{u} hpair) :
    FiniteTripleProductCoeffExtractionAssumptions.{u} hpair where
  coeff_assoc_A_from_triple := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp htriple
    by_cases hsub : Subsingleton A
    · exact hsingle.coeff_assoc_A_of_subsingleton
        F hax hs q r s hq hr hsupp hsub htriple
    · exact coeff_assoc_A_from_triple_of_nontrivial_left
        hpair F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_mixed_from_triple := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp htriple
    by_cases hsub : Subsingleton B
    · exact hsingle.coeff_assoc_mixed_of_subsingleton
        F hax hs q r s hq hr hsupp hsub htriple
    · exact coeff_assoc_mixed_from_triple_of_nontrivial_middle
        hpair F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_B_from_triple := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp htriple
    by_cases hsub : Subsingleton C
    · exact hsingle.coeff_assoc_B_of_subsingleton
        F hax hs q r s hq hr hsupp hsub htriple
    · exact coeff_assoc_B_from_triple_of_nontrivial_right
        hpair F hax hs q r s hq hr hsupp hsub htriple

/-- Reassemble the paper Step 3 C1-C3 coefficient associativity package from
value-level triple associativity plus coefficient extraction. -/
theorem linearCoeffAssociativity_of_triple_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (htriple : FiniteTripleProductValueAssociativityAssumptions.{u})
    (hextract : FiniteTripleProductCoeffExtractionAssumptions.{u} hpair) :
    FiniteProductLinearCoeffAssociativityAssumptions.{u} hpair where
  coeff_assoc_A := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact hextract.coeff_assoc_A_from_triple F hax hs q r s hq hr hsupp
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  coeff_assoc_mixed := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact hextract.coeff_assoc_mixed_from_triple F hax hs q r s hq hr hsupp
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  coeff_assoc_B := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact hextract.coeff_assoc_B_from_triple F hax hs q r s hq hr hsupp
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)

/--
Paper Step 3 coordinate-swap consequence for the linear coefficient ratio:
`rho(r,p) = rho(p,r)^{-1}`, stated without division by writing the product as
one. This is the coefficient-level part forced by product swap before choosing
the normalized gauge.
-/
structure FiniteProductLinearCoeffSwapAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  rho_reciprocity :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      linearCoeffRho hpair F hax hs q r *
          linearCoeffRho hpair F hax hs r q =
        1

/-- Nondegenerate swap extraction for the first linear coefficient:
`A_{q,r} = B_{r,q}`. -/
theorem leftCoeff_eq_swapped_rightCoeff_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton A) :
    hpair.leftCoeff F hax hs q r =
      hpair.rightCoeff F hax hs r q := by
  have hVnonzero :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hnot_subsingleton
  have hval :=
    product_value_swap_eq_of_value_relabeling hrelV F hax hs q r
      (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)
  rw [product_pair_bilinear_right_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel A A)] at hval
  rw [product_pair_bilinear_left_uninformative hpair F hax hs r q hr hq
      (Channel.idChannel : Channel A A)] at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate swap extraction for the second linear coefficient:
`B_{q,r} = A_{r,q}`. -/
theorem rightCoeff_eq_swapped_leftCoeff_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton B) :
    hpair.rightCoeff F hax hs q r =
      hpair.leftCoeff F hax hs r q := by
  have hVnonzero :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hnot_subsingleton
  have hval :=
    product_value_swap_eq_of_value_relabeling hrelV F hax hs q r
      (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B)
  rw [product_pair_bilinear_left_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_right_uninformative hpair F hax hs r q hr hq
      (Channel.idChannel : Channel B B)] at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate rho reciprocity extracted from product swap. -/
theorem linearCoeffRho_reciprocity_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hnot_subsingleton_A : ¬ Subsingleton A)
    (hnot_subsingleton_B : ¬ Subsingleton B) :
    linearCoeffRho hpair F hax hs q r *
        linearCoeffRho hpair F hax hs r q =
      1 := by
  have hA :=
    leftCoeff_eq_swapped_rightCoeff_of_value_swap_nondegenerate
      hrelV hpair F hax hs q r hq hr hnot_subsingleton_A
  have hB :=
    rightCoeff_eq_swapped_leftCoeff_of_value_swap_nondegenerate
      hrelV hpair F hax hs q r hq hr hnot_subsingleton_B
  unfold linearCoeffRho
  rw [hB, hA]
  have hleft_ne :
      hpair.leftCoeff F hax hs q r ≠ 0 :=
    ne_of_gt (hpair.leftCoeff_pos F hax hs q r hq hr)
  have hright_ne :
      hpair.leftCoeff F hax hs r q ≠ 0 :=
    ne_of_gt (hpair.leftCoeff_pos F hax hs r q hr hq)
  have hswapped_right_ne :
      hpair.rightCoeff F hax hs r q ≠ 0 :=
    ne_of_gt (hpair.rightCoeff_pos F hax hs r q hr hq)
  field_simp [hleft_ne, hright_ne, hswapped_right_ne]

/--
Singleton coefficient swap normalization. When one coordinate is singleton, the
corresponding value representative is identically zero, so the swap coefficient
comparison cannot be extracted from value variation. These equations are
therefore classified with the singleton/gauge normalizations rather than as
nondegenerate coefficient extraction.
-/
structure FiniteProductLinearCoeffSwapSingletonNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  rho_reciprocity_of_subsingleton_left :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton A →
      linearCoeffRho hpair F hax hs q r *
          linearCoeffRho hpair F hax hs r q =
        1
  rho_reciprocity_of_subsingleton_right :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton B →
      linearCoeffRho hpair F hax hs q r *
          linearCoeffRho hpair F hax hs r q =
        1

/-- Reconstruct the old swap/rho reciprocity package from the internally
proved nondegenerate swap extraction and the remaining singleton normalization. -/
theorem productLinearCoeffSwap_of_valueSwap_and_singletonNormalization
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hsingle :
      FiniteProductLinearCoeffSwapSingletonNormalizationAssumptions.{u} hpair) :
    FiniteProductLinearCoeffSwapAssumptions.{u} hpair where
  rho_reciprocity := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    by_cases hsubA : Subsingleton A
    · exact hsingle.rho_reciprocity_of_subsingleton_left
        F hax hs q r hq hr hsubA
    · by_cases hsubB : Subsingleton B
      · exact hsingle.rho_reciprocity_of_subsingleton_right
          F hax hs q r hq hr hsubB
      · exact linearCoeffRho_reciprocity_of_value_swap_nondegenerate
          hrelV hpair F hax hs q r hq hr hsubA hsubB

/--
The remaining Step 3 gauge-choice bridge. The paper proves that after choosing
a positive reference-prior gauge and rescaling the zero-normalized
representatives, the current representatives may be taken to satisfy
`A_{p,r}=B_{p,r}=1`. Lean currently has no operation that replaces the
`PosteriorValueRepresentation` inside `ScaleCoherenceStructure` by a positively
rescaled coherent representative, so this record isolates exactly that
chosen-normal-gauge statement.
-/
structure FiniteProductPositiveGaugeChoiceAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  current_leftCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff F hax hs q r = 1
  current_rightCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff F hax hs q r = 1

/-- The paper's coefficient transformation law for the left linear coefficient
under a positive prior-dependent rescaling `F_q^* = φ(q) F_q`. -/
noncomputable def gaugeTransformedLeftCoeff
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (gauge : ∀ (F : PrefFamily.{u}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A : Type u} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.leftCoeff F hax hs q r *
    (gauge F hax hs (prodDist q r) / gauge F hax hs q)

/-- The paper's coefficient transformation law for the right linear coefficient
under a positive prior-dependent rescaling `F_q^* = φ(q) F_q`. -/
noncomputable def gaugeTransformedRightCoeff
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (gauge : ∀ (F : PrefFamily.{u}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A : Type u} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.rightCoeff F hax hs q r *
    (gauge F hax hs (prodDist q r) / gauge F hax hs r)

/--
Reference-gauge transform package for paper Step 3. This records the positive
gauge `φ` and the fact that the coefficients obtained after applying the
paper's transform law are normalized. It does not by itself replace the
`PosteriorValueRepresentation` stored inside `ScaleCoherenceStructure`.
-/
structure FiniteProductReferenceGaugeTransformAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  gauge :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A : Type v} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ
  gauge_pos :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      0 < gauge F hax hs q
  transformed_leftCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      gaugeTransformedLeftCoeff hpair gauge F hax hs q r = 1
  transformed_rightCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      gaugeTransformedRightCoeff hpair gauge F hax hs q r = 1

/--
Representative-choice normalization connecting the paper's transformed
coefficients to the current Lean representatives. Since the current code does
not implement a new `ScaleCoherenceStructure` with rescaled `V`, this says the
currently selected representatives are the post-gauge representatives.
-/
structure FiniteCurrentRepresentativesGaugeNormalizedAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v})
    (hgauge : FiniteProductReferenceGaugeTransformAssumptions.{v} hpair) where
  current_leftCoeff_eq_transformed :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff F hax hs q r =
        gaugeTransformedLeftCoeff hpair hgauge.gauge F hax hs q r
  current_rightCoeff_eq_transformed :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff F hax hs q r =
        gaugeTransformedRightCoeff hpair hgauge.gauge F hax hs q r

end TraceableAgency
