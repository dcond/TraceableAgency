/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence.FaceScales

namespace TraceableAgency

universe u

/-!
## Interaction collapse and universal chain scale

The next named paper result starts from coherent face scales and proves two
things: the product interaction coefficient vanishes, and the prior-dependent
chain scale is actually universal.  This section gives a faithful pre-entropy
API for that result, split into the paper's product-revelation and two-grouping
subclaims rather than using the old all-in-one `FiniteScaleCoherenceAssumptions`
monolith.
-/

/-- Full-revelation value `H(q)` used in the scale-coherence proof, stated
against the faithful face-scale package. -/
noncomputable def fullRevelationValueForFaceScales
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  hfaces.branch_result.branch_agg.value_rep.V q
    (experimentOfChannel (Channel.idChannel : Channel A A))

/-- Coherent product quasi-additivity stated against the pre-universal
face-scale package.

This is the product formula from the earlier coherent-product result, but its
signature avoids requiring `ScaleCoherenceStructure` as an input. -/
structure FiniteProductQuasiAdditivityForFaceScales.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) where
  kappa : PureTraceConditions F → ℝ
  product_quasi_add :
    ∀ (hax : PureTraceConditions F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) +
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) +
        kappa hax *
          hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) *
          hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Face-scale-level first-coordinate slice affinity.

This is the pre-universal analogue of the Stage 10 left-slice affine package:
for fixed second-coordinate channel `R`, the product value is affine in the
first-coordinate value. -/
structure FiniteFaceScaleProductLeftSliceAffineAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) where
  leftSliceSlope :
    PureTraceConditions F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftSliceIntercept :
    PureTraceConditions F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  left_slice_affine :
    ∀ (hax : PureTraceConditions F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftSliceSlope hax q r R *
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) +
        leftSliceIntercept hax q r R

/-- Face-scale-level intercept identification in the second-coordinate value.
-/
structure FiniteFaceScaleProductSliceInterceptAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) where
  rightCoeff :
    PureTraceConditions F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff_pos :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff hax q r
  leftSliceIntercept_value :
    ∀ (hax : PureTraceConditions F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      hslice.leftSliceIntercept hax q r R =
        rightCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R)

/-- Face-scale-level slope identification in the second-coordinate value. -/
structure FiniteFaceScaleProductSliceSlopeAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) where
  leftCoeff :
    PureTraceConditions F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    PureTraceConditions F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff hax q r
  leftSliceSlope_value :
    ∀ (hax : PureTraceConditions F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A)
      (R : Channel B Y),
      hslice.leftSliceSlope hax q r R =
        leftCoeff hax q r +
          interactionCoeff hax q r *
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R)

/-- Product left-slice value in the pre-universal face-scale structure. -/
noncomputable def faceScaleProductLeftSliceValue
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B Y O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (R : Channel B Y) (P : Channel A O) : ℝ :=
  hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Face-scale product left-slice base-value public-mixture affinity. -/
structure FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  base_value_publicMix_affine :
    ∀ (_hax : PureTraceConditions F)
      {A O Z : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
        t * hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) +
        (1 - t) * hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel Q)

/-- Face-scale product left-slice public-mixture affinity in the first
coordinate. -/
structure FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  left_slice_publicMix_affine :
    ∀ (_hax : PureTraceConditions F)
      {A B O Z Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      faceScaleProductLeftSliceValue hfaces q r R
          (publicMixChannel t ht0 ht1 P Q) =
        t * faceScaleProductLeftSliceValue hfaces q r R P +
        (1 - t) * faceScaleProductLeftSliceValue hfaces q r R Q

/-- Face-scale product left-slice order identification with the base
first-coordinate order. -/
structure FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  left_slice_same_order :
    ∀ (_hax : PureTraceConditions F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y) (P Q : Channel A O),
      faceScaleProductLeftSliceValue hfaces q r R P ≥
          faceScaleProductLeftSliceValue hfaces q r R Q ↔
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) ≥
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel Q)

/-- Face-scale base-value nonconstancy for non-singleton full-support priors. -/
structure FiniteFaceScaleBaseValueNonconstancyAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  base_value_nonconstant :
    ∀ (_hax : PureTraceConditions F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hA : ¬ Subsingleton A),
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))

/-- Singleton first-coordinate slice affine normalization.  This covers the
degenerate case where the first-coordinate value domain cannot identify a
positive slope from comparisons. -/
structure FiniteFaceScaleSingletonSliceAffineAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  singleton_left_slice_positive_affine_transform :
    ∀ (_hax : PureTraceConditions F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : Subsingleton A) (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          faceScaleProductLeftSliceValue hfaces q r R P =
            a * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) + b

/-- Classical affine-utility uniqueness specialized to face-scale product
left slices. -/
structure ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  positive_affine_transform :
    ∀ (_hax : PureTraceConditions F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (R : Channel B Y),
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
          t * hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) +
            (1 - t) * hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel Q)) →
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        faceScaleProductLeftSliceValue hfaces q r R
            (publicMixChannel t ht0 ht1 P Q) =
          t * faceScaleProductLeftSliceValue hfaces q r R P +
            (1 - t) * faceScaleProductLeftSliceValue hfaces q r R Q) →
      (hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))) →
      (∀ {O : Type v} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        faceScaleProductLeftSliceValue hfaces q r R P ≥
            faceScaleProductLeftSliceValue hfaces q r R Q ↔
          hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) ≥
            hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel Q)) →
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          faceScaleProductLeftSliceValue hfaces q r R P =
            a * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) + b

/-- The precise affine-transform output behind
`FiniteFaceScaleProductLeftSliceAffineAssumptionsFor`. -/
structure FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  left_slice_positive_affine_transform :
    ∀ (_hax : PureTraceConditions F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          faceScaleProductLeftSliceValue hfaces q r R P =
            a * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) + b

/-- Reconstruct the face-scale affine-transform package from the product
mixture/order/nonconstancy pieces and the classical affine-utility theorem. -/
theorem faceScaleProductLeftSliceAffineTransform_of_parts
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hnonconst :
      FiniteFaceScaleBaseValueNonconstancyAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq :
      ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor hfaces) :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces where
  left_slice_positive_affine_transform := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    by_cases hsub : Subsingleton A
    · exact hsingle.singleton_left_slice_positive_affine_transform
        hax q r hq hr hsub R
    · exact
        huniq.positive_affine_transform hax q r hq hr hsub R
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact hbaseAff.base_value_publicMix_affine
              hax q hq t ht0 ht1 P Q)
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact hsliceAff.left_slice_publicMix_affine
              hax q r hq hr R t ht0 ht1 P Q)
          (hnonconst.base_value_nonconstant hax q hq hsub)
          (by
            intro O _ _ P Q
            exact hsameOrder.left_slice_same_order hax q r hq hr R P Q)

noncomputable def faceScaleAffineSliceTransformSlope
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (haff.left_slice_positive_affine_transform hax q r h.1 h.2 R)
    else 0

noncomputable def faceScaleAffineSliceTransformIntercept
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform hax q r h.1 h.2 R))
    else 0

/-- The chosen slice-transform slope is strictly positive at full-support
priors: it is the multiplier `a` of a positive affine transform.  This is the
Lean form of the paper's positive-slice-slope condition (Lemma coherentnorm,
`α(ν) > 0`), from which POS follows. -/
theorem faceScaleAffineSliceTransformSlope_pos
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    0 < faceScaleAffineSliceTransformSlope haff hax q r R := by
  classical
  have hcond : q.FullSupport ∧ r.FullSupport := ⟨hq, hr⟩
  have hpos :=
    (Classical.choose_spec
      (Classical.choose_spec
        (haff.left_slice_positive_affine_transform hax q r hq hr R))).1
  simpa [faceScaleAffineSliceTransformSlope, hcond] using hpos

/-- Reconstruct face-scale left-slice affinity from the exact
positive-affine-transform output. -/
noncomputable def faceScaleProductLeftSliceAffine_of_transform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces) :
    FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces where
  leftSliceSlope := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r R
    exact faceScaleAffineSliceTransformSlope haff hax q r R
  leftSliceIntercept := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r R
    exact faceScaleAffineSliceTransformIntercept haff hax q r R
  left_slice_affine := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    classical
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform
            hax q r hq hr R))).2 (P := P)
    simpa [faceScaleProductLeftSliceValue, faceScaleAffineSliceTransformSlope,
      faceScaleAffineSliceTransformIntercept, hq, hr] using hspec

/-- Face-scale second-coordinate intercept positive-linearity theorem. -/
structure FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_positive_linear :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceIntercept hax q r R =
            Bcoeff * hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R)

/-- Face-scale intercept same-order condition. -/
structure FiniteFaceScaleProductInterceptSameOrderAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_same_order :
    ∀ (hax : PureTraceConditions F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R S : Channel B Y),
      hslice.leftSliceIntercept hax q r R ≥
          hslice.leftSliceIntercept hax q r S ↔
        hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) ≥
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel S)

/-- Face-scale intercept public-mixture affinity. -/
structure FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_publicMix_affine :
    ∀ (hax : PureTraceConditions F)
      {A B Y Z : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      [Fintype Z] [DecidableEq Z]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (R : Channel B Y) (S : Channel B Z),
      hslice.leftSliceIntercept hax q r
          (publicMixChannel t ht0 ht1 R S) =
        t * hslice.leftSliceIntercept hax q r R +
        (1 - t) * hslice.leftSliceIntercept hax q r S

/-- The universe-polymorphic uninformative channel has zero value under the
chosen posterior-value representative. -/
theorem V_uninformativeChannelU_eq_zero
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
  hV.zero_normalized q hq

/-- If a channel has a subsingleton outcome type, its posterior law evaluates
as the prior itself. -/
theorem posteriorLawIntegralExp_subsingleton_outcome
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Nonempty O] [Subsingleton O]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (experimentOfChannel P) φ = φ q := by
  obtain ⟨o₀⟩ : Nonempty O := inferInstance
  have huniq : ∀ o : O, o = o₀ := fun o => Subsingleton.elim o o₀
  have hP_o₀ : ∀ a : A, (P a).prob o₀ = 1 := by
    intro a
    have hsum := (P a).sum_eq_one
    rw [show (∑ o : O, (P a).prob o) = (P a).prob o₀ from
      Finset.sum_eq_single o₀ (fun b _ hb => absurd (huniq b) hb)
        (fun h => absurd (Finset.mem_univ o₀) h)] at hsum
    exact hsum
  have hmarg : (Channel.outcomeMarginal P q).prob o₀ = 1 := by
    simp only [Channel.outcomeMarginal_apply, hP_o₀, mul_one]
    exact q.sum_eq_one
  have hmarg_pos : (0 : ℝ) < (Channel.outcomeMarginal P q).prob o₀ := by
    rw [hmarg]
    exact one_pos
  have hpost : Channel.posterior P q o₀ = q := by
    unfold Channel.posterior
    rw [dif_pos hmarg_pos]
    ext a
    simp only [Channel.outcomeMarginal_apply, hP_o₀, mul_one]
    simp [q.sum_eq_one]
  unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
  simp only [FiniteExperimentOn.outcomeMarginal, FiniteExperimentOn.posterior]
  rw [show (∑ o : O, (Channel.outcomeMarginal P q).prob o *
      φ (Channel.posterior P q o)) =
      (Channel.outcomeMarginal P q).prob o₀ *
        φ (Channel.posterior P q o₀) from
    Finset.sum_eq_single o₀ (fun b _ hb => absurd (huniq b) hb)
      (fun h => absurd (Finset.mem_univ o₀) h)]
  rw [hmarg, hpost, one_mul]

/-- A channel with a subsingleton outcome type has zero value under the
zero-normalised posterior-value representative. -/
theorem V_eq_zero_of_subsingleton_outcome
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Nonempty O] [Subsingleton O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    hV.V q (experimentOfChannel P) = 0 := by
  have hsameLaw : SamePosteriorLawExp q
      (experimentOfChannel P)
      (experimentOfChannel (Channel.uninformativeChannelU A)) := by
    intro φ _hcont
    rw [posteriorLawIntegralExp_subsingleton_outcome q P φ]
    have hU :
        posteriorLawIntegralExp q
          (experimentOfChannel (Channel.uninformativeChannelU A)) φ = φ q :=
      posteriorLawIntegralExp_subsingleton_outcome q
        (Channel.uninformativeChannelU A) φ
    rw [hU]
  rw [hV.respects_same_posterior_law q _ _ hsameLaw]
  exact hV.zero_normalized q hq

/-- Face-scale intercept zero-normalisation at the no-information channel. -/
structure FiniteFaceScaleProductInterceptZeroAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_uninformative_eq_zero :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hslice.leftSliceIntercept hax q r
        (Channel.uninformativeChannelU B) = 0

/-- The left-slice intercept is the product value at the first-coordinate
no-information channel. -/
theorem faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hslice.leftSliceIntercept hax q r R =
      faceScaleProductLeftSliceValue hfaces q r R
        (Channel.uninformativeChannelU A) := by
  have hslice_eq :=
    hslice.left_slice_affine hax q r hq hr
      (Channel.uninformativeChannelU A) R
  have hzero :
      hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  rw [hzero, mul_zero, zero_add] at hslice_eq
  exact hslice_eq.symm

/-- Intercept zero-normalisation follows internally from the slice-affine
identity and subsingleton-outcome zero-normalisation. -/
theorem faceScaleProductInterceptZero_of_sliceAffine
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptZeroAssumptionsFor hslice where
  intercept_uninformative_eq_zero := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr (Channel.uninformativeChannelU B)]
    exact V_eq_zero_of_subsingleton_outcome F
      hfaces.branch_result.branch_agg.value_rep
      (prodDist q r) (prodDist_fullSupport q r hq hr)
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B))

/-- Single source-ready finite affine-utility uniqueness theorem.

This is the generic classical statement used by both the first-coordinate
left-slice affine transform and the second-coordinate intercept normalization:
if two public-mixture affine real representatives on the same finite
experiment domain induce the same weak order and the base representative is
nonconstant, then the second representative is a positive affine transform of
the base. -/
structure ClassicalFiniteAffineUtilityUniquenessAssumptions.{v} : Prop where
  positive_affine_transform :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (base target :
        {O : Type v} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ),
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        base (publicMixChannel t ht0 ht1 P Q) =
          t * base P + (1 - t) * base Q) →
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        target (publicMixChannel t ht0 ht1 P Q) =
          t * target P + (1 - t) * target Q) →
      (base (Channel.idChannel : Channel A A) ≠
        base (Channel.uninformativeChannelU A)) →
      (∀ {O : Type v} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        target P ≥ target Q ↔ base P ≥ base Q) →
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O), target P = a * base P + b

private theorem affineUtility_value_eq_of_cross
    {bi bu ti tu x y : ℝ}
    (hden : bi - bu ≠ 0)
    (hcross : (bi - bu) * y + (bu - x) * ti + (x - bi) * tu = 0) :
    y = ((ti - tu) / (bi - bu)) * x +
      (tu - ((ti - tu) / (bi - bu)) * bu) := by
  field_simp [hden]
  nlinarith [hcross]

/-- Finite public-mixture affine utility uniqueness.

The proof uses only the hypotheses exposed in
`ClassicalFiniteAffineUtilityUniquenessAssumptions`: public-mixture affinity,
nonconstancy of the identity/no-information anchors, and same weak order on
each common outcome type.  Cross-outcome comparisons are obtained by embedding
any channel and the two anchors into a common three-arm public mixture. -/
theorem classicalFiniteAffineUtilityUniquenessAssumptions :
    ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} where
  positive_affine_transform := by
    intro A _ _ _ base target hbaseAff htargetAff hnonconst horder
    classical
    let I : Channel A A := Channel.idChannel
    let U : Channel A PUnit.{u+1} := Channel.uninformativeChannelU A
    let bi : ℝ := base I
    let bu : ℝ := base U
    let ti : ℝ := target I
    let tu : ℝ := target U
    let Δ : ℝ := bi - bu
    have hΔ_ne : Δ ≠ 0 := by
      dsimp [Δ, bi, bu, I, U]
      exact sub_ne_zero.mpr hnonconst
    have two_thirds_pos : (0 : ℝ) < (2 / 3 : ℝ) := by norm_num
    have two_thirds_lt_one : (2 / 3 : ℝ) < 1 := by norm_num
    have one_third_pos : (0 : ℝ) < (1 / 3 : ℝ) := by norm_num
    have one_third_lt_one : (1 / 3 : ℝ) < 1 := by norm_num
    let Mhi : Channel A (A ⊕ PUnit.{u+1}) :=
      publicMixChannel (2 / 3 : ℝ) two_thirds_pos two_thirds_lt_one I U
    let Mlo : Channel A (A ⊕ PUnit.{u+1}) :=
      publicMixChannel (1 / 3 : ℝ) one_third_pos one_third_lt_one I U
    have hbase_hi :
        base Mhi = (2 / 3 : ℝ) * bi + (1 / 3 : ℝ) * bu := by
      change base (publicMixChannel (2 / 3 : ℝ)
          two_thirds_pos two_thirds_lt_one I U) =
        (2 / 3 : ℝ) * bi + (1 / 3 : ℝ) * bu
      rw [hbaseAff (O := A) (Z := PUnit.{u+1})
        (2 / 3 : ℝ) two_thirds_pos two_thirds_lt_one I U]
      dsimp [bi, bu]
      norm_num
    have hbase_lo :
        base Mlo = (1 / 3 : ℝ) * bi + (2 / 3 : ℝ) * bu := by
      change base (publicMixChannel (1 / 3 : ℝ)
          one_third_pos one_third_lt_one I U) =
        (1 / 3 : ℝ) * bi + (2 / 3 : ℝ) * bu
      rw [hbaseAff (O := A) (Z := PUnit.{u+1})
        (1 / 3 : ℝ) one_third_pos one_third_lt_one I U]
      dsimp [bi, bu]
      norm_num
    have htarget_hi :
        target Mhi = (2 / 3 : ℝ) * ti + (1 / 3 : ℝ) * tu := by
      change target (publicMixChannel (2 / 3 : ℝ)
          two_thirds_pos two_thirds_lt_one I U) =
        (2 / 3 : ℝ) * ti + (1 / 3 : ℝ) * tu
      rw [htargetAff (O := A) (Z := PUnit.{u+1})
        (2 / 3 : ℝ) two_thirds_pos two_thirds_lt_one I U]
      dsimp [ti, tu]
      norm_num
    have htarget_lo :
        target Mlo = (1 / 3 : ℝ) * ti + (2 / 3 : ℝ) * tu := by
      change target (publicMixChannel (1 / 3 : ℝ)
          one_third_pos one_third_lt_one I U) =
        (1 / 3 : ℝ) * ti + (2 / 3 : ℝ) * tu
      rw [htargetAff (O := A) (Z := PUnit.{u+1})
        (1 / 3 : ℝ) one_third_pos one_third_lt_one I U]
      dsimp [ti, tu]
      norm_num
    have hslope_pos : 0 < (ti - tu) / (bi - bu) := by
      rcases lt_or_gt_of_ne hΔ_ne with hΔ_neg | hΔ_pos
      · have hb_lt : base Mhi < base Mlo := by
          rw [hbase_hi, hbase_lo]
          dsimp [Δ, bi, bu] at hΔ_neg
          nlinarith
        have ht_not_ge : ¬ target Mhi ≥ target Mlo := by
          intro hge
          have hbase_ge : base Mhi ≥ base Mlo :=
            (horder Mhi Mlo).1 hge
          linarith
        have ht_lt : target Mhi < target Mlo := not_le.mp ht_not_ge
        have hti_lt : ti < tu := by
          rw [htarget_hi, htarget_lo] at ht_lt
          nlinarith
        have hnum_pos : 0 < -(ti - tu) := by linarith
        have hden_pos : 0 < -(bi - bu) := by
          dsimp [Δ, bi, bu] at hΔ_neg
          linarith
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
      · have hb_gt : base Mhi > base Mlo := by
          rw [hbase_hi, hbase_lo]
          dsimp [Δ, bi, bu] at hΔ_pos
          nlinarith
        have ht_not_ge : ¬ target Mlo ≥ target Mhi := by
          intro hge
          have hbase_ge : base Mlo ≥ base Mhi :=
            (horder Mlo Mhi).1 hge
          linarith
        have ht_gt : target Mhi > target Mlo := not_le.mp ht_not_ge
        have hti_gt : ti > tu := by
          rw [htarget_hi, htarget_lo] at ht_gt
          nlinarith
        exact div_pos (by linarith) (by
          dsimp [Δ, bi, bu] at hΔ_pos
          exact hΔ_pos)
    refine ⟨(ti - tu) / (bi - bu),
      tu - ((ti - tu) / (bi - bu)) * bu, hslope_pos, ?_⟩
    intro O _ _ P
    let x : ℝ := base P
    let y : ℝ := target P
    let cP : ℝ := bi - bu
    let cI : ℝ := bu - x
    let cU : ℝ := x - bi
    let K : ℝ := |cP| + |cI| + |cU| + 1
    let S : ℝ := 3 * K
    have hc_sum : cP + cI + cU = 0 := by
      dsimp [cP, cI, cU]
      ring
    have hK_pos : 0 < K := by
      have hnonneg : 0 ≤ |cP| + |cI| + |cU| := by positivity
      dsimp [K]
      linarith
    have hS_pos : 0 < S := by
      dsimp [S]
      positivity
    have hKcP_pos : 0 < K + cP := by
      have hlt : -cP < K := by
        dsimp [K]
        linarith [neg_le_abs cP, abs_nonneg cI, abs_nonneg cU]
      linarith
    have hKcI_pos : 0 < K + cI := by
      have hlt : -cI < K := by
        dsimp [K]
        linarith [neg_le_abs cI, abs_nonneg cP, abs_nonneg cU]
      linarith
    have hKcU_pos : 0 < K + cU := by
      have hlt : -cU < K := by
        dsimp [K]
        linarith [neg_le_abs cU, abs_nonneg cP, abs_nonneg cI]
      linarith
    let α : ℝ := (K + cP) / S
    let β : ℝ := (K + cI) / S
    let γ : ℝ := (K + cU) / S
    let α₀ : ℝ := K / S
    let β₀ : ℝ := K / S
    let γ₀ : ℝ := K / S
    have hα_pos : 0 < α := by
      dsimp [α]
      exact div_pos hKcP_pos hS_pos
    have hβ_pos : 0 < β := by
      dsimp [β]
      exact div_pos hKcI_pos hS_pos
    have hγ_pos : 0 < γ := by
      dsimp [γ]
      exact div_pos hKcU_pos hS_pos
    have hα₀_pos : 0 < α₀ := by
      dsimp [α₀]
      exact div_pos hK_pos hS_pos
    have hβ₀_pos : 0 < β₀ := by
      dsimp [β₀]
      exact div_pos hK_pos hS_pos
    have hγ₀_pos : 0 < γ₀ := by
      dsimp [γ₀]
      exact div_pos hK_pos hS_pos
    have hsum : α + β + γ = 1 := by
      dsimp [α, β, γ, S]
      field_simp [ne_of_gt hK_pos]
      nlinarith [hc_sum]
    have hsum₀ : α₀ + β₀ + γ₀ = 1 := by
      dsimp [α₀, β₀, γ₀, S]
      field_simp [ne_of_gt hK_pos]
      ring
    have three_base :
        ∀ {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
          (hsum : α + β + γ = 1),
          base
            (publicMixChannel α hα (by linarith)
              P
              (publicMixChannel (β / (β + γ))
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  exact div_pos hβ hden_pos)
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  have hlt : β < β + γ := by linarith
                  exact (div_lt_one hden_pos).2 hlt)
                I U)) =
            α * x + β * bi + γ * bu := by
      intro α β γ hα hβ hγ hsum
      have hα_lt : α < 1 := by linarith
      have hden_pos : 0 < β + γ := by positivity
      have hden_ne : β + γ ≠ 0 := ne_of_gt hden_pos
      have hone_sub : 1 - α = β + γ := by linarith
      rw [hbaseAff α hα hα_lt]
      rw [hbaseAff (β / (β + γ))
        (by exact div_pos hβ hden_pos)
        (by
          have hlt : β < β + γ := by linarith
          exact (div_lt_one hden_pos).2 hlt)]
      dsimp [x, bi, bu, I, U]
      rw [hone_sub]
      have hcoefβ : (β + γ) * (β / (β + γ)) = β := by
        field_simp [hden_ne]
      have hcoefγ : (β + γ) * (1 - β / (β + γ)) = γ := by
        field_simp [hden_ne]
        ring
      calc
        α * base P +
            (β + γ) *
              (β / (β + γ) * base Channel.idChannel +
                (1 - β / (β + γ)) * base (Channel.uninformativeChannelU A)) =
            α * base P +
              ((β + γ) * (β / (β + γ))) * base Channel.idChannel +
              ((β + γ) * (1 - β / (β + γ))) *
                base (Channel.uninformativeChannelU A) := by
          ring
        _ = α * base P + β * base Channel.idChannel +
              γ * base (Channel.uninformativeChannelU A) := by
          rw [hcoefβ, hcoefγ]
    have three_target :
        ∀ {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
          (hsum : α + β + γ = 1),
          target
            (publicMixChannel α hα (by linarith)
              P
              (publicMixChannel (β / (β + γ))
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  exact div_pos hβ hden_pos)
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  have hlt : β < β + γ := by linarith
                  exact (div_lt_one hden_pos).2 hlt)
                I U)) =
            α * y + β * ti + γ * tu := by
      intro α β γ hα hβ hγ hsum
      have hα_lt : α < 1 := by linarith
      have hden_pos : 0 < β + γ := by positivity
      have hden_ne : β + γ ≠ 0 := ne_of_gt hden_pos
      have hone_sub : 1 - α = β + γ := by linarith
      rw [htargetAff α hα hα_lt]
      rw [htargetAff (β / (β + γ))
        (by exact div_pos hβ hden_pos)
        (by
          have hlt : β < β + γ := by linarith
          exact (div_lt_one hden_pos).2 hlt)]
      dsimp [y, ti, tu, I, U]
      rw [hone_sub]
      have hcoefβ : (β + γ) * (β / (β + γ)) = β := by
        field_simp [hden_ne]
      have hcoefγ : (β + γ) * (1 - β / (β + γ)) = γ := by
        field_simp [hden_ne]
        ring
      calc
        α * target P +
            (β + γ) *
              (β / (β + γ) * target Channel.idChannel +
                (1 - β / (β + γ)) * target (Channel.uninformativeChannelU A)) =
            α * target P +
              ((β + γ) * (β / (β + γ))) * target Channel.idChannel +
              ((β + γ) * (1 - β / (β + γ))) *
                target (Channel.uninformativeChannelU A) := by
          ring
        _ = α * target P + β * target Channel.idChannel +
              γ * target (Channel.uninformativeChannelU A) := by
          rw [hcoefβ, hcoefγ]
    have hbase_weight :
        α * x + β * bi + γ * bu =
          α₀ * x + β₀ * bi + γ₀ * bu := by
      dsimp [α, β, γ, α₀, β₀, γ₀, S]
      field_simp [ne_of_gt hK_pos]
      dsimp [cP, cI, cU]
      ring
    let T₁ : Channel A (O ⊕ (A ⊕ PUnit.{u+1})) :=
      publicMixChannel α hα_pos (by linarith)
        P
        (publicMixChannel (β / (β + γ))
          (by
            have hden_pos : 0 < β + γ := by linarith
            exact div_pos hβ_pos hden_pos)
          (by
            have hden_pos : 0 < β + γ := by linarith
            have hlt : β < β + γ := by linarith
            exact (div_lt_one hden_pos).2 hlt)
          I U)
    let T₀ : Channel A (O ⊕ (A ⊕ PUnit.{u+1})) :=
      publicMixChannel α₀ hα₀_pos (by linarith)
        P
        (publicMixChannel (β₀ / (β₀ + γ₀))
          (by
            have hden_pos : 0 < β₀ + γ₀ := by linarith
            exact div_pos hβ₀_pos hden_pos)
          (by
            have hden_pos : 0 < β₀ + γ₀ := by linarith
            have hlt : β₀ < β₀ + γ₀ := by linarith
            exact (div_lt_one hden_pos).2 hlt)
          I U)
    have hbase_T₁ : base T₁ = α * x + β * bi + γ * bu := by
      simpa [T₁] using three_base hα_pos hβ_pos hγ_pos hsum
    have hbase_T₀ : base T₀ = α₀ * x + β₀ * bi + γ₀ * bu := by
      simpa [T₀] using three_base hα₀_pos hβ₀_pos hγ₀_pos hsum₀
    have htarget_T₁ : target T₁ = α * y + β * ti + γ * tu := by
      simpa [T₁] using three_target hα_pos hβ_pos hγ_pos hsum
    have htarget_T₀ : target T₀ = α₀ * y + β₀ * ti + γ₀ * tu := by
      simpa [T₀] using three_target hα₀_pos hβ₀_pos hγ₀_pos hsum₀
    have hbase_T_eq : base T₁ = base T₀ := by
      rw [hbase_T₁, hbase_T₀]
      exact hbase_weight
    have htarget_T_eq : target T₁ = target T₀ := by
      apply le_antisymm
      · exact (horder T₀ T₁).2 (by rw [hbase_T_eq])
      · exact (horder T₁ T₀).2 (by rw [hbase_T_eq])
    have htarget_weight :
        α * y + β * ti + γ * tu =
          α₀ * y + β₀ * ti + γ₀ * tu := by
      rw [← htarget_T₁, ← htarget_T₀]
      exact htarget_T_eq
    have hlinear : cP * y + cI * ti + cU * tu = 0 := by
      have hscaled :
          (K + cP) * y + (K + cI) * ti + (K + cU) * tu =
            K * y + K * ti + K * tu := by
        have hmul := congrArg (fun z : ℝ => S * z) htarget_weight
        dsimp [α, β, γ, α₀, β₀, γ₀] at hmul
        field_simp [ne_of_gt hS_pos] at hmul
        calc
          (K + cP) * y + (K + cI) * ti + (K + cU) * tu =
              K * (y + ti + tu) := hmul
          _ = K * y + K * ti + K * tu := by ring
      calc
        cP * y + cI * ti + cU * tu =
            ((K + cP) * y + (K + cI) * ti + (K + cU) * tu) -
              (K * y + K * ti + K * tu) := by
          ring
        _ = 0 := by rw [hscaled]; ring
    have hcross :
        (bi - bu) * y + (bu - x) * ti + (x - bi) * tu = 0 := by
      simpa [cP, cI, cU] using hlinear
    have hden : bi - bu ≠ 0 := by
      dsimp [bi, bu, I, U]
      exact sub_ne_zero.mpr hnonconst
    have hy_eq :
        y = ((ti - tu) / (bi - bu)) * x +
          (tu - ((ti - tu) / (bi - bu)) * bu) := by
      exact affineUtility_value_eq_of_cross hden hcross
    simpa [x, y, bi, bu, ti, tu] using hy_eq

/-- The face-scale first-coordinate affine-utility uniqueness package is an
instance of the single classical finite affine-utility uniqueness theorem. -/
theorem classicalFaceScaleAffineUtilityUniqueness_of_finiteAffineUtility
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor hfaces where
  positive_affine_transform := by
    intro _hax A B Y _ _ _ _ _ _ _ _ q r _hq _hr _hA R
      hbaseAff htargetAff hnonconst horder
    let base :
        {O : Type u} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ :=
      fun {O} [Fintype O] [DecidableEq O] P =>
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P)
    let target :
        {O : Type u} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ :=
      fun {O} [Fintype O] [DecidableEq O] P =>
        faceScaleProductLeftSliceValue hfaces q r R P
    exact
      huniq.positive_affine_transform base target
        (by
          intro O Z _ _ _ _ t ht0 ht1 P Q
          exact hbaseAff t ht0 ht1 P Q)
        (by
          intro O Z _ _ _ _ t ht0 ht1 P Q
          exact htargetAff t ht0 ht1 P Q)
        hnonconst
        (by
          intro O _ _ P Q
          exact horder P Q)

/-- Classical second-coordinate affine uniqueness for the face-scale intercept
functional. -/
structure ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  positive_linear_of_same_order_affine_zero :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      (∀ {Y Z : Type v} [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (R : Channel B Y) (S : Channel B Z),
        hslice.leftSliceIntercept hax q r
            (publicMixChannel t ht0 ht1 R S) =
          t * hslice.leftSliceIntercept hax q r R +
          (1 - t) * hslice.leftSliceIntercept hax q r S) →
      (∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
        (R S : Channel B Y),
        hslice.leftSliceIntercept hax q r R ≥
            hslice.leftSliceIntercept hax q r S ↔
          hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) ≥
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel S)) →
      hslice.leftSliceIntercept hax q r
        (Channel.uninformativeChannelU B) = 0 →
      ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceIntercept hax q r R =
            Bcoeff * hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R)

/-- Reconstruct intercept positive-linearity from same-order, affinity,
zero-normalisation, and classical affine uniqueness. -/
theorem faceScaleProductInterceptPositiveLinear_of_parts
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (horder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor hslice)
    (haff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice)
    (hzero :
      FiniteFaceScaleProductInterceptZeroAssumptionsFor hslice)
    (huniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor hslice) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice where
  intercept_positive_linear := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact huniq.positive_linear_of_same_order_affine_zero
      hax q r hq hr
      (by
        intro Y Z _ _ _ _ t ht0 ht1 R S
        exact haff.intercept_publicMix_affine
          hax q r hq hr t ht0 ht1 R S)
      (by
        intro Y _ _ R S
        exact horder.intercept_same_order hax q r hq hr R S)
      (hzero.intercept_uninformative_eq_zero hax q r hq hr)

/-- Reconstruct intercept positive-linearity without an external intercept-zero
assumption.  The zero-normalisation is internal from `hslice`. -/
theorem faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (horder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor hslice)
    (haff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice)
    (huniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor hslice) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice :=
  faceScaleProductInterceptPositiveLinear_of_parts
    horder haff (faceScaleProductInterceptZero_of_sliceAffine hslice) huniq

noncomputable def faceScaleInterceptRightCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hlin :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose (hlin.intercept_positive_linear hax q r h.1 h.2)
    else 1

/-- Reconstruct the face-scale intercept package from the exact
positive-linearity output. -/
noncomputable def faceScaleProductSliceIntercept_of_positiveLinear
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hlin :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice) :
    FiniteFaceScaleProductSliceInterceptAssumptionsFor hslice where
  rightCoeff := by
    intro hax A B _ _ _ _ _ _ q r
    exact faceScaleInterceptRightCoeff hlin hax q r
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    classical
    have hpos :=
      (Classical.choose_spec
        (hlin.intercept_positive_linear hax q r hq hr)).1
    simpa [faceScaleInterceptRightCoeff, hq, hr] using hpos
  leftSliceIntercept_value := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hspec :=
      (Classical.choose_spec
        (hlin.intercept_positive_linear hax q r hq hr)).2 (R := R)
    simpa [faceScaleInterceptRightCoeff, hq, hr] using hspec

/-- Exact face-scale slope-affine output behind the slice-slope package. -/
structure FiniteFaceScaleProductSlopeAffineAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  slope_affine_in_second_value :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A),
      ∃ Acoeff Ccoeff : ℝ, 0 < Acoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceSlope hax q r R =
            Acoeff +
              Ccoeff * hfaces.branch_result.branch_agg.value_rep.V r
                (experimentOfChannel R)

noncomputable def faceScaleSlopeLeftCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (haff : FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A then
      Classical.choose
        (haff.slope_affine_in_second_value hax q r h.1 h.2.1 h.2.2)
    else 1

noncomputable def faceScaleSlopeInteractionCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (haff : FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A then
      Classical.choose
        (Classical.choose_spec
          (haff.slope_affine_in_second_value hax q r h.1 h.2.1 h.2.2))
    else 0

/-- Reconstruct the face-scale slice-slope package from the exact
slope-affine output. -/
noncomputable def faceScaleProductSliceSlope_of_slopeAffine
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (haff : FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice) :
    FiniteFaceScaleProductSliceSlopeAssumptionsFor hslice where
  leftCoeff := by
    intro hax A B _ _ _ _ _ _ q r
    exact faceScaleSlopeLeftCoeff haff hax q r
  interactionCoeff := by
    intro hax A B _ _ _ _ _ _ q r
    exact faceScaleSlopeInteractionCoeff haff hax q r
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    classical
    by_cases hA : Subsingleton A
    · -- degenerate first coordinate: the calibrated coefficient defaults to 1
      have hne : ¬ (q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A) := by
        rintro ⟨_, _, hnotA⟩; exact hnotA hA
      simp only [faceScaleSlopeLeftCoeff, dif_neg hne]
      exact one_pos
    · have hpos :=
        (Classical.choose_spec
          (Classical.choose_spec
            (haff.slope_affine_in_second_value hax q r hq hr hA))).1
      have hcond : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A :=
        ⟨hq, hr, hA⟩
      simpa [faceScaleSlopeLeftCoeff, hcond] using hpos
  leftSliceSlope_value := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr hA R
    classical
    have hcond : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A :=
      ⟨hq, hr, hA⟩
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.slope_affine_in_second_value hax q r hq hr hA))).2 (R := R)
    simpa [faceScaleSlopeLeftCoeff, faceScaleSlopeInteractionCoeff, hcond]
      using hspec

/-- Face-scale-level pairwise product bilinear form.

This is the non-circular analogue of the old
`FinitePairwiseProductBilinearAssumptions`: it is stated against the
pre-universal `CoherentRelabelingFaceScalesStructure`, not against the
`ScaleCoherenceStructure` that the interaction-collapse theorem is trying to
construct. -/
structure FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) where
  leftCoeff :
    PureTraceConditions F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff :
    PureTraceConditions F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    PureTraceConditions F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff hax q r
  rightCoeff_pos :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff hax q r
  product_pair_bilinear :
    ∀ (hax : PureTraceConditions F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) +
        rightCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) +
        interactionCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R)

/-- Left linear product coefficient after applying a coherent positive
prior-gauge transform to the selected face-scale representatives. -/
noncomputable def faceScaleGaugeTransformedLeftCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u})
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.leftCoeff hax q r *
    (hgauge.gauge (prodDist q r) / hgauge.gauge q)

/-- Right linear product coefficient after applying a coherent positive
prior-gauge transform to the selected face-scale representatives. -/
noncomputable def faceScaleGaugeTransformedRightCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u})
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.rightCoeff hax q r *
    (hgauge.gauge (prodDist q r) / hgauge.gauge r)

/-- Interaction product coefficient after applying a coherent positive
prior-gauge transform to the selected face-scale representatives. -/
noncomputable def faceScaleGaugeTransformedInteractionCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u})
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.interactionCoeff hax q r *
    (hgauge.gauge (prodDist q r) /
      (hgauge.gauge q * hgauge.gauge r))

/-- Pairwise product bilinearity is transported by coherent positive
prior-gauge rescaling, with the usual coefficient transformation laws from
Lemma `coherentnorm`. -/
noncomputable def faceScaleProductPairwiseBilinearity_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
      (hfaces.gaugeTransform hgauge) where
  leftCoeff := fun hax {A B} _ _ _ _ _ _ q r =>
    faceScaleGaugeTransformedLeftCoeff hpair hgauge hax q r
  rightCoeff := fun hax {A B} _ _ _ _ _ _ q r =>
    faceScaleGaugeTransformedRightCoeff hpair hgauge hax q r
  interactionCoeff := fun hax {A B} _ _ _ _ _ _ q r =>
    faceScaleGaugeTransformedInteractionCoeff hpair hgauge hax q r
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact mul_pos (hpair.leftCoeff_pos hax q r hq hr)
      (div_pos (hgauge.gauge_pos (prodDist q r)) (hgauge.gauge_pos q))
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact mul_pos (hpair.rightCoeff_pos hax q r hq hr)
      (div_pos (hgauge.gauge_pos (prodDist q r)) (hgauge.gauge_pos r))
  product_pair_bilinear := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    dsimp [CoherentRelabelingFaceScalesStructure.gaugeTransform,
      branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      branchAggregationStructure_gaugeTransform,
      posteriorValueRepresentation_gaugeTransform,
      faceScaleGaugeTransformedLeftCoeff,
      faceScaleGaugeTransformedRightCoeff,
      faceScaleGaugeTransformedInteractionCoeff]
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    have hgq_ne : hgauge.gauge q ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos q)
    have hgr_ne : hgauge.gauge r ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos r)
    field_simp [hgq_ne, hgr_ne]

/-- Explicit product-gauge transform data for a raw pairwise face-scale
bilinear package.  This records the positive coherent gauge selected in the
paper's product-normalisation step and the two transformed linear coefficient
normalisations. -/
structure FiniteFaceScaleProductGaugeTransformFor
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    where
  gauge : CoherentFaceScaleGauge.{u}
  transformed_leftCoeff_normalized :
    ∀ (hax : PureTraceConditions F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      faceScaleGaugeTransformedLeftCoeff hpair gauge hax q r = 1
  transformed_rightCoeff_normalized :
    ∀ (hax : PureTraceConditions F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      faceScaleGaugeTransformedRightCoeff hpair gauge hax q r = 1

/-- Reconstruct face-scale pairwise product bilinearity from the same Step 2
slice-affine pieces used by the old Stage 10 coherent-product route. -/
def faceScaleProductPairwiseBilinearity_of_sliceAffine
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductSliceInterceptAssumptionsFor hslice)
    (hslope : FiniteFaceScaleProductSliceSlopeAssumptionsFor hslice) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces where
  leftCoeff := hslope.leftCoeff
  rightCoeff := hintercept.rightCoeff
  interactionCoeff := hslope.interactionCoeff
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hslope.leftCoeff_pos hax q r hq hr
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hintercept.rightCoeff_pos hax q r hq hr
  product_pair_bilinear := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    classical
    by_cases hA : Subsingleton A
    · -- degenerate first coordinate: V_q(P) = 0, so both slope terms vanish
      haveI : Subsingleton A := hA
      have hVq :
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep q hq P
      rw [hslice.left_slice_affine hax q r hq hr P R]
      rw [hintercept.leftSliceIntercept_value hax q r hq hr R]
      rw [hVq]
      ring
    · rw [hslice.left_slice_affine hax q r hq hr P R]
      rw [hslope.leftSliceSlope_value hax q r hq hr hA R]
      rw [hintercept.leftSliceIntercept_value hax q r hq hr R]
      ring

/-- Face-scale-level Step 3 gauge normalization of product linear
coefficients. -/
structure FiniteFaceScaleProductGaugeNormalizationAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  leftCoeff_normalized :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff hax q r = 1
  rightCoeff_normalized :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff hax q r = 1

/-- Explicit current-representative product gauge normalization.

The paper chooses positive rescalings of the zero-normalised representatives
before stating coherent product quasi-additivity.  At this point of the Lean
development the representatives in `hfaces` are fixed, so this normalization says
they are already in the product gauge where the two linear coefficients are
normalised to one. -/
structure FiniteFaceScaleCurrentProductGaugeNormalizationFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  current_leftCoeff_normalized :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff hax q r = 1
  current_rightCoeff_normalized :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff hax q r = 1

/-- Reconstruct the gauge-normalization package from the explicit
current-representative gauge normalization. -/
theorem faceScaleProductGaugeNormalization_of_currentGauge
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair) :
    FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair where
  leftCoeff_normalized := hgauge.current_leftCoeff_normalized
  rightCoeff_normalized := hgauge.current_rightCoeff_normalized

/-- After applying the selected product gauge, the transformed representatives
are in the current product gauge by construction. -/
theorem faceScaleCurrentProductGaugeNormalization_of_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair) :
    FiniteFaceScaleCurrentProductGaugeNormalizationFor
      (faceScaleProductPairwiseBilinearity_gaugeTransform
        hpair hgauge.gauge) where
  current_leftCoeff_normalized := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hgauge.transformed_leftCoeff_normalized hax q r hq hr
  current_rightCoeff_normalized := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hgauge.transformed_rightCoeff_normalized hax q r hq hr

/-- Normalized face-scale product bilinear form.  Once the current
representatives are in the product gauge, the two linear product coefficients
are both one and the only pair-dependent term is the interaction coefficient. -/
theorem faceScaleProductPairBilinear_normalized
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) +
      hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel R) +
      hpair.interactionCoeff hax q r *
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) *
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear hax q r hq hr P R]
  rw [hnorm.leftCoeff_normalized hax q r hq hr]
  rw [hnorm.rightCoeff_normalized hax q r hq hr]
  ring

/-- Pure-trace nontriviality makes full revelation nonzero in the current face-scale
value representative.  This early helper is used by the normalized
triple-product coefficient algebra below. -/
theorem faceScale_idChannel_value_ne_zero_of_A1
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
  have hne :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) :=
    branch_value_ne_of_strict_experiment_pref
      F hfaces.branch_result.branch_agg.value_rep q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      hstrict.1 hstrict.2
  have hzero :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  intro hid
  exact hne (by rw [hid, hzero])

/-- Face-scale-level Steps 4--5 interaction universality: after gauge
normalization, the bilinear interaction coefficient is a common `kappa`
independent of the two product factors. -/
structure FiniteFaceScaleProductInteractionUniversalityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) where
  kappa : PureTraceConditions F → ℝ
  interactionCoeff_common :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.interactionCoeff hax q r = kappa hax

/-- Fixed nondegenerate reference type for the face-scale common-κ extraction. -/
abbrev faceScaleInteractionReferenceType : Type u := ULift.{u, 0} Bool

/-- Fixed full-support reference prior for the face-scale common-κ extraction. -/
noncomputable def faceScaleInteractionReferencePrior :
    Dist faceScaleInteractionReferenceType :=
  Dist.uniform

theorem faceScaleInteractionReferencePrior_fullSupport :
    faceScaleInteractionReferencePrior.FullSupport :=
  Dist.uniform_fullSupport (A := faceScaleInteractionReferenceType)

theorem faceScaleInteractionReference_not_subsingleton :
    ¬ Subsingleton faceScaleInteractionReferenceType := by
  intro hsub
  have htf : (true : Bool) = false := by
    exact congrArg ULift.down
      (Subsingleton.elim
        (ULift.up true : faceScaleInteractionReferenceType)
        (ULift.up false : faceScaleInteractionReferenceType))
  cases htf

/-- The reference interaction coefficient used to name common `kappa`. -/
noncomputable def faceScaleInteractionReferenceKappa
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : PureTraceConditions F) : ℝ :=
  hpair.interactionCoeff hax
    faceScaleInteractionReferencePrior faceScaleInteractionReferencePrior

/-- Face-scale-level K1--K3 interaction associativity equations.  These are
the exact source-ready coefficient equations needed to identify a common
interaction coefficient. -/
structure FiniteFaceScaleProductInteractionAssociativityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  interaction_assoc_xy :
    ∀ (hax : PureTraceConditions F)
      {A B C : Type v}
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
    ∀ (hax : PureTraceConditions F)
      {A B C : Type v}
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
    ∀ (hax : PureTraceConditions F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax r s

/-- Singleton interaction coefficient normalization for face-scale product
bilinearity.  Singleton coordinate values vanish, so the interaction
coefficient is not value-identified in singleton factors. -/
structure FiniteFaceScaleSingletonInteractionNormalizationFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  interactionCoeff_eq_reference_of_subsingleton_left :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton A →
      hpair.interactionCoeff hax q r =
        faceScaleInteractionReferenceKappa hpair hax
  interactionCoeff_eq_reference_of_subsingleton_right :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton B →
      hpair.interactionCoeff hax q r =
        faceScaleInteractionReferenceKappa hpair hax

/-- Nondegenerate common-κ extraction from K1--K3. -/
theorem faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.interactionCoeff hax q r =
      faceScaleInteractionReferenceKappa hpair hax := by
  let q₀ : Dist faceScaleInteractionReferenceType :=
    faceScaleInteractionReferencePrior
  have hq₀ : q₀.FullSupport :=
    faceScaleInteractionReferencePrior_fullSupport
  have hRef : ¬ Subsingleton faceScaleInteractionReferenceType :=
    faceScaleInteractionReference_not_subsingleton
  have h_qr_to_r_ref :
      hpair.interactionCoeff hax q r =
        hpair.interactionCoeff hax r q₀ := by
    calc
      hpair.interactionCoeff hax q r
          = hpair.interactionCoeff hax q (prodDist r q₀) :=
            hassoc.interaction_assoc_xy hax q r q₀ hq hr hq₀ hA hB hRef
      _ = hpair.interactionCoeff hax (prodDist q r) q₀ :=
            (hassoc.interaction_assoc_xz hax q r q₀ hq hr hq₀ hA hB hRef).symm
      _ = hpair.interactionCoeff hax r q₀ :=
            hassoc.interaction_assoc_yz hax q r q₀ hq hr hq₀ hA hB hRef
  have h_r_ref_to_ref_ref :
      hpair.interactionCoeff hax r q₀ =
        hpair.interactionCoeff hax q₀ q₀ := by
    calc
      hpair.interactionCoeff hax r q₀
          = hpair.interactionCoeff hax r (prodDist q₀ q₀) :=
            hassoc.interaction_assoc_xy hax r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
      _ = hpair.interactionCoeff hax (prodDist r q₀) q₀ :=
            (hassoc.interaction_assoc_xz hax r q₀ q₀ hr hq₀ hq₀ hB hRef hRef).symm
      _ = hpair.interactionCoeff hax q₀ q₀ :=
            hassoc.interaction_assoc_yz hax r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
  calc
    hpair.interactionCoeff hax q r
        = hpair.interactionCoeff hax r q₀ := h_qr_to_r_ref
    _ = faceScaleInteractionReferenceKappa hpair hax := by
        simpa [faceScaleInteractionReferenceKappa, q₀]
          using h_r_ref_to_ref_ref

/-- Reconstruct face-scale interaction universality from K1--K3 and singleton
interaction normalizations. -/
noncomputable def faceScaleProductInteractionUniversality_of_parts
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair) :
    FiniteFaceScaleProductInteractionUniversalityAssumptionsFor hpair where
  kappa := faceScaleInteractionReferenceKappa hpair
  interactionCoeff_common := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    by_cases hsubA : Subsingleton A
    · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_left
        hax q r hq hr hsubA
    · by_cases hsubB : Subsingleton B
      · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_right
          hax q r hq hr hsubB
      · exact faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc hax q r hq hr hsubA hsubB

/-- Product quasi-additivity from product gauge normalization and interaction
associativity, without a singleton interaction normalization.

The singleton coefficient is not value-identified: if either factor is a
subsingleton, the corresponding posterior value is zero, so the interaction term
vanishes for every coefficient.  The only coefficient identification needed for
the product formula is therefore the nondegenerate one, which follows from the
K1--K3 associativity equations. -/
noncomputable def productQuasiAdditivityForFaceScales_of_components_noSingleton
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces where
  kappa := faceScaleInteractionReferenceKappa hpair
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    rw [hnorm.leftCoeff_normalized hax q r hq hr]
    rw [hnorm.rightCoeff_normalized hax q r hq hr]
    by_cases hsubA : Subsingleton A
    · haveI : Subsingleton A := hsubA
      have hVq :
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep q hq P
      rw [hVq]
      ring
    · by_cases hsubB : Subsingleton B
      · haveI : Subsingleton B := hsubB
        have hVr :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) = 0 :=
          branchValue_channel_eq_zero_of_subsingleton F
            hfaces.branch_result.branch_agg.value_rep r hr R
        rw [hVr]
        ring
      · rw [faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc hax q r hq hr hsubA hsubB]
        ring

/-- Face-scale triple-product value associativity.  This is the
pre-universal, pre-entropy version of the product-parenthesization value
transport used in the old Stage 10 interaction-associativity proof. -/
structure FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  triple_value_assoc :
    ∀ (_hax : PureTraceConditions F)
      {A B C O Y Z : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      [Fintype Z] [DecidableEq Z]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (P : Channel A O) (R : Channel B Y) (S : Channel C Z),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist (prodDist q r) s)
          (experimentOfChannel (prodChannel (prodChannel P R) S)) =
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q (prodDist r s))
          (experimentOfChannel (prodChannel P (prodChannel R S)))

/-- Face-scale triple-product value associativity follows from exact
relabeling coherence of the selected posterior-value representatives and the
structural product associator relabeling facts. -/
theorem faceScaleTripleProductValueAssociativity_of_valueRelabeling
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u}) :
    FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces where
  triple_value_assoc := by
    intro hax A B C O Y Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q r s _hq _hr _hs
      P R S
    have hrel :=
      hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc O Y Z)
        (prodDist (prodDist q r) s) (prodChannel (prodChannel P R) S)
    have hrel' :
        hfaces.branch_result.branch_agg.value_rep.V
            (prodDist q (prodDist r s))
            (experimentOfChannel (prodChannel P (prodChannel R S))) =
          hfaces.branch_result.branch_agg.value_rep.V
            (prodDist (prodDist q r) s)
            (experimentOfChannel (prodChannel (prodChannel P R) S)) := by
      simpa [relabelDist_prodAssoc q r s, relabelChannel_prodAssoc P R S]
        using hrel
    exact hrel'.symm

/-- Triple-product value associativity is preserved by coherent positive
prior-gauge rescaling.  The two product-parenthesized priors are related by
the canonical product associator, and `CoherentFaceScaleGauge.gauge_relabel_eq`
aligns the two gauge factors. -/
theorem faceScaleTripleProductValueAssociativity_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
      (hfaces.gaugeTransform hgauge) where
  triple_value_assoc := by
    intro hax A B C O Y Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q r s hq hr hs P R S
    dsimp [CoherentRelabelingFaceScalesStructure.gaugeTransform,
      branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      branchAggregationStructure_gaugeTransform,
      posteriorValueRepresentation_gaugeTransform]
    have hraw :=
      htriple.triple_value_assoc hax q r s hq hr hs P R S
    have hg :
        hgauge.gauge (prodDist q (prodDist r s)) =
          hgauge.gauge (prodDist (prodDist q r) s) := by
      have h :=
        hgauge.gauge_relabel_eq
          (Equiv.prodAssoc A B C) (prodDist (prodDist q r) s)
      simpa [relabelDist_prodAssoc q r s] using h
    rw [hraw, hg]

/-- Coefficient extraction from triple-product value associativity and
normalized product coefficients.  This is the exact source-ready algebraic
bridge needed to turn value-level associativity into the K1--K3 interaction
coefficient equations. -/
structure FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (_hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (_htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    Prop where
  interaction_assoc_xy :
    ∀ (hax : PureTraceConditions F)
      {A B C : Type v}
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
    ∀ (hax : PureTraceConditions F)
      {A B C : Type v}
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
    ∀ (hax : PureTraceConditions F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax r s

/-- Face-scale K1--K3 coefficient extraction from value-level triple-product
associativity and normalized product bilinear form.

This is the pre-universal analogue of the old Stage 10 normalized
triple-product algebra, stated directly against
`CoherentRelabelingFaceScalesStructure`. -/
theorem faceScaleTripleProductCoeffExtraction_of_valueAssociativity
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    {hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair}
    {htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces} :
    FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
      hpair hnorm htriple where
  interaction_assoc_xy := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB _hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hxne :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hyne :
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
    have hxyne :
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel (Channel.idChannel : Channel A A)) *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      mul_ne_zero hxne hyne
    have hval :=
      htriple.triple_value_assoc hax q r s hq hr hs
        (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C)
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.idChannel : Channel B B))
        (Channel.uninformativeChannelU C)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.uninformativeChannelU C))] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q r hq hr
        (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        r s hr hs
        (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized s hs] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxyne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_xz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA _hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hxne :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
    have hxzne :
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel (Channel.idChannel : Channel A A)) *
          hfaces.branch_result.branch_agg.value_rep.V s
            (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      mul_ne_zero hxne hzne
    have hval :=
      htriple.triple_value_assoc hax q r s hq hr hs
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C)
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.uninformativeChannelU B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q r hq hr
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        r s hr hs
        (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_yz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs _hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hyne :
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
    have hyzne :
        hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) *
          hfaces.branch_result.branch_agg.value_rep.V s
            (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      mul_ne_zero hyne hzne
    have hval :=
      htriple.triple_value_assoc hax q r s hq hr hs
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C)
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs
        (Channel.uninformativeChannelU A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q r hq hr
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        r s hr hs
        (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hyzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Reconstruct K1--K3 interaction associativity from triple-product
coefficient extraction. -/
theorem faceScaleProductInteractionAssociativity_of_coeffExtraction
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    {hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair}
    {htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces}
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        hpair hnorm htriple) :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair where
  interaction_assoc_xy := hextract.interaction_assoc_xy
  interaction_assoc_xz := hextract.interaction_assoc_xz
  interaction_assoc_yz := hextract.interaction_assoc_yz

/-- Interaction associativity for the product-gauge transformed representative,
obtained by transporting pairwise bilinearity and triple-product value
associativity through the coherent gauge and then applying the existing
coefficient-extraction algebra. -/
theorem faceScaleProductInteractionAssociativity_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor
      (faceScaleProductPairwiseBilinearity_gaugeTransform
        hpair hgauge.gauge) :=
  faceScaleProductInteractionAssociativity_of_coeffExtraction
    (faceScaleTripleProductCoeffExtraction_of_valueAssociativity
      (hpair :=
        faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)
      (hnorm :=
        faceScaleProductGaugeNormalization_of_currentGauge
          (faceScaleCurrentProductGaugeNormalization_of_gaugeTransform hgauge))
      (htriple :=
        faceScaleTripleProductValueAssociativity_gaugeTransform
          htriple hgauge.gauge))

/-- Interaction associativity for a representative already in the current
product gauge, obtained directly from value-level triple-product
associativity. -/
theorem faceScaleProductInteractionAssociativity_of_valueAssociativity_currentGauge
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair :=
  faceScaleProductInteractionAssociativity_of_coeffExtraction
    (faceScaleTripleProductCoeffExtraction_of_valueAssociativity
      (hpair := hpair)
      (hnorm := faceScaleProductGaugeNormalization_of_currentGauge hgauge)
      (htriple := htriple))

/-- Pairwise product bilinearity reconstructed from the multi-stage
left-slice affine, intercept, and slope outputs. -/
noncomputable def faceScaleProductPairwiseBilinearity_of_multiPieces
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff)) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces :=
  faceScaleProductPairwiseBilinearity_of_sliceAffine
    (faceScaleProductLeftSliceAffine_of_transform haff)
    (faceScaleProductSliceIntercept_of_positiveLinear hintercept)
    (faceScaleProductSliceSlope_of_slopeAffine hslope)

/-- Reassemble the face-scale product quasi-additivity theorem from the
non-circular face-scale analogues of the Stage 10 product components. -/
def productQuasiAdditivityForFaceScales_of_components
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (huniv :
      FiniteFaceScaleProductInteractionUniversalityAssumptionsFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces where
  kappa := huniv.kappa
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    rw [hnorm.leftCoeff_normalized hax q r hq hr]
    rw [hnorm.rightCoeff_normalized hax q r hq hr]
    rw [huniv.interactionCoeff_common hax q r hq hr]
    ring

/-- Product quasi-additivity from pairwise bilinearity, explicit current-gauge
normalization, and the K-associativity/singleton interaction-universality
pieces. -/
noncomputable def productQuasiAdditivityForFaceScales_of_finalProductComponents
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  productQuasiAdditivityForFaceScales_of_components hpair
    (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
    (faceScaleProductInteractionUniversality_of_parts hpair hassoc hsingle)

/-- Product quasi-additivity for the product-gauge transformed representative.

This is the Lean form of the paper move "rescale by the chosen positive product
gauge, then work with the normalized representatives": the raw pairwise
bilinear package is transported through the gauge, the transformed left/right
coefficients are normalized by `hgauge`, and the usual interaction
associativity/singleton pieces supply the common `κ`. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedComponents
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge))
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_finalProductComponents
    (faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
    (faceScaleCurrentProductGaugeNormalization_of_gaugeTransform hgauge)
    hassoc hsingle

/-- Product quasi-additivity for the product-gauge transformed representative,
with transformed interaction associativity derived internally from raw
triple-product value associativity. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_gaugeTransformedComponents
    hpair hgauge
    (faceScaleProductInteractionAssociativity_gaugeTransform hgauge htriple)
    hsingle

/-- Product quasi-additivity for the product-gauge transformed representative,
with singleton-factor cases handled by value-zero rather than by an arbitrary
singleton coefficient normalization. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData_noSingleton
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_components_noSingleton
    (faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
    (faceScaleProductGaugeNormalization_of_currentGauge
      (faceScaleCurrentProductGaugeNormalization_of_gaugeTransform hgauge))
    (faceScaleProductInteractionAssociativity_gaugeTransform hgauge htriple)

/-- Product quasi-additivity from the multi-stage source-ready components:
left-slice affine transform, intercept linearity, slope affinity, current
gauge, triple-product value/coefficient extraction, and singleton interaction
normalization. -/
noncomputable def productQuasiAdditivityForFaceScales_of_multiComponents
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        htriple)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope)) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  productQuasiAdditivityForFaceScales_of_finalProductComponents
    (faceScaleProductPairwiseBilinearity_of_multiPieces
      haff hintercept hslope)
    hgauge
    (faceScaleProductInteractionAssociativity_of_coeffExtraction hextract)
    hsingle

/-- Paper Step 1: product revelation links the chain scales to
`Z(q) = 1 + kappa * H(q)`.

The equations are written without division to keep the algebraic downstream
proof independent of denominator-normalization details. -/
structure FiniteProductRevelationScaleLinkAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  scale_product_left :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        (1 + hprod.kappa hax *
          fullRevelationValueForFaceScales hfaces q) *
        hfaces.branch_result.scale_factorization.scale r
  scale_product_right :
    ∀ (hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        (1 + hprod.kappa hax *
          fullRevelationValueForFaceScales hfaces r) *
        hfaces.branch_result.scale_factorization.scale q

/-- Paper Step 3: the two-grouping argument collapses the product interaction
coefficient to zero. -/
structure FiniteTwoGroupingInteractionCollapseAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  kappa_eq_zero :
    ∀ (hax : PureTraceConditions F), hprod.kappa hax = 0

/-- Singleton/degenerate scale normalization for extending the nondegenerate
universal-scale conclusion to all full-support priors. -/
structure FiniteUniversalScaleSingletonNormalizationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  scale_eq_of_subsingleton :
    ∀ {A B : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      (Subsingleton A ∨ Subsingleton B) →
      hfaces.branch_result.scale_factorization.scale q =
        hfaces.branch_result.scale_factorization.scale r

end TraceableAgency
