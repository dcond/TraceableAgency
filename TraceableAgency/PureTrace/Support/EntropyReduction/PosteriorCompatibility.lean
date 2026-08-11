/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.BackgroundInertness

namespace TraceableAgency

universe u

/-!
## Right-Side Product/Public-Mix Posterior-Law Compatibility

Mirror of the left-side machinery: shows that mixing in the second coordinate
inside a product channel is equivalent (up to outcome relabeling) to the public
mixture of the two product channels. This is Stage 10P structural content.
-/

/-- Right-side product/sum distributivity: `O × (Y ⊕ Z) ≃ (O × Y) ⊕ (O × Z)`. -/
def prodSumDistribEquivRight (O Y Z : Type u) :
    (O × (Y ⊕ Z)) ≃ ((O × Y) ⊕ (O × Z)) where
  toFun oys :=
    match oys.2 with
    | Sum.inl y => Sum.inl (oys.1, y)
    | Sum.inr z => Sum.inr (oys.1, z)
  invFun s :=
    match s with
    | Sum.inl oy => (oy.1, Sum.inl oy.2)
    | Sum.inr oz => (oz.1, Sum.inr oz.2)
  left_inv := by
    intro ⟨o, yz⟩
    cases yz <;> rfl
  right_inv := by
    intro s
    cases s with
    | inl oy => cases oy; rfl
    | inr oz => cases oz; rfl

@[simp]
theorem prodSumDistribEquivRight_inl {O Y Z : Type u} (o : O) (y : Y) :
    prodSumDistribEquivRight O Y Z (o, Sum.inl y) = Sum.inl (o, y) := rfl

@[simp]
theorem prodSumDistribEquivRight_inr {O Y Z : Type u} (o : O) (z : Z) :
    prodSumDistribEquivRight O Y Z (o, Sum.inr z) = Sum.inr (o, z) := rfl

/-- Right-side product/public-mix channel postprocessing: mixing in the second
coordinate of a product channel, then relabeling outcomes, equals the public
mixture of the two product channels. -/
theorem prodChannel_publicMix_right_postprocess
    {A B O Y Z : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (R : Channel B Y) (S : Channel B Z) :
    Channel.postprocess
        (prodChannel P (publicMixChannel t ht0 ht1 R S))
        (posteriorLawEquivKernel (prodSumDistribEquivRight O Y Z)) =
      publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S) := by
  ext ⟨a, b⟩ s
  cases s with
  | inl oy =>
    rcases oy with ⟨o, y⟩
    change
      (∑ oy' : O × (Y ⊕ Z),
          (P a oy'.1 * publicMixChannel t ht0 ht1 R S b oy'.2) *
            Dist.pure (prodSumDistribEquivRight O Y Z oy') (Sum.inl (o, y))) =
        t * (P a o * R b y)
    rw [Fintype.sum_eq_single (o, (Sum.inl y : Y ⊕ Z))]
    · simp [prodSumDistribEquivRight, publicMixChannel]
      ring
    · intro ⟨o', yz'⟩ hne
      by_cases hmap : prodSumDistribEquivRight O Y Z (o', yz') = Sum.inl (o, y)
      · have hsource : (o', yz') = (o, Sum.inl y) := by
          cases yz' with
          | inl y' =>
            simp only [prodSumDistribEquivRight_inl, Sum.inl.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨ho, hy⟩
            subst ho; subst hy; rfl
          | inr z =>
            simp [prodSumDistribEquivRight_inr] at hmap
        exact (hne hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquivRight O Y Z (o', yz')) (Sum.inl (o, y)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]
  | inr oz =>
    rcases oz with ⟨o, z⟩
    change
      (∑ oy' : O × (Y ⊕ Z),
          (P a oy'.1 * publicMixChannel t ht0 ht1 R S b oy'.2) *
            Dist.pure (prodSumDistribEquivRight O Y Z oy') (Sum.inr (o, z))) =
        (1 - t) * (P a o * S b z)
    rw [Fintype.sum_eq_single (o, (Sum.inr z : Y ⊕ Z))]
    · simp [prodSumDistribEquivRight, publicMixChannel]
      ring
    · intro ⟨o', yz'⟩ hne
      by_cases hmap : prodSumDistribEquivRight O Y Z (o', yz') = Sum.inr (o, z)
      · have hsource : (o', yz') = (o, Sum.inr z) := by
          cases yz' with
          | inl y =>
            simp [prodSumDistribEquivRight_inl] at hmap
          | inr z' =>
            simp only [prodSumDistribEquivRight_inr, Sum.inr.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨ho, hz⟩
            subst ho; subst hz; rfl
        exact (hne hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquivRight O Y Z (o', yz')) (Sum.inr (o, z)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]

/-- Right-side product/public-mix posterior-law theorem: mixing in the second
coordinate inside a product channel gives the same posterior law as the public
mixture of the two product channels. Mirror of
`samePosteriorLaw_prod_publicMix_left_of_postprocess`. -/
theorem samePosteriorLaw_prod_publicMix_right_of_postprocess
    {A B O Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B)
    (P : Channel A O)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel P (publicMixChannel t ht0 ht1 R S)))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S))) := by
  let PmixProd := prodChannel P (publicMixChannel t ht0 ht1 R S)
  have hsame :
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel PmixProd)
        (experimentOfChannel
          (Channel.postprocess PmixProd
            (posteriorLawEquivKernel (prodSumDistribEquivRight O Y Z)))) :=
    samePosteriorLawExp_of_bijective_postprocess
      (prodDist q r) PmixProd (prodSumDistribEquivRight O Y Z)
  have hchan :
      Channel.postprocess PmixProd
          (posteriorLawEquivKernel (prodSumDistribEquivRight O Y Z)) =
        publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S) :=
    prodChannel_publicMix_right_postprocess t ht0 ht1 P R S
  simpa [PmixProd, hchan] using hsame

/-- Right-slice public-mix affinity: for a fixed first-coordinate background,
the product value is public-mix affine in the second-coordinate channel.
Derived from the right-side posterior-law theorem plus posterior-value
public-mix affinity. -/
theorem product_right_slice_publicMix_affine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    productRightSliceValue hs q r P (publicMixChannel t ht0 ht1 R S) =
      t * productRightSliceValue hs q r P R +
        (1 - t) * productRightSliceValue hs q r P S := by
  have hsame :=
    samePosteriorLaw_prod_publicMix_right_of_postprocess q r P t ht0 ht1 R S
  have hVeq :=
    hs.branch_agg.value_rep.respects_same_posterior_law
      (prodDist q r)
      (experimentOfChannel (prodChannel P (publicMixChannel t ht0 ht1 R S)))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S)))
      hsame
  have hprod : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  calc
    productRightSliceValue hs q r P (publicMixChannel t ht0 ht1 R S)
        = hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S))) := by
          simpa [productRightSliceValue] using hVeq
    _ = t * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel P R)) +
          (1 - t) * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel P S)) := by
          exact
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
              F hax hs.branch_agg.value_rep
              (prodDist q r) hprod t ht0 ht1
              (prodChannel P R) (prodChannel P S)
    _ = t * productRightSliceValue hs q r P R +
          (1 - t) * productRightSliceValue hs q r P S := by
          rfl

/--
**Product Left-Slice Public-Mix Affinity**

Paper-specific product-affinity content for the first-coordinate slice:
`P ↦ V_{q⊗r}(P⊗R)` is affine under public mixtures of the first-coordinate
experiment. In the paper this follows because `L_{q,r}` is separately affine.
Stage 10I derives this from channel-level value public-mix affinity plus the
narrow posterior-law compatibility between `prodChannel (publicMix P Q) R` and
the public mixture of `prodChannel P R` and `prodChannel Q R`. Stage 10K
derives the channel-level value public-mix affinity from law-level posterior
value affinity and the structural public-mix posterior-law mixture theorem.
-/
structure FiniteProductLeftSlicePublicMixAffineAssumptions.{v} where
  product_left_slice_publicMix_affine :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B O Z Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q) =
        t * productLeftSliceValue hs q r R P +
          (1 - t) * productLeftSliceValue hs q r R Q

theorem product_left_slice_publicMix_affine_of_posterior_affinity
    (hVaff : FinitePosteriorValueAffineAssumptions.{u})
    (hmixlaw : FiniteProductPublicMixPosteriorLawAssumptions.{u}) :
    FiniteProductLeftSlicePublicMixAffineAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hs A B O Z Y _ _ _ _ _ _ _ _ _ _ _ _ q r hq hr R t ht0 ht1 P Q
  have hsame :
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) :=
    hmixlaw.samePosteriorLaw_prod_publicMix_left q r R t ht0 ht1 P Q
  have hVeq :=
    hs.branch_agg.value_rep.respects_same_posterior_law
      (prodDist q r)
      (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R)))
      hsame
  have hprod : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  calc
    productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q)
        = hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) := by
          simpa [productLeftSliceValue] using hVeq
    _ = t * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel P R)) +
          (1 - t) * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel Q R)) := by
          exact
            hVaff.V_publicMix_affine F hax hs.branch_agg.value_rep
              (prodDist q r) hprod t ht0 ht1
              (prodChannel P R) (prodChannel Q R)
    _ = t * productLeftSliceValue hs q r R P +
          (1 - t) * productLeftSliceValue hs q r R Q := by
          rfl

/-- Face-scale base-value public-mixture affinity follows from the global
posterior-law value-affinity package. -/
theorem faceScaleBaseValuePublicMixAffinity_of_posteriorLawValueAffine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces where
  base_value_publicMix_affine := by
    intro hax A O Z _ _ _ _ _ _ _ q hq t ht0 ht1 P Q
    exact
      (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
        F hax hfaces.branch_result.branch_agg.value_rep
        q hq t ht0 ht1 P Q

/-- Face-scale first-coordinate product-slice public-mixture affinity follows
from posterior-law value affinity plus the structural product/public-mix
posterior-law transport. -/
theorem faceScaleProductCoordinateMixtureAffinity_of_posteriorLawValueAffine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces where
  left_slice_publicMix_affine := by
    intro hax A B O Z Y _ _ _ _ _ _ _ _ _ _ _ _ q r hq hr R t ht0 ht1 P Q
    have hsame :
        SamePosteriorLawExp (prodDist q r)
          (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
          (experimentOfChannel
            (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) :=
      samePosteriorLaw_prod_publicMix_left_of_postprocess q r R t ht0 ht1 P Q
    have hVeq :=
      hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
        (prodDist q r)
        (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R)))
        hsame
    have hprod : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    calc
      faceScaleProductLeftSliceValue hfaces q r R
          (publicMixChannel t ht0 ht1 P Q)
          = hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) := by
            simpa [faceScaleProductLeftSliceValue] using hVeq
      _ = t * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel (prodChannel P R)) +
            (1 - t) * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel (prodChannel Q R)) := by
            exact
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
                F hax hfaces.branch_result.branch_agg.value_rep
                (prodDist q r) hprod t ht0 ht1
                (prodChannel P R) (prodChannel Q R)
      _ = t * faceScaleProductLeftSliceValue hfaces q r R P +
            (1 - t) * faceScaleProductLeftSliceValue hfaces q r R Q := by
            rfl

/-- Face-scale intercept public-mixture affinity follows from posterior-law
value affinity and product/public-mix posterior-law transport in the second
coordinate. -/
theorem faceScaleProductInterceptPublicMixAffinity_of_posteriorLawValueAffine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice where
  intercept_publicMix_affine := by
    intro hax A B Y Z _ _ _ _ _ _ _ _ _ _ q r hq hr t ht0 ht1 R S
    have hsame :
        SamePosteriorLawExp (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (publicMixChannel t ht0 ht1 R S)))
          (experimentOfChannel
            (publicMixChannel t ht0 ht1
              (prodChannel (Channel.uninformativeChannelU A) R)
              (prodChannel (Channel.uninformativeChannelU A) S))) :=
      samePosteriorLaw_prod_publicMix_right_of_postprocess
        q r (Channel.uninformativeChannelU A) t ht0 ht1 R S
    have hVeq :=
      hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
        (prodDist q r)
        (experimentOfChannel
          (prodChannel (Channel.uninformativeChannelU A)
            (publicMixChannel t ht0 ht1 R S)))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1
            (prodChannel (Channel.uninformativeChannelU A) R)
            (prodChannel (Channel.uninformativeChannelU A) S)))
        hsame
    have hprod : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr (publicMixChannel t ht0 ht1 R S)]
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr R]
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr S]
    calc
      faceScaleProductLeftSliceValue hfaces q r
          (publicMixChannel t ht0 ht1 R S)
          (Channel.uninformativeChannelU A)
          = hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (publicMixChannel t ht0 ht1
                  (prodChannel (Channel.uninformativeChannelU A) R)
                  (prodChannel (Channel.uninformativeChannelU A) S))) := by
            simpa [faceScaleProductLeftSliceValue] using hVeq
      _ = t * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (prodChannel (Channel.uninformativeChannelU A) R)) +
            (1 - t) * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (prodChannel (Channel.uninformativeChannelU A) S)) := by
            exact
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
                F hax hfaces.branch_result.branch_agg.value_rep
                (prodDist q r) hprod t ht0 ht1
                (prodChannel (Channel.uninformativeChannelU A) R)
                (prodChannel (Channel.uninformativeChannelU A) S)
      _ = t * faceScaleProductLeftSliceValue hfaces q r R
              (Channel.uninformativeChannelU A) +
            (1 - t) * faceScaleProductLeftSliceValue hfaces q r S
              (Channel.uninformativeChannelU A) := by
            rfl

/-- HM-specialized wrapper for the face-scale base public-mix field. -/
theorem faceScaleBaseValuePublicMixAffinity_of_HM
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces :=
  faceScaleBaseValuePublicMixAffinity_of_posteriorLawValueAffine
    (finitePosteriorLawValueAffine_of_HM hhm) hfaces

/-- HM-specialized wrapper for the face-scale product-coordinate public-mix
field. -/
theorem faceScaleProductCoordinateMixtureAffinity_of_HM
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces :=
  faceScaleProductCoordinateMixtureAffinity_of_posteriorLawValueAffine
    (finitePosteriorLawValueAffine_of_HM hhm) hfaces

/-- HM-specialized wrapper for the face-scale intercept public-mix field. -/
theorem faceScaleProductInterceptPublicMixAffinity_of_HM
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice :=
  faceScaleProductInterceptPublicMixAffinity_of_posteriorLawValueAffine
    (finitePosteriorLawValueAffine_of_HM hhm) hslice

/-- Face-scale version of derived product-coordinate order independence
theorem for first-coordinate product experiments.  Unlike the older
`product_left_coordinate_value_order_independent`, this is stated before
universal scale coherence and uses only the value representative already
contained in `CoherentRelabelingFaceScalesStructure`. -/
theorem faceScaleProduct_left_coordinate_value_order_independent
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : PureTraceConditions F)
    {A B O O₂R O₂S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype O₂R] [DecidableEq O₂R]
    [Fintype O₂S] [DecidableEq O₂S]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) (R : Channel B O₂R) (S : Channel B O₂S) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q R)) ↔
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P S)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q S)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel Q R))
  have hS :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P S))
      (experimentOfChannel (prodChannel Q S))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q R)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel P S) (prodChannel Q S))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P S)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q S)) at hS'
  exact hR'.symm.trans
    (((independentBackgroundSeparability_of_axioms F hax).1
      q r hq hr P Q R S).trans hS')

/-- Face-scale product left-slice with no-information background recovers the
base first-coordinate order. -/
theorem faceScaleProduct_left_noInfo_value_order_iff_base
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : PureTraceConditions F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) Q)) ↔
    hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Q) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
  have hprod_rel :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) := by
    change
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftProductLiftChannel (B := B) P) (leftUnitOutcomeChannel P)
      (leftProductLiftChannel (B := B) Q) (leftUnitOutcomeChannel Q)
      (prodDist q r) q (prodDist q r) q
      (leftProductLift_rel_leftUnitOutcome F hax P q r)
      (leftUnitOutcome_rel_leftProductLift F hax P q r)
      (leftProductLift_rel_leftUnitOutcome F hax Q q r)
      (leftUnitOutcome_rel_leftProductLift F hax Q q r)
  have hunit_to_base :
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) ↔
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftUnitOutcomeChannel P) P
      (leftUnitOutcomeChannel Q) Q
      q q q q
      (leftUnitOutcome_rel_original F hax P q)
      (original_rel_leftUnitOutcome F hax P q)
      (leftUnitOutcome_rel_original F hax Q q)
      (original_rel_leftUnitOutcome F hax Q q)
  have hbase_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      q hq (experimentOfChannel P) (experimentOfChannel Q)
  have hbase_rel :
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Q) := by
    change
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Q) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- Derived background inertness gives the face-scale first-coordinate slice order before universal
scale coherence. -/
theorem faceScaleProductLeftSliceSameOrder_of_backgroundInertness
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces where
  left_slice_same_order := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr R P Q
    have hbackground :=
      faceScaleProduct_left_coordinate_value_order_independent
        hfaces hax q r hq hr P Q R (Channel.uninformativeChannelU B)
    have hbase :=
      faceScaleProduct_left_noInfo_value_order_iff_base
        hfaces hax q r hq hr P Q
    simpa [faceScaleProductLeftSliceValue, leftProductLiftChannel] using
      hbackground.trans hbase

/-- Face-scale product right-slice value in the pre-universal structure. -/
noncomputable def faceScaleProductRightSliceValue
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O)
    (R : Channel B Y) : ℝ :=
  hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Face-scale derived product-coordinate order independence for second-coordinate
product experiments. -/
theorem faceScaleProduct_right_coordinate_value_order_independent
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : PureTraceConditions F)
    {A B O₁R O₁S O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O₁R] [DecidableEq O₁R]
    [Fintype O₁S] [DecidableEq O₁S]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel A O₁R) (S : Channel A O₁S) (P Q : Channel B O) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R P)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R Q)) ↔
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S P)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S Q)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel R P))
      (experimentOfChannel (prodChannel R Q))
  have hS :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel S P))
      (experimentOfChannel (prodChannel S Q))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel R P) (prodChannel R Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R Q)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel S P) (prodChannel S Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S Q)) at hS'
  exact hR'.symm.trans
    (((independentBackgroundSeparability_of_axioms F hax).2
      q r hq hr R S P Q).trans hS')

/-- Face-scale product right-slice with no-information first-coordinate
background recovers the base second-coordinate order. -/
theorem faceScaleProduct_right_noInfo_value_order_iff_base
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R S : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) S)) ↔
    hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) ≥
      hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel S) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (rightProductLiftChannel (A := A) R))
      (experimentOfChannel (rightProductLiftChannel (A := A) S))
  have hprod_rel :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) := by
    change
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightProductLiftChannel (A := A) R) (rightUnitOutcomeChannel R)
      (rightProductLiftChannel (A := A) S) (rightUnitOutcomeChannel S)
      (prodDist q r) r (prodDist q r) r
      (rightProductLift_rel_rightUnitOutcome F hax R q r)
      (rightUnitOutcome_rel_rightProductLift F hax R q r)
      (rightProductLift_rel_rightUnitOutcome F hax S q r)
      (rightUnitOutcome_rel_rightProductLift F hax S q r)
  have hunit_to_base :
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) ↔
      F.rel (blockChannel R S) (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightUnitOutcomeChannel R) R
      (rightUnitOutcomeChannel S) S
      r r r r
      (rightUnitOutcome_rel_original F hax R r)
      (original_rel_rightUnitOutcome F hax R r)
      (rightUnitOutcome_rel_original F hax S r)
      (original_rel_rightUnitOutcome F hax S r)
  have hbase_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      r hr (experimentOfChannel R) (experimentOfChannel S)
  have hbase_rel :
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel S) := by
    change
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel S) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- Derived background inertness gives the face-scale second-coordinate slice order before universal
scale coherence. -/
theorem faceScaleProductRightSliceSameOrder_of_backgroundInertness
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R S : Channel B Y) :
    faceScaleProductRightSliceValue hfaces q r P R ≥
        faceScaleProductRightSliceValue hfaces q r P S ↔
      hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel R) ≥
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel S) := by
  have hbackground :=
    faceScaleProduct_right_coordinate_value_order_independent
      hfaces hax q r hq hr (Channel.uninformativeChannelU A) P R S
  have hbase :=
    faceScaleProduct_right_noInfo_value_order_iff_base
      hfaces hax q r hq hr R S
  simpa [faceScaleProductRightSliceValue, rightProductLiftChannel] using
    hbackground.symm.trans hbase

/-- Face-scale intercept same-order reconstructed from derived right-slice order
and the internal intercept/no-information identity. -/
theorem faceScaleProductInterceptSameOrder_of_backgroundInertness
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptSameOrderAssumptionsFor hslice where
  intercept_same_order := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr R S
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr R]
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr S]
    simpa [faceScaleProductRightSliceValue, faceScaleProductLeftSliceValue]
      using
        faceScaleProductRightSliceSameOrder_of_backgroundInertness
          hfaces hax q r hq hr (Channel.uninformativeChannelU A) R S

/-- Post-HM product representation reassembler.

HM supplies all public-mixture fields, and derived background inertness supplies the product-coordinate
same-order fields.  The remaining inputs are exactly the non-HM product
representation pieces: second-coordinate affine uniqueness, slope affine
identification, and triple-product coefficient extraction. -/
theorem finiteFaceScaleProductRepresentationTheorem_of_HM
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hsecond :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
              hsingle huniq)))
    (hslope :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        FiniteFaceScaleProductSlopeAffineAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
              hsingle huniq)))
    (hextract :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
        (hgauge :
          FiniteFaceScaleCurrentProductGaugeNormalizationFor
            (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
              hsingle huniq
              (faceScaleProductInterceptSameOrder_of_backgroundInertness
                (faceScaleProductLeftSliceAffine_of_transform
                  (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                    (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                    (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                    (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
                    hsingle huniq)))
              (faceScaleProductInterceptPublicMixAffinity_of_HM hhm
                (faceScaleProductLeftSliceAffine_of_transform
                  (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                    (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                    (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                    (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
                    hsingle huniq)))
              (hsecond hsingle huniq)
              (hslope hsingle huniq)))
        (hrelV : FinitePosteriorValueRelabelingAssumptions.{u}),
        FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
          (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
            (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
            (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
            (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
            hsingle huniq
            (faceScaleProductInterceptSameOrder_of_backgroundInertness
              (faceScaleProductLeftSliceAffine_of_transform
                (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                  (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                  (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                  (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
                  hsingle huniq)))
            (faceScaleProductInterceptPublicMixAffinity_of_HM hhm
              (faceScaleProductLeftSliceAffine_of_transform
                (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                  (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                  (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                  (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
                  hsingle huniq)))
            (hsecond hsingle huniq)
            (hslope hsingle huniq))
          (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
          (faceScaleTripleProductValueAssociativity_of_valueRelabeling
            hfaces hrelV)) :
    FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces where
  base_publicMix := faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces
  coordinate_publicMix :=
    faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces
  left_slice_same_order := faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces
  intercept_same_order := by
    intro hsingle huniq
    exact faceScaleProductInterceptSameOrder_of_backgroundInertness
      (faceScaleProductLeftSliceAffine_of_transform
        (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
          (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
          (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
          (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
          hsingle huniq))
  intercept_publicMix := by
    intro hsingle huniq
    exact faceScaleProductInterceptPublicMixAffinity_of_HM hhm
      (faceScaleProductLeftSliceAffine_of_transform
        (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
          (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
          (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
          (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
          hsingle huniq))
  second_coordinate_uniqueness := hsecond
  slope_affine := hslope
  triple_coeff_extraction := hextract

/-- Post-HM product representation reassembler with triple-product coefficient
extraction discharged internally.

The remaining product-representation inputs are the genuinely coherent
second-coordinate/slope identifications.  Public mixtures come from HM,
same-order comes from derived background inertness, and triple coefficient extraction is now pure
face-scale algebra from product value associativity. -/
theorem finiteFaceScaleProductRepresentationTheorem_of_HM_and_coeffExtraction
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hsecond :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
              hsingle huniq)))
    (hslope :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        FiniteFaceScaleProductSlopeAffineAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
              hsingle huniq))) :
    FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces :=
  finiteFaceScaleProductRepresentationTheorem_of_HM hhm hfaces hsecond hslope
    (by
      intro hsingle huniq hgauge hrelV
      exact
        faceScaleTripleProductCoeffExtraction_of_valueAssociativity)

end TraceableAgency
