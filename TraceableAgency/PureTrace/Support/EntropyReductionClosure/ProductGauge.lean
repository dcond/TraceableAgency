/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.SingletonInteraction

namespace TraceableAgency

universe u

/-- Current-representative nondegenerate product-gauge normalization. -/
structure FiniteFaceScaleProductGaugeNormalizationNondegenerateFor
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  leftCoeff_normalized_nd :
    ∀ (hax : PureTraceConditions F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A),
      hpair.leftCoeff hax q r = 1
  rightCoeff_normalized_nd :
    ∀ (hax : PureTraceConditions F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hB : ¬ Subsingleton B),
      hpair.rightCoeff hax q r = 1

/-- Nondegenerate product-gauge transform data.

Unlike `FiniteFaceScaleProductGaugeTransformFor`, this does not impose
normalization on behaviorally unidentified singleton-factor coefficients. -/
structure FiniteFaceScaleProductGaugeTransformNondegenerateFor
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    where
  gauge : CoherentFaceScaleGauge.{u}
  transformed_leftCoeff_normalized_nd :
    ∀ (hax : PureTraceConditions F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A),
      faceScaleGaugeTransformedLeftCoeff hpair gauge hax q r = 1
  transformed_rightCoeff_normalized_nd :
    ∀ (hax : PureTraceConditions F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hB : ¬ Subsingleton B),
      faceScaleGaugeTransformedRightCoeff hpair gauge hax q r = 1

/-- Normalized product bilinear form using only nondegenerate coefficient
normalization. -/
theorem faceScaleProductPairBilinear_normalized_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm :
      FiniteFaceScaleProductGaugeNormalizationNondegenerateFor hpair)
    (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
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
  rw [hnorm.leftCoeff_normalized_nd hax q r hq hr hA]
  rw [hnorm.rightCoeff_normalized_nd hax q r hq hr hB]
  ring

/-- Coefficient extraction from triple-product value associativity and
nondegenerate product-gauge normalization. -/
theorem faceScaleTripleProductCoeffExtraction_of_valueAssociativity_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    {hnorm : FiniteFaceScaleProductGaugeNormalizationNondegenerateFor hpair}
    {htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces} :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair where
  interaction_assoc_xy := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
    have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
    have hxne :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hyne :
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
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
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.idChannel : Channel B B))
        (Channel.uninformativeChannelU C)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.uninformativeChannelU C))] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q r hq hr hA hB
        (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        r s hr hs hB hC
        (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized s hs] at hval
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
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
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
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.uninformativeChannelU B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q r hq hr hA hB
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        r s hr hs hB hC
        (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr] at hval
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
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
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
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.uninformativeChannelU A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q r hq hr hA hB
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        r s hr hs hB hC
        (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hyzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Product quasi-additivity from pairwise bilinearity, nondegenerate
normalization, and interaction associativity. Singleton factors are handled by
value-zero, not coefficient normalizations. -/
noncomputable def productQuasiAdditivityForFaceScales_of_components_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm :
      FiniteFaceScaleProductGaugeNormalizationNondegenerateFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces where
  kappa := faceScaleInteractionReferenceKappa hpair
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    by_cases hsubA : Subsingleton A
    · haveI : Subsingleton A := hsubA
      have hVq :
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep q hq P
      rw [hVq]
      by_cases hsubB : Subsingleton B
      · haveI : Subsingleton B := hsubB
        have hVr :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) = 0 :=
          branchValue_channel_eq_zero_of_subsingleton F
            hfaces.branch_result.branch_agg.value_rep r hr R
        rw [hVr]
        ring
      · rw [hnorm.rightCoeff_normalized_nd hax q r hq hr hsubB]
        ring
    · by_cases hsubB : Subsingleton B
      · haveI : Subsingleton B := hsubB
        have hVr :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) = 0 :=
          branchValue_channel_eq_zero_of_subsingleton F
            hfaces.branch_result.branch_agg.value_rep r hr R
        rw [hVr]
        rw [hnorm.leftCoeff_normalized_nd hax q r hq hr hsubA]
        ring
      · rw [hnorm.leftCoeff_normalized_nd hax q r hq hr hsubA]
        rw [hnorm.rightCoeff_normalized_nd hax q r hq hr hsubB]
        rw [faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc hax q r hq hr hsubA hsubB]
        ring

/-- Product quasi-additivity for a coherently transformed representative using
only nondegenerate product normalization. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge :
      FiniteFaceScaleProductGaugeTransformNondegenerateFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_components_nondegenerate
    (faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
    { leftCoeff_normalized_nd := by
        intro hax A B _ _ _ _ _ _ q r hq hr hA
        exact hgauge.transformed_leftCoeff_normalized_nd hax q r hq hr hA
      rightCoeff_normalized_nd := by
        intro hax A B _ _ _ _ _ _ q r hq hr hB
        exact hgauge.transformed_rightCoeff_normalized_nd hax q r hq hr hB }
    (faceScaleTripleProductCoeffExtraction_of_valueAssociativity_nondegenerate
      (hpair := faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
      (hnorm :=
        { leftCoeff_normalized_nd := by
            intro hax A B _ _ _ _ _ _ q r hq hr hA
            exact hgauge.transformed_leftCoeff_normalized_nd hax q r hq hr hA
          rightCoeff_normalized_nd := by
            intro hax A B _ _ _ _ _ _ q r hq hr hB
            exact hgauge.transformed_rightCoeff_normalized_nd hax q r hq hr hB })
      (htriple := faceScaleTripleProductValueAssociativity_gaugeTransform
        htriple hgauge.gauge))

/-- The selected coboundary gauge gives the nondegenerate product-normalization
transform for the selected `hax`. Universality over proof arguments follows
from proof irrelevance of `PureTraceConditions F`. -/
noncomputable def cobGaugeSFProductTransform_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax0 : PureTraceConditions F) :
    FiniteFaceScaleProductGaugeTransformNondegenerateFor hpair where
  gauge := cobGaugeSFGauge_selected hpair hsel hax0
  transformed_leftCoeff_normalized_nd := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA
    have hp : hax = hax0 := Subsingleton.elim _ _
    cases hp
    exact cobGaugeSFGauge_leftCoeff_normalized_selected
      hpair hsel htriple hax0 q r hq hr hA
  transformed_rightCoeff_normalized_nd := by
    intro hax A B _ _ _ _ _ _ q r hq hr hB
    have hp : hax = hax0 := Subsingleton.elim _ _
    cases hp
    exact cobGaugeSFGauge_rightCoeff_normalized_selected
      hpair hsel htriple hax0 q r hq hr hB


/-- Product quasi-additivity for a positive-gauge representative with the
intercept positive-linearity field discharged internally. -/
noncomputable def productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData_internalIntercept
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : PureTraceConditions F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          hslope)) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData
    hhm hfaith hax hgauge hrel hsupport hsingleSlice
    (productInterceptPositiveLinear_of_FinalHM_positiveGauge
      hhm hfaith hax hgauge hrel hsupport hsingleSlice)
    hslope hcurrentGauge htriple hsingleInteraction

/-- Product quasi-additivity for a positive-gauge representative whose selected
representatives have already been product-normalized.

The product-normalized selected representative package supplies selected value
relabeling; selected relabeling supplies both the product-swap slope proof and
triple-product value associativity.  Thus this constructor no longer takes the
obsolete all-representatives relabeling package, an explicit slope-affinity
field, or an explicit triple-product associativity field. -/
noncomputable def productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : PureTraceConditions F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hnorm :
      FiniteSelectedPosteriorValueRelabelingFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hcurrentGauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            hnorm
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm hfaith hax hgauge hrel hsupport hsingleSlice))))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            hnorm
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm hfaith hax hgauge hrel hsupport hsingleSlice)))) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData_internalIntercept
    hhm hfaith hax hgauge hrel hsupport hsingleSlice
    (faceScaleProductSlopeAffine_of_selectedRelabeling
      hnorm
      (productInterceptPositiveLinear_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport hsingleSlice))
    hcurrentGauge
    (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport)
      hnorm)
    hsingleInteraction

/-- Product-normalised coherent face scales obtained by applying the selected
positive product gauge to the raw coherent representatives. -/
noncomputable def productNormalizedFaceScales_of_FinalHM_gauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : PureTraceConditions F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair) :
    CoherentRelabelingFaceScalesStructure F :=
  (rawCoherentFaceScales_of_FinalHM_faithfulBranch
    hhm hfaith hax hscaleRelabel hfaceScale).gaugeTransform hgauge.gauge

/-- Product quasi-additivity for the product-gauge-normalised representatives.

The product quasi-additivity package is constructed for the transformed
witness, not required for arbitrary raw face scales. -/
noncomputable def productQuasiAdditivity_of_FinalHM_gauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : PureTraceConditions F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)) :
    FiniteProductQuasiAdditivityForFaceScales
      (productNormalizedFaceScales_of_FinalHM_gauge
        hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge) :=
  productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData
    hpair hgauge htriple hsingle
/-! ## Boundary-completed scale: eliminating the boundary normalized-value support field

The following machinery proves `FiniteNormalizedValueSupportBoundaryAssumptions`
(field 1 of `FiniteCardinalSupportBoundaryAssumptions`) rather than assuming it,
for a boundary-completed scale.  `wrapScale` completes the prior-dependent scale
to its support-face value at nondegenerate boundary priors (leaving full-support
and singleton priors untouched); `boundaryCompleteScale` re-proves the four
`ScaleCoherenceStructure` fields; `wrapCross` transports the cross-prior block
representation (whose comparison clause is full-support-guarded, where the
wrapped scale agrees with the original); and `field1_wrapper` /
`normalizedValueSupportBoundary_of_boundaryComplete` prove the boundary
normalized-value support restriction from the Herstein--Milnor marginal-value
support-face coherence clause plus the coherent support-face scale relation. -/

/-- Equivalence `A ≃ supportSubtype q` for a full-support `q`. -/
noncomputable def fsSupportEquiv {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (hq : q.FullSupport) : A ≃ supportSubtype q where
  toFun a := ⟨a, hq a⟩
  invFun s := s.1
  left_inv a := rfl
  right_inv s := by cases s; rfl

theorem restrictToSupport_eq_relabel_fullSupport {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (hq : q.FullSupport) :
    q.restrictToSupport = Relabeling.relabelDist (fsSupportEquiv q hq) q := by
  ext s; rcases s with ⟨a, ha⟩
  simp [Relabeling.relabelDist, fsSupportEquiv, Dist.restrictToSupport_apply]

end TraceableAgency
