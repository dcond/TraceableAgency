/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction
import TraceableAgency.PureTrace.Support.PreUniversalGrouping

/-!
# Pre-Entropy Closure Wrappers

This file contains thin reassembly wrappers that keep the new pre-universal
grouping route outside the Faddeev/entropy-reduction files.
-/

namespace TraceableAgency

universe u

/--
Final interaction-collapse constructor using the TeX grouping recursion `(GR)`
instead of taking the already-rearranged weight equation `(W)` as an input.

The wrapper still takes the existing full value-relabeling input because the
current product-representation constructor has not yet been rebuilt along the
swap-free selected-representative route.
-/
noncomputable def InteractionCollapseUniversalScale_of_preUniversalGR
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hcoordValue : FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hGR :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalGroupingGRFor hfaces hprod)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_targetedFinalClosure
    hfaces hhm hrelV hsingle huniq hgauge hinterSingle hcoordValue hcoordScale
    (fun hprod =>
      finitePreUniversalGroupingWeightRecursion_of_GR
        (hGR hprod)
        (productScaleZpositive_of_sliceTransform hprod
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
            (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
            (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
            hsingle huniq)))
    hunivSingle hax

end TraceableAgency
