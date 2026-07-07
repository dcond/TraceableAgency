/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.PreEntropyClosure
import TraceableAgency.External.PreUniversalBlockBridge

/-!
# Full Pre-Entropy Closure Wrappers

This file adds the sharpest current pre-entropy constructor: it replaces the
external `(GR)` input by the earlier block-reveal identity plus branch/chain
assembly, while leaving the still-open cardinal relabeling input explicit.
-/

namespace TraceableAgency

universe u

/--
Interaction-collapse constructor from the pre-universal block-reveal identity
and the block-reveal branch/chain assembly.

The constructor still takes the old full value-relabeling input because the
non-circular selected actionbase/permutation-invariance proof is not completed
in Lean.  The grouping input is reduced from `(GR)` to the two earlier named
obligations in `PreUniversalBlockBridge.lean`.
-/
noncomputable def InteractionCollapseUniversalScale_of_blockRevealChain
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hcoordValue : FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hblock : FinitePreUniversalBlockRevealValueFor hfaces)
    (hchain :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalBlockRevealChainRuleFor hfaces hprod)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_preUniversalGR
    hfaces hhm hrelV hsingle huniq hgauge hinterSingle hcoordValue hcoordScale
    (fun hprod =>
      finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
        hblock (hchain hprod))
    hunivSingle hax

end TraceableAgency
