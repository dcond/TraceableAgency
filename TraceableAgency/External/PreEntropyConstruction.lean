/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.PreEntropyReady
import TraceableAgency.External.EntropyReduction

/-!
# Pre-Entropy Construction Lemmas

This file formalizes the forward product-lift part of the TeX proof at the
face-scale level.  The key point is that the pre-universal cross-prior
blockbridge is not an arbitrary field: it follows from the same-prior
face-scale representation, A3/A5 product-block transfer, and the product-lift
value identities supplied by face-scale product quasi-additivity.
-/

namespace TraceableAgency

universe u

/-- Left product-lift value identity for the selected face-scale representative.

This is the face-scale retyping of the paper's identity
`F_{q x r}(P x U_B) = F_q(P)`: product quasi-additivity plus zero normalization
of the uninformative background removes the right factor. -/
theorem faceScaleLeftProductLiftValue_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : TraceAxioms F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) P)) =
      hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel P) := by
  rw [leftProductLiftChannel]
  rw [hprod.product_quasi_add hax q r hq hr P
    (Channel.uninformativeChannelU B)]
  rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr]
  ring

/-- Right product-lift value identity for the selected face-scale representative.

This is the symmetric identity `F_{q x r}(U_A x Q) = F_r(Q)`. -/
theorem faceScaleRightProductLiftValue_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (Q : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) Q)) =
      hfaces.branch_result.branch_agg.value_rep.V r
        (experimentOfChannel Q) := by
  rw [rightProductLiftChannel]
  rw [hprod.product_quasi_add hax q r hq hr
    (Channel.uninformativeChannelU A) Q]
  rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq]
  ring

/-- Product-lifted comparisons are represented by the selected product-prior
face-scale value.

This is just `PosteriorValueRepresentation.represents_block_comparisons` at
the product prior, retargeted from `ScaleCoherenceStructure` to
`CoherentRelabelingFaceScalesStructure`. -/
theorem faceScaleProductLiftedComparison_represents
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    ProductLiftedComparison F q r P Q ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) Q)) := by
  have hprod : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  exact
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (rightProductLiftChannel (A := A) Q))

/-- Pre-universal cross-prior blockbridge from face-scale product
quasi-additivity.

This is the TeX blockbridge route at the selected face-scale level:
A3/A5 transfer replaces a cross-prior block comparison by a same-prior
product-lifted comparison, same-prior representation evaluates that comparison,
and product quasi-additivity identifies the two product lifts with their
unscaled component values. -/
theorem finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) :
    FinitePreUniversalCrossPriorBlockBridgeFor hfaces where
  unscaled_cross_prior_block_rep := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P Q
    have htransfer :
        F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
          ProductLiftedComparison F q r P Q :=
      product_block_transfer_of_A5_A3 F hax q r hq hr P Q
    have hrep :=
      faceScaleProductLiftedComparison_represents hfaces q r hq hr P Q
    have hleft :=
      faceScaleLeftProductLiftValue_of_productQuasiAdditivity
        hprod hax q r hq hr P
    have hright :=
      faceScaleRightProductLiftValue_of_productQuasiAdditivity
        hprod hax q r hq hr Q
    have hrep' :
        ProductLiftedComparison F q r P Q ↔
          hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) ≥
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel Q) := by
      simpa [hleft, hright] using hrep
    exact htransfer.trans hrep'

/-- Block-reveal value identity obtained directly from product quasi-additivity
via the pre-universal cross-prior blockbridge. -/
theorem finitePreUniversalBlockRevealValue_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) :
    FinitePreUniversalBlockRevealValueFor hfaces :=
  finitePreUniversalBlockRevealValue_of_crossPriorBlockBridge
    (finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod)

/-- GR from the product-lift blockbridge and the existing pre-universal chain
assembly. -/
theorem finitePreUniversalGroupingGR_of_productQuasiAdditivity_chain
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hchain : FinitePreUniversalBlockRevealChainRuleFor hfaces hprod) :
    FinitePreUniversalGroupingGRFor hfaces hprod :=
  finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
    (finitePreUniversalBlockRevealValue_of_productQuasiAdditivity hprod)
    hchain

/-- W from the product-lift blockbridge, the pre-universal chain assembly, and
the already proved positive product scale. -/
theorem finitePreUniversalGroupingWeightRecursion_of_productQuasiAdditivity_chain
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hchain : FinitePreUniversalBlockRevealChainRuleFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursion_of_GR
    (finitePreUniversalGroupingGR_of_productQuasiAdditivity_chain hchain)
    (productScaleZpositive_of_sliceTransform hprod haff)

/-- W from product quasi-additivity and the explicit lower-level block-chain
construction ingredients.  This closes the pre-universal grouping recursion
without taking the block-reveal chain rule, GR, or W as assumptions. -/
theorem finitePreUniversalGroupingWeightRecursion_of_preUniversalBlockReveal
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueIdentificationFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleIdentificationFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportFace_productScale
    (finitePreUniversalBlockRevealValue_of_productQuasiAdditivity hprod)
    (productScaleZpositive_of_sliceTransform hprod haff)
    hvalue hscale hlink href

/--
Full pre-entropy interaction-collapse constructor.

This route derives the two formerly open pre-entropy inputs before reassembly:
full-support value relabeling comes from HM/affine uniqueness plus product
normalization, and the pre-universal grouping weight recursion comes from the
block support-face construction rather than from GR/W/block-chain assumptions.
-/
noncomputable def InteractionCollapseUniversalScale_of_fullPreEntropyClosure
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueIdentificationFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleIdentificationFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  let hpos := productScaleZpositive_of_sliceTransform hprod haff
  let hfull :=
    finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
      hhm huniq hpos
  let hrec :=
    finitePreUniversalGroupingWeightRecursion_of_preUniversalBlockReveal
      haff hblockValue hblockScale hlink href
  let htwo :=
    finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  let hreference :=
    productGroupingReferenceWeight_of_twoGroupingWeightEquation htwo hpos
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces hprod
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    (productGroupingWeightConstant_of_reference hreference)
    hsingle hax

/--
Full pre-entropy interaction-collapse constructor with the harmless
representative/gauge/support choices bundled explicitly.

The bundle does not contain theorem-like product inputs: product
quasi-additivity, left-slice affine positivity, and product-revelation scale
link remain visible obligations of the pre-entropy route.
-/
noncomputable def InteractionCollapseUniversalScale_of_fullPreEntropyClosure_withNormalizations
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hgauge : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_fullPreEntropyClosure
    hfaces hhm huniq hprod haff
    hgauge.coordinate_value
    hgauge.coordinate_scale
    hgauge.block_value
    hgauge.block_scale
    hlink
    hgauge.reference_z
    hgauge.universal_singleton
    hax

/--
Minimal full pre-entropy constructor after the remaining-input audit.

The product-revelation scale link is derived from product quasi-additivity,
same-posterior-law transport, the normalized chain rule, and the coordinate
support-face value/scale normalizations.  The only bundled inputs are explicit
representative/gauge/support normalizations.
-/
noncomputable def InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hgauge : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  let hvalue :=
    coordinateRevealValueTransport_of_marginal_and_swap
      (coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
        hfaces hprod)
      (coordinateSwapFullRevelationValueTransport_of_posteriorLaw hfaces)
  let hbranch :=
    coordinateRevealBranchContinuationTransport_of_coordinateSupportFaceTransports
      (coordinateSupportFaceValueTransport_of_identification hgauge.coordinate_value)
      (coordinateSupportFaceScaleTransport_of_identification hgauge.coordinate_scale)
  let hcont :=
    coordinateRevealContinuationTransport_of_branchTransport hbranch
  let hnorm :=
    sequentialFullRevelationNormalizedChain_of_coordinateTransports
      hfaces hvalue hcont
  let hseq :=
    productRevelationSequentialScale_of_normalizedChain hfaces hnorm
  let hlink :=
    productRevelationScaleLink_of_sequentialScale hfaces hprod hseq
  InteractionCollapseUniversalScale_of_fullPreEntropyClosure_withNormalizations
    hfaces hhm huniq hprod haff hlink hgauge hax

namespace PreEntropyReadyFaceScalesStructure

/-- Build the ready object while deriving its cross-prior blockbridge from
product quasi-additivity, rather than taking the bridge as a separate external
field. -/
noncomputable def ofProductQuasiAdditivity
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hnorm : FiniteProductNormalizedSelectedRepresentativesFor hfaces)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordV : FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordZ : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hchain :
      ∀ (hprod' : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalBlockRevealChainRuleFor hfaces hprod')
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces) :
    PreEntropyReadyFaceScalesStructure F where
  hfaces := hfaces
  product_normalized_representatives := hnorm
  cross_prior_blockbridge :=
    finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod
  product_quasi_additivity := hprod
  left_slice_affine_transform := haff
  coordinate_value := hcoordV
  coordinate_scale := hcoordZ
  block_reveal_chain := hchain
  universal_singleton := hsingle

end PreEntropyReadyFaceScalesStructure

end TraceableAgency
