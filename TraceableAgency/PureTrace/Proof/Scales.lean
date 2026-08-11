/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Proof.Branch
import TraceableAgency.PureTrace.Support.EntropyReductionClosure

namespace TraceableAgency

universe u

/-!
# Paper Stage 5: compatibility of product and sequential scales

This file starts from the two cardinal structures proved in the preceding
paper stages: product quasi-additivity and a coherent branch-chain scale.  It
then carries out the product-versus-sequential comparison, the reference-free
two-grouping argument, and the collapse of the interaction coefficient.

The positivity input is stated directly as the paper's strict product-slice
inequality.  In particular, this route does not reconstruct a posterior
integrand or use an integral representation merely to prove positivity of the
already selected product gauge.
-/

/-- Exact selected relabelling immediately supplies the weaker full-support
relabel package used by the two-grouping reindexing calculation. -/
theorem fullSupportSelectedRelabeling_of_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces) :
    FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces where
  V_relabel_eq := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q _hq _hA P
    exact hsel.V_relabel_eq hax eA eO q P

/-- The nondegenerate output of the product/sequential compatibility and
two-grouping argument.  Singleton scales are deliberately not part of this
record: they are attached only after the nondegenerate scale has been compared
with the fixed binary reference. -/
structure PaperScaleComparisonCore
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) where
  product_scale_link :
    FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod
  reference_Z : FiniteProductReferenceZNormalizationFor hfaces hprod
  interaction_collapse :
    FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod

/-- Paper-faithful nondegenerate scale-comparison core.

The order of construction mirrors Appendix A: compare product and sequential
full revelation; derive the grouping recursion; evaluate the same labelled
law in two groupings; normalize the reference `Z`; and only then conclude
that the common interaction coefficient is zero. -/
noncomputable def paperScaleComparisonCore
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    : PaperScaleComparisonCore hfaces hprod := by
  let hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces :=
    coordinateSupportFaceValueSupportRead_of_selectedRelabeling hsel
  let hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces :=
    coordinateSupportFaceScaleSupportRead_of_relabeling hfaces
  let hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces :=
    blockSupportFaceValueSupportRead_of_selectedRelabeling hsel
  let hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces :=
    blockSupportFaceScaleSupportRead_of_relabeling hfaces
  let hnorm :
      FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces :=
    sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
      hfaces hboundaryValue hprod hcoordValue hcoordScale
  let hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod :=
    productRevelationScaleLink_of_sequentialScale hfaces hprod
      (productRevelationSequentialScale_of_normalizedChain hfaces hnorm)
  let hfull : FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces :=
    fullSupportSelectedRelabeling_of_selected hsel
  let hrecNoReference :
      FinitePreUniversalGroupingWeightRecursionNoReferenceFor hfaces hprod :=
    finitePreUniversalGroupingWeightRecursionNoReference_of_blockReveal_supportRead_productScale_and_Zpositive
      hboundaryValue hpos hblockValue hblockScale hlink
  let htwoNoReference :
      FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod :=
    finiteProductTwoGroupingWeightEquationNoReference_of_weightRecursion_fullSupportRelabeling
      hfull hrecNoReference hpos
  let href : FiniteProductReferenceZNormalizationFor hfaces hprod :=
    finiteProductReferenceZNormalization_of_twoGroupingNoReference
      htwoNoReference hpos
  let hrec :
      FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
    finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale_and_Zpositive
      hboundaryValue hpos hblockValue hblockScale hlink href
  let htwo :
      FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod :=
    finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  let hreference :
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod :=
    productGroupingReferenceWeight_of_twoGroupingWeightEquation htwo hpos
  let hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod :=
    productGroupingWeightConstant_of_reference hreference
  let hcollapse :
      FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod :=
    twoGroupingInteractionCollapse_of_weightConstant hfaces hprod hweight
  exact
    { product_scale_link := hlink
      reference_Z := href
      interaction_collapse := hcollapse }

/-- Once the raw construction gives scale `1` both on singleton priors and on
the fixed binary reference, the nondegenerate comparison core extends the
universal-scale conclusion to singleton alphabets. -/
theorem universalSingletonScale_of_paperCore
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hcore : PaperScaleComparisonCore hfaces hprod)
    (hreference :
      hfaces.branch_result.scale_factorization.scale
        universalScaleReferencePrior = 1)
    (hsingleOne :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A), q.FullSupport → Subsingleton A →
          hfaces.branch_result.scale_factorization.scale q = 1)
    (hax : PureTraceConditions F) :
    FiniteUniversalScaleSingletonNormalizationFor hfaces where
  scale_eq_of_subsingleton := by
    intro A B _ _ _ _ _ _ q r hq hr hsub
    rcases hsub with hA | hB
    · have hqOne := hsingleOne q hq hA
      by_cases hB' : Subsingleton B
      · rw [hqOne, hsingleOne r hr hB']
      · have hrRef :=
          scale_eq_of_productRevelation_and_interactionCollapse
            hfaces hprod hcore.product_scale_link
              hcore.interaction_collapse hax
              r universalScaleReferencePrior hr
              universalScaleReferencePrior_fullSupport hB'
              universalScaleReference_not_subsingleton
        rw [hqOne, hrRef, hreference]
    · have hrOne := hsingleOne r hr hB
      by_cases hA' : Subsingleton A
      · rw [hsingleOne q hq hA', hrOne]
      · have hqRef :=
          scale_eq_of_productRevelation_and_interactionCollapse
            hfaces hprod hcore.product_scale_link
              hcore.interaction_collapse hax
              q universalScaleReferencePrior hq
              universalScaleReferencePrior_fullSupport hA'
              universalScaleReference_not_subsingleton
        rw [hqRef, hreference, hrOne]

/-- Final Stage-5 assembly after the harmless singleton scale convention has
been justified from the already-completed nondegenerate argument. -/
noncomputable def interactionCollapse_of_paperScaleComparison
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hcore : PaperScaleComparisonCore hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  { face_scales := hfaces
    product_quasi_add := hprod
    scale_coherence :=
      scaleCoherence_of_faceScales_interactionCollapse
        hfaces hprod hcore.product_scale_link
          hcore.interaction_collapse hsingle hax
    interaction_collapse := hcore.interaction_collapse.kappa_eq_zero }

end TraceableAgency
