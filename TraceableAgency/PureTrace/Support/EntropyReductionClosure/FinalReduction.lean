/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.Grouping

namespace TraceableAgency

universe u

/-- Entropy reduction produced by the coordinate-support-read route. -/
noncomputable def entropyReduction_of_coordinateSupportRead
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_interactionCollapse
    (InteractionCollapseUniversalScale_of_coordinateSupportRead
      hfaces hboundaryValue hhm huniq hprod haff hcoordValue hcoordScale
      hblockValue hblockScale href hsingle hax)

/-- Cross-prior block representation produced by the coordinate-support-read
route. -/
noncomputable def crossPriorBlockRepresentation_of_coordinateSupportRead
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_preUniversalBridge
    (finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod)
    hax
    (entropyReduction_of_coordinateSupportRead
      hfaces hboundaryValue hhm huniq hprod haff hcoordValue hcoordScale
      hblockValue hblockScale href hsingle hax)
    rfl

/-- MI representation from the corrected coordinate support-read route.

Compared with `MIRep_of_PureTraceConditions_HM_Faddeev_withPreEntropyInputs_noCardinal`,
the coordinate hypotheses are the support-read facts and no ambient coordinate
transport/identification is assumed.  The remaining reference/singleton inputs
are deliberately left visible for the next grafting steps. -/
theorem MIRep_of_PureTraceConditions_HM_Faddeev_withCoordinateSupportRead_noCardinal
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : PureTraceConditions F) :
    PureTraceMIRepresentation F := by
  set hcross := crossPriorBlockRepresentation_of_coordinateSupportRead
    hfaces hboundaryValue hhm huniq hprod haff hcoordValue hcoordScale
    hblockValue hblockScale href hsingle hax with hcrossdef
  have hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross.entropy_reduction.scale_coherence.scale q /
          hcross.entropy_reduction.scale_coherence.scale r.restrictToSupport := by
    intro A _ _ _ q hq r _ hn hnd hb
    exact hfaces.support_face_scale_eq q hq r hn hnd hb
  set hc := wrapCross hcross hsf with hcdef
  have hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hc.entropy_reduction.Hfun q =
        normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel :=
    fun q => rfl
  have hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hc.entropy_reduction.scale_coherence q P =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    intro A O _ _ _ _ _ P q hqb
    apply field1_boundaryComplete_of_selectedValue
      hcross.entropy_reduction.scale_coherence hsf
    · intro A' O' _ _ _ _ _ r _ R
      change
        hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) =
          hfaces.branch_result.branch_agg.value_rep.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport R r))
      exact hboundaryValue.boundary_value_support r R
    · exact hqb
  have hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hc.entropy_reduction.Hfun q = hc.entropy_reduction.Hfun q.restrictToSupport := by
    intro A _ _ _ q
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    rw [hHfunId q, hHfunId q.restrictToSupport,
      show normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport Channel.idChannel q) from ?_,
      normalizedValue_restrict_idChannel_eq_idSupport hc.entropy_reduction q]
    by_cases hqf : q.FullSupport
    · exact normalizedValue_support_restrict_fullSupport_of_crossPrior
        F hax hc Channel.idChannel q hqf
    · exact hnormC Channel.idChannel q hqf
  have hrelabC : ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (qA : Dist A), qA.FullSupport →
      hc.entropy_reduction.Hfun (Relabeling.relabelDist e qA) =
        hc.entropy_reduction.Hfun qA := by
    intro A B _ _ _ _ _ _ e qA hqA
    have hqB : (Relabeling.relabelDist e qA).FullSupport :=
      Relabeling.relabelDist_fullSupport e qA hqA
    rw [wrapCross_Hfun_fullSupport hcross hsf (Relabeling.relabelDist e qA) hqB,
      wrapCross_Hfun_fullSupport hcross hsf qA hqA]
    unfold normalizedValue
    change
      hfaces.branch_result.branch_agg.value_rep.V
          (Relabeling.relabelDist e qA)
          (experimentOfChannel (Channel.idChannel : Channel B B)) /
        hfaces.branch_result.scale_factorization.scale
          (Relabeling.relabelDist e qA) =
      hfaces.branch_result.branch_agg.value_rep.V qA
          (experimentOfChannel (Channel.idChannel : Channel A A)) /
        hfaces.branch_result.scale_factorization.scale qA
    have hV := hsel.V_relabel_eq hax e e qA
      (Channel.idChannel : Channel A A)
    rw [relabelChannel_id_eq e] at hV
    have hs :=
      CoherentRelabelingFaceScalesStructure.scale_relabel_eq
        hfaces e qA hqA
    rw [hV, hs]
  have hIntC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      posteriorLawIntegral q P hc.entropy_reduction.Hfun =
        posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
          hc.entropy_reduction.Hfun := by
    intro A O _ _ _ _ _ P q
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    classical
    have hsupport := posteriorLawIntegral_restrictToSupport P q
      (fun d => hc.entropy_reduction.Hfun d)
    rw [hsupport]
    unfold posteriorLawIntegral
    apply Finset.sum_congr rfl
    intro o _
    congr 1
    set t := Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o with htdef
    haveI : Nonempty (supportSubtype (Channel.actionPushforward t (supportIncludeKernel q))) :=
      supportSubtype_nonempty _
    haveI : Nonempty (supportSubtype t) := supportSubtype_nonempty t
    have hl := hhfunC (Channel.actionPushforward t (supportIncludeKernel q))
    have hr := hhfunC t
    have hrestrict : (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport =
        Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm t.restrictToSupport :=
      restrict_supportInclude_eq_relabel_support q t
    have hrel := hrelabC (supportIncludePushforwardSupportEquiv q t).symm t.restrictToSupport
      (Dist.restrictToSupport_fullSupport t)
    calc hc.entropy_reduction.Hfun (Channel.actionPushforward t (supportIncludeKernel q))
        = hc.entropy_reduction.Hfun
            (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport := hl
      _ = hc.entropy_reduction.Hfun
            (Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
              t.restrictToSupport) := by rw [hrestrict]
      _ = hc.entropy_reduction.Hfun t.restrictToSupport := hrel
      _ = hc.entropy_reduction.Hfun t := hr.symm
  have hreg : EntropyRegularity F hc.entropy_reduction :=
    entropyRegularity_forCross hax hc hHfunId hnormC
  have hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hc.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hc.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hc.entropy_reduction.Hfun :=
    fun {K} _ _ _ Act _ _ _ _ p q =>
      coarseReveal_entropyReduction_ofFacts F hax hc hnormC hhfunC hIntC Act p q
  have hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hc.entropy_reduction.Hfun (blockEmbedDist Act k qk) = hc.entropy_reduction.Hfun qk :=
    fun {K} _ _ _ Act _ _ _ _ k qk =>
      Hfun_blockEmbed_ofFacts F hc hhfunC hrelabC Act k qk
  have hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hc.entropy_reduction.Hfun p :=
    fun {K} _ _ _ Act _ _ _ _ p q =>
      coarseVal_forCross F hax hc hreg hnormC
        (field3_restricted_coarse_reveal F hax hc hreg) hhfunC Act p q
  intro A O instA instDA instO instDO P qq qq'
  exact MIRep_ofCrossFacts
    hfad F hax hc hreg hhfunC hER hblockE hcoarse P qq qq'

/-- Scale-only cardinal alignment of the selected branch structure.

The cardinal factor changes the cross-alphabet choice of chain scale without
rescaling the selected posterior value.  Multiplying both would leave
normalized values unchanged, fail to remove the embedding defect, and destroy
the canonical boundary-to-support equality. -/
noncomputable def cardinalScaleBranchResultFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    BranchAggregationCocycleNormalizedChainRuleStructure F := by
  let hraw :=
    BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax branch
  let t : ℕ → ℝ := cardScaleTFor hhm hax branch
  exact
    { branch_agg := hraw.branch_agg
      coeff_cocycle := hraw.coeff_cocycle
      full_support_scale :=
        { scale := fun {A} _ _ _ q =>
            t (Fintype.card A) * hraw.full_support_scale.scale q
          scale_pos := by
            intro A _ _ _ q hq hnd
            exact mul_pos
              (cardScaleT_posFor hhm hax branch (Fintype.card A))
              (hraw.full_support_scale.scale_pos q hq hnd)
          branchCoeff_factorization_fullSupport := by
            intro A _ _ _ q r hq hr hnd
            rw [hraw.full_support_scale.branchCoeff_factorization_fullSupport
              q r hq hr hnd]
            have ht : t (Fintype.card A) ≠ 0 :=
              ne_of_gt
                (cardScaleT_posFor hhm hax branch (Fintype.card A))
            field_simp [ht] }
      scale_factorization :=
        { scale := fun {A} _ _ _ q =>
            t (Fintype.card A) * hraw.scale_factorization.scale q
          scale_pos := by
            intro A _ _ _ q hq
            exact mul_pos
              (cardScaleT_posFor hhm hax branch (Fintype.card A))
              (hraw.scale_factorization.scale_pos q hq)
          branchCoeff_factorization := by
            intro A O _ _ _ _ _ q hq P o hpos
            rw [hraw.scale_factorization.branchCoeff_factorization
              q hq P o hpos]
            have ht : t (Fintype.card A) ≠ 0 :=
              ne_of_gt
                (cardScaleT_posFor hhm hax branch (Fintype.card A))
            field_simp [ht] } }

/-- Coherent face scales after scale-only cardinal alignment. -/
noncomputable def cardinalGaugeFaceScalesFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    CoherentRelabelingFaceScalesStructure F := by
  let hraw :=
    BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax branch
  let hscaled := cardinalScaleBranchResultFor hhm hax branch
  exact
    { branch_result := hscaled
      scale_relabeling :=
        { scale_relabel_eq := by
            intro A B _ _ _ _ _ _ e q hq
            change
              cardScaleTFor hhm hax branch (Fintype.card B) *
                  hraw.scale_factorization.scale
                    (Relabeling.relabelDist e q) =
                cardScaleTFor hhm hax branch (Fintype.card A) *
                  hraw.scale_factorization.scale q
            rw [Fintype.card_congr e.symm]
            rw [scaleRelabel_of_FinalHM_covarianceAtomicFor
              hhm hax branch e q hq] }
      support_face_scale :=
        { support_face_scale := by
            intro A _ _ _ q hq r _ hrn hrnd hrb
            have hs :=
              cardinalGauge_hsupportFor hhm hax branch
                q hq r hrn hrnd hrb
            have ht :
                cardScaleTFor hhm hax branch (Fintype.card A) ≠ 0 :=
              ne_of_gt
                (cardScaleT_posFor hhm hax branch (Fintype.card A))
            simpa [hraw, hscaled, cardinalScaleBranchResultFor,
              cardinalGaugeFor, ht] using hs } }

/-- Singleton left-slice affine normalisation for the selected raw cardinal-gauge
face scales is internal. -/
theorem cardinalGaugeSingletonSliceFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleSingletonSliceAffineAssumptionsFor
      (cardinalGaugeFaceScalesFor hhm hax branch) :=
  finiteFaceScaleSingletonSliceAffine_of_faces
    (cardinalGaugeFaceScalesFor hhm hax branch)

/-- Selected relabelling for the scale-only cardinal alignment. -/
theorem cardinalGaugeSelectedRelabelingFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteSelectedPosteriorValueRelabelingFor
      (cardinalGaugeFaceScalesFor hhm hax branch) where
  V_relabel_eq := by
    intro _hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    change
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P)
    exact
      (finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq
        hax eA eO q P

/-- Canonical boundary-value transport survives the scale-only cardinal
alignment because its value representative is unchanged. -/
theorem cardinalGaugeBoundaryValueSupportReadFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBoundaryValueSupportReadFor
      (cardinalGaugeFaceScalesFor hhm hax branch) where
  boundary_value_support := by
    intro A O _ _ _ _ _ q _ P
    change
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P) =
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q))
    exact finalHM_supportFaceValueTransport hhm hax q P

/-- Product-intercept positive linearity for the selected raw cardinal-gauge face
scales. -/
theorem cardinalGaugeProductInterceptFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch))) :=
  faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
    (faceScaleProductInterceptSameOrder_of_backgroundInertness
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch))))
    (faceScaleProductInterceptPublicMixAffinity_of_HM
      (integralRepresentationData_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch))))
    (classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
      (integralRepresentationData_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch)))
      classicalFiniteAffineUtilityUniquenessAssumptions)

/-- Pairwise product bilinearity for the selected raw cardinal-gauge face scales. -/
noncomputable def cardinalGaugeProductPairFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
      (cardinalGaugeFaceScalesFor hhm hax branch) :=
  faceScaleProductPairwiseBilinearity_of_multiPieces
    (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      (integralRepresentationData_of_FinalHMInterface
        hhm)
      (cardinalGaugeSingletonSliceFor hhm hax branch))
    (cardinalGaugeProductInterceptFor hhm hax branch)
    (faceScaleProductSlopeAffine_of_selectedRelabeling
      (cardinalGaugeSelectedRelabelingFor hhm hax branch)
      (cardinalGaugeProductInterceptFor hhm hax branch))

/-- Triple-product value associativity for the selected raw cardinal-gauge face
scales, derived from selected relabelling. -/
theorem cardinalGaugeTripleProductValueAssociativityFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
      (cardinalGaugeFaceScalesFor hhm hax branch) :=
  faceScaleTripleProductValueAssociativity_of_selectedRelabeling
    (cardinalGaugeFaceScalesFor hhm hax branch)
    (cardinalGaugeSelectedRelabelingFor hhm hax branch)

/-- The selected coboundary product transform for the cardinal-gauge face
scales.  This replaces the former product-gauge normalization by the explicit
coboundary constructed from product coefficient associativity. -/
noncomputable def cardinalGaugeProductCoboundaryTransformFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleProductGaugeTransformNondegenerateFor
      (cardinalGaugeProductPairFor hhm hax branch) :=
  cobGaugeSFProductTransform_selected
    (cardinalGaugeProductPairFor hhm hax branch)
    (cardinalGaugeSelectedRelabelingFor hhm hax branch)
    (cardinalGaugeTripleProductValueAssociativityFor hhm hax branch)
    hax

/-- Product quasi-additivity for the selected cardinal-gauge face scales after
the internally constructed coboundary product transform. -/
noncomputable def cardinalGaugeProductQuasiAdditivityFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteProductQuasiAdditivityForFaceScales
      ((cardinalGaugeFaceScalesFor hhm hax branch).gaugeTransform
        (cardinalGaugeProductCoboundaryTransformFor
          hhm hax branch).gauge) :=
  productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData_nondegenerate
    (cardinalGaugeProductPairFor hhm hax branch)
    (cardinalGaugeProductCoboundaryTransformFor hhm hax branch)
    (cardinalGaugeTripleProductValueAssociativityFor hhm hax branch)

/-- The final constructed face-scale representative used by the paper-facing
cardinal-gauge route.  The branch data is constructed internally from the HM
interface and `PureTraceConditions`, so this definition has no branch hypothesis. -/
noncomputable def finalConstructedCardinalGaugeFaceScales
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    CoherentRelabelingFaceScalesStructure F :=
  let branchData :=
    finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax
  (cardinalGaugeFaceScalesFor hhm hax branchData).gaugeTransform
    (cardinalGaugeProductCoboundaryTransformFor
      hhm hax branchData).gauge

/-- Product quasi-additivity for the final constructed face-scale
representative. -/
noncomputable def finalConstructedCardinalGaugeProductQuasiAdditivity
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteProductQuasiAdditivityForFaceScales
      (finalConstructedCardinalGaugeFaceScales hhm hax) := by
  dsimp [finalConstructedCardinalGaugeFaceScales]
  exact cardinalGaugeProductQuasiAdditivityFor hhm hax
    (finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax)

/-- Selected value relabeling for the final constructed cardinal/product-gauge
representative. -/
theorem finalConstructedCardinalGaugeSelectedRelabeling
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteSelectedPosteriorValueRelabelingFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) := by
  dsimp [finalConstructedCardinalGaugeFaceScales]
  exact
    finiteSelectedPosteriorValueRelabeling_gaugeTransform
      (cardinalGaugeSelectedRelabelingFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax))
      (cardinalGaugeProductCoboundaryTransformFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax)).gauge

/-- Boundary-value transport for the final scale-aligned/product-gauged
representative.  The cardinal alignment is scale-only, and the subsequent
coboundary gauge is support-coherent. -/
theorem finalConstructedBoundaryValueSupportRead_of_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteBoundaryValueSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) := by
  dsimp [finalConstructedCardinalGaugeFaceScales]
  exact
    finiteBoundaryValueSupportRead_gaugeTransform
      (cardinalGaugeBoundaryValueSupportReadFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax))
      (cardinalGaugeProductCoboundaryTransformFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax)).gauge

/-- Coordinate support-read value transport for the final constructed
representative.  This is the support-face theorem replacing the false ambient
coordinate-value convention. -/
theorem finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteCoordinateSupportFaceValueSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  coordinateSupportFaceValueSupportRead_of_selectedRelabeling
    (finalConstructedCardinalGaugeSelectedRelabeling hhm hax)

/-- Coordinate support-read scale transport for the final constructed
representative.  This is the support-face scale theorem replacing the false
ambient coordinate-scale convention. -/
theorem finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteCoordinateSupportFaceScaleSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  coordinateSupportFaceScaleSupportRead_of_relabeling
    (finalConstructedCardinalGaugeFaceScales hhm hax)

/-- Block support-read value transport for the final constructed
representative. -/
theorem finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteBlockSupportFaceValueSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  blockSupportFaceValueSupportRead_of_selectedRelabeling
    (finalConstructedCardinalGaugeSelectedRelabeling hhm hax)

/-- Block support-read scale transport for the final constructed
representative. -/
theorem finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteBlockSupportFaceScaleSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  blockSupportFaceScaleSupportRead_of_relabeling
    (finalConstructedCardinalGaugeFaceScales hhm hax)

/-- The final constructed representative assigns scale `1` to full-support
subsingleton alphabets.  This is definitional from the support-face coboundary
gauge, the cardinal gauge value `t_1 = 1`, and the selected atomic singleton
scale. -/
theorem finalConstructedScale_eq_one_of_subsingleton
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : Subsingleton A) :
    (finalConstructedCardinalGaugeFaceScales hhm hax).branch_result.scale_factorization.scale q =
      1 := by
  classical
  letI : Subsingleton A := hA
  let branch := finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax
  change
    cobGaugeSF (cardinalGaugeProductPairFor hhm hax branch) hax q *
      ((cardinalGaugeFor hhm hax branch).gauge q *
        selectedAtomicBranchScaleFor hhm hax branch q) = 1
  have hsupport : Subsingleton (supportSubtype q) := by
    refine ⟨?_⟩
    intro x y
    exact Subtype.ext (Subsingleton.elim x.1 y.1)
  have hcob :
      cobGaugeSF (cardinalGaugeProductPairFor hhm hax branch) hax q = 1 := by
    unfold cobGaugeSF
    rw [if_pos hsupport]
  have hcard : Fintype.card A = 1 := by
    exact Fintype.card_eq_one_iff.mpr
      ⟨Classical.arbitrary A, fun y => Subsingleton.elim y (Classical.arbitrary A)⟩
  have hcgauge : (cardinalGaugeFor hhm hax branch).gauge q = 1 := by
    dsimp [cardinalGaugeFor, cardScaleTFor]
    rw [hcard]
    norm_num
  have hnotnd :
      ¬ ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
    rintro ⟨a, b, hne, _ha, _hb⟩
    exact hne (Subsingleton.elim a b)
  have hsel :
      selectedAtomicBranchScaleFor hhm hax branch q = 1 := by
    rw [selectedAtomicBranchScaleFor_fullSupport hhm hax branch q hq]
    simp only [branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
      hq, Dist.uniform_fullSupport, dif_pos]
    rw [dif_neg hnotnd]
  rw [hcob, hcgauge, hsel]
  ring

/-- The binary reference prior has final constructed scale `1`.  The only
coefficient calculation is product-swap symmetry at the binary reference, which
identifies the right and left product coefficients in the coboundary gauge. -/
theorem finalConstructedReferenceScale_eq_one
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    (finalConstructedCardinalGaugeFaceScales hhm hax).branch_result.scale_factorization.scale
      universalScaleReferencePrior = 1 := by
  classical
  let branch := finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions hhm hax
  let hpair := cardinalGaugeProductPairFor hhm hax branch
  let hsel := cardinalGaugeSelectedRelabelingFor hhm hax branch
  change
    cobGaugeSF hpair hax universalScaleReferencePrior *
      ((cardinalGaugeFor hhm hax branch).gauge universalScaleReferencePrior *
        selectedAtomicBranchScaleFor hhm hax branch universalScaleReferencePrior) = 1
  have href_nd : ¬ Subsingleton universalScaleReferenceType :=
    universalScaleReference_not_subsingleton
  have hcob : cobGaugeSF hpair hax universalScaleReferencePrior = 1 := by
    rw [cobGaugeSF_eq_cobGauge_of_fullSupport_selected
      hpair hsel hax universalScaleReferencePrior
      universalScaleReferencePrior_fullSupport href_nd]
    unfold cobGauge
    change
      hpair.rightCoeff hax universalScaleReferencePrior universalScaleReferencePrior /
          hpair.leftCoeff hax universalScaleReferencePrior universalScaleReferencePrior =
        1
    have hswap :=
      fs_rightCoeff_eq_swapped_leftCoeff_selected
        hpair hsel hax universalScaleReferencePrior universalScaleReferencePrior
        universalScaleReferencePrior_fullSupport universalScaleReferencePrior_fullSupport
        href_nd
    have hleft_pos :
        0 < hpair.leftCoeff hax universalScaleReferencePrior universalScaleReferencePrior :=
      hpair.leftCoeff_pos hax universalScaleReferencePrior universalScaleReferencePrior
        universalScaleReferencePrior_fullSupport universalScaleReferencePrior_fullSupport
    rw [hswap]
    exact div_self (ne_of_gt hleft_pos)
  have hcard : Fintype.card universalScaleReferenceType.{u} = 2 := by
    simp [universalScaleReferenceType]
  have hcgauge :
      (cardinalGaugeFor hhm hax branch).gauge universalScaleReferencePrior = 1 := by
    simp [cardinalGaugeFor, cardScaleTFor, hcard]
  have hnd :
      ∃ a b : universalScaleReferenceType, a ≠ b :=
    ⟨ULift.up true, ULift.up false, by
      intro h
      cases congrArg ULift.down h⟩
  have hsel_scale :
      selectedAtomicBranchScaleFor hhm hax branch universalScaleReferencePrior = 1 := by
    have hraw :=
      scale_uniform_eq_oneAtomicFor hhm hax branch
        (A := universalScaleReferenceType) hnd
    change selectedAtomicBranchScaleFor hhm hax branch
        (Dist.uniform (A := universalScaleReferenceType)) = 1 at hraw
    simpa [universalScaleReferencePrior] using hraw
  rw [hcob, hcgauge, hsel_scale]
  ring

/-- The product-reference `Z` normalization for the final constructed
cardinal-gauge representative is internal.  The proof uses the reference-free
two-grouping calculation: `Z` is constant on nondegenerate full-support priors,
and multiplicativity at `q_ref × q_ref` plus positivity forces the constant to
be `1`. -/
theorem finalConstructedProductReferenceZNormalization_of_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteProductReferenceZNormalizationFor
      (finalConstructedCardinalGaugeFaceScales hhm hax)
      (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax) := by
  let hfacesKnown : CoherentRelabelingFaceScalesStructure F :=
    finalConstructedCardinalGaugeFaceScales hhm hax
  let hprodKnown :
      FiniteProductQuasiAdditivityForFaceScales hfacesKnown :=
    finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax
  let hhmClassical :
      FinitePosteriorIntegralRepresentationData.{u} :=
    integralRepresentationData_of_FinalHMInterface hhm
  let huniqKnown : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} :=
    classicalFiniteAffineUtilityUniquenessAssumptions
  let haffKnown :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor
        hfacesKnown :=
    finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      hhmClassical
      (finiteFaceScaleSingletonSliceAffine_of_faces hfacesKnown)
  let hboundaryValueKnown :
      FiniteBoundaryValueSupportReadFor hfacesKnown :=
    finalConstructedBoundaryValueSupportRead_of_FinalHM_PureTraceConditions hhm hax
  let hcoordValueKnown :
      FiniteCoordinateSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hcoordScaleKnown :
      FiniteCoordinateSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hblockValueKnown :
      FiniteBlockSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hblockScaleKnown :
      FiniteBlockSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hnorm :=
    sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
      hfacesKnown hboundaryValueKnown hprodKnown
      hcoordValueKnown hcoordScaleKnown
  let hlink :=
    productRevelationScaleLink_of_sequentialScale hfacesKnown hprodKnown
      (productRevelationSequentialScale_of_normalizedChain hfacesKnown hnorm)
  let hpos := productScaleZpositive_of_sliceTransform hprodKnown haffKnown
  let hfull :=
    finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
      hhmClassical huniqKnown hpos
  let hrec :=
    finitePreUniversalGroupingWeightRecursionNoReference_of_blockReveal_supportRead_productScale
      hboundaryValueKnown haffKnown hblockValueKnown hblockScaleKnown hlink
  let htwo :=
    finiteProductTwoGroupingWeightEquationNoReference_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  exact finiteProductReferenceZNormalization_of_twoGroupingNoReference htwo hpos

/-- Given the remaining product-reference `Z` normalization, every nondegenerate
full-support prior has final constructed scale `1`.  This packages the already
proved product-revelation link, grouping-weight collapse, and the reference-scale
calculation above. -/
theorem finalConstructedNondegenerateScale_eq_one_of_referenceZ
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    (finalConstructedCardinalGaugeFaceScales hhm hax).branch_result.scale_factorization.scale q =
      1 := by
  classical
  let hfacesKnown : CoherentRelabelingFaceScalesStructure F :=
    finalConstructedCardinalGaugeFaceScales hhm hax
  let hprodKnown :
      FiniteProductQuasiAdditivityForFaceScales hfacesKnown :=
    finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax
  let hhmClassical :
      FinitePosteriorIntegralRepresentationData.{u} :=
    integralRepresentationData_of_FinalHMInterface hhm
  let huniqKnown : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} :=
    classicalFiniteAffineUtilityUniquenessAssumptions
  let haffKnown :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor
        hfacesKnown :=
    finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      hhmClassical
      (finiteFaceScaleSingletonSliceAffine_of_faces hfacesKnown)
  let hboundaryValueKnown :
      FiniteBoundaryValueSupportReadFor hfacesKnown :=
    finalConstructedBoundaryValueSupportRead_of_FinalHM_PureTraceConditions hhm hax
  let hcoordValueKnown :
      FiniteCoordinateSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hcoordScaleKnown :
      FiniteCoordinateSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hblockValueKnown :
      FiniteBlockSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hblockScaleKnown :
      FiniteBlockSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hnorm :=
    sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
      hfacesKnown hboundaryValueKnown hprodKnown
      hcoordValueKnown hcoordScaleKnown
  let hlink :=
    productRevelationScaleLink_of_sequentialScale hfacesKnown hprodKnown
      (productRevelationSequentialScale_of_normalizedChain hfacesKnown hnorm)
  let hpos := productScaleZpositive_of_sliceTransform hprodKnown haffKnown
  let hfull :=
    finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
      hhmClassical huniqKnown hpos
  let hrec :=
    finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale
      hboundaryValueKnown haffKnown hblockValueKnown hblockScaleKnown
      hlink reference_z
  let htwo :=
    finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  let hreference :=
    productGroupingReferenceWeight_of_twoGroupingWeightEquation htwo hpos
  let hweight :=
    productGroupingWeightConstant_of_reference hreference
  let hcollapse :=
    twoGroupingInteractionCollapse_of_weightConstant
      hfacesKnown hprodKnown hweight
  have hscale_eq :=
    scale_eq_of_productRevelation_and_interactionCollapse
      hfacesKnown hprodKnown hlink hcollapse hax q
      universalScaleReferencePrior hq universalScaleReferencePrior_fullSupport
      hA universalScaleReference_not_subsingleton
  exact hscale_eq.trans (finalConstructedReferenceScale_eq_one hhm hax)

/-- The remaining singleton universal-scale normalization follows from the final
constructed singleton/reference scale computations plus the product-reference `Z`
normalization.  Thus it is no longer an independent pre-entropy input once
`reference_z` is available. -/
theorem finalConstructedUniversalScaleSingleton_of_referenceZ_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax)) :
    FiniteUniversalScaleSingletonNormalizationFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) where
  scale_eq_of_subsingleton := by
    intro A B _ _ _ _ _ _ q r hq hr hsub
    rcases hsub with hA | hB
    · have hq1 :=
        finalConstructedScale_eq_one_of_subsingleton hhm hax q hq hA
      by_cases hB' : Subsingleton B
      · have hr1 :=
          finalConstructedScale_eq_one_of_subsingleton hhm hax r hr hB'
        rw [hq1, hr1]
      · have hr1 :=
          finalConstructedNondegenerateScale_eq_one_of_referenceZ
            hhm hax reference_z r hr hB'
        rw [hq1, hr1]
    · have hr1 :=
        finalConstructedScale_eq_one_of_subsingleton hhm hax r hr hB
      by_cases hA' : Subsingleton A
      · have hq1 :=
          finalConstructedScale_eq_one_of_subsingleton hhm hax q hq hA'
        rw [hq1, hr1]
      · have hq1 :=
          finalConstructedNondegenerateScale_eq_one_of_referenceZ
            hhm hax reference_z q hq hA'
        rw [hq1, hr1]

/-- Universal singleton scale normalization for the final constructed
representative, with the product-reference normalization now supplied
internally. -/
theorem finalConstructedUniversalScaleSingleton_of_FinalHM_PureTraceConditions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    FiniteUniversalScaleSingletonNormalizationFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  finalConstructedUniversalScaleSingleton_of_referenceZ_FinalHM_PureTraceConditions
    hhm hax
    (finalConstructedProductReferenceZNormalization_of_FinalHM_PureTraceConditions
      hhm hax)

/-- MI route using the corrected coordinate support-read facts internally.

The coordinate value and scale facts are constructed from `FinalHMInterface`
  and `PureTraceConditions`; only the still-unrepaired reference/singleton pre-entropy
  obligations remain explicit. -/
theorem MIRep_of_PureTraceConditions_FinalHM_Faddeev_withCoordinateSupportReadPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    (universal_singleton :
      FiniteUniversalScaleSingletonNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)) :
    PureTraceMIRepresentation F := by
  let hfacesKnown : CoherentRelabelingFaceScalesStructure F :=
    finalConstructedCardinalGaugeFaceScales hhm hax
  let hprodKnown :
      FiniteProductQuasiAdditivityForFaceScales hfacesKnown :=
    finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax
  let hhmClassical : FinitePosteriorIntegralRepresentationData.{u} :=
    integralRepresentationData_of_FinalHMInterface hhm
  let huniqKnown : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} :=
    classicalFiniteAffineUtilityUniquenessAssumptions
  let haffKnown :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor
        hfacesKnown :=
    finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      hhmClassical
      (finiteFaceScaleSingletonSliceAffine_of_faces hfacesKnown)
  let hboundaryValueKnown :
      FiniteBoundaryValueSupportReadFor hfacesKnown :=
    finalConstructedBoundaryValueSupportRead_of_FinalHM_PureTraceConditions hhm hax
  let hcoordValueKnown :
      FiniteCoordinateSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hcoordScaleKnown :
      FiniteCoordinateSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hblockValueKnown :
      FiniteBlockSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hblockScaleKnown :
      FiniteBlockSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_PureTraceConditions
      hhm hax
  let hselKnown :
      FiniteSelectedPosteriorValueRelabelingFor hfacesKnown :=
    finalConstructedCardinalGaugeSelectedRelabeling hhm hax
  exact
    @MIRep_of_PureTraceConditions_HM_Faddeev_withCoordinateSupportRead_noCardinal
      hfad F hfacesKnown hboundaryValueKnown hhmClassical huniqKnown
      hprodKnown haffKnown hcoordValueKnown hcoordScaleKnown
      hblockValueKnown hblockScaleKnown reference_z universal_singleton
      hselKnown hax

/-- MI route after eliminating the universal-singleton pre-entropy input.

The only remaining pre-entropy normalization at this boundary is the
product-reference `Z` normalization; the universal singleton scale condition is
constructed from it and the final HM/trace-axiom representative. -/
theorem MIRep_of_PureTraceConditions_FinalHM_Faddeev_onlyReferenceZPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax)) :
    PureTraceMIRepresentation F := by
  exact
    MIRep_of_PureTraceConditions_FinalHM_Faddeev_withCoordinateSupportReadPreEntropy
      hfad hhm hax reference_z
      (finalConstructedUniversalScaleSingleton_of_referenceZ_FinalHM_PureTraceConditions
        hhm hax reference_z)

/-- Convention-free MI route.

All support restriction, relabelling covariance, cardinal scale alignment,
and pre-entropy normalizations for the selected canonical posterior value are
derived internally. -/
theorem MIRep_of_PureTraceConditions_FinalHM_Faddeev
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F) :
    PureTraceMIRepresentation F := by
  exact
    MIRep_of_PureTraceConditions_FinalHM_Faddeev_onlyReferenceZPreEntropy
      hfad hhm hax
      (finalConstructedProductReferenceZNormalization_of_FinalHM_PureTraceConditions
        hhm hax)

end TraceableAgency
