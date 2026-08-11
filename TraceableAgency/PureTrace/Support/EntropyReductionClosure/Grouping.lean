/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.BoundaryCompletion

namespace TraceableAgency

universe u

/-- Grouping recursion with block posteriors read on support faces. -/
theorem finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale_and_Zpositive
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursion_of_blockReveal
    (finitePreUniversalBlockRevealValue_of_productQuasiAdditivity hprod)
    (preUniversalBlockRevealChainRule_of_branchChain_supportRead_productScale
      hboundaryValue hvalue hscale hlink href)
    hpos

/-- Backward-compatible specialization using the historical slice-transform
proof of product-slope positivity. -/
theorem finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale_and_Zpositive
    hboundaryValue (productScaleZpositive_of_sliceTransform hprod haff)
    hvalue hscale hlink href

/-- Reference-free version of the pre-universal weight recursion.  The old
package also carried `Z(q_ref)=1`; the field below is the real recursion content
needed for the two-grouping calculation. -/
structure FinitePreUniversalGroupingWeightRecursionNoReferenceFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  weight_recursion :
    ∀ (hax : PureTraceConditions F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (f : ∀ k, Dist (Act k))
      (_hp : p.FullSupport)
      (_hf : ∀ k, (f k).FullSupport)
      (_hsigma : (sigmaDist p f).FullSupport)
      (_hKnd : ¬ Subsingleton K)
      (_hAnd : ∀ k, ¬ Subsingleton (Act k)),
      (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f))⁻¹ =
        (productScaleZForFaceScales hfaces hprod hax p)⁻¹ *
          ∑ k, p k *
            (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹

private theorem weightRecursion_algebra_of_groupingGR_noReference
    {K : Type u} [Fintype K]
    (p : Dist K)
    (κ Hsigma Hp : ℝ) (Hf : K → ℝ)
    (hZsigma_pos : 0 < 1 + κ * Hsigma)
    (hZp_pos : 0 < 1 + κ * Hp)
    (hZf_pos : ∀ k, 0 < 1 + κ * Hf k)
    (hGR :
      Hsigma =
        Hp + (1 + κ * Hsigma) *
          ∑ k, p k * (Hf k / (1 + κ * Hf k))) :
    (1 + κ * Hsigma)⁻¹ =
      (1 + κ * Hp)⁻¹ * ∑ k, p k * (1 + κ * Hf k)⁻¹ := by
  classical
  by_cases hκ : κ = 0
  · simp [hκ, p.sum_eq_one]
  · let Zsigma : ℝ := 1 + κ * Hsigma
    let Zp : ℝ := 1 + κ * Hp
    let Zf : K → ℝ := fun k => 1 + κ * Hf k
    let S : ℝ := ∑ k, p k * (Zf k)⁻¹
    let T : ℝ := ∑ k, p k * (Hf k / Zf k)
    have hZsigma_ne : Zsigma ≠ 0 :=
      ne_of_gt (by simpa [Zsigma] using hZsigma_pos)
    have hZp_ne : Zp ≠ 0 :=
      ne_of_gt (by simpa [Zp] using hZp_pos)
    have hZf_ne : ∀ k, Zf k ≠ 0 := fun k =>
      ne_of_gt (by simpa [Zf] using hZf_pos k)
    have hGR' : Hsigma = Hp + Zsigma * T := by
      simpa [Zsigma, Zf, T] using hGR
    have hκT : κ * T = 1 - S := by
      have hsum :
          ∑ k, κ * (p k * (Hf k / Zf k)) =
            ∑ k, p k * (1 - (Zf k)⁻¹) := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        have hz_ne : Zf k ≠ 0 := hZf_ne k
        field_simp [hz_ne, hκ, Zf]
        ring
      calc
        κ * T = ∑ k, κ * (p k * (Hf k / Zf k)) := by
          simp [T, Finset.mul_sum]
        _ = ∑ k, p k * (1 - (Zf k)⁻¹) := hsum
        _ = ∑ k, (p k - p k * (Zf k)⁻¹) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          ring
        _ = ∑ k, p k - ∑ k, p k * (Zf k)⁻¹ := by
          rw [Finset.sum_sub_distrib]
        _ = 1 - S := by
          simp [S, p.sum_eq_one]
    have hZeq : Zsigma = Zp + Zsigma * (1 - S) := by
      calc
        Zsigma = 1 + κ * Hsigma := rfl
        _ = 1 + κ * (Hp + Zsigma * T) := by rw [hGR']
        _ = Zp + Zsigma * (κ * T) := by ring
        _ = Zp + Zsigma * (1 - S) := by rw [hκT]
    have hZp_eq : Zp = Zsigma * S := by
      nlinarith [hZeq]
    have hS_ne : S ≠ 0 := by
      intro hS
      exact hZp_ne (by rw [hZp_eq, hS, mul_zero])
    have hmain : Zsigma⁻¹ = Zp⁻¹ * S := by
      rw [hZp_eq]
      field_simp [hZsigma_ne, hS_ne]
    simpa [Zsigma, Zp, Zf, S] using hmain

/-- Support-read grouping recursion without assuming the reference `Z`
normalization. -/
theorem finitePreUniversalGroupingWeightRecursionNoReference_of_blockReveal_supportRead_productScale_and_Zpositive
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionNoReferenceFor hfaces hprod where
  weight_recursion := by
    intro hax K _ _ _ Act _ _ _ _ p f hp hf hsigma hKnd hAnd
    classical
    let SigmaAct : Type u := (k : K) × Act k
    let C : Channel SigmaAct K :=
      preUniversalCoarseRevealChannel (K := K) Act
    let hchainSR := supportReadBranchChain hfaces
    have hCeq : C = coarseRevealChannel Act := rfl
    have hsigma_nd : ¬ Subsingleton SigmaAct :=
      not_subsingleton_sigma_of_fiber_not_subsingleton Act hAnd
    have hchain :=
      branchNormalizedValue_seqCompose_of_chain hchainSR
        (sigmaDist p f) hsigma C
        (fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))
    have hseqV :
        hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
            (experimentOfChannel
              (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))) =
          fullRevelationValueForFaceScales hfaces (sigmaDist p f) := by
      have hsame :=
        preUniversal_samePosteriorLaw_seq_id_full_revelation
          (sigmaDist p f) C
      have hV :=
        hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
          (sigmaDist p f)
          (experimentOfChannel
            (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct)))
          (experimentOfChannel
            (Channel.idChannel : Channel SigmaAct SigmaAct))
          hsame
      simpa [fullRevelationValueForFaceScales] using hV
    have hbranchScale :
        fullRevelationValueForFaceScales hfaces (sigmaDist p f) =
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) +
            hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              ∑ k, p k *
                (fullRevelationValueForFaceScales hfaces (f k) /
                  hfaces.branch_result.scale_factorization.scale (f k)) := by
      have hsigma_scale_pos :
          0 < hfaces.branch_result.scale_factorization.scale (sigmaDist p f) :=
        hfaces.branch_result.scale_factorization.scale_pos (sigmaDist p f) hsigma
      have hsigma_scale_ne :
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) ≠ 0 :=
        ne_of_gt hsigma_scale_pos
      have hseqNV :
          branchNormalizedValue hchainSR (sigmaDist p f)
              (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct)) =
            fullRevelationValueForFaceScales hfaces (sigmaDist p f) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f) := by
        unfold branchNormalizedValue
        change
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel
                (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))) /
              faceSupportReadScale hfaces (sigmaDist p f) =
            fullRevelationValueForFaceScales hfaces (sigmaDist p f) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f)
        rw [faceSupportReadScale_fullSupport hfaces (sigmaDist p f) hsigma]
        rw [hseqV]
      have hcoarseNV :
          branchNormalizedValue hchainSR (sigmaDist p f) C =
            hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f) := by
        unfold branchNormalizedValue
        change
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              faceSupportReadScale hfaces (sigmaDist p f) =
            hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f)
        rw [faceSupportReadScale_fullSupport hfaces (sigmaDist p f) hsigma]
      have hmarg :
          Channel.outcomeMarginal C (sigmaDist p f) = p := by
        simpa [C, hCeq] using outcomeMarginal_coarseReveal_sigmaDist Act p f
      have hpost :
          ∀ k,
            Channel.posterior C (sigmaDist p f) k =
              blockEmbedDist Act k (f k) := by
        intro k
        simpa [C, hCeq] using
          posterior_coarseReveal_sigmaDist_of_pos Act p f k (hp k)
      have hterms :
          ∑ k, Channel.outcomeMarginal C (sigmaDist p f) k *
              branchNormalizedValue hchainSR
                (Channel.posterior C (sigmaDist p f) k)
                (Channel.idChannel : Channel SigmaAct SigmaAct) =
          ∑ k, p k *
            (fullRevelationValueForFaceScales hfaces (f k) /
              hfaces.branch_result.scale_factorization.scale (f k)) := by
        rw [hmarg]
        apply Finset.sum_congr rfl
        intro k _
        rw [hpost k]
        rw [block_supportRead_branchNormalizedValue
          hboundaryValue hvalue hscale hax Act hKnd k (f k) (hf k)]
      rw [hseqNV, hcoarseNV, hterms] at hchain
      have hmul := congrArg
        (fun x => x *
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f))
        hchain
      field_simp [hsigma_scale_ne] at hmul
      ring_nf at hmul ⊢
      linarith
    have hscaleToZ :
        hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)) =
          productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hratio :=
        faceScale_scale_div_eq_productScaleZ_div_of_productRevelation
          hlink hax (sigmaDist p f) (f k) hsigma (hf k)
          hsigma_nd (hAnd k)
      have hsf_pos :
          0 < hfaces.branch_result.scale_factorization.scale (f k) :=
        hfaces.branch_result.scale_factorization.scale_pos (f k) (hf k)
      have hsf_ne :
          hfaces.branch_result.scale_factorization.scale (f k) ≠ 0 :=
        ne_of_gt hsf_pos
      have hZf_ne :
          productScaleZForFaceScales hfaces hprod hax (f k) ≠ 0 :=
        productScaleZ_ne_zero_of_productRevelation
          hlink hax (sigmaDist p f) (f k) hsigma (hf k)
          hsigma_nd (hAnd k)
      have hterm :
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)) =
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
        calc
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k))
              =
            (hfaces.branch_result.scale_factorization.scale (sigmaDist p f) /
                hfaces.branch_result.scale_factorization.scale (f k)) *
              fullRevelationValueForFaceScales hfaces (f k) := by
                field_simp [hsf_ne]
          _ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) /
                productScaleZForFaceScales hfaces hprod hax (f k)) *
              fullRevelationValueForFaceScales hfaces (f k) := by
                rw [hratio]
          _ =
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
                field_simp [hZf_ne]
      calc
        hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
            (p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)))
            =
          p k *
            (hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k))) := by ring
        _ =
          p k *
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k))) := by
              rw [hterm]
        _ =
          productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            (p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k))) := by ring
    have hblock :=
      finitePreUniversalBlockRevealValue_of_productQuasiAdditivity hprod
    have hcoarse :
        hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
            (experimentOfChannel
              (preUniversalCoarseRevealChannel (K := K) Act)) =
          fullRevelationValueForFaceScales hfaces p :=
      hblock.block_reveal_value_eq_fullRevelationValue
        hax Act p f hp hf hsigma
    have hGR :
        fullRevelationValueForFaceScales hfaces (sigmaDist p f) =
          fullRevelationValueForFaceScales hfaces p +
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              ∑ k, p k *
                (fullRevelationValueForFaceScales hfaces (f k) /
                  productScaleZForFaceScales hfaces hprod hax (f k)) := by
      rw [hbranchScale, hscaleToZ]
      simpa [C] using congrArg
        (fun x =>
          x + productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)))
        hcoarse
    have hsigma_pos := hpos.Z_pos hax (sigmaDist p f) hsigma
    have hp_pos := hpos.Z_pos hax p hp
    have hf_pos :
        ∀ k, 0 < productScaleZForFaceScales hfaces hprod hax (f k) :=
      fun k => hpos.Z_pos hax (f k) (hf k)
    simpa [productScaleZForFaceScales] using
      weightRecursion_algebra_of_groupingGR_noReference
        p (hprod.kappa hax)
        (fullRevelationValueForFaceScales hfaces (sigmaDist p f))
        (fullRevelationValueForFaceScales hfaces p)
        (fun k => fullRevelationValueForFaceScales hfaces (f k))
        (by simpa [productScaleZForFaceScales] using hsigma_pos)
        (by simpa [productScaleZForFaceScales] using hp_pos)
        (fun k => by simpa [productScaleZForFaceScales] using hf_pos k)
        (by simpa [productScaleZForFaceScales] using hGR)

/-- Backward-compatible specialization of the reference-free grouping
recursion.  The proof itself only needs positivity of `Z`; the historical
slice-transform package is one way, but not the only way, to establish it. -/
theorem finitePreUniversalGroupingWeightRecursionNoReference_of_blockReveal_supportRead_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionNoReferenceFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursionNoReference_of_blockReveal_supportRead_productScale_and_Zpositive
    hboundaryValue (productScaleZpositive_of_sliceTransform hprod haff)
    hvalue hscale hlink

/-- Reference-free two-grouping evaluations. -/
structure FiniteProductTwoGroupingWeightEquationNoReferenceFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  two_grouping_evaluations :
    ∀ (hax : PureTraceConditions F)
      {U V : Type u}
      [Fintype U] [DecidableEq U] [Nonempty U]
      [Fintype V] [DecidableEq V] [Nonempty V]
      (u : Dist U) (v : Dist V) (_hu : u.FullSupport) (_hv : v.FullSupport)
      (_hU : ¬ Subsingleton U) (_hV : ¬ Subsingleton V),
      ∃ wT wp : ℝ, 0 < wp ∧
        wT = wp *
            (((productScaleZForFaceScales hfaces hprod hax u)⁻¹ ^ 2 +
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹ ^ 2) / 2) ∧
        wT = wp *
            ((((productScaleZForFaceScales hfaces hprod hax u)⁻¹ +
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹) / 2) ^ 2)

/-- Two-grouping theorem from reference-free weight recursion. -/
theorem finiteProductTwoGroupingWeightEquationNoReference_of_weightRecursion_fullSupportRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hfull : FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces)
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hrec :
      FinitePreUniversalGroupingWeightRecursionNoReferenceFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod where
  two_grouping_evaluations := by
    intro hax U V _ _ _ _ _ _ u v hu hv hU hV
    classical
    set K := universalScaleReferenceType with hK
    set p₂ := universalScaleReferencePrior with hp₂
    have hp₂fs : p₂.FullSupport := universalScaleReferencePrior_fullSupport
    have hKnd : ¬ Subsingleton K := universalScaleReference_not_subsingleton
    set g := twoGroupingConditional u v with hg
    have hgfs : ∀ k, (g k).FullSupport := by
      intro k
      rcases k with ⟨b⟩
      cases b
      · exact hu
      · exact hv
    have hgnd : ∀ k, ¬ Subsingleton (twoGroupingFiber U V k) := by
      intro k
      rcases k with ⟨b⟩
      cases b
      · exact hU
      · exact hV
    set f := fun k => prodDist (g k) (g k) with hf
    have hffs : ∀ k, (f k).FullSupport := fun k =>
      prodDist_fullSupport (g k) (g k) (hgfs k) (hgfs k)
    have hfnd : ∀ k, ¬ Subsingleton (twoGroupingFiber U V k ×
        twoGroupingFiber U V k) := fun k =>
      not_subsingleton_prod_left (hgnd k)
    set T := sigmaDist p₂ f with hT
    set S := sigmaDist p₂ g with hS
    have hTfs : T.FullSupport := sigmaDist_fullSupport p₂ f hp₂fs hffs
    have hSfs : S.FullSupport := sigmaDist_fullSupport p₂ g hp₂fs hgfs
    haveI : Nonempty ((k : K) × (twoGroupingFiber U V k ×
        twoGroupingFiber U V k)) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    haveI : Nonempty ((k : K) × twoGroupingFiber U V k) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    set f' := fun (ka : (k : K) × twoGroupingFiber U V k) => g ka.1 with hf'
    have hf'fs : ∀ ka : (k : K) × twoGroupingFiber U V k,
        (f' ka).FullSupport := fun ka => hgfs ka.1
    have hf'nd : ∀ ka : (k : K) × twoGroupingFiber U V k,
        ¬ Subsingleton (twoGroupingFiber U V ka.1) := fun ka => hgnd ka.1
    set T' := sigmaDist S f' with hT'
    have hT'fs : T'.FullSupport := sigmaDist_fullSupport S f' hSfs hf'fs
    haveI :
        Nonempty ((ka : (k : K) × twoGroupingFiber U V k) ×
          twoGroupingFiber U V ka.1) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    have hSnd : ¬ Subsingleton ((k : K) × twoGroupingFiber U V k) :=
      not_subsingleton_sigma hKnd
    have hT'nd :
        ¬ Subsingleton
          ((ka : (k : K) × twoGroupingFiber U V k) ×
            twoGroupingFiber U V ka.1) :=
      not_subsingleton_sigma_of_fiber_not_subsingleton
        (fun ka : (k : K) × twoGroupingFiber U V k =>
          twoGroupingFiber U V ka.1) hf'nd
    have hHrel :
        fullRevelationValueForFaceScales hfaces
            (Relabeling.relabelDist (twoGroupingReassoc U V) T') =
          fullRevelationValueForFaceScales hfaces T' :=
      fullRevelationValueForFaceScales_relabel_eq_fullSupport hfull hax
        (twoGroupingReassoc U V) T' hT'fs hT'nd
    have hTeq : Relabeling.relabelDist (twoGroupingReassoc U V) T' = T :=
      relabelDist_twoGroupingReassoc u v
    have hZTT' :
        productScaleZForFaceScales hfaces hprod hax T =
          productScaleZForFaceScales hfaces hprod hax T' := by
      unfold productScaleZForFaceScales
      rw [← hTeq, hHrel]
    have hrecT :=
      hrec.weight_recursion hax
        (fun k : K => twoGroupingFiber U V k × twoGroupingFiber U V k)
        p₂ f hp₂fs hffs hTfs hKnd hfnd
    have hrecT' :=
      hrec.weight_recursion hax
        (fun ka : (k : K) × twoGroupingFiber U V k =>
          twoGroupingFiber U V ka.1)
        S f' hSfs hf'fs hT'fs hSnd hf'nd
    have hrecS :=
      hrec.weight_recursion hax (twoGroupingFiber U V)
        p₂ g hp₂fs hgfs hSfs hKnd hgnd
    set x := (productScaleZForFaceScales hfaces hprod hax u)⁻¹ with hx
    set y := (productScaleZForFaceScales hfaces hprod hax v)⁻¹ with hy
    have hsum_f :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹) =
          (x ^ 2 + y ^ 2) / 2 := by
      rw [sum_universalScaleReferenceType
        (fun k => p₂ k *
          (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹)]
      have hZff :
          productScaleZForFaceScales hfaces hprod hax (f (ULift.up false)) =
            productScaleZForFaceScales hfaces hprod hax u *
              productScaleZForFaceScales hfaces hprod hax u := by
        change productScaleZForFaceScales hfaces hprod hax (prodDist u u) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax u u hu hu
      have hZft :
          productScaleZForFaceScales hfaces hprod hax (f (ULift.up true)) =
            productScaleZForFaceScales hfaces hprod hax v *
              productScaleZForFaceScales hfaces hprod hax v := by
        change productScaleZForFaceScales hfaces hprod hax (prodDist v v) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax v v hv hv
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply,
        hZff, hZft, mul_inv, mul_inv]
      change 1 / 2 *
          ((productScaleZForFaceScales hfaces hprod hax u)⁻¹ *
            (productScaleZForFaceScales hfaces hprod hax u)⁻¹) +
          1 / 2 *
            ((productScaleZForFaceScales hfaces hprod hax v)⁻¹ *
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹) = _
      rw [← hx, ← hy]
      ring
    have hsum_g :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) =
          (x + y) / 2 := by
      rw [sum_universalScaleReferenceType
        (fun k => p₂ k *
          (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹)]
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply]
      change 1 / 2 * (productScaleZForFaceScales hfaces hprod hax u)⁻¹ +
          1 / 2 * (productScaleZForFaceScales hfaces hprod hax v)⁻¹ = _
      rw [← hx, ← hy]
      ring
    have hsum_f' :
        (∑ ka : (k : K) × twoGroupingFiber U V k,
          S ka * (productScaleZForFaceScales hfaces hprod hax (f' ka))⁻¹) =
          (x + y) / 2 := by
      rw [Fintype.sum_sigma]
      have hterm :
          ∀ k, (∑ a : twoGroupingFiber U V k,
              S ⟨k, a⟩ *
                (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹) =
            p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
        intro k
        have : ∀ a : twoGroupingFiber U V k,
            S ⟨k, a⟩ *
                (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹ =
              p₂ k * (g k) a *
                (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
          intro a
          change (sigmaDist p₂ g) ⟨k, a⟩ *
              (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ = _
          rw [sigmaDist_apply]
        rw [Finset.sum_congr rfl (fun a _ => this a)]
        have hfactor :
            (∑ a : twoGroupingFiber U V k,
              p₂ k * (g k) a *
                (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) =
              (p₂ k *
                (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) *
                (∑ a, (g k) a) := by
          rw [Finset.mul_sum]
          congr 1
          ext a
          ring
        rw [hfactor, (g k).sum_eq_one, mul_one]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      exact hsum_g
    have hZp₂pos : 0 < productScaleZForFaceScales hfaces hprod hax p₂ :=
      hpos.Z_pos hax p₂ hp₂fs
    refine ⟨(productScaleZForFaceScales hfaces hprod hax T)⁻¹,
      (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹,
      inv_pos.mpr hZp₂pos, ?_, ?_⟩
    · rw [show (productScaleZForFaceScales hfaces hprod hax T)⁻¹ =
          (productScaleZForFaceScales hfaces hprod hax (sigmaDist p₂ f))⁻¹
        from rfl]
      rw [hrecT, hsum_f]
    · have hE2' :
          (productScaleZForFaceScales hfaces hprod hax T')⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹ *
              (((x + y) / 2) ^ 2) := by
        rw [show (productScaleZForFaceScales hfaces hprod hax T')⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist S f'))⁻¹
          from rfl]
        rw [hrecT', hsum_f']
        rw [show (productScaleZForFaceScales hfaces hprod hax S)⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax S)⁻¹ from rfl]
        rw [show (productScaleZForFaceScales hfaces hprod hax S)⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p₂ g))⁻¹
          from rfl]
        rw [hrecS, hsum_g]
        ring
      rw [hZTT']
      exact hE2'

theorem productScaleZ_inv_eq_of_twoGroupingNoReference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod)
    (hax : PureTraceConditions F)
    {U V : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (u : Dist U) (v : Dist V) (hu : u.FullSupport) (hv : v.FullSupport)
    (hU : ¬ Subsingleton U) (hV : ¬ Subsingleton V) :
    (productScaleZForFaceScales hfaces hprod hax u)⁻¹ =
      (productScaleZForFaceScales hfaces hprod hax v)⁻¹ := by
  obtain ⟨wT, wp, hwp, hE1, hE2⟩ :=
    hgroup.two_grouping_evaluations hax u v hu hv hU hV
  exact twoGrouping_eq_of_evaluations hwp (hE1.symm.trans hE2)

theorem productScaleZ_eq_of_twoGroupingNoReference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hax : PureTraceConditions F)
    {U V : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (u : Dist U) (v : Dist V) (hu : u.FullSupport) (hv : v.FullSupport)
    (hU : ¬ Subsingleton U) (hV : ¬ Subsingleton V) :
    productScaleZForFaceScales hfaces hprod hax u =
      productScaleZForFaceScales hfaces hprod hax v := by
  have hinv :=
    productScaleZ_inv_eq_of_twoGroupingNoReference
      hgroup hax u v hu hv hU hV
  have := congrArg (fun t => t⁻¹) hinv
  simpa [inv_inv] using this

/-- The reference normalization is a theorem from reference-free two-grouping:
two-grouping makes `Z` constant on nondegenerate full-support priors; applying
this to `q_ref × q_ref` and using multiplicativity forces the positive constant
to satisfy `c = c^2`, hence `c = 1`. -/
theorem finiteProductReferenceZNormalization_of_twoGroupingNoReference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductReferenceZNormalizationFor hfaces hprod where
  reference_Z_eq_one := by
    intro hax
    set q0 : Dist universalScaleReferenceType := universalScaleReferencePrior with hq0
    have hq0fs : q0.FullSupport := universalScaleReferencePrior_fullSupport
    have hq0nd : ¬ Subsingleton universalScaleReferenceType :=
      universalScaleReference_not_subsingleton
    have hpfs : (prodDist q0 q0).FullSupport :=
      prodDist_fullSupport q0 q0 hq0fs hq0fs
    have hpnd : ¬ Subsingleton (universalScaleReferenceType × universalScaleReferenceType) :=
      not_subsingleton_prod_left hq0nd
    have hconst :
        productScaleZForFaceScales hfaces hprod hax (prodDist q0 q0) =
          productScaleZForFaceScales hfaces hprod hax q0 :=
      productScaleZ_eq_of_twoGroupingNoReference
        hgroup hpos hax (prodDist q0 q0) q0 hpfs hq0fs hpnd hq0nd
    have hmul :
        productScaleZForFaceScales hfaces hprod hax (prodDist q0 q0) =
          productScaleZForFaceScales hfaces hprod hax q0 *
            productScaleZForFaceScales hfaces hprod hax q0 :=
      productScaleZForFaceScales_prod_eq hfaces hprod hax q0 q0 hq0fs hq0fs
    have hposq : 0 < productScaleZForFaceScales hfaces hprod hax q0 :=
      hpos.Z_pos hax q0 hq0fs
    have hsquare :
        productScaleZForFaceScales hfaces hprod hax q0 *
            productScaleZForFaceScales hfaces hprod hax q0 =
          productScaleZForFaceScales hfaces hprod hax q0 := by
      exact hmul.symm.trans hconst
    have hone :
        productScaleZForFaceScales hfaces hprod hax q0 = 1 := by
      nlinarith [hposq, hsquare]
    simpa [q0, hq0] using hone

/-- Interaction collapse from support-read coordinate continuations.

This constructor is the support-face replacement for the coordinate part of
`InteractionCollapseUniversalScale_of_fullPreEntropyClosure`: the product scale
link is derived from `sequentialFullRevelationNormalizedChain_of_coordinateSupportRead`,
so it never asks for ambient coordinate boundary value/scale equalities.  The
  block input is also support-read; the remaining visible pre-entropy obligations
  are the product-reference and singleton normalizations. -/
noncomputable def InteractionCollapseUniversalScale_of_coordinateSupportRead
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
    InteractionCollapseUniversalChainScaleStructure F :=
  let hnorm :=
    sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
      hfaces hboundaryValue hprod hcoordValue hcoordScale
  let hlink :=
    productRevelationScaleLink_of_sequentialScale hfaces hprod
      (productRevelationSequentialScale_of_normalizedChain hfaces hnorm)
  let hpos := productScaleZpositive_of_sliceTransform hprod haff
  let hfull :=
    finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
      hhm huniq hpos
  let hrec :=
    finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale
      hboundaryValue haff hblockValue hblockScale hlink href
  let htwo :=
    finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  let hreference :=
    productGroupingReferenceWeight_of_twoGroupingWeightEquation htwo hpos
  let hweight :=
    productGroupingWeightConstant_of_reference hreference
  let hcollapse :=
    twoGroupingInteractionCollapse_of_weightConstant hfaces hprod hweight
  { face_scales := hfaces
    product_quasi_add := hprod
    scale_coherence :=
      scaleCoherence_of_faceScales_interactionCollapse
        hfaces hprod hlink hcollapse hsingle hax
    interaction_collapse := hcollapse.kappa_eq_zero }




/-! ## Field 3 (restricted coarse-reveal value) proved via support reindexing -/

noncomputable def sigmaSupportEquiv
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    supportSubtype (sigmaDist p q) ≃
      Σ (k' : supportSubtype p), supportSubtype (q k'.1) where
  toFun := fun ⟨⟨k, a⟩, hpos⟩ =>
    have hp : p k > 0 := by
      rw [sigmaDist_apply] at hpos
      rcases (p.nonneg k).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hpos; simp at hpos
    have hq : (q k) a > 0 := by
      rw [sigmaDist_apply] at hpos
      rcases ((q k).nonneg a).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hpos; simp at hpos
    ⟨⟨k, hp⟩, ⟨a, hq⟩⟩
  invFun := fun ⟨⟨k, hp⟩, ⟨a, hq⟩⟩ =>
    ⟨⟨k, a⟩, by rw [sigmaDist_apply]; exact mul_pos hp hq⟩
  left_inv := by rintro ⟨⟨k, a⟩, hpos⟩; rfl
  right_inv := by rintro ⟨⟨k, hp⟩, ⟨a, hq⟩⟩; rfl

theorem sigma_restrict_reindex
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Relabeling.relabelDist (sigmaSupportEquiv Act p q) (sigmaDist p q).restrictToSupport =
      sigmaDist p.restrictToSupport (fun k' => (q k'.1).restrictToSupport) := by
  ext y
  rcases y with ⟨⟨k, hk⟩, ⟨a, ha⟩⟩
  rw [Relabeling.relabelDist_apply, sigmaDist_apply]
  simp only [sigmaSupportEquiv, Equiv.coe_fn_symm_mk, Dist.restrictToSupport_apply, sigmaDist_apply]



theorem normalizedValue_relabelAction_of_crossPrior
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    haveI : Nonempty B := ⟨eA (Classical.arbitrary A)⟩
    normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist eA q) (Relabeling.relabelChannel eA (Equiv.refl O) P) =
      normalizedValue hcross.entropy_reduction.scale_coherence q P := by
  haveI : Nonempty B := ⟨eA (Classical.arbitrary A)⟩
  set P' : Channel B O := Relabeling.relabelChannel eA (Equiv.refl O) P with hP'
  have hqB : (Relabeling.relabelDist eA q).FullSupport :=
    Relabeling.relabelDist_fullSupport eA q hq
  -- A5 both directions between P (on q) and P' (on relabel q)
  have hq_to_new : F.rel (blockChannel P P') (inlDist q) (inrDist (Relabeling.relabelDist eA q)) := by
    have h := hax.actionProcessing P q (Relabeling.actionEquivKernel eA) P'
      (Relabeling.relabelChannel_isBayesPushforwardCompletion eA P q)
    simpa [P', Relabeling.actionPushforward_equiv] using h
  have hq_to_old : F.rel (blockChannel P' P) (inlDist (Relabeling.relabelDist eA q)) (inrDist q) := by
    have h := hax.actionProcessing P' (Relabeling.relabelDist eA q) (Relabeling.actionEquivKernel eA.symm) P
      (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion eA P q)
    simpa [P', Relabeling.actionPushforward_equiv, Relabeling.relabelDist_symm] using h
  -- convert each block comparison to a normalizedValue inequality
  have hge₁ := (hcross.cross_prior_block_rep q (Relabeling.relabelDist eA q) hq hqB P P').mp hq_to_new
  have hge₂ := (hcross.cross_prior_block_rep (Relabeling.relabelDist eA q) q hqB hq P' P).mp hq_to_old
  have e₁ : normalizedValue hcross.entropy_reduction.scale_coherence q P ≥
      normalizedValue hcross.entropy_reduction.scale_coherence (Relabeling.relabelDist eA q) P' := by
    simpa [normalizedValue] using hge₁
  have e₂ : normalizedValue hcross.entropy_reduction.scale_coherence (Relabeling.relabelDist eA q) P' ≥
      normalizedValue hcross.entropy_reduction.scale_coherence q P := by
    simpa [normalizedValue] using hge₂
  exact le_antisymm e₁ e₂


/- Target coarse channel on supp(s): reveal the block index in supportSubtype p. -/
noncomputable def coarseTgt
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Channel (supportSubtype (sigmaDist p q)) (supportSubtype p) :=
  fun x =>
    haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    Dist.pure ((sigmaSupportEquiv Act p q x).1)

/- coarseTgt is the action-relabel (outcome refl) of coarseReveal over the reindexed Act'. -/
theorem coarseTgt_eq_relabel
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    coarseTgt Act p q =
      Relabeling.relabelChannel (sigmaSupportEquiv Act p q).symm (Equiv.refl (supportSubtype p))
        (coarseRevealChannel (fun k' : supportSubtype p => supportSubtype (q k'.1))) := by
  haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
  ext x y
  simp only [coarseTgt, Relabeling.relabelChannel_apply, Equiv.refl_symm, Equiv.refl_apply,
    coarseRevealChannel, Equiv.symm_symm, Equiv.apply_symm_apply]

/- Step B (outcome collapse): C|supp and coarseTgt have the same posterior law at s|supp.
   Both deterministically reveal the block; posteriors are the fibres.  The K-valued reveal
   has zero marginal off supp(p), so its posterior-law integral matches the supp(p)-valued one. -/
theorem samePosteriorLaw_coarse_restrict_tgt
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    [Nonempty (supportSubtype (sigmaDist p q))] :
    SamePosteriorLawExp (sigmaDist p q).restrictToSupport
      (experimentOfChannel (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)))
      (experimentOfChannel (coarseTgt Act p q)) := by
  intro φ _
  rw [posteriorLawIntegralExp_experimentOfChannel, posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  classical
  haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
  -- RHS sum over supportSubtype p equals a sum over K of terms zero off supp(p)
  rw [← sum_supportSubtype_eq_sum_of_zero p
        (fun k =>
          (Channel.outcomeMarginal (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport) k *
          φ (Channel.posterior (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport k))
        ?_]
  · -- Now both are sums over supportSubtype p; match termwise.
    apply Finset.sum_congr rfl
    intro k' _
    have hind : ∀ x : supportSubtype (sigmaDist p q),
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) x (k'.1) =
        (coarseTgt Act p q) x k' := by
      intro x
      have hfst : ((sigmaSupportEquiv Act p q x).1).1 = x.1.1 := by
        rcases x with ⟨⟨j, a⟩, hxpos⟩
        rfl
      simp only [coarseTgt, Channel.restrictToSupport_apply, coarseRevealChannel, Dist.pure_apply]
      by_cases hx : k'.1 = x.1.1
      · have h2 : (k' = (sigmaSupportEquiv Act p q x).1) := by
          apply Subtype.ext; rw [hfst]; exact hx
        rw [if_pos hx, if_pos h2]
      · have h2 : ¬ (k' = (sigmaSupportEquiv Act p q x).1) := by
          intro h; apply hx; rw [← hfst]; exact congrArg Subtype.val h
        rw [if_neg hx, if_neg h2]
    have hmarg : (Channel.outcomeMarginal
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
        (sigmaDist p q).restrictToSupport) k'.1 =
        (Channel.outcomeMarginal (coarseTgt Act p q) (sigmaDist p q).restrictToSupport) k' := by
      rw [Channel.outcomeMarginal_apply, Channel.outcomeMarginal_apply]
      apply Finset.sum_congr rfl
      intro x _; rw [hind x]
    have hpost : (Channel.posterior
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
        (sigmaDist p q).restrictToSupport) k'.1 =
        (Channel.posterior (coarseTgt Act p q) (sigmaDist p q).restrictToSupport) k' := by
      by_cases hpos : (Channel.outcomeMarginal (coarseTgt Act p q)
          (sigmaDist p q).restrictToSupport) k' > 0
      · have hposC : (Channel.outcomeMarginal
            (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport) k'.1 > 0 := by rw [hmarg]; exact hpos
        ext y
        simp only [Channel.posterior, dif_pos hposC, dif_pos hpos]
        rw [hind y, hmarg]
      · have hnegC : ¬ (Channel.outcomeMarginal
            (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport) k'.1 > 0 := by rw [hmarg]; exact hpos
        simp only [Channel.posterior, dif_neg hnegC, dif_neg hpos]
    rw [hmarg, hpost]
  · -- off-support terms vanish: for p k = 0, outcomeMarginal of restricted coarseReveal at k is 0
    intro k hk0
    have hm : (Channel.outcomeMarginal
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
        (sigmaDist p q).restrictToSupport) k = 0 := by
      rw [Channel.outcomeMarginal_apply]
      apply Finset.sum_eq_zero
      intro x _
      rcases x with ⟨⟨j, a⟩, hx⟩
      have hjne : j ≠ k := by
        rintro rfl
        rw [sigmaDist_apply] at hx
        have : p j = 0 := hk0
        rw [this, zero_mul] at hx
        exact lt_irrefl 0 hx
      simp only [Channel.restrictToSupport_apply, coarseRevealChannel, Dist.pure_apply]
      rw [if_neg (by simpa [eq_comm] using hjne), mul_zero]
    rw [hm, zero_mul]


/- normalizedValue respects same posterior law (numerator respects, scale unaffected). -/
theorem normalizedValue_congr_samePosteriorLaw
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A O O' : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype O'] [DecidableEq O']
    (q : Dist A) (P : Channel A O) (P' : Channel A O')
    (hsame : SamePosteriorLawExp q (experimentOfChannel P) (experimentOfChannel P')) :
    normalizedValue hs q P = normalizedValue hs q P' := by
  unfold normalizedValue
  rw [hs.branch_agg.value_rep.respects_same_posterior_law q
    (experimentOfChannel P) (experimentOfChannel P') hsame]

/- FIELD 3: restricted coarse-reveal value equals Hfun of the restricted coarse prior. -/
theorem field3_restricted_coarse_reveal
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    (hnot : ¬ (sigmaDist p q).FullSupport) :
    letI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
    letI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    normalizedValue hcross.entropy_reduction.scale_coherence
        (sigmaDist p q).restrictToSupport
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) =
      hcross.entropy_reduction.Hfun p.restrictToSupport := by
  haveI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
  haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
  set hs := hcross.entropy_reduction.scale_coherence with hsdef
  set p' : Dist (supportSubtype p) := p.restrictToSupport with hp'
  set q' : (k' : supportSubtype p) → Dist (supportSubtype (q k'.1)) :=
    fun k' => (q k'.1).restrictToSupport with hq'
  haveI : ∀ k' : supportSubtype p, Nonempty (supportSubtype (q k'.1)) :=
    fun k' => supportSubtype_nonempty _
  haveI : Nonempty ((k' : supportSubtype p) × supportSubtype (q k'.1)) :=
    (sigmaSupportEquiv Act p q).nonempty_congr.mp inferInstance
  -- Step B: collapse the K-outcome to coarseTgt (into supp p)
  have hstepB : normalizedValue hs (sigmaDist p q).restrictToSupport
      (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) =
      normalizedValue hs (sigmaDist p q).restrictToSupport (coarseTgt Act p q) :=
    normalizedValue_congr_samePosteriorLaw hs _ _ _
      (samePosteriorLaw_coarse_restrict_tgt Act p q)
  rw [hstepB]
  -- coarseTgt = relabelChannel eA.symm (refl) (coarseReveal Act'), s|supp = relabelDist eA.symm (sigmaDist p' q')
  set eA := (sigmaSupportEquiv Act p q) with heA
  have hs_eq : (sigmaDist p q).restrictToSupport = Relabeling.relabelDist eA.symm (sigmaDist p' q') := by
    conv_lhs => rw [← Relabeling.relabelDist_symm eA (sigmaDist p q).restrictToSupport]
    rw [sigma_restrict_reindex Act p q]
  have hC_eq : coarseTgt Act p q =
      Relabeling.relabelChannel eA.symm (Equiv.refl (supportSubtype p))
        (coarseRevealChannel (fun k' : supportSubtype p => supportSubtype (q k'.1))) :=
    coarseTgt_eq_relabel Act p q
  rw [hs_eq, hC_eq]
  -- action engine transports the normalized value across the reindex relabeling
  have hp'full : (sigmaDist p' q').FullSupport := by
    intro x
    rw [sigmaDist_apply]
    exact mul_pos (Dist.restrictToSupport_fullSupport p x.1)
      (Dist.restrictToSupport_fullSupport (q x.1.1) x.2)
  rw [normalizedValue_relabelAction_of_crossPrior F hax hcross eA.symm (sigmaDist p' q')
      hp'full
      (coarseRevealChannel (fun k' : supportSubtype p => supportSubtype (q k'.1)))]
  -- full-support coarse lemma: normValue (sigmaDist p' q') (coarseReveal Act') = Hfun p'
  rw [coarseReveal_value_eq_Hfun_of_axioms_fullSupport F hax hcross hreg
      (fun k' : supportSubtype p => supportSubtype (q k'.1)) p' q'
      (by
        -- sigmaDist p' q' is full support (p' and each q' full support)
        intro x
        rw [sigmaDist_apply]
        exact mul_pos (Dist.restrictToSupport_fullSupport p x.1)
          (Dist.restrictToSupport_fullSupport (q x.1.1) x.2))]



/-! ## hcard-free MI route from per-cross boundary facts -/

/- Per-hcross coarse-reveal value: assemble from the three boundary facts (all now
   proved theorems for the wrapped structure), reusing the full-support lemma. -/
theorem coarseVal_forCross
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    -- field 1 (boundary normalized-value support restriction) for THIS hcross:
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    -- field 3 (restricted coarse-reveal) for THIS hcross:
    (hrestrC : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)), ¬ (sigmaDist p q).FullSupport →
      haveI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
      haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q).restrictToSupport
          (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) =
        hcross.entropy_reduction.Hfun p.restrictToSupport)
    -- Hfun support restriction for THIS hcross (field 2 + field 1 at id):
    (hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q = hcross.entropy_reduction.Hfun q.restrictToSupport)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    normalizedValue hcross.entropy_reduction.scale_coherence
        (sigmaDist p q) (coarseRevealChannel Act) =
      hcross.entropy_reduction.Hfun p := by
  by_cases hsig : (sigmaDist p q).FullSupport
  · exact coarseReveal_value_eq_Hfun_of_axioms_fullSupport F hax hcross hreg Act p q hsig
  · haveI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
    haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    have h1 := hnormC (coarseRevealChannel Act) (sigmaDist p q) hsig
    have h3 := hrestrC Act p q hsig
    have hH := hhfunC p
    rw [h1, h3, ← hH]

/- Faddeev recursion from per-hcross coarse value. -/
theorem satisfiesFaddeevRecursion_forCross
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p) :
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  intro K _ _ _ Act _ _ _ _ p q
  have hER := hred.coarse_reveal_entropy_reduction F hax hreg Act p q
  have hV := hcoarse Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) :=
    posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k => hblock.Hfun_blockEmbed F hax hreg Act k (q k))
  change hcross.entropy_reduction.Hfun (sigmaDist p q) =
    hcross.entropy_reduction.Hfun p +
      ∑ k, p k * hcross.entropy_reduction.Hfun (q k)
  rw [hER, hV, hInt]

/- FaddeevEntropyForm from per-hcross coarse value. -/
noncomputable def FaddeevEntropyForm_forCross
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p) :
    FaddeevEntropyForm F := by
  have hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    { regularity := hreg
      grouping_recursion :=
        satisfiesFaddeevRecursion_forCross hblock hred F hax hcross hreg hcoarse }
  have hstandard :
      FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun :=
    finiteFaddeevStandardHypotheses_of_axioms hax hcross hrecForm hsupport
  have hex :=
    hfad.of_standard_hypotheses
      hcross.entropy_reduction.Hfun hstandard
  have hH : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hcross.entropy_reduction.Hfun q = (Classical.choose hex) * H(q) :=
    (Classical.choose_spec hex).2
  have hHfun_pos : 0 < hcross.entropy_reduction.Hfun (Dist.uniform (A := ULift.{u,0} Bool)) :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrecForm
  exact
    { cross_prior := hcross
      alpha := Classical.choose hex
      alpha_pos :=
        alpha_strict_pos_of_positive_Hfun_witness F hax hcross hrecForm hHfun_pos
          (Classical.choose hex) hH
      H_eq_alpha_shannon := hH
      a3_block_equivalence := a3_block_equivalence_of_traceAxioms F hax }

/- PureTraceMIRepresentation from per-hcross coarse value (no FiniteCardinalSupportBoundaryAssumptions). -/
theorem MIRep_forCross
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p) :
    PureTraceMIRepresentation F :=
  let hfe : FaddeevEntropyForm F :=
    FaddeevEntropyForm_forCross hblock hred hfad F hax hcross hreg hsupport hcoarse
  MIRep_of_SufficiencyMIPackage F
    (FullSupportMIRepExtendsToBoundary_of_supportRestriction F
      (FullSupportBlockMI_of_FaddeevEntropyForm F hfe) hax
      (FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F hfe))



/-! ## Capstone: boundary-completed MI route with no cardinal-boundary assumption -/

/- Wrapped cross-prior representation: same as hcross but with the boundary-completed scale. -/
noncomputable def wrapCross
    {F : PrefFamily.{u}} (hcross : CrossPriorBlockRepresentation F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross.entropy_reduction.scale_coherence.scale q /
          hcross.entropy_reduction.scale_coherence.scale r.restrictToSupport)
    : CrossPriorBlockRepresentation F where
  entropy_reduction :=
    EntropyReductionRepresentation_of_scale F
      (boundaryCompleteScale hcross.entropy_reduction.scale_coherence hsf)
  cross_prior_block_rep := by
    intro A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P Q
    have hsq : wrapScale hcross.entropy_reduction.scale_coherence q =
        hcross.entropy_reduction.scale_coherence.scale q :=
      wrapScale_fullSupport _ q hq
    have hsr : wrapScale hcross.entropy_reduction.scale_coherence r =
        hcross.entropy_reduction.scale_coherence.scale r :=
      wrapScale_fullSupport _ r hr
    have hb := hcross.cross_prior_block_rep q r hq hr P Q
    rw [← hsq, ← hsr] at hb
    exact hb

/- Per-hcross nonneg of normalizedValue at id (boundary case uses per-hcross field1). -/
theorem normalizedValue_id_nonneg_forCross
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 ≤ normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel := by
  by_cases hq : q.FullSupport
  · exact normalizedValue_id_nonneg_of_crossPrior_fullSupport hax hcross q hq
  · haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    rw [hnormC Channel.idChannel q hq,
      normalizedValue_restrict_idChannel_eq_idSupport hcross.entropy_reduction q]
    exact normalizedValue_id_nonneg_of_crossPrior_fullSupport hax hcross
      q.restrictToSupport (Dist.restrictToSupport_fullSupport q)

/- Per-hcross pure-zero. -/
theorem normalizedValue_id_pure_zero_forCross
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (a : A) :
    normalizedValue hcross.entropy_reduction.scale_coherence (Dist.pure a) Channel.idChannel = 0 := by
  by_cases hq : (Dist.pure a).FullSupport
  · haveI : Subsingleton A :=
      ⟨fun b c => by rw [eq_of_pure_pos (hq b), eq_of_pure_pos (hq c)]⟩
    have hV0 : hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V
        (Dist.pure a) (experimentOfChannel Channel.idChannel) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep (Dist.pure a) hq Channel.idChannel
    simp [normalizedValue, hV0]
  · haveI : Nonempty (supportSubtype (Dist.pure a)) := supportSubtype_nonempty (Dist.pure a)
    haveI : Subsingleton (supportSubtype (Dist.pure a)) := subsingleton_supportSubtype_pure a
    rw [hnormC Channel.idChannel (Dist.pure a) hq,
      normalizedValue_restrict_idChannel_eq_idSupport hcross.entropy_reduction (Dist.pure a)]
    have hV0 : hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V
        (Dist.pure a).restrictToSupport
        (experimentOfChannel (Channel.idChannel :
          Channel (supportSubtype (Dist.pure a)) (supportSubtype (Dist.pure a)))) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep
        (Dist.pure a).restrictToSupport (Dist.restrictToSupport_fullSupport _) Channel.idChannel
    simp [normalizedValue, hV0]

/- Per-hcross EntropyRegularity, when Hfun = normalizedValue·id (constructed rep). -/
theorem entropyRegularity_forCross
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hcross.entropy_reduction.Hfun q =
        normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q)) :
    EntropyRegularity F hcross.entropy_reduction where
  H_nonneg := fun q => by
    rw [hHfunId q]; exact normalizedValue_id_nonneg_forCross hax hcross hnormC q
  H_singleton := fun a => by
    rw [hHfunId (Dist.pure a)]; exact normalizedValue_id_pure_zero_forCross hax hcross hnormC a

/- CAPSTONE: PureTraceMIRepresentation with NO FiniteCardinalSupportBoundaryAssumptions, from wrapCross. -/
theorem MIRep_of_boundaryComplete
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross0 : CrossPriorBlockRepresentation F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross0.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross0.entropy_reduction.scale_coherence.scale q /
          hcross0.entropy_reduction.scale_coherence.scale r.restrictToSupport)
    (hcoh : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) [Nonempty (supportSubtype q)] (d : Dist (supportSubtype q)),
      hint.marginalValue F (boundaryCompleteScale hcross0.entropy_reduction.scale_coherence hsf).branch_agg.value_rep q
        (Channel.actionPushforward d (supportIncludeKernel q)) =
        hint.marginalValue F (boundaryCompleteScale hcross0.entropy_reduction.scale_coherence hsf).branch_agg.value_rep
          q.restrictToSupport d) :
    PureTraceMIRepresentation F := by
  set hc := wrapCross hcross0 hsf with hcdef
  -- Hfun of hc = normalizedValue (wrapped) id  (definitional via EntropyReductionRepresentation_of_scale)
  have hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hc.entropy_reduction.Hfun q =
        normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel :=
    fun q => rfl
  -- field 1 for hc:
  have hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hc.entropy_reduction.scale_coherence q P =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    intro A O _ _ _ _ _ P q hqb
    exact field1_boundaryComplete hint (hcross0.entropy_reduction.scale_coherence) hsf hcoh P q hqb
  have hreg : EntropyRegularity F hc.entropy_reduction :=
    entropyRegularity_forCross hax hc hHfunId hnormC
  have hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hc.entropy_reduction.Hfun q =
        hc.entropy_reduction.Hfun q.restrictToSupport := by
    intro A _ _ _ q
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    rw [hHfunId q, hHfunId q.restrictToSupport]
    rw [show normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel =
          normalizedValue hc.entropy_reduction.scale_coherence
            q.restrictToSupport (Channel.restrictToSupport Channel.idChannel q) from ?_,
        normalizedValue_restrict_idChannel_eq_idSupport hc.entropy_reduction q]
    by_cases hqf : q.FullSupport
    · exact normalizedValue_support_restrict_fullSupport_of_crossPrior
        F hax hc Channel.idChannel q hqf
    · exact hnormC Channel.idChannel q hqf
  -- per-hcross coarse value from the three facts:
  have hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hc.entropy_reduction.Hfun p := by
    intro K _ _ _ Act _ _ _ _ p q
    refine coarseVal_forCross F hax hc hreg hnormC ?_ ?_ Act p q
    · -- field 3 for hc
      intro K2 _ _ _ Act2 _ _ _ _ p2 q2 hnot2
      exact field3_restricted_coarse_reveal F hax hc hreg Act2 p2 q2 hnot2
    · -- Hfun support restriction: Hfun q = Hfun (q|supp), via hHfunId + field1 at id
      exact hhfunC
  apply MIRep_forCross hblock hred hfad F hax hc hreg hhfunC
  intro K _ _ _ Act _ _ _ _ p q
  exact hcoarse Act p q


/-! ## hcard-free producers: Faddeev recursion / entropy form / PureTraceMIRepresentation from per-cross facts -/

theorem satisfiesFaddeevRecursion_ofCrossFacts
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hcross.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun)
    (hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
        hcross.entropy_reduction.Hfun qk)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hcross.entropy_reduction.Hfun p) :
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  intro K _ _ _ Act _ _ _ _ p q
  have hE := hER Act p q
  have hV := hcoarse Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) :=
    posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k => hblockE Act k (q k))
  change hcross.entropy_reduction.Hfun (sigmaDist p q) =
    hcross.entropy_reduction.Hfun p +
      ∑ k, p k * hcross.entropy_reduction.Hfun (q k)
  rw [hE, hV, hInt]

/- FaddeevEntropyForm from per-cross facts (hER, hblockE, hcoarse). -/
noncomputable def FaddeevEntropyForm_ofCrossFacts
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hcross.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun)
    (hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
        hcross.entropy_reduction.Hfun qk)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hcross.entropy_reduction.Hfun p) :
    FaddeevEntropyForm F := by
  have hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    { regularity := hreg
      grouping_recursion :=
        satisfiesFaddeevRecursion_ofCrossFacts F hax hcross hreg hER hblockE hcoarse }
  have hstandard :
      FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun :=
    finiteFaddeevStandardHypotheses_of_axioms hax hcross hrecForm hsupport
  have hex :=
    hfad.of_standard_hypotheses
      hcross.entropy_reduction.Hfun hstandard
  have hH : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hcross.entropy_reduction.Hfun q = (Classical.choose hex) * H(q) :=
    (Classical.choose_spec hex).2
  have hHfun_pos : 0 < hcross.entropy_reduction.Hfun (Dist.uniform (A := ULift.{u,0} Bool)) :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrecForm
  exact
    { cross_prior := hcross
      alpha := Classical.choose hex
      alpha_pos :=
        alpha_strict_pos_of_positive_Hfun_witness F hax hcross hrecForm hHfun_pos
          (Classical.choose hex) hH
      H_eq_alpha_shannon := hH
      a3_block_equivalence := a3_block_equivalence_of_traceAxioms F hax }

/- PureTraceMIRepresentation from per-cross facts. -/
theorem MIRep_ofCrossFacts
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hcross.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun)
    (hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
        hcross.entropy_reduction.Hfun qk)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hcross.entropy_reduction.Hfun p) :
    PureTraceMIRepresentation F :=
  let hfe : FaddeevEntropyForm F :=
    FaddeevEntropyForm_ofCrossFacts
      hfad F hax hcross hreg hsupport hER hblockE hcoarse
  MIRep_of_SufficiencyMIPackage F
    (FullSupportMIRepExtendsToBoundary_of_supportRestriction F
      (FullSupportBlockMI_of_FaddeevEntropyForm F hfe) hax
      (FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F hfe))



/-! ## Producers for wrapCross (bridge full-support Hfun, block-embed, entropy reduction) -/

/- On full support, wrapCross's Hfun equals the original hcross's Hfun. -/
theorem wrapCross_Hfun_fullSupport
    {F : PrefFamily.{u}} (hcross : CrossPriorBlockRepresentation F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross.entropy_reduction.scale_coherence.scale q /
          hcross.entropy_reduction.scale_coherence.scale r.restrictToSupport)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    (wrapCross hcross hsf).entropy_reduction.Hfun q =
      normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel := by
  -- LHS: Hfun(wrapCross) q = normalizedValue (boundaryComplete) q id  (definitional)
  --     = V q id / wrapScale q = V q id / scale q  (full support) = normalizedValue original q id
  show normalizedValue (boundaryCompleteScale hcross.entropy_reduction.scale_coherence hsf) q
      Channel.idChannel = _
  unfold normalizedValue
  change _ / wrapScale hcross.entropy_reduction.scale_coherence q = _
  rw [wrapScale_fullSupport _ q hq]
  rfl

/- Generic block-embed Hfun invariance from: per-cross Hfun-support-restriction (hhfunC) +
   per-cross full-support relabel invariance (hrelabC). Mirrors the closure proof. -/
theorem Hfun_blockEmbed_ofFacts
    (F : PrefFamily.{u}) (hcross : CrossPriorBlockRepresentation F)
    (hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q = hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hrelabC : ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A), q.FullSupport →
      hcross.entropy_reduction.Hfun (Relabeling.relabelDist e q) =
        hcross.entropy_reduction.Hfun q)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
    (k : K) (qk : Dist (Act k)) :
    hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
      hcross.entropy_reduction.Hfun qk := by
  haveI : Nonempty (supportSubtype qk) := supportSubtype_nonempty qk
  haveI : Nonempty (supportSubtype (blockEmbedDist Act k qk)) :=
    supportSubtype_nonempty (blockEmbedDist Act k qk)
  have hleft := hhfunC (blockEmbedDist Act k qk)
  have hright := hhfunC qk
  have hrestrict : (blockEmbedDist Act k qk).restrictToSupport =
      Relabeling.relabelDist (blockEmbedSupportEquiv Act k qk).symm qk.restrictToSupport :=
    restrict_blockEmbed_eq_relabel_support Act k qk
  have hrel := hrelabC (blockEmbedSupportEquiv Act k qk).symm qk.restrictToSupport
    (Dist.restrictToSupport_fullSupport qk)
  calc
    hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk)
        = hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk).restrictToSupport := hleft
    _ = hcross.entropy_reduction.Hfun
          (Relabeling.relabelDist (blockEmbedSupportEquiv Act k qk).symm qk.restrictToSupport) := by
          rw [hrestrict]
    _ = hcross.entropy_reduction.Hfun qk.restrictToSupport := hrel
    _ = hcross.entropy_reduction.Hfun qk := hright.symm

/- Generic coarse-reveal entropy reduction (hER) from per-cross facts. -/
theorem coarseReveal_entropyReduction_ofFacts
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    (hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q = hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hIntC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      posteriorLawIntegral q P hcross.entropy_reduction.Hfun =
        posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
          hcross.entropy_reduction.Hfun)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    hcross.entropy_reduction.Hfun (sigmaDist p q) =
      normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
        (coarseRevealChannel Act) +
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
        hcross.entropy_reduction.Hfun := by
  set s : Dist ((k : K) × Act k) := sigmaDist p q with hsdef
  set C : Channel ((k : K) × Act k) K := coarseRevealChannel Act with hCdef
  by_cases hs : s.FullSupport
  · have hER := hcross.entropy_reduction.value_entropy_reduction s hs C
    have hER' : normalizedValue hcross.entropy_reduction.scale_coherence s C =
        hcross.entropy_reduction.Hfun s -
          posteriorLawIntegral s C hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    linarith
  · haveI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
    have hH := hhfunC s
    have hV := hnormC C s hs
    have hI := hIntC C s
    have hER := hcross.entropy_reduction.value_entropy_reduction
      s.restrictToSupport (Dist.restrictToSupport_fullSupport s) (Channel.restrictToSupport C s)
    have hER' : normalizedValue hcross.entropy_reduction.scale_coherence
          s.restrictToSupport (Channel.restrictToSupport C s) =
        hcross.entropy_reduction.Hfun s.restrictToSupport -
          posteriorLawIntegral s.restrictToSupport (Channel.restrictToSupport C s)
            hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    rw [hH, hV, hI]
    linarith



/-! ## Exported MI theorem with NO cardinal-boundary assumption -/

/- The exported final theorem WITHOUT FiniteCardinalSupportBoundaryAssumptions.
   Uses the boundary-completed cross-prior representation built from the closure hcross. -/
theorem MIRep_of_PureTraceConditions_HM_Faddeev_withPreEntropyInputs_noCardinal
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hpre : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    -- coherence clause supplied by the HM interface (marginalValue support-face):
    (hcohRaw : ∀ (hV : PosteriorValueRepresentation F)
      {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) [Nonempty (supportSubtype q)] (d : Dist (supportSubtype q)),
      hint.marginalValue F hV q (Channel.actionPushforward d (supportIncludeKernel q)) =
        hint.marginalValue F hV q.restrictToSupport d)
    (hax : PureTraceConditions F) :
    PureTraceMIRepresentation F := by
  set hcross := crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
    hfaces hhm huniq hprod haff hpre hax with hcrossdef
  -- support_face_scale from hfaces (hcross.scale = hfaces scale by construction)
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
  -- Hfun of hc is definitionally normalizedValue (boundaryComplete) · id
  have hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hc.entropy_reduction.Hfun q =
        normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel :=
    fun q => rfl
  -- field 1 for hc:
  have hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hc.entropy_reduction.scale_coherence q P =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    intro A O _ _ _ _ _ P q hqb
    exact field1_boundaryComplete hint hcross.entropy_reduction.scale_coherence hsf
      (fun {A} _ _ _ q _ d => hcohRaw hcross.entropy_reduction.scale_coherence.branch_agg.value_rep q d)
      P q hqb
  -- hhfunC: Hfun q = Hfun (q|supp) for hc
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
  -- hrelabC: full-support relabel invariance of Hfun for hc, via wrapCross bridge + closure relabel
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
    -- now goal: normalizedValue hcross (relabel e qA) id = normalizedValue hcross qA id
    -- = Hfun(hcross)(relabel) = Hfun(hcross) qA via closure Hfun_relabel_fullSupport + Hcandidate rfl
    have h1 : normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist e qA) Channel.idChannel =
        hcross.entropy_reduction.Hfun (Relabeling.relabelDist e qA) := by
      rw [hcrossdef]; rfl
    have h2 : normalizedValue hcross.entropy_reduction.scale_coherence qA Channel.idChannel =
        hcross.entropy_reduction.Hfun qA := by
      rw [hcrossdef]; rfl
    rw [h1, h2, hcrossdef]
    exact Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
      hhm huniq haff hpre hax e qA hqA
  -- hIntC: posterior-law integral support restriction for hc
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
    -- Hfun_supportInclude for hc: Hfun (incl-pushforward t) = Hfun t
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
  -- regularity for hc
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
    fun {K} _ _ _ Act _ _ _ _ p q => coarseReveal_entropyReduction_ofFacts F hax hc hnormC hhfunC hIntC Act p q
  have hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hc.entropy_reduction.Hfun (blockEmbedDist Act k qk) = hc.entropy_reduction.Hfun qk :=
    fun {K} _ _ _ Act _ _ _ _ k qk => Hfun_blockEmbed_ofFacts F hc hhfunC hrelabC Act k qk
  have hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hc.entropy_reduction.Hfun p :=
    fun {K} _ _ _ Act _ _ _ _ p q => coarseVal_forCross F hax hc hreg hnormC
      (field3_restricted_coarse_reveal F hax hc hreg) hhfunC Act p q
  intro A O instA instDA instO instDO P qq qq'
  exact MIRep_ofCrossFacts
    hfad F hax hc hreg hhfunC hER hblockE hcoarse P qq qq'

end TraceableAgency
