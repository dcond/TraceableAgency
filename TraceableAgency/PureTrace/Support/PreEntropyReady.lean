/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.RepairedPreEntropyTargets
import TraceableAgency.PureTrace.Support.FullPreEntropyClosure
import TraceableAgency.PureTrace.Support.Faddeev

/-!
# Pre-Entropy Ready Face Scales

This module fixes the architecture exposed by the strict countermodel audits:
product-normalized selected representatives and the pre-universal cross-prior
block bridge are construction data, not theorems of an arbitrary
`CoherentRelabelingFaceScalesStructure`.

The final constructor below consumes one coherent ready object rather than a
long list of scattered cardinal/product/grouping primitives.
-/

namespace TraceableAgency

universe u

/--
The pre-universal block-reveal value identity follows from the unscaled
cross-prior block bridge and A5 projection/refinement neutrality.

This is a face-scale version of the coarse-reveal argument in the TeX proof:
coarse reveal and coarse identity weakly dominate each other after the
appropriate action coarsening/refinement, so the unscaled blockbridge identifies
their selected values.
-/
theorem finitePreUniversalBlockRevealValue_of_crossPriorBlockBridge
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbridge : FinitePreUniversalCrossPriorBlockBridgeFor hfaces) :
    FinitePreUniversalBlockRevealValueFor hfaces where
  block_reveal_value_eq_fullRevelationValue := by
    intro hax K _ _ _ Act _ _ _ _ p f hp _hf hsigma
    have hcoarse :
        (preUniversalCoarseRevealChannel (K := K) Act) =
          coarseRevealChannel Act := rfl
    have hrel₁_old :=
      coarseReveal_rel_id_of_A5 F hax Act p f
    have hrel₁ :
        F.rel
          (blockChannel
          (preUniversalCoarseRevealChannel (K := K) Act)
          (Channel.idChannel : Channel K K))
          (inlDist (sigmaDist p f)) (inrDist p) := by
      simpa [hcoarse] using hrel₁_old
    have hrel₂_old :=
      id_rel_coarseReveal_of_A5 F hax Act p f
    have hrel₂ :
        F.rel
          (blockChannel
          (Channel.idChannel : Channel K K)
          (preUniversalCoarseRevealChannel (K := K) Act))
          (inlDist p) (inrDist (sigmaDist p f)) := by
      simpa [hcoarse] using hrel₂_old
    have hge₁ :
        hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
            (experimentOfChannel
              (preUniversalCoarseRevealChannel (K := K) Act)) ≥
          fullRevelationValueForFaceScales hfaces p := by
      have h :=
        (hbridge.unscaled_cross_prior_block_rep hax
          (q := sigmaDist p f) (r := p) hsigma hp
          (preUniversalCoarseRevealChannel (K := K) Act)
          (Channel.idChannel : Channel K K)).mp hrel₁
      simpa [fullRevelationValueForFaceScales] using h
    have hge₂ :
        fullRevelationValueForFaceScales hfaces p ≥
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
            (experimentOfChannel
              (preUniversalCoarseRevealChannel (K := K) Act)) := by
      have h :=
        (hbridge.unscaled_cross_prior_block_rep hax
          (q := p) (r := sigmaDist p f) hp hsigma
          (Channel.idChannel : Channel K K)
          (preUniversalCoarseRevealChannel (K := K) Act)).mp hrel₂
      simpa [fullRevelationValueForFaceScales] using h
    exact le_antisymm hge₂ hge₁

/-- Value transport for arbitrary dependent-sum support faces.

This is the fiber version of the coordinate support-face representative
normalization: a posterior supported on the block `{k} × Act k` is evaluated with
the intrinsic representative on `Act k`. -/
structure FiniteBlockSupportFaceValueIdentificationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_value :
    ∀ (_hax : PureTraceConditions F)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.branch_agg.value_rep.V
        (blockEmbedDist Act k q)
        (experimentOfChannel
          (Channel.idChannel : Channel ((k : K) × Act k) ((k : K) × Act k))) =
      fullRevelationValueForFaceScales hfaces q

/-- Scale transport for arbitrary dependent-sum support faces. -/
structure FiniteBlockSupportFaceScaleIdentificationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_scale :
    ∀ (_hax : PureTraceConditions F)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.scale_factorization.scale
        (blockEmbedDist Act k q) =
      hfaces.branch_result.scale_factorization.scale q

/-- Reference normalization for the product `Z` gauge. -/
structure FiniteProductReferenceZNormalizationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  reference_Z_eq_one :
    ∀ (hax : PureTraceConditions F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- Explicit representative/gauge/support normalizations used by the full
pre-entropy constructor.

This bundle intentionally contains only harmless choices: coordinate and block
support-face identifications, product-reference `Z` gauge normalization, and
singleton-scale normalization.  The product theorem inputs remain outside this
bundle. -/
structure PreEntropyRepresentativeGaugeNormalizations.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  coordinate_value :
    FiniteCoordinateSupportFaceValueIdentificationFor hfaces
  coordinate_scale :
    FiniteCoordinateSupportFaceScaleIdentificationFor hfaces
  block_value :
    FiniteBlockSupportFaceValueIdentificationFor hfaces
  block_scale :
    FiniteBlockSupportFaceScaleIdentificationFor hfaces
  reference_z :
    FiniteProductReferenceZNormalizationFor hfaces hprod
  universal_singleton :
    FiniteUniversalScaleSingletonNormalizationFor hfaces

/-- Outcome marginal of a channel followed by full revelation. -/
theorem preUniversal_outcomeMarginal_seq_id_apply
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) (o : O) (a : A) :
    Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) =
      q a * P a o := by
  unfold Channel.outcomeMarginal
  simp only [seqCompose_apply, Channel.idChannel]
  rw [Finset.sum_eq_single a]
  · simp [Dist.pure_apply_self]
  · intro b _ hb
    have hab : a ≠ b := fun h => hb h.symm
    simp [Dist.pure_apply_ne _ _ hab]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

/-- Positive posterior after a channel followed by full revelation is pure. -/
theorem preUniversal_posterior_seq_id_eq_pure_of_pos
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) {o : O} {a : A}
    (hpos : Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) > 0) :
    Channel.posterior (P ▷ fun _ => Channel.idChannel) q (o, a) =
      Dist.pure a := by
  ext b
  have hm :
      Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) =
        q a * P a o :=
    preUniversal_outcomeMarginal_seq_id_apply q P o a
  unfold Channel.posterior
  rw [dif_pos hpos]
  change q b * ((P ▷ fun _ => Channel.idChannel) b) (o, a) /
      Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) =
    (Dist.pure a) b
  rw [hm]
  by_cases hba : b = a
  · subst b
    simp [seqCompose_apply, Channel.idChannel, Dist.pure_apply_self,
      div_self (ne_of_gt (by rwa [hm] at hpos))]
  · have hab : a ≠ b := fun h => hba h.symm
    simp [seqCompose_apply, Channel.idChannel, Dist.pure_apply_ne _ _ hab,
      Dist.pure_apply_ne _ _ hba]

/-- Posterior-law integral of full revelation is the expectation over pure
posteriors. -/
theorem preUniversal_posteriorLawIntegral_idChannel_eq_sum_pure
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (φ : Dist A → ℝ) :
    posteriorLawIntegral q Channel.idChannel φ =
      ∑ a : A, q a * φ (Dist.pure a) := by
  unfold posteriorLawIntegral
  apply Finset.sum_congr rfl
  intro a _
  rw [outcomeMarginal_idChannel']
  by_cases ha : q a > 0
  · rw [posterior_idChannel_eq_pure_of_pos q a ha]
  · have hzero : q a = 0 :=
      le_antisymm (le_of_not_gt ha) (q.nonneg a)
    simp [hzero]

/-- Posterior-law integral of a channel followed by full revelation is also the
expectation over pure posteriors. -/
theorem preUniversal_posteriorLawIntegral_seq_id_eq_sum_pure
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (P ▷ fun _ => Channel.idChannel) φ =
      ∑ a : A, q a * φ (Dist.pure a) := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  have hterm :
      (∑ x : O, ∑ y : A,
        Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (x, y) *
          φ (Channel.posterior (P ▷ fun _ => Channel.idChannel) q (x, y))) =
      ∑ x : O, ∑ y : A, q y * P y x * φ (Dist.pure y) := by
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro a _
    by_cases hpos :
        Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) > 0
    · rw [preUniversal_posterior_seq_id_eq_pure_of_pos q P hpos,
        preUniversal_outcomeMarginal_seq_id_apply q P o a]
    · have hm0 :
        Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) = 0 :=
        le_antisymm (le_of_not_gt hpos)
          ((Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q).nonneg (o, a))
      have hqa : q a * P a o = 0 := by
        rw [← preUniversal_outcomeMarginal_seq_id_apply q P o a, hm0]
      rw [hm0, hqa]
      ring
  rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ x : O, q a * P a x * φ (Dist.pure a))
        = q a * φ (Dist.pure a) * ∑ x : O, P a x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro o _
          ring
    _ = q a * φ (Dist.pure a) := by
          rw [(P a).sum_eq_one, mul_one]

/-- A channel followed by full revelation has the same posterior law as full
revelation. -/
theorem preUniversal_samePosteriorLaw_seq_id_full_revelation
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    SamePosteriorLawExp q
      (experimentOfChannel (P ▷ fun _ => Channel.idChannel))
      (experimentOfChannel Channel.idChannel) := by
  intro φ _hφ
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  rw [preUniversal_posteriorLawIntegral_seq_id_eq_sum_pure,
    preUniversal_posteriorLawIntegral_idChannel_eq_sum_pure]

/-- A dependent sigma type is non-subsingleton if one of its fibers is. -/
theorem not_subsingleton_sigma_of_fiber_not_subsingleton
    {K : Type u} [Nonempty K]
    (Act : K → Type u) [∀ k, Nonempty (Act k)]
    (hnd : ∀ k, ¬ Subsingleton (Act k)) :
    ¬ Subsingleton ((k : K) × Act k) := by
  classical
  intro hsigma
  let k : K := Classical.choice (inferInstance : Nonempty K)
  have hAct : Subsingleton (Act k) := by
    refine ⟨?_⟩
    intro a b
    have h :
        (Sigma.mk k a : (k : K) × Act k) = Sigma.mk k b :=
      Subsingleton.elim _ _
    cases h
    rfl
  exact hnd k hAct

/-- Product-revelation scale links identify the branch-scale ratio with the
product-`Z` ratio on nondegenerate full-support priors. -/
theorem faceScale_scale_div_eq_productScaleZ_div_of_productRevelation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hfaces.branch_result.scale_factorization.scale q /
        hfaces.branch_result.scale_factorization.scale r =
      productScaleZForFaceScales hfaces hprod hax q /
        productScaleZForFaceScales hfaces hprod hax r := by
  classical
  have hqr : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  have hs_prod_pos :
      0 < hfaces.branch_result.scale_factorization.scale (prodDist q r) :=
    hfaces.branch_result.scale_factorization.scale_pos (prodDist q r) hqr
  have hs_q_pos :
      0 < hfaces.branch_result.scale_factorization.scale q :=
    hfaces.branch_result.scale_factorization.scale_pos q hq
  have hs_r_pos :
      0 < hfaces.branch_result.scale_factorization.scale r :=
    hfaces.branch_result.scale_factorization.scale_pos r hr
  have hleft :=
    hlink.scale_product_left hax q r hq hr hA hB
  have hright :=
    hlink.scale_product_right hax q r hq hr hA hB
  have hZr_ne :
      productScaleZForFaceScales hfaces hprod hax r ≠ 0 := by
    intro hz
    have hzero :
        hfaces.branch_result.scale_factorization.scale (prodDist q r) = 0 := by
      rw [hright]
      simpa [productScaleZForFaceScales] using congrArg
        (fun z => z * hfaces.branch_result.scale_factorization.scale q) hz
    exact ne_of_gt hs_prod_pos hzero
  have hs_r_ne :
      hfaces.branch_result.scale_factorization.scale r ≠ 0 :=
    ne_of_gt hs_r_pos
  have heq :
      productScaleZForFaceScales hfaces hprod hax q *
          hfaces.branch_result.scale_factorization.scale r =
        productScaleZForFaceScales hfaces hprod hax r *
          hfaces.branch_result.scale_factorization.scale q := by
    simpa [productScaleZForFaceScales] using hleft.symm.trans hright
  field_simp [hs_r_ne, hZr_ne]
  linarith

/-- The product `Z` factor is nonzero under product-revelation scale links. -/
theorem productScaleZ_ne_zero_of_productRevelation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    productScaleZForFaceScales hfaces hprod hax r ≠ 0 := by
  classical
  have hqr : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  have hs_prod_pos :
      0 < hfaces.branch_result.scale_factorization.scale (prodDist q r) :=
    hfaces.branch_result.scale_factorization.scale_pos (prodDist q r) hqr
  have hright :=
    hlink.scale_product_right hax q r hq hr hA hB
  intro hz
  have hzero :
      hfaces.branch_result.scale_factorization.scale (prodDist q r) = 0 := by
    rw [hright]
    simpa [productScaleZForFaceScales] using congrArg
      (fun z => z * hfaces.branch_result.scale_factorization.scale q) hz
  exact ne_of_gt hs_prod_pos hzero

/-- Pre-universal block-reveal chain assembly from normalized branch-chain,
fiber support-face normalizations, product-revelation scale links, and the
reference `Z` gauge. -/
theorem preUniversalBlockRevealChainRule_of_branchChain_supportFace_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hvalue : FiniteBlockSupportFaceValueIdentificationFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleIdentificationFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalBlockRevealChainRuleFor hfaces hprod where
  block_reveal_chain := by
    intro hax K _ _ _ Act _ _ _ _ p f hp hf hsigma hKnd hAnd
    classical
    let SigmaAct : Type u := (k : K) × Act k
    let C : Channel SigmaAct K :=
      preUniversalCoarseRevealChannel (K := K) Act
    have hCeq : C = coarseRevealChannel Act := rfl
    have hsigma_nd : ¬ Subsingleton SigmaAct :=
      not_subsingleton_sigma_of_fiber_not_subsingleton Act hAnd
    have hchain :=
      hfaces.normalizedChainRule (sigmaDist p f) hsigma C
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
      unfold branchNormalizedValue at hchain
      simp only [CoherentRelabelingFaceScalesStructure.chain,
        BranchAggregationCocycleNormalizedChainRuleStructure.chain,
        branchChainStructure_of_scaleFactorization] at hchain
      rw [hseqV] at hchain
      have hmarg :
          Channel.outcomeMarginal C (sigmaDist p f) = p := by
        simpa [C, hCeq] using outcomeMarginal_coarseReveal_sigmaDist Act p f
      rw [hmarg] at hchain
      have hpost :
          ∀ k,
            Channel.posterior C (sigmaDist p f) k =
              blockEmbedDist Act k (f k) := by
        intro k
        simpa [C, hCeq] using
          posterior_coarseReveal_sigmaDist_of_pos Act p f k (hp k)
      have hterms :
          ∑ k, p k *
            (hfaces.branch_result.branch_agg.value_rep.V
              (Channel.posterior C (sigmaDist p f) k)
              (experimentOfChannel
                (Channel.idChannel : Channel SigmaAct SigmaAct)) /
              hfaces.branch_result.scale_factorization.scale
                (Channel.posterior C (sigmaDist p f) k)) =
          ∑ k, p k *
            (fullRevelationValueForFaceScales hfaces (f k) /
              hfaces.branch_result.scale_factorization.scale (f k)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hpost k]
        rw [hvalue.block_face_value hax Act k (f k) (hf k)]
        rw [hscale.block_face_scale hax Act k (f k) (hf k)]
      rw [hterms] at hchain
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
    rw [hbranchScale, hscaleToZ]
  reference_Z_eq_one := href.reference_Z_eq_one

/-- Direct pre-universal grouping recursion from block value, POS, and the
actual chain-construction ingredients, without taking GR/W or the block-reveal
chain rule as an external assumption. -/
theorem finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportFace_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hblock : FinitePreUniversalBlockRevealValueFor hfaces)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hvalue : FiniteBlockSupportFaceValueIdentificationFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleIdentificationFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursion_of_blockReveal
    hblock
    (preUniversalBlockRevealChainRule_of_branchChain_supportFace_productScale
      hvalue hscale hlink href)
    hpos

/-- Full-support selected actionbase scalar.

This is the HM/affine-uniqueness part of the cardinal relabeling proof.  It is
restricted to full-support nondegenerate priors because the public
`PosteriorValueRepresentation` order-representation field is full-support. -/
structure FiniteFullSupportSelectedActionbaseScalarFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  relabel_scalar :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (eA : A ≃ B) (q : Dist A) (_hq : q.FullSupport)
      (_hA : ¬ Subsingleton A),
      ∃ c : ℝ, 0 < c ∧
        ∀ {O Y : Type v}
          [Fintype O] [DecidableEq O]
          [Fintype Y] [DecidableEq Y]
          (eO : O ≃ Y) (P : Channel A O),
          hfaces.branch_result.branch_agg.value_rep.V
              (Relabeling.relabelDist eA q)
              (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
            c *
              hfaces.branch_result.branch_agg.value_rep.V q
                (experimentOfChannel P)

/-- Outcome relabeling alone does not change the posterior law. -/
theorem samePosteriorLawExp_outcomeRelabel
    {A O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (q : Dist A) (P : Channel A O) :
    SamePosteriorLawExp q
      (experimentOfChannel
        (Relabeling.relabelChannel (Equiv.refl A) eO P))
      (experimentOfChannel P) := by
  intro φ _hφ
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  have h :=
    posteriorLawIntegral_relabelChannel (Equiv.refl A) eO q P φ
  simpa using h

/-- Relabeling commutes with public-coin mixtures in the action coordinate. -/
theorem relabelChannel_publicMix_action
    {A B O Y : Type u}
    [Fintype A] [Fintype B]
    [Fintype O] [Fintype Y]
    (eA : A ≃ B) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) :
    Relabeling.relabelChannel eA (Equiv.refl (O ⊕ Y))
        (publicMixChannel t ht0 ht1 P Q) =
      publicMixChannel t ht0 ht1
        (Relabeling.relabelChannel eA (Equiv.refl O) P)
        (Relabeling.relabelChannel eA (Equiv.refl Y) Q) := by
  ext b oy
  cases oy with
  | inl o => rfl
  | inr y => rfl

/-- Action relabeling sends the no-information channel to no information. -/
theorem relabelChannel_uninformative_action
    {A B : Type u} [Fintype A] [Fintype B]
    (eA : A ≃ B) :
    Relabeling.relabelChannel eA (Equiv.refl PUnit.{u + 1})
        (Channel.uninformativeChannelU A) =
      Channel.uninformativeChannelU B := by
  ext b u
  cases u
  rfl

/-- Positive scalar relating an arbitrary zero-normalised affine posterior
representative to its action-relabelled copy at a full-support,
non-singleton prior.  This is the generic form of affine-utility uniqueness;
it does not assume that the representative has already been made natural. -/
theorem posteriorValue_relabel_positiveScalar_fullSupport
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (V : PosteriorValueRepresentation F)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (eA : A ≃ B) (q : Dist A) (hq : q.FullSupport)
    (hA : ¬ Subsingleton A) :
    ∃ c : ℝ, 0 < c ∧
      ∀ {O Y : Type u}
        [Fintype O] [DecidableEq O]
        [Fintype Y] [DecidableEq Y]
        (eO : O ≃ Y) (P : Channel A O),
        V.V (Relabeling.relabelDist eA q)
            (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          c * V.V q (experimentOfChannel P) := by
  classical
  let q' : Dist B := Relabeling.relabelDist eA q
  have hq' : q'.FullSupport :=
    Relabeling.relabelDist_fullSupport eA q hq
  let base :
      {O : Type u} → [Fintype O] → [DecidableEq O] →
        Channel A O → ℝ :=
    fun {O} [Fintype O] [DecidableEq O] P =>
      V.V q (experimentOfChannel P)
  let target :
      {O : Type u} → [Fintype O] → [DecidableEq O] →
        Channel A O → ℝ :=
    fun {O} [Fintype O] [DecidableEq O] P =>
      V.V q'
        (experimentOfChannel
          (Relabeling.relabelChannel eA (Equiv.refl O) P))
  let hVaff :=
    posteriorValueAffine_of_lawAffine_and_publicMixLaw
      finitePosteriorLawValueAffine_of_representation
  have hbaseAff :
      ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        base (publicMixChannel t ht0 ht1 P Q) =
          t * base P + (1 - t) * base Q := by
    intro O Z _ _ _ _ t ht0 ht1 P Q
    exact hVaff.V_publicMix_affine F hax V q hq t ht0 ht1 P Q
  have htargetAff :
      ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        target (publicMixChannel t ht0 ht1 P Q) =
          t * target P + (1 - t) * target Q := by
    intro O Z _ _ _ _ t ht0 ht1 P Q
    change
      V.V q'
          (experimentOfChannel
            (Relabeling.relabelChannel eA (Equiv.refl (O ⊕ Z))
              (publicMixChannel t ht0 ht1 P Q))) =
        t * target P + (1 - t) * target Q
    rw [show
        Relabeling.relabelChannel eA (Equiv.refl (O ⊕ Z))
            (publicMixChannel t ht0 ht1 P Q) =
          publicMixChannel t ht0 ht1
            (Relabeling.relabelChannel eA (Equiv.refl O) P)
            (Relabeling.relabelChannel eA (Equiv.refl Z) Q) from
          relabelChannel_publicMix_action eA t ht0 ht1 P Q]
    exact hVaff.V_publicMix_affine F hax V q' hq' t ht0 ht1
      (Relabeling.relabelChannel eA (Equiv.refl O) P)
      (Relabeling.relabelChannel eA (Equiv.refl Z) Q)
  have hnonconst :
      base (Channel.idChannel : Channel A A) ≠
        base (Channel.uninformativeChannelU A) := by
    have hstrict :=
      branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
    exact branch_value_ne_of_strict_experiment_pref F V q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      hstrict.1 hstrict.2
  have horder :
      ∀ {O : Type u} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        target P ≥ target Q ↔ base P ≥ base Q := by
    intro O _ _ P Q
    let P' : Channel B O := Relabeling.relabelChannel eA (Equiv.refl O) P
    let Q' : Channel B O := Relabeling.relabelChannel eA (Equiv.refl O) Q
    have hrel_order :
        ExperimentPairPref F (experimentOfChannel P') (experimentOfChannel Q')
            q' q' ↔
          ExperimentPairPref F (experimentOfChannel P) (experimentOfChannel Q)
            q q := by
      have hblockRelabel :
          Relabeling.relabelChannel (Equiv.sumCongr eA eA)
              (Equiv.sumCongr (Equiv.refl O) (Equiv.refl O))
              (blockChannel P Q) =
            blockChannel P' Q' := by
        simpa [P', Q'] using
          Relabeling.relabel_blockChannel_sumCongr_eq
            eA (Equiv.refl O) P Q
      have hrel :=
        Relabeling.relabel_rel_of_axioms F hax
          (Equiv.sumCongr eA eA)
          (Equiv.sumCongr (Equiv.refl O) (Equiv.refl O))
          (blockChannel P Q) (inlDist q) (inrDist q)
      have hrel' :
          F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
            F.rel (blockChannel P' Q') (inlDist q') (inrDist q') := by
        have hrel'' := hrel
        rw [hblockRelabel] at hrel''
        rw [Relabeling.relabelDist_sumCongr_inl eA q] at hrel''
        rw [Relabeling.relabelDist_sumCongr_inr eA q] at hrel''
        simpa [q'] using hrel''
      change
        F.rel (blockChannel P' Q') (inlDist q') (inrDist q') ↔
          F.rel (blockChannel P Q) (inlDist q) (inrDist q)
      exact hrel'.symm
    have htgt :=
      V.represents_block_comparisons q' hq'
        (experimentOfChannel P') (experimentOfChannel Q')
    have hbase :=
      V.represents_block_comparisons q hq
        (experimentOfChannel P) (experimentOfChannel Q)
    calc
      target P ≥ target Q
          ↔ ExperimentPairPref F
              (experimentOfChannel P') (experimentOfChannel Q') q' q' := by
            simpa [target, P', Q'] using htgt.symm
      _ ↔ ExperimentPairPref F
              (experimentOfChannel P) (experimentOfChannel Q) q q :=
            hrel_order
      _ ↔ base P ≥ base Q := by
            simpa [base] using hbase
  rcases huniq.positive_affine_transform base target
      hbaseAff htargetAff hnonconst horder with
    ⟨c, b, hc, hct⟩
  have hbaseU : base (Channel.uninformativeChannelU A) = 0 :=
    V.zero_normalized q hq
  have htargetU : target (Channel.uninformativeChannelU A) = 0 := by
    have hUrel := relabelChannel_uninformative_action eA
    simpa [target, q', hUrel] using V.zero_normalized q' hq'
  have hb : b = 0 := by
    have hU := hct (Channel.uninformativeChannelU A)
    rw [hbaseU, htargetU] at hU
    linarith
  refine ⟨c, hc, ?_⟩
  intro O Y _ _ _ _ eO P
  let P₀ : Channel B O :=
    Relabeling.relabelChannel eA (Equiv.refl O) P
  have hout :
      V.V q'
          (experimentOfChannel
            (Relabeling.relabelChannel eA eO P)) =
        V.V q' (experimentOfChannel P₀) := by
    have hsame :
        SamePosteriorLawExp q'
          (experimentOfChannel
            (Relabeling.relabelChannel (Equiv.refl B) eO P₀))
          (experimentOfChannel P₀) :=
      samePosteriorLawExp_outcomeRelabel eO q' P₀
    have hVsame :=
      V.respects_same_posterior_law q'
        (experimentOfChannel
          (Relabeling.relabelChannel (Equiv.refl B) eO P₀))
        (experimentOfChannel P₀) hsame
    simpa [P₀, Relabeling.relabelChannel_action_then_outcome] using hVsame
  have hmain := hct P
  rw [hb, add_zero] at hmain
  simpa [target, base, q', P₀] using hout.trans hmain

/-- Full-support actionbase scalar from order-level relabeling, HM public-mix
affinity, and finite affine-utility uniqueness. -/
theorem selectedActionbaseScalar_of_orderRelabeling_HM_fullSupport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    FiniteFullSupportSelectedActionbaseScalarFor hfaces where
  relabel_scalar := by
    intro hax A B _ _ _ _ _ _ eA q hq hA
    classical
    let V := hfaces.branch_result.branch_agg.value_rep
    let q' : Dist B := Relabeling.relabelDist eA q
    have hq' : q'.FullSupport :=
      Relabeling.relabelDist_fullSupport eA q hq
    let base :
        {O : Type u} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ :=
      fun {O} [Fintype O] [DecidableEq O] P =>
        V.V q (experimentOfChannel P)
    let target :
        {O : Type u} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ :=
      fun {O} [Fintype O] [DecidableEq O] P =>
        V.V q'
          (experimentOfChannel
            (Relabeling.relabelChannel eA (Equiv.refl O) P))
    let hVaff :=
      posteriorValueAffine_of_lawAffine_and_publicMixLaw
        (finitePosteriorLawValueAffine_of_HM hhm)
    have hbaseAff :
        ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
          [Fintype Z] [DecidableEq Z]
          (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
          (P : Channel A O) (Q : Channel A Z),
          base (publicMixChannel t ht0 ht1 P Q) =
            t * base P + (1 - t) * base Q := by
      intro O Z _ _ _ _ t ht0 ht1 P Q
      exact hVaff.V_publicMix_affine F hax V q hq t ht0 ht1 P Q
    have htargetAff :
        ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
          [Fintype Z] [DecidableEq Z]
          (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
          (P : Channel A O) (Q : Channel A Z),
          target (publicMixChannel t ht0 ht1 P Q) =
            t * target P + (1 - t) * target Q := by
      intro O Z _ _ _ _ t ht0 ht1 P Q
      change
        V.V q'
            (experimentOfChannel
              (Relabeling.relabelChannel eA (Equiv.refl (O ⊕ Z))
                (publicMixChannel t ht0 ht1 P Q))) =
          t * target P + (1 - t) * target Q
      rw [show
          Relabeling.relabelChannel eA (Equiv.refl (O ⊕ Z))
              (publicMixChannel t ht0 ht1 P Q) =
            publicMixChannel t ht0 ht1
              (Relabeling.relabelChannel eA (Equiv.refl O) P)
              (Relabeling.relabelChannel eA (Equiv.refl Z) Q) from
            relabelChannel_publicMix_action eA t ht0 ht1 P Q]
      exact hVaff.V_publicMix_affine F hax V q' hq' t ht0 ht1
        (Relabeling.relabelChannel eA (Equiv.refl O) P)
        (Relabeling.relabelChannel eA (Equiv.refl Z) Q)
    have hnonconst :
        base (Channel.idChannel : Channel A A) ≠
          base (Channel.uninformativeChannelU A) := by
      have hH_ne :
          fullRevelationValueForFaceScales hfaces q ≠ 0 :=
        fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax q hq hA
      have hU : base (Channel.uninformativeChannelU A) = 0 :=
        V.zero_normalized q hq
      intro hEq
      apply hH_ne
      simpa [base, fullRevelationValueForFaceScales, hU] using hEq
    have horder :
        ∀ {O : Type u} [Fintype O] [DecidableEq O]
          (P Q : Channel A O),
          target P ≥ target Q ↔ base P ≥ base Q := by
      intro O _ _ P Q
      let P' : Channel B O := Relabeling.relabelChannel eA (Equiv.refl O) P
      let Q' : Channel B O := Relabeling.relabelChannel eA (Equiv.refl O) Q
      have hrel_order :
          ExperimentPairPref F (experimentOfChannel P') (experimentOfChannel Q')
              q' q' ↔
            ExperimentPairPref F (experimentOfChannel P) (experimentOfChannel Q)
              q q := by
        have hblockRelabel :
            Relabeling.relabelChannel (Equiv.sumCongr eA eA)
                (Equiv.sumCongr (Equiv.refl O) (Equiv.refl O))
                (blockChannel P Q) =
              blockChannel P' Q' := by
          simpa [P', Q'] using
            Relabeling.relabel_blockChannel_sumCongr_eq
              eA (Equiv.refl O) P Q
        have hrel :=
          Relabeling.relabel_rel_of_axioms F hax
            (Equiv.sumCongr eA eA)
            (Equiv.sumCongr (Equiv.refl O) (Equiv.refl O))
            (blockChannel P Q) (inlDist q) (inrDist q)
        have hrel' :
            F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
              F.rel (blockChannel P' Q') (inlDist q') (inrDist q') := by
          have hrel'' := hrel
          rw [hblockRelabel] at hrel''
          rw [Relabeling.relabelDist_sumCongr_inl eA q] at hrel''
          rw [Relabeling.relabelDist_sumCongr_inr eA q] at hrel''
          simpa [q'] using hrel''
        change
          F.rel (blockChannel P' Q') (inlDist q') (inrDist q') ↔
            F.rel (blockChannel P Q) (inlDist q) (inrDist q)
        exact hrel'.symm
      have htgt :=
        V.represents_block_comparisons q' hq'
          (experimentOfChannel P') (experimentOfChannel Q')
      have hbase :=
        V.represents_block_comparisons q hq
          (experimentOfChannel P) (experimentOfChannel Q)
      calc
        target P ≥ target Q
            ↔ ExperimentPairPref F
                (experimentOfChannel P') (experimentOfChannel Q') q' q' := by
              simpa [target, P', Q'] using htgt.symm
        _ ↔ ExperimentPairPref F
                (experimentOfChannel P) (experimentOfChannel Q) q q :=
              hrel_order
        _ ↔ base P ≥ base Q := by
              simpa [base] using hbase
    rcases huniq.positive_affine_transform base target
        hbaseAff htargetAff hnonconst horder with
      ⟨c, b, hc, hct⟩
    have hbaseU : base (Channel.uninformativeChannelU A) = 0 :=
      V.zero_normalized q hq
    have htargetU : target (Channel.uninformativeChannelU A) = 0 := by
      have hUrel :=
        relabelChannel_uninformative_action eA
      simpa [target, q', hUrel] using V.zero_normalized q' hq'
    have hb : b = 0 := by
      have hU := hct (Channel.uninformativeChannelU A)
      rw [hbaseU, htargetU] at hU
      linarith
    refine ⟨c, hc, ?_⟩
    intro O Y _ _ _ _ eO P
    let P₀ : Channel B O :=
      Relabeling.relabelChannel eA (Equiv.refl O) P
    have hout :
        V.V q'
            (experimentOfChannel
              (Relabeling.relabelChannel eA eO P)) =
          V.V q' (experimentOfChannel P₀) := by
      have hsame :
          SamePosteriorLawExp q'
            (experimentOfChannel
              (Relabeling.relabelChannel (Equiv.refl B) eO P₀))
            (experimentOfChannel P₀) :=
        samePosteriorLawExp_outcomeRelabel eO q' P₀
      have hVsame :=
        V.respects_same_posterior_law q'
          (experimentOfChannel
            (Relabeling.relabelChannel (Equiv.refl B) eO P₀))
          (experimentOfChannel P₀) hsame
      simpa [P₀, Relabeling.relabelChannel_action_then_outcome] using hVsame
    have hmain := hct P
    rw [hb, add_zero] at hmain
    simpa [target, base, q', P₀] using hout.trans hmain

/-- Full-support scalar pinning for the selected representative.

This is the product-normalization calculation in the TeX proof, stated at the
same full-support/nondegenerate actionbase where the public HM representation
gives a scalar. -/
structure FiniteFullSupportSelectedPermutationInvariancePinningFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  scalar_eq_one :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (eA : A ≃ B) (q : Dist A) (_hq : q.FullSupport)
      (_hA : ¬ Subsingleton A)
      (c : ℝ) (_hc : 0 < c),
      (∀ {O Y : Type v}
          [Fintype O] [DecidableEq O]
          [Fintype Y] [DecidableEq Y]
          (eO : O ≃ Y) (P : Channel A O),
          hfaces.branch_result.branch_agg.value_rep.V
              (Relabeling.relabelDist eA q)
              (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
            c *
              hfaces.branch_result.branch_agg.value_rep.V q
                (experimentOfChannel P)) →
        c = 1

/-- Product normalization pins the full-support actionbase scalar to one. -/
theorem selectedPermutationInvariancePinning_of_productNormalization_fullSupport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haction : FiniteFullSupportSelectedActionbaseScalarFor hfaces)
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteFullSupportSelectedPermutationInvariancePinningFor hfaces where
  scalar_eq_one := by
    intro hax A B _ _ _ _ _ _ eA q hq hA c _hc hscalar
    classical
    let V := hfaces.branch_result.branch_agg.value_rep
    let K := universalScaleReferenceType
    let r : Dist K := universalScaleReferencePrior
    let q' : Dist B := Relabeling.relabelDist eA q
    let eProd : A × K ≃ B × K := Equiv.prodCongr eA (Equiv.refl K)
    have hr : r.FullSupport := universalScaleReferencePrior_fullSupport
    have hK : ¬ Subsingleton K := universalScaleReference_not_subsingleton
    have hq' : q'.FullSupport :=
      Relabeling.relabelDist_fullSupport eA q hq
    have hqr : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hProdND : ¬ Subsingleton (A × K) :=
      not_subsingleton_prod_left hA
    rcases haction.relabel_scalar hax eProd (prodDist q r) hqr hProdND with
      ⟨d, hdpos, hdscalar⟩
    let UA : Channel A PUnit.{u + 1} := Channel.uninformativeChannelU A
    let UB : Channel B PUnit.{u + 1} := Channel.uninformativeChannelU B
    let IR : Channel K K := Channel.idChannel
    let eUnitK : PUnit.{u + 1} × K ≃ PUnit.{u + 1} × K :=
      Equiv.prodCongr (Equiv.refl PUnit.{u + 1}) (Equiv.refl K)
    have hprodU := hdscalar eUnitK (prodChannel UA IR)
    have hprodU' :
        V.V (prodDist q' r) (experimentOfChannel (prodChannel UB IR)) =
          d *
            V.V (prodDist q r)
              (experimentOfChannel (prodChannel UA IR)) := by
      simpa [q', r, eProd, eUnitK, UA, UB, IR,
        Relabeling.relabelDist_prodCongr,
        Relabeling.relabelChannel_prodCongr,
        relabelChannel_uninformative_action] using hprodU
    have hUq' :
        V.V q' (experimentOfChannel UB) = 0 :=
      V.zero_normalized q' hq'
    have hUq :
        V.V q (experimentOfChannel UA) = 0 :=
      V.zero_normalized q hq
    have hprodU_left :
        V.V (prodDist q' r) (experimentOfChannel (prodChannel UB IR)) =
          fullRevelationValueForFaceScales hfaces r := by
      have hqa :=
        hprod.product_quasi_add hax q' r hq' hr UB IR
      rw [hqa, hUq']
      simp [fullRevelationValueForFaceScales, IR]
    have hprodU_right :
        V.V (prodDist q r) (experimentOfChannel (prodChannel UA IR)) =
          fullRevelationValueForFaceScales hfaces r := by
      have hqa :=
        hprod.product_quasi_add hax q r hq hr UA IR
      rw [hqa, hUq]
      simp [fullRevelationValueForFaceScales, IR]
    have hHr_ne :
        fullRevelationValueForFaceScales hfaces r ≠ 0 :=
      fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax r hr hK
    have hd_one : d = 1 := by
      have h :
          fullRevelationValueForFaceScales hfaces r =
            d * fullRevelationValueForFaceScales hfaces r := by
        simpa [hprodU_left, hprodU_right] using hprodU'
      have hmul :
          d * fullRevelationValueForFaceScales hfaces r =
            1 * fullRevelationValueForFaceScales hfaces r := by
        rw [one_mul]
        exact h.symm
      exact mul_right_cancel₀ hHr_ne hmul
    let Pid : Channel A A := Channel.idChannel
    let PidRel : Channel B A :=
      Relabeling.relabelChannel eA (Equiv.refl A) Pid
    let eAK : A × K ≃ A × K :=
      Equiv.prodCongr (Equiv.refl A) (Equiv.refl K)
    have hprodId := hdscalar eAK (prodChannel Pid IR)
    have hprodId' :
        V.V (prodDist q' r)
            (experimentOfChannel (prodChannel PidRel IR)) =
          V.V (prodDist q r)
            (experimentOfChannel (prodChannel Pid IR)) := by
      have htmp := hprodId
      rw [hd_one, one_mul] at htmp
      simpa [q', r, eProd, eAK, Pid, PidRel, IR,
        Relabeling.relabelDist_prodCongr,
        Relabeling.relabelChannel_prodCongr] using htmp
    have hPidRel :
        V.V q' (experimentOfChannel PidRel) =
          c * fullRevelationValueForFaceScales hfaces q := by
      have h := hscalar (Equiv.refl A) Pid
      simpa [PidRel, Pid, fullRevelationValueForFaceScales] using h
    have hqa_left :=
      hprod.product_quasi_add hax q' r hq' hr PidRel IR
    have hqa_right :=
      hprod.product_quasi_add hax q r hq hr Pid IR
    let Hq := fullRevelationValueForFaceScales hfaces q
    let Hr := fullRevelationValueForFaceScales hfaces r
    let k := hprod.kappa hax
    have hEq :
        c * Hq + Hr + k * (c * Hq) * Hr =
          Hq + Hr + k * Hq * Hr := by
      have h := hprodId'
      rw [hqa_left, hqa_right, hPidRel] at h
      simpa [Hq, Hr, k, fullRevelationValueForFaceScales, IR] using h
    have hHq_ne : Hq ≠ 0 := by
      exact fullRevelationValueForFaceScales_ne_zero_of_A1
        hfaces hax q hq hA
    have hZ_pos : 0 < 1 + k * Hr := by
      simpa [productScaleZForFaceScales, Hq, Hr, k, r] using
        hpos.Z_pos hax r hr
    have hZ_ne : 1 + k * Hr ≠ 0 := ne_of_gt hZ_pos
    have hfactor : (c - 1) * (Hq * (1 + k * Hr)) = 0 := by
      nlinarith [hEq]
    have hnonzero : Hq * (1 + k * Hr) ≠ 0 :=
      mul_ne_zero hHq_ne hZ_ne
    have hc_minus : c - 1 = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hnonzero
    linarith

/-- Exact selected relabeling on the full-support nondegenerate actionbase. -/
structure FiniteFullSupportSelectedPosteriorValueRelabelingFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  V_relabel_eq :
    ∀ (_hax : PureTraceConditions F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (eA : A ≃ B) (eO : O ≃ Y)
      (q : Dist A) (_hq : q.FullSupport) (_hA : ¬ Subsingleton A)
      (P : Channel A O),
      hfaces.branch_result.branch_agg.value_rep.V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P)

/-- Full-support selected value relabeling from the scalar theorem and product
normalization pinning. -/
theorem finiteFullSupportSelectedPosteriorValueRelabeling_of_actionbase_pinning
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haction : FiniteFullSupportSelectedActionbaseScalarFor hfaces)
    (hpin : FiniteFullSupportSelectedPermutationInvariancePinningFor hfaces) :
    FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces where
  V_relabel_eq := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q hq hA P
    rcases haction.relabel_scalar hax eA q hq hA with
      ⟨c, hc, hscalar⟩
    have hc1 : c = 1 :=
      hpin.scalar_eq_one hax eA q hq hA c hc hscalar
    have h := hscalar eO P
    simpa [hc1] using h

/-- Full-support selected value relabeling from HM/affine uniqueness and the
product-normalization pinning calculation. -/
theorem finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces :=
  let haction :=
    selectedActionbaseScalar_of_orderRelabeling_HM_fullSupport
      hhm huniq
  finiteFullSupportSelectedPosteriorValueRelabeling_of_actionbase_pinning
    haction
    (selectedPermutationInvariancePinning_of_productNormalization_fullSupport
      haction hpos)

/-- Full-revelation value is invariant under relabeling for full-support
nondegenerate priors, from the proved full-support selected relabeling theorem.
-/
theorem fullRevelationValueForFaceScales_relabel_eq_fullSupport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hfull : FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport)
    (hA : ¬ Subsingleton A) :
    fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) =
      fullRevelationValueForFaceScales hfaces q := by
  have hrel :=
    hfull.V_relabel_eq hax e e q hq hA
      (Channel.idChannel : Channel A A)
  have hid :
      Relabeling.relabelChannel e e (Channel.idChannel : Channel A A) =
        (Channel.idChannel : Channel B B) := by
    funext b
    ext b'
    rw [Relabeling.relabelChannel_apply]
    simp only [Channel.idChannel]
    by_cases hbb : b' = b
    · subst hbb
      rw [Dist.pure_apply_self, Dist.pure_apply_self]
    · rw [Dist.pure_apply_ne (e.symm b) (e.symm b')
          (fun h => hbb (e.symm.injective h)),
        Dist.pure_apply_ne b b' hbb]
  rw [hid] at hrel
  simpa [fullRevelationValueForFaceScales] using hrel

/--
Two-grouping theorem from the weight recursion using only the full-support
full-revelation relabeling theorem proved by actionbase scalar pinning.
-/
theorem finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hfull : FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces)
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hrec :
      FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod where
  reference_Z_eq_one := hrec.reference_Z_eq_one
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
        (f' ka).FullSupport :=
      fun ka => hgfs ka.1
    have hf'nd : ∀ ka : (k : K) × twoGroupingFiber U V k,
        ¬ Subsingleton (twoGroupingFiber U V ka.1) :=
      fun ka => hgnd ka.1
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
        change productScaleZForFaceScales hfaces hprod hax
            (prodDist u u) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax u u hu hu
      have hZft :
          productScaleZForFaceScales hfaces hprod hax (f (ULift.up true)) =
            productScaleZForFaceScales hfaces hprod hax v *
              productScaleZForFaceScales hfaces hprod hax v := by
        change productScaleZForFaceScales hfaces hprod hax
            (prodDist v v) = _
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

/--
Selected-relabeling variant of the two-grouping theorem from the weight
recursion.

The existing theorem uses the old all-representatives relabeling package only
to transport full-revelation value across the `twoGroupingReassoc` bijection.
The selected relabeling package is exactly sufficient for that one step.
-/
theorem finiteProductTwoGroupingWeightEquation_of_weightRecursion_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hrec :
      FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod where
  reference_Z_eq_one := hrec.reference_Z_eq_one
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
        (f' ka).FullSupport :=
      fun ka => hgfs ka.1
    have hf'nd : ∀ ka : (k : K) × twoGroupingFiber U V k,
        ¬ Subsingleton (twoGroupingFiber U V ka.1) :=
      fun ka => hgnd ka.1
    set T' := sigmaDist S f' with hT'
    have hT'fs : T'.FullSupport := sigmaDist_fullSupport S f' hSfs hf'fs
    haveI :
        Nonempty ((ka : (k : K) × twoGroupingFiber U V k) ×
          twoGroupingFiber U V ka.1) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    have hSnd : ¬ Subsingleton ((k : K) × twoGroupingFiber U V k) :=
      not_subsingleton_sigma hKnd
    have hHrel :
        fullRevelationValueForFaceScales hfaces
            (Relabeling.relabelDist (twoGroupingReassoc U V) T') =
          fullRevelationValueForFaceScales hfaces T' :=
      fullRevelationValueForFaceScales_relabel_eq_selected hsel hax
        (twoGroupingReassoc U V) T'
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
        change productScaleZForFaceScales hfaces hprod hax
            (prodDist u u) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax u u hu hu
      have hZft :
          productScaleZForFaceScales hfaces hprod hax (f (ULift.up true)) =
            productScaleZForFaceScales hfaces hprod hax v *
              productScaleZForFaceScales hfaces hprod hax v := by
        change productScaleZForFaceScales hfaces hprod hax
            (prodDist v v) = _
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

/--
Family-level grouping equation reconstructed from the weight recursion using
selected exact relabeling rather than the old all-representatives relabeling
package.
-/
theorem finiteProductGroupingEquation_of_weightRecursion_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hrec :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod) :
    FiniteProductGroupingEquationAssumptionsFor hfaces :=
  finiteProductGroupingEquation_of_twoGroupingWeightEquation
    (fun hprod =>
      finiteProductTwoGroupingWeightEquation_of_weightRecursion_selected hsel
        (hrec hprod)
        (productScaleZpositive_of_sliceTransform hprod haff))
    (fun hprod => productScaleZpositive_of_sliceTransform hprod haff)

/--
Family-level grouping equation reconstructed from the weight recursion using
only full-support selected relabeling, as proved from HM plus product
normalization.
-/
theorem finiteProductGroupingEquation_of_weightRecursion_fullSupportRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hrec :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod) :
    FiniteProductGroupingEquationAssumptionsFor hfaces :=
  finiteProductGroupingEquation_of_twoGroupingWeightEquation
    (fun hprod =>
      let hpos := productScaleZpositive_of_sliceTransform hprod haff
      let hfull :=
        finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
          hhm huniq hpos
      finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
        hfull (hrec hprod) hpos)
    (fun hprod => productScaleZpositive_of_sliceTransform hprod haff)

/--
Construction-output package for the pre-entropy interaction-collapse spine.

The fields are not claimed to follow from arbitrary `hfaces`; they are the
coherent product-normalized and blockbridge data produced by the TeX proof
before entropy reduction and Faddeev.
-/
structure PreEntropyReadyFaceScalesStructure (F : PrefFamily.{u}) where
  hfaces : CoherentRelabelingFaceScalesStructure F
  product_normalized_representatives :
    FiniteProductNormalizedSelectedRepresentativesFor hfaces
  cross_prior_blockbridge :
    FinitePreUniversalCrossPriorBlockBridgeFor hfaces
  product_quasi_additivity :
    FiniteProductQuasiAdditivityForFaceScales hfaces
  left_slice_affine_transform :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces
  coordinate_value :
    FiniteCoordinateSupportFaceValueIdentificationFor hfaces
  coordinate_scale :
    FiniteCoordinateSupportFaceScaleIdentificationFor hfaces
  block_reveal_chain :
    ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
      FinitePreUniversalBlockRevealChainRuleFor hfaces hprod
  universal_singleton :
    FiniteUniversalScaleSingletonNormalizationFor hfaces

namespace PreEntropyReadyFaceScalesStructure

theorem selectedRelabeling
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FiniteSelectedPosteriorValueRelabelingFor hready.hfaces :=
  finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
    hready.product_normalized_representatives

theorem blockRevealValue
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FinitePreUniversalBlockRevealValueFor hready.hfaces :=
  finitePreUniversalBlockRevealValue_of_crossPriorBlockBridge
    hready.cross_prior_blockbridge

theorem productScaleZPositive
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FiniteProductScaleZPositiveAssumptionsFor hready.hfaces
      hready.product_quasi_additivity :=
  productScaleZpositive_of_sliceTransform
    hready.product_quasi_additivity hready.left_slice_affine_transform

theorem groupingGR
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FinitePreUniversalGroupingGRFor hready.hfaces
      hready.product_quasi_additivity :=
  finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
    hready.blockRevealValue
    (hready.block_reveal_chain hready.product_quasi_additivity)

theorem groupingW
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hready.hfaces
      hready.product_quasi_additivity :=
  finitePreUniversalGroupingWeightRecursion_of_GR
    hready.groupingGR
    hready.productScaleZPositive

theorem twoGroupingWeight
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FiniteProductTwoGroupingWeightEquationAssumptionsFor hready.hfaces
      hready.product_quasi_additivity :=
  finiteProductTwoGroupingWeightEquation_of_weightRecursion_selected
    hready.selectedRelabeling
    hready.groupingW
    hready.productScaleZPositive

theorem groupingReferenceWeight
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FiniteProductGroupingReferenceWeightAssumptionsFor hready.hfaces
      hready.product_quasi_additivity :=
  productGroupingReferenceWeight_of_twoGroupingWeightEquation
    hready.twoGroupingWeight
    hready.productScaleZPositive

theorem groupingEquation
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F) :
    FiniteProductGroupingEquationAssumptionsFor hready.hfaces :=
  finiteProductGroupingEquation_of_weightRecursion_selected
    hready.selectedRelabeling
    hready.left_slice_affine_transform
    (fun hprod =>
      finitePreUniversalGroupingWeightRecursion_of_GR
        (finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
          hready.blockRevealValue
          (hready.block_reveal_chain hprod))
        (productScaleZpositive_of_sliceTransform hprod
          hready.left_slice_affine_transform))

theorem fullSupportRelabeling
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    FiniteFullSupportSelectedPosteriorValueRelabelingFor hready.hfaces :=
  finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
    hhm huniq hready.productScaleZPositive

theorem twoGroupingWeight_fullSupportRelabeling
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    FiniteProductTwoGroupingWeightEquationAssumptionsFor hready.hfaces
      hready.product_quasi_additivity :=
  finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
    (hready.fullSupportRelabeling hhm huniq)
    hready.groupingW
    hready.productScaleZPositive

theorem groupingReferenceWeight_fullSupportRelabeling
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    FiniteProductGroupingReferenceWeightAssumptionsFor hready.hfaces
      hready.product_quasi_additivity :=
  productGroupingReferenceWeight_of_twoGroupingWeightEquation
    (hready.twoGroupingWeight_fullSupportRelabeling hhm huniq)
    hready.productScaleZPositive

theorem groupingEquation_fullSupportRelabeling
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    FiniteProductGroupingEquationAssumptionsFor hready.hfaces :=
  finiteProductGroupingEquation_of_weightRecursion_fullSupportRelabeling
    hhm huniq
    hready.left_slice_affine_transform
    (fun hprod =>
      finitePreUniversalGroupingWeightRecursion_of_GR
        (finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
          hready.blockRevealValue
          (hready.block_reveal_chain hprod))
        (productScaleZpositive_of_sliceTransform hprod
          hready.left_slice_affine_transform))

end PreEntropyReadyFaceScalesStructure

/--
Interaction collapse and universal scale from a pre-entropy-ready face-scale
construction object.

The constructor does not assert that product normalization or blockbridge follow
from arbitrary `hfaces`; they are fields of `hready`, matching the TeX proof
order.
-/
noncomputable def InteractionCollapseUniversalScale_of_preEntropyReady
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (_hhm : FinitePosteriorIntegralRepresentationData.{u})
    (_huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hready.hfaces
    hready.product_quasi_additivity
    (coordinateSupportFaceValueTransport_of_identification hready.coordinate_value)
    (coordinateSupportFaceScaleTransport_of_identification hready.coordinate_scale)
    (productGroupingWeightConstant_of_reference hready.groupingReferenceWeight)
    hready.universal_singleton
    hax

/--
Interaction collapse and universal scale from the pre-entropy-ready object, but
with the grouping/reference-weight route using the proved full-support
relabeling theorem instead of `product_normalized_representatives`.
-/
noncomputable def InteractionCollapseUniversalScale_of_preEntropyReady_fullSupportRelabeling
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hready.hfaces
    hready.product_quasi_additivity
    (coordinateSupportFaceValueTransport_of_identification hready.coordinate_value)
    (coordinateSupportFaceScaleTransport_of_identification hready.coordinate_scale)
    (productGroupingWeightConstant_of_reference
      (hready.groupingReferenceWeight_fullSupportRelabeling hhm huniq))
    hready.universal_singleton
    hax

end TraceableAgency
