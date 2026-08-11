/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.EntropyRegularity

namespace TraceableAgency

universe u

/-!
## Stage ER-D: concrete Faddeev-recursion inputs

The legacy recursion-input structures in `Faddeev.lean` quantify over an
arbitrary `EntropyReductionRepresentation`.  The closed pre-entropy route
constructs a specific representation, with `Hfun` definitionally equal to the
full-revelation normalized value.  The declarations below target that concrete
representation rather than strengthening the old public structures.
-/

/-- Entropy reduction produced by the minimal full pre-entropy closure route. -/
noncomputable def entropyReduction_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_interactionCollapse
    (InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax)

/-- Cross-prior block representation produced by the minimal full
pre-entropy closure route and the product-quasi-additive blockbridge. -/
noncomputable def crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_preUniversalBridge
    (finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod)
    hax
    (entropyReduction_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax)
    rfl

/-- Entropy regularity for the minimal full pre-entropy closure route. -/
theorem entropyRegularity_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    EntropyRegularity F
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction :=
  entropyRegularity_of_crossPrior_boundary
    (normalizedValueSupportBoundary_of_cardinalBoundary hcard) hax _ (fun _ => rfl)

/-- The positive support of a block-embedded fibre distribution is equivalent
to the fibre's positive support. -/
noncomputable def blockEmbedSupportEquiv
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (k : K) (q : Dist (Act k)) :
    supportSubtype (blockEmbedDist Act k q) ≃ supportSubtype q where
  toFun b := by
    rcases b with ⟨ka, hb⟩
    rcases ka with ⟨j, a⟩
    have hjk : j = k := by
      by_contra hne
      have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
        blockEmbedDist_apply_ne Act hne q a
      rw [hzero] at hb
      linarith
    subst j
    exact ⟨a, by simpa using hb⟩
  invFun a := ⟨⟨k, a.1⟩, by simpa using a.2⟩
  left_inv b := by
    rcases b with ⟨ka, hb⟩
    rcases ka with ⟨j, a⟩
    have hjk : j = k := by
      by_contra hne
      have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
        blockEmbedDist_apply_ne Act hne q a
      rw [hzero] at hb
      linarith
    subst j
    rfl
  right_inv a := by
    rfl

/-- Support restriction of a block-embedded distribution is the relabeling of
the intrinsic support-restricted fibre distribution. -/
theorem restrict_blockEmbed_eq_relabel_support
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (k : K) (q : Dist (Act k)) :
    (blockEmbedDist Act k q).restrictToSupport =
      Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
        q.restrictToSupport := by
  ext b
  rcases b with ⟨ka, hb⟩
  rcases ka with ⟨j, a⟩
  have hjk : j = k := by
    by_contra hne
    have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
      blockEmbedDist_apply_ne Act hne q a
    rw [hzero] at hb
    linarith
  subst j
  simp [Relabeling.relabelDist, blockEmbedSupportEquiv, Dist.restrictToSupport_apply]

/-- Pointwise formula for pushing a support-face distribution back to the
ambient action type by support inclusion. -/
theorem actionPushforward_supportIncludeKernel_apply
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (t : Dist (supportSubtype q)) (a : A) :
    Channel.actionPushforward t (supportIncludeKernel q) a =
      if h : q a > 0 then t ⟨a, h⟩ else 0 := by
  unfold Channel.actionPushforward supportIncludeKernel
  change (∑ c : supportSubtype q, t c * (Dist.pure c.1) a) =
    if h : q a > 0 then t ⟨a, h⟩ else 0
  by_cases hqa : q a > 0
  · rw [dif_pos hqa]
    let b : supportSubtype q := ⟨a, hqa⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro c _ hc
      have hne : c.1 ≠ a := by
        intro hca
        apply hc
        exact Subtype.ext hca
      rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · rw [dif_neg hqa]
    apply Finset.sum_eq_zero
    intro c _
    have hne : c.1 ≠ a := by
      intro hca
      exact hqa (hca ▸ c.2)
    rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]

/-- **Inclusion pushforward of a signed posterior law.**

A signed law on the support face `supportSubtype r` is pushed to the ambient
action type `A` by precomposing test functions with the support inclusion.  This
is the tangent-space map `i_ι` in the paper's face-scale argument. -/
noncomputable def pushSignedIncl {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (η : PosteriorLawSigned (supportSubtype r)) : PosteriorLawSigned A :=
  fun φ => η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))

/-- The inclusion pushforward preserves the atomic-linear witness: push each
atom's point along the support inclusion. -/
noncomputable def atomicLinear_pushSignedIncl {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    {η : PosteriorLawSigned (supportSubtype r)}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (pushSignedIncl r η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i => Channel.actionPushforward (hη.witness.point i) (supportIncludeKernel r)
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext φ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        φ (Channel.actionPushforward (hη.witness.point i) (supportIncludeKernel r))) =
      η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))
    have h := congrFun hη.eval_eq
      (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- The inclusion pushforward preserves tangency (zero mass, zero barycentre). -/
theorem pushSignedIncl_tangent {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    {η : PosteriorLawSigned (supportSubtype r)}
    (hη : PosteriorLawSigned.AtomicLinear η)
    (htan : PosteriorLawTangent η) :
    PosteriorLawTangent (pushSignedIncl r η) := by
  refine ⟨?_, ?_⟩
  · show η (fun _ => (1:ℝ)) = 0
    exact htan.1
  · intro a
    show η (fun d => (Channel.actionPushforward d (supportIncludeKernel r)) a) = 0
    by_cases ha : r a > 0
    · have heq :
          (fun d : Dist (supportSubtype r) =>
            (Channel.actionPushforward d (supportIncludeKernel r)) a) =
          (fun d : Dist (supportSubtype r) => d ⟨a, ha⟩) := by
        funext d; rw [actionPushforward_supportIncludeKernel_apply, dif_pos ha]
      rw [heq]; exact htan.2 ⟨a, ha⟩
    · have heq :
          (fun d : Dist (supportSubtype r) =>
            (Channel.actionPushforward d (supportIncludeKernel r)) a) =
          (fun _ => (0:ℝ)) := by
        funext d; rw [actionPushforward_supportIncludeKernel_apply, dif_neg ha]
      rw [heq]
      have h := congrFun hη.eval_eq (fun _ => (0:ℝ))
      rw [AtomicPosteriorSignedLaw.eval_apply] at h
      rw [← h]; simp

/-- The support of a support-included distribution is equivalent to the
distribution's intrinsic positive support. -/
noncomputable def supportIncludePushforwardSupportEquiv
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (t : Dist (supportSubtype q)) :
    supportSubtype (Channel.actionPushforward t (supportIncludeKernel q)) ≃
      supportSubtype t where
  toFun b := by
    rcases b with ⟨a, hb⟩
    have hqa : q a > 0 := by
      by_contra hnot
      have happly :=
        actionPushforward_supportIncludeKernel_apply q t a
      rw [happly, dif_neg hnot] at hb
      linarith
    refine ⟨⟨a, hqa⟩, ?_⟩
    have happly :=
      actionPushforward_supportIncludeKernel_apply q t a
    rw [happly, dif_pos hqa] at hb
    exact hb
  invFun b := by
    refine ⟨b.1.1, ?_⟩
    have happly :=
      actionPushforward_supportIncludeKernel_apply q t b.1.1
    rw [happly, dif_pos b.1.2]
    exact b.2
  left_inv b := by
    rcases b with ⟨a, hb⟩
    apply Subtype.ext
    rfl
  right_inv b := by
    rcases b with ⟨a, hb⟩
    apply Subtype.ext
    rfl

/-- Restricting a support-included distribution is the relabeling of the
intrinsic support restriction. -/
theorem restrict_supportInclude_eq_relabel_support
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (t : Dist (supportSubtype q)) :
    (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport =
      Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
        t.restrictToSupport := by
  ext b
  rcases b with ⟨a, hb⟩
  have hqa : q a > 0 := by
    by_contra hnot
    have happly :=
      actionPushforward_supportIncludeKernel_apply q t a
    rw [happly, dif_neg hnot] at hb
    linarith
  simp [Relabeling.relabelDist, supportIncludePushforwardSupportEquiv,
    Dist.restrictToSupport_apply, actionPushforward_supportIncludeKernel_apply,
    hqa]

/-- Full-support fibre block embedding preserves the concrete entropy
candidate of the minimal full pre-entropy closure route. -/
theorem Hfun_blockEmbed_fullSupport_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (k : K) (q : Dist (Act k)) (hq : q.FullSupport) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
        (blockEmbedDist Act k q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun q := by
  change
    hfaces.branch_result.branch_agg.value_rep.V (blockEmbedDist Act k q)
        (experimentOfChannel
          (Channel.idChannel : Channel ((k : K) × Act k) ((k : K) × Act k))) /
      hfaces.branch_result.scale_factorization.scale (blockEmbedDist Act k q)
    =
    hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel
          (Channel.idChannel : Channel (Act k) (Act k))) /
      hfaces.branch_result.scale_factorization.scale q
  rw [hnorm.block_value.block_face_value hax Act k q hq]
  rw [hnorm.block_scale.block_face_scale hax Act k q hq]
  rfl

/-- Full-support relabeling invariance for the concrete entropy candidate
constructed by the minimal full pre-entropy closure route. -/
theorem Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
        (Relabeling.relabelDist e q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun q := by
  have hq' : (Relabeling.relabelDist e q).FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  by_cases hA : Subsingleton A
  · haveI : Subsingleton A := hA
    haveI : Subsingleton B :=
      ⟨fun b₁ b₂ => by
        apply e.symm.injective
        exact Subsingleton.elim (e.symm b₁) (e.symm b₂)⟩
    have hV_left :
        hfaces.branch_result.branch_agg.value_rep.V
            (Relabeling.relabelDist e q)
            (experimentOfChannel
              (Channel.idChannel : Channel B B)) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hfaces.branch_result.branch_agg.value_rep
        (Relabeling.relabelDist e q) hq'
        (Channel.idChannel : Channel B B)
    have hV_right :
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel
              (Channel.idChannel : Channel A A)) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hfaces.branch_result.branch_agg.value_rep q hq
        (Channel.idChannel : Channel A A)
    change
      hfaces.branch_result.branch_agg.value_rep.V
          (Relabeling.relabelDist e q)
          (experimentOfChannel
            (Channel.idChannel : Channel B B)) /
        hfaces.branch_result.scale_factorization.scale
          (Relabeling.relabelDist e q)
      =
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel
            (Channel.idChannel : Channel A A)) /
        hfaces.branch_result.scale_factorization.scale q
    rw [hV_left, hV_right]
    simp
  · have hpos :
        FiniteProductScaleZPositiveAssumptionsFor hfaces hprod :=
      productScaleZpositive_of_sliceTransform hprod haff
    have hfull :
        FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces :=
      finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
        hhm huniq hpos
    have hV :
        fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) =
          fullRevelationValueForFaceScales hfaces q :=
      fullRevelationValueForFaceScales_relabel_eq_fullSupport
        hfull hax e q hq hA
    have hscale :
        hfaces.branch_result.scale_factorization.scale (Relabeling.relabelDist e q) =
          hfaces.branch_result.scale_factorization.scale q := by
      exact
        (InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hnorm hax).scale_coherence.scale_universal
          (Relabeling.relabelDist e q) q hq' hq
    change
      fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) /
        hfaces.branch_result.scale_factorization.scale (Relabeling.relabelDist e q)
      =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q
    rw [hV, hscale]

/-- Embedding a distribution on a support face back into the ambient action
type preserves the concrete entropy candidate of the minimal full pre-entropy
closure route. -/
theorem Hfun_supportInclude_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    ∀ (t : Dist (supportSubtype q)),
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)) =
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun t := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  intro t
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hreg : EntropyRegularity F hcross.entropy_reduction :=
    entropyRegularity_of_fullPreEntropyClosure_minimal
      hcard hfaces hhm huniq hprod haff hnorm hax
  let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
    hfunSupportRestriction_of_boundaryIdentity hsupport hid
  haveI :
      Nonempty (supportSubtype (Channel.actionPushforward t (supportIncludeKernel q))) :=
    supportSubtype_nonempty (Channel.actionPushforward t (supportIncludeKernel q))
  haveI : Nonempty (supportSubtype t) := supportSubtype_nonempty t
  have hleft :
      hcross.entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)) =
        hcross.entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport :=
    hhfun.Hfun_support_restrict F hax hcross hreg
      (Channel.actionPushforward t (supportIncludeKernel q))
  have hright :
      hcross.entropy_reduction.Hfun t =
        hcross.entropy_reduction.Hfun t.restrictToSupport :=
    hhfun.Hfun_support_restrict F hax hcross hreg t
  have hrestrict :
      (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport =
        Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
          t.restrictToSupport :=
    restrict_supportInclude_eq_relabel_support q t
  have hrel :
      hcross.entropy_reduction.Hfun
          (Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
            t.restrictToSupport) =
        hcross.entropy_reduction.Hfun t.restrictToSupport :=
    Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
      hhm huniq haff hnorm hax
      (supportIncludePushforwardSupportEquiv q t).symm t.restrictToSupport
      (Dist.restrictToSupport_fullSupport t)
  calc
    hcross.entropy_reduction.Hfun
        (Channel.actionPushforward t (supportIncludeKernel q))
        = hcross.entropy_reduction.Hfun
            (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport := hleft
    _ = hcross.entropy_reduction.Hfun
          (Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
            t.restrictToSupport) := by rw [hrestrict]
    _ = hcross.entropy_reduction.Hfun t.restrictToSupport := hrel
    _ = hcross.entropy_reduction.Hfun t := hright.symm

/-- Block embedding preserves the concrete entropy candidate of the minimal
full pre-entropy closure route.  Boundary fibres are routed through the single
cardinal support-boundary interface and the support-face relabeling above. -/
theorem Hfun_blockEmbed_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (k : K) (q : Dist (Act k)) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
        (blockEmbedDist Act k q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun q := by
  by_cases hq : q.FullSupport
  · exact Hfun_blockEmbed_fullSupport_of_fullPreEntropyClosure_minimal
      hhm huniq haff hnorm hax Act k q hq
  · let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
      normalizedValueSupportBoundary_of_cardinalBoundary hcard
    let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
      hfunBoundaryIdentity_of_cardinalBoundary hcard
    let hreg : EntropyRegularity F hcross.entropy_reduction :=
      entropyRegularity_of_fullPreEntropyClosure_minimal
        hcard hfaces hhm huniq hprod haff hnorm hax
    let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
      hfunSupportRestriction_of_boundaryIdentity hsupport hid
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    haveI : Nonempty (supportSubtype (blockEmbedDist Act k q)) :=
      supportSubtype_nonempty (blockEmbedDist Act k q)
    have hleft :
        hcross.entropy_reduction.Hfun (blockEmbedDist Act k q) =
          hcross.entropy_reduction.Hfun
            (blockEmbedDist Act k q).restrictToSupport :=
      hhfun.Hfun_support_restrict F hax hcross hreg (blockEmbedDist Act k q)
    have hright :
        hcross.entropy_reduction.Hfun q =
          hcross.entropy_reduction.Hfun q.restrictToSupport :=
      hhfun.Hfun_support_restrict F hax hcross hreg q
    have hrestrict :
        (blockEmbedDist Act k q).restrictToSupport =
          Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
            q.restrictToSupport :=
      restrict_blockEmbed_eq_relabel_support Act k q
    have hrel :
        hcross.entropy_reduction.Hfun
            (Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
              q.restrictToSupport) =
          hcross.entropy_reduction.Hfun q.restrictToSupport :=
      Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
        hhm huniq haff hnorm hax
        (blockEmbedSupportEquiv Act k q).symm q.restrictToSupport
        (Dist.restrictToSupport_fullSupport q)
    calc
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k q)
          = hcross.entropy_reduction.Hfun
              (blockEmbedDist Act k q).restrictToSupport := hleft
      _ = hcross.entropy_reduction.Hfun
            (Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
              q.restrictToSupport) := by rw [hrestrict]
      _ = hcross.entropy_reduction.Hfun q.restrictToSupport := hrel
      _ = hcross.entropy_reduction.Hfun q := hright.symm

/-- Posterior-law integrals are preserved by support restriction for the
concrete entropy candidate of the minimal full pre-entropy closure route. -/
theorem posteriorLawIntegral_supportRestrict_Hfun_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O]
    (P : Channel A O) (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    posteriorLawIntegral q P
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun =
      posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  letI : DecidableEq O := Classical.decEq O
  have hsupport :=
    posteriorLawIntegral_restrictToSupport P q
      (fun d => hcross.entropy_reduction.Hfun d)
  rw [hsupport]
  unfold posteriorLawIntegral
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  exact
    Hfun_supportInclude_of_fullPreEntropyClosure_minimal
      hcard hhm huniq haff hnorm hax q
      (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)

/-- Coarse-reveal entropy reduction for the concrete entropy candidate of the
minimal full pre-entropy closure route. -/
theorem coarseReveal_entropyReduction_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    hcross.entropy_reduction.Hfun (sigmaDist p q) =
      normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
        (coarseRevealChannel Act) +
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
        hcross.entropy_reduction.Hfun := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  let s : Dist ((k : K) × Act k) := sigmaDist p q
  let C : Channel ((k : K) × Act k) K := coarseRevealChannel Act
  by_cases hs : s.FullSupport
  · have hER :=
      hcross.entropy_reduction.value_entropy_reduction s hs C
    have hER' :
        normalizedValue hcross.entropy_reduction.scale_coherence s C =
          hcross.entropy_reduction.Hfun s -
            posteriorLawIntegral s C hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    linarith
  · let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
      normalizedValueSupportBoundary_of_cardinalBoundary hcard
    let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
      hfunBoundaryIdentity_of_cardinalBoundary hcard
    let hreg : EntropyRegularity F hcross.entropy_reduction :=
      entropyRegularity_of_fullPreEntropyClosure_minimal
        hcard hfaces hhm huniq hprod haff hnorm hax
    let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
      hfunSupportRestriction_of_boundaryIdentity hsupport hid
    haveI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
    have hH :
        hcross.entropy_reduction.Hfun s =
          hcross.entropy_reduction.Hfun s.restrictToSupport :=
      hhfun.Hfun_support_restrict F hax hcross hreg s
    have hV :
      normalizedValue hcross.entropy_reduction.scale_coherence s C =
          normalizedValue hcross.entropy_reduction.scale_coherence
            s.restrictToSupport (Channel.restrictToSupport C s) :=
      normalizedValue_support_restrict_of_boundary hsupport F hax hcross C s
    have hI :
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun =
          posteriorLawIntegral s.restrictToSupport (Channel.restrictToSupport C s)
            hcross.entropy_reduction.Hfun :=
      posteriorLawIntegral_supportRestrict_Hfun_of_fullPreEntropyClosure_minimal
        hcard hhm huniq haff hnorm hax C s
    have hER :=
      hcross.entropy_reduction.value_entropy_reduction
        s.restrictToSupport (Dist.restrictToSupport_fullSupport s)
        (Channel.restrictToSupport C s)
    have hER' :
        normalizedValue hcross.entropy_reduction.scale_coherence
            s.restrictToSupport (Channel.restrictToSupport C s) =
          hcross.entropy_reduction.Hfun s.restrictToSupport -
            posteriorLawIntegral s.restrictToSupport
              (Channel.restrictToSupport C s)
              hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    rw [hH, hV, hI]
    linarith

/-- Finite Faddeev recursion for the concrete entropy candidate produced by
the minimal full pre-entropy closure route. -/
theorem satisfiesFiniteFaddeevRecursion_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u} :=
    restrictedCoarseRevealValue_of_cardinalBoundary hcard
  let hreg : EntropyRegularity F hcross.entropy_reduction :=
    entropyRegularity_of_fullPreEntropyClosure_minimal
      hcard hfaces hhm huniq hprod haff hnorm hax
  let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
    hfunSupportRestriction_of_boundaryIdentity hsupport hid
  change SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun
  intro K _ _ _ Act _ _ _ _ p q
  have hER :=
    coarseReveal_entropyReduction_of_fullPreEntropyClosure_minimal
      (hcard := hcard) (hhm := hhm) (huniq := huniq)
      (haff := haff) (hnorm := hnorm) (hax := hax)
      (Act := Act) (p := p) (q := q)
  have hV :=
    coarseReveal_value_eq_Hfun_of_axioms
      hsupport hhfun hrestricted F hax hcross hreg Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) := by
    exact posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k =>
        Hfun_blockEmbed_of_fullPreEntropyClosure_minimal
          (hcard := hcard) (hhm := hhm) (huniq := huniq)
          (haff := haff) (hnorm := hnorm) (hax := hax)
          (Act := Act) (k := k) (q := q k))
  change hcross.entropy_reduction.Hfun (sigmaDist p q) =
    hcross.entropy_reduction.Hfun p +
      ∑ k, p k * hcross.entropy_reduction.Hfun (q k)
  rw [hER, hV, hInt]

/-- `FaddeevRecursionForm` for the concrete entropy candidate produced by the
minimal full pre-entropy closure route. -/
theorem faddeevRecursionForm_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    FaddeevRecursionForm F hcross.entropy_reduction := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  exact
    { regularity :=
        entropyRegularity_of_fullPreEntropyClosure_minimal
          hcard hfaces hhm huniq hprod haff hnorm hax
      grouping_recursion :=
        satisfiesFiniteFaddeevRecursion_of_fullPreEntropyClosure_minimal
          (hcard := hcard) (hhm := hhm) (huniq := huniq)
          (haff := haff) (hnorm := hnorm) (hax := hax) }

/-- `FaddeevEntropyForm` for the concrete entropy candidate produced by the
minimal full pre-entropy closure route.  The only Faddeev/Shannon input is the
classical finite Faddeev theorem interface. -/
noncomputable def FaddeevEntropyForm_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    FaddeevEntropyForm F := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  let hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    faddeevRecursionForm_of_fullPreEntropyClosure_minimal
      (hcard := hcard) (hhm := hhm) (huniq := huniq)
      (haff := haff) (hnorm := hnorm) (hax := hax)
  let hsupport :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hhfun :=
    hfunSupportRestriction_of_boundaryIdentity hsupport hid
  let hstandard :
      FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun :=
    finiteFaddeevStandardHypotheses_of_axioms hax hcross hrecForm
      (fun q =>
        hhfun.Hfun_support_restrict F hax hcross hrecForm.regularity q)
  let hex :=
    hfad.of_standard_hypotheses
      hcross.entropy_reduction.Hfun hstandard
  let alpha := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hH :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        hcross.entropy_reduction.Hfun q = alpha * H(q) :=
    hspec.2
  have hHfun_pos :
      0 < hcross.entropy_reduction.Hfun
        (Dist.uniform (A := ULift.{u, 0} Bool)) :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrecForm
  exact
    { cross_prior := hcross
      alpha := alpha
      alpha_pos :=
        alpha_strict_pos_of_positive_Hfun_witness
          F hax hcross hrecForm hHfun_pos alpha hH
      H_eq_alpha_shannon := hH
      a3_block_equivalence := a3_block_equivalence_of_traceAxioms F hax }

/-- Same Faddeev/Shannon interface as
`FaddeevEntropyForm_of_fullPreEntropyClosure_minimal`, with affine uniqueness
filled by the internal finite uniqueness theorem. -/
noncomputable def FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    FaddeevEntropyForm F :=
  FaddeevEntropyForm_of_fullPreEntropyClosure_minimal
    (hcard := hcard) (hfad := hfad) (hhm := hhm)
    (huniq := classicalFiniteAffineUtilityUniquenessAssumptions)
    (haff := haff) (hnorm := hnorm) (hax := hax)

/-- Full-support MI representation package obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem fullSupportSufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    FullSupportSufficiencyMIPackage F :=
  FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F
    (FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Full-support block MI representation package obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem fullSupportBlockMI_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    FullSupportBlockMI F :=
  FullSupportBlockMI_of_FaddeevEntropyForm F
    (FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Boundary extension for MI representation obtained internally from the
support-restriction theorem and the full-support block MI package. -/
theorem fullSupportMIRepExtendsToBoundary_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    FullSupportMIRepExtendsToBoundary F :=
  FullSupportMIRepExtendsToBoundary_of_supportRestriction F
    (fullSupportBlockMI_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Final sufficiency package obtained from the closed pre-entropy spine,
internal boundary extension, and the classical finite Faddeev theorem
interface. -/
theorem sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    SufficiencyMIPackage F :=
  (fullSupportMIRepExtendsToBoundary_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard := hcard) (hfad := hfad) (hhm := hhm)
    (haff := haff) (hnorm := hnorm) (hax := hax))
    hax
    (fullSupportSufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Final mutual-information representation obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem MIRep_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : PureTraceConditions F) :
    PureTraceMIRepresentation F :=
  MIRep_of_SufficiencyMIPackage F
    (sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Left-slice affine transform for the selected face-scale representative
from HM public-mixture affinity, derived background same-order transport, internal finite
affine-utility uniqueness, and the singleton slice normalization. -/
theorem finiteFaceScaleProductLeftSliceAffineTransform_of_HM
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces :=
  faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
    (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
    (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
    (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
    hsingle
    classicalFiniteAffineUtilityUniquenessAssumptions

/-- Exact boundary-to-positive-support transport for the single value
representative carried by a coherent face-scale structure.  This deliberately
contains no universal quantification over alternative representatives. -/
structure FiniteBoundaryValueSupportReadFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  boundary_value_support :
    ∀ {A O : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (q : Dist A) [Nonempty (supportSubtype q)] (P : Channel A O),
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) =
        hfaces.branch_result.branch_agg.value_rep.V q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q))

/-- Block support-face value transport for the pre-entropy route, stated as a
theorem-style transport input rather than a representative normalization. -/
structure FiniteBlockSupportFaceValueTransportFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_value :
    ∀ (_hax : PureTraceConditions F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.branch_agg.value_rep.V
        (blockEmbedDist Act k q)
        (experimentOfChannel
          (Channel.idChannel : Channel ((k : K) × Act k) ((k : K) × Act k))) =
      fullRevelationValueForFaceScales hfaces q

/-- Block support-face scale transport for the pre-entropy route. -/
structure FiniteBlockSupportFaceScaleTransportFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_scale :
    ∀ (_hax : PureTraceConditions F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.scale_factorization.scale
        (blockEmbedDist Act k q) =
      hfaces.branch_result.scale_factorization.scale q

/-- Block value read on the support face of the embedded block posterior.

The full-revelation continuation is evaluated after restricting the embedded
prior to its positive support and using the identity channel on that support
face.  This is the support-read counterpart of the ambient
`FiniteBlockSupportFaceValueTransportFor`. -/
structure FiniteBlockSupportFaceValueSupportReadFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_value_support :
    ∀ (_hax : PureTraceConditions F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.branch_agg.value_rep.V
        (blockEmbedDist Act k q).restrictToSupport
        (experimentOfChannel
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q)))) =
      fullRevelationValueForFaceScales hfaces q

/-- Block scale read on the support face of the embedded block posterior. -/
structure FiniteBlockSupportFaceScaleSupportReadFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_scale_support :
    ∀ (_hax : PureTraceConditions F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.scale_factorization.scale
        (blockEmbedDist Act k q).restrictToSupport =
      hfaces.branch_result.scale_factorization.scale q

/-- The pre-entropy representative/gauge facts needed by the final constructor,
with normalization terminology removed from the public-facing route. -/
structure PreEntropyRepresentativeGaugeKnownResults
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  coordinate_value :
    FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces
  coordinate_scale :
    FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces
  block_value :
    FiniteBlockSupportFaceValueTransportFor hfaces
  block_scale :
    FiniteBlockSupportFaceScaleTransportFor hfaces
  reference_z :
    FiniteProductReferenceZNormalizationFor hfaces hprod
  universal_singleton :
    FiniteUniversalScaleSingletonNormalizationFor hfaces

theorem coordinateSupportFaceValueIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces) :
    FiniteCoordinateSupportFaceValueIdentificationFor hfaces where
  first_coordinate_face_value := h.first_coordinate_face_value
  second_coordinate_face_value := h.second_coordinate_face_value

theorem coordinateSupportFaceScaleIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces) :
    FiniteCoordinateSupportFaceScaleIdentificationFor hfaces where
  first_coordinate_face_scale := h.first_coordinate_face_scale
  second_coordinate_face_scale := h.second_coordinate_face_scale

theorem blockSupportFaceValueIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteBlockSupportFaceValueTransportFor hfaces) :
    FiniteBlockSupportFaceValueIdentificationFor hfaces where
  block_face_value := h.block_face_value

theorem blockSupportFaceScaleIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteBlockSupportFaceScaleTransportFor hfaces) :
    FiniteBlockSupportFaceScaleIdentificationFor hfaces where
  block_face_scale := h.block_face_scale

theorem universalScaleSingleton_of_normalization
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteUniversalScaleSingletonNormalizationFor hfaces) :
    FiniteUniversalScaleSingletonNormalizationFor hfaces where
  scale_eq_of_subsingleton := h.scale_eq_of_subsingleton

theorem preEntropyRepresentativeGaugeNormalizations_of_knownResults
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (h : PreEntropyRepresentativeGaugeKnownResults hfaces hprod) :
    PreEntropyRepresentativeGaugeNormalizations hfaces hprod where
  coordinate_value :=
    coordinateSupportFaceValueIdentification_of_transport h.coordinate_value
  coordinate_scale :=
    coordinateSupportFaceScaleIdentification_of_transport h.coordinate_scale
  block_value :=
    blockSupportFaceValueIdentification_of_transport h.block_value
  block_scale :=
    blockSupportFaceScaleIdentification_of_transport h.block_scale
  reference_z := h.reference_z
  universal_singleton :=
    universalScaleSingleton_of_normalization h.universal_singleton

/-- Harmless final inputs stated as known transport/normalization results. -/
structure FinalHarmlessKnownResults
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  pre_entropy :
    PreEntropyRepresentativeGaugeKnownResults hfaces hprod

/-- Posterior integral representation supplied by the HM component of the
final interface. -/
noncomputable def posteriorIntegralRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u}) :
    FinitePosteriorIntegralRepresentationAssumptions.{u} :=
  finitePosteriorIntegralRepresentation_of_HM
    (integralRepresentationData_of_FinalHMInterface hhm)

/-- Affine linear-part package supplied by the internally proved posterior
integral representation.  Defining it from the named posterior package keeps
the two downstream views definitionally synchronized without unfolding the
finite construction itself. -/
noncomputable def affineLinearPart_of_FinalHMInterface
    (hhm : FinalHMInterface.{u}) :
    FiniteAffineLinearPartAssumptions.{u} :=
  finiteAffineLinearPartAssumptions_of_integralRepresentation
    (posteriorIntegralRepresentation_of_FinalHMInterface hhm)

/-- Hax-specific singleton branch package whose arbitrary singleton coefficient
is chosen to be the selected branch path scale `β(q,u_A)`.

The value-zero field is still proved from the HM/integral support-face theorem.
The coefficient choice is scale-aware, so it is the right package for removing
the old singleton scale-factorization normalization on the selected branch route. -/
noncomputable def finalHMSingletonScaleNormalizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) :
    FiniteBranchSingletonScaleNormalizationFor F
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  refine
    { singletonCoeff := fun {A} _ _ _ q _ =>
        hpath.branchPathCoeff q (Dist.uniform (A := A))
      singletonCoeff_pos := ?_
      singleton_branch_value_zero := ?_ }
  · intro A _ _ _ q _r hq _hr_singleton
    by_cases hnd :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b
    · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
        hq Dist.uniform_fullSupport hnd
    · have hpath_eq :
          hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hnd]
      rw [hpath_eq]
      exact one_pos
  · intro A O _ _ _ _ _ r hr_singleton P
    change canonicalPosteriorValue
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      r (experimentOfChannel P) = 0
    by_cases hr : r.FullSupport
    · rcases hr_singleton with ⟨a, _ha, huniq⟩
      have hsub : Subsingleton A :=
        ⟨fun x y => (huniq x (hr x)).trans (huniq y (hr y)).symm⟩
      simp [canonicalPosteriorValue, hr, hsub]
    · have hsub : Subsingleton (supportSubtype r) :=
        supportSubtype_subsingleton_of_singleton_support r hr_singleton
      simp [canonicalPosteriorValue, hr, hsub]

/-- The selected singleton coefficient is definitionally the selected branch
path scale to the uniform prior. -/
theorem finalHMSingletonScaleNormalizationFor_coeff
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) :
    (finalHMSingletonScaleNormalizationFor hhm hax).singletonCoeff q r =
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q (Dist.uniform (A := A)) := by
  rfl

/-- Canonical full-revelation normalization makes the selected value
functional exactly covariant under finite action/outcome relabellings. -/
theorem finalSelectedRelabelCovariance_of_canonicalNormalization
    (hhm : FinalHMInterface.{u}) :
    FinalSelectedRelabelCovariance hhm where
  V_relabel_eq := by
    intro F hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    classical
    change canonicalPosteriorValue
        (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
        (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      canonicalPosteriorValue
        (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
        q (experimentOfChannel P)
    exact canonicalPosteriorValue_relabel hax
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      eA eO q P

/-- Relabelling covariance in the only form needed by branch aggregation:
equality after applying an atomic tangent signed posterior law.  This is
representation-independent; in particular it does not assert that an
arbitrarily chosen integral test function is pointwise natural. -/
theorem finalHM_affineLinearPart_relabel_atomic_eval
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (s : Dist A) (hs : s.FullSupport)
    (η : PosteriorLawSigned A)
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    relabelPosteriorLawSigned e η
        ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue
          F (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (Relabeling.relabelDist e s)) =
      η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue
        F (posteriorValueRepresentation_of_FinalHMInterface hhm hax) s) := by
  have h :=
    affineLinearPart_relabel_atomicTangent
      (affineLinearPart_of_FinalHMInterface hhm)
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ((finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq hax)
      e s hs η hηatomic hηtan
  exact h

end TraceableAgency
