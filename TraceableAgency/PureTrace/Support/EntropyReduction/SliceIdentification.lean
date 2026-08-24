/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.CrossPrior

namespace TraceableAgency

universe u

/-!
## Fable Stage: Selected right-slice coefficient / slope identification

This section discharges the two remaining opaque inputs of the product
representation theorem:

* `ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor` — the
  right-slice intercept `B_{p,r}` identification, and
* `FiniteFaceScaleProductSlopeAffineAssumptionsFor` — the slice-slope affinity
  `α(ν)=A_{p,r}+C_{p,r}y(ν)`.

Both are proved from the single global classical finite affine-utility
uniqueness theorem, derived background same-order, HM public mixtures, and — crucially for the
slope — exact posterior-value relabeling invariance under the product swap
(`Equiv.prodComm`).  This is the Lean form of the paper's coordinate-swap
scalar `d(p,r)` (Paper/appendix_a_pure_trace_v10.tex, Lemma
`pt:lem:coherentnorm`, Step 2).

The slope target is repaired to nondegenerate first coordinate
(`¬ Subsingleton A`): in a singleton first coordinate the base value
`V_q(P) = 0` for every channel, so the slice slope is not value-identified and
the paper's Step 2 explicitly restricts to nondegenerate action sets.  The
degenerate first coordinate is handled downstream in
`faceScaleProductPairwiseBilinearity_of_sliceAffine`, where `V_q(P)=0` makes
both slope terms vanish, so no interaction-collapse content is lost.
-/

/-- On a singleton second coordinate, the product experiment `P ⊗ R` induces the
same posterior law as `P ⊗ U_B`: the singleton `B`-coordinate carries no
information. Mirror of `samePosteriorLawExp_prodChannel_singleton_fst`. -/
theorem samePosteriorLawExp_prodChannel_singleton_snd
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (P : Channel A O) (R : Channel B Y) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU B))) := by
  obtain ⟨b₀⟩ : Nonempty B := inferInstance
  have huniq : ∀ b : B, b = b₀ := fun b => Subsingleton.elim b b₀
  have hr_eq : r b₀ = 1 := by
    have hsum := r.sum_eq_one
    rw [show (∑ b : B, r b) = r b₀ from
      Finset.sum_eq_single b₀ (fun b _ hb => absurd (huniq b) hb)
        (fun h => absurd (Finset.mem_univ b₀) h)] at hsum
    exact hsum
  have hU_val : ∀ (u : PUnit.{u+1}),
      (Channel.uninformativeChannelU B b₀ : Dist PUnit.{u+1}) u = 1 := by
    intro u; cases u; simp [Channel.uninformativeChannelU]
  have hR_sum : (∑ y : Y, (R b₀).prob y) = 1 := (R b₀).sum_eq_one
  intro φ _hcont
  show posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel P R)) φ =
    posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU B))) φ
  simp only [posteriorLawIntegralExp, experimentOfChannel, FiniteExperimentOn.ofChannel,
    FiniteExperimentOn.outcomeMarginal, FiniteExperimentOn.posterior]
  have hmarg_factored : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
      (R b₀).prob y * Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) (o, PUnit.unit) := by
    intro o y
    simp only [Channel.outcomeMarginal_apply]
    have hstep_R : ∀ x : A × B, (prodDist q r) x * (prodChannel P R) x (o, y) =
        (R b₀).prob y * (q x.1 * P x.1 o) := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq b, hr_eq, one_mul]; ring
    have hstep_U : ∀ x : A × B, (prodDist q r) x *
        (prodChannel P (Channel.uninformativeChannelU B)) x (o, PUnit.unit) =
        q x.1 * P x.1 o := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq b, hr_eq, one_mul,
        hU_val, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => hstep_R x), ← Finset.mul_sum,
      Finset.sum_congr rfl (fun x _ => hstep_U x)]
  have hpost_when_pos : ∀ (o : O) (y : Y),
      (R b₀).prob y > 0 →
      Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) (o, PUnit.unit) > 0 →
      Channel.posterior (prodChannel P R) (prodDist q r) (o, y) =
        Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) := by
    intro o y hRy hUo
    have hmarg_P_pos : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) > 0 := by
      rw [hmarg_factored o y]; exact mul_pos hRy hUo
    unfold Channel.posterior
    rw [dif_pos hmarg_P_pos, dif_pos hUo]
    ext ⟨a, b⟩
    simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq b, hr_eq, one_mul,
      hU_val, mul_one]
    rw [show Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
        (R b₀).prob y * Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) from hmarg_factored o y]
    have hRy_ne : (R b₀).prob y ≠ 0 := ne_of_gt hRy
    have hUo_ne : (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) : Dist (O × PUnit.{u+1})).prob (o, PUnit.unit) ≠ 0 := ne_of_gt hUo
    field_simp
  suffices h : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
      (R b₀).prob y *
        (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit))) by
    have hlhs : (∑ oy : O × Y,
        Channel.outcomeMarginal (prodChannel P R) (prodDist q r) oy *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) oy)) =
      ∑ o : O, Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [h]
      simp_rw [← Finset.sum_mul, hR_sum, one_mul]
    have hrhs : (∑ oy : O × PUnit.{u+1},
        Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) oy *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) oy)) =
      ∑ o : O, Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [Finset.univ_unique]
    exact hlhs.trans hrhs.symm
  intro o y
  rcases eq_or_lt_of_le ((R b₀).nonneg y) with hRy | hRy
  · have hmarg0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
      rw [hmarg_factored o y]; simp [hRy.symm]
    simp only [Channel.outcomeMarginal_apply] at hmarg0
    simp [hmarg0, hRy.symm]
  · have hUo_nn : (0 : ℝ) ≤ Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) (o, PUnit.unit) :=
      (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r)).nonneg (o, PUnit.unit)
    rcases eq_or_lt_of_le hUo_nn with hUo | hUo
    · have hmU0 : Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) = 0 := hUo.symm
      have hmP0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
        rw [hmarg_factored o y, hmU0, mul_zero]
      change Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
          φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
        (R b₀).prob y *
          (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
            (prodDist q r) (o, PUnit.unit) *
          φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
            (prodDist q r) (o, PUnit.unit)))
      rw [hmP0, hmU0]; ring
    · rw [hmarg_factored o y, hpost_when_pos o y hRy hUo, mul_assoc]

/-- On a singleton second coordinate, the left-slice intercept vanishes:
`P ⊗ R ∼ P ⊗ U_B ∼ U_A ⊗ U_B`, and the latter has a subsingleton outcome, hence
value zero. -/
theorem faceScaleLeftSliceIntercept_eq_zero_of_subsingleton_snd
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hslice.leftSliceIntercept hax q r R = 0 := by
  rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
    hslice hax q r hq hr R]
  unfold faceScaleProductLeftSliceValue
  -- V_{q⊗r}(U_A ⊗ R) = V_{q⊗r}(U_A ⊗ U_B) = 0 (subsingleton outcome).
  have hsame :=
    samePosteriorLawExp_prodChannel_singleton_snd q r
      (Channel.uninformativeChannelU A) R
  rw [hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
    (prodDist q r)
    (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R))
    (experimentOfChannel
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B)))
    hsame]
  exact V_eq_zero_of_subsingleton_outcome F
    hfaces.branch_result.branch_agg.value_rep
    (prodDist q r) (prodDist_fullSupport q r hq hr)
    (prodChannel (Channel.uninformativeChannelU A)
      (Channel.uninformativeChannelU B))

/-- Face-scale product-swap value equality from coherent value relabeling.

This is the pre-universal analogue of `product_value_swap_eq_of_value_relabeling`,
stated directly against `CoherentRelabelingFaceScalesStructure`. -/
theorem faceScaleProduct_value_swap_eq_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hfaces.branch_result.branch_agg.value_rep.V (prodDist r q)
        (experimentOfChannel (prodChannel R P)) := by
  have hrel :=
    hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
      (Equiv.prodComm A B) (Equiv.prodComm O Y)
      (prodDist q r) (prodChannel P R)
  have hrel' :
      hfaces.branch_result.branch_agg.value_rep.V (prodDist r q)
          (experimentOfChannel (prodChannel R P)) =
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) := by
    simpa [relabelDist_prodComm q r, relabelChannel_prodComm P R] using hrel
  exact hrel'.symm

/-- **Target 1a.** Second-coordinate right-slice intercept identification.

Mirrors `classicalFaceScaleAffineUtilityUniqueness_of_finiteAffineUtility` with
base representative `V_r` and target representative `leftSliceIntercept`.  The
nondegenerate second coordinate uses the single global classical
affine-utility uniqueness theorem; the intercept vanishes at the no-information
channel, so the additive constant is zero.  The singleton second coordinate is
handled by the value-zero collapse: `V_r ≡ 0`, and the supplied same-order
hypothesis forces the intercept constant, equal to its zero value at `U_B`. -/
theorem classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor hslice where
  positive_linear_of_same_order_affine_zero := by
    intro hax A B _ _ _ _ _ _ q r hq hr haffine horder hzero
    classical
    have hbaseAff :=
      (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces).base_value_publicMix_affine
    by_cases hB : Subsingleton B
    · -- Degenerate second coordinate: V_r ≡ 0 and the intercept vanishes.
      haveI : Subsingleton B := hB
      refine ⟨1, one_pos, ?_⟩
      intro Y _ _ R
      have hVzero :
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep r hr R
      rw [faceScaleLeftSliceIntercept_eq_zero_of_subsingleton_snd
        hslice hax q r hq hr R, hVzero, mul_zero]
    · -- Nondegenerate second coordinate: classical affine-utility uniqueness.
      obtain ⟨a, b, ha_pos, htransform⟩ :=
        huniq.positive_affine_transform (A := B)
          (fun {Y} [Fintype Y] [DecidableEq Y] R =>
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R))
          (fun {Y} [Fintype Y] [DecidableEq Y] R =>
            hslice.leftSliceIntercept hax q r R)
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact hbaseAff hax r hr t ht0 ht1 P Q)
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact haffine t ht0 ht1 P Q)
          (faceScaleBaseValueNonconstancy_of_A1 hfaces
            |>.base_value_nonconstant hax r hr hB)
          (by
            intro O _ _ P Q
            exact horder P Q)
      have hb : b = 0 := by
        have h0 := htransform (Channel.uninformativeChannelU B)
        have hbase0 :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel (Channel.uninformativeChannelU B)) = 0 :=
          hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr
        rw [hbase0, mul_zero, zero_add] at h0
        rw [hzero] at h0
        exact h0.symm
      refine ⟨a, ha_pos, ?_⟩
      intro Y _ _ R
      have := htransform R
      rw [hb, add_zero] at this
      exact this

/-- **Target 1b.** Slice-slope affinity in the second-coordinate value.

This is the Lean form of the paper's `α(ν)=A_{p,r}+C_{p,r}y(ν)` (Lemma
coherentnorm, Step 2), proved via the coordinate swap.  For nondegenerate first
coordinate, evaluate the slice-affine identity at full first-coordinate
revelation `id_A`, transport it across `Equiv.prodComm` to the swapped product,
expand the swapped slice, and use intercept positive-linearity on both slices.
Dividing by `H(q) ≠ 0` gives an affine dependence of the slope on `V_r(R)`, with
positive constant coefficient `B_{r,q}`. -/
theorem faceScaleProductSlopeAffine_of_HM_backgroundInertness_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hlin :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice) :
    FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice where
  slope_affine_in_second_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA
    classical
    -- H(q) = V_q(id_A) ≠ 0 for nondegenerate first coordinate.
    have hHq :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    -- Intercept positive-linearity at (q,r) and (r,q).
    obtain ⟨Bqr, _hBqr_pos, hBqr⟩ := hlin.intercept_positive_linear hax q r hq hr
    obtain ⟨Brq, hBrq_pos, hBrq⟩ := hlin.intercept_positive_linear hax r q hr hq
    refine ⟨Brq,
      (hslice.leftSliceSlope hax r q (Channel.idChannel : Channel A A) - Bqr) /
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)),
      hBrq_pos, ?_⟩
    intro Y _ _ R
    -- (1) slice-affine at (q,r) with first channel id_A:
    have h1 :=
      hslice.left_slice_affine hax q r hq hr
        (Channel.idChannel : Channel A A) R
    -- (2) swap value equality: V_{q⊗r}(id_A ⊗ R) = V_{r⊗q}(R ⊗ id_A).
    have h2 :=
      faceScaleProduct_value_swap_eq_of_value_relabeling hrelV hax hfaces
        q r (Channel.idChannel : Channel A A) R
    -- (3) slice-affine at (r,q) with first channel R:
    have h3 :=
      hslice.left_slice_affine hax r q hr hq R
        (Channel.idChannel : Channel A A)
    -- Intercept identifications.
    have hIqr := hBqr R
    have hIrq := hBrq (Channel.idChannel : Channel A A)
    -- Master equation: slope(q,r,R) * H(q) = slope(r,q,id_A) * V_r(R)
    --   + B_{r,q} * H(q) - B_{q,r} * V_r(R).
    have key :
        hslice.leftSliceSlope hax q r R *
            hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel (Channel.idChannel : Channel A A)) =
          hslice.leftSliceSlope hax r q (Channel.idChannel : Channel A A) *
              hfaces.branch_result.branch_agg.value_rep.V r
                (experimentOfChannel R) +
            Brq * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel (Channel.idChannel : Channel A A)) -
            Bqr * hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) := by
      have hchain := h1.symm.trans (h2.trans h3)
      -- hchain : slope(q,r,R)*H(q) + intercept(q,r,R)
      --          = slope(r,q,id_A)*V_r(R) + intercept(r,q,id_A)
      rw [hIqr, hIrq] at hchain
      linarith [hchain]
    have hgoal :
        hslice.leftSliceSlope hax q r R =
          Brq +
            (hslice.leftSliceSlope hax r q (Channel.idChannel : Channel A A) - Bqr) /
              hfaces.branch_result.branch_agg.value_rep.V q
                (experimentOfChannel (Channel.idChannel : Channel A A)) *
              hfaces.branch_result.branch_agg.value_rep.V r
                (experimentOfChannel R) := by
      field_simp
      linear_combination key
    exact hgoal

/-- Fully-closed product representation theorem.

All second-coordinate/slope inputs of `finiteFaceScaleProductRepresentationTheorem_of_HM`
are now discharged internally:

* second-coordinate intercept uniqueness by
  `classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility`
  (HM public mixtures + the single global classical affine-utility theorem);
* slope affinity by `faceScaleProductSlopeAffine_of_HM_backgroundInertness_relabeling`
  (intercept positive-linearity + exact posterior-value relabeling under the
  product swap).

The remaining inputs are the accepted global classical/relabeling assumptions
(`hhm`, `hrelV`), which are the same inputs already used throughout the product
layer. -/
theorem finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces :=
  finiteFaceScaleProductRepresentationTheorem_of_HM_and_coeffExtraction hhm hfaces
    (fun hsingle huniq =>
      classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
        hhm
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
            (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
            (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
            hsingle huniq))
        huniq)
    (fun hsingle huniq =>
      faceScaleProductSlopeAffine_of_HM_backgroundInertness_relabeling hrelV
        (faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
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
          (classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
            hhm
            (faceScaleProductLeftSliceAffine_of_transform
              (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
                hsingle huniq))
            huniq)))

/-- **Fable product-closure interaction-collapse constructor.**

This is the reassembled clean constructor after the Fable stage.  Compared with
`InteractionCollapseUniversalScale_of_totalClosure`:

* the product-representation input is discharged internally by
  `finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling`
  (the slope/second-coordinate content is now proved, not assumed);
* the opaque grouping-equation input is replaced by the repaired, faithful
  two-grouping weight equation `hgroup` plus the positive-slice-slope condition
  `hpos` (paper eqs. (E1)/(E2)/POS), from which the full `κ = 0` cancellation is
  proved by `finiteProductGroupingEquation_of_twoGroupingWeightEquation`.

The remaining inputs are the accepted global classical/relabeling assumptions
(`hhm`, `huniq`, `hrelV`), the accepted normalizations, and the two honest paper
product-grouping primitives (`hgroup`, `hpos`). -/
noncomputable def InteractionCollapseUniversalScale_of_fableProductClosure
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
    (hgroup :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_totalClosure
    hfaces
    (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
      hhm hrelV hfaces)
    hsingle huniq hgauge hrelV hinterSingle hcoordValue hcoordScale
    (finiteProductGroupingEquation_of_twoGroupingWeightEquation hgroup hpos)
    hunivSingle hax

/-- **Targeted final interaction-collapse constructor.**

Compared with `InteractionCollapseUniversalScale_of_fableProductClosure`:

* POS (`FiniteProductScaleZPositiveAssumptionsFor`) is NO LONGER an input — it
  is proved (`productScaleZpositive_of_sliceTransform`): `Z(q)` is identified
  with the calibrated slice-transform slope, which is the positive multiplier of
  a positive affine transform;
* the two-grouping evaluations E1/E2 are NO LONGER an input — they are derived
  (`finiteProductTwoGroupingWeightEquation_of_weightRecursion`) from the sharper
  pre-universal weight recursion (W)
  (`FinitePreUniversalGroupingWeightRecursionAssumptionsFor`), which is now the
  exact remaining product-grouping primitive.

Remaining inputs: the global classical assumptions (`hhm`, `huniq`), the global
cardinal relabeling coherence (`hrelV`), the accepted normalizations, and the
weight recursion (W). -/
noncomputable def InteractionCollapseUniversalScale_of_targetedFinalClosure
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
    (hrec :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_totalClosure
    hfaces
    (finiteFaceScaleProductRepresentationTheorem_of_HM_backgroundInertness_classical_relabeling
      hhm hrelV hfaces)
    hsingle huniq hgauge hrelV hinterSingle hcoordValue hcoordScale
    (finiteProductGroupingEquation_of_weightRecursion hrelV
      (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
        (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
        (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
        (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces)
        hsingle huniq)
      hrec)
    hunivSingle hax

end TraceableAgency
