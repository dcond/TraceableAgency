/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.SliceAffine

namespace TraceableAgency

universe u

/-- Reconstruct the old normalized-current-coefficients package from the
reference-gauge transform law plus the normalization that the current
representatives are already the post-gauge representatives. -/
theorem positiveGaugeChoice_of_representativeGaugeNormalization
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hgauge : FiniteProductReferenceGaugeTransformAssumptions.{u} hpair)
    (hcurrent :
      FiniteCurrentRepresentativesGaugeNormalizedAssumptions.{u} hpair hgauge) :
    FiniteProductPositiveGaugeChoiceAssumptions.{u} hpair where
  current_leftCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    rw [hcurrent.current_leftCoeff_eq_transformed F hax hs q r hq hr]
    exact hgauge.transformed_leftCoeff_normalized F hax hs q r hq hr
  current_rightCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    rw [hcurrent.current_rightCoeff_eq_transformed F hax hs q r hq hr]
    exact hgauge.transformed_rightCoeff_normalized F hax hs q r hq hr

/--
**Product Gauge Normalization Assumptions**

Compatibility package for paper Step 3 of Lemma `coherentnorm`. Stage 10T no
longer keeps this as the live external assumption; it is derived from the
coefficient associativity equations, the swap/rho reciprocity equation, and the
remaining gauge-choice bridge saying the current representatives have already
been put in the normalized positive gauge.
-/
structure FiniteProductGaugeNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_associativity : FiniteProductLinearCoeffAssociativityAssumptions.{v} hpair
  coeff_swap : FiniteProductLinearCoeffSwapAssumptions.{v} hpair
  gauge_choice : FiniteProductPositiveGaugeChoiceAssumptions.{v} hpair

/-- Reassemble the Step 3 normalization compatibility package from the
coefficient associativity, swap/rho, and normalized-gauge-choice components. -/
theorem productGaugeNormalization_of_step3_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hassoc : FiniteProductLinearCoeffAssociativityAssumptions.{u} hpair)
    (hswap : FiniteProductLinearCoeffSwapAssumptions.{u} hpair)
    (hgauge : FiniteProductPositiveGaugeChoiceAssumptions.{u} hpair) :
    FiniteProductGaugeNormalizationAssumptions.{u} hpair where
  coeff_associativity := hassoc
  coeff_swap := hswap
  gauge_choice := hgauge

/-- Compatibility accessor for the old normalized-left-coefficient field. -/
theorem FiniteProductGaugeNormalizationAssumptions.leftCoeff_normalized
    {hpair : FinitePairwiseProductBilinearAssumptions.{u}}
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hpair.leftCoeff F hax hs q r = 1 :=
  hnorm.gauge_choice.current_leftCoeff_normalized F hax hs q r hq hr

/-- Compatibility accessor for the old normalized-right-coefficient field. -/
theorem FiniteProductGaugeNormalizationAssumptions.rightCoeff_normalized
    {hpair : FinitePairwiseProductBilinearAssumptions.{u}}
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hpair.rightCoeff F hax hs q r = 1 :=
  hnorm.gauge_choice.current_rightCoeff_normalized F hax hs q r hq hr

/-- Pairwise product bilinear formula after the Step 3 gauge normalization,
with both linear coefficients rewritten to one. -/
theorem product_pair_bilinear_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        hs.branch_agg.value_rep.V r (experimentOfChannel R) +
        hpair.interactionCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) *
          hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
  rw [hnorm.leftCoeff_normalized F hax hs q r hq hr]
  rw [hnorm.rightCoeff_normalized F hax hs q r hq hr]
  ring

/--
**Product Interaction Universality Assumptions**

Paper Steps 4-5 of Lemma `coherentnorm`: after the linear coefficients have
been normalized, the remaining interaction coefficient is independent of the
two finite factors, with singleton factors included by compatibility.
-/
structure FiniteProductInteractionUniversalityAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  kappa : ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F → ℝ
  interactionCoeff_common :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.interactionCoeff F hax hs q r = kappa F hax hs

/-- A fixed nondegenerate reference action type for Step 4 common-κ
arguments. -/
abbrev interactionReferenceType : Type u := ULift.{u, 0} Bool

/-- The fixed full-support reference prior used to name the common interaction
coefficient. -/
noncomputable def interactionReferencePrior : Dist interactionReferenceType :=
  Dist.uniform

theorem interactionReferencePrior_fullSupport :
    interactionReferencePrior.FullSupport :=
  Dist.uniform_fullSupport (A := interactionReferenceType)

theorem interactionReference_not_subsingleton :
    ¬ Subsingleton interactionReferenceType := by
  intro hsub
  have htf : (true : Bool) = false := by
    exact congrArg ULift.down
      (Subsingleton.elim
        (ULift.up true : interactionReferenceType)
        (ULift.up false : interactionReferenceType))
  cases htf

/-- The interaction coefficient at the fixed reference prior. -/
noncomputable def interactionReferenceKappa
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F) : ℝ :=
  hpair.interactionCoeff F hax hs
    interactionReferencePrior interactionReferencePrior

/--
Paper Step 4 interaction associativity equations K1-K4 for nondegenerate
factors after the Step 3 gauge normalization. K4 is recorded for faithfulness
even though the common-κ extraction below only needs K1-K3.
-/
structure FiniteProductInteractionAssociativityAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  interaction_assoc_xy :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs q (prodDist r s)
  interaction_assoc_xz :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs q (prodDist r s)
  interaction_assoc_yz :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs r s
  interaction_assoc_xyz :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs (prodDist q r) s *
          hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs q (prodDist r s) *
          hpair.interactionCoeff F hax hs r s

/-- K1 from normalized triple-product expansions. Set the third coordinate to
no information, vary the first two coordinates, and cancel the nonzero pure-trace
witness values. -/
theorem interaction_assoc_xy_from_triple_of_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (_hC : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.interactionCoeff F hax hs q r =
      hpair.interactionCoeff F hax hs q (prodDist r s) := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hxne :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hA
  have hyne :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hB
  have hxyne :
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) *
        hs.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    mul_ne_zero hxne hyne
  have hval := htriple
    (P := (Channel.idChannel : Channel A A))
    (R := (Channel.idChannel : Channel B B))
    (S := (Channel.uninformativeChannelU C))
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      (prodDist q r) s hqr hsupp
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B))
      (Channel.uninformativeChannelU C)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q (prodDist r s) hq hrs
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C))] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q r hq hr (Channel.idChannel : Channel A A)
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      r s hr hsupp (Channel.idChannel : Channel B B)
      (Channel.uninformativeChannelU C)] at hval
  rw [hs.branch_agg.value_rep.zero_normalized s hsupp] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hxyne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- K2 from normalized triple-product expansions. Set the middle coordinate to
no information, vary the first and third coordinates, and cancel the nonzero
pure-trace witness values. -/
theorem interaction_assoc_xz_from_triple_of_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
    (hC : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.interactionCoeff F hax hs (prodDist q r) s =
      hpair.interactionCoeff F hax hs q (prodDist r s) := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hxne :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hA
  have hzne :
      hs.branch_agg.value_rep.V s
        (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs s hsupp hC
  have hxzne :
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) *
        hs.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    mul_ne_zero hxne hzne
  have hval := htriple
    (P := (Channel.idChannel : Channel A A))
    (R := (Channel.uninformativeChannelU B))
    (S := (Channel.idChannel : Channel C C))
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      (prodDist q r) s hqr hsupp
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B))
      (Channel.idChannel : Channel C C)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q (prodDist r s) hq hrs
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C))] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q r hq hr (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      r s hr hsupp (Channel.uninformativeChannelU B)
      (Channel.idChannel : Channel C C)] at hval
  rw [hs.branch_agg.value_rep.zero_normalized r hr] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hxzne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- K3 from normalized triple-product expansions. Set the first coordinate to
no information, vary the last two coordinates, and cancel the nonzero pure-trace
witness values. -/
theorem interaction_assoc_yz_from_triple_of_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (_hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (hC : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.interactionCoeff F hax hs (prodDist q r) s =
      hpair.interactionCoeff F hax hs r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hyne :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hB
  have hzne :
      hs.branch_agg.value_rep.V s
        (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs s hsupp hC
  have hyzne :
      hs.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) *
        hs.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    mul_ne_zero hyne hzne
  have hval := htriple
    (P := (Channel.uninformativeChannelU A))
    (R := (Channel.idChannel : Channel B B))
    (S := (Channel.idChannel : Channel C C))
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      (prodDist q r) s hqr hsupp
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B))
      (Channel.idChannel : Channel C C)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C))] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q r hq hr (Channel.uninformativeChannelU A)
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      r s hr hsupp (Channel.idChannel : Channel B B)
      (Channel.idChannel : Channel C C)] at hval
  rw [hs.branch_agg.value_rep.zero_normalized q hq] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hyzne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- K4 follows algebraically from K1-K3. -/
theorem interaction_assoc_xyz_from_interaction_assoc_xyz_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hxy :
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs q (prodDist r s))
    (hxz :
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs q (prodDist r s))
    (hyz :
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs r s) :
    hpair.interactionCoeff F hax hs (prodDist q r) s *
        hpair.interactionCoeff F hax hs q r =
      hpair.interactionCoeff F hax hs q (prodDist r s) *
        hpair.interactionCoeff F hax hs r s := by
  rw [hxz, hxy, ← hyz, hxz]

/-- Derive the full nondegenerate K1-K4 interaction associativity package from
value-level triple-product associativity and the Step 3 normalized product
gauge. -/
theorem productInteractionAssociativity_of_tripleValue_and_gaugeNormalization
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (htriple : FiniteTripleProductValueAssociativityAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair) :
    FiniteProductInteractionAssociativityAssumptions.{u} hpair where
  interaction_assoc_xy := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_xy_from_triple_of_normalized hpair hnorm
      F hax hs q r s hq hr hsupp hA hB hC
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  interaction_assoc_xz := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_xz_from_triple_of_normalized hpair hnorm
      F hax hs q r s hq hr hsupp hA hB hC
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  interaction_assoc_yz := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_yz_from_triple_of_normalized hpair hnorm
      F hax hs q r s hq hr hsupp hA hB hC
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  interaction_assoc_xyz := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_xyz_from_interaction_assoc_xyz_parts
      hpair F hax hs q r s
      (interaction_assoc_xy_from_triple_of_normalized hpair hnorm
        F hax hs q r s hq hr hsupp hA hB hC
        (htriple.triple_value_assoc F hax hs q r s hq hr hsupp))
      (interaction_assoc_xz_from_triple_of_normalized hpair hnorm
        F hax hs q r s hq hr hsupp hA hB hC
        (htriple.triple_value_assoc F hax hs q r s hq hr hsupp))
      (interaction_assoc_yz_from_triple_of_normalized hpair hnorm
        F hax hs q r s hq hr hsupp hA hB hC
        (htriple.triple_value_assoc F hax hs q r s hq hr hsupp))

/-- Paper Step 4 coordinate-swap symmetry for the interaction coefficient in
nondegenerate factors after Step 3 normalization. -/
structure FiniteProductInteractionSwapAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  interaction_swap :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs r q

/-- Nondegenerate interaction coefficient symmetry from product swap after the
Step 3 gauge normalization. Evaluate both coordinates at full revelation, use
product-swap value equality, expand both sides with the normalized pairwise
formula, and cancel the nonzero pure-trace witness values. -/
theorem interactionCoeff_eq_swapped_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.interactionCoeff F hax hs q r =
      hpair.interactionCoeff F hax hs r q := by
  have hxne :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hA
  have hyne :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hB
  have hxyne :
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) *
        hs.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    mul_ne_zero hxne hyne
  have hval :=
    product_value_swap_eq_of_value_relabeling hrelV F hax hs q r
      (Channel.idChannel : Channel A A) (Channel.idChannel : Channel B B)
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs q r hq hr
      (Channel.idChannel : Channel A A)
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs r q hr hq
      (Channel.idChannel : Channel B B)
      (Channel.idChannel : Channel A A)] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hxyne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Derive the nondegenerate interaction-swap package from coherent product
value relabeling and the Step 3 gauge-normalized product formula. -/
theorem productInteractionSwap_of_valueSwap_and_gaugeNormalization
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair) :
    FiniteProductInteractionSwapAssumptions.{u} hpair where
  interaction_swap := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr hA hB
    exact interactionCoeff_eq_swapped_of_value_swap_nondegenerate
      hrelV hpair hnorm F hax hs q r hq hr hA hB

/--
Singleton interaction normalization. If one factor is singleton, the product
interaction term is multiplied by a zero coordinate value, so the coefficient
is not identified by value variation. The paper handles singleton factors in
Step 5 using extra product-bijection/gauge reasoning; Lean isolates the
remaining normalization directly against the reference common coefficient.
-/
structure FiniteSingletonInteractionCoefficientNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  interactionCoeff_eq_reference_of_subsingleton_left :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton A →
      hpair.interactionCoeff F hax hs q r =
        interactionReferenceKappa hpair F hax hs
  interactionCoeff_eq_reference_of_subsingleton_right :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton B →
      hpair.interactionCoeff F hax hs q r =
        interactionReferenceKappa hpair F hax hs

/-- Nondegenerate common-κ extraction from the K1-K3 associativity equations.
The swap symmetry is part of the paper Step 4 split and is carried by the
reassembly theorem, but K1-K3 already suffice for this algebraic extraction
once the lifted-Bool reference prior is fixed. -/
theorem interactionCoeff_eq_reference_of_assoc_nondegenerate
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hassoc : FiniteProductInteractionAssociativityAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.interactionCoeff F hax hs q r =
      interactionReferenceKappa hpair F hax hs := by
  let q₀ : Dist interactionReferenceType := interactionReferencePrior
  have hq₀ : q₀.FullSupport := interactionReferencePrior_fullSupport
  have hRef : ¬ Subsingleton interactionReferenceType :=
    interactionReference_not_subsingleton
  have h_qr_to_r_ref :
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs r q₀ := by
    calc
      hpair.interactionCoeff F hax hs q r
          = hpair.interactionCoeff F hax hs q (prodDist r q₀) :=
            hassoc.interaction_assoc_xy F hax hs q r q₀ hq hr hq₀ hA hB hRef
      _ = hpair.interactionCoeff F hax hs (prodDist q r) q₀ :=
            (hassoc.interaction_assoc_xz F hax hs q r q₀ hq hr hq₀ hA hB hRef).symm
      _ = hpair.interactionCoeff F hax hs r q₀ :=
            hassoc.interaction_assoc_yz F hax hs q r q₀ hq hr hq₀ hA hB hRef
  have h_r_ref_to_ref_ref :
      hpair.interactionCoeff F hax hs r q₀ =
        hpair.interactionCoeff F hax hs q₀ q₀ := by
    calc
      hpair.interactionCoeff F hax hs r q₀
          = hpair.interactionCoeff F hax hs r (prodDist q₀ q₀) :=
            hassoc.interaction_assoc_xy F hax hs r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
      _ = hpair.interactionCoeff F hax hs (prodDist r q₀) q₀ :=
            (hassoc.interaction_assoc_xz F hax hs r q₀ q₀ hr hq₀ hq₀ hB hRef hRef).symm
      _ = hpair.interactionCoeff F hax hs q₀ q₀ :=
            hassoc.interaction_assoc_yz F hax hs r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
  calc
    hpair.interactionCoeff F hax hs q r
        = hpair.interactionCoeff F hax hs r q₀ := h_qr_to_r_ref
    _ = interactionReferenceKappa hpair F hax hs := by
        simpa [interactionReferenceKappa, q₀] using h_r_ref_to_ref_ref

/-- Reconstruct the old common-κ package from nondegenerate Step 4
associativity, nondegenerate swap symmetry, and the singleton interaction
normalization. -/
noncomputable def interactionUniversality_of_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hassoc : FiniteProductInteractionAssociativityAssumptions.{u} hpair)
    (_hswap : FiniteProductInteractionSwapAssumptions.{u} hpair)
    (hsingle :
      FiniteSingletonInteractionCoefficientNormalizationAssumptions.{u} hpair) :
    FiniteProductInteractionUniversalityAssumptions.{u} hpair where
  kappa := interactionReferenceKappa hpair
  interactionCoeff_common := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    by_cases hsubA : Subsingleton A
    · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_left
        F hax hs q r hq hr hsubA
    · by_cases hsubB : Subsingleton B
      · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_right
          F hax hs q r hq hr hsubB
      · exact interactionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc F hax hs q r hq hr hsubA hsubB

/-- Reassemble the old gauge coherence package from the Step 3 normalization
and Steps 4-5 interaction-universality components. -/
def productGaugeCoherence_of_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (huniv : FiniteProductInteractionUniversalityAssumptions.{u} hpair) :
    FiniteProductGaugeCoherenceAssumptions.{u} hpair where
  kappa := huniv.kappa
  leftCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hnorm.leftCoeff_normalized F hax hs q r hq hr
  rightCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hnorm.rightCoeff_normalized F hax hs q r hq hr
  interactionCoeff_common := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact huniv.interactionCoeff_common F hax hs q r hq hr

/--
**Coherent Product Quasi-Additivity Assumptions**

Compatibility package for the conclusion of paper Lemma `coherentnorm`.
Stage 10E no longer keeps this as the live external assumption; it is derived
from pairwise bilinear product form plus coherent gauge/κ normalization.

`V_{q⊗r}(P⊗R) = V_q(P) + V_r(R) + κ V_q(P)V_r(R)`.

Stage 10D uses only the `δ`-factor consequences of this formula, where one
factor is no-information and hence has value zero.
-/
structure FiniteCoherentProductQuasiAdditivityAssumptions.{v} where
  kappa : ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F → ℝ
  product_quasi_add :
    ∀ (F : PrefFamily.{v})
      (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        hs.branch_agg.value_rep.V r (experimentOfChannel R) +
        kappa F hax hs *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Assemble the coherent product quasi-additivity conclusion from the two
paper-level cardinal components isolated in Stage 10E. -/
def coherentProductQuasiAdditivity_of_pairwiseBilinear_and_gauge
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hgauge : FiniteProductGaugeCoherenceAssumptions.{u} hpair) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} where
  kappa := hgauge.kappa
  product_quasi_add := by
    intro F hax hs A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
    rw [hgauge.leftCoeff_normalized F hax hs q r hq hr]
    rw [hgauge.rightCoeff_normalized F hax hs q r hq hr]
    rw [hgauge.interactionCoeff_common F hax hs q r hq hr]
    ring

/-- Direct coherentnorm reassembly from the decomposed Step 3 normalization
and Steps 4-5 interaction-universality components. This is the same
quasi-additivity package as `coherentProductQuasiAdditivity_of_pairwiseBilinear_and_gauge`,
but exposes that the monolithic gauge package is no longer a live assumption. -/
def coherentProductQuasiAdditivity_of_gaugeNormalization_and_interaction
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (huniv : FiniteProductInteractionUniversalityAssumptions.{u} hpair) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} :=
  coherentProductQuasiAdditivity_of_pairwiseBilinear_and_gauge hpair
    (productGaugeCoherence_of_parts hpair hnorm huniv)

/--
**Product-Lift Value Assumptions**

Paper-specific value identities from Lemma blockbridge:
`F_{q⊗r}(μ_{q,P} ⊗ δ_r) = F_q(μ_{q,P})` and
`F_{q⊗r}(δ_q ⊗ μ_{r,Q}) = F_r(μ_{r,Q})`.

These are the special `δ`-factor consequences of coherent product
quasi-additivity and zero normalization.
-/
structure FiniteProductLiftValueAssumptions.{v} where
  left_lift_value :
    ∀ (F : PrefFamily.{v})
      (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B O : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) =
        hs.branch_agg.value_rep.V q (experimentOfChannel P)
  right_lift_value :
    ∀ (F : PrefFamily.{v})
      (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (Q : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) Q)) =
        hs.branch_agg.value_rep.V r (experimentOfChannel Q)

/-- Left product-lift value identity from coherent product quasi-additivity
and zero normalization of the no-information background. -/
theorem left_lift_value_of_coherentProductQuasiAdditivity
    (hcoh : FiniteCoherentProductQuasiAdditivityAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) P)) =
      hs.branch_agg.value_rep.V q (experimentOfChannel P) := by
  rw [leftProductLiftChannel]
  rw [hcoh.product_quasi_add F hax hs q r hq hr P (Channel.uninformativeChannelU B)]
  rw [hs.branch_agg.value_rep.zero_normalized r hr]
  ring

/-- Right product-lift value identity from coherent product quasi-additivity
and zero normalization of the no-information background. -/
theorem right_lift_value_of_coherentProductQuasiAdditivity
    (hcoh : FiniteCoherentProductQuasiAdditivityAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (Q : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) Q)) =
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) := by
  rw [rightProductLiftChannel]
  rw [hcoh.product_quasi_add F hax hs q r hq hr (Channel.uninformativeChannelU A) Q]
  rw [hs.branch_agg.value_rep.zero_normalized q hq]
  ring

/-- Package the two product-lift value identities derived from coherent
product quasi-additivity. -/
theorem productLiftValue_of_coherentProductQuasiAdditivity
    (hcoh : FiniteCoherentProductQuasiAdditivityAssumptions.{u}) :
    FiniteProductLiftValueAssumptions.{u} where
  left_lift_value := by
    intro F hax hs
    exact left_lift_value_of_coherentProductQuasiAdditivity hcoh F hax hs
  right_lift_value := by
    intro F hax hs
    exact right_lift_value_of_coherentProductQuasiAdditivity hcoh F hax hs

/--
Assemble the unscaled full-support blockbridge from product-lift value
identification, same-prior value representation, and the product-block transfer
proved from main-text A5--A7.
-/
theorem unscaled_cross_prior_block_rep_of_product_parts
    (hvalue : FiniteProductLiftValueAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) := by
  have htransfer' :=
    product_block_transfer_of_A5_A3 F hax q r hq hr P Q
  have hrep :=
    productLiftedComparison_represents F hs q r hq hr P Q
  have hleft :=
    hvalue.left_lift_value F hax hs q r hq hr P
  have hright :=
    hvalue.right_lift_value F hax hs q r hq hr Q
  have hrep' :
      ProductLiftedComparison F q r P Q ↔
        hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel Q) := by
    simpa [hleft, hright] using hrep
  exact htransfer'.trans hrep'

/--
**Finite Cross-Prior Block Assumptions**

External assumptions for the paper's unscaled full-support cross-prior
blockbridge, after internalizing the product-to-block transfer from main-text A5--A7
and the derived value-order coordinate-independence consequence. What remains
external is split into the paper's cardinal coherent-product pieces and the
remaining HM/affine/product bridges: posterior-law value affinity, first-slice
classical affine-utility uniqueness, second-coordinate intercept affine
uniqueness, slope identification, and coherent
gauge/κ normalization. Public-mix posterior-law mixture, product-public-mix
posterior-law compatibility, product-slice public-mix affinity, and cardinal
base-value nonconstancy are now derived/internal; the pure-trace experiment-pair
strictness bridge is now derived from structural relabeling/block-swap
plumbing; singleton first-slice handling and product-slice intercept
identification are also derived internally. The left-slice affine package,
pairwise bilinear form, coherent product formula, and product-lift value
identities are derived from these parts by setting one factor to the
zero-normalized no-information experiment:

1. `V_{q⊗r}(P ⊗ U_B) = V_q(P)`;
2. `V_{q⊗r}(U_A ⊗ Q) = V_r(Q)`.

The same-prior product comparison itself is proved internally from
`PosteriorValueRepresentation.represents_block_comparisons`.
-/
structure FiniteCrossPriorBlockAssumptions.{v} where
  posterior_law_affinity : FinitePosteriorLawValueAffineAssumptions.{v}
  classical_affine_uniqueness : ClassicalAffineUtilityUniquenessAssumptions.{v}
  intercept_uniqueness : ClassicalSecondCoordinateAffineUniquenessAssumptions.{v}
  slope_uniqueness : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{v}
    (productLeftSliceAffine_of_affineUniqueness
      (affineSliceUniqueness_of_parts
        (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
        (product_left_slice_publicMix_affine_of_posterior_affinity
          (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
          productPublicMixPosteriorLaw_of_structural)
        (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
        singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
  posterior_value_relabeling : FinitePosteriorValueRelabelingAssumptions.{v}
  singleton_coeff_gauge :
    FiniteSingletonCoefficientGaugeNormalizationAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
  gauge_coeff_swap_singleton :
    FiniteProductLinearCoeffSwapSingletonNormalizationAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
  reference_gauge :
    FiniteProductReferenceGaugeTransformAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
  current_gauge_normalized :
    FiniteCurrentRepresentativesGaugeNormalizedAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
      reference_gauge
  singleton_interaction :
    FiniteSingletonInteractionCoefficientNormalizationAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))

/-- The old Stage 10F left-slice affine compatibility package, derived from
the narrower affine-slice uniqueness assumption. -/
theorem FiniteCrossPriorBlockAssumptions.affine_slice
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteAffineSliceUniquenessAssumptions.{u} :=
  affineSliceUniqueness_of_parts
    (posteriorValueAffine_of_lawAffine_and_publicMixLaw hcross.posterior_law_affinity)
    (product_left_slice_publicMix_affine_of_posterior_affinity
      (posteriorValueAffine_of_lawAffine_and_publicMixLaw hcross.posterior_law_affinity)
      productPublicMixPosteriorLaw_of_structural)
    (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
    singletonSliceAffine_of_singletonCollapse
    hcross.classical_affine_uniqueness

/-- The old Stage 10F left-slice affine compatibility package, derived from the
sharper Stage 10H affine-uniqueness decomposition. -/
noncomputable def FiniteCrossPriorBlockAssumptions.slice_affine
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductLeftSliceAffineAssumptions.{u} :=
  productLeftSliceAffine_of_affineUniqueness hcross.affine_slice

/-- The old Stage 10F intercept package, now derived from second-coordinate
affine uniqueness plus the internal intercept same-order/zero/affinity facts. -/
noncomputable def FiniteCrossPriorBlockAssumptions.slice_intercept
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductSliceInterceptAssumptions.{u} hcross.slice_affine :=
  productSliceIntercept_of_secondCoordinateAffineUniqueness
    hcross.slice_affine hcross.posterior_law_affinity hcross.intercept_uniqueness

/-- The old Stage 10F slope package, now derived from second-coordinate
slope-affine uniqueness. -/
noncomputable def FiniteCrossPriorBlockAssumptions.slice_slope
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductSliceSlopeAssumptions.{u} hcross.slice_affine :=
  productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
    hcross.slice_affine hcross.slope_uniqueness

/-- The pairwise bilinear compatibility package derived from the Stage 10F
slice-affine split assumptions. -/
noncomputable def FiniteCrossPriorBlockAssumptions.pairwise_bilinear
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FinitePairwiseProductBilinearAssumptions.{u} :=
  pairwiseProductBilinear_of_sliceAffine
    hcross.slice_affine hcross.slice_intercept hcross.slice_slope

/-- The singleton coefficient-extraction compatibility package, reconstructed
from the live singleton coefficient gauge normalization. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_singleton
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteTripleProductCoeffExtractionSingletonAssumptions.{u} hcross.pairwise_bilinear :=
  tripleProductCoeffExtractionSingleton_of_gaugeNormalization
    hcross.pairwise_bilinear hcross.singleton_coeff_gauge

/-- The old Stage 10U full coefficient-extraction package, now derived from
the proved nondegenerate C1-C3 extraction lemmas plus the remaining singleton
branches. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_extraction
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteTripleProductCoeffExtractionAssumptions.{u} hcross.pairwise_bilinear :=
  tripleProductCoeffExtraction_of_nondegenerate_and_singleton
    hcross.pairwise_bilinear hcross.gauge_coeff_singleton

/-- The old value-level triple-product associativity package, reconstructed
from coherent value relabeling of the selected posterior representatives. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_triple_value_assoc
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteTripleProductValueAssociativityAssumptions.{u} :=
  tripleProductValueAssociativity_of_value_relabeling
    hcross.posterior_value_relabeling

/-- The old Stage 10T C1-C3 coefficient associativity package, now derived
from value-level triple associativity plus coefficient extraction. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_associativity
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductLinearCoeffAssociativityAssumptions.{u} hcross.pairwise_bilinear :=
  linearCoeffAssociativity_of_triple_parts hcross.pairwise_bilinear
    hcross.gauge_triple_value_assoc hcross.gauge_coeff_extraction

/-- The old Stage 10T coordinate-swap/rho package, now reconstructed from
coherent value relabeling plus the remaining singleton swap normalization. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_swap
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductLinearCoeffSwapAssumptions.{u} hcross.pairwise_bilinear :=
  productLinearCoeffSwap_of_valueSwap_and_singletonNormalization
    hcross.posterior_value_relabeling hcross.pairwise_bilinear
    hcross.gauge_coeff_swap_singleton

/-- The old Stage 10T positive gauge-choice package, now reconstructed from
the reference-gauge transform law plus the normalization that the current
representatives are already the post-gauge representatives. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_choice
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductPositiveGaugeChoiceAssumptions.{u} hcross.pairwise_bilinear :=
  positiveGaugeChoice_of_representativeGaugeNormalization hcross.pairwise_bilinear
    hcross.reference_gauge hcross.current_gauge_normalized

/-- The old Stage 10S Step 3 normalization package, now derived from
coefficient associativity, swap/rho reciprocity, and the normalized gauge
choice. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_normalization
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductGaugeNormalizationAssumptions.{u} hcross.pairwise_bilinear :=
  productGaugeNormalization_of_step3_parts hcross.pairwise_bilinear
    hcross.gauge_coeff_associativity hcross.gauge_coeff_swap hcross.gauge_choice

/-- The Stage 10AB interaction associativity package, derived from
value-level triple associativity and the Step 3 gauge-normalized product
formula. -/
theorem FiniteCrossPriorBlockAssumptions.interaction_assoc
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductInteractionAssociativityAssumptions.{u} hcross.pairwise_bilinear :=
  productInteractionAssociativity_of_tripleValue_and_gaugeNormalization
    hcross.pairwise_bilinear hcross.gauge_triple_value_assoc hcross.gauge_normalization

/-- The Stage 10AC interaction-swap package, derived from coherent product
value relabeling and the Step 3 gauge-normalized product formula. -/
theorem FiniteCrossPriorBlockAssumptions.interaction_swap
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductInteractionSwapAssumptions.{u} hcross.pairwise_bilinear :=
  productInteractionSwap_of_valueSwap_and_gaugeNormalization
    hcross.posterior_value_relabeling hcross.pairwise_bilinear hcross.gauge_normalization

/-- The old Stage 10S interaction-universality package, reconstructed from
the Step 4 nondegenerate interaction associativity equations, interaction swap
symmetry, and the Step 5 singleton interaction normalization. -/
noncomputable def FiniteCrossPriorBlockAssumptions.interaction_universality
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductInteractionUniversalityAssumptions.{u} hcross.pairwise_bilinear :=
  interactionUniversality_of_parts hcross.pairwise_bilinear
    hcross.interaction_assoc hcross.interaction_swap hcross.singleton_interaction

/-- The old Stage 10E gauge package, now derived from the Step 3 linear
normalization and Steps 4-5 interaction-universality components. -/
noncomputable def FiniteCrossPriorBlockAssumptions.coherent_gauge
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductGaugeCoherenceAssumptions.{u} hcross.pairwise_bilinear :=
  productGaugeCoherence_of_parts hcross.pairwise_bilinear
    hcross.gauge_normalization hcross.interaction_universality

/-- The coherent product quasi-additivity compatibility package derived from
the Stage 10E/10F split assumptions. -/
noncomputable def FiniteCrossPriorBlockAssumptions.coherent_product
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} :=
  coherentProductQuasiAdditivity_of_gaugeNormalization_and_interaction
    hcross.pairwise_bilinear hcross.gauge_normalization hcross.interaction_universality

/-- Named Stage 10AE reassembly of paper Lemma `coherentnorm` from the
decomposed HM/coherent-representative interfaces and gauge/singleton
normalizations carried by `FiniteCrossPriorBlockAssumptions`. -/
noncomputable def coherentnorm_of_decomposed_components
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} :=
  hcross.coherent_product

/-- Compatibility theorem exposing the Stage 10A unscaled bridge from the Stage
10C product decomposition. -/
theorem FiniteCrossPriorBlockAssumptions.unscaled_cross_prior_block_rep
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) :=
  unscaled_cross_prior_block_rep_of_product_parts
    (productLiftValue_of_coherentProductQuasiAdditivity hcross.coherent_product)
    F hax hs q r hq hr P Q

end TraceableAgency
