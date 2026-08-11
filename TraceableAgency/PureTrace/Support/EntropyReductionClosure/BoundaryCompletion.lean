/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.ProductGauge

namespace TraceableAgency

universe u

open Classical in
/-- Scale completed to the support-face value at nondegenerate boundary priors. -/
noncomputable def wrapScale
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  if (¬ q.FullSupport ∧ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) then
    hs.scale q.restrictToSupport
  else hs.scale q

theorem wrapScale_fullSupport
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    wrapScale hs q = hs.scale q := by
  classical
  simp only [wrapScale]
  rw [if_neg (by rintro ⟨hnf, _⟩; exact hnf hq)]

theorem wrapScale_boundary_nondeg
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnf : ¬ q.FullSupport)
    (hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    wrapScale hs q = hs.scale q.restrictToSupport := by
  classical
  simp only [wrapScale]
  rw [if_pos ⟨hnf, hnd⟩]

theorem wrapScale_singleton
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnd : ¬ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    wrapScale hs q = hs.scale q := by
  classical
  simp only [wrapScale]
  rw [if_neg (by rintro ⟨_, hc⟩; exact hnd hc)]

/-- The boundary-completed scale coherence structure. -/
noncomputable def boundaryCompleteScale
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hs.branch_agg.branchCoeff q r = hs.scale q / hs.scale r.restrictToSupport)
    : ScaleCoherenceStructure F where
  branch_agg := hs.branch_agg
  scale := fun {A} _ _ _ q => wrapScale hs q
  scale_pos := by
    intro A _ _ _ q hq
    rw [wrapScale_fullSupport hs q hq]; exact hs.scale_pos q hq
  scale_universal := by
    intro A B _ _ _ _ _ _ q r hq hr
    rw [wrapScale_fullSupport hs q hq, wrapScale_fullSupport hs r hr]
    exact hs.scale_universal q r hq hr
  branchCoeff_factorization := by
    classical
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ hpos
    set r := Channel.posterior P₁ q o₁ with hrdef
    rw [wrapScale_fullSupport hs q hq]
    by_cases hrfull : r.FullSupport
    · rw [wrapScale_fullSupport hs r hrfull]
      exact hs.branchCoeff_factorization q hq P₁ o₁ hpos
    · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b
      · haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
        obtain ⟨a0, b0, hab0, ha0, hb0⟩ := hnd
        rw [wrapScale_boundary_nondeg hs r hrfull ⟨a0, b0, hab0, ha0, hb0⟩]
        exact hsf q hq r ⟨a0, ha0⟩ ⟨a0, b0, hab0, ha0, hb0⟩ hrfull
      · rw [wrapScale_singleton hs r hnd]
        exact hs.branchCoeff_factorization q hq P₁ o₁ hpos

/-- Field 1 (boundary normalized-value support restriction) proved for the
boundary-completed scale. -/
theorem field1_boundaryComplete
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hs.branch_agg.branchCoeff q r = hs.scale q / hs.scale r.restrictToSupport)
    (hcoh : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) [Nonempty (supportSubtype q)] (d : Dist (supportSubtype q)),
      hint.marginalValue F hs.branch_agg.value_rep q
        (Channel.actionPushforward d (supportIncludeKernel q)) =
        hint.marginalValue F hs.branch_agg.value_rep q.restrictToSupport d)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (hqb : ¬ q.FullSupport) :
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    normalizedValue (boundaryCompleteScale hs hsf) q P =
      normalizedValue (boundaryCompleteScale hs hsf) q.restrictToSupport
        (Channel.restrictToSupport P q) := by
  classical
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hnum : hs.branch_agg.value_rep.V q (experimentOfChannel P) =
      hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) := by
    rw [hint.value_eq_integral F hs.branch_agg.value_rep q (experimentOfChannel P)]
    rw [hint.value_eq_integral F hs.branch_agg.value_rep q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q))]
    rw [posteriorLawIntegralExp_experimentOfChannel]
    rw [posteriorLawIntegral_restrictToSupport P q]
    rw [posteriorLawIntegralExp_experimentOfChannel]
    unfold posteriorLawIntegral
    apply Finset.sum_congr rfl
    intro o _
    congr 1
    exact hcoh q (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)
  change hs.branch_agg.value_rep.V q (experimentOfChannel P) / wrapScale hs q =
      hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) / wrapScale hs q.restrictToSupport
  rw [hnum]
  rw [wrapScale_fullSupport hs q.restrictToSupport (Dist.restrictToSupport_fullSupport q)]
  by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
  · rw [wrapScale_boundary_nondeg hs q hqb hnd]
  · have hss : Subsingleton (supportSubtype q) := by
      rw [subsingleton_iff]
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      by_contra hne
      exact hnd ⟨a, b, fun h => hne (Subtype.ext h), ha, hb⟩
    haveI := hss
    have hz : hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) = 0 :=
      branchValue_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep
        q.restrictToSupport (Dist.restrictToSupport_fullSupport q)
        (Channel.restrictToSupport P q)
    rw [hz, zero_div, zero_div]

/-- Boundary-completed normalized-value transport from exact transport of the
selected value representative.  No pointwise convention on an integral test
function is used. -/
theorem field1_boundaryComplete_of_selectedValue
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
      [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a)
      (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hs.branch_agg.branchCoeff q r =
        hs.scale q / hs.scale r.restrictToSupport)
    (hvalue :
      ∀ {A O : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype O] [DecidableEq O]
        (q : Dist A) [Nonempty (supportSubtype q)] (P : Channel A O),
        hs.branch_agg.value_rep.V q (experimentOfChannel P) =
          hs.branch_agg.value_rep.V q.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport P q)))
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (hqb : ¬ q.FullSupport) :
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    normalizedValue (boundaryCompleteScale hs hsf) q P =
      normalizedValue (boundaryCompleteScale hs hsf) q.restrictToSupport
        (Channel.restrictToSupport P q) := by
  classical
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hnum := hvalue q P
  change hs.branch_agg.value_rep.V q (experimentOfChannel P) /
      wrapScale hs q =
    hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) /
      wrapScale hs q.restrictToSupport
  rw [hnum]
  rw [wrapScale_fullSupport hs q.restrictToSupport
    (Dist.restrictToSupport_fullSupport q)]
  by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
  · rw [wrapScale_boundary_nondeg hs q hqb hnd]
  · have hss : Subsingleton (supportSubtype q) := by
      rw [subsingleton_iff]
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      by_contra hne
      exact hnd ⟨a, b, fun h => hne (Subtype.ext h), ha, hb⟩
    haveI := hss
    have hz : hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) = 0 :=
      branchValue_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep
        q.restrictToSupport (Dist.restrictToSupport_fullSupport q)
        (Channel.restrictToSupport P q)
    rw [hz, zero_div, zero_div]

open Classical in
/-- Boundary-completed chain scale for a coherent face-scale package, before
the final universal-scale field has been proved.  Full-support and singleton
priors keep the original chain scale; nondegenerate boundary priors are read on
their support face. -/
noncomputable def faceSupportReadScale
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  if (¬ q.FullSupport ∧ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) then
    hfaces.branch_result.scale_factorization.scale q.restrictToSupport
  else
    hfaces.branch_result.scale_factorization.scale q

theorem faceSupportReadScale_fullSupport
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    faceSupportReadScale hfaces q =
      hfaces.branch_result.scale_factorization.scale q := by
  classical
  simp only [faceSupportReadScale]
  rw [if_neg (by rintro ⟨hnf, _⟩; exact hnf hq)]

theorem faceSupportReadScale_boundary_nondeg
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnf : ¬ q.FullSupport)
    (hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    faceSupportReadScale hfaces q =
      hfaces.branch_result.scale_factorization.scale q.restrictToSupport := by
  classical
  simp only [faceSupportReadScale]
  rw [if_pos ⟨hnf, hnd⟩]

theorem faceSupportReadScale_singleton
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnd : ¬ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    faceSupportReadScale hfaces q =
      hfaces.branch_result.scale_factorization.scale q := by
  classical
  simp only [faceSupportReadScale]
  rw [if_neg (by rintro ⟨_, hc⟩; exact hnd hc)]

/-- The support-read branch-chain package induced by coherent face scales.

This is not a new arbitrary gauge: it is the WLOG support-face reading of the
same branch aggregation, with the branch-coefficient factorization re-proved
from the already available support-face scale theorem. -/
noncomputable def supportReadBranchChain
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F) :
    BranchChainStructure F where
  branch_agg := hfaces.branch_result.branch_agg
  scale := fun {A} _ _ _ q => faceSupportReadScale hfaces q
  scale_pos := by
    intro A _ _ _ q hq
    rw [faceSupportReadScale_fullSupport hfaces q hq]
    exact hfaces.branch_result.scale_factorization.scale_pos q hq
  branchCoeff_factorization := by
    classical
    intro A O _ _ _ _ _ q hq P o hpos
    set r := Channel.posterior P q o with hrdef
    rw [faceSupportReadScale_fullSupport hfaces q hq]
    by_cases hrfull : r.FullSupport
    · rw [faceSupportReadScale_fullSupport hfaces r hrfull]
      exact hfaces.branch_result.scale_factorization.branchCoeff_factorization
        q hq P o hpos
    · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b
      · haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
        obtain ⟨a0, b0, hab0, ha0, hb0⟩ := hnd
        rw [faceSupportReadScale_boundary_nondeg hfaces r hrfull
          ⟨a0, b0, hab0, ha0, hb0⟩]
        exact hfaces.support_face_scale_eq q hq r ⟨a0, ha0⟩
          ⟨a0, b0, hab0, ha0, hb0⟩ hrfull
      · rw [faceSupportReadScale_singleton hfaces r hnd]
        exact hfaces.branch_result.scale_factorization.branchCoeff_factorization
          q hq P o hpos

/-- Normalized values for the support-read branch chain are unchanged by
restricting a boundary prior to its positive support.  The numerator equality
is the HM/posterior-integral support-face theorem; the denominator equality is
the support-read scale definition. -/
theorem branchNormalizedValue_supportRead_restrictToSupport
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (hqb : ¬ q.FullSupport) :
    branchNormalizedValue (supportReadBranchChain hfaces) q P =
      branchNormalizedValue (supportReadBranchChain hfaces)
        q.restrictToSupport (Channel.restrictToSupport P q) := by
  classical
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hnum := hboundaryValue.boundary_value_support q P
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) /
        faceSupportReadScale hfaces q =
      hfaces.branch_result.branch_agg.value_rep.V q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q)) /
        faceSupportReadScale hfaces q.restrictToSupport
  rw [hnum]
  rw [faceSupportReadScale_fullSupport hfaces q.restrictToSupport
    (Dist.restrictToSupport_fullSupport q)]
  by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
  · rw [faceSupportReadScale_boundary_nondeg hfaces q hqb hnd]
  · have hss : Subsingleton (supportSubtype q) := by
      rw [subsingleton_iff]
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      by_contra hne
      exact hnd ⟨a, b, fun h => hne (Subtype.ext h), ha, hb⟩
    haveI := hss
    have hz : hfaces.branch_result.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) = 0 :=
      branchValue_channel_eq_zero_of_subsingleton F
        hfaces.branch_result.branch_agg.value_rep
        q.restrictToSupport (Dist.restrictToSupport_fullSupport q)
        (Channel.restrictToSupport P q)
    rw [hz, zero_div, zero_div]

/-- First-coordinate continuation value for the support-read branch chain.

The posterior after revealing `a` is ambient-boundary, but the normalized
continuation is evaluated by first restricting that posterior to its support
face. -/
theorem first_coordinate_supportRead_branchNormalizedValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (a : A) :
    branchNormalizedValue (supportReadBranchChain hfaces)
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (productSecondRevealChannel (A := A) (B := B)) =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r := by
  classical
  have ha : 0 < q a := hq a
  have hpost :
      Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a =
        prodDist (Dist.pure a) r :=
    posterior_productFirstRevealChannel_prodDist_of_pos q r a ha
  have hnotfull : ¬ (prodDist (Dist.pure a) r).FullSupport := by
    intro hfs
    haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    rcases exists_ne a with ⟨a', ha'⟩
    have hp := hfs (a', Classical.arbitrary B)
    rw [prodDist_apply_pair,
      Dist.pure_apply_ne a a' ha', zero_mul] at hp
    exact lt_irrefl 0 hp
  have hrestrict :=
    branchNormalizedValue_supportRead_restrictToSupport
      hfaces hboundaryValue (productSecondRevealChannel (A := A) (B := B))
      (prodDist (Dist.pure a) r) hnotfull
  have hv := hvalue.first_coordinate_face_value_support
    hax q r hq hr hA hB a
  have hs := hscale.first_coordinate_face_scale_support
    hax q r hq hr hA hB a
  rw [hpost] at hv
  rw [hpost] at hs
  rw [hpost]
  rw [hrestrict]
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (prodDist (Dist.pure a) r).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productSecondRevealChannel (A := A) (B := B))
            (prodDist (Dist.pure a) r))) /
        faceSupportReadScale hfaces (prodDist (Dist.pure a) r).restrictToSupport =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r
  rw [faceSupportReadScale_fullSupport hfaces
    (prodDist (Dist.pure a) r).restrictToSupport
    (Dist.restrictToSupport_fullSupport (prodDist (Dist.pure a) r))]
  rw [hv, hs]

/-- Second-coordinate continuation value for the support-read branch chain. -/
theorem second_coordinate_supportRead_branchNormalizedValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (b : B) :
    branchNormalizedValue (supportReadBranchChain hfaces)
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (productFirstRevealChannel (A := A) (B := B)) =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q := by
  classical
  have hb : 0 < r b := hr b
  have hpost :
      Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b =
        prodDist q (Dist.pure b) :=
    posterior_productSecondRevealChannel_prodDist_of_pos q r b hb
  have hnotfull : ¬ (prodDist q (Dist.pure b)).FullSupport := by
    intro hfs
    haveI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
    rcases exists_ne b with ⟨b', hb'⟩
    have hp := hfs (Classical.arbitrary A, b')
    rw [prodDist_apply_pair,
      Dist.pure_apply_ne b b' hb', mul_zero] at hp
    exact lt_irrefl 0 hp
  have hrestrict :=
    branchNormalizedValue_supportRead_restrictToSupport
      hfaces hboundaryValue (productFirstRevealChannel (A := A) (B := B))
      (prodDist q (Dist.pure b)) hnotfull
  have hv := hvalue.second_coordinate_face_value_support
    hax q r hq hr hA hB b
  have hs := hscale.second_coordinate_face_scale_support
    hax q r hq hr hA hB b
  rw [hpost] at hv
  rw [hpost] at hs
  rw [hpost]
  rw [hrestrict]
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (prodDist q (Dist.pure b)).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productFirstRevealChannel (A := A) (B := B))
            (prodDist q (Dist.pure b)))) /
        faceSupportReadScale hfaces (prodDist q (Dist.pure b)).restrictToSupport =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q
  rw [faceSupportReadScale_fullSupport hfaces
    (prodDist q (Dist.pure b)).restrictToSupport
    (Dist.restrictToSupport_fullSupport (prodDist q (Dist.pure b)))]
  rw [hv, hs]

/-- Sequential full-revelation normalized chain rule with coordinate
continuations read on support faces.

This is the corrected replacement for the old ambient coordinate-continuation
route: no equality of ambient boundary scales such as
`scale (pure a ⊗ r) = scale r` is used. -/
theorem sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hvalueSupport : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hscaleSupport : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces) :
    FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces where
  normalized_chain_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    classical
    let hchainSR := supportReadBranchChain hfaces
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hvalue :=
      coordinateRevealValueTransport_of_marginal_and_swap
        (coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
          hfaces hprod)
        (coordinateSwapFullRevelationValueTransport_of_posteriorLaw hfaces)
    have hchain :=
      branchNormalizedValue_seqCompose_of_chain hchainSR
        (prodDist q r) hprod_full
        (productFirstRevealChannel (A := A) (B := B))
        (fun _ => productSecondRevealChannel (A := A) (B := B))
    have hseq_left :
        branchNormalizedValue hchainSR (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              fun _ => productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productFirstThenSecondReveal_eq_idChannel]
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (Channel.idChannel : Channel (A × B) (A × B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rfl
    have hfirst :
        branchNormalizedValue hchainSR (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (productFirstRevealChannel (A := A) (B := B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rw [hvalue.first_reveal_value hax q r hq hr hA hB]
    have hcontsum :
        ∑ a : A,
            Channel.outcomeMarginal
                (productFirstRevealChannel (A := A) (B := B))
                (prodDist q r) a *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productFirstRevealChannel (A := A) (B := B))
                  (prodDist q r) a)
                (productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r := by
      calc
        ∑ a : A,
            Channel.outcomeMarginal
                (productFirstRevealChannel (A := A) (B := B))
                (prodDist q r) a *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productFirstRevealChannel (A := A) (B := B))
                  (prodDist q r) a)
                (productSecondRevealChannel (A := A) (B := B))
            =
          ∑ a : A, q a *
            (fullRevelationValueForFaceScales hfaces r /
              hfaces.branch_result.scale_factorization.scale r) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [outcomeMarginal_productFirstRevealChannel_prodDist]
            rw [first_coordinate_supportRead_branchNormalizedValue
              hboundaryValue hvalueSupport hscaleSupport hax
              q r hq hr hA hB a]
        _ =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r := by
            rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hchainSR (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              fun _ => productSecondRevealChannel (A := A) (B := B)) :=
            hseq_left.symm
      _ =
        branchNormalizedValue hchainSR (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) +
          ∑ a : A,
            Channel.outcomeMarginal
                (productFirstRevealChannel (A := A) (B := B))
                (prodDist q r) a *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productFirstRevealChannel (A := A) (B := B))
                  (prodDist q r) a)
                (productSecondRevealChannel (A := A) (B := B)) := hchain
      _ =
        fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r := by
            rw [hfirst, hcontsum]
  normalized_chain_right := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    classical
    let hchainSR := supportReadBranchChain hfaces
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hvalue :=
      coordinateRevealValueTransport_of_marginal_and_swap
        (coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
          hfaces hprod)
        (coordinateSwapFullRevelationValueTransport_of_posteriorLaw hfaces)
    have hchain :=
      branchNormalizedValue_seqCompose_of_chain hchainSR
        (prodDist q r) hprod_full
        (productSecondRevealChannel (A := A) (B := B))
        (fun _ => productFirstRevealChannel (A := A) (B := B))
    have hseq_right :
        branchNormalizedValue hchainSR (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              fun _ => productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productSecondThenFirstReveal_eq_swapReveal]
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (productSwapRevealChannel (A := A) (B := B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rw [hvalue.swap_full_revelation_value hax q r hq hr hA hB]
    have hsecond :
        branchNormalizedValue hchainSR (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (productSecondRevealChannel (A := A) (B := B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rw [hvalue.second_reveal_value hax q r hq hr hA hB]
    have hcontsum :
        ∑ b : B,
            Channel.outcomeMarginal
                (productSecondRevealChannel (A := A) (B := B))
                (prodDist q r) b *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productSecondRevealChannel (A := A) (B := B))
                  (prodDist q r) b)
                (productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q := by
      calc
        ∑ b : B,
            Channel.outcomeMarginal
                (productSecondRevealChannel (A := A) (B := B))
                (prodDist q r) b *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productSecondRevealChannel (A := A) (B := B))
                  (prodDist q r) b)
                (productFirstRevealChannel (A := A) (B := B))
            =
          ∑ b : B, r b *
            (fullRevelationValueForFaceScales hfaces q /
              hfaces.branch_result.scale_factorization.scale q) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [outcomeMarginal_productSecondRevealChannel_prodDist]
            rw [second_coordinate_supportRead_branchNormalizedValue
              hboundaryValue hvalueSupport hscaleSupport hax
              q r hq hr hA hB b]
        _ =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q := by
            rw [← Finset.sum_mul, r.sum_eq_one, one_mul]
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hchainSR (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              fun _ => productFirstRevealChannel (A := A) (B := B)) :=
            hseq_right.symm
      _ =
        branchNormalizedValue hchainSR (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) +
          ∑ b : B,
            Channel.outcomeMarginal
                (productSecondRevealChannel (A := A) (B := B))
                (prodDist q r) b *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productSecondRevealChannel (A := A) (B := B))
                  (prodDist q r) b)
                (productFirstRevealChannel (A := A) (B := B)) := hchain
      _ =
        fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q := by
            rw [hsecond, hcontsum]

/-- Block-embedded continuation value for the support-read branch chain. -/
theorem block_supportRead_branchNormalizedValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hax : PureTraceConditions F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (hK : ¬ Subsingleton K)
    (k : K) (q : Dist (Act k)) (hq : q.FullSupport) :
    branchNormalizedValue (supportReadBranchChain hfaces)
        (blockEmbedDist Act k q)
        (Channel.idChannel : Channel ((k : K) × Act k) ((k : K) × Act k)) =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q := by
  classical
  let SigmaAct : Type u := (k : K) × Act k
  have hnotfull : ¬ (blockEmbedDist Act k q).FullSupport := by
    intro hfs
    haveI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hK
    rcases exists_ne k with ⟨j, hj⟩
    let a : Act j := Classical.choice inferInstance
    have hp := hfs (⟨j, a⟩ : SigmaAct)
    have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
      blockEmbedDist_apply_ne Act hj q a
    rw [hzero] at hp
    exact lt_irrefl 0 hp
  have hrestrict :=
    branchNormalizedValue_supportRead_restrictToSupport
      hfaces hboundaryValue
      (Channel.idChannel : Channel SigmaAct SigmaAct)
      (blockEmbedDist Act k q) hnotfull
  have hcollapse :
      branchNormalizedValue (supportReadBranchChain hfaces)
          (blockEmbedDist Act k q).restrictToSupport
          (Channel.restrictToSupport
            (Channel.idChannel : Channel SigmaAct SigmaAct)
            (blockEmbedDist Act k q)) =
        branchNormalizedValue (supportReadBranchChain hfaces)
          (blockEmbedDist Act k q).restrictToSupport
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q))) := by
    have hV :=
      (supportReadBranchChain hfaces).branch_agg.value_rep.respects_same_posterior_law
        (blockEmbedDist Act k q).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (Channel.idChannel : Channel SigmaAct SigmaAct)
            (blockEmbedDist Act k q)))
        (experimentOfChannel
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q))))
        (samePosteriorLaw_restrict_idChannel_idSupport (blockEmbedDist Act k q))
    simpa [branchNormalizedValue] using congrArg
      (fun x => x /
        (supportReadBranchChain hfaces).scale
          (blockEmbedDist Act k q).restrictToSupport) hV
  have hv := hvalue.block_face_value_support hax Act k q hq
  have hs := hscale.block_face_scale_support hax Act k q hq
  rw [hrestrict, hcollapse]
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (blockEmbedDist Act k q).restrictToSupport
        (experimentOfChannel
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q)))) /
        faceSupportReadScale hfaces (blockEmbedDist Act k q).restrictToSupport =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q
  rw [faceSupportReadScale_fullSupport hfaces
    (blockEmbedDist Act k q).restrictToSupport
    (Dist.restrictToSupport_fullSupport (blockEmbedDist Act k q))]
  rw [hv, hs]

/-- Pre-universal block-reveal chain rule with embedded block posteriors read
on their support faces. -/
theorem preUniversalBlockRevealChainRule_of_branchChain_supportRead_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalBlockRevealChainRuleFor hfaces hprod where
  block_reveal_chain := by
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
    rw [hbranchScale, hscaleToZ]
  reference_Z_eq_one := href.reference_Z_eq_one

end TraceableAgency
