/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.BoundaryTransport

namespace TraceableAgency

universe u

/-- **R2a: prior-independence of the boundary embedding defect.**

For a fixed boundary posterior `r` and two full-support ambient priors `q, q'`,
the boundary coefficients satisfy
`boundaryCoeff q r · branchPathCoeff q' q = boundaryCoeff q' r`.
Equivalently `boundaryCoeff q r / scale q` is independent of `q` (paper: the
embedding defect `K(ι)` does not depend on the ambient prior).  The proof uses
the support-face marginal-value transport (which pins each `boundaryCoeff`), the
full-support tangent-scalar relation applied to the *pushed* support-face tangent
(`pushSignedIncl`), and cancellation of the A1-nonzero support-face tangent.  It
does **not** use the cross-prior block bridge, so the defect is definable
non-circularly. -/
theorem boundaryCoeff_qIndep_of_FinalHM
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      ).boundaryCoeff q r *
      (branchPathTangentScalarStructure_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q' q =
    (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      ).boundaryCoeff q' r := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
    with hfaith_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
    with hpath_def
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hint_def
  set hboundary := branchBoundaryFaceScale_of_faithfulAssumptions hfaith with hbdef
  have hrs_fs : (r.restrictToSupport).FullSupport := Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h; exact hab (congrArg Subtype.val h)
    · rw [Dist.restrictToSupport_apply]; exact ha
    · rw [Dist.restrictToSupport_apply]; exact hb
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hfaith.linear_part F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have htrans := hbranchData.marginal_value.support_face_marginalValue_scalar
  have hTq := htrans F hax hV q r hq hrn hrnd hrb η hηtan
  have hTq' := htrans F hax hV q' r hq' hrn hrnd hrb η hηtan
  have hpush_atomic := atomicLinear_pushSignedIncl r hηatomic
  have hpush_tan := pushSignedIncl_tangent r hηatomic hηtan
  have hrel := hpath.linear_part_scalar_relation_on_tangent q' q hq' hq
    (by obtain ⟨a, b, hab, _, _⟩ := hrnd; exact ⟨a, b, hab, hq a, hq b⟩)
    (pushSignedIncl r η) hpush_atomic hpush_tan
  have hLq : hfaith.linear_part.linearPart F hV q (pushSignedIncl r η) =
      hboundary.boundaryCoeff q r * η (hint.marginalValue F hV r.restrictToSupport) := hTq
  have hLq' : hfaith.linear_part.linearPart F hV q' (pushSignedIncl r η) =
      hboundary.boundaryCoeff q' r * η (hint.marginalValue F hV r.restrictToSupport) := hTq'
  rw [hLq, hLq'] at hrel
  have hLnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  have hstep : hboundary.boundaryCoeff q' r * η (hint.marginalValue F hV r.restrictToSupport) =
      (hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q) *
        η (hint.marginalValue F hV r.restrictToSupport) := by
    rw [hrel]; ring
  have hcancel := mul_right_cancel₀ hLnz hstep
  linarith [hcancel]

/-- Selected prior-independence of the boundary embedding defect. -/
theorem boundaryCoeff_qIndep_of_FinalHMFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q r *
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q' q =
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q' r := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  change hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q =
    hboundary.boundaryCoeff q' r
  have hrs_fs : (r.restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h
      exact hab (congrArg Subtype.val h)
    · rw [Dist.restrictToSupport_apply]
      exact ha
    · rw [Dist.restrictToSupport_apply]
      exact hb
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have htrans := hbranchData.marginal_value.support_face_marginalValue_scalar
  have hTq := htrans F hax hV q r hq hrn hrnd hrb η hηtan
  have hTq' := htrans F hax hV q' r hq' hrn hrnd hrb η hηtan
  have hpush_atomic := atomicLinear_pushSignedIncl r hηatomic
  have hpush_tan := pushSignedIncl_tangent r hηatomic hηtan
  have hrel := hpath.linear_part_scalar_relation_on_tangent q' q hq' hq
    (by obtain ⟨a, b, hab, _, _⟩ := hrnd; exact ⟨a, b, hab, hq a, hq b⟩)
    (pushSignedIncl r η) hpush_atomic hpush_tan
  have hLq : hlin.linearPart F hV q (pushSignedIncl r η) =
      hboundary.boundaryCoeff q r * η (hint.marginalValue F hV r.restrictToSupport) := hTq
  have hLq' : hlin.linearPart F hV q' (pushSignedIncl r η) =
      hboundary.boundaryCoeff q' r * η (hint.marginalValue F hV r.restrictToSupport) := hTq'
  rw [hLq, hLq'] at hrel
  have hLnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  have hstep :
      hboundary.boundaryCoeff q' r *
          η (hint.marginalValue F hV r.restrictToSupport) =
        (hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q) *
          η (hint.marginalValue F hV r.restrictToSupport) := by
    rw [hrel]
    ring
  have hcancel := mul_right_cancel₀ hLnz hstep
  linarith [hcancel]

/-- Selected prior-independence of the boundary embedding defect, using only
the atomic support-face marginal transport theorem. -/
theorem boundaryCoeff_qIndep_of_FinalHMAtomicFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q r *
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q' q =
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q' r := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  change hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q =
    hboundary.boundaryCoeff q' r
  have hrs_fs : (r.restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h
      exact hab (congrArg Subtype.val h)
    · rw [Dist.restrictToSupport_apply]
      exact ha
    · rw [Dist.restrictToSupport_apply]
      exact hb
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have hTq :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := A) q r hq hrn hrnd hrb η hηatomic hηtan
  have hTq' :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := A) q' r hq' hrn hrnd hrb η hηatomic hηtan
  have hpush_atomic := atomicLinear_pushSignedIncl r hηatomic
  have hpush_tan := pushSignedIncl_tangent r hηatomic hηtan
  have hrel := hpath.linear_part_scalar_relation_on_tangent q' q hq' hq
    (by obtain ⟨a, b, hab, _, _⟩ := hrnd; exact ⟨a, b, hab, hq a, hq b⟩)
    (pushSignedIncl r η) hpush_atomic hpush_tan
  have hLq : hlin.linearPart F hV q (pushSignedIncl r η) =
      hboundary.boundaryCoeff q r *
        η (hint.marginalValue F hV r.restrictToSupport) := hTq
  have hLq' : hlin.linearPart F hV q' (pushSignedIncl r η) =
      hboundary.boundaryCoeff q' r *
        η (hint.marginalValue F hV r.restrictToSupport) := hTq'
  rw [hLq, hLq'] at hrel
  have hLnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  have hstep :
      hboundary.boundaryCoeff q' r *
          η (hint.marginalValue F hV r.restrictToSupport) =
        (hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q) *
          η (hint.marginalValue F hV r.restrictToSupport) := by
    rw [hrel]
    ring
  have hcancel := mul_right_cancel₀ hLnz hstep
  linarith [hcancel]

/-- Selected branch scale for the atomic boundary coefficient.

For full-support priors it agrees with the usual path-to-uniform scale.  For
nondegenerate boundary priors it is the inverse of the internally constructed
uniform-to-face boundary coefficient; singleton/degenerate priors retain the
harmless normalization `1`. -/
noncomputable def selectedAtomicBranchScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hb :=
    boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
  exact
    if hq : q.FullSupport then
      hpath.branchPathCoeff q (Dist.uniform (A := A))
    else if hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b then
      1 / hb.boundaryCoeff (Dist.uniform (A := A)) q
    else
      1

theorem selectedAtomicBranchScaleFor_fullSupport
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    selectedAtomicBranchScaleFor hhm hax hbranchData q =
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q (Dist.uniform (A := A)) := by
  classical
  simp [selectedAtomicBranchScaleFor, hq]

theorem selectedAtomicBranchScaleFor_boundary
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    selectedAtomicBranchScaleFor hhm hax hbranchData r =
      1 /
        (boundaryFaceScale_of_coefficientScaleNormalization
          hbranchData.boundary_coeff
        ).boundaryCoeff (Dist.uniform (A := A)) r := by
  classical
  simp [selectedAtomicBranchScaleFor, hrb, hrnd]

/-- Full-support positivity of the selected atomic branch scale. -/
theorem selectedAtomicBranchScaleFor_pos
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    0 < selectedAtomicBranchScaleFor hhm hax hbranchData q := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq]
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

/-- Full-support scale factorization for the selected atomic branch scale. -/
noncomputable def atomicFullSupportScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (faithfulBranchAggregationStructure_of_atomicDataFor
        hhm hax hbranchData) where
  scale := fun q => selectedAtomicBranchScaleFor hhm hax hbranchData q
  scale_pos := by
    intro A _ _ _ q hq _hnd
    exact selectedAtomicBranchScaleFor_pos hhm hax hbranchData q hq
  branchCoeff_factorization_fullSupport := by
    intro A _ _ _ q r hq hr hnd
    classical
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      selectedAtomicBranchScaleFor hhm hax hbranchData q /
        selectedAtomicBranchScaleFor hhm hax hbranchData r
    rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq,
      selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData r hr]
    rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
        hpath.branchPathCoeff q r by
      simp [branchCoeffFromTangentRepParts, hr]]
    have hU_nd :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
      obtain ⟨a, b, hab⟩ := hnd
      exact ⟨a, b, hab, Dist.uniform_fullSupport a,
        Dist.uniform_fullSupport b⟩
    have hpos :
        0 < hpath.branchPathCoeff r (Dist.uniform (A := A)) :=
      hpath.branchPathCoeff_pos r (Dist.uniform (A := A))
        hr Dist.uniform_fullSupport hU_nd
    have hcoc :=
      branchCoeffTangentScalar_cocycle_fullSupport
        hlin F hax hV hpath q r (Dist.uniform (A := A))
        hq hr Dist.uniform_fullSupport hnd
    rw [hcoc]
    change hpath.branchPathCoeff q r =
      hpath.branchPathCoeff q r * hpath.branchPathCoeff r (Dist.uniform (A := A)) /
        hpath.branchPathCoeff r (Dist.uniform (A := A))
    field_simp [ne_of_gt hpos]

/-- Boundary scale factorization for the selected atomic branch scale.

The boundary scale is not an extra normalization: for a nondegenerate boundary
posterior `r` it is fixed as the inverse of the internally constructed
uniform-to-face boundary coefficient, and the q-independence theorem identifies
the `q`-boundary coefficient with the full-support path scale. -/
noncomputable def atomicBoundaryScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBranchScaleFactorizationBoundaryTransportAssumptions
      (faithfulBranchAggregationStructure_of_atomicDataFor
        hhm hax hbranchData)
      (atomicFullSupportScaleFor hhm hax hbranchData) where
  branchCoeff_factorization_boundary := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hrnd hrb
    classical
    let r : Dist A := Channel.posterior P₁ q o₁
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    have hrnd_r :
        ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      simpa [r] using hrnd
    have hrb_r : ¬ r.FullSupport := by
      simpa [r] using hrb
    have hrn : ∃ a : A, 0 < r a := by
      rcases hrnd_r with ⟨a, _b, _hab, ha, _hb⟩
      exact ⟨a, ha⟩
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      selectedAtomicBranchScaleFor hhm hax hbranchData q /
        selectedAtomicBranchScaleFor hhm hax hbranchData r
    rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
        hboundary.boundaryCoeff q r by
      unfold branchCoeffFromTangentRepParts
      rw [dif_neg hrb_r]
      rw [dif_pos hrnd_r]]
    rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq,
      selectedAtomicBranchScaleFor_boundary
        hhm hax hbranchData r hrnd_r hrb_r]
    have hbc_pos :
        0 < hboundary.boundaryCoeff (Dist.uniform (A := A)) r :=
      hboundary.boundaryCoeff_pos (Dist.uniform (A := A)) r
        Dist.uniform_fullSupport hrn hrnd_r hrb_r
    have hqi :=
      boundaryCoeff_qIndep_of_FinalHMAtomicFor
        hhm hax hbranchData (Dist.uniform (A := A)) q r
        Dist.uniform_fullSupport hq hrn hrnd_r hrb_r
    rw [← hqi]
    field_simp [ne_of_gt hbc_pos]

/-- Singleton/degenerate scale factorization for the selected atomic branch
scale.

Singleton-support posteriors carry no identified value variation.  The HM
singleton coefficient is therefore fixed to the same full-support path scale,
while the selected atomic scale assigns value `1` to degenerate boundary
posteriors. -/
noncomputable def atomicSingletonScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBranchScaleFactorizationSingletonNormalization
      (faithfulBranchAggregationStructure_of_atomicDataFor
        hhm hax hbranchData)
      (atomicFullSupportScaleFor hhm hax hbranchData) where
  scale_pos_singleton := by
    intro A _ _ _ q hq _hr_singleton
    change 0 < selectedAtomicBranchScaleFor hhm hax hbranchData q
    exact selectedAtomicBranchScaleFor_pos hhm hax hbranchData q hq
  branchCoeff_factorization_singleton := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hsingle_support
    classical
    let r : Dist A := Channel.posterior P₁ q o₁
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    have hnotnd :
        ¬ ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      exact not_nondegenerate_of_singleton_support r
        (by simpa [r] using hsingle_support)
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      selectedAtomicBranchScaleFor hhm hax hbranchData q /
        selectedAtomicBranchScaleFor hhm hax hbranchData r
    by_cases hrfull : r.FullSupport
    · have hsub : Subsingleton A := by
        rcases hsingle_support with ⟨c, _hc, huniq⟩
        refine ⟨?_⟩
        intro a b
        exact (huniq a (hrfull a)).trans
          (huniq b (hrfull b)).symm
      have hU_notnd :
          ¬ ∃ a b : A, a ≠ b ∧
            0 < (Dist.uniform (A := A)) a ∧
            0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hne, _ha, _hb⟩
        exact hne (Subsingleton.elim a b)
      have hpath_qr_one : hpath.branchPathCoeff q r = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, hrfull, dif_pos]
        rw [dif_neg hnotnd]
      have hscale_q_one :
          selectedAtomicBranchScaleFor hhm hax hbranchData q = 1 := by
        rw [selectedAtomicBranchScaleFor_fullSupport
          hhm hax hbranchData q hq]
        change hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      have hscale_r_one :
          selectedAtomicBranchScaleFor hhm hax hbranchData r = 1 := by
        rw [selectedAtomicBranchScaleFor_fullSupport
          hhm hax hbranchData r hrfull]
        change hpath.branchPathCoeff r (Dist.uniform (A := A)) = 1
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hrfull, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
          hpath.branchPathCoeff q r by
        simp [branchCoeffFromTangentRepParts, hrfull]]
      rw [hpath_qr_one, hscale_q_one, hscale_r_one]
      norm_num
    · have hbranch_qr :
          branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
            hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
        unfold branchCoeffFromTangentRepParts
        rw [dif_neg hrfull]
        rw [dif_neg hnotnd]
        simpa [hsingle] using
          finalHMSingletonScaleNormalizationFor_coeff hhm hax q r
      have hscale_r_one :
          selectedAtomicBranchScaleFor hhm hax hbranchData r = 1 := by
        simp [selectedAtomicBranchScaleFor, hrfull, hnotnd]
      rw [hbranch_qr]
      rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq]
      change hpath.branchPathCoeff q (Dist.uniform (A := A)) =
        hpath.branchPathCoeff q (Dist.uniform (A := A)) /
          selectedAtomicBranchScaleFor hhm hax hbranchData r
      rw [hscale_r_one]
      rw [div_one]

/-- Selected faithful branch/cocycle/chain result assembled from the corrected
atomic support-face theorem.

This is the convention-free branch-chain route: its boundary coefficient,
support-face marginal transport, and boundary/singleton scale extensions are all
constructed from `PureTraceConditions` and the HM interface. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransportAtomicFor
      F hax hV hint hpath hboundary hsingle hvalue
      hbranchData.marginal_value
  let hbranch :=
    branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula
  let hcocycle :=
    branchCoeffCocycleFor_of_tangentScalar
      F hax hV hlin hpath hboundary hsingle hformula
  let hfull := atomicFullSupportScaleFor hhm hax hbranchData
  {
    branch_agg := hbranch
    coeff_cocycle := hcocycle
    full_support_scale := hfull
    scale_factorization :=
      branchScaleFactorization_of_fullSupport_boundary_singleton
        hbranch hfull
        (atomicBoundaryScaleFactorizationFor hhm hax hbranchData)
        (atomicSingletonScaleFactorizationFor hhm hax hbranchData)
  }

/-- Relabelling invariance of the selected atomic branch scale on full-support
priors. -/
theorem scaleRelabel_of_FinalHM_covarianceAtomicFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale (Relabeling.relabelDist e q) =
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale q := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  have hscale_eq :
      ∀ (C : Type u) [Fintype C] [DecidableEq C] [Nonempty C]
        (s : Dist C), s.FullSupport →
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
          hhm hax hbranchData
        ).scale_factorization.scale s =
          hpath.branchPathCoeff s (Dist.uniform (A := C)) := by
    intro C _ _ _ s hs
    change selectedAtomicBranchScaleFor hhm hax hbranchData s =
      hpath.branchPathCoeff s (Dist.uniform (A := C))
    exact selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData s hs
  have hqfsB : (Relabeling.relabelDist e q).FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  rw [hscale_eq B (Relabeling.relabelDist e q) hqfsB,
    hscale_eq A q hq]
  have huni :
      Relabeling.relabelDist e (Dist.uniform (A := A)) =
        Dist.uniform (A := B) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply,
      Dist.uniform_apply, Fintype.card_congr e]
  by_cases hA : Subsingleton A
  · have h1A : hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      have hnn :
          ¬ ∃ a b : A, a ≠ b ∧
            0 < (Dist.uniform (A := A)) a ∧
            0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hab, _, _⟩
        exact hab (Subsingleton.elim a b)
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hq, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    have h1B :
        hpath.branchPathCoeff
          (Relabeling.relabelDist e q) (Dist.uniform (A := B)) = 1 := by
      haveI : Subsingleton B := Equiv.subsingleton e.symm
      have hnn :
          ¬ ∃ a b : B, a ≠ b ∧
            0 < (Dist.uniform (A := B)) a ∧
            0 < (Dist.uniform (A := B)) b := by
        rintro ⟨a, b, hab, _, _⟩
        exact hab (Subsingleton.elim a b)
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hqfsB, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    rw [h1B, h1A]
  · have hndU :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
      rw [not_subsingleton_iff_nontrivial] at hA
      obtain ⟨a, b, hab⟩ := hA
      exact ⟨a, b, hab, Dist.uniform_fullSupport a,
        Dist.uniform_fullSupport b⟩
    rw [← huni]
    exact branchPathCoeff_relabel_of_atomic_eval
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm) hax hV
      (by
        intro A' B' O' Y' _ _ _ _ _ _ _ _ _ _ eA eO s P
        change
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              (Relabeling.relabelDist eA s)
              (experimentOfChannel
                (Relabeling.relabelChannel eA eO P)) =
            (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              s (experimentOfChannel P)
        exact
          (finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq
            hax eA eO s P)
      hpath
      e q (Dist.uniform (A := A)) hq Dist.uniform_fullSupport hndU

/-- Positivity of the selected atomic chain scale for every finite prior. -/
theorem faithful_atomic_scale_posFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 < (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale q := by
  classical
  change 0 < selectedAtomicBranchScaleFor hhm hax hbranchData q
  by_cases hq : q.FullSupport
  · exact selectedAtomicBranchScaleFor_pos hhm hax hbranchData q hq
  · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
    · rw [selectedAtomicBranchScaleFor_boundary hhm hax hbranchData q hnd hq]
      have hnonempty : ∃ a : A, 0 < q a := by
        rcases hnd with ⟨a, _b, _hab, ha, _hb⟩
        exact ⟨a, ha⟩
      have hbpos :
          0 <
            (boundaryFaceScale_of_coefficientScaleNormalization
              hbranchData.boundary_coeff
            ).boundaryCoeff (Dist.uniform (A := A)) q :=
        (boundaryFaceScale_of_coefficientScaleNormalization
          hbranchData.boundary_coeff).boundaryCoeff_pos
          (Dist.uniform (A := A)) q Dist.uniform_fullSupport
          hnonempty hnd hq
      exact one_div_pos.mpr hbpos
    · simp [selectedAtomicBranchScaleFor, hq, hnd]

/-- The selected atomic chain scale of a nondegenerate uniform prior is `1`. -/
theorem scale_uniform_eq_oneAtomicFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (hnd : ∃ a b : A, a ≠ b) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale (Dist.uniform (A := A)) = 1 := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  change selectedAtomicBranchScaleFor hhm hax hbranchData
      (Dist.uniform (A := A)) = 1
  rw [selectedAtomicBranchScaleFor_fullSupport
    hhm hax hbranchData (Dist.uniform (A := A))
    Dist.uniform_fullSupport]
  change hpath.branchPathCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) = 1
  have hcoc := branchCoeffTangentScalar_cocycle_fullSupport
    hlin F hax hV hpath
    (Dist.uniform (A := A)) (Dist.uniform (A := A))
    (Dist.uniform (A := A))
    Dist.uniform_fullSupport Dist.uniform_fullSupport Dist.uniform_fullSupport
    hnd
  have hpos :
      0 < hpath.branchPathCoeff
        (Dist.uniform (A := A)) (Dist.uniform (A := A)) := by
    obtain ⟨a, b, hab⟩ := hnd
    exact hpath.branchPathCoeff_pos _ _
      Dist.uniform_fullSupport Dist.uniform_fullSupport
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  nlinarith [hcoc, hpos]

/-- Canonical `n`-element action type in `Type u` (for the cardinal gauge). -/
abbrev canonType (n : ℕ) : Type u := ULift.{u} (Fin n)

/-- The faithful chain scale of the uniform prior on the canonical `n`-element
action type.  By R1 (`scaleRelabel_of_FinalHM_covariance`) it equals the chain
scale of the uniform prior on *any* `n`-element type (`scale_uniform_eq_cardScale`
below), so it depends only on `n`.

**Caveat (not the cardinal gauge `t_n`).**  This value is in fact `1` for every
nondegenerate `n` (`scale (u_A) = branchCoeff (u_A) (u_A) = branchPathCoeff (u_A)
(u_A) = 1` by the full-support cocycle at `q = r = s = u_A`).  So it is a true but
degenerate quantity and is **not** the paper's cardinal gauge `t_n = K_{n,2}`,
which is a genuine cross-cardinality embedding defect.  The real `t_n` is defined
from `boundaryCoeff` on a canonical boundary prior (see the R2b plan in
`ELIMINATE_PRODUCT_NORMALIZED_PROGRESS.md`); `cardScale` is retained only as the
`scale (u_A)`-value bookkeeping lemma. -/
noncomputable def cardScale
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F) (n : ℕ) : ℝ :=
  if h : n = 0 then 1
  else
    haveI : NeZero n := ⟨h⟩
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := canonType.{u} n))

/-- The chain scale of the uniform prior depends only on the cardinality: it
equals `cardScale (card A)`.  Immediate from R1 via the equivalence
`A ≃ canonType (card A)`, which carries the uniform prior to the uniform prior. -/
theorem scale_uniform_eq_cardScale
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := A)) =
      cardScale hhm hbranchData hax (Fintype.card A) := by
  classical
  have hcard0 : Fintype.card A ≠ 0 := Fintype.card_ne_zero
  rw [cardScale, dif_neg hcard0]
  haveI : NeZero (Fintype.card A) := ⟨hcard0⟩
  set e : A ≃ canonType.{u} (Fintype.card A) :=
    (Fintype.equivFin A).trans Equiv.ulift.symm with he
  have huni : Relabeling.relabelDist e (Dist.uniform (A := A)) =
      Dist.uniform (A := canonType.{u} (Fintype.card A)) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply]
    congr 1
    simp [canonType]
  rw [← huni]
  exact (scaleRelabel_of_FinalHM_covariance hhm hbranchData hax e
    (Dist.uniform (A := A)) Dist.uniform_fullSupport).symm

/-! ### Canonical boundary priors for the cardinal-gauge (`t_n`) construction

`canonBoundary n m` is the uniform prior on the first `m` actions of the canonical
`n`-element type — the paper's canonical `m`-point face inside an `n`-point action
set.  The embedding defect `K_{n,m}` is read off from the boundary coefficient at
`(u_n, canonBoundary n m)`; the cocycle over nested faces yields `t_n`. -/

/-- Inclusion kernel `canonType m → canonType n` (m ≤ n) via `Fin.castLE`. -/
noncomputable def canonInclKernel (n m : ℕ) (hmn : m ≤ n) :
    Channel.ActionKernel (canonType.{u} m) (canonType.{u} n) :=
  fun a => Dist.pure (ULift.up (Fin.castLE hmn a.down))

/-- Canonical `m`-point boundary prior inside the `n`-point action set: the
uniform prior on `canonType m` pushed forward along the inclusion. -/
noncomputable def canonBoundary (n m : ℕ) (hmn : m ≤ n) [NeZero m] :
    Dist (canonType.{u} n) :=
  Channel.actionPushforward (Dist.uniform (A := canonType.{u} m)) (canonInclKernel n m hmn)

theorem canonBoundary_apply (n m : ℕ) (hmn : m ≤ n) [NeZero m] (j : Fin n) :
    (canonBoundary.{u} n m hmn) (ULift.up j) =
      if (j : ℕ) < m then (1 : ℝ) / m else 0 := by
  classical
  have hcard : Fintype.card (canonType.{u} m) = m := by simp [canonType]
  unfold canonBoundary canonInclKernel Channel.actionPushforward
  show (∑ a : canonType.{u} m, (Dist.uniform (A := canonType.{u} m)) a *
      (Dist.pure (ULift.up (Fin.castLE hmn a.down)) : Dist (canonType.{u} n)) (ULift.up j)) = _
  have hterm : ∀ a : canonType.{u} m,
      (Dist.pure (ULift.up (Fin.castLE hmn a.down)) : Dist (canonType.{u} n)) (ULift.up j) =
        if (a.down : ℕ) = (j : ℕ) then (1:ℝ) else 0 := by
    intro a
    by_cases h : (a.down : ℕ) = (j : ℕ)
    · rw [if_pos h]
      have : (ULift.up (Fin.castLE hmn a.down) : canonType.{u} n) = ULift.up j := by
        apply ULift.ext; apply Fin.ext; rw [Fin.val_castLE]; exact h
      rw [this, Dist.pure_apply_self]
    · rw [if_neg h, Dist.pure_apply_ne]
      intro hc
      apply h
      have : Fin.castLE hmn a.down = j := ULift.up.inj hc.symm
      rw [← Fin.val_castLE (h := hmn), this]
  simp only [hterm, Dist.uniform_apply, hcard, mul_ite, mul_one, mul_zero]
  by_cases hj : (j : ℕ) < m
  · rw [if_pos hj]
    rw [Finset.sum_eq_single (ULift.up (⟨(j:ℕ), hj⟩ : Fin m))]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg]
      intro hc
      apply hb
      apply ULift.ext; apply Fin.ext; simpa using hc
    · intro hne; exact absurd (Finset.mem_univ _) hne
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    intro hc; exact hj (hc ▸ a.down.isLt)

theorem canonBoundary_pos (n m : ℕ) (hmn : m ≤ n) [NeZero m] (j : Fin n) :
    0 < (canonBoundary.{u} n m hmn) (ULift.up j) ↔ (j : ℕ) < m := by
  rw [canonBoundary_apply]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  split
  · rename_i h; constructor
    · intro _; assumption
    · intro _
      have : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      positivity
  · rename_i h; constructor
    · intro hc; exact absurd hc (lt_irrefl 0)
    · intro hc; exact absurd hc h

theorem canonBoundary_support_nonempty (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hn : 0 < n) :
    ∃ a : canonType.{u} n, 0 < (canonBoundary.{u} n m hmn) a := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  exact ⟨ULift.up ⟨0, hn⟩, (canonBoundary_pos n m hmn ⟨0, hn⟩).mpr hm⟩

theorem canonBoundary_nondeg (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m) :
    ∃ a b : canonType.{u} n, a ≠ b ∧
      0 < (canonBoundary.{u} n m hmn) a ∧ 0 < (canonBoundary.{u} n m hmn) b := by
  have h0 : (0:ℕ) < n := lt_of_lt_of_le (by omega) hmn
  have h1 : (1:ℕ) < n := lt_of_lt_of_le hm2 hmn
  refine ⟨ULift.up ⟨0, h0⟩, ULift.up ⟨1, h1⟩, ?_, ?_, ?_⟩
  · intro h
    rw [ULift.up.injEq] at h
    have : (0:ℕ) = 1 := Fin.val_eq_of_eq h
    exact absurd this (by norm_num)
  · exact (canonBoundary_pos n m hmn ⟨0, h0⟩).mpr (by show (0:ℕ) < m; omega)
  · exact (canonBoundary_pos n m hmn ⟨1, h1⟩).mpr (by show (1:ℕ) < m; omega)

theorem canonBoundary_boundary (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hmlt : m < n) :
    ¬ (canonBoundary.{u} n m hmn).FullSupport := by
  intro hfs
  have := hfs (ULift.up ⟨m, hmlt⟩)
  rw [canonBoundary_apply] at this
  simp at this

/-- The positive support of `canonBoundary n m` is the canonical `m`-element type. -/
noncomputable def canonBoundarySupportEquiv (n m : ℕ) (hmn : m ≤ n) [NeZero m] :
    supportSubtype (canonBoundary.{u} n m hmn) ≃ canonType.{u} m where
  toFun a := ULift.up ⟨(a.1.down : ℕ), by
    have := (canonBoundary_pos n m hmn a.1.down).mp (by simpa using a.2)
    simpa using this⟩
  invFun b := ⟨ULift.up (Fin.castLE hmn b.down), by
    show 0 < (canonBoundary n m hmn) (ULift.up (Fin.castLE hmn b.down))
    rw [canonBoundary_pos]; simpa using b.down.isLt⟩
  left_inv a := by apply Subtype.ext; apply ULift.ext; apply Fin.ext; simp
  right_inv b := by apply ULift.ext; apply Fin.ext; simp

/-- **Nesting of canonical boundary priors.**  The canonical `ℓ`-point face
inside the `n`-point set is the pushforward of the canonical `ℓ`-point face
inside the `m`-point set along the `m ↪ n` inclusion (`ℓ ≤ m ≤ n`).  This is the
geometric identity underlying the embedding-defect cocycle. -/
theorem canonBoundary_nest (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] :
    canonBoundary.{u} n l (hml.trans hmn) =
      Channel.actionPushforward (canonBoundary.{u} m l hml) (canonInclKernel n m hmn) := by
  ext j
  obtain ⟨jn⟩ := j
  rw [canonBoundary_apply]
  show (if (jn:ℕ) < l then (1:ℝ)/l else 0) =
    ∑ c : canonType.{u} m, (canonBoundary.{u} m l hml) c *
      (Dist.pure (ULift.up (Fin.castLE hmn c.down)) : Dist (canonType.{u} n)) (ULift.up jn)
  by_cases hjm : (jn:ℕ) < m
  · rw [Finset.sum_eq_single (ULift.up (⟨(jn:ℕ), hjm⟩ : Fin m))]
    · have hpt : (ULift.up.{u} (Fin.castLE hmn ((ULift.up.{u} (⟨(jn:ℕ),hjm⟩ : Fin m)).down))
            : canonType.{u} n) = (ULift.up.{u} jn : canonType.{u} n) := by
        apply ULift.ext; apply Fin.ext; simp
      rw [hpt, Dist.pure_apply_self, mul_one, canonBoundary_apply]
    · intro c _ hc
      rw [Dist.pure_apply_ne, mul_zero]
      intro hcontra
      apply hc
      apply ULift.ext; apply Fin.ext
      have hce : Fin.castLE hmn c.down = jn := ULift.up.inj hcontra.symm
      have := Fin.ext_iff.mp hce
      simpa using this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (fun h => hjm (lt_of_lt_of_le h hml))]
    refine (Finset.sum_eq_zero ?_).symm
    intro c _
    rw [Dist.pure_apply_ne, mul_zero]
    intro hcontra
    apply hjm
    have hce : Fin.castLE hmn c.down = jn := ULift.up.inj hcontra.symm
    rw [← hce, Fin.val_castLE]
    exact c.down.isLt

/-- Deterministic (pure-kernel) pushforward composition: pushing by `pure ∘ f`
then `pure ∘ g` equals pushing by `pure ∘ (g ∘ f)`. -/
theorem actionPushforward_pure_comp {A B C : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (d : Dist A) (f : A → B) (g : B → C) :
    Channel.actionPushforward (Channel.actionPushforward d (fun a => Dist.pure (f a)))
        (fun b => Dist.pure (g b)) =
      Channel.actionPushforward d (fun a => Dist.pure (g (f a))) := by
  ext c
  show (∑ b : B, (Channel.actionPushforward d (fun a => Dist.pure (f a))) b *
        (Dist.pure (g b) : Dist C) c) =
      ∑ a : A, d a * (Dist.pure (g (f a)) : Dist C) c
  have hinner : ∀ b : B, (Channel.actionPushforward d (fun a => Dist.pure (f a))) b =
      ∑ a : A, d a * (Dist.pure (f a) : Dist B) b := fun b => rfl
  simp only [hinner, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : c = g (f a)
  · subst hc
    rw [Finset.sum_eq_single (f a)]
    · rw [Dist.pure_apply_self, Dist.pure_apply_self, mul_one, mul_one]
    · intro b _ hb
      rw [Dist.pure_apply_ne (f a) b hb, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Dist.pure_apply_ne (g (f a)) c hc, mul_zero]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b = f a
    · subst hb; rw [Dist.pure_apply_ne (g (f a)) c hc, mul_zero]
    · rw [Dist.pure_apply_ne (f a) b hb, mul_zero, zero_mul]

/-- The canonical inclusion kernels compose: `(m ↪ n) ∘ (ℓ ↪ m) = (ℓ ↪ n)`. -/
theorem canonInclKernel_comp (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) (d : Dist (canonType.{u} l)) :
    Channel.actionPushforward
        (Channel.actionPushforward d (canonInclKernel m l hml)) (canonInclKernel n m hmn) =
      Channel.actionPushforward d (canonInclKernel n l (hml.trans hmn)) := by
  have h := actionPushforward_pure_comp (C := canonType.{u} n) d
    (fun b : canonType.{u} l => ULift.up (Fin.castLE hml b.down))
    (fun c : canonType.{u} m => ULift.up (Fin.castLE hmn c.down))
  show Channel.actionPushforward
      (Channel.actionPushforward d (fun b => Dist.pure (ULift.up (Fin.castLE hml b.down))))
      (fun c => Dist.pure (ULift.up (Fin.castLE hmn c.down))) = _
  rw [h]
  apply congrArg (Channel.actionPushforward d)
  funext a
  congr 2

/-- The faithful chain scale of the uniform prior on a nondegenerate action type
is `1`: `scale (u_A) = branchCoeff (u_A) (u_A) = branchPathCoeff (u_A) (u_A) = 1`
by the full-support tangent-scalar cocycle at `q = r = s = u_A`. -/
theorem scale_uniform_eq_one
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (hnd : ∃ a b : A, a ≠ b) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := A)) = 1 := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
  show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff (Dist.uniform (A := A)) (Dist.uniform (A := A)) = 1
  rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
    ).branch_agg.branchCoeff (Dist.uniform (A := A)) (Dist.uniform (A := A)) =
    branchCoeffFromTangentRepParts hpath
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
      hfaith.singleton_scale (Dist.uniform (A := A)) (Dist.uniform (A := A)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  have hcoc := branchCoeffTangentScalar_cocycle_fullSupport hfaith.linear_part F hax hV hpath
    (Dist.uniform (A := A)) (Dist.uniform (A := A)) (Dist.uniform (A := A))
    Dist.uniform_fullSupport Dist.uniform_fullSupport Dist.uniform_fullSupport hnd
  have hpos : 0 < hpath.branchPathCoeff (Dist.uniform (A := A)) (Dist.uniform (A := A)) := by
    obtain ⟨a, b, hab⟩ := hnd
    exact hpath.branchPathCoeff_pos _ _ Dist.uniform_fullSupport Dist.uniform_fullSupport
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  nlinarith [hcoc, hpos]

/-- The support-face of `canonBoundary n m` carries the uniform prior on its
`m`-element support (each surviving action has probability `1/m`). -/
theorem canonBoundary_face_uniform (n m : ℕ) (hmn : m ≤ n) [NeZero m]
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    (canonBoundary.{u} n m hmn).restrictToSupport =
      Dist.uniform (A := supportSubtype (canonBoundary.{u} n m hmn)) := by
  classical
  have hcard : Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) = m := by
    rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]; simp [canonType]
  ext a
  rw [Dist.restrictToSupport_apply, Dist.uniform_apply, hcard]
  obtain ⟨⟨j⟩, hj⟩ := a
  rw [canonBoundary_apply]
  have : (j : ℕ) < m := by
    have := (canonBoundary_pos n m hmn j).mp (by simpa using hj); simpa using this
  rw [if_pos this]

/-- The chain scale of the `canonBoundary n m` support-face is `1` (it is the
uniform prior on an `m ≥ 2`-element type; `scale_uniform_eq_one`). -/
theorem canonBoundary_face_scale_eq_one
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m)
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (canonBoundary.{u} n m hmn).restrictToSupport = 1 := by
  rw [canonBoundary_face_uniform n m hmn]
  have hnd : ∃ a b : supportSubtype (canonBoundary.{u} n m hmn), a ≠ b := by
    have hcard : Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) = m := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]; simp [canonType]
    have : 1 < Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) := by omega
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    exact ⟨a, b, hab⟩
  exact scale_uniform_eq_one hhm hbranchData hax hnd

/-- **The embedding defect `K_{n,m}`** (`2 ≤ m ≤ n`): the boundary coefficient
from the uniform prior on the `n`-point action set to the canonical `m`-point
face.  Since both `scale (u_n)` and the face scale are `1`
(`scale_uniform_eq_one`, `canonBoundary_face_scale_eq_one`), this boundary
coefficient *is* the paper's embedding defect for the canonical inclusion.  The
cardinal gauge `t_n` is `cardDefect n 2`. -/
noncomputable def cardDefect
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F) (n m : ℕ) : ℝ :=
  if h : 2 ≤ m ∧ m ≤ n then
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m h.2)
  else 1

/-- The embedding defect is positive for `2 ≤ m < n`. -/
theorem cardDefect_pos
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F) (n m : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    0 < cardDefect hhm hbranchData hax n m := by
  classical
  have hle : m ≤ n := le_of_lt hmn
  rw [cardDefect, dif_pos ⟨hm2, hle⟩]
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
  apply (branchBoundaryFaceScale_of_faithfulAssumptions
    (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)).boundaryCoeff_pos
  · exact Dist.uniform_fullSupport
  · exact canonBoundary_support_nonempty n m hle (by omega)
  · exact canonBoundary_nondeg n m hle hm2
  · exact canonBoundary_boundary n m hle hmn

/-- Selected-chain scale of the canonical boundary support face is `1`. -/
theorem canonBoundary_face_scale_eq_oneFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m)
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale (canonBoundary.{u} n m hmn).restrictToSupport = 1 := by
  rw [canonBoundary_face_uniform n m hmn]
  have hnd :
      ∃ a b : supportSubtype (canonBoundary.{u} n m hmn), a ≠ b := by
    have hcard :
        Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) = m := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]
      simp [canonType]
    have : 1 < Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) := by
      omega
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    exact ⟨a, b, hab⟩
  exact scale_uniform_eq_oneAtomicFor hhm hax hbranchData hnd

/-- Selected embedding defect `K_{n,m}` read from the selected boundary
coefficient package. -/
noncomputable def cardDefectFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) : ℝ :=
  if h : 2 ≤ m ∧ m ≤ n then
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
    (boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
    ).boundaryCoeff (Dist.uniform (A := canonType.{u} n))
      (canonBoundary.{u} n m h.2)
  else 1

/-- Positivity of the selected embedding defect for strict boundary faces. -/
theorem cardDefect_posFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    0 < cardDefectFor hhm hax hbranchData n m := by
  classical
  have hle : m ≤ n := le_of_lt hmn
  rw [cardDefectFor, dif_pos ⟨hm2, hle⟩]
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
  apply (boundaryFaceScale_of_coefficientScaleNormalization
    hbranchData.boundary_coeff).boundaryCoeff_pos
  · exact Dist.uniform_fullSupport
  · exact canonBoundary_support_nonempty n m hle (by omega)
  · exact canonBoundary_nondeg n m hle hm2
  · exact canonBoundary_boundary n m hle hmn

/-- Inclusion of the `ℓ`-face support into the `m`-face support (same ambient
element), for `ℓ ≤ m ≤ n`. -/
noncomputable def nestSupportMap (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] [NeZero m] :
    supportSubtype (canonBoundary.{u} n l (hml.trans hmn)) →
    supportSubtype (canonBoundary.{u} n m hmn) :=
  fun a => ⟨a.1, by
    obtain ⟨⟨jn⟩, hj⟩ := a
    show 0 < (canonBoundary n m hmn) (ULift.up jn)
    rw [canonBoundary_pos]
    have hjl : ((jn : Fin n) : ℕ) < l := (canonBoundary_pos n l (hml.trans hmn) jn).mp hj
    exact lt_of_lt_of_le hjl hml⟩

/-- The support inclusion of the `ℓ`-face factors through the `m`-face: pushing a
belief into the ambient space via the `ℓ`-face inclusion equals first mapping to
the `m`-face support then including. -/
theorem supportInclude_nest (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] [NeZero m]
    (d : Dist (supportSubtype (canonBoundary.{u} n l (hml.trans hmn)))) :
    Channel.actionPushforward d (supportIncludeKernel (canonBoundary.{u} n l (hml.trans hmn))) =
      Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)))
        (supportIncludeKernel (canonBoundary.{u} n m hmn)) := by
  show Channel.actionPushforward d
        (fun a => Dist.pure (a.1 : canonType.{u} n)) =
      Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)))
        (fun b => Dist.pure (b.1 : canonType.{u} n))
  rw [actionPushforward_pure_comp d (nestSupportMap n m l hmn hml) (fun b => (b.1 : canonType.{u} n))]
  rfl

/-- Pull a signed posterior law through a deterministic pushforward map. -/
noncomputable def pushSignedDet
    {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (K : S → T) (η : PosteriorLawSigned S) :
    PosteriorLawSigned T :=
  fun ψ => η (fun d => ψ (Channel.actionPushforward d
    (fun s => Dist.pure (K s))))

/-- Deterministic pushforward preserves atomic-linearity of signed posterior
laws. -/
noncomputable def atomicLinear_pushSignedDet
    {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (K : S → T) {η : PosteriorLawSigned S}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (pushSignedDet K η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i =>
        Channel.actionPushforward (hη.witness.point i)
          (fun s => Dist.pure (K s))
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext ψ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        ψ (Channel.actionPushforward (hη.witness.point i)
          (fun s => Dist.pure (K s)))) =
      η (fun d => ψ (Channel.actionPushforward d
        (fun s => Dist.pure (K s))))
    have h := congrFun hη.eval_eq
      (fun d => ψ (Channel.actionPushforward d
        (fun s => Dist.pure (K s))))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- Relabelling pullback along an arbitrary finite equivalence preserves
atomic-linearity. -/
noncomputable def atomicLinear_relabelPullbackDirect
    {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (E : S ≃ T) {η : PosteriorLawSigned S}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear
      (fun ψ : Dist T → ℝ => η (fun d => ψ (Relabeling.relabelDist E d))) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i => Relabeling.relabelDist E (hη.witness.point i)
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext ψ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        ψ (Relabeling.relabelDist E (hη.witness.point i))) =
      η (fun d => ψ (Relabeling.relabelDist E d))
    have h := congrFun hη.eval_eq
      (fun d => ψ (Relabeling.relabelDist E d))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- **Transport equation for the embedding defect.**  For `2 ≤ m < n` and a
tangent `η` on the `m`-face support, the ambient marginal value of the uniform
prior, restricted along the face inclusion, equals `cardDefect n m` times the
intrinsic face marginal value.  (This is the support-face marginal-value
transport, with `boundaryCoeff` identified as `cardDefect`.) -/
theorem cardDefect_transport
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n)
    (η : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m (le_of_lt hmn))))
    (hηtan : PosteriorLawTangent η) :
    η (fun d => (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (Dist.uniform (A := canonType.{u} n))
          (Channel.actionPushforward d
            (supportIncludeKernel (canonBoundary.{u} n m (le_of_lt hmn))))) =
      cardDefect hhm hbranchData hax n m *
        η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (canonBoundary.{u} n m (le_of_lt hmn)).restrictToSupport) := by
  classical
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  have htr := hbranchData.marginal_value.support_face_marginalValue_scalar
    F hax hV (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m (le_of_lt hmn))
    Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n m (le_of_lt hmn) (by omega))
    (canonBoundary_nondeg n m (le_of_lt hmn) hm2)
    (canonBoundary_boundary n m (le_of_lt hmn) hmn) η hηtan
  have hcd : cardDefect hhm hbranchData hax n m =
      (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      ).boundaryCoeff (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m (le_of_lt hmn)) := by
    rw [cardDefect, dif_pos ⟨hm2, le_of_lt hmn⟩]
  rw [hcd]
  exact htr

/-- Selected transport equation for the embedding defect. -/
theorem cardDefect_transportFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n)
    (η : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m (le_of_lt hmn))))
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    η (fun d => (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (Dist.uniform (A := canonType.{u} n))
          (Channel.actionPushforward d
            (supportIncludeKernel (canonBoundary.{u} n m (le_of_lt hmn))))) =
      cardDefectFor hhm hax hbranchData n m *
        η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (canonBoundary.{u} n m (le_of_lt hmn)).restrictToSupport) := by
  classical
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  have htr :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
    (A := canonType.{u} n) (Dist.uniform (A := canonType.{u} n))
    (canonBoundary.{u} n m (le_of_lt hmn))
    Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n m (le_of_lt hmn) (by omega))
    (canonBoundary_nondeg n m (le_of_lt hmn) hm2)
    (canonBoundary_boundary n m (le_of_lt hmn) hmn) η hηatomic hηtan
  have hcd :
      cardDefectFor hhm hax hbranchData n m =
        (boundaryFaceScale_of_coefficientScaleNormalization
          hbranchData.boundary_coeff
        ).boundaryCoeff (Dist.uniform (A := canonType.{u} n))
          (canonBoundary.{u} n m (le_of_lt hmn)) := by
    rw [cardDefectFor, dif_pos ⟨hm2, le_of_lt hmn⟩]
  rw [hcd]
  exact htr

theorem relabelDist_eq_actionPushforward {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (q : Dist A) :
    relabelDist e q = Channel.actionPushforward q (fun a => Dist.pure (e a)) := by
  ext b
  rw [relabelDist_apply]
  show q (e.symm b) = ∑ a : A, q a * (Dist.pure (e a) : Dist B) b
  rw [Finset.sum_eq_single (e.symm b)]
  · rw [Equiv.apply_symm_apply, Dist.pure_apply_self, mul_one]
  · intro a _ ha
    rw [Dist.pure_apply_ne (e a) b, mul_zero]
    intro hcontra; apply ha; rw [hcontra, Equiv.symm_apply_apply]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cBface_eq_relabel_uniform (n m : ℕ) (hmn : m ≤ n) [NeZero m] :
    haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hmn)) := supportSubtype_nonempty _
    (canonBoundary.{u} n m hmn).restrictToSupport =
      relabelDist (canonBoundarySupportEquiv n m hmn).symm (Dist.uniform (A := canonType.{u} m)) := by
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hmn)) := supportSubtype_nonempty _
  rw [canonBoundary_face_uniform n m hmn]
  ext a
  rw [Dist.uniform_apply, relabelDist_apply, Dist.uniform_apply]
  congr 1
  rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]

-- push d along pure∘nestMap = relabel e.symm (push (push d along pure∘equiv_nl) along canonIncl)
theorem push_nest_eq_relabel (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] [NeZero m]
    (d : Dist (supportSubtype (canonBoundary.{u} n l (hml.trans hmn)))) :
    Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)) =
      relabelDist (canonBoundarySupportEquiv n m hmn).symm
        (Channel.actionPushforward
          (Channel.actionPushforward d
            (fun a => Dist.pure (canonBoundarySupportEquiv n l (hml.trans hmn) a)))
          (canonInclKernel m l hml)) := by
  rw [relabelDist_eq_actionPushforward]
  show Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)) =
    Channel.actionPushforward
      (Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (canonBoundarySupportEquiv n l (hml.trans hmn) a)))
        (fun b => Dist.pure (ULift.up (Fin.castLE hml b.down))))
      (fun c => Dist.pure ((canonBoundarySupportEquiv n m hmn).symm c))
  rw [actionPushforward_pure_comp _ (fun a => canonBoundarySupportEquiv n l (hml.trans hmn) a)
    (fun b => ULift.up (Fin.castLE hml b.down))]
  rw [actionPushforward_pure_comp _ (fun a => ULift.up (Fin.castLE hml (canonBoundarySupportEquiv n l (hml.trans hmn) a).down))
    (fun c => (canonBoundarySupportEquiv n m hmn).symm c)]
  apply congrArg (Channel.actionPushforward d)
  funext a
  congr 1


theorem canonIncl_eq_supportInclude (m l : ℕ) (hml : l ≤ m) [NeZero l] [NeZero m]
    (x : Dist (canonType.{u} l)) :
    haveI : Nonempty (supportSubtype (canonBoundary.{u} m l hml)) := supportSubtype_nonempty _
    Channel.actionPushforward x (canonInclKernel m l hml) =
      Channel.actionPushforward
        (Channel.actionPushforward x
          (fun b => Dist.pure ((canonBoundarySupportEquiv m l hml).symm b)))
        (supportIncludeKernel (canonBoundary.{u} m l hml)) := by
  haveI : Nonempty (supportSubtype (canonBoundary.{u} m l hml)) := supportSubtype_nonempty _
  show Channel.actionPushforward x (fun b => Dist.pure (ULift.up (Fin.castLE hml b.down))) =
    Channel.actionPushforward
      (Channel.actionPushforward x (fun b => Dist.pure ((canonBoundarySupportEquiv m l hml).symm b)))
      (fun a => Dist.pure (a.1 : canonType.{u} m))
  rw [actionPushforward_pure_comp x (fun b => (canonBoundarySupportEquiv m l hml).symm b)
    (fun a => (a.1 : canonType.{u} m))]
  apply congrArg (Channel.actionPushforward x)
  funext b
  congr 1

/-- **The embedding-defect cocycle.** -/
theorem cardDefect_cocycle
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    (n m l : ℕ) [NeZero l] [NeZero m] [NeZero n]
    (hl2 : 2 ≤ l) (hlm : l < m) (hmn : m < n) :
    cardDefect hhm hbranchData hax n m * cardDefect hhm hbranchData hax m l =
      cardDefect hhm hbranchData hax n l := by
  classical
  have hle_ml : l ≤ m := le_of_lt hlm
  have hle_mn : m ≤ n := le_of_lt hmn
  have hle_ln : l ≤ n := hle_ml.trans hle_mn
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hintdef
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
    with hfaithdef
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n l hle_ln)) := supportSubtype_nonempty _
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hle_mn)) := supportSubtype_nonempty _
  -- A1 nonzero tangent η on supp(cB n l)
  have hfaceNL_fs : ((canonBoundary.{u} n l hle_ln).restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport _
  have hfaceNL_nd : ∃ a b : supportSubtype (canonBoundary.{u} n l hle_ln), a ≠ b ∧
      0 < (canonBoundary.{u} n l hle_ln).restrictToSupport a ∧
      0 < (canonBoundary.{u} n l hle_ln).restrictToSupport b := by
    have hcard : Fintype.card (supportSubtype (canonBoundary.{u} n l hle_ln)) = l := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n l hle_ln)]; simp [canonType]
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card (supportSubtype (canonBoundary.{u} n l hle_ln)))
    exact ⟨a, b, hab, hfaceNL_fs a, hfaceNL_fs b⟩
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hfaith.linear_part F hax hV
      (canonBoundary.{u} n l hle_ln).restrictToSupport (canonBoundary.{u} n l hle_ln).restrictToSupport
      hfaceNL_fs hfaceNL_fs hfaceNL_nd
  -- hηnz : linPart faceNL η ≠ 0, i.e. η(mV faceNL) ≠ 0
  have hηnz' : η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) ≠ 0 := hηnz
  -- Transport at (n, l):
  have hT_nl := cardDefect_transport hhm hbranchData hax n l hl2 (lt_of_lt_of_le hlm hle_mn) η hηtan
  -- The nest-pushed tangent η'' on supp(cB n m)
  set η'' : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m hle_mn)) :=
    (fun ψ => η (fun d => ψ (Channel.actionPushforward d
      (fun a => Dist.pure (nestSupportMap n m l hle_mn hle_ml a))))) with hη''def
  have hη''tan : PosteriorLawTangent η'' := by
    refine ⟨?_, ?_⟩
    · show η (fun d => (1:ℝ)) = 0; exact hηtan.1
    · intro a
      show η (fun d => (Channel.actionPushforward d
        (fun a' => Dist.pure (nestSupportMap n m l hle_mn hle_ml a'))) a) = 0
      by_cases hex : ∃ a'₀ : supportSubtype (canonBoundary.{u} n l hle_ln),
          nestSupportMap n m l hle_mn hle_ml a'₀ = a
      · obtain ⟨a'₀, ha'₀⟩ := hex
        have hfn : (fun d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)) =>
            (Channel.actionPushforward d
              (fun a' => Dist.pure (nestSupportMap n m l hle_mn hle_ml a'))) a) =
            (fun d => d a'₀) := by
          funext d
          show (∑ a' : supportSubtype (canonBoundary.{u} n l hle_ln),
            d a' * (Dist.pure (nestSupportMap n m l hle_mn hle_ml a') : Dist _) a) = d a'₀
          rw [Finset.sum_eq_single a'₀]
          · rw [ha'₀, Dist.pure_apply_self, mul_one]
          · intro b _ hb
            rw [Dist.pure_apply_ne, mul_zero]
            intro hc
            apply hb
            -- nestMap b = a = nestMap a'₀, and nestMap preserves .1, so b = a'₀
            have hb1 : (nestSupportMap n m l hle_mn hle_ml b).1 = a.1 := by rw [← hc]
            have ha1 : (nestSupportMap n m l hle_mn hle_ml a'₀).1 = a.1 := by rw [ha'₀]
            apply Subtype.ext
            have : (b.1 : canonType.{u} n) = a'₀.1 := by
              have := hb1.trans ha1.symm
              simpa [nestSupportMap] using this
            exact this
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hfn]; exact hηtan.2 a'₀
      · have hfn : (fun d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)) =>
            (Channel.actionPushforward d
              (fun a' => Dist.pure (nestSupportMap n m l hle_mn hle_ml a'))) a) =
            (fun _ => (0:ℝ)) := by
          funext d
          show (∑ a' : supportSubtype (canonBoundary.{u} n l hle_ln),
            d a' * (Dist.pure (nestSupportMap n m l hle_mn hle_ml a') : Dist _) a) = 0
          apply Finset.sum_eq_zero
          intro a' _
          rw [Dist.pure_apply_ne, mul_zero]
          intro hc; exact hex ⟨a', hc.symm⟩
        rw [hfn]
        have := hηtan.1
        -- η(fun _ => 0) = 0: use η is atomicLinear ⟹ η 0 = 0
        have h0 := congrFun hηatomic.eval_eq (fun _ => (0:ℝ))
        rw [AtomicPosteriorSignedLaw.eval_apply] at h0
        rw [← h0]; simp
  have hη''atomic : PosteriorLawSigned.AtomicLinear η'' := by
    rw [hη''def]
    exact atomicLinear_pushSignedDet
      (nestSupportMap n m l hle_mn hle_ml) hηatomic
-- LHS link via supportInclude_nest: η(mV(u_n)∘push_{cB n l}) = η''(mV(u_n)∘push_{cB n m})
  have hLHS_link :
      η (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} n))
            (Channel.actionPushforward d (supportIncludeKernel (canonBoundary.{u} n l hle_ln)))) =
      η'' (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} n))
            (Channel.actionPushforward d (supportIncludeKernel (canonBoundary.{u} n m hle_mn)))) := by
    rw [hη''def]
    congr 1
    funext d
    rw [supportInclude_nest n m l hle_mn hle_ml d]
  have h2m : 2 ≤ m := le_of_lt (lt_of_le_of_lt hl2 hlm)
  have hT_nm := cardDefect_transport hhm hbranchData hax n m h2m hmn η'' hη''tan
  -- Combine hT_nl, hLHS_link, hT_nm:
  --   cardDefect n l · η(mV faceNL) = LHS_nl = LHS_nm(via link) = cardDefect n m · η''(mV faceNM)
  have hchain1 : cardDefect hhm hbranchData hax n l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      cardDefect hhm hbranchData hax n m *
      η'' (hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport) := by
    rw [← hT_nl, hLHS_link, hT_nm]
  -- Bridge: η''(mV faceNM) = cardDefect m l · η(mV faceNL)
-- Bridge: η''(mV faceNM) = cardDefect m l · η(mV faceNL)
  have hbridge :
      η'' (hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport) =
      cardDefect hhm hbranchData hax m l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
    let eNM :=
      canonBoundarySupportEquiv n m hle_mn
    have hfaceNM :
        Relabeling.relabelDist eNM
            (canonBoundary.{u} n m hle_mn).restrictToSupport =
          Dist.uniform (A := canonType.{u} m) := by
      rw [cBface_eq_relabel_uniform n m hle_mn]
      ext a
      simp [Relabeling.relabelDist_apply]
    have hnatural :=
      finalHM_affineLinearPart_relabel_atomic_eval hhm hax eNM
        (canonBoundary.{u} n m hle_mn).restrictToSupport
        (Dist.restrictToSupport_fullSupport _)
        η'' hη''atomic hη''tan
    rw [hfaceNM] at hnatural
    rw [← hnatural]
    change η (fun d => hint.marginalValue F hV
      (Dist.uniform (A := canonType.{u} m))
      (Relabeling.relabelDist eNM
        (Channel.actionPushforward d
          (fun a => Dist.pure
            (nestSupportMap n m l hle_mn hle_ml a))))) = _
    have hpush : ∀ d,
        Relabeling.relabelDist eNM
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (nestSupportMap n m l hle_mn hle_ml a))) =
          Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml) := by
      intro d
      calc
        Relabeling.relabelDist eNM
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (nestSupportMap n m l hle_mn hle_ml a))) =
            Relabeling.relabelDist eNM
              (Relabeling.relabelDist eNM.symm
                (Channel.actionPushforward
                  (Channel.actionPushforward d
                    (fun a => Dist.pure
                      (canonBoundarySupportEquiv n l hle_ln a)))
                  (canonInclKernel m l hle_ml))) :=
              congrArg (Relabeling.relabelDist eNM)
                (push_nest_eq_relabel n m l hle_mn hle_ml d)
        _ = _ := by
          ext a
          simp [Relabeling.relabelDist_apply]
    have hleft :
        η (fun d => hint.marginalValue F hV
          (Dist.uniform (A := canonType.{u} m))
          (Relabeling.relabelDist eNM
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (nestSupportMap n m l hle_mn hle_ml a))))) =
        η (fun d => hint.marginalValue F hV
          (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml))) := by
      congr 1
      funext d
      rw [hpush d]
    rw [hleft]
    -- Now this is η(fun d => mV u_m (push (e_nl·d) along canonIncl)).
    -- = (e_nl-pushed η)(fun d' => mV u_m (push d' along canonIncl)) — a transport at (m,l).
    -- Define the pushed tangent ζ on supp(cB m l), reindexing d ↦ e_nl·d then supp.
-- φ : supp(cB n l) ≃ supp(cB m l), the composite equiv (both faces ≃ canonType l)
    set φ : supportSubtype (canonBoundary.{u} n l hle_ln) ≃ supportSubtype (canonBoundary.{u} m l hle_ml) :=
      (canonBoundarySupportEquiv n l hle_ln).trans (canonBoundarySupportEquiv m l hle_ml).symm with hφdef
    haveI : Nonempty (supportSubtype (canonBoundary.{u} m l hle_ml)) := supportSubtype_nonempty _
    -- reindex: push (e_nl·d) along canonIncl m l = push (relabel φ d) along supportInclude(cB m l)
    have hreindex : ∀ d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)),
        Channel.actionPushforward
          (Channel.actionPushforward d (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
          (canonInclKernel m l hle_ml) =
        Channel.actionPushforward (relabelDist φ d)
          (supportIncludeKernel (canonBoundary.{u} m l hle_ml)) := by
      intro d
      rw [canonIncl_eq_supportInclude m l hle_ml
        (Channel.actionPushforward d (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))]
      congr 1
      rw [relabelDist_eq_actionPushforward]
      rw [actionPushforward_pure_comp d (fun a => canonBoundarySupportEquiv n l hle_ln a)
        (fun b => (canonBoundarySupportEquiv m l hle_ml).symm b)]
      apply congrArg (Channel.actionPushforward d)
      funext a
      rfl
    -- η(fun d => mV u_m (push (e_nl·d) along canonIncl)) = η(fun d => mV u_m (push (relabel φ d) along supportInclude(cB m l)))
    rw [show (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml))) =
        (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward (relabelDist φ d)
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) from
      funext (fun d => by rw [hreindex d])]
    -- this equals ζ(fun d' => mV u_m (push d' along supportInclude(cB m l))) with ζ = relabel-transported η
    set ζ : PosteriorLawSigned (supportSubtype (canonBoundary.{u} m l hle_ml)) :=
      (fun ψ => η (fun d => ψ (relabelDist φ d))) with hζdef
    have hζtan : PosteriorLawTangent ζ := by
      refine ⟨?_, ?_⟩
      · show η (fun d => (1:ℝ)) = 0; exact hηtan.1
      · intro a
        show η (fun d => (relabelDist φ d) a) = 0
        have : (fun d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)) => (relabelDist φ d) a) =
            (fun d => d (φ.symm a)) := by funext d; rw [relabelDist_apply]
        rw [this]; exact hηtan.2 _
    -- transport at (m,l) with ζ
    have hT_ml := cardDefect_transport hhm hbranchData hax m l hl2 hlm ζ hζtan
    -- LHS of hT_ml IS our expression (ζ unfolded)
    have hLHS_eq : η (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward (relabelDist φ d)
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) =
        ζ (fun d' => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward d' (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) := rfl
    rw [hLHS_eq, hT_ml]
    -- goal: cardDefect m l · ζ(mV faceML) = cardDefect m l · η(mV faceNL). Need ζ(mV faceML)=η(mV faceNL).
    congr 1
    change relabelPosteriorLawSigned φ η
        (hint.marginalValue F hV
          (canonBoundary.{u} m l hle_ml).restrictToSupport) =
      η (hint.marginalValue F hV
        (canonBoundary.{u} n l hle_ln).restrictToSupport)
    have hfaceML_rel : (canonBoundary.{u} m l hle_ml).restrictToSupport =
        relabelDist φ (canonBoundary.{u} n l hle_ln).restrictToSupport := by
      rw [canonBoundary_face_uniform m l hle_ml, canonBoundary_face_uniform n l hle_ln]
      ext a
      rw [Dist.uniform_apply, relabelDist_apply, Dist.uniform_apply]
      congr 1
      rw [Fintype.card_congr (canonBoundarySupportEquiv m l hle_ml),
        Fintype.card_congr (canonBoundarySupportEquiv n l hle_ln)]
    rw [hfaceML_rel]
    exact finalHM_affineLinearPart_relabel_atomic_eval hhm hax φ
      (canonBoundary.{u} n l hle_ln).restrictToSupport
      hfaceNL_fs η hηatomic hηtan
  -- final cancellation
  have hfin : cardDefect hhm hbranchData hax n l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefect hhm hbranchData hax n m * cardDefect hhm hbranchData hax m l) *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
    rw [hchain1, hbridge]; ring
  have := mul_right_cancel₀ hηnz' (by linarith [hfin] : _ )
  linarith [hfin, mul_right_cancel₀ hηnz'
    (show cardDefect hhm hbranchData hax n l *
        η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefect hhm hbranchData hax n m * cardDefect hhm hbranchData hax m l) *
        η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) from hfin)]

end TraceableAgency
