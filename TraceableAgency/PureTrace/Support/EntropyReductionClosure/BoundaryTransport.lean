/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.RecursionInputs

namespace TraceableAgency

universe u

/-- The selected value representative is coherent with restriction to the
positive support face.  This is the selected-representative version of the old
support-face value normalization. -/
theorem finalHM_supportFaceValueTransport
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O) :
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
        (experimentOfChannel P) =
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
        r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P r)) := by
  change canonicalPosteriorValue
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      r (experimentOfChannel P) =
    canonicalPosteriorValue
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      r.restrictToSupport
      (experimentOfChannel (Channel.restrictToSupport P r))
  exact canonicalPosteriorValue_supportFace hax
    (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax) r P

/-- Selected boundary-value transport for the constructed representative,
packaged in
the branch-aggregation interface that only fixes the representative actually
used downstream. -/
theorem finalHM_boundaryValueTransportFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) :
    FiniteBranchBoundaryValueTransportFor
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax) where
  boundary_value_transport := by
    intro A O _ _ _ _ _ r _ P
    exact finalHM_supportFaceValueTransport hhm hax r P

/-- Boundary linear-part transport from the selected integral representation plus the
support-face marginal-value transport normalization. -/
theorem boundaryLinearPartTransport_of_FinalHM_marginalTransport
    (hhm : FinalHMInterface.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAssumptions
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        hboundary) :
    FiniteBoundaryLinearPartTransportAssumptions
      (affineLinearPart_of_FinalHMInterface hhm)
      hboundary :=
  boundaryLinearPartTransport_of_integralRepresentation
    (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
    hboundary hmarginal

/-- The hax-specific singleton coefficient `β(q,u_A)` satisfies the singleton
scale-factorization clause.  This is the theorem that removes the old selected
singleton scale-factorization normalization once the final route is switched to the
`...For` branch package. -/
theorem finalHMSingletonScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions
        (affineLinearPart_of_FinalHMInterface hhm) hboundary) :
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    let hvalue := finalHM_boundaryValueTransportFor hhm hax
    FiniteBranchScaleFactorizationSingletonNormalization
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  change FiniteBranchScaleFactorizationSingletonNormalization
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
  refine
    { scale_pos_singleton := ?_
      branchCoeff_factorization_singleton := ?_ }
  · intro A _ _ _ q hq _hr_singleton
    show 0 <
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q (Dist.uniform (A := A))
    rw [show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q (Dist.uniform (A := A)) =
        branchCoeffFromTangentRepParts hpath hboundary hsingle q
          (Dist.uniform (A := A)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
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
  · intro A O₁ _ _ _ _ _ q hq P₁ o₁ hpos hsingle_support
    let r : Dist A := Channel.posterior P₁ q o₁
    have hnotnd :
        ¬ ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      exact not_nondegenerate_of_singleton_support r
        (by simpa [r] using hsingle_support)
    have hscale_eq : ∀ s : Dist A,
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).scale s =
          hpath.branchPathCoeff s (Dist.uniform (A := A)) := by
      intro s
      show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff s (Dist.uniform (A := A)) =
          hpath.branchPathCoeff s (Dist.uniform (A := A))
      rw [show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff s (Dist.uniform (A := A)) =
          branchCoeffFromTangentRepParts hpath hboundary hsingle s
            (Dist.uniform (A := A)) from rfl]
      simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
    by_cases hrfull : r.FullSupport
    · have hsub : Subsingleton A := by
        rcases hsingle_support with ⟨c, _hc, huniq⟩
        refine ⟨?_⟩
        intro a b
        exact (huniq a (hrfull a)).trans (huniq b (hrfull b)).symm
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
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale q = 1 := by
        rw [hscale_eq q]
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      have hscale_r_one :
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale r = 1 := by
        rw [hscale_eq r]
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hrfull, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff q (Channel.posterior P₁ q o₁) =
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale q /
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale (Channel.posterior P₁ q o₁)
      rw [show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff q r =
          branchCoeffFromTangentRepParts hpath hboundary hsingle q r from rfl]
      simp only [r, branchCoeffFromTangentRepParts, hrfull, dif_pos]
      rw [hpath_qr_one, hscale_q_one, hscale_r_one]
      norm_num
    · have hpath_r_one :
          hpath.branchPathCoeff r (Dist.uniform (A := A)) = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
        rw [dif_neg hrfull]
      have hbranch_qr :
          (faithfulBranchAggregationStructure_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).branchCoeff q r =
            hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
          rw [show
            (faithfulBranchAggregationStructure_of_componentsFor
              F hax hV hlin hpath hboundary hsingle hvalue hcoeff
            ).branchCoeff q r =
              branchCoeffFromTangentRepParts hpath hboundary hsingle q r from rfl]
          unfold branchCoeffFromTangentRepParts
          rw [dif_neg hrfull]
          rw [dif_neg hnotnd]
          simpa [hsingle] using
            finalHMSingletonScaleNormalizationFor_coeff hhm hax q r
      show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff q (Channel.posterior P₁ q o₁) =
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale q /
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale (Channel.posterior P₁ q o₁)
      rw [show (Channel.posterior P₁ q o₁) = r from rfl]
      rw [hbranch_qr, hscale_eq q, hscale_eq r, hpath_r_one]
      rw [div_one]

/-- Canonical selected boundary coefficient for the final HM route.

For a nondegenerate boundary posterior, the coefficient is fixed to be the
selected tangent path coefficient from the ambient prior to the uniform
basepoint.  This is the normalization under which boundary scale factorization
becomes a theorem rather than a separate normalization field. -/
noncomputable def finalHMBoundaryCoefficientScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) :
    FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u} := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  refine
    { boundaryCoeff := fun {A} _ _ _ q _ =>
        hpath.branchPathCoeff q (Dist.uniform (A := A))
      boundaryCoeff_pos := ?_ }
  intro A _ _ _ q r hq _hr_nonempty hrnd _hr_boundary
  have hU_nd :
      ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
    obtain ⟨a, b, hab, _ha, _hb⟩ := hrnd
    exact ⟨a, b, hab, Dist.uniform_fullSupport a,
      Dist.uniform_fullSupport b⟩
  exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
    hq Dist.uniform_fullSupport hU_nd

/-- Boundary coefficient normalization obtained from the proved atomic
support-face tangent scalar, rather than from the older uniform-path gauge
choice. -/
noncomputable def finalHMBoundaryAtomicCoefficientScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) :
    FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u} :=
  boundaryCoefficientScaleNormalization_of_A1_atomicLinearTangentSpanning
    (affineLinearPart_of_FinalHMInterface hhm)
    (atomicLinearTangentSpanning_of_atomic
      finiteAtomicPosteriorTangentSpanning)
    F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)

/-- Corrected support-face marginal transport for the selected final HM route.

This is the theorem-strength boundary actually proved from A1/A6 and atomic
tangent spanning: the support-face scalar relation is required only for
atomic-linear feasible tangents, which is exactly the domain generated by
continuation experiment differences in the branch formula. -/
structure FinalSupportFaceMarginalValueTransportAtomicFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) : Prop where
  support_face_marginalValue_scalar_atomic :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport)
      (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawSigned.AtomicLinear η →
      PosteriorLawTangent η →
      η (fun d =>
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax) q
          (Channel.actionPushforward d (supportIncludeKernel r))) =
        (boundaryFaceScale_of_coefficientScaleNormalization
          (finalHMBoundaryAtomicCoefficientScaleFor hhm hax)
        ).boundaryCoeff q r *
          η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
            (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            r.restrictToSupport)

/-- The corrected atomic support-face marginal transport is internal to the
final HM route and the paper axioms. -/
theorem finalSupportFaceMarginalValueTransportAtomic_of_FinalHM_PureTraceConditions
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) :
    FinalSupportFaceMarginalValueTransportAtomicFor hhm hax where
  support_face_marginalValue_scalar_atomic := by
    intro A _ _ _ q r hq _ hr_nonempty hr_nondegenerate _hr_boundary η hηatomic hηtan
    classical
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let htangent :=
      atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning
    have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
        0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
      obtain ⟨a, b, hab, ha, hb⟩ := hr_nondegenerate
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
      · intro h
        exact hab (congrArg Subtype.val h)
      · rw [Dist.restrictToSupport_apply]
        exact ha
      · rw [Dist.restrictToSupport_apply]
        exact hb
    have hrel :=
      boundaryAtomicLinearTangentCoeffOfA1Spanning_relation
        hlin htangent F hax hV q r hq hrs_nd η hηatomic hηtan
    simpa [hlin, hV, htangent, finalHMBoundaryAtomicCoefficientScaleFor,
      affineLinearPart_of_FinalHMInterface,
      boundaryFaceScale_of_coefficientScaleNormalization,
      boundaryCoefficientScaleNormalization_of_A1_atomicLinearTangentSpanning,
      finiteAffineLinearPartAssumptions_of_integralRepresentation]
      using hrel

/-- Repackage the selected atomic transport theorem under the lower-level
fixed-representative interface. -/
theorem supportFaceMarginalValueTransportAtomic_of_FinalHMFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (htransport : FinalSupportFaceMarginalValueTransportAtomicFor hhm hax) :
    FiniteSupportFaceMarginalValueTransportAtomicFor
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization
        (finalHMBoundaryAtomicCoefficientScaleFor hhm hax)) where
  support_face_marginalValue_scalar_atomic := by
    intro A _ _ _ q r hq _ hrn hrnd hrb η hηatomic hηtan
    exact htransport.support_face_marginalValue_scalar_atomic
      q r hq hrn hrnd hrb η hηatomic hηtan

/-- The theorem-strength support-face marginal transport required by the
canonical selected branch route.

Unlike the old normalization bundle, this fixes the boundary coefficient
internally to `finalHMBoundaryCoefficientScaleFor`.  The remaining content is
the actual support-face scalar theorem for the HM marginal test function. -/
structure FinalSupportFaceMarginalValueTransportFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) : Prop where
  support_face_marginalValue_scalar :
    ∀ (F' : PrefFamily.{u}) (hax' : PureTraceConditions F')
      (hV' : PosteriorValueRepresentation F')
      {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport)
      (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawTangent η →
      η (fun d =>
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F'
          hV' q
          (Channel.actionPushforward d (supportIncludeKernel r))) =
        (boundaryFaceScale_of_coefficientScaleNormalization
          (finalHMBoundaryCoefficientScaleFor hhm hax)
        ).boundaryCoeff q r *
          η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F'
            hV' r.restrictToSupport)

/-- Repackage the canonical selected marginal-transport theorem under the
historical interface consumed by the lower-level branch constructors. -/
theorem supportFaceMarginalValueTransport_of_FinalHMFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (htransport : FinalSupportFaceMarginalValueTransportFor hhm hax) :
    FiniteSupportFaceMarginalValueTransportAssumptions
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization
        (finalHMBoundaryCoefficientScaleFor hhm hax)) where
  support_face_marginalValue_scalar := by
    intro F' hax' hV' A _ _ _ q r hq _ hrn hrnd hrb η hη
    exact htransport.support_face_marginalValue_scalar
      F' hax' hV' q r hq hrn hrnd hrb η hη

/-- Boundary scale factorization for the canonical selected boundary
coefficient.

Once the boundary coefficient is fixed as the tangent coefficient to the
uniform basepoint, the boundary case of branch scale factorization is just the
definition of the full-support base scale; no separate boundary-scale
normalization is needed. -/
theorem finalHMBoundaryScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (htransport : FinalSupportFaceMarginalValueTransportFor hhm hax) :
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        (finalHMBoundaryCoefficientScaleFor hhm hax)
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    let hvalue := finalHM_boundaryValueTransportFor hhm hax
    let hmarginal :=
      supportFaceMarginalValueTransport_of_FinalHMFor
        hhm hax htransport
    let hcoeff :=
      boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
        (boundaryLinearPartTransport_of_FinalHM_marginalTransport
          hhm hboundary hmarginal)
    FiniteBranchScaleFactorizationBoundaryTransportAssumptions
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff) := by
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
      (finalHMBoundaryCoefficientScaleFor hhm hax)
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  let hmarginal :=
    supportFaceMarginalValueTransport_of_FinalHMFor
      hhm hax htransport
  let hcoeff :=
    boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
      (boundaryLinearPartTransport_of_FinalHM_marginalTransport
        hhm hboundary hmarginal)
  change FiniteBranchScaleFactorizationBoundaryTransportAssumptions
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
  refine ⟨?_⟩
  intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hrnd hrb
  let r : Dist A := Channel.posterior P₁ q o₁
  have hscale_eq : ∀ s : Dist A,
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).scale s =
        hpath.branchPathCoeff s (Dist.uniform (A := A)) := by
    intro s
    show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff s (Dist.uniform (A := A)) =
        hpath.branchPathCoeff s (Dist.uniform (A := A))
    rw [show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff s (Dist.uniform (A := A)) =
        branchCoeffFromTangentRepParts hpath hboundary hsingle s
          (Dist.uniform (A := A)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  have hpath_r_one :
      hpath.branchPathCoeff r (Dist.uniform (A := A)) = 1 := by
    simp only [hpath,
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
    rw [dif_neg (by simpa [r] using hrb)]
  have hbranch_qr :
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q r =
        hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
    rw [show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q r =
        branchCoeffFromTangentRepParts hpath hboundary hsingle q r from rfl]
    unfold branchCoeffFromTangentRepParts
    rw [dif_neg (by simpa [r] using hrb)]
    rw [dif_pos (by simpa [r] using hrnd)]
    rfl
  show
    (faithfulBranchAggregationStructure_of_componentsFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
    ).branchCoeff q (Channel.posterior P₁ q o₁) =
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).scale q /
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).scale (Channel.posterior P₁ q o₁)
  rw [show (Channel.posterior P₁ q o₁) = r from rfl]
  rw [hbranch_qr, hscale_eq q, hscale_eq r, hpath_r_one, div_one]

/-- Faithful branch package with the internal HM/finite-linear-algebra fields
filled automatically.

The remaining inputs are exactly the boundary/support representative choices
and the boundary/singleton scale-factorization transports.  This exposes more
of the proof order than passing an opaque `FiniteFaithfulBranchAggregationAssumptions`
bundle. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_components
    (hhm : FinalHMInterface.{u})
    (hatomic : FiniteAtomicPosteriorTangentSpanningAssumptions.{u})
    (hsupportFace : FiniteSupportFaceRepresentativeTransportAssumptions.{u})
    (hboundaryCoeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAssumptions
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        (boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff))
    (hboundaryScale :
      ∀ (F : PrefFamily.{u}) (hax : PureTraceConditions F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic hatomic) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationBoundaryTransportAssumptions
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff))
    (hsingleScale :
      ∀ (F : PrefFamily.{u}) (hax : PureTraceConditions F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic hatomic) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationSingletonNormalization
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    FiniteFaithfulBranchAggregationAssumptions.{u} where
  linear_part := affineLinearPart_of_FinalHMInterface hhm
  tangent_spanning := atomicLinearTangentSpanning_of_atomic hatomic
  same_sign_scalar := finiteLinearFunctionalSameSignScalarOnTangent_of_direct
  support_face_rep := hsupportFace
  boundary_coeff_scale := hboundaryCoeff
  singleton_scale := hsingle
  boundary_linear_transport :=
    boundaryLinearPartTransport_of_FinalHM_marginalTransport
      hhm (boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff)
      hmarginal
  boundary_scale_factorization := hboundaryScale
  singleton_scale_factorization := hsingleScale

/-- Faithful branch package from the final construction interface and explicit
support/boundary normalizations, with finite atomic tangent spanning discharged by
the internal theorem `finiteAtomicPosteriorTangentSpanning`. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_normalizations
    (hhm : FinalHMInterface.{u})
    (hsupportFace : FiniteSupportFaceRepresentativeTransportAssumptions.{u})
    (hboundaryCoeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAssumptions
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        (boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff))
    (hboundaryScale :
      ∀ (F : PrefFamily.{u}) (hax : PureTraceConditions F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic
              finiteAtomicPosteriorTangentSpanning) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationBoundaryTransportAssumptions
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff))
    (hsingleScale :
      ∀ (F : PrefFamily.{u}) (hax : PureTraceConditions F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic
              finiteAtomicPosteriorTangentSpanning) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationSingletonNormalization
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    FiniteFaithfulBranchAggregationAssumptions.{u} :=
  faithfulBranchAggregationAssumptions_of_FinalHM_components
    hhm finiteAtomicPosteriorTangentSpanning
    hsupportFace hboundaryCoeff hsingle hmarginal
    hboundaryScale hsingleScale

/-- Legacy explicit boundary/scale data used by the pre-canonical route.

Unlike the final route, this structure asks for representative transport and
scale choices explicitly.  It is retained only for intermediate compatibility
and is not an assumption of `MIRep_of_PureTraceConditions_FinalHM_Faddeev` or the public
main theorem. -/
structure FinalFaithfulBranchData
    (hhm : FinalHMInterface.{u}) where
  support_face : FiniteSupportFaceRepresentativeTransportAssumptions.{u}
  singleton_scale : FiniteBranchSingletonScaleNormalizationAssumptions.{u}
  boundary_coeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u}
  marginal_value :
    FiniteSupportFaceMarginalValueTransportAssumptions
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff)
  boundary_scale :
    ∀ (F : PrefFamily.{u}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F),
      let hlin := affineLinearPart_of_FinalHMInterface hhm
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
          (atomicLinearTangentSpanning_of_atomic
            finiteAtomicPosteriorTangentSpanning) F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport
          support_face
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalTransport
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)
  singleton_scale_factorization :
    ∀ (F : PrefFamily.{u}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F),
      let hlin := affineLinearPart_of_FinalHMInterface hhm
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
          (atomicLinearTangentSpanning_of_atomic
            finiteAtomicPosteriorTangentSpanning) F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport
          support_face
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalTransport
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationSingletonNormalization
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)

/-- Producer from the explicit faithful-branch normalization bundle. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_data
    (hhm : FinalHMInterface.{u})
    (hnorm : FinalFaithfulBranchData hhm) :
    FiniteFaithfulBranchAggregationAssumptions.{u} :=
  faithfulBranchAggregationAssumptions_of_FinalHM_normalizations
    hhm
    hnorm.support_face
    hnorm.boundary_coeff hnorm.singleton_scale
    hnorm.marginal_value hnorm.boundary_scale
    hnorm.singleton_scale_factorization

/-- HM-specific faithful branch normalizations with support-face value transport
internalised.

This is the selected-representative counterpart of
`FinalFaithfulBranchData`: it fixes the boundary value transport only for
the HM representative being assembled, via `finalHM_boundaryValueTransportFor`. -/
structure FinalFaithfulBranchDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) where
  boundary_coeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u}
  marginal_value :
    FiniteSupportFaceMarginalValueTransportAssumptions
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff)
  boundary_scale :
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff
    let hvalue := finalHM_boundaryValueTransportFor hhm hax
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalTransport
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary
            (finalHMSingletonScaleNormalizationFor hhm hax) hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary
            (finalHMSingletonScaleNormalizationFor hhm hax) hvalue hcoeff)

/-- Selected faithful branch data with the corrected atomic support-face
marginal theorem.

This is the branch datum that is actually constructed from pure-trace
nontriviality, finite-branch continuation, and the HM interface.  It does not
contain the old arbitrary-`PosteriorLawTangent`
support-face transport convention. -/
structure FinalFaithfulBranchAtomicDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) where
  boundary_coeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u}
  marginal_value :
    FiniteSupportFaceMarginalValueTransportAtomicFor
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff)

/-- Internal constructor for the selected atomic branch datum. -/
noncomputable def finalFaithfulBranchAtomicDataFor_of_FinalHM_PureTraceConditions
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) :
    FinalFaithfulBranchAtomicDataFor hhm hax where
  boundary_coeff := finalHMBoundaryAtomicCoefficientScaleFor hhm hax
  marginal_value :=
    supportFaceMarginalValueTransportAtomic_of_FinalHMFor
      hhm hax
      (finalSupportFaceMarginalValueTransportAtomic_of_FinalHM_PureTraceConditions
        hhm hax)

/-- Selected branch aggregation structure assembled directly from the atomic
support-face theorem.  This bypasses the historical boundary-coefficient
transport route, whose support-face input quantified over arbitrary extensional
tangents. -/
noncomputable def faithfulBranchAggregationStructure_of_atomicDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    BranchAggregationStructure F :=
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
  branchAggregationStructure_of_tangentFormulaFor
    F hax hV hlin hpath hboundary hsingle hformula

/-- Known-result boundary input for the selected faithful branch route.

The boundary coefficient and boundary scale factorization are now constructed
internally.  The only remaining branch input is the support-face scalar theorem
for the HM marginal-value test function, expressed relative to the canonical
coefficient `finalHMBoundaryCoefficientScaleFor`. -/
structure FinalFaithfulBranchKnownResultsFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) : Prop where
  marginal_transport : FinalSupportFaceMarginalValueTransportFor hhm hax

/-- Convert the known-result branch input into the legacy internal bundle
consumed by existing constructors. -/
noncomputable def finalFaithfulBranchDataFor_of_knownResults
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hknown : FinalFaithfulBranchKnownResultsFor hhm hax) :
    FinalFaithfulBranchDataFor hhm hax where
  boundary_coeff := finalHMBoundaryCoefficientScaleFor hhm hax
  marginal_value :=
    supportFaceMarginalValueTransport_of_FinalHMFor
      hhm hax hknown.marginal_transport
  boundary_scale :=
    finalHMBoundaryScaleFactorizationFor hhm hax
      hknown.marginal_transport

/-- Selected faithful branch/cocycle/chain result from the HM-specific branch
bundle. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hnorm : FinalFaithfulBranchDataFor hhm hax) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hnorm.boundary_coeff
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
    let hcoeff :=
      boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
        (boundaryLinearPartTransport_of_FinalHM_marginalTransport
          hhm hboundary hnorm.marginal_value)
    BranchAggregationCocycleNormalizedChainRule_of_componentsFor
      F hax hV hlin hpath hboundary
        (finalHMSingletonScaleNormalizationFor hhm hax) hvalue hcoeff
      hnorm.boundary_scale
      (finalHMSingletonScaleFactorizationFor
        hhm hax hboundary hcoeff)

/-- Selected-branch scale relabelling from selected-representative covariance.

This is the hax-specific counterpart of `scaleRelabel_of_FinalHM_covariance`.
It uses the selected singleton scale and the theorem-produced singleton
factorization, so no hax-free singleton normalization is needed. -/
theorem scaleRelabel_of_FinalHM_covarianceFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).scale_factorization.scale (Relabeling.relabelDist e q) =
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
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
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  let hcoeff :=
    boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
      (boundaryLinearPartTransport_of_FinalHM_marginalTransport
        hhm hboundary hbranchData.marginal_value)
  have hscale_eq :
      ∀ (C : Type u) [Fintype C] [DecidableEq C] [Nonempty C] (s : Dist C),
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
          hhm hax hbranchData
        ).scale_factorization.scale s =
          hpath.branchPathCoeff s (Dist.uniform (A := C)) := by
    intro C _ _ _ s
    show
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
        hhm hax hbranchData
      ).branch_agg.branchCoeff s (Dist.uniform (A := C)) =
        hpath.branchPathCoeff s (Dist.uniform (A := C))
    rw [show
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
        hhm hax hbranchData
      ).branch_agg.branchCoeff s (Dist.uniform (A := C)) =
        branchCoeffFromTangentRepParts hpath hboundary hsingle s
          (Dist.uniform (A := C)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  rw [hscale_eq B (Relabeling.relabelDist e q), hscale_eq A q]
  have huni :
      Relabeling.relabelDist e (Dist.uniform (A := A)) =
        Dist.uniform (A := B) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply,
      Dist.uniform_apply, Fintype.card_congr e]
  by_cases hA : Subsingleton A
  · have hqfsB : (Relabeling.relabelDist e q).FullSupport :=
      Relabeling.relabelDist_fullSupport e q hq
    have h1A : hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      have hnn :
          ¬ ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
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
          ¬ ∃ a b : B, a ≠ b ∧ 0 < (Dist.uniform (A := B)) a ∧
            0 < (Dist.uniform (A := B)) b := by
        rintro ⟨a, b, hab, _, _⟩
        exact hab (Subsingleton.elim a b)
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hqfsB, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    rw [h1B, h1A]
  · have hndU :
        ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
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

/-- Positivity of the selected faithful chain scale for every finite prior. -/
theorem faithful_scale_posFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 < (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
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
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  show 0 <
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff q (Dist.uniform (A := A))
  rw [show
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff q (Dist.uniform (A := A)) =
      branchCoeffFromTangentRepParts hpath hboundary hsingle q
        (Dist.uniform (A := A)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  by_cases hqfs : q.FullSupport
  · by_cases hnd :
        ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b
    · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
        hqfs Dist.uniform_fullSupport hnd
    · have hpath_eq :
          hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hqfs, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hnd]
      rw [hpath_eq]
      exact one_pos
  · have hpath_eq :
        hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
      rw [dif_neg hqfs]
    rw [hpath_eq]
    exact one_pos

/-- The selected faithful chain scale of a nondegenerate uniform prior is `1`. -/
theorem scale_uniform_eq_oneFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (hnd : ∃ a b : A, a ≠ b) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
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
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  show
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) = 1
  rw [show
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) =
      branchCoeffFromTangentRepParts hpath hboundary hsingle
        (Dist.uniform (A := A)) (Dist.uniform (A := A)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
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

/-- **R1: raw chain-scale relabelling invariance from selected covariance.**

The faithful branch chain scale is `scale q = branchCoeff q u_A` (the branch
coefficient to the uniform prior).  Relabelling carries `u_A` to `u_B`
(`Fintype.card_congr`), the full-support branch coefficient equals the tangent
scalar `branchPathCoeff`, and `branchPathCoeff` is relabel-invariant
(`branchPathCoeff_relabel_of_atomic_eval`).  On a subsingleton action
type both coefficients are the degenerate value `1`.  This discharges the raw
form of the `scale_relabel` gauge normalization (under the constant gauge). -/
theorem scaleRelabel_of_FinalHM_covariance
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Relabeling.relabelDist e q) =
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale q := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
    with hfaith_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
    with hpath_def
  have hscale_eq : ∀ (C : Type u) [Fintype C] [DecidableEq C] [Nonempty C] (s : Dist C),
      (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).scale_factorization.scale s =
      hpath.branchPathCoeff s (Dist.uniform (A := C)) := by
    intro C _ _ _ s
    show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).branch_agg.branchCoeff s (Dist.uniform (A := C)) = _
    rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff s (Dist.uniform (A := C)) =
      branchCoeffFromTangentRepParts hpath
        (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
        hfaith.singleton_scale s (Dist.uniform (A := C)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  rw [hscale_eq B (Relabeling.relabelDist e q), hscale_eq A q]
  have huni : Relabeling.relabelDist e (Dist.uniform (A := A)) = Dist.uniform (A := B) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply, Fintype.card_congr e]
  by_cases hA : Subsingleton A
  · have hqfsB : (Relabeling.relabelDist e q).FullSupport :=
      Relabeling.relabelDist_fullSupport e q hq
    have h1A : hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      have hnn : ¬ ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hab, _, _⟩; exact hab (Subsingleton.elim a b)
      rw [hpath_def]
      simp only [branchPathTangentScalarStructure_of_faithfulAssumptions,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hq, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    have h1B : hpath.branchPathCoeff (Relabeling.relabelDist e q) (Dist.uniform (A := B)) = 1 := by
      have hnn : ¬ ∃ a b : B, a ≠ b ∧ 0 < (Dist.uniform (A := B)) a ∧
          0 < (Dist.uniform (A := B)) b := by
        haveI : Subsingleton B := Equiv.subsingleton e.symm
        rintro ⟨a, b, hab, _, _⟩; exact hab (Subsingleton.elim a b)
      rw [hpath_def]
      simp only [branchPathTangentScalarStructure_of_faithfulAssumptions,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hqfsB, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    rw [h1B, h1A]
  · have hndU : ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
      rw [not_subsingleton_iff_nontrivial] at hA
      obtain ⟨a, b, hab⟩ := hA
      exact ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
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
      hpath e q
      (Dist.uniform (A := A)) hq Dist.uniform_fullSupport hndU

end TraceableAgency
