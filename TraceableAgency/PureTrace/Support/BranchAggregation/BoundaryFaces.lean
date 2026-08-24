/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.PathScalars

namespace TraceableAgency

universe u v

/-!
## Boundary and singleton branch interfaces

For literal singleton action types, the zero-value branch claim is structural:
all posterior laws are the same and the zero-normalised no-information value is
zero.  Singleton supports inside a larger ambient action set still require
support-face identification, so they are kept as a separate normalization/interface.
-/

/-- Branch-local copy of the singleton distribution collapse theorem. -/
theorem branchDist_eq_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Subsingleton A]
    (q q' : Dist A) : q = q' := by
  ext a
  have huniq : ∀ b : A, b = a := fun b => Subsingleton.elim b a
  have hq : q a = ∑ b : A, q b :=
    (Finset.sum_eq_single a (fun b _ hba => absurd (huniq b) hba)
      (fun h => absurd (Finset.mem_univ a) h)).symm
  have hq' : q' a = ∑ b : A, q' b :=
    (Finset.sum_eq_single a (fun b _ hba => absurd (huniq b) hba)
      (fun h => absurd (Finset.mem_univ a) h)).symm
  linarith [q.sum_eq_one, q'.sum_eq_one]

/-- On a singleton action type, every experiment posterior equals the prior. -/
theorem branchPosterior_eq_prior_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E : FiniteExperimentOn A) (o : E.OutcomeType) :
    @FiniteExperimentOn.posterior A _ _ _ E q o = q :=
  branchDist_eq_of_subsingleton _ _

/-- On a singleton action type, posterior-law integrals collapse to evaluation
at the prior. -/
theorem posteriorLawIntegralExp_singleton_branch
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E : FiniteExperimentOn A) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q E φ = φ q := by
  unfold posteriorLawIntegralExp
  have hpost : ∀ o : E.OutcomeType,
      @FiniteExperimentOn.posterior A _ _ _ E q o = q :=
    branchPosterior_eq_prior_of_subsingleton q E
  simp_rw [hpost]
  letI := E.outFintype
  have hmarg_sum : (∑ o : E.OutcomeType, (E.outcomeMarginal q) o) = 1 :=
    (E.outcomeMarginal q).sum_eq_one
  rw [← Finset.sum_mul, hmarg_sum, one_mul]

/-- On a singleton action type, all experiments induce the same posterior law. -/
theorem samePosteriorLawExp_of_subsingleton_branch
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    SamePosteriorLawExp q E E' := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_singleton_branch q E φ,
    posteriorLawIntegralExp_singleton_branch q E' φ]

/-- On a singleton action type, every posterior value is zero. -/
theorem branchValue_eq_zero_of_subsingleton
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A) :
    hV.V q E = 0 := by
  have heq : hV.V q E =
      hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) :=
    hV.respects_same_posterior_law q E
      (experimentOfChannel (Channel.uninformativeChannelU A))
      (samePosteriorLawExp_of_subsingleton_branch q E _)
  rw [heq, hV.zero_normalized q hq]

/-- Channel version of `branchValue_eq_zero_of_subsingleton`. -/
theorem branchValue_channel_eq_zero_of_subsingleton
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    hV.V q (experimentOfChannel P) = 0 :=
  branchValue_eq_zero_of_subsingleton F hV q hq (experimentOfChannel P)

/-- Boundary face-scale interface for non-full-support, non-singleton branch
posteriors.

This is the paper's full-to-face coefficient step: continuation values and
linear parts at a boundary posterior are interpreted intrinsically on the
positive support face, and the ambient branch coefficient is a positive scalar
relating the ambient prior linear part to the face representative. -/
structure FiniteBranchBoundaryFaceScaleAssumptions where
  boundaryCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  boundaryCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      0 < boundaryCoeff q r

/-- Boundary value transport interface.

Support restriction proves posterior-law and preference transport.  The branch
aggregation boundary case also needs the chosen value representatives to agree
between the ambient boundary prior and the intrinsic full-support prior on the
positive support face. -/
structure FiniteBranchBoundaryValueTransportAssumptions where
  boundary_value_transport :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV.V r (experimentOfChannel P) =
        hV.V r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P r))

/-- Boundary value transport for a fixed representative.

This is the theorem-strength interface used by the selected HM route.  The old
`FiniteBranchBoundaryValueTransportAssumptions` is stronger: it asks for the
same equality for every representative, which is a representative normalization
rather than a consequence of the integral HM construction. -/
structure FiniteBranchBoundaryValueTransportFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) : Prop where
  boundary_value_transport :
    ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV.V r (experimentOfChannel P) =
        hV.V r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P r))

/-- The historical universal boundary-value package specializes to any fixed
representative. -/
theorem boundaryValueTransportFor_of_boundaryValueTransport
    (hvalue : FiniteBranchBoundaryValueTransportAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBranchBoundaryValueTransportFor F hax hV where
  boundary_value_transport := hvalue.boundary_value_transport F hax hV

/-- Explicit normalization that representatives on a boundary face are chosen
coherently with the intrinsic positive-support representative.

This is a renamed/classified version of boundary value transport.  It is not a
posterior-law theorem: the equality crosses from the ambient boundary prior to
the intrinsic support-face prior. -/
structure FiniteSupportFaceRepresentativeTransportAssumptions where
  support_face_value_transport :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV.V r (experimentOfChannel P) =
        hV.V r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P r))

/-- Boundary value transport is exactly the support-face representative
normalization, packaged under the historical name. -/
theorem boundaryValueTransport_of_supportFaceRepresentativeTransport
    (hface : FiniteSupportFaceRepresentativeTransportAssumptions.{u}) :
    FiniteBranchBoundaryValueTransportAssumptions.{u} where
  boundary_value_transport := hface.support_face_value_transport

/-- Explicit normalization choosing positive boundary branch coefficients. -/
structure FiniteBoundaryCoefficientScaleNormalizationAssumptions where
  boundaryCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  boundaryCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      0 < boundaryCoeff q r

/-- Boundary face-scale coefficients are the packaged boundary coefficient
choice normalization. -/
def boundaryFaceScale_of_coefficientScaleNormalization
    (hcoeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u}) :
    FiniteBranchBoundaryFaceScaleAssumptions.{u} where
  boundaryCoeff := hcoeff.boundaryCoeff
  boundaryCoeff_pos := hcoeff.boundaryCoeff_pos

/-- Boundary coefficient transport interface.

This is the scalar relation missing after pure support restriction: the ambient
linear part at `q` applied to a support-face tangent direction is a positive
multiple of the intrinsic support-face linear part. -/
structure FiniteBranchBoundaryCoefficientTransportAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  boundary_linear_part_scalar :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport)
      (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawTangent η →
      hlin.linearPart F hV q
          (fun φ => η (fun d =>
            φ (Channel.actionPushforward d (supportIncludeKernel r)))) =
        hboundary.boundaryCoeff q r *
          hlin.linearPart F hV r.restrictToSupport η

/-- Support-face linear-part transport bridge.

**Paper role**: with the integral representation `L_q(η) = η(φ_q)`, this asserts
`η(φ_q ∘ incl) = boundaryCoeff(q,r) · η(φ_{r.restrictToSupport})` for support-face
tangents `η : PosteriorLawSigned (supportSubtype r)`, where `incl : supportSubtype r → Dist A`
is the canonical inclusion.  Equivalently: `φ_q ∘ incl = boundaryCoeff(q,r) · φ_{r.restrictToSupport}`
as functions on `supportSubtype r`.

**External mathematical status**: this is a theorem about how the ambient marginal
value function `φ_q` restricts to the support face.  It follows from the branch
aggregation formula at the boundary (the value of a boundary-prior experiment
equals the support-face value), which is established in the paper at lines
corresponding to the boundary support-restriction argument.  Formalizing this
transport in Lean requires connecting the branch aggregation formula to the
integral representation, which is out of scope for the current development.

This has definite mathematical content rather than merely fixing representatives.
The positive boundary coefficient `boundaryCoeff(q,r)` is separately chosen by
`FiniteBoundaryCoefficientScaleNormalizationAssumptions`, but the scalar transport
equation itself is a theorem. -/
structure FiniteBoundaryLinearPartTransportAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  boundary_linear_part_scalar :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport)
      (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawTangent η →
      hlin.linearPart F hV q
          (fun φ => η (fun d =>
            φ (Channel.actionPushforward d (supportIncludeKernel r)))) =
        hboundary.boundaryCoeff q r *
          hlin.linearPart F hV r.restrictToSupport η

/-- Support-face marginal-value transport normalization for the HM integral
representatives.

Once Herstein--Milnor supplies an integral representative
`L_q(η) = η (φ_q)`, boundary linear-part transport is exactly the statement
that the ambient marginal test function restricted to the support face agrees,
up to the selected boundary coefficient, with the intrinsic support-face
marginal test function.  This structure records that representative
normalisation directly at the level of test functions, rather than hiding it as
a generic linear-part assumption. -/
structure FiniteSupportFaceMarginalValueTransportAssumptions
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  support_face_marginalValue_scalar :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport)
      (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawTangent η →
      η (fun d =>
        hint.marginalValue F hV q
          (Channel.actionPushforward d (supportIncludeKernel r))) =
        hboundary.boundaryCoeff q r *
          η (hint.marginalValue F hV r.restrictToSupport)

/-- Corrected support-face marginal-value transport for the actual boundary
domain used by the branch formula.

Boundary branch summands only apply the support-face transport theorem to
posterior-law differences on the positive face.  Those signed laws are
atomic-linear feasible tangents.  This hax-specific interface records exactly
that theorem boundary, avoiding the stronger and generally unjustified
arbitrary-`PosteriorLawTangent` transport convention. -/
structure FiniteSupportFaceMarginalValueTransportAtomicFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u}) : Prop where
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
        hint.marginalValue F hV q
          (Channel.actionPushforward d (supportIncludeKernel r))) =
        hboundary.boundaryCoeff q r *
          η (hint.marginalValue F hV r.restrictToSupport)

/-- Integral representatives plus support-face marginal-value transport
reconstruct the historical boundary linear-part transport interface. -/
theorem boundaryLinearPartTransport_of_integralRepresentation
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (htransport :
      FiniteSupportFaceMarginalValueTransportAssumptions.{u}
        hint hboundary) :
    FiniteBoundaryLinearPartTransportAssumptions.{u}
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint)
      hboundary where
  boundary_linear_part_scalar := by
    intro F hax hV A _ _ _ q r hq _ hnonempty hnondeg hboundary' η hη
    exact htransport.support_face_marginalValue_scalar
      F hax hV q r hq hnonempty hnondeg hboundary' η hη

/-- Repackage support-face linear-part transport as the historical boundary
coefficient transport interface. -/
theorem boundaryCoefficientTransport_of_linearPartTransport
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (htransport :
      FiniteBoundaryLinearPartTransportAssumptions.{u} hlin hboundary) :
    FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary where
  boundary_linear_part_scalar := htransport.boundary_linear_part_scalar

/-- Boundary branch summand interface for the formula bridge.

This is narrower than the full branch aggregation formula: it states only the
single boundary-branch contribution after support-face value and coefficient
transport have been supplied. -/
structure FiniteBranchFormulaBoundarySummandAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  boundary_summand_linearPart_eq :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A O₁ O₂ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (_hr_nonempty : ∃ a : A, 0 < (branchPosterior P₁ q target) a)
      (_hr_nondegenerate :
        ∃ a b : A, a ≠ b ∧
          0 < (branchPosterior P₁ q target) a ∧
          0 < (branchPosterior P₁ q target) b)
      (_hr_boundary : ¬ (branchPosterior P₁ q target).FullSupport)
      (Q : Channel A O₂),
      hlin.linearPart F hV q
        (posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
          (posteriorLawDifferenceExp (branchPosterior P₁ q target)
            (experimentOfChannel Q)
            (experimentOfChannel (Channel.uninformativeChannelU A)))) =
        (Channel.outcomeMarginal P₁ q) target *
          hboundary.boundaryCoeff q (branchPosterior P₁ q target) *
          hV.V (branchPosterior P₁ q target) (experimentOfChannel Q)

/-- Hax-aware boundary branch summand package.

This is the faithful version of the boundary summand bridge: the proof from
support-face value transport requires `PureTraceConditions F`, so the older hax-free
`FiniteBranchFormulaBoundarySummandAssumptions` is too strong as a derived
target. -/
structure FiniteBranchFormulaBoundarySummandFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u}) : Prop where
  boundary_summand_linearPart_eq :
    ∀ {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (_hr_nonempty : ∃ a : A, 0 < (branchPosterior P₁ q target) a)
      (_hr_nondegenerate :
        ∃ a b : A, a ≠ b ∧
          0 < (branchPosterior P₁ q target) a ∧
          0 < (branchPosterior P₁ q target) b)
      (_hr_boundary : ¬ (branchPosterior P₁ q target).FullSupport)
      (Q : Channel A O₂),
      hlin.linearPart F hV q
        (posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
          (posteriorLawDifferenceExp (branchPosterior P₁ q target)
            (experimentOfChannel Q)
            (experimentOfChannel (Channel.uninformativeChannelU A)))) =
        (Channel.outcomeMarginal P₁ q) target *
          hboundary.boundaryCoeff q (branchPosterior P₁ q target) *
          hV.V (branchPosterior P₁ q target) (experimentOfChannel Q)

/-- The ambient posterior-law difference at a boundary prior is the
push-forward of the intrinsic support-face posterior-law difference. -/
theorem posteriorLawDifferenceExp_restrictToSupport_pushforward
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)] (Q : Channel A O)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp r
        (experimentOfChannel Q)
        (experimentOfChannel (Channel.uninformativeChannelU A)) φ =
      posteriorLawDifferenceExp r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := by
  unfold posteriorLawDifferenceExp
  have hQ :
      posteriorLawIntegralExp r (experimentOfChannel Q) φ =
        posteriorLawIntegralExp r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport Q r))
          (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := by
    rw [posteriorLawIntegralExp_experimentOfChannel]
    rw [posteriorLawIntegralExp_experimentOfChannel]
    exact posteriorLawIntegral_restrictToSupport Q r φ
  have hU_ambient :
      posteriorLawIntegralExp r
          (experimentOfChannel (Channel.uninformativeChannelU A)) φ =
        φ r :=
    posteriorLawIntegralExp_uninformativeChannelU_eq_prior r φ
  have hU_face :
      posteriorLawIntegralExp r.restrictToSupport
          (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))
          (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) =
        φ r := by
    rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior]
    rw [actionPushforward_restrict_include r]
  rw [hQ, hU_ambient, hU_face]

/-- Extend a channel on the positive support face to the ambient action type.
Rows outside the support are behaviourally irrelevant under prior `r`, so they
are filled with an arbitrary support row. -/
noncomputable def supportExtendChannel
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] (r : Dist A) [Nonempty (supportSubtype r)]
    (P : Channel (supportSubtype r) O) : Channel A O :=
  fun a => if h : 0 < r a then P ⟨a, h⟩ else P (Classical.choice inferInstance)

/-- Restricting the support extension recovers the original face channel. -/
@[simp] theorem restrictToSupport_supportExtendChannel
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] (r : Dist A) [Nonempty (supportSubtype r)]
    (P : Channel (supportSubtype r) O) :
    Channel.restrictToSupport (supportExtendChannel r P) r = P := by
  funext a
  ext o
  simp [supportExtendChannel, Channel.restrictToSupport, a.2]

/-- Positive support of the left block prior is canonically the support of the
underlying prior. -/
noncomputable def supportInlDistEquiv
    {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) :
    supportSubtype r ≃
      supportSubtype (inlDist (B := A) r : Dist (A ⊕ A)) where
  toFun a := ⟨Sum.inl a.1, by simpa using a.2⟩
  invFun x :=
    match hx : x.1 with
    | Sum.inl a =>
        ⟨a, by
          have hxpos : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inl a) > 0 := by
            simpa [hx] using x.2
          simpa using hxpos⟩
    | Sum.inr a =>
        False.elim (by
          have hxpos : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) > 0 := by
            simpa [hx] using x.2
          have hzero : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) = 0 := rfl
          exact (lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
  left_inv := by
    intro a
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    cases x with
    | mk x hx =>
        cases x with
        | inl a =>
            apply Subtype.ext
            rfl
        | inr a =>
            have hxpos : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) > 0 := hx
            have hzero : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) = 0 := rfl
            exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))

/-- Positive support of the right block prior is canonically the support of the
underlying prior. -/
noncomputable def supportInrDistEquiv
    {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) :
    supportSubtype r ≃
      supportSubtype (inrDist (A := A) r : Dist (A ⊕ A)) where
  toFun a := ⟨Sum.inr a.1, by simpa using a.2⟩
  invFun x :=
    match hx : x.1 with
    | Sum.inl a =>
        False.elim (by
          have hxpos : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) > 0 := by
            simpa [hx] using x.2
          have hzero : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) = 0 := rfl
          exact (lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
    | Sum.inr a =>
        ⟨a, by
          have hxpos : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inr a) > 0 := by
            simpa [hx] using x.2
          simpa using hxpos⟩
  left_inv := by
    intro a
    apply Subtype.ext
    rfl
  right_inv := by
    intro x
    cases x with
    | mk x hx =>
        cases x with
        | inl a =>
            have hxpos : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) > 0 := hx
            have hzero : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) = 0 := rfl
            exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
        | inr a =>
            apply Subtype.ext
            rfl

/-- The support of the two boundary block priors is the sum of the intrinsic
support face with itself. -/
noncomputable def supportBoundarySumEquiv
    {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) :
    (supportSubtype r ⊕ supportSubtype r) ≃
      (supportSubtype (inlDist (B := A) r : Dist (A ⊕ A)) ⊕
        supportSubtype (inrDist (A := A) r : Dist (A ⊕ A))) :=
  Equiv.sumCongr (supportInlDistEquiv r) (supportInrDistEquiv r)

@[simp]
theorem relabelDist_supportBoundarySumEquiv_inl
    {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) :
    Relabeling.relabelDist (supportBoundarySumEquiv r)
        (inlDist (B := supportSubtype r) r.restrictToSupport) =
      inlDist
        ((inlDist (B := A) r : Dist (A ⊕ A)).restrictToSupport) := by
  ext x
  cases x with
  | inl x =>
      cases x with
      | mk x hx =>
          cases x with
          | inl a =>
              simp [Relabeling.relabelDist, supportBoundarySumEquiv,
                supportInlDistEquiv]
          | inr a =>
              have hxpos : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) > 0 := hx
              have hzero : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) = 0 := rfl
              exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
  | inr x =>
      simp [Relabeling.relabelDist, supportBoundarySumEquiv]

@[simp]
theorem relabelDist_supportBoundarySumEquiv_inr
    {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) :
    Relabeling.relabelDist (supportBoundarySumEquiv r)
        (inrDist (A := supportSubtype r) r.restrictToSupport) =
      inrDist
        ((inrDist (A := A) r : Dist (A ⊕ A)).restrictToSupport) := by
  ext x
  cases x with
  | inl x =>
      simp [Relabeling.relabelDist, supportBoundarySumEquiv]
  | inr x =>
      cases x with
      | mk x hx =>
          cases x with
          | inl a =>
              have hxpos : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) > 0 := hx
              have hzero : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) = 0 := rfl
              exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
          | inr a =>
              simp [Relabeling.relabelDist, supportBoundarySumEquiv,
                supportInrDistEquiv]

/-- Embed the clean two-block outcome tags into the nested outcome tags produced
by support-restricting an already blocked comparison. -/
noncomputable def boundaryNestedOutcomeEmbed
    (O : Type u) [Fintype O] [DecidableEq O] :
    Channel (O ⊕ O) ((O ⊕ O) ⊕ (O ⊕ O))
  | Sum.inl o => Dist.pure (Sum.inl (Sum.inl o))
  | Sum.inr o => Dist.pure (Sum.inr (Sum.inr o))

/-- Collapse the nested support-restriction outcome tags back to the clean
two-block outcome tags.  The two off-diagonal nested tags have zero probability
in the boundary block channels below, so their deterministic image is irrelevant. -/
noncomputable def boundaryNestedOutcomeProject
    (O : Type u) [Fintype O] [DecidableEq O] :
    Channel ((O ⊕ O) ⊕ (O ⊕ O)) (O ⊕ O)
  | Sum.inl (Sum.inl o) => Dist.pure (Sum.inl o)
  | Sum.inl (Sum.inr o) => Dist.pure (Sum.inr o)
  | Sum.inr (Sum.inl o) => Dist.pure (Sum.inl o)
  | Sum.inr (Sum.inr o) => Dist.pure (Sum.inr o)

/-- If two finite channels are mutual outcome postprocessings, then main-text
A6 plus A1/A5 allows replacing one by the other in any pairwise comparison. -/
theorem rel_of_mutual_postprocess_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (P' : Channel A Y)
    (T : Channel O Y) (S : Channel Y O)
    (hT : P' = Channel.postprocess P T)
    (hS : P = Channel.postprocess P' S)
    (q r : Dist A) :
    F.rel P q r ↔ F.rel P' q r := by
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q) := by
    rw [hT]
    exact hax.recordProcessing P T q
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist q) (inrDist q) := by
    rw [hS]
    exact hax.recordProcessing P' S q
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r) := by
    rw [hT]
    exact hax.recordProcessing P T r
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist r) (inrDist r) := by
    rw [hS]
    exact hax.recordProcessing P' S r
  exact
    Relabeling.pairwise_relabel_replacement_from_weak_equiv
      F hax P P' q r q r
      hq_to_new hq_to_old hr_to_new hr_to_old

/-- Support-restricted nested boundary block channels are exactly the clean
support-face block channel after deterministic outcome embedding. -/
theorem boundaryNested_postprocess_embed_eq
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P R : Channel (supportSubtype r) O) :
    let eA := supportBoundarySumEquiv r
    let clean :=
      Relabeling.relabelChannel eA (Equiv.refl (O ⊕ O))
        (blockChannel P R)
    let ambient :=
      blockChannel (supportExtendChannel r P) (supportExtendChannel r R)
    let nested :=
      blockChannel
        (Channel.restrictToSupport ambient (inlDist (B := A) r))
        (Channel.restrictToSupport ambient (inrDist (A := A) r))
    nested = Channel.postprocess clean (boundaryNestedOutcomeEmbed O) := by
  classical
  ext x y
  cases x with
  | inl x =>
      cases x with
      | mk x hx =>
          cases x with
          | inl a =>
              cases y with
              | inl y =>
                  cases y with
                  | inl o =>
                      have hpos : 0 < r a := by simpa using hx
                      simp only [Channel.postprocess]
                      rw [Fintype.sum_eq_single (Sum.inl o)]
                      · simp [supportBoundarySumEquiv, supportInlDistEquiv,
                          supportExtendChannel, boundaryNestedOutcomeEmbed,
                          Channel.postprocess, Relabeling.relabelChannel, hpos]
                      · intro o' ho'
                        cases o' with
                        | inl o₂ =>
                            have hne : o₂ ≠ o := by
                              intro h
                              exact ho' (by simp [h])
                            have hpure :
                                (Dist.pure
                                      (Sum.inl (Sum.inl o₂) :
                                        (O ⊕ O) ⊕ (O ⊕ O)))
                                    (Sum.inl (Sum.inl o) :
                                      (O ⊕ O) ⊕ (O ⊕ O)) = 0 := by
                              have hneq :
                                  (Sum.inl (Sum.inl o) :
                                    (O ⊕ O) ⊕ (O ⊕ O)) ≠
                                    Sum.inl (Sum.inl o₂) := by
                                intro h
                                exact hne ((Sum.inl.inj (Sum.inl.inj h)).symm)
                              exact Dist.pure_apply_ne
                                (Sum.inl (Sum.inl o₂) :
                                  (O ⊕ O) ⊕ (O ⊕ O))
                                (Sum.inl (Sum.inl o) :
                                  (O ⊕ O) ⊕ (O ⊕ O))
                                hneq
                            simpa [boundaryNestedOutcomeEmbed] using
                              (mul_eq_zero_of_right _ hpure)
                        | inr o₂ =>
                            simp [Relabeling.relabelChannel, supportBoundarySumEquiv,
                              supportInlDistEquiv]
                  | inr o =>
                      simp [supportBoundarySumEquiv, supportInlDistEquiv,
                        supportExtendChannel, boundaryNestedOutcomeEmbed,
                        Channel.postprocess, Relabeling.relabelChannel]
              | inr y =>
                  cases y <;>
                    simp [supportBoundarySumEquiv, supportInlDistEquiv,
                      supportExtendChannel, boundaryNestedOutcomeEmbed,
                      Channel.postprocess, Relabeling.relabelChannel]
          | inr a =>
              have hxpos : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) > 0 := hx
              have hzero : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) = 0 := rfl
              exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
  | inr x =>
      cases x with
      | mk x hx =>
          cases x with
          | inl a =>
              have hxpos : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) > 0 := hx
              have hzero : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) = 0 := rfl
              exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
          | inr a =>
              cases y with
              | inl y =>
                  cases y <;>
                    simp [supportBoundarySumEquiv, supportInrDistEquiv,
                      supportExtendChannel, boundaryNestedOutcomeEmbed,
                      Channel.postprocess, Relabeling.relabelChannel]
              | inr y =>
                  cases y with
                  | inl o =>
                      simp [supportBoundarySumEquiv, supportInrDistEquiv,
                        supportExtendChannel, boundaryNestedOutcomeEmbed,
                        Channel.postprocess, Relabeling.relabelChannel]
                  | inr o =>
                      have hpos : 0 < r a := by simpa using hx
                      simp only [Channel.postprocess]
                      rw [Fintype.sum_eq_single (Sum.inr o)]
                      · simp [supportBoundarySumEquiv, supportInrDistEquiv,
                          supportExtendChannel, boundaryNestedOutcomeEmbed,
                          Channel.postprocess, Relabeling.relabelChannel, hpos]
                      · intro o' ho'
                        cases o' with
                        | inl o₂ =>
                            simp [Relabeling.relabelChannel, supportBoundarySumEquiv,
                              supportInrDistEquiv]
                        | inr o₂ =>
                            have hne : o₂ ≠ o := by
                              intro h
                              exact ho' (by simp [h])
                            have hpure :
                                (Dist.pure
                                      (Sum.inr (Sum.inr o₂) :
                                        (O ⊕ O) ⊕ (O ⊕ O)))
                                    (Sum.inr (Sum.inr o) :
                                      (O ⊕ O) ⊕ (O ⊕ O)) = 0 := by
                              have hneq :
                                  (Sum.inr (Sum.inr o) :
                                    (O ⊕ O) ⊕ (O ⊕ O)) ≠
                                    Sum.inr (Sum.inr o₂) := by
                                intro h
                                exact hne ((Sum.inr.inj (Sum.inr.inj h)).symm)
                              exact Dist.pure_apply_ne
                                (Sum.inr (Sum.inr o₂) :
                                  (O ⊕ O) ⊕ (O ⊕ O))
                                (Sum.inr (Sum.inr o) :
                                  (O ⊕ O) ⊕ (O ⊕ O))
                                hneq
                            simpa [boundaryNestedOutcomeEmbed] using
                              (mul_eq_zero_of_right _ hpure)

/-- The deterministic projection from nested support-restriction tags recovers
the clean support-face block channel. -/
theorem boundaryNested_postprocess_project_eq
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P R : Channel (supportSubtype r) O) :
    let eA := supportBoundarySumEquiv r
    let clean :=
      Relabeling.relabelChannel eA (Equiv.refl (O ⊕ O))
        (blockChannel P R)
    let ambient :=
      blockChannel (supportExtendChannel r P) (supportExtendChannel r R)
    let nested :=
      blockChannel
        (Channel.restrictToSupport ambient (inlDist (B := A) r))
        (Channel.restrictToSupport ambient (inrDist (A := A) r))
    clean = Channel.postprocess nested (boundaryNestedOutcomeProject O) := by
  classical
  ext x y
  cases x with
  | inl x =>
      cases x with
      | mk x hx =>
          cases x with
          | inl a =>
              cases y with
              | inl o =>
                  have hpos : 0 < r a := by simpa using hx
                  simp only [Channel.postprocess]
                  rw [Fintype.sum_eq_single (Sum.inl (Sum.inl o))]
                  · simp [supportBoundarySumEquiv, supportInlDistEquiv,
                      supportExtendChannel, boundaryNestedOutcomeProject,
                      Channel.postprocess, Relabeling.relabelChannel, hpos]
                  · intro o' ho'
                    cases o' with
                    | inl y =>
                        cases y with
                        | inl o₂ =>
                            have hne : o₂ ≠ o := by
                              intro h
                              exact ho' (by simp [h])
                            have hpure :
                                (Dist.pure (Sum.inl o₂ : O ⊕ O))
                                    (Sum.inl o : O ⊕ O) = 0 := by
                              have hneq :
                                  (Sum.inl o : O ⊕ O) ≠ Sum.inl o₂ := by
                                intro h
                                exact hne ((Sum.inl.inj h).symm)
                              exact Dist.pure_apply_ne
                                (Sum.inl o₂ : O ⊕ O) (Sum.inl o : O ⊕ O) hneq
                            simpa [boundaryNestedOutcomeProject] using
                              (mul_eq_zero_of_right _ hpure)
                        | inr o₂ =>
                            simp [supportExtendChannel]
                    | inr y =>
                        cases y <;> simp
              | inr o =>
                  simp [supportBoundarySumEquiv, supportInlDistEquiv,
                    supportExtendChannel, boundaryNestedOutcomeProject,
                    Channel.postprocess, Relabeling.relabelChannel]
          | inr a =>
              have hxpos : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) > 0 := hx
              have hzero : (inlDist (B := A) r : Dist (A ⊕ A)) (Sum.inr a) = 0 := rfl
              exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
  | inr x =>
      cases x with
      | mk x hx =>
          cases x with
          | inl a =>
              have hxpos : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) > 0 := hx
              have hzero : (inrDist (A := A) r : Dist (A ⊕ A)) (Sum.inl a) = 0 := rfl
              exact False.elim ((lt_irrefl (0 : ℝ)) (by simpa [hzero] using hxpos))
          | inr a =>
              cases y with
              | inl o =>
                  simp [supportBoundarySumEquiv, supportInrDistEquiv,
                    supportExtendChannel, boundaryNestedOutcomeProject,
                    Channel.postprocess, Relabeling.relabelChannel]
              | inr o =>
                  have hpos : 0 < r a := by simpa using hx
                  simp only [Channel.postprocess]
                  rw [Fintype.sum_eq_single (Sum.inr (Sum.inr o))]
                  · simp [supportBoundarySumEquiv, supportInrDistEquiv,
                      supportExtendChannel, boundaryNestedOutcomeProject,
                      Channel.postprocess, Relabeling.relabelChannel, hpos]
                  · intro o' ho'
                    cases o' with
                    | inl y =>
                        cases y <;> simp
                    | inr y =>
                        cases y with
                        | inl o₂ =>
                            simp [supportExtendChannel]
                        | inr o₂ =>
                            have hne : o₂ ≠ o := by
                              intro h
                              exact ho' (by simp [h])
                            have hpure :
                                (Dist.pure (Sum.inr o₂ : O ⊕ O))
                                    (Sum.inr o : O ⊕ O) = 0 := by
                              have hneq :
                                  (Sum.inr o : O ⊕ O) ≠ Sum.inr o₂ := by
                                intro h
                                exact hne ((Sum.inr.inj h).symm)
                              exact Dist.pure_apply_ne
                                (Sum.inr o₂ : O ⊕ O) (Sum.inr o : O ⊕ O) hneq
                            simpa [boundaryNestedOutcomeProject] using
                              (mul_eq_zero_of_right _ hpure)

/-- Boundary block lift: an intrinsic support-face block comparison extends to
the ambient boundary prior, with no extra convention. -/
theorem boundary_block_lift_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P R : Channel (supportSubtype r) O) :
    F.rel (blockChannel P R)
        (inlDist (B := supportSubtype r) r.restrictToSupport)
        (inrDist (A := supportSubtype r) r.restrictToSupport) →
      F.rel
        (blockChannel (supportExtendChannel r P) (supportExtendChannel r R))
        (inlDist (B := A) r) (inrDist (A := A) r) := by
  classical
  intro hface
  let eA := supportBoundarySumEquiv r
  let clean :=
    Relabeling.relabelChannel eA (Equiv.refl (O ⊕ O))
      (blockChannel P R)
  let ambient :=
    blockChannel (supportExtendChannel r P) (supportExtendChannel r R)
  let nested :=
    blockChannel
      (Channel.restrictToSupport ambient (inlDist (B := A) r))
      (Channel.restrictToSupport ambient (inrDist (A := A) r))
  let qS := (inlDist (B := A) r : Dist (A ⊕ A)).restrictToSupport
  let rS := (inrDist (A := A) r : Dist (A ⊕ A)).restrictToSupport
  have hclean :
      F.rel clean (inlDist qS) (inrDist rS) := by
    have h :=
      (Relabeling.relabel_rel_of_axioms F hax eA (Equiv.refl (O ⊕ O))
        (blockChannel P R)
        (inlDist (B := supportSubtype r) r.restrictToSupport)
        (inrDist (A := supportSubtype r) r.restrictToSupport)).mp hface
    simpa [clean, qS, rS, eA] using h
  have hnested : F.rel nested (inlDist qS) (inrDist rS) := by
    have hT : nested = Channel.postprocess clean (boundaryNestedOutcomeEmbed O) := by
      simpa [clean, ambient, nested] using
        boundaryNested_postprocess_embed_eq r P R
    have hS : clean = Channel.postprocess nested (boundaryNestedOutcomeProject O) := by
      simpa [clean, ambient, nested] using
        boundaryNested_postprocess_project_eq r P R
    exact
      (rel_of_mutual_postprocess_of_axioms F hax clean nested
        (boundaryNestedOutcomeEmbed O) (boundaryNestedOutcomeProject O)
        hT hS (inlDist qS) (inrDist rS)).mp hclean
  have hpref :
      F.rel ambient (inlDist (B := A) r) (inrDist (A := A) r) ↔
        F.rel nested (inlDist qS) (inrDist rS) := by
    simpa [ambient, nested, qS, rS] using
      preference_support_restriction_of_axioms F hax ambient
        (inlDist (B := A) r) (inrDist (A := A) r)
  exact hpref.mpr hnested

/-- Boundary block comparison is WLOG intrinsic to the positive support face.

The forward implication is the support-restriction theorem applied to the
ambient boundary block.  The reverse implication is `boundary_block_lift_of_axioms`.
Both directions use only main-text A1 and A5--A7 through relabeling, outcome
postprocessing, and support restriction. -/
theorem boundary_block_rel_iff_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P R : Channel (supportSubtype r) O) :
    F.rel
        (blockChannel (supportExtendChannel r P) (supportExtendChannel r R))
        (inlDist (B := A) r) (inrDist (A := A) r) ↔
      F.rel (blockChannel P R)
        (inlDist (B := supportSubtype r) r.restrictToSupport)
        (inrDist (A := supportSubtype r) r.restrictToSupport) := by
  classical
  constructor
  · intro hambient
    let eA := supportBoundarySumEquiv r
    let clean :=
      Relabeling.relabelChannel eA (Equiv.refl (O ⊕ O))
        (blockChannel P R)
    let ambient :=
      blockChannel (supportExtendChannel r P) (supportExtendChannel r R)
    let nested :=
      blockChannel
        (Channel.restrictToSupport ambient (inlDist (B := A) r))
        (Channel.restrictToSupport ambient (inrDist (A := A) r))
    let qS := (inlDist (B := A) r : Dist (A ⊕ A)).restrictToSupport
    let rS := (inrDist (A := A) r : Dist (A ⊕ A)).restrictToSupport
    have hnested : F.rel nested (inlDist qS) (inrDist rS) := by
      have hpref :
          F.rel ambient (inlDist (B := A) r) (inrDist (A := A) r) ↔
            F.rel nested (inlDist qS) (inrDist rS) := by
        simpa [ambient, nested, qS, rS] using
          preference_support_restriction_of_axioms F hax ambient
            (inlDist (B := A) r) (inrDist (A := A) r)
      exact hpref.mp (by simpa [ambient] using hambient)
    have hclean : F.rel clean (inlDist qS) (inrDist rS) := by
      have hT : nested = Channel.postprocess clean (boundaryNestedOutcomeEmbed O) := by
        simpa [clean, ambient, nested] using
          boundaryNested_postprocess_embed_eq r P R
      have hS : clean = Channel.postprocess nested (boundaryNestedOutcomeProject O) := by
        simpa [clean, ambient, nested] using
          boundaryNested_postprocess_project_eq r P R
      exact
        (rel_of_mutual_postprocess_of_axioms F hax clean nested
          (boundaryNestedOutcomeEmbed O) (boundaryNestedOutcomeProject O)
          hT hS (inlDist qS) (inrDist rS)).mpr hnested
    have hface :=
      (Relabeling.relabel_rel_of_axioms F hax eA (Equiv.refl (O ⊕ O))
        (blockChannel P R)
        (inlDist (B := supportSubtype r) r.restrictToSupport)
        (inrDist (A := supportSubtype r) r.restrictToSupport)).mpr
        (by simpa [clean, qS, rS, eA] using hclean)
    simpa [clean, qS, rS, eA] using hface
  · exact boundary_block_lift_of_axioms F hax r P R

/-- Strict boundary block comparisons are also WLOG intrinsic to the positive
support face.  The negated reverse comparison is transported through the same
support-face equivalence after applying the already-derived block swap
relabeling theorem. -/
theorem boundary_block_strictRel_iff_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P R : Channel (supportSubtype r) O) :
    F.strictRel
        (blockChannel (supportExtendChannel r P) (supportExtendChannel r R))
        (inlDist (B := A) r) (inrDist (A := A) r) ↔
      F.strictRel (blockChannel P R)
        (inlDist (B := supportSubtype r) r.restrictToSupport)
        (inrDist (A := supportSubtype r) r.restrictToSupport) := by
  classical
  constructor
  · intro hambient
    constructor
    · exact (boundary_block_rel_iff_of_axioms F hax r P R).mp hambient.1
    · intro hrevFace
      have hrevFaceSwapped :
          F.rel (blockChannel R P)
            (inlDist (B := supportSubtype r) r.restrictToSupport)
            (inrDist (A := supportSubtype r) r.restrictToSupport) := by
        exact
          (Relabeling.block_swap_rel_of_axioms F hax P R
            r.restrictToSupport r.restrictToSupport).mp hrevFace
      have hrevAmbientSwapped :
          F.rel
            (blockChannel (supportExtendChannel r R) (supportExtendChannel r P))
            (inlDist (B := A) r) (inrDist (A := A) r) := by
        exact
          (boundary_block_rel_iff_of_axioms F hax r R P).mpr
            hrevFaceSwapped
      have hrevAmbient :
          F.rel
            (blockChannel (supportExtendChannel r P) (supportExtendChannel r R))
            (inrDist (A := A) r) (inlDist (B := A) r) := by
        exact
          (Relabeling.block_swap_rel_of_axioms F hax
            (supportExtendChannel r P) (supportExtendChannel r R) r r).mpr
            hrevAmbientSwapped
      exact hambient.2 hrevAmbient
  · intro hface
    constructor
    · exact (boundary_block_rel_iff_of_axioms F hax r P R).mpr hface.1
    · intro hrevAmbient
      have hrevAmbientSwapped :
          F.rel
            (blockChannel (supportExtendChannel r R) (supportExtendChannel r P))
            (inlDist (B := A) r) (inrDist (A := A) r) := by
        exact
          (Relabeling.block_swap_rel_of_axioms F hax
            (supportExtendChannel r P) (supportExtendChannel r R) r r).mp
            hrevAmbient
      have hrevFaceSwapped :
          F.rel (blockChannel R P)
            (inlDist (B := supportSubtype r) r.restrictToSupport)
            (inrDist (A := supportSubtype r) r.restrictToSupport) := by
        exact
          (boundary_block_rel_iff_of_axioms F hax r R P).mp
            hrevAmbientSwapped
      have hrevFace :
          F.rel (blockChannel P R)
            (inrDist (A := supportSubtype r) r.restrictToSupport)
            (inlDist (B := supportSubtype r) r.restrictToSupport) := by
        exact
          (Relabeling.block_swap_rel_of_axioms F hax P R
            r.restrictToSupport r.restrictToSupport).mpr hrevFaceSwapped
      exact hface.2 hrevFace

/-- Posterior-law differences at a boundary prior are the push-forward of the
corresponding intrinsic support-face differences. -/
theorem posteriorLawDifferenceExp_restrictToSupport_pushforward_pair
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)] (P R : Channel A O)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp r
        (experimentOfChannel P)
        (experimentOfChannel R) φ =
      posteriorLawDifferenceExp r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P r))
        (experimentOfChannel (Channel.restrictToSupport R r))
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := by
  unfold posteriorLawDifferenceExp
  have hP :
      posteriorLawIntegralExp r (experimentOfChannel P) φ =
        posteriorLawIntegralExp r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P r))
          (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := by
    rw [posteriorLawIntegralExp_experimentOfChannel]
    rw [posteriorLawIntegralExp_experimentOfChannel]
    exact posteriorLawIntegral_restrictToSupport P r φ
  have hR :
      posteriorLawIntegralExp r (experimentOfChannel R) φ =
        posteriorLawIntegralExp r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport R r))
          (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := by
    rw [posteriorLawIntegralExp_experimentOfChannel]
    rw [posteriorLawIntegralExp_experimentOfChannel]
    exact posteriorLawIntegral_restrictToSupport R r φ
  rw [hP, hR]

/-- Specialization of support-face posterior-law transport to extended
continuation channels. -/
theorem posteriorLawDifferenceExp_supportExtendChannel
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P R : Channel (supportSubtype r) O)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp r
        (experimentOfChannel (supportExtendChannel r P))
        (experimentOfChannel (supportExtendChannel r R)) φ =
      posteriorLawDifferenceExp r.restrictToSupport
        (experimentOfChannel P)
        (experimentOfChannel R)
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := by
  rw [posteriorLawDifferenceExp_restrictToSupport_pushforward_pair]
  rw [restrictToSupport_supportExtendChannel,
    restrictToSupport_supportExtendChannel]

/-- Boundary analogue of the common-outcome tangent sign step.

If a tangent direction on the positive support face of a boundary posterior is
realized as a common-outcome feasible difference on that face, then its
push-forward to the ambient simplex has the same forward/zero sign transport
from the reached boundary branch to the full-support aggregate prior.  The
target branch comparison is lifted from the support face by
`boundary_block_strictRel_iff_of_axioms`, so this introduces no boundary
convention. -/
theorem branch_boundary_tangent_forward_zero_of_commonOutcome_realization
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A O O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype O₁] [DecidableEq O₁]
    (q r : Dist A) (hq : q.FullSupport) [Nonempty (supportSubtype r)]
    (η : PosteriorLawSigned (supportSubtype r)) (t : ℝ) (ht : 0 < t)
    (P R : Channel (supportSubtype r) O)
    (hη :
      ∀ φ : Dist (supportSubtype r) → ℝ,
        η φ =
          t * posteriorLawDifferenceExp r.restrictToSupport
            (experimentOfChannel P) (experimentOfChannel R) φ)
    (P₁ : Channel A O₁) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (hpost : branchPosterior P₁ q target = r) :
    (0 < hlin.linearPart F hV r.restrictToSupport η →
      0 < hlin.linearPart F hV q
        (fun φ : Dist A → ℝ =>
          η (fun d =>
            φ (Channel.actionPushforward d (supportIncludeKernel r))))) ∧
    (hlin.linearPart F hV r.restrictToSupport η = 0 →
      hlin.linearPart F hV q
        (fun φ : Dist A → ℝ =>
          η (fun d =>
            φ (Channel.actionPushforward d (supportIncludeKernel r)))) = 0) := by
  classical
  let O₂ : O₁ → Type u := fun _ => O
  let Q : ∀ o, Channel A (O₂ o) := fun o =>
    if o = target then supportExtendChannel r P else supportExtendChannel r P
  let S : ∀ o, Channel A (O₂ o) := fun o =>
    if o = target then supportExtendChannel r R else supportExtendChannel r P
  let faceDiff : PosteriorLawSigned (supportSubtype r) :=
    posteriorLawDifferenceExp r.restrictToSupport
      (experimentOfChannel P) (experimentOfChannel R)
  let branchDiff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r
      (experimentOfChannel (supportExtendChannel r P))
      (experimentOfChannel (supportExtendChannel r R))
  let pushη : PosteriorLawSigned A :=
    fun φ : Dist A → ℝ =>
      η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))
  let seqDiff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp q
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel (seqComposeDep P₁ O₂ S))
  have hsame : ∀ o, o ≠ target → Q o = S o := by
    intro o ho
    simp [Q, S, ho]
  have hη_eq : η = posteriorLawSignedSMul t faceDiff := by
    funext φ
    exact hη φ
  have hpushη_eq : pushη = posteriorLawSignedSMul t branchDiff := by
    funext φ
    calc
      pushη φ =
          η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := rfl
      _ = t * posteriorLawDifferenceExp r.restrictToSupport
            (experimentOfChannel P) (experimentOfChannel R)
            (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) := hη _
      _ = t * branchDiff φ := by
            rw [← posteriorLawDifferenceExp_supportExtendChannel r P R φ]
  have hη_lin_r :
      hlin.linearPart F hV r.restrictToSupport η =
        t * hlin.linearPart F hV r.restrictToSupport faceDiff := by
    rw [hη_eq, hlin.linearPart_smul]
  have hη_lin_q :
      hlin.linearPart F hV q pushη =
        t * hlin.linearPart F hV q branchDiff := by
    rw [hpushη_eq, hlin.linearPart_smul]
  have htargetQ :
      Q target = supportExtendChannel r P := by
    simp [Q]
  have htargetS :
      S target = supportExtendChannel r R := by
    simp [S]
  have hseq_eq :
      seqDiff =
        posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
          branchDiff := by
    funext φ
    have h :=
      posteriorLawDifference_seqComposeDep_one_branch
        q P₁ O₂ Q S target hsame φ
    simpa [seqDiff, branchDiff, Q, S, hpost, posteriorLawSignedSMul] using h
  have hseq_lin_q :
      hlin.linearPart F hV q seqDiff =
        (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff := by
    rw [hseq_eq, hlin.linearPart_smul]
  have hbranch_pos_to_q_pos :
      0 < hlin.linearPart F hV r.restrictToSupport faceDiff →
        0 < hlin.linearPart F hV q branchDiff := by
    intro hbpos
    have hbranch_gt :
        hV.V r.restrictToSupport (experimentOfChannel R) <
          hV.V r.restrictToSupport (experimentOfChannel P) :=
      (linearPart_difference_pos_iff_value_gt hlin F hV
        r.restrictToSupport (experimentOfChannel P)
        (experimentOfChannel R)).mp hbpos
    have htarget_face_weak :
        F.rel (blockChannel P R)
          (inlDist (B := supportSubtype r) r.restrictToSupport)
          (inrDist (A := supportSubtype r) r.restrictToSupport) :=
      block_rel_of_channel_value_ge F hV
        r.restrictToSupport (Dist.restrictToSupport_fullSupport r)
        P R (le_of_lt hbranch_gt)
    have htarget_face_strict :
        F.strictRel (blockChannel P R)
          (inlDist (B := supportSubtype r) r.restrictToSupport)
          (inrDist (A := supportSubtype r) r.restrictToSupport) :=
      block_strictRel_of_channel_value_gt F hax hV
        r.restrictToSupport (Dist.restrictToSupport_fullSupport r)
        P R hbranch_gt
    have htarget_weak :
        F.rel (blockChannel (Q target) (S target))
          (inlDist (branchPosterior P₁ q target))
          (inrDist (branchPosterior P₁ q target)) := by
      have hamb :=
        (boundary_block_rel_iff_of_axioms F hax r P R).mpr
          htarget_face_weak
      simpa [htargetQ, htargetS, hpost] using hamb
    have htarget_strict :
        F.strictRel (blockChannel (Q target) (S target))
          (inlDist (branchPosterior P₁ q target))
          (inrDist (branchPosterior P₁ q target)) := by
      have hamb :=
        (boundary_block_strictRel_iff_of_axioms F hax r P R).mpr
          htarget_face_strict
      simpa [htargetQ, htargetS, hpost] using hamb
    have hagg_strict :
        F.strictRel
          (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ S))
          (inlDist q) (inrDist q) :=
      A6_strict_one_branch_of_strict F hax O₂ q P₁ Q S target hpos hsame
        htarget_weak htarget_strict
    have hagg_gt :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ S)) <
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) := by
      have hpref :
          ExperimentPairPref F
            (experimentOfChannel (seqComposeDep P₁ O₂ Q))
            (experimentOfChannel (seqComposeDep P₁ O₂ S)) q q := by
        change F.rel
          (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ S))
          (inlDist q) (inrDist q)
        exact hagg_strict.1
      have hge :
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) ≥
            hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ S)) :=
        (hV.represents_block_comparisons q hq _ _).mp hpref
      by_contra hnot_gt
      have hge_rev :
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ S)) ≥
            hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) :=
        le_of_not_gt hnot_gt
      have hpref_rev :
          ExperimentPairPref F
            (experimentOfChannel (seqComposeDep P₁ O₂ S))
            (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q :=
        (hV.represents_block_comparisons q hq _ _).mpr hge_rev
      have hrel_rev :
          F.rel
            (blockChannel (seqComposeDep P₁ O₂ S) (seqComposeDep P₁ O₂ Q))
            (inlDist q) (inrDist q) := by
        exact hpref_rev
      have hrel_rev_same :
          F.rel
            (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ S))
            (inrDist q) (inlDist q) :=
        (Relabeling.block_swap_rel_of_axioms F hax
          (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ S) q q).mpr
          hrel_rev
      exact hagg_strict.2 hrel_rev_same
    have hseq_pos :
        0 < hlin.linearPart F hV q seqDiff :=
      (linearPart_difference_pos_iff_value_gt hlin F hV q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ S))).mpr hagg_gt
    have hmpos : 0 < (Channel.outcomeMarginal P₁ q) target := hpos
    have hmul :
        0 < (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff := by
      simpa [hseq_lin_q] using hseq_pos
    nlinarith [hmpos, hmul]
  have hbranch_zero_to_q_zero :
      hlin.linearPart F hV r.restrictToSupport faceDiff = 0 →
        hlin.linearPart F hV q branchDiff = 0 := by
    intro hbzero
    have hbranch_eq :
        hV.V r.restrictToSupport (experimentOfChannel P) =
          hV.V r.restrictToSupport (experimentOfChannel R) :=
      (linearPart_difference_zero_iff_value_eq hlin F hV
        r.restrictToSupport (experimentOfChannel P)
        (experimentOfChannel R)).mp hbzero
    have htarget_face_QR :
        F.rel (blockChannel P R)
          (inlDist (B := supportSubtype r) r.restrictToSupport)
          (inrDist (A := supportSubtype r) r.restrictToSupport) :=
      block_rel_of_channel_value_ge F hV
        r.restrictToSupport (Dist.restrictToSupport_fullSupport r)
        P R (by rw [hbranch_eq])
    have htarget_face_RQ :
        F.rel (blockChannel R P)
          (inlDist (B := supportSubtype r) r.restrictToSupport)
          (inrDist (A := supportSubtype r) r.restrictToSupport) :=
      block_rel_of_channel_value_ge F hV
        r.restrictToSupport (Dist.restrictToSupport_fullSupport r)
        R P (by rw [hbranch_eq])
    have htarget_QR :
        F.rel (blockChannel (Q target) (S target))
          (inlDist (branchPosterior P₁ q target))
          (inrDist (branchPosterior P₁ q target)) := by
      have hamb :=
        (boundary_block_rel_iff_of_axioms F hax r P R).mpr
          htarget_face_QR
      simpa [htargetQ, htargetS, hpost] using hamb
    have htarget_RQ :
        F.rel (blockChannel (S target) (Q target))
          (inlDist (branchPosterior P₁ q target))
          (inrDist (branchPosterior P₁ q target)) := by
      have hamb :=
        (boundary_block_rel_iff_of_axioms F hax r R P).mpr
          htarget_face_RQ
      simpa [htargetQ, htargetS, hpost] using hamb
    have hagg_QR :
        F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ S))
          (inlDist q) (inrDist q) :=
      A6_weak_one_branch_of_rel F hax O₂ q P₁ Q S target hsame htarget_QR
    have hagg_RQ :
        F.rel (blockChannel (seqComposeDep P₁ O₂ S) (seqComposeDep P₁ O₂ Q))
          (inlDist q) (inrDist q) :=
      A6_weak_one_branch_of_rel F hax O₂ q P₁ S Q target
        (fun o ho => (hsame o ho).symm) htarget_RQ
    have hpref_QR :
        ExperimentPairPref F
          (experimentOfChannel (seqComposeDep P₁ O₂ Q))
          (experimentOfChannel (seqComposeDep P₁ O₂ S)) q q := by
      change F.rel
        (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ S))
        (inlDist q) (inrDist q)
      exact hagg_QR
    have hpref_RQ :
        ExperimentPairPref F
          (experimentOfChannel (seqComposeDep P₁ O₂ S))
          (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q := by
      change F.rel
        (blockChannel (seqComposeDep P₁ O₂ S) (seqComposeDep P₁ O₂ Q))
        (inlDist q) (inrDist q)
      exact hagg_RQ
    have hge_QR :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) ≥
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ S)) :=
      (hV.represents_block_comparisons q hq _ _).mp hpref_QR
    have hge_RQ :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ S)) ≥
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) :=
      (hV.represents_block_comparisons q hq _ _).mp hpref_RQ
    have hseq_eq_value :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ S)) := by
      linarith
    have hseq_zero :
        hlin.linearPart F hV q seqDiff = 0 :=
      (linearPart_difference_zero_iff_value_eq hlin F hV q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ S))).mpr hseq_eq_value
    have hmne : (Channel.outcomeMarginal P₁ q) target ≠ 0 := ne_of_gt hpos
    have hmul :
        (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff = 0 := by
      simpa [hseq_lin_q] using hseq_zero
    exact (mul_eq_zero.mp hmul).resolve_left hmne
  constructor
  · intro hrη_pos
    have hbpos : 0 < hlin.linearPart F hV r.restrictToSupport faceDiff := by
      nlinarith [hη_lin_r, ht, hrη_pos]
    have hqpos := hbranch_pos_to_q_pos hbpos
    nlinarith [hη_lin_q, ht, hqpos]
  · intro hrη_zero
    have hbzero : hlin.linearPart F hV r.restrictToSupport faceDiff = 0 := by
      nlinarith [hη_lin_r, ht, hrη_zero]
    have hqzero := hbranch_zero_to_q_zero hbzero
    nlinarith [hη_lin_q, ht, hqzero]

/-- Pure-trace nontriviality and finite-branch aggregation, plus atomic tangent
spanning, construct the boundary support-face
scalar.

For a full-support ambient prior `q` and an arbitrary finite boundary posterior
`r`, the linear part at `q`, evaluated on pushed support-face tangent
directions, is a positive scalar multiple of the intrinsic support-face linear
part at `r.restrictToSupport`.  This is the theorem-level replacement for a
bare boundary transport convention: it proves existence of the coefficient
from the axioms and the accepted finite tangent-spanning result. -/
theorem boundary_atomicLinear_tangent_scalar_of_A1_spanning
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    [Nonempty (supportSubtype r)]
    (hr_nondegenerate :
      ∃ a b : supportSubtype r, a ≠ b ∧
        0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b) :
    ∃ β : ℝ, 0 < β ∧
      ∀ (η : PosteriorLawSigned (supportSubtype r)),
        PosteriorLawSigned.AtomicLinear η → PosteriorLawTangent η →
        hlin.linearPart F hV q
          (fun φ : Dist A → ℝ =>
            η (fun d =>
              φ (Channel.actionPushforward d (supportIncludeKernel r)))) =
          β * hlin.linearPart F hV r.restrictToSupport η := by
  classical
  let pushSigned : PosteriorLawSigned (supportSubtype r) → PosteriorLawSigned A :=
    fun η φ =>
      η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))
  let Lq : PosteriorLawSigned (supportSubtype r) → ℝ :=
    fun η => hlin.linearPart F hV q (pushSigned η)
  let Lr : PosteriorLawSigned (supportSubtype r) → ℝ :=
    fun η => hlin.linearPart F hV r.restrictToSupport η
  have hLq_zero :
      Lq ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) = 0 := by
    have hpush_zero :
        pushSigned ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) =
          ((fun _ => 0) : PosteriorLawSigned A) := by
      funext φ
      rfl
    simpa [Lq, hpush_zero] using linearPart_zero hlin F hV q
  have hLr_zero :
      Lr ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) = 0 := by
    simpa [Lr] using linearPart_zero hlin F hV r.restrictToSupport
  have hLq_add :
      ∀ η ζ : PosteriorLawSigned (supportSubtype r),
        Lq (posteriorLawSignedAdd η ζ) = Lq η + Lq ζ := by
    intro η ζ
    have hpush_add :
        pushSigned (posteriorLawSignedAdd η ζ) =
          posteriorLawSignedAdd (pushSigned η) (pushSigned ζ) := by
      funext φ
      rfl
    simpa [Lq, hpush_add] using
      hlin.linearPart_add F hV q (pushSigned η) (pushSigned ζ)
  have hLq_smul :
      ∀ (c : ℝ) (η : PosteriorLawSigned (supportSubtype r)),
        Lq (posteriorLawSignedSMul c η) = c * Lq η := by
    intro c η
    have hpush_smul :
        pushSigned (posteriorLawSignedSMul c η) =
          posteriorLawSignedSMul c (pushSigned η) := by
      funext φ
      rfl
    simpa [Lq, hpush_smul] using
      hlin.linearPart_smul F hV q c (pushSigned η)
  have hLr_add :
      ∀ η ζ : PosteriorLawSigned (supportSubtype r),
        Lr (posteriorLawSignedAdd η ζ) = Lr η + Lr ζ := by
    intro η ζ
    simpa [Lr] using
      hlin.linearPart_add F hV r.restrictToSupport η ζ
  have hLr_smul :
      ∀ (c : ℝ) (η : PosteriorLawSigned (supportSubtype r)),
        Lr (posteriorLawSignedSMul c η) = c * Lr η := by
    intro c η
    simpa [Lr] using
      hlin.linearPart_smul F hV r.restrictToSupport c η
  have hforward :
      ∀ (η : PosteriorLawSigned (supportSubtype r)),
        PosteriorLawSigned.AtomicLinear η →
        PosteriorLawTangent η →
        η ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) →
        (0 < Lr η → 0 < Lq η) ∧
        (Lr η = 0 → Lq η = 0) := by
    intro η hηatomic htan hηne
    rcases commonOutcomeAtomicLinearTangentRealization_of_atomicLinearSpanning
        htangent r.restrictToSupport (Dist.restrictToSupport_fullSupport r)
        η hηatomic htan hηne with
      ⟨t, ht, O, hO, hOdec, hrealized⟩
    letI : Fintype O := hO
    letI : DecidableEq O := hOdec
    rcases hrealized with ⟨P, R, hηreal⟩
    rcases branchReachability_of_fullSupport_prior q r hq with
      ⟨O₁, hO₁, hO₁dec, hreachable⟩
    letI : Fintype O₁ := hO₁
    letI : DecidableEq O₁ := hO₁dec
    rcases hreachable with ⟨P₁, target, hpos, hpost⟩
    exact branch_boundary_tangent_forward_zero_of_commonOutcome_realization
      hlin F hax hV q r hq η t ht P R hηreal P₁ target hpos hpost
  have hsign :
      ∀ (η : PosteriorLawSigned (supportSubtype r)),
        PosteriorLawSigned.AtomicLinear η →
        PosteriorLawTangent η →
        η ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) →
        (0 < Lq η ↔ 0 < Lr η) ∧
        (Lq η = 0 ↔ Lr η = 0) := by
    intro η hηatomic htan hηne
    have hfwd := hforward η hηatomic htan hηne
    let negη : PosteriorLawSigned (supportSubtype r) :=
      posteriorLawSignedSMul (-1) η
    have hneg_atomic := PosteriorLawSigned.AtomicLinear.smul (-1) hηatomic
    have hneg_tan := PosteriorLawTangent_neg htan
    have hneg_ne := posteriorLawSignedSMul_neg_ne_zero hηne
    have hfwd_neg := hforward negη hneg_atomic hneg_tan hneg_ne
    have hq_neg : Lq negη = -Lq η := by
      simp [negη, hLq_smul]
    have hr_neg : Lr negη = -Lr η := by
      simp [negη, hLr_smul]
    constructor
    · constructor
      · intro hqpos
        by_contra hrnot
        have hrle : Lr η ≤ 0 := le_of_not_gt hrnot
        by_cases hrzero : Lr η = 0
        · have hqzero := hfwd.2 hrzero
          linarith
        · have hrlt : Lr η < 0 := lt_of_le_of_ne hrle hrzero
          have hrnegpos : 0 < Lr negη := by
            rw [hr_neg]
            linarith
          have hqnegpos := hfwd_neg.1 hrnegpos
          rw [hq_neg] at hqnegpos
          linarith
      · exact hfwd.1
    · constructor
      · intro hqzero
        by_contra hrne
        rcases lt_or_gt_of_ne hrne with hrlt | hrpos
        · have hrnegpos : 0 < Lr negη := by
            rw [hr_neg]
            linarith
          have hqnegpos := hfwd_neg.1 hrnegpos
          rw [hq_neg] at hqnegpos
          linarith
        · have hqpos := hfwd.1 hrpos
          linarith
      · exact hfwd.2
  obtain ⟨x0, hx0_atomic, hx0_tan, hx0_Lr_ne⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      r.restrictToSupport r.restrictToSupport
      (Dist.restrictToSupport_fullSupport r)
      (Dist.restrictToSupport_fullSupport r)
      hr_nondegenerate
  have hx0_ne :
      x0 ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) := by
    intro hx0_eq
    exact hx0_Lr_ne (by rw [hx0_eq]; exact hLr_zero)
  let x : PosteriorLawSigned (supportSubtype r) :=
    if 0 < Lr x0 then x0 else posteriorLawSignedSMul (-1) x0
  have hx_atomic : PosteriorLawSigned.AtomicLinear x := by
    dsimp [x]
    split_ifs
    · exact hx0_atomic
    · exact PosteriorLawSigned.AtomicLinear.smul (-1) hx0_atomic
  have hx_tan : PosteriorLawTangent x := by
    dsimp [x]
    split_ifs
    · exact hx0_tan
    · exact PosteriorLawTangent_smul (-1) hx0_tan
  have hx_ne :
      x ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) := by
    dsimp [x]
    split_ifs
    · exact hx0_ne
    · exact posteriorLawSignedSMul_neg_ne_zero hx0_ne
  have hx_Lr_pos : 0 < Lr x := by
    dsimp [x]
    split_ifs with hpos
    · exact hpos
    · have hle : Lr x0 ≤ 0 := le_of_not_gt hpos
      have hlt : Lr x0 < 0 := lt_of_le_of_ne hle hx0_Lr_ne
      rw [hLr_smul]
      linarith
  have hx_Lr_ne : Lr x ≠ 0 := ne_of_gt hx_Lr_pos
  have hx_Lq_pos : 0 < Lq x :=
    (hsign x hx_atomic hx_tan hx_ne).1.mpr hx_Lr_pos
  let β : ℝ := Lq x / Lr x
  have hβ_pos : 0 < β := div_pos hx_Lq_pos hx_Lr_pos
  refine ⟨β, hβ_pos, ?_⟩
  intro y hy_atomic hy_tan
  by_cases hy_zero : y = ((fun _ => 0) : PosteriorLawSigned (supportSubtype r))
  · rw [hy_zero]
    change
      hlin.linearPart F hV q
          (((fun _ => 0) : PosteriorLawSigned A)) =
        β * hlin.linearPart F hV r.restrictToSupport
          (((fun _ => 0) : PosteriorLawSigned (supportSubtype r)))
    rw [linearPart_zero hlin F hV q,
      linearPart_zero hlin F hV r.restrictToSupport]
    ring
  · let c : ℝ := -(Lr y / Lr x)
    let z : PosteriorLawSigned (supportSubtype r) :=
      posteriorLawSignedAdd y (posteriorLawSignedSMul c x)
    have hz_atomic : PosteriorLawSigned.AtomicLinear z :=
      PosteriorLawSigned.AtomicLinear.add hy_atomic
        (PosteriorLawSigned.AtomicLinear.smul c hx_atomic)
    have hz_tan : PosteriorLawTangent z :=
      PosteriorLawTangent_add hy_tan (PosteriorLawTangent_smul c hx_tan)
    have hz_Lr : Lr z = 0 := by
      have hstep : Lr z = Lr y + c * Lr x := by
        calc
          Lr z = Lr (posteriorLawSignedAdd y (posteriorLawSignedSMul c x)) := rfl
          _ = Lr y + c * Lr x := by
              rw [hLr_add, hLr_smul]
      rw [hstep]
      have hc_val : c = -(Lr y / Lr x) := rfl
      have hdiv := div_mul_cancel₀ (Lr y) hx_Lr_ne
      linarith [hc_val, hdiv]
    have hz_Lq : Lq z = 0 := by
      by_cases hz_zero :
          z = ((fun _ => 0) : PosteriorLawSigned (supportSubtype r))
      · rw [hz_zero]
        exact hLq_zero
      · exact (hsign z hz_atomic hz_tan hz_zero).2.2 hz_Lr
    have hLq_z_expand : Lq y + c * Lq x = 0 := by
      have hzq : Lq z = Lq y + c * Lq x := by
        calc
          Lq z = Lq (posteriorLawSignedAdd y (posteriorLawSignedSMul c x)) := rfl
          _ = Lq y + c * Lq x := by
              rw [hLq_add, hLq_smul]
      linarith [hzq, hz_Lq]
    have hβ_eq : β = Lq x / Lr x := rfl
    show Lq y = β * Lr y
    have hc_expand : c = -(Lr y / Lr x) := rfl
    have hLqy : Lq y = -c * Lq x := by
      linarith [hLq_z_expand]
    rw [hLqy, hc_expand, hβ_eq]
    field_simp

/-- Canonical boundary coefficient obtained by choosing the positive scalar
constructed in `boundary_atomicLinear_tangent_scalar_of_A1_spanning`.  Outside
the full-support/nondegenerate case its value is immaterial for the branch
interfaces, so it is set to `1`. -/
noncomputable def boundaryAtomicLinearTangentCoeffOfA1Spanning
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ := by
  classical
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  exact
    if hq : q.FullSupport then
      if hnd : ∃ a b : supportSubtype r, a ≠ b ∧
          0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b then
        Classical.choose
          (boundary_atomicLinear_tangent_scalar_of_A1_spanning
            hlin htangent F hax hV q r hq hnd)
      else 1
    else 1

theorem boundaryAtomicLinearTangentCoeffOfA1Spanning_eq_choose
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hnd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b) :
    boundaryAtomicLinearTangentCoeffOfA1Spanning
        hlin htangent F hax hV q r =
      Classical.choose
        (boundary_atomicLinear_tangent_scalar_of_A1_spanning
          hlin htangent F hax hV q r hq hnd) := by
  classical
  unfold boundaryAtomicLinearTangentCoeffOfA1Spanning
  rw [dif_pos hq]
  rw [dif_pos hnd]

theorem boundaryAtomicLinearTangentCoeffOfA1Spanning_pos
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hnd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b) :
    0 <
      boundaryAtomicLinearTangentCoeffOfA1Spanning
        hlin htangent F hax hV q r := by
  rw [boundaryAtomicLinearTangentCoeffOfA1Spanning_eq_choose
    hlin htangent F hax hV q r hq hnd]
  exact (Classical.choose_spec
    (boundary_atomicLinear_tangent_scalar_of_A1_spanning
      hlin htangent F hax hV q r hq hnd)).1

theorem boundaryAtomicLinearTangentCoeffOfA1Spanning_relation
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hnd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b)
    (η : PosteriorLawSigned (supportSubtype r))
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    hlin.linearPart F hV q
        (fun φ : Dist A → ℝ =>
          η (fun d =>
            φ (Channel.actionPushforward d (supportIncludeKernel r)))) =
      boundaryAtomicLinearTangentCoeffOfA1Spanning
          hlin htangent F hax hV q r *
        hlin.linearPart F hV r.restrictToSupport η := by
  rw [boundaryAtomicLinearTangentCoeffOfA1Spanning_eq_choose
    hlin htangent F hax hV q r hq hnd]
  exact (Classical.choose_spec
    (boundary_atomicLinear_tangent_scalar_of_A1_spanning
      hlin htangent F hax hV q r hq hnd)).2 η hηatomic hηtan

/-- A boundary coefficient normalization whose positive coefficient is proved
to exist from pure-trace nontriviality, finite-branch aggregation, and atomic
tangent spanning. -/
noncomputable def boundaryCoefficientScaleNormalization_of_A1_atomicLinearTangentSpanning
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u} where
  boundaryCoeff := fun {A} _ _ _ q r =>
    boundaryAtomicLinearTangentCoeffOfA1Spanning
      hlin htangent F hax hV q r
  boundaryCoeff_pos := by
    intro A _ _ _ q r hq _hr_nonempty hr_nondegenerate _hr_boundary
    classical
    haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
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
    exact boundaryAtomicLinearTangentCoeffOfA1Spanning_pos
      hlin htangent F hax hV q r hq hrs_nd

/-- Boundary summand identity from selected support-face value transport and
coefficient transport. -/
theorem branchFormulaBoundarySummandFor_of_value_for_and_coefficient_transport
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary) :
    FiniteBranchFormulaBoundarySummandFor F hax hV hlin hboundary where
  boundary_summand_linearPart_eq := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ target
      hr_nonempty hr_nondegenerate hr_boundary Q
    classical
    let r : Dist A := branchPosterior P₁ q target
    let m : ℝ := (Channel.outcomeMarginal P₁ q) target
    haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
    let η : PosteriorLawSigned (supportSubtype r) :=
      posteriorLawDifferenceExp r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))
    have hηtan : PosteriorLawTangent η := by
      exact posteriorLawDifferenceExp_tangent r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))
    have hdiff_ext :
        ∀ φ : Dist A → ℝ,
          posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A)) φ =
            (fun φ : Dist A → ℝ =>
              η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))) φ := by
      intro φ
      exact posteriorLawDifferenceExp_restrictToSupport_pushforward r Q φ
    have hdiff_linear :
        hlin.linearPart F hV q
            (posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))) =
          hlin.linearPart F hV q
            (fun φ : Dist A → ℝ =>
              η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))) :=
      hlin.linearPart_ext F hV q
        (posteriorLawDifferenceExp r
          (experimentOfChannel Q)
          (experimentOfChannel (Channel.uninformativeChannelU A)))
        (fun φ : Dist A → ℝ =>
          η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))))
        hdiff_ext
    have hscalar :
        hlin.linearPart F hV q
            (posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))) =
          hboundary.boundaryCoeff q r *
            hlin.linearPart F hV r.restrictToSupport η := by
      rw [hdiff_linear]
      exact hcoeff.boundary_linear_part_scalar
        F hax hV q r hq
        (by simpa [r] using hr_nonempty)
        (by simpa [r] using hr_nondegenerate)
        (by simpa [r] using hr_boundary)
        η hηtan
    have hface_linear :
        hlin.linearPart F hV r.restrictToSupport η =
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport Q r)) := by
      have hdiff :=
        (hlin.value_difference F hV r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport Q r))
          (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))).symm
      have hzero :
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r))) = 0 :=
        hV.zero_normalized r.restrictToSupport
          (Dist.restrictToSupport_fullSupport r)
      rw [hzero, sub_zero] at hdiff
      simpa [η] using hdiff
    have hvalue_transport :
        hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport Q r)) =
          hV.V r (experimentOfChannel Q) := by
      exact (hvalue.boundary_value_transport r Q).symm
    calc
      hlin.linearPart F hV q
          (posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
            (posteriorLawDifferenceExp (branchPosterior P₁ q target)
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))))
          =
        m * hlin.linearPart F hV q
          (posteriorLawDifferenceExp r
            (experimentOfChannel Q)
            (experimentOfChannel (Channel.uninformativeChannelU A))) := by
          rw [hlin.linearPart_smul]
      _ =
        m * (hboundary.boundaryCoeff q r *
          hlin.linearPart F hV r.restrictToSupport η) := by
          rw [hscalar]
      _ =
        m * hboundary.boundaryCoeff q r *
          hV.V r (experimentOfChannel Q) := by
          rw [hface_linear, hvalue_transport]
          ring
      _ =
        (Channel.outcomeMarginal P₁ q) target *
          hboundary.boundaryCoeff q (branchPosterior P₁ q target) *
          hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
          simp [m, r]

/-- Boundary summand identity from selected support-face value transport and
the corrected atomic marginal-value transport theorem.

The only support-face tangent used here is the posterior-law difference induced
by a continuation experiment on the positive face, and this signed law is
atomic-linear. -/
theorem branchFormulaBoundarySummandFor_of_value_for_and_marginal_transport_atomic
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAtomicFor
        F hax hV hint hboundary) :
    FiniteBranchFormulaBoundarySummandFor F hax hV
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint)
      hboundary where
  boundary_summand_linearPart_eq := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ target
      hr_nonempty hr_nondegenerate hr_boundary Q
    classical
    let hlin := finiteAffineLinearPartAssumptions_of_integralRepresentation hint
    let r : Dist A := branchPosterior P₁ q target
    let m : ℝ := (Channel.outcomeMarginal P₁ q) target
    haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
    let η : PosteriorLawSigned (supportSubtype r) :=
      posteriorLawDifferenceExp r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))
    have hηatomic : PosteriorLawSigned.AtomicLinear η := by
      exact posteriorLawDifferenceExp_atomicLinear r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))
    have hηtan : PosteriorLawTangent η := by
      exact posteriorLawDifferenceExp_tangent r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))
    have hdiff_ext :
        ∀ φ : Dist A → ℝ,
          posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A)) φ =
            (fun φ : Dist A → ℝ =>
              η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))) φ := by
      intro φ
      exact posteriorLawDifferenceExp_restrictToSupport_pushforward r Q φ
    have hdiff_linear :
        hlin.linearPart F hV q
            (posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))) =
          hlin.linearPart F hV q
            (fun φ : Dist A → ℝ =>
              η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))) :=
      hlin.linearPart_ext F hV q
        (posteriorLawDifferenceExp r
          (experimentOfChannel Q)
          (experimentOfChannel (Channel.uninformativeChannelU A)))
        (fun φ : Dist A → ℝ =>
          η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))))
        hdiff_ext
    have hscalar :
        hlin.linearPart F hV q
            (posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))) =
          hboundary.boundaryCoeff q r *
            hlin.linearPart F hV r.restrictToSupport η := by
      rw [hdiff_linear]
      exact hmarginal.support_face_marginalValue_scalar_atomic
        q r hq
        (by simpa [r] using hr_nonempty)
        (by simpa [r] using hr_nondegenerate)
        (by simpa [r] using hr_boundary)
        η hηatomic hηtan
    have hface_linear :
        hlin.linearPart F hV r.restrictToSupport η =
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport Q r)) := by
      have hdiff :=
        (hlin.value_difference F hV r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport Q r))
          (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r)))).symm
      have hzero :
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.uninformativeChannelU (supportSubtype r))) = 0 :=
        hV.zero_normalized r.restrictToSupport
          (Dist.restrictToSupport_fullSupport r)
      rw [hzero, sub_zero] at hdiff
      simpa [η] using hdiff
    have hvalue_transport :
        hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport Q r)) =
          hV.V r (experimentOfChannel Q) := by
      exact (hvalue.boundary_value_transport r Q).symm
    calc
      hlin.linearPart F hV q
          (posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
            (posteriorLawDifferenceExp (branchPosterior P₁ q target)
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))))
          =
        m * hlin.linearPart F hV q
          (posteriorLawDifferenceExp r
            (experimentOfChannel Q)
            (experimentOfChannel (Channel.uninformativeChannelU A))) := by
          rw [hlin.linearPart_smul]
      _ =
        m * (hboundary.boundaryCoeff q r *
          hlin.linearPart F hV r.restrictToSupport η) := by
          rw [hscalar]
      _ =
        m * hboundary.boundaryCoeff q r *
          hV.V r (experimentOfChannel Q) := by
          rw [hface_linear, hvalue_transport]
          ring
      _ =
        (Channel.outcomeMarginal P₁ q) target *
          hboundary.boundaryCoeff q (branchPosterior P₁ q target) *
          hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
          simp [m, r]

/-- Boundary summand identity from the historical universal support-face value
transport package and coefficient transport. -/
theorem branchFormulaBoundarySummandFor_of_value_and_coefficient_transport
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hvalue : FiniteBranchBoundaryValueTransportAssumptions.{u})
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBranchFormulaBoundarySummandFor F hax hV hlin hboundary :=
  branchFormulaBoundarySummandFor_of_value_for_and_coefficient_transport
    F hax hV hlin hboundary
    (boundaryValueTransportFor_of_boundaryValueTransport hvalue F hax hV)
    hcoeff

/-- Singleton branch coefficient normalization.

If a reached posterior has singleton support, all continuation values on the
intrinsic support face are zero.  The coefficient multiplying that zero term is
not behaviourally identified; the paper fixes it by positive normalization so the
aggregation and chain formulas have uniform notation. -/
structure FiniteBranchSingletonScaleNormalizationAssumptions where
  singletonCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  singletonCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr_singleton_support :
        ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a),
      0 < singletonCoeff q r
  singleton_branch_value_zero :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (r : Dist A)
      (_hr_singleton_support :
        ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
      (P : Channel A O),
      hV.V r (experimentOfChannel P) = 0

/-- Singleton coefficient data for one selected posterior-value
representative.

Unlike the historical universal package above, this record makes no assertion
about arbitrary gauge transforms of the selected representative.  It is the
appropriate branch-layer interface once the HM output has been canonically
normalised. -/

structure FiniteBranchSingletonScaleNormalizationFor
    (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F) where
  singletonCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  singletonCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr_singleton_support :
        ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a),
      0 < singletonCoeff q r
  singleton_branch_value_zero :
    ∀ {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (r : Dist A)
      (_hr_singleton_support :
        ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
      (P : Channel A O),
      hV.V r (experimentOfChannel P) = 0

/-- Specialize the historical universal singleton package to one
representative.  This compatibility coercion is one-way: the selected package
does not imply the false universal assertion. -/
def FiniteBranchSingletonScaleNormalizationAssumptions.forRepresentative
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{v})
    (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F) :
    FiniteBranchSingletonScaleNormalizationFor F hV where
  singletonCoeff := hsingle.singletonCoeff
  singletonCoeff_pos := hsingle.singletonCoeff_pos
  singleton_branch_value_zero :=
    hsingle.singleton_branch_value_zero F hV

instance {F : PrefFamily.{v}} {hV : PosteriorValueRepresentation F} :
    Coe (FiniteBranchSingletonScaleNormalizationAssumptions.{v})
      (FiniteBranchSingletonScaleNormalizationFor F hV) :=
  ⟨fun hsingle => hsingle.forRepresentative F hV⟩

end TraceableAgency
