/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.Reachability

namespace TraceableAgency

universe u v

/-!
## Representation-level path scalar

The paper first proves the path-independent branch coefficient at the level of
the affine linear parts for a fixed coherent value representative.  The older
`FiniteBranchPathIndependenceAssumptions` below packages a global coefficient
directly.  The following declarations split out the narrower full-support
linear-algebra core: tangent sign preservation plus the finite same-sign
theorem gives a positive scalar relating `L_q` and `L_r`.
-/

/-- Tangent sign-preservation interface for the branch path argument.

This is the A6/realization part after tangent-space spanning has reduced the
problem to signed posterior-law directions: on nonzero tangent directions, the
aggregate prior linear part and the reached-posterior linear part have the same
positive half-space and zero set. -/
structure FiniteBranchTangentSignPreservationAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  tangent_sign_preservation :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (η : PosteriorLawSigned A),
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
        (0 < hlin.linearPart F hV q η ↔
          0 < hlin.linearPart F hV r η) ∧
        (hlin.linearPart F hV q η = 0 ↔
          hlin.linearPart F hV r η = 0)
  branch_linear_nonzero :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      ∃ η : PosteriorLawSigned A, hlin.linearPart F hV r η ≠ 0

/-- The sign-agreement part of tangent sign preservation, separated from the
nonzero branch-linear-functional witness. -/
structure FiniteBranchTangentSignAgreementAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  tangent_sign_preservation :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (η : PosteriorLawSigned A),
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
        (0 < hlin.linearPart F hV q η ↔
          0 < hlin.linearPart F hV r η) ∧
        (hlin.linearPart F hV q η = 0 ↔
          hlin.linearPart F hV r η = 0)

/-- Faithful A6-aware tangent-domain sign agreement for a fixed
representation.

Unlike the legacy `FiniteBranchTangentSignAgreementAssumptions`, this package
carries `PureTraceConditions F` and restricts the assertion to genuine tangent signed
posterior laws. -/
structure BranchTangentSignAgreementOnTangentFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u}) : Prop where
  tangent_sign_preservation_on_tangent :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (η : PosteriorLawSigned A),
      PosteriorLawTangent η →
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
        (0 < hlin.linearPart F hV q η ↔
          0 < hlin.linearPart F hV r η) ∧
        (hlin.linearPart F hV q η = 0 ↔
          hlin.linearPart F hV r η = 0)

/-- The forward and zero half of tangent sign preservation.

This is exactly what the one-branch continuation plumbing proves directly.  The reverse
positive direction is the remaining swapped-direction realization step. -/
structure BranchTangentForwardZeroOnTangentFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u}) : Prop where
  forward_zero_on_tangent :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (η : PosteriorLawSigned A),
      PosteriorLawTangent η →
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
        (0 < hlin.linearPart F hV r η →
          0 < hlin.linearPart F hV q η) ∧
        (hlin.linearPart F hV r η = 0 →
          hlin.linearPart F hV q η = 0)

/-- Common-outcome tangent realization plus full-support branch reachability
gives the forward/zero tangent-sign package. -/
theorem branchTangentForwardZeroOnTangentFor_of_realization
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hreal : FiniteCommonOutcomeTangentRealizationAssumptions.{u})
    (hreach : FiniteFullSupportBranchReachabilityAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchTangentForwardZeroOnTangentFor F hax hV hlin where
  forward_zero_on_tangent := by
    intro A _ _ _ q r hq hr η htan hη_ne
    rcases hreal.tangent_as_common_outcome_difference r hr η htan hη_ne with
      ⟨t, ht, O, hO, hOdec, hrealized⟩
    letI : Fintype O := hO
    letI : DecidableEq O := hOdec
    rcases hrealized with ⟨P, R, hη⟩
    rcases hreach.reaches q r hq hr with
      ⟨O₁, hO₁, hO₁dec, hreachable⟩
    letI : Fintype O₁ := hO₁
    letI : DecidableEq O₁ := hO₁dec
    rcases hreachable with ⟨P₁, target, hpos, hpost⟩
    exact branch_tangent_forward_zero_of_commonOutcome_realization
      hlin F hax hV q r hq hr η t ht P R hη P₁ target hpos hpost

/-- Forward/zero transport on tangent directions gives full tangent-domain sign
agreement by applying the forward positive implication to `-η`. -/
theorem branchTangentSignAgreementOnTangentFor_of_forwardZero_and_neg
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hforward : BranchTangentForwardZeroOnTangentFor F hax hV hlin) :
    BranchTangentSignAgreementOnTangentFor F hax hV hlin where
  tangent_sign_preservation_on_tangent := by
    intro A _ _ _ q r hq hr _hr_nondegenerate η htan hηne
    let negη : PosteriorLawSigned A := posteriorLawSignedSMul (-1) η
    have hneg_tan : PosteriorLawTangent negη :=
      PosteriorLawTangent_neg htan
    have hneg_ne : negη ≠ ((fun _ => 0) : PosteriorLawSigned A) :=
      posteriorLawSignedSMul_neg_ne_zero hηne
    have hfwd := hforward.forward_zero_on_tangent q r hq hr η htan hηne
    have hfwd_neg :=
      hforward.forward_zero_on_tangent q r hq hr negη hneg_tan hneg_ne
    have hq_neg :
        hlin.linearPart F hV q negη =
          -hlin.linearPart F hV q η := by
      simp [negη, hlin.linearPart_smul]
    have hr_neg :
        hlin.linearPart F hV r negη =
          -hlin.linearPart F hV r η := by
      simp [negη, hlin.linearPart_smul]
    constructor
    · constructor
      · intro hqpos
        by_contra hrnot
        have hrle : hlin.linearPart F hV r η ≤ 0 := le_of_not_gt hrnot
        by_cases hrzero : hlin.linearPart F hV r η = 0
        · have hqzero := hfwd.2 hrzero
          linarith
        · have hrlt : hlin.linearPart F hV r η < 0 :=
            lt_of_le_of_ne hrle hrzero
          have hrnegpos : 0 < hlin.linearPart F hV r negη := by
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
        · have hrnegpos : 0 < hlin.linearPart F hV r negη := by
            rw [hr_neg]
            linarith
          have hqnegpos := hfwd_neg.1 hrnegpos
          rw [hq_neg] at hqnegpos
          linarith
        · have hqpos := hfwd.1 hrpos
          linarith
      · exact hfwd.2

/-- Common-outcome tangent realization and full-support reachability close the
faithful A6-aware tangent-domain sign agreement package. -/
theorem branchTangentSignAgreementOnTangentFor_of_realization_and_reachability
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hreal : FiniteCommonOutcomeTangentRealizationAssumptions.{u})
    (hreach : FiniteFullSupportBranchReachabilityAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchTangentSignAgreementOnTangentFor F hax hV hlin :=
  branchTangentSignAgreementOnTangentFor_of_forwardZero_and_neg hlin F hax hV
    (branchTangentForwardZeroOnTangentFor_of_realization hlin hreal hreach
      F hax hV)

/-- Finite tangent spanning plus the internal full-support branch reachability
construction gives the faithful tangent-domain sign agreement package. -/
theorem branchTangentSignAgreementOnTangentFor_of_tangentSpanning
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FinitePosteriorTangentSpaceSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchTangentSignAgreementOnTangentFor F hax hV hlin :=
  branchTangentSignAgreementOnTangentFor_of_realization_and_reachability hlin
    (commonOutcomeTangentRealization_of_tangentSpanning htangent)
    fullSupportBranchReachability_of_finite F hax hV

/-- Nonzero branch-linear-functional witness for nondegenerate full-support
posterior values. -/
structure FiniteBranchLinearPartNonzeroAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  branch_linear_nonzero :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      ∃ η : PosteriorLawSigned A, hlin.linearPart F hV r η ≠ 0

/-- Nontriviality-aware nonzero branch-linear-functional witness.

This is the faithful version of the nonzero witness proved in this stage.  The
legacy `FiniteBranchLinearPartNonzeroAssumptions` above omits `PureTraceConditions F`;
without some nontriviality hypothesis on `F`, a constant value representation
and zero linear part would satisfy the representation/linearity interfaces but
make the nonzero conclusion false. -/
structure FiniteBranchLinearPartNonzeroFromA1Assumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  branch_linear_nonzero_of_axioms :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      ∃ η : PosteriorLawSigned A, hlin.linearPart F hV r η ≠ 0

/-- Package the A1-derived nonzero witness as a narrow faithful interface. -/
theorem branchLinearPartNonzeroFromA1_of_linearPart
    (hlin : FiniteAffineLinearPartAssumptions.{u}) :
    FiniteBranchLinearPartNonzeroFromA1Assumptions.{u} hlin where
  branch_linear_nonzero_of_axioms := by
    intro F hax hV A _ _ _ q r hq hr hnd
    exact branch_linear_part_nonzero_of_A1 hlin F hax hV q r hq hr hnd

/-- Representation-level tangent sign agreement for a fixed axiomatized
preference family and value representative.

The nonzero branch-linear witness is intentionally not bundled here; it is
supplied by pure-trace nontriviality through `branch_linear_part_nonzero_of_A1`. -/
structure BranchTangentSignPreservationFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u}) : Prop where
  tangent_sign_preservation :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (η : PosteriorLawSigned A),
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
        (0 < hlin.linearPart F hV q η ↔
          0 < hlin.linearPart F hV r η) ∧
        (hlin.linearPart F hV q η = 0 ↔
          hlin.linearPart F hV r η = 0)

/-- The old sign-agreement interface specializes to the representation-level
`For` package. -/
theorem branchTangentSignPreservationFor_of_signAgreement
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsign : FiniteBranchTangentSignAgreementAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchTangentSignPreservationFor F hax hV hlin where
  tangent_sign_preservation := by
    intro A _ _ _ q r hq hr hnd η hη
    exact hsign.tangent_sign_preservation F hV q r hq hr hnd η hη

/-- Reconstruct the old tangent sign-preservation package from its two
separated components. -/
theorem branchTangentSignPreservation_of_signAgreement_and_nonzero
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsign : FiniteBranchTangentSignAgreementAssumptions.{u} hlin)
    (hnonzero : FiniteBranchLinearPartNonzeroAssumptions.{u} hlin) :
    FiniteBranchTangentSignPreservationAssumptions.{u} hlin := by
  exact
    { tangent_sign_preservation := hsign.tangent_sign_preservation
      branch_linear_nonzero := hnonzero.branch_linear_nonzero }

/-- Same-sign tangent preservation gives the positive scalar relation between
the aggregate and branch linear parts. -/
theorem branch_linear_scalar_exists_of_tangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (htsign : FiniteBranchTangentSignPreservationAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ β : ℝ, 0 < β ∧
      ∀ η : PosteriorLawSigned A,
        hlin.linearPart F hV q η = β * hlin.linearPart F hV r η := by
  exact hsignscalar.same_sign_scalar
    (hlin.linearPart F hV q)
    (hlin.linearPart F hV r)
    (hlin.linearPart_add F hV q)
    (hlin.linearPart_smul F hV q)
    (hlin.linearPart_add F hV r)
    (hlin.linearPart_smul F hV r)
    (htsign.tangent_sign_preservation F hV q r hq hr hr_nondegenerate)
    (htsign.branch_linear_nonzero F hV q r hq hr hr_nondegenerate)

/-- Positive scalar coefficient obtained from tangent sign preservation for a
fixed value representative.  It is intentionally representation-level: the old
global path-independence package below additionally requires coherence of these
scalars with the globally chosen branch coefficient notation. -/
noncomputable def branchPathScalarCoeffOfTangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (htsign : FiniteBranchTangentSignPreservationAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ := by
  classical
  exact
    if hq : q.FullSupport then
      if hr : r.FullSupport then
        if hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b then
          Classical.choose
            (branch_linear_scalar_exists_of_tangentSign
              hlin hsignscalar htsign F hV q r hq hr hnd)
        else 1
      else 1
    else 1

theorem branchPathScalarCoeffOfTangentSign_eq_choose
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (htsign : FiniteBranchTangentSignPreservationAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    branchPathScalarCoeffOfTangentSign hlin hsignscalar htsign F hV q r =
      Classical.choose
        (branch_linear_scalar_exists_of_tangentSign
          hlin hsignscalar htsign F hV q r hq hr hr_nondegenerate) := by
  classical
  unfold branchPathScalarCoeffOfTangentSign
  simp [hq, hr, hr_nondegenerate]

theorem branchPathScalarCoeffOfTangentSign_pos
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (htsign : FiniteBranchTangentSignPreservationAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    0 < branchPathScalarCoeffOfTangentSign hlin hsignscalar htsign F hV q r := by
  rw [branchPathScalarCoeffOfTangentSign_eq_choose
    hlin hsignscalar htsign F hV q r hq hr hr_nondegenerate]
  exact (Classical.choose_spec
    (branch_linear_scalar_exists_of_tangentSign
      hlin hsignscalar htsign F hV q r hq hr hr_nondegenerate)).1

theorem branchPathScalarCoeffOfTangentSign_relation
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (htsign : FiniteBranchTangentSignPreservationAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (η : PosteriorLawSigned A) :
    hlin.linearPart F hV q η =
      branchPathScalarCoeffOfTangentSign hlin hsignscalar htsign F hV q r *
        hlin.linearPart F hV r η := by
  rw [branchPathScalarCoeffOfTangentSign_eq_choose
    hlin hsignscalar htsign F hV q r hq hr hr_nondegenerate]
  exact (Classical.choose_spec
    (branch_linear_scalar_exists_of_tangentSign
      hlin hsignscalar htsign F hV q r hq hr hr_nondegenerate)).2 η

/-- Representation-level full-support path scalar structure. -/
structure BranchPathScalarStructure
    (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{v}) where
  branchPathCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  branchPathCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      0 < branchPathCoeff q r
  linear_part_scalar_relation :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (η : PosteriorLawSigned A),
      hlin.linearPart F hV q η =
        branchPathCoeff q r * hlin.linearPart F hV r η

/-- Representation-level full-support path scalar restricted to atomic-linear
tangent directions.  This is the faithful object produced by the corrected A6
tangent-sign route; the broader `BranchPathScalarStructure` asserts the scalar
relation on all extensional signed laws. -/
structure BranchPathTangentScalarStructure
    (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{v}) where
  branchPathCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  branchPathCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      0 < branchPathCoeff q r
  linear_part_scalar_relation_on_tangent :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (η : PosteriorLawSigned A),
      PosteriorLawSigned.AtomicLinear η →
      PosteriorLawTangent η →
      hlin.linearPart F hV q η =
        branchPathCoeff q r * hlin.linearPart F hV r η

/-- Tangent-domain sign agreement plus the tangent same-sign scalar theorem
gives a positive scalar relation on the tangent subspace. -/
theorem branch_linear_tangent_scalar_exists_of_A1_tangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignAgreementOnTangentFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ β : ℝ, 0 < β ∧
      ∀ η : PosteriorLawSigned A, PosteriorLawTangent η →
        hlin.linearPart F hV q η = β * hlin.linearPart F hV r η := by
  exact hsignscalar.same_sign_scalar_on_tangent
    (hlin.linearPart F hV q)
    (hlin.linearPart F hV r)
    (hlin.linearPart_add F hV q)
    (hlin.linearPart_smul F hV q)
    (hlin.linearPart_add F hV r)
    (hlin.linearPart_smul F hV r)
    (hsign.tangent_sign_preservation_on_tangent q r hq hr hr_nondegenerate)
    (branch_linear_part_nonzero_tangent_of_A1 hlin F hax hV q r hq hr hr_nondegenerate)

/-- A1-aware tangent scalar coefficient for a fixed representative. -/
noncomputable def branchPathTangentScalarCoeffOfA1TangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignAgreementOnTangentFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ := by
  classical
  exact
    if hq : q.FullSupport then
      if hr : r.FullSupport then
        if hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b then
          Classical.choose
            (branch_linear_tangent_scalar_exists_of_A1_tangentSign
              hlin hsignscalar F hax hV hsign q r hq hr hnd)
        else 1
      else 1
    else 1

theorem branchPathTangentScalarCoeffOfA1TangentSign_eq_choose
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignAgreementOnTangentFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    branchPathTangentScalarCoeffOfA1TangentSign hlin hsignscalar
        F hax hV hsign q r =
      Classical.choose
        (branch_linear_tangent_scalar_exists_of_A1_tangentSign
          hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate) := by
  classical
  unfold branchPathTangentScalarCoeffOfA1TangentSign
  simp [hq, hr, hr_nondegenerate]

theorem branchPathTangentScalarCoeffOfA1TangentSign_pos
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignAgreementOnTangentFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    0 < branchPathTangentScalarCoeffOfA1TangentSign
      hlin hsignscalar F hax hV hsign q r := by
  rw [branchPathTangentScalarCoeffOfA1TangentSign_eq_choose
    hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate]
  exact (Classical.choose_spec
    (branch_linear_tangent_scalar_exists_of_A1_tangentSign
      hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate)).1

theorem branchPathTangentScalarCoeffOfA1TangentSign_relation
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignAgreementOnTangentFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (η : PosteriorLawSigned A) (hηtan : PosteriorLawTangent η) :
    hlin.linearPart F hV q η =
      branchPathTangentScalarCoeffOfA1TangentSign
        hlin hsignscalar F hax hV hsign q r *
        hlin.linearPart F hV r η := by
  rw [branchPathTangentScalarCoeffOfA1TangentSign_eq_choose
    hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate]
  exact (Classical.choose_spec
    (branch_linear_tangent_scalar_exists_of_A1_tangentSign
      hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate)).2 η hηtan

/-- Build the tangent-subspace scalar structure from the faithful tangent-sign
agreement route. -/
noncomputable def branchPathTangentScalarStructure_of_A1_tangentSignOnTangent
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u})
    (htangent : FinitePosteriorTangentSpaceSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchPathTangentScalarStructure F hV hlin where
  branchPathCoeff := fun q r =>
    branchPathTangentScalarCoeffOfA1TangentSign hlin hsignscalar F hax hV
      (branchTangentSignAgreementOnTangentFor_of_tangentSpanning hlin htangent F hax hV) q r
  branchPathCoeff_pos := by
    intro A _ _ _ q r hq hr hnd
    exact branchPathTangentScalarCoeffOfA1TangentSign_pos
      hlin hsignscalar F hax hV
      (branchTangentSignAgreementOnTangentFor_of_tangentSpanning hlin htangent F hax hV)
      q r hq hr hnd
  linear_part_scalar_relation_on_tangent := by
    intro A _ _ _ q r hq hr hnd η _hηatomic hηtan
    exact branchPathTangentScalarCoeffOfA1TangentSign_relation
      hlin hsignscalar F hax hV
      (branchTangentSignAgreementOnTangentFor_of_tangentSpanning hlin htangent F hax hV)
      q r hq hr hnd η hηtan

/-- Core algebraic lemma: atomic-linear tangent spanning gives a positive scalar
β with linearPart q η = β * linearPart r η for all atomic-linear tangent η.

The proof proceeds by:
1. Forward-zero from common-outcome realization of atomic-linear tangent η
2. Sign agreement for atomic-linear tangent η (forward + reverse via -η)
3. Same-sign-scalar algebraic argument restricted to atomic-linear subspace -/
theorem atomicLinear_tangent_scalar_of_A1_spanning
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ β : ℝ, 0 < β ∧
      ∀ (η : PosteriorLawSigned A),
        PosteriorLawSigned.AtomicLinear η → PosteriorLawTangent η →
        hlin.linearPart F hV q η = β * hlin.linearPart F hV r η := by
  have hforward :
      ∀ (η : PosteriorLawSigned A),
        PosteriorLawSigned.AtomicLinear η →
        PosteriorLawTangent η →
        η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
        (0 < hlin.linearPart F hV r η → 0 < hlin.linearPart F hV q η) ∧
        (hlin.linearPart F hV r η = 0 → hlin.linearPart F hV q η = 0) := by
    intro η hηatomic htan hηne
    rcases commonOutcomeAtomicLinearTangentRealization_of_atomicLinearSpanning
        htangent r hr η hηatomic htan hηne with
      ⟨t, ht, O, hO, hOdec, hrealized⟩
    letI : Fintype O := hO
    letI : DecidableEq O := hOdec
    rcases hrealized with ⟨P, R, hη⟩
    rcases fullSupportBranchReachability_of_finite.reaches q r hq hr with
      ⟨O₁, hO₁, hO₁dec, hreachable⟩
    letI : Fintype O₁ := hO₁
    letI : DecidableEq O₁ := hO₁dec
    rcases hreachable with ⟨P₁, target, hpos, hpost⟩
    exact branch_tangent_forward_zero_of_commonOutcome_realization
      hlin F hax hV q r hq hr η t ht P R hη P₁ target hpos hpost
  have hsign :
      ∀ (η : PosteriorLawSigned A),
        PosteriorLawSigned.AtomicLinear η →
        PosteriorLawTangent η →
        η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
        (0 < hlin.linearPart F hV q η ↔ 0 < hlin.linearPart F hV r η) ∧
        (hlin.linearPart F hV q η = 0 ↔ hlin.linearPart F hV r η = 0) := by
    intro η hηatomic htan hηne
    have hfwd := hforward η hηatomic htan hηne
    let negη := posteriorLawSignedSMul (-1) η
    have hneg_atomic := PosteriorLawSigned.AtomicLinear.smul (-1) hηatomic
    have hneg_tan := PosteriorLawTangent_neg htan
    have hneg_ne := posteriorLawSignedSMul_neg_ne_zero hηne
    have hfwd_neg := hforward negη hneg_atomic hneg_tan hneg_ne
    have hq_neg : hlin.linearPart F hV q negη = -hlin.linearPart F hV q η := by
      simp [negη, hlin.linearPart_smul]
    have hr_neg : hlin.linearPart F hV r negη = -hlin.linearPart F hV r η := by
      simp [negη, hlin.linearPart_smul]
    constructor
    · constructor
      · intro hqpos
        by_contra hrnot
        have hrle := le_of_not_gt hrnot
        by_cases hrzero : hlin.linearPart F hV r η = 0
        · linarith [hfwd.2 hrzero]
        · have hrlt : hlin.linearPart F hV r η < 0 := lt_of_le_of_ne hrle hrzero
          have hrnegpos : 0 < hlin.linearPart F hV r negη := by rw [hr_neg]; linarith
          linarith [hfwd_neg.1 hrnegpos, hq_neg]
      · intro hrpos
        exact hfwd.1 hrpos
    · constructor
      · intro hqzero
        by_contra hrne
        rcases lt_or_gt_of_ne hrne with hrlt | hrpos
        · have hrnegpos : 0 < hlin.linearPart F hV r negη := by rw [hr_neg]; linarith
          linarith [hfwd_neg.1 hrnegpos, hq_neg]
        · linarith [hfwd.1 hrpos]
      · exact hfwd.2
  rcases branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV q r hq hr hr_nondegenerate with
    ⟨x0, hx0_atomic, hx0_tan, hx0_nz⟩
  have hx0_ne : x0 ≠ ((fun _ => 0) : PosteriorLawSigned A) := by
    intro hx0_eq
    exact hx0_nz (by rw [hx0_eq]; exact linearPart_zero hlin F hV r)
  let x : PosteriorLawSigned A :=
    if 0 < hlin.linearPart F hV r x0 then x0
    else posteriorLawSignedSMul (-1) x0
  have hx_atomic : PosteriorLawSigned.AtomicLinear x := by
    dsimp [x]; split_ifs
    · exact hx0_atomic
    · exact PosteriorLawSigned.AtomicLinear.smul (-1) hx0_atomic
  have hx_tan : PosteriorLawTangent x := by
    dsimp [x]; split_ifs
    · exact hx0_tan
    · exact PosteriorLawTangent_smul (-1) hx0_tan
  have hx_ne : x ≠ ((fun _ => 0) : PosteriorLawSigned A) := by
    dsimp [x]; split_ifs
    · exact hx0_ne
    · exact posteriorLawSignedSMul_neg_ne_zero hx0_ne
  have hx_Lr_pos : 0 < hlin.linearPart F hV r x := by
    dsimp [x]; split_ifs with hpos
    · exact hpos
    · have hle : hlin.linearPart F hV r x0 ≤ 0 := le_of_not_gt hpos
      have hlt : hlin.linearPart F hV r x0 < 0 :=
        lt_of_le_of_ne hle hx0_nz
      rw [hlin.linearPart_smul]; linarith
  have hx_Lr_ne : hlin.linearPart F hV r x ≠ 0 := ne_of_gt hx_Lr_pos
  have hx_Lq_pos : 0 < hlin.linearPart F hV q x :=
    (hsign x hx_atomic hx_tan hx_ne).1.mpr hx_Lr_pos
  let β : ℝ := hlin.linearPart F hV q x / hlin.linearPart F hV r x
  have hβ_pos : 0 < β := div_pos hx_Lq_pos hx_Lr_pos
  refine ⟨β, hβ_pos, ?_⟩
  intro y hy_atomic hy_tan
  by_cases hy_ne : y = ((fun _ => 0) : PosteriorLawSigned A)
  · rw [hy_ne]
    simp [linearPart_zero hlin F hV q, linearPart_zero hlin F hV r]
  · let c : ℝ := -(hlin.linearPart F hV r y / hlin.linearPart F hV r x)
    let z : PosteriorLawSigned A :=
      posteriorLawSignedAdd y (posteriorLawSignedSMul c x)
    have hz_atomic : PosteriorLawSigned.AtomicLinear z :=
      PosteriorLawSigned.AtomicLinear.add hy_atomic
        (PosteriorLawSigned.AtomicLinear.smul c hx_atomic)
    have hz_tan : PosteriorLawTangent z :=
      PosteriorLawTangent_add hy_tan (PosteriorLawTangent_smul c hx_tan)
    have hz_Lr : hlin.linearPart F hV r z = 0 := by
      have hstep : hlin.linearPart F hV r z =
          hlin.linearPart F hV r y + c * hlin.linearPart F hV r x := by
        calc hlin.linearPart F hV r z
            = hlin.linearPart F hV r (posteriorLawSignedAdd y (posteriorLawSignedSMul c x)) := rfl
          _ = hlin.linearPart F hV r y + c * hlin.linearPart F hV r x := by
              rw [hlin.linearPart_add, hlin.linearPart_smul]
      rw [hstep]
      have hc_val : c = -(hlin.linearPart F hV r y / hlin.linearPart F hV r x) := rfl
      have hdiv := div_mul_cancel₀ (hlin.linearPart F hV r y) hx_Lr_ne
      linarith [hc_val, hdiv]
    have hz_Lq : hlin.linearPart F hV q z = 0 := by
      by_cases hz_ne : z = ((fun _ => 0) : PosteriorLawSigned A)
      · rw [hz_ne]; exact linearPart_zero hlin F hV q
      · exact (hsign z hz_atomic hz_tan hz_ne).2.2 hz_Lr
    have hLq_z_expand :
        hlin.linearPart F hV q y + c * hlin.linearPart F hV q x = 0 := by
      have hzq : hlin.linearPart F hV q z =
          hlin.linearPart F hV q y + c * hlin.linearPart F hV q x := by
        calc hlin.linearPart F hV q z
            = hlin.linearPart F hV q (posteriorLawSignedAdd y (posteriorLawSignedSMul c x)) := rfl
          _ = hlin.linearPart F hV q y + c * hlin.linearPart F hV q x := by
              rw [hlin.linearPart_add, hlin.linearPart_smul]
      linarith [hzq, hz_Lq]
    have hβ_eq : β = hlin.linearPart F hV q x / hlin.linearPart F hV r x := rfl
    show hlin.linearPart F hV q y = β * hlin.linearPart F hV r y
    have hc_expand : c = -(hlin.linearPart F hV r y / hlin.linearPart F hV r x) := rfl
    have hLqy : hlin.linearPart F hV q y = -c * hlin.linearPart F hV q x := by
      linarith [hLq_z_expand]
    rw [hLqy, hc_expand, hβ_eq]
    field_simp

/-- Build the tangent-subspace scalar structure from the corrected atomic-linear
tangent spanning, bypassing the legacy broad interface entirely.

The proof builds forward-zero for atomic-linear tangent η from the spanning, then
derives the scalar relation by an inline same-sign-scalar argument restricted to
the atomic-linear subspace (which is closed under add and smul). -/
noncomputable def branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (_hsignscalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchPathTangentScalarStructure F hV hlin where
  branchPathCoeff := fun {A} [Fintype A] [DecidableEq A] [Nonempty A] (q r : Dist A) => by
    classical
    exact
      if hq : q.FullSupport then
        if hr : r.FullSupport then
          if hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b then
            Classical.choose (atomicLinear_tangent_scalar_of_A1_spanning
              hlin htangent F hax hV q r hq hr hnd)
          else 1
        else 1
      else 1
  branchPathCoeff_pos := by
    intro A _ _ _ q r hq hr hnd
    simp [hq, hr, hnd]
    exact (Classical.choose_spec (atomicLinear_tangent_scalar_of_A1_spanning
      hlin htangent F hax hV q r hq hr hnd)).1
  linear_part_scalar_relation_on_tangent := by
    intro A _ _ _ q r hq hr hnd η hηatomic hηtan
    simp [hq, hr, hnd]
    exact (Classical.choose_spec (atomicLinear_tangent_scalar_of_A1_spanning
      hlin htangent F hax hV q r hq hr hnd)).2 η hηatomic hηtan

/-- Build the representation-level path scalar structure from tangent
sign-preservation and the finite same-sign scalar theorem. -/
noncomputable def branchPathScalarStructure_of_tangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (htsign : FiniteBranchTangentSignPreservationAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F) :
    BranchPathScalarStructure F hV hlin where
  branchPathCoeff :=
    branchPathScalarCoeffOfTangentSign hlin hsignscalar htsign F hV
  branchPathCoeff_pos := by
    intro A _ _ _ q r hq hr hnd
    exact branchPathScalarCoeffOfTangentSign_pos
      hlin hsignscalar htsign F hV q r hq hr hnd
  linear_part_scalar_relation := by
    intro A _ _ _ q r hq hr hnd η
    exact branchPathScalarCoeffOfTangentSign_relation
      hlin hsignscalar htsign F hV q r hq hr hnd η

/-- A1-aware same-sign scalar extraction for a fixed value representative.

This is the faithful replacement for `branch_linear_scalar_exists_of_tangentSign`:
the sign-agreement part is representation-level, and the nonzero branch
functional comes from pure-trace nontriviality through
`branch_linear_part_nonzero_of_A1`. -/
theorem branch_linear_scalar_exists_of_A1_tangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignPreservationFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ β : ℝ, 0 < β ∧
      ∀ η : PosteriorLawSigned A,
        hlin.linearPart F hV q η = β * hlin.linearPart F hV r η := by
  exact hsignscalar.same_sign_scalar
    (hlin.linearPart F hV q)
    (hlin.linearPart F hV r)
    (hlin.linearPart_add F hV q)
    (hlin.linearPart_smul F hV q)
    (hlin.linearPart_add F hV r)
    (hlin.linearPart_smul F hV r)
    (hsign.tangent_sign_preservation q r hq hr hr_nondegenerate)
    (branch_linear_part_nonzero_of_A1 hlin F hax hV q r hq hr hr_nondegenerate)

/-- A1-aware scalar coefficient for a fixed representative. -/
noncomputable def branchPathScalarCoeffOfA1TangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignPreservationFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ := by
  classical
  exact
    if hq : q.FullSupport then
      if hr : r.FullSupport then
        if hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b then
          Classical.choose
            (branch_linear_scalar_exists_of_A1_tangentSign
              hlin hsignscalar F hax hV hsign q r hq hr hnd)
        else 1
      else 1
    else 1

theorem branchPathScalarCoeffOfA1TangentSign_eq_choose
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignPreservationFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    branchPathScalarCoeffOfA1TangentSign hlin hsignscalar F hax hV hsign q r =
      Classical.choose
        (branch_linear_scalar_exists_of_A1_tangentSign
          hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate) := by
  classical
  unfold branchPathScalarCoeffOfA1TangentSign
  simp [hq, hr, hr_nondegenerate]

theorem branchPathScalarCoeffOfA1TangentSign_pos
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignPreservationFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    0 < branchPathScalarCoeffOfA1TangentSign
      hlin hsignscalar F hax hV hsign q r := by
  rw [branchPathScalarCoeffOfA1TangentSign_eq_choose
    hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate]
  exact (Classical.choose_spec
    (branch_linear_scalar_exists_of_A1_tangentSign
      hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate)).1

theorem branchPathScalarCoeffOfA1TangentSign_relation
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hsign : BranchTangentSignPreservationFor F hax hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (η : PosteriorLawSigned A) :
    hlin.linearPart F hV q η =
      branchPathScalarCoeffOfA1TangentSign
        hlin hsignscalar F hax hV hsign q r *
        hlin.linearPart F hV r η := by
  rw [branchPathScalarCoeffOfA1TangentSign_eq_choose
    hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate]
  exact (Classical.choose_spec
    (branch_linear_scalar_exists_of_A1_tangentSign
      hlin hsignscalar F hax hV hsign q r hq hr hr_nondegenerate)).2 η

/-- Build the representation-level scalar structure from tangent sign agreement,
the nonzero pure-trace branch-linear witness and the finite same-sign scalar theorem. -/
noncomputable def branchPathScalarStructure_of_A1_tangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (hsign : FiniteBranchTangentSignAgreementAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchPathScalarStructure F hV hlin where
  branchPathCoeff := fun q r =>
    branchPathScalarCoeffOfA1TangentSign hlin hsignscalar F hax hV
      (branchTangentSignPreservationFor_of_signAgreement hlin hsign F hax hV) q r
  branchPathCoeff_pos := by
    intro A _ _ _ q r hq hr hnd
    exact branchPathScalarCoeffOfA1TangentSign_pos
      hlin hsignscalar F hax hV
      (branchTangentSignPreservationFor_of_signAgreement hlin hsign F hax hV)
      q r hq hr hnd
  linear_part_scalar_relation := by
    intro A _ _ _ q r hq hr hnd η
    exact branchPathScalarCoeffOfA1TangentSign_relation
      hlin hsignscalar F hax hV
      (branchTangentSignPreservationFor_of_signAgreement hlin hsign F hax hV)
      q r hq hr hnd η

/-- Full-support slope identity from a representation-level scalar.

This is the remaining analytic bridge from the scalar relation
`L_q = β(q,r)L_r` to the branch-slice affine slope `α = mβ(q,r)` for a branch
whose reached posterior has full support. -/
structure FiniteBranchFullSupportSlopeIdentityAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  branch_slice_slope_eq_probability_mul_scalar :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      (hscalar : BranchPathScalarStructure F hV hlin)
      {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (hpos : BranchPositive P₁ q target)
      (_hr : (branchPosterior P₁ q target).FullSupport)
      (O₂ : O₁ → Type v)
      [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
      (background : ∀ o, Channel A (O₂ o))
      (slope intercept : ℝ),
      (∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept) →
      slope =
        (Channel.outcomeMarginal P₁ q) target *
          hscalar.branchPathCoeff q (branchPosterior P₁ q target)

/-- If a fixed branch-continuation outcome alphabet contains two continuations
with distinct reached-posterior values, then the affine branch-slice slope is
identified by the full-support scalar relation.

This is the compiled nondegenerate algebra behind the paper's
`alpha = m beta(q,r)` step.  The broader legacy
`FiniteBranchFullSupportSlopeIdentityAssumptions` quantifies over all fixed
continuation outcome alphabets; for value-constant alphabets the slope in an
affine formula is not identifiable. -/
theorem branch_slice_slope_eq_probability_mul_scalar_of_value_gap
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    (hscalar : BranchPathScalarStructure F hV hlin)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (_hpos : BranchPositive P₁ q target)
    (hr : (branchPosterior P₁ q target).FullSupport)
    (hr_nondegenerate :
      ∃ a b : A, a ≠ b ∧
        0 < (branchPosterior P₁ q target) a ∧
        0 < (branchPosterior P₁ q target) b)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (background : ∀ o, Channel A (O₂ o))
    (slope intercept : ℝ)
    (hslice :
      ∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept)
    (Q R : ∀ o, Channel A (O₂ o))
    (hQ : ∀ o, o ≠ target → Q o = background o)
    (hR : ∀ o, o ≠ target → R o = background o)
    (hgap :
      hV.V (branchPosterior P₁ q target) (experimentOfChannel (Q target)) ≠
        hV.V (branchPosterior P₁ q target) (experimentOfChannel (R target))) :
    slope =
      (Channel.outcomeMarginal P₁ q) target *
        hscalar.branchPathCoeff q (branchPosterior P₁ q target) := by
  classical
  let r : Dist A := branchPosterior P₁ q target
  let m : ℝ := (Channel.outcomeMarginal P₁ q) target
  let β : ℝ := hscalar.branchPathCoeff q r
  let EQ : FiniteExperimentOn A :=
    experimentOfChannel (seqComposeDep P₁ O₂ Q)
  let ER : FiniteExperimentOn A :=
    experimentOfChannel (seqComposeDep P₁ O₂ R)
  let BQ : FiniteExperimentOn A := experimentOfChannel (Q target)
  let BR : FiniteExperimentOn A := experimentOfChannel (R target)
  let branchDiff : PosteriorLawSigned A := posteriorLawDifferenceExp r BQ BR
  let seqDiff : PosteriorLawSigned A := posteriorLawDifferenceExp q EQ ER
  have hsameQR : ∀ o, o ≠ target → Q o = R o := by
    intro o ho
    rw [hQ o ho, hR o ho]
  have hsliceQ := hslice Q hQ
  have hsliceR := hslice R hR
  have hslice_diff :
      hV.V q EQ - hV.V q ER =
        slope * (hV.V r BQ - hV.V r BR) := by
    change hV.V q EQ = slope * hV.V r BQ + intercept at hsliceQ
    change hV.V q ER = slope * hV.V r BR + intercept at hsliceR
    nlinarith
  have hseq_ext :
      ∀ φ : Dist A → ℝ,
        seqDiff φ = posteriorLawSignedSMul m branchDiff φ := by
    intro φ
    have h :=
      posteriorLawDifference_seqComposeDep_one_branch
        q P₁ O₂ Q R target hsameQR φ
    simpa [seqDiff, branchDiff, EQ, ER, BQ, BR, r, m,
      posteriorLawSignedSMul] using h
  have hseq_linear :
      hlin.linearPart F hV q seqDiff =
        m * hlin.linearPart F hV q branchDiff := by
    rw [hlin.linearPart_ext F hV q seqDiff
      (posteriorLawSignedSMul m branchDiff) hseq_ext]
    rw [hlin.linearPart_smul]
  have hscalar_rel :
      hlin.linearPart F hV q branchDiff =
        β * hlin.linearPart F hV r branchDiff := by
    simpa [r, β, branchDiff] using
      hscalar.linear_part_scalar_relation q r hq hr hr_nondegenerate branchDiff
  have hseq_value :
      hV.V q EQ - hV.V q ER =
        m * β * (hV.V r BQ - hV.V r BR) := by
    calc
      hV.V q EQ - hV.V q ER =
          hlin.linearPart F hV q seqDiff := by
            simpa [seqDiff, EQ, ER] using hlin.value_difference F hV q EQ ER
      _ = m * hlin.linearPart F hV q branchDiff := hseq_linear
      _ = m * (β * hlin.linearPart F hV r branchDiff) := by
            rw [hscalar_rel]
      _ = m * β * (hV.V r BQ - hV.V r BR) := by
            have hbranch :=
              hlin.value_difference F hV r BQ BR
            rw [← hbranch]
            ring
  have hdiff_ne : hV.V r BQ - hV.V r BR ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa [r, BQ, BR] using hgap)
  have hmul :
      slope * (hV.V r BQ - hV.V r BR) =
        m * β * (hV.V r BQ - hV.V r BR) := by
    nlinarith [hslice_diff, hseq_value]
  have hfactor :
      (slope - m * β) * (hV.V r BQ - hV.V r BR) = 0 := by
    nlinarith
  have hslope : slope - m * β = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hdiff_ne
  simpa [m, β, r] using sub_eq_zero.mp hslope

/-- Faithful nondegenerate/value-gap version of the full-support slope
identity.  It records exactly the part that value comparisons identify: once
the target branch slice contains two continuations with different branch value,
the affine slope must be `m * beta(q,r)`. -/
structure FiniteBranchFullSupportSlopeIdentityWithValueGapAssumptions
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  branch_slice_slope_eq_probability_mul_scalar_of_value_gap :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      (hscalar : BranchPathScalarStructure F hV hlin)
      {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (_hpos : BranchPositive P₁ q target)
      (_hr : (branchPosterior P₁ q target).FullSupport)
      (_hr_nondegenerate :
        ∃ a b : A, a ≠ b ∧
          0 < (branchPosterior P₁ q target) a ∧
          0 < (branchPosterior P₁ q target) b)
      (O₂ : O₁ → Type v)
      [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
      (background : ∀ o, Channel A (O₂ o))
      (slope intercept : ℝ),
      (∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept) →
      ∀ (Q R : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background o) →
        (∀ o, o ≠ target → R o = background o) →
        hV.V (branchPosterior P₁ q target)
            (experimentOfChannel (Q target)) ≠
          hV.V (branchPosterior P₁ q target)
            (experimentOfChannel (R target)) →
      slope =
        (Channel.outcomeMarginal P₁ q) target *
          hscalar.branchPathCoeff q (branchPosterior P₁ q target)

/-- The value-gap slope identity package is internal algebra from the affine
linear-part interface and the scalar relation. -/
theorem branchFullSupportSlopeIdentityWithValueGap_of_linearPart
    (hlin : FiniteAffineLinearPartAssumptions.{u}) :
    FiniteBranchFullSupportSlopeIdentityWithValueGapAssumptions.{u} hlin where
  branch_slice_slope_eq_probability_mul_scalar_of_value_gap := by
    intro F hV hscalar A _ _ _ O₁ _ _ q hq P₁ target hpos hr hnd
      O₂ _ _ background slope intercept hslice Q R hQ hR hgap
    exact branch_slice_slope_eq_probability_mul_scalar_of_value_gap
      hlin F hV hscalar q hq P₁ target hpos hr hnd O₂ background
      slope intercept hslice Q R hQ hR hgap

/-- Tangent-scalar version of the value-gap slope identity.  This is the
faithful counterpart of
`branch_slice_slope_eq_probability_mul_scalar_of_value_gap`, using only the
scalar relation on genuine tangent signed posterior-law directions. -/
theorem branch_slice_slope_eq_probability_mul_tangent_scalar_of_value_gap
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    (hscalar : BranchPathTangentScalarStructure F hV hlin)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (_hpos : BranchPositive P₁ q target)
    (hr : (branchPosterior P₁ q target).FullSupport)
    (hr_nondegenerate :
      ∃ a b : A, a ≠ b ∧
        0 < (branchPosterior P₁ q target) a ∧
        0 < (branchPosterior P₁ q target) b)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (background : ∀ o, Channel A (O₂ o))
    (slope intercept : ℝ)
    (hslice :
      ∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept)
    (Q R : ∀ o, Channel A (O₂ o))
    (hQ : ∀ o, o ≠ target → Q o = background o)
    (hR : ∀ o, o ≠ target → R o = background o)
    (hgap :
      hV.V (branchPosterior P₁ q target) (experimentOfChannel (Q target)) ≠
        hV.V (branchPosterior P₁ q target) (experimentOfChannel (R target))) :
    slope =
      (Channel.outcomeMarginal P₁ q) target *
        hscalar.branchPathCoeff q (branchPosterior P₁ q target) := by
  classical
  let r : Dist A := branchPosterior P₁ q target
  let m : ℝ := (Channel.outcomeMarginal P₁ q) target
  let β : ℝ := hscalar.branchPathCoeff q r
  let EQ : FiniteExperimentOn A :=
    experimentOfChannel (seqComposeDep P₁ O₂ Q)
  let ER : FiniteExperimentOn A :=
    experimentOfChannel (seqComposeDep P₁ O₂ R)
  let BQ : FiniteExperimentOn A := experimentOfChannel (Q target)
  let BR : FiniteExperimentOn A := experimentOfChannel (R target)
  let branchDiff : PosteriorLawSigned A := posteriorLawDifferenceExp r BQ BR
  let seqDiff : PosteriorLawSigned A := posteriorLawDifferenceExp q EQ ER
  have hsameQR : ∀ o, o ≠ target → Q o = R o := by
    intro o ho
    rw [hQ o ho, hR o ho]
  have hsliceQ := hslice Q hQ
  have hsliceR := hslice R hR
  have hslice_diff :
      hV.V q EQ - hV.V q ER =
        slope * (hV.V r BQ - hV.V r BR) := by
    change hV.V q EQ = slope * hV.V r BQ + intercept at hsliceQ
    change hV.V q ER = slope * hV.V r BR + intercept at hsliceR
    nlinarith
  have hseq_ext :
      ∀ φ : Dist A → ℝ,
        seqDiff φ = posteriorLawSignedSMul m branchDiff φ := by
    intro φ
    have h :=
      posteriorLawDifference_seqComposeDep_one_branch
        q P₁ O₂ Q R target hsameQR φ
    simpa [seqDiff, branchDiff, EQ, ER, BQ, BR, r, m,
      posteriorLawSignedSMul] using h
  have hseq_linear :
      hlin.linearPart F hV q seqDiff =
        m * hlin.linearPart F hV q branchDiff := by
    rw [hlin.linearPart_ext F hV q seqDiff
      (posteriorLawSignedSMul m branchDiff) hseq_ext]
    rw [hlin.linearPart_smul]
  have hbranch_tangent : PosteriorLawTangent branchDiff := by
    exact posteriorLawDifferenceExp_tangent r BQ BR
  have hbranch_atomic : PosteriorLawSigned.AtomicLinear branchDiff :=
    posteriorLawDifferenceExp_atomicLinear r BQ BR
  have hscalar_rel :
      hlin.linearPart F hV q branchDiff =
        β * hlin.linearPart F hV r branchDiff := by
    simpa [r, β, branchDiff] using
      hscalar.linear_part_scalar_relation_on_tangent
        q r hq hr hr_nondegenerate branchDiff hbranch_atomic hbranch_tangent
  have hseq_value :
      hV.V q EQ - hV.V q ER =
        m * β * (hV.V r BQ - hV.V r BR) := by
    calc
      hV.V q EQ - hV.V q ER =
          hlin.linearPart F hV q seqDiff := by
            simpa [seqDiff, EQ, ER] using hlin.value_difference F hV q EQ ER
      _ = m * hlin.linearPart F hV q branchDiff := hseq_linear
      _ = m * (β * hlin.linearPart F hV r branchDiff) := by
            rw [hscalar_rel]
      _ = m * β * (hV.V r BQ - hV.V r BR) := by
            have hbranch :=
              hlin.value_difference F hV r BQ BR
            rw [← hbranch]
            ring
  have hdiff_ne : hV.V r BQ - hV.V r BR ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa [r, BQ, BR] using hgap)
  have hmul :
      slope * (hV.V r BQ - hV.V r BR) =
        m * β * (hV.V r BQ - hV.V r BR) := by
    nlinarith [hslice_diff, hseq_value]
  have hfactor :
      (slope - m * β) * (hV.V r BQ - hV.V r BR) = 0 := by
    nlinarith
  have hslope : slope - m * β = 0 :=
    (mul_eq_zero.mp hfactor).resolve_right hdiff_ne
  simpa [m, β, r] using sub_eq_zero.mp hslope

/-- Representation-level full-support branch path-independence package. -/
structure BranchFullSupportPathIndependenceStructure
    (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F) where
  branchPathCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  branchPathCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      0 < branchPathCoeff q r
  branch_slice_slope_eq_probability_mul_coeff :
    ∀ (hax : PureTraceConditions F)
      {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (hpos : BranchPositive P₁ q target)
      (_hr : (branchPosterior P₁ q target).FullSupport)
      (O₂ : O₁ → Type v)
      [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
      (background : ∀ o, Channel A (O₂ o))
      (slope intercept : ℝ),
      (∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept) →
      slope =
        (Channel.outcomeMarginal P₁ q) target *
          branchPathCoeff q (branchPosterior P₁ q target)

/-- Reassemble the full-support, representation-level path-independence
package from the scalar relation plus the slope identity. -/
noncomputable def branchFullSupportPathIndependence_of_scalar
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hslope : FiniteBranchFullSupportSlopeIdentityAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hscalar : BranchPathScalarStructure F hV hlin) :
    BranchFullSupportPathIndependenceStructure F hV where
  branchPathCoeff := hscalar.branchPathCoeff
  branchPathCoeff_pos := hscalar.branchPathCoeff_pos
  branch_slice_slope_eq_probability_mul_coeff := by
    intro hax' A O₁ _ _ _ _ _ q hq P₁ target hpos hr O₂ _ _ background
      slope intercept hslice
    exact hslope.branch_slice_slope_eq_probability_mul_scalar
      F hax' hV hscalar q hq P₁ target hpos hr O₂ background slope intercept hslice

/-- A1-aware full-support path-independence package.

This is the faithful representation-level path from tangent sign agreement and
Pure-trace nontriviality to full-support path independence.  It bypasses the old
hax-free `FiniteBranchTangentSignPreservationAssumptions`. -/
noncomputable def branchFullSupportPathIndependence_of_A1_scalar
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (hsign : FiniteBranchTangentSignAgreementAssumptions.{u} hlin)
    (hslope : FiniteBranchFullSupportSlopeIdentityAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchFullSupportPathIndependenceStructure F hV :=
  branchFullSupportPathIndependence_of_scalar hlin hslope F hax hV
    (branchPathScalarStructure_of_A1_tangentSign
      hlin hsignscalar hsign F hax hV)

/-- Path-independent branch slope coefficient interface.

This isolates the paper claim that the one-branch affine slope divided by the
branch probability depends only on the prior and reached posterior, not on the
first-stage experiment or fixed continuations. -/
structure FiniteBranchPathIndependenceAssumptions where
  branchPathCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  branchPathCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      0 < branchPathCoeff q r
  branch_slice_slope_eq_probability_mul_coeff :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (hpos : BranchPositive P₁ q target)
      (O₂ : O₁ → Type v)
      [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
      (background : ∀ o, Channel A (O₂ o))
      (slope intercept : ℝ),
      (∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept) →
      slope =
        (Channel.outcomeMarginal P₁ q) target *
          branchPathCoeff q (branchPosterior P₁ q target)

end TraceableAgency
