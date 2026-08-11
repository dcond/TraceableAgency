/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.BoundaryFaces

namespace TraceableAgency

universe u v

/-!
## Aggregation coefficient assembly

The branch coefficient used in the uniform downstream formula is assembled from
the three paper cases: full support, nondegenerate boundary support, and
singleton/degenerate normalization.
-/

/-- Branch coefficient assembled from the full-support path coefficient,
boundary full-to-face coefficient, and singleton/degenerate normalization. -/
noncomputable def branchCoeffFromParts
    (hpath : FiniteBranchPathIndependenceAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ := by
  classical
  exact
  if hfull : r.FullSupport then
    hpath.branchPathCoeff q r
  else if hnond : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b then
    hboundary.boundaryCoeff q r
  else
    hsingle.singletonCoeff q r

/-- The assembled branch coefficient is positive in the nondegenerate cases
required by `BranchAggregationStructure.branchCoeff_pos`. -/
theorem branchCoeffFromParts_pos
    (hpath : FiniteBranchPathIndependenceAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hr : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    0 < branchCoeffFromParts hpath hboundary hsingle q r := by
  classical
  unfold branchCoeffFromParts
  by_cases hfull : r.FullSupport
  · simp [hfull]
    exact hpath.branchPathCoeff_pos q r hq hr
  · have hnonempty : ∃ a : A, 0 < r a := by
      rcases hr with ⟨a, _b, _hne, ha, _hb⟩
      exact ⟨a, ha⟩
    simp [hfull, hr]
    exact hboundary.boundaryCoeff_pos q r hq hnonempty hr hfull

/-- Formula-level branch aggregation bridge for the assembled coefficient.

This is narrower than the old `FiniteBranchAggregationAssumptions`: it does
not construct affine linear parts, branch-slice slopes, path-independent
coefficients, boundary coefficients, or singleton normalizations.  It states only
the final uniform-outcome formula once those components have been supplied. -/
structure FiniteBranchAggregationFormulaAssumptions
    (hpath : FiniteBranchPathIndependenceAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{v}) where
  branch_aggregation_formula :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A O₁ O₂ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂),
      hV.V q (experimentOfChannel (P₁ ▷ Q)) =
      hV.V q (experimentOfChannel P₁) +
      ∑ o₁ : O₁,
        (Channel.outcomeMarginal P₁ q) o₁ *
        branchCoeffFromParts hpath hboundary hsingle
          q (Channel.posterior P₁ q o₁) *
        hV.V (Channel.posterior P₁ q o₁) (experimentOfChannel (Q o₁))

/-- Reassemble a `BranchAggregationStructure` from the decomposed branch
coefficient pieces and the remaining formula-level bridge. -/
noncomputable def branchAggregationStructure_of_formula
    (hpath : FiniteBranchPathIndependenceAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hformula :
      FiniteBranchAggregationFormulaAssumptions.{u} hpath hboundary hsingle)
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F) :
    BranchAggregationStructure F where
  value_rep := hV
  branchCoeff := fun q r => branchCoeffFromParts hpath hboundary hsingle q r
  branchCoeff_pos := by
    intro A _ _ _ q r hq hr
    exact branchCoeffFromParts_pos hpath hboundary hsingle q r hq hr
  branch_aggregation := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ Q
    exact hformula.branch_aggregation_formula F hV q hq P₁ Q

/-- Representation-level branch coefficient assembled from a representation-level
full-support path package, boundary face coefficients, and singleton
normalizations. -/
noncomputable def branchCoeffFromRepParts
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpath : BranchFullSupportPathIndependenceStructure F hV)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ := by
  classical
  exact
  if hfull : r.FullSupport then
    hpath.branchPathCoeff q r
  else if hnond : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b then
    hboundary.boundaryCoeff q r
  else
    hsingle.singletonCoeff q r

/-- Positivity for the representation-level assembled branch coefficient. -/
theorem branchCoeffFromRepParts_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpath : BranchFullSupportPathIndependenceStructure F hV)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hr : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    0 < branchCoeffFromRepParts hpath hboundary hsingle q r := by
  classical
  unfold branchCoeffFromRepParts
  by_cases hfull : r.FullSupport
  · simp [hfull]
    exact hpath.branchPathCoeff_pos q r hq hfull hr
  · have hnonempty : ∃ a : A, 0 < r a := by
      rcases hr with ⟨a, _b, _hne, ha, _hb⟩
      exact ⟨a, ha⟩
    simp [hfull, hr]
    exact hboundary.boundaryCoeff_pos q r hq hnonempty hr hfull

/-- Formula-level branch aggregation bridge for a fixed value representative and
representation-level full-support path package. -/
structure FiniteBranchAggregationFormulaFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hpath : BranchFullSupportPathIndependenceStructure F hV)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV) where
  branch_aggregation_formula :
    ∀ {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂),
      hV.V q (experimentOfChannel (P₁ ▷ Q)) =
      hV.V q (experimentOfChannel P₁) +
      ∑ o₁ : O₁,
        (Channel.outcomeMarginal P₁ q) o₁ *
        branchCoeffFromRepParts hpath hboundary hsingle
          q (Channel.posterior P₁ q o₁) *
        hV.V (Channel.posterior P₁ q o₁) (experimentOfChannel (Q o₁))

/-- Reassemble `BranchAggregationStructure` from representation-level full-support
path data and a representation-level formula bridge. -/
noncomputable def branchAggregationStructure_of_formulaFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hpath : BranchFullSupportPathIndependenceStructure F hV)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hformula :
      FiniteBranchAggregationFormulaFor F hax hV hpath hboundary hsingle) :
    BranchAggregationStructure F where
  value_rep := hV
  branchCoeff := fun q r => branchCoeffFromRepParts hpath hboundary hsingle q r
  branchCoeff_pos := by
    intro A _ _ _ q r hq hr
    exact branchCoeffFromRepParts_pos hpath hboundary hsingle q r hq hr
  branch_aggregation := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ Q
    exact hformula.branch_aggregation_formula q hq P₁ Q

/-- Representation-level branch coefficient assembled from the faithful
tangent-scalar full-support path package, boundary face coefficients, and
singleton normalizations.

This is the branch-coefficient assembly that bypasses the legacy hax-free
`FiniteBranchPathIndependenceAssumptions`. -/
noncomputable def branchCoeffFromTangentRepParts
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    {hlin : FiniteAffineLinearPartAssumptions.{u}}
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ := by
  classical
  exact
  if hfull : r.FullSupport then
    hpath.branchPathCoeff q r
  else if hnond : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b then
    hboundary.boundaryCoeff q r
  else
    hsingle.singletonCoeff q r

/-- Positivity for the faithful tangent-scalar assembled branch coefficient. -/
theorem branchCoeffFromTangentRepParts_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    {hlin : FiniteAffineLinearPartAssumptions.{u}}
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hr : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    0 < branchCoeffFromTangentRepParts hpath hboundary hsingle q r := by
  classical
  unfold branchCoeffFromTangentRepParts
  by_cases hfull : r.FullSupport
  · simp [hfull]
    exact hpath.branchPathCoeff_pos q r hq hfull hr
  · have hnonempty : ∃ a : A, 0 < r a := by
      rcases hr with ⟨a, _b, _hne, ha, _hb⟩
      exact ⟨a, ha⟩
    simp [hfull, hr]
    exact hboundary.boundaryCoeff_pos q r hq hnonempty hr hfull

/-- Full-support branch summand identity for the formula bridge.  The branch
contribution from the no-information baseline is exactly
`m(o) * beta(q,r_o) * V_{r_o}(Q^o)`. -/
theorem branch_formula_fullSupport_summand_linearPart_eq
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (hr : (branchPosterior P₁ q target).FullSupport)
    (hr_nondegenerate :
      ∃ a b : A, a ≠ b ∧
        0 < (branchPosterior P₁ q target) a ∧
        0 < (branchPosterior P₁ q target) b)
    (Q : Channel A O₂) :
    hlin.linearPart F hV q
      (posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
        (posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel Q)
          (experimentOfChannel (Channel.uninformativeChannelU A)))) =
      (Channel.outcomeMarginal P₁ q) target *
        hpath.branchPathCoeff q (branchPosterior P₁ q target) *
        hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
  classical
  let r : Dist A := branchPosterior P₁ q target
  let m : ℝ := (Channel.outcomeMarginal P₁ q) target
  let diff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r
      (experimentOfChannel Q)
      (experimentOfChannel (Channel.uninformativeChannelU A))
  have htan : PosteriorLawTangent diff := by
    exact posteriorLawDifferenceExp_tangent r
      (experimentOfChannel Q)
      (experimentOfChannel (Channel.uninformativeChannelU A))
  have hatomic : PosteriorLawSigned.AtomicLinear diff :=
    posteriorLawDifferenceExp_atomicLinear r
      (experimentOfChannel Q)
      (experimentOfChannel (Channel.uninformativeChannelU A))
  have hscalar :
      hlin.linearPart F hV q diff =
        hpath.branchPathCoeff q r * hlin.linearPart F hV r diff := by
    exact hpath.linear_part_scalar_relation_on_tangent
      q r hq hr hr_nondegenerate diff hatomic htan
  have hbranch :
      hlin.linearPart F hV r diff =
        hV.V r (experimentOfChannel Q) -
          hV.V r (experimentOfChannel (Channel.uninformativeChannelU A)) := by
    simpa [diff] using
      (hlin.value_difference F hV r
        (experimentOfChannel Q)
        (experimentOfChannel (Channel.uninformativeChannelU A))).symm
  calc
    hlin.linearPart F hV q (posteriorLawSignedSMul m diff)
        = m * hlin.linearPart F hV q diff := by
          rw [hlin.linearPart_smul]
    _ = m * (hpath.branchPathCoeff q r * hlin.linearPart F hV r diff) := by
          rw [hscalar]
    _ = m * hpath.branchPathCoeff q r *
          hV.V r (experimentOfChannel Q) := by
          rw [hbranch, hV.zero_normalized r hr]
          ring

/-- Singleton branch terms are zero, independently of the coefficient
normalization. -/
theorem branch_formula_singleton_summand_zero
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {hlin : FiniteAffineLinearPartAssumptions.{u}}
    {hpath : BranchPathTangentScalarStructure F hV hlin}
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q r : Dist A) (m : ℝ)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
    (Q : Channel A O) :
    m * branchCoeffFromTangentRepParts hpath hboundary hsingle q r *
        hV.V r (experimentOfChannel Q) = 0 := by
  rw [hsingle.singleton_branch_value_zero r hr_singleton_support Q]
  ring

/-- A distribution whose positive support is not nondegenerate has singleton
positive support. -/
theorem singleton_support_of_not_nondegenerate
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hnot :
      ¬ ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a := by
  classical
  rcases supportSubtype_nonempty r with ⟨a, ha⟩
  refine ⟨a, ha, ?_⟩
  intro b hb
  by_contra hne
  exact hnot ⟨b, a, hne, hb, ha⟩

/-- If a prior has singleton positive support, then the positive support subtype
is subsingleton. -/
theorem supportSubtype_subsingleton_of_singleton_support
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a) :
    Subsingleton (supportSubtype r) := by
  rcases hr_singleton_support with ⟨a, _ha, huniq⟩
  refine ⟨?_⟩
  intro x y
  apply Subtype.ext
  exact (huniq x.1 x.2).trans (huniq y.1 y.2).symm

/-- Singleton positive support rules out a nondegenerate positive support. -/
theorem not_nondegenerate_of_singleton_support
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a) :
    ¬ ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
  rcases hr_singleton_support with ⟨c, _hc, huniq⟩
  rintro ⟨a, b, hne, ha, hb⟩
  exact hne ((huniq a ha).trans (huniq b hb).symm)

/-- A singleton-support prior gives the same posterior law for every
experiment: the point mass at the prior. -/
theorem posteriorLawIntegral_singleton_support
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
    (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegral r P φ = φ r := by
  classical
  haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  haveI : Subsingleton (supportSubtype r) :=
    supportSubtype_subsingleton_of_singleton_support r hr_singleton_support
  have hrestrict :=
    posteriorLawIntegral_restrictToSupport (P := P) (q := r) (φ := φ)
  rw [hrestrict]
  change
    posteriorLawIntegralExp r.restrictToSupport
      (experimentOfChannel (Channel.restrictToSupport P r))
      (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) =
      φ r
  rw [posteriorLawIntegralExp_singleton_branch]
  rw [actionPushforward_restrict_include r]

/-- Singleton-support posterior-law differences from a continuation to
no-information are zero. -/
theorem posteriorLawDifferenceExp_singleton_support_eq_zero
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
    (Q : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp r
      (experimentOfChannel Q)
      (experimentOfChannel (Channel.uninformativeChannelU A)) φ = 0 := by
  unfold posteriorLawDifferenceExp
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegral_singleton_support r hr_singleton_support Q φ]
  rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior]
  ring

/-- Singleton-support branch linear-part contributions are zero. -/
theorem branch_formula_singleton_summand_linearPart_zero
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q r : Dist A) (m : ℝ)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
    (Q : Channel A O) :
    hlin.linearPart F hV q
      (posteriorLawSignedSMul m
        (posteriorLawDifferenceExp r
          (experimentOfChannel Q)
          (experimentOfChannel (Channel.uninformativeChannelU A)))) = 0 := by
  classical
  let diff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r
      (experimentOfChannel Q)
      (experimentOfChannel (Channel.uninformativeChannelU A))
  have hdiff_zero :
      ∀ φ : Dist A → ℝ, diff φ = ((fun _ => 0) : PosteriorLawSigned A) φ := by
    intro φ
    exact posteriorLawDifferenceExp_singleton_support_eq_zero
      r hr_singleton_support Q φ
  have hlinear_zero :
      hlin.linearPart F hV q diff = 0 := by
    calc
      hlin.linearPart F hV q diff =
          hlin.linearPart F hV q
            (((fun _ => 0) : PosteriorLawSigned A)) :=
            hlin.linearPart_ext F hV q diff _ hdiff_zero
      _ = 0 := linearPart_zero hlin F hV q
  calc
    hlin.linearPart F hV q (posteriorLawSignedSMul m diff)
        = m * hlin.linearPart F hV q diff := by
          rw [hlin.linearPart_smul]
    _ = 0 := by rw [hlinear_zero, mul_zero]

/-- Full singleton-support branch summand identity: both the linear-part
contribution and the displayed coefficient/value term are zero. -/
theorem branch_formula_singleton_summand_linearPart_eq
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {hpath : BranchPathTangentScalarStructure F hV hlin}
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q r : Dist A) (m : ℝ)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
    (Q : Channel A O) :
    hlin.linearPart F hV q
      (posteriorLawSignedSMul m
        (posteriorLawDifferenceExp r
          (experimentOfChannel Q)
          (experimentOfChannel (Channel.uninformativeChannelU A)))) =
      m * branchCoeffFromTangentRepParts hpath hboundary hsingle q r *
        hV.V r (experimentOfChannel Q) := by
  rw [branch_formula_singleton_summand_linearPart_zero
    hlin F hV q r m hr_singleton_support Q]
  rw [branch_formula_singleton_summand_zero
    F hV hboundary hsingle q r m hr_singleton_support Q]

/-- Zero-probability branches contribute zero to the branch formula. -/
theorem branch_formula_zero_probability_summand_zero
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {hpath : BranchPathTangentScalarStructure F hV hlin}
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (target : O₁)
    (hm0 : (Channel.outcomeMarginal P₁ q) target = 0)
    (Q : Channel A O₂) :
    (Channel.outcomeMarginal P₁ q) target *
      hlin.linearPart F hV q
        (posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel Q)
          (experimentOfChannel (Channel.uninformativeChannelU A))) =
      (Channel.outcomeMarginal P₁ q) target *
        branchCoeffFromTangentRepParts hpath hboundary hsingle
          q (branchPosterior P₁ q target) *
        hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
  rw [hm0]
  ring

/-- Branchwise summand package for the public formula.  This is narrower than
`FiniteBranchAggregationFormulaTangentFor`: it gives only the equality of each
linear-part branch contribution with the displayed coefficient/value summand. -/
structure FiniteBranchFormulaSummandAssumptions
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV) : Prop where
  summand_linearPart_eq :
    ∀ {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁) (Q : Channel A O₂),
      (Channel.outcomeMarginal P₁ q) target *
        hlin.linearPart F hV q
          (posteriorLawDifferenceExp (branchPosterior P₁ q target)
            (experimentOfChannel Q)
            (experimentOfChannel (Channel.uninformativeChannelU A))) =
        (Channel.outcomeMarginal P₁ q) target *
          branchCoeffFromTangentRepParts hpath hboundary hsingle
            q (branchPosterior P₁ q target) *
          hV.V (branchPosterior P₁ q target) (experimentOfChannel Q)

/-- Boundary summand assumptions, together with the internal full-support,
singleton-support, and zero-probability summand theorems, give the branchwise
summand package. -/
theorem branchFormulaSummands_of_boundary
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hboundarySummand :
      FiniteBranchFormulaBoundarySummandAssumptions hlin hboundary) :
    FiniteBranchFormulaSummandAssumptions F hax hV hlin hpath hboundary hsingle where
  summand_linearPart_eq := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ target Q
    classical
    let r : Dist A := branchPosterior P₁ q target
    let m : ℝ := (Channel.outcomeMarginal P₁ q) target
    by_cases hmpos : 0 < m
    · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b
      · by_cases hfull : r.FullSupport
        · have hfull_summand :=
            branch_formula_fullSupport_summand_linearPart_eq
              hlin F hV hpath q hq P₁ target (by simpa [r] using hfull)
              (by simpa [r] using hnd) Q
          have hfull_summand' :
              m *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) =
              m * hpath.branchPathCoeff q r *
                hV.V r (experimentOfChannel Q) := by
            have hsmul :
                hlin.linearPart F hV q
                  (posteriorLawSignedSMul m
                    (posteriorLawDifferenceExp r
                      (experimentOfChannel Q)
                      (experimentOfChannel (Channel.uninformativeChannelU A)))) =
                m * hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) := by
              rw [hlin.linearPart_smul]
            rw [hsmul] at hfull_summand
            simpa [m, r] using hfull_summand
          calc
            (Channel.outcomeMarginal P₁ q) target *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp (branchPosterior P₁ q target)
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A)))
                =
              m * hpath.branchPathCoeff q r *
                hV.V r (experimentOfChannel Q) := by
                simpa [m, r] using hfull_summand'
            _ =
              (Channel.outcomeMarginal P₁ q) target *
                branchCoeffFromTangentRepParts hpath hboundary hsingle
                  q (branchPosterior P₁ q target) *
                hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
                simp [m, r, branchCoeffFromTangentRepParts, hfull]
        · have hr_nonempty : ∃ a : A, 0 < r a := by
            rcases hnd with ⟨a, _b, _hne, ha, _hb⟩
            exact ⟨a, ha⟩
          have hboundary_summand :=
            hboundarySummand.boundary_summand_linearPart_eq
              F hV q hq P₁ target
              (by simpa [r] using hr_nonempty)
              (by simpa [r] using hnd)
              (by simpa [r] using hfull) Q
          have hboundary_summand' :
              m *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) =
              m * hboundary.boundaryCoeff q r *
                hV.V r (experimentOfChannel Q) := by
            have hsmul :
                hlin.linearPart F hV q
                  (posteriorLawSignedSMul m
                    (posteriorLawDifferenceExp r
                      (experimentOfChannel Q)
                      (experimentOfChannel (Channel.uninformativeChannelU A)))) =
                m * hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) := by
              rw [hlin.linearPart_smul]
            rw [hsmul] at hboundary_summand
            simpa [m, r] using hboundary_summand
          calc
            (Channel.outcomeMarginal P₁ q) target *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp (branchPosterior P₁ q target)
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A)))
                =
              m * hboundary.boundaryCoeff q r *
                hV.V r (experimentOfChannel Q) := by
                simpa [m, r] using hboundary_summand'
            _ =
              (Channel.outcomeMarginal P₁ q) target *
                branchCoeffFromTangentRepParts hpath hboundary hsingle
                  q (branchPosterior P₁ q target) *
                hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
                simp [m, r, branchCoeffFromTangentRepParts, hfull, hnd]
      · have hsingle_support :
            ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a :=
          singleton_support_of_not_nondegenerate r hnd
        have hsingle_summand :=
          branch_formula_singleton_summand_linearPart_eq
            (hlin := hlin) (F := F) (hV := hV) (hpath := hpath)
            hboundary hsingle q r m hsingle_support Q
        calc
          (Channel.outcomeMarginal P₁ q) target *
              hlin.linearPart F hV q
                (posteriorLawDifferenceExp (branchPosterior P₁ q target)
                  (experimentOfChannel Q)
                  (experimentOfChannel (Channel.uninformativeChannelU A)))
              =
            hlin.linearPart F hV q
              (posteriorLawSignedSMul m
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A)))) := by
              rw [hlin.linearPart_smul]
          _ =
            m * branchCoeffFromTangentRepParts hpath hboundary hsingle q r *
              hV.V r (experimentOfChannel Q) := hsingle_summand
          _ =
            (Channel.outcomeMarginal P₁ q) target *
              branchCoeffFromTangentRepParts hpath hboundary hsingle
                q (branchPosterior P₁ q target) *
              hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
              simp [m, r]
    · have hm0 : m = 0 :=
        le_antisymm (le_of_not_gt hmpos)
          ((Channel.outcomeMarginal P₁ q).nonneg target)
      exact branch_formula_zero_probability_summand_zero
        hlin F hV hboundary hsingle q P₁ target (by simpa [m] using hm0) Q

/-- Hax-aware boundary summand assumptions, together with the internal
full-support, singleton-support, and zero-probability summand theorems, give
the branchwise summand package. -/
theorem branchFormulaSummands_of_boundaryFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hboundarySummand :
      FiniteBranchFormulaBoundarySummandFor F hax hV hlin hboundary) :
    FiniteBranchFormulaSummandAssumptions F hax hV hlin hpath hboundary hsingle where
  summand_linearPart_eq := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ target Q
    classical
    let r : Dist A := branchPosterior P₁ q target
    let m : ℝ := (Channel.outcomeMarginal P₁ q) target
    by_cases hmpos : 0 < m
    · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b
      · by_cases hfull : r.FullSupport
        · have hfull_summand :=
            branch_formula_fullSupport_summand_linearPart_eq
              hlin F hV hpath q hq P₁ target (by simpa [r] using hfull)
              (by simpa [r] using hnd) Q
          have hfull_summand' :
              m *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) =
              m * hpath.branchPathCoeff q r *
                hV.V r (experimentOfChannel Q) := by
            have hsmul :
                hlin.linearPart F hV q
                  (posteriorLawSignedSMul m
                    (posteriorLawDifferenceExp r
                      (experimentOfChannel Q)
                      (experimentOfChannel (Channel.uninformativeChannelU A)))) =
                m * hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) := by
              rw [hlin.linearPart_smul]
            rw [hsmul] at hfull_summand
            simpa [m, r] using hfull_summand
          calc
            (Channel.outcomeMarginal P₁ q) target *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp (branchPosterior P₁ q target)
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A)))
                =
              m * hpath.branchPathCoeff q r *
                hV.V r (experimentOfChannel Q) := by
                simpa [m, r] using hfull_summand'
            _ =
              (Channel.outcomeMarginal P₁ q) target *
                branchCoeffFromTangentRepParts hpath hboundary hsingle
                  q (branchPosterior P₁ q target) *
                hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
                simp [m, r, branchCoeffFromTangentRepParts, hfull]
        · have hr_nonempty : ∃ a : A, 0 < r a := by
            rcases hnd with ⟨a, _b, _hne, ha, _hb⟩
            exact ⟨a, ha⟩
          have hboundary_summand :=
            hboundarySummand.boundary_summand_linearPart_eq
              q hq P₁ target
              (by simpa [r] using hr_nonempty)
              (by simpa [r] using hnd)
              (by simpa [r] using hfull) Q
          have hboundary_summand' :
              m *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) =
              m * hboundary.boundaryCoeff q r *
                hV.V r (experimentOfChannel Q) := by
            have hsmul :
                hlin.linearPart F hV q
                  (posteriorLawSignedSMul m
                    (posteriorLawDifferenceExp r
                      (experimentOfChannel Q)
                      (experimentOfChannel (Channel.uninformativeChannelU A)))) =
                m * hlin.linearPart F hV q
                  (posteriorLawDifferenceExp r
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A))) := by
              rw [hlin.linearPart_smul]
            rw [hsmul] at hboundary_summand
            simpa [m, r] using hboundary_summand
          calc
            (Channel.outcomeMarginal P₁ q) target *
                hlin.linearPart F hV q
                  (posteriorLawDifferenceExp (branchPosterior P₁ q target)
                    (experimentOfChannel Q)
                    (experimentOfChannel (Channel.uninformativeChannelU A)))
                =
              m * hboundary.boundaryCoeff q r *
                hV.V r (experimentOfChannel Q) := by
                simpa [m, r] using hboundary_summand'
            _ =
              (Channel.outcomeMarginal P₁ q) target *
                branchCoeffFromTangentRepParts hpath hboundary hsingle
                  q (branchPosterior P₁ q target) *
                hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
                simp [m, r, branchCoeffFromTangentRepParts, hfull, hnd]
      · have hsingle_support :
            ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a :=
          singleton_support_of_not_nondegenerate r hnd
        have hsingle_summand :=
          branch_formula_singleton_summand_linearPart_eq
            (hlin := hlin) (F := F) (hV := hV) (hpath := hpath)
            hboundary hsingle q r m hsingle_support Q
        calc
          (Channel.outcomeMarginal P₁ q) target *
              hlin.linearPart F hV q
                (posteriorLawDifferenceExp (branchPosterior P₁ q target)
                  (experimentOfChannel Q)
                  (experimentOfChannel (Channel.uninformativeChannelU A)))
              =
            hlin.linearPart F hV q
              (posteriorLawSignedSMul m
                (posteriorLawDifferenceExp r
                  (experimentOfChannel Q)
                  (experimentOfChannel (Channel.uninformativeChannelU A)))) := by
              rw [hlin.linearPart_smul]
          _ =
            m * branchCoeffFromTangentRepParts hpath hboundary hsingle q r *
              hV.V r (experimentOfChannel Q) := hsingle_summand
          _ =
            (Channel.outcomeMarginal P₁ q) target *
              branchCoeffFromTangentRepParts hpath hboundary hsingle
                q (branchPosterior P₁ q target) *
              hV.V (branchPosterior P₁ q target) (experimentOfChannel Q) := by
              simp [m, r]
    · have hm0 : m = 0 :=
        le_antisymm (le_of_not_gt hmpos)
          ((Channel.outcomeMarginal P₁ q).nonneg target)
      exact branch_formula_zero_probability_summand_zero
        hlin F hV hboundary hsingle q P₁ target (by simpa [m] using hm0) Q

/-- Formula-level branch aggregation bridge for a fixed representative and the
faithful tangent-scalar full-support path package.

This bridge is intentionally narrower than `FiniteBranchAggregationAssumptions`:
it assumes only the final sequential formula after the tangent scalar,
boundary, and singleton coefficient pieces have been supplied. -/
structure FiniteBranchAggregationFormulaTangentFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV) where
  branch_aggregation_formula :
    ∀ {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂),
      hV.V q (experimentOfChannel (P₁ ▷ Q)) =
      hV.V q (experimentOfChannel P₁) +
      ∑ o₁ : O₁,
        (Channel.outcomeMarginal P₁ q) o₁ *
        branchCoeffFromTangentRepParts hpath hboundary hsingle
          q (Channel.posterior P₁ q o₁) *
        hV.V (Channel.posterior P₁ q o₁) (experimentOfChannel (Q o₁))

/-- The branch formula follows from the fixed-output affine expansion and a
branchwise summand package. -/
theorem branchAggregationFormulaTangentFor_of_summands
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hsummand :
      FiniteBranchFormulaSummandAssumptions F hax hV hlin hpath hboundary hsingle) :
    FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle where
  branch_aggregation_formula := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ Q
    have haff :=
      branch_formula_affine_expansion_seqCompose hlin F hV q P₁ Q
    have hsum :=
      branch_formula_linearPart_seqCompose_sum hlin F hV q P₁ Q
    have hsummand_sum :
        (∑ o : O₁,
          (Channel.outcomeMarginal P₁ q) o *
            hlin.linearPart F hV q
              (posteriorLawDifferenceExp (branchPosterior P₁ q o)
                (experimentOfChannel (Q o))
                (experimentOfChannel (Channel.uninformativeChannelU A)))) =
        ∑ o : O₁,
          (Channel.outcomeMarginal P₁ q) o *
            branchCoeffFromTangentRepParts hpath hboundary hsingle
              q (Channel.posterior P₁ q o) *
            hV.V (Channel.posterior P₁ q o) (experimentOfChannel (Q o)) := by
      apply Finset.sum_congr rfl
      intro o _ho
      exact hsummand.summand_linearPart_eq q hq P₁ o (Q o)
    calc
      hV.V q (experimentOfChannel (P₁ ▷ Q))
          =
        hV.V q (experimentOfChannel P₁) +
          (hV.V q (experimentOfChannel (P₁ ▷ Q)) -
            hV.V q (experimentOfChannel P₁)) := by
            ring
      _ =
        hV.V q (experimentOfChannel P₁) +
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp q
              (experimentOfChannel (P₁ ▷ Q))
              (experimentOfChannel P₁)) := by
            rw [haff]
      _ =
        hV.V q (experimentOfChannel P₁) +
          ∑ o : O₁,
            (Channel.outcomeMarginal P₁ q) o *
              hlin.linearPart F hV q
                (posteriorLawDifferenceExp (branchPosterior P₁ q o)
                  (experimentOfChannel (Q o))
                  (experimentOfChannel (Channel.uninformativeChannelU A))) := by
            rw [hsum]
      _ =
        hV.V q (experimentOfChannel P₁) +
          ∑ o : O₁,
            (Channel.outcomeMarginal P₁ q) o *
            branchCoeffFromTangentRepParts hpath hboundary hsingle
              q (Channel.posterior P₁ q o) *
            hV.V (Channel.posterior P₁ q o) (experimentOfChannel (Q o)) := by
            rw [hsummand_sum]

/-- Formula bridge reassembly from the boundary summand package. -/
theorem branchAggregationFormulaTangentFor_of_boundarySummands
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hboundarySummand :
      FiniteBranchFormulaBoundarySummandAssumptions hlin hboundary) :
    FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle :=
  branchAggregationFormulaTangentFor_of_summands
    F hax hV hlin hpath hboundary hsingle
    (branchFormulaSummands_of_boundary
      F hax hV hlin hpath hboundary hsingle hboundarySummand)

/-- Formula bridge reassembly from the hax-aware boundary summand package. -/
theorem branchAggregationFormulaTangentFor_of_boundarySummandsFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hboundarySummand :
      FiniteBranchFormulaBoundarySummandFor F hax hV hlin hboundary) :
    FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle :=
  branchAggregationFormulaTangentFor_of_summands
    F hax hV hlin hpath hboundary hsingle
    (branchFormulaSummands_of_boundaryFor
      F hax hV hlin hpath hboundary hsingle hboundarySummand)

/-- Formula bridge reassembly from selected boundary value transport and
coefficient transport. -/
theorem branchAggregationFormulaTangentFor_of_boundaryTransportFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary) :
    FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle :=
  branchAggregationFormulaTangentFor_of_boundarySummandsFor
    F hax hV hlin hpath hboundary hsingle
    (branchFormulaBoundarySummandFor_of_value_for_and_coefficient_transport
      F hax hV hlin hboundary hvalue hcoeff)

/-- Formula bridge reassembly from selected boundary value transport and the
atomic support-face marginal-value theorem.

This is the convention-free selected route: the only support-face tangents used
by the branch formula are posterior-law differences induced by finite
continuation experiments, and those are atomic-linear. -/
theorem branchAggregationFormulaTangentFor_of_boundaryTransportAtomicFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hpath :
      BranchPathTangentScalarStructure F hV
        (finiteAffineLinearPartAssumptions_of_integralRepresentation hint))
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAtomicFor
        F hax hV hint hboundary) :
    FiniteBranchAggregationFormulaTangentFor F hax hV
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint)
      hpath hboundary hsingle :=
  branchAggregationFormulaTangentFor_of_boundarySummandsFor
    F hax hV
    (finiteAffineLinearPartAssumptions_of_integralRepresentation hint)
    hpath hboundary hsingle
    (branchFormulaBoundarySummandFor_of_value_for_and_marginal_transport_atomic
      F hax hV hint hboundary hvalue hmarginal)

/-- Formula bridge reassembly from boundary value and coefficient transport. -/
theorem branchAggregationFormulaTangentFor_of_boundaryTransport
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hvalue : FiniteBranchBoundaryValueTransportAssumptions.{u})
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary) :
    FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle :=
  branchAggregationFormulaTangentFor_of_boundaryTransportFor
    F hax hV hlin hpath hboundary hsingle
    (boundaryValueTransportFor_of_boundaryValueTransport hvalue F hax hV)
    hcoeff

/-- Reassemble `BranchAggregationStructure` from the faithful tangent-scalar
path data and a formula bridge. -/
noncomputable def branchAggregationStructure_of_tangentFormulaFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hformula :
      FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle) :
    BranchAggregationStructure F where
  value_rep := hV
  branchCoeff := fun q r => branchCoeffFromTangentRepParts hpath hboundary hsingle q r
  branchCoeff_pos := by
    intro A _ _ _ q r hq hr
    exact branchCoeffFromTangentRepParts_pos hpath hboundary hsingle q r hq hr
  branch_aggregation := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ Q
    exact hformula.branch_aggregation_formula q hq P₁ Q

/-- The public branch coefficient of the faithful tangent-formula
`BranchAggregationStructure` is the assembled tangent/boundary/singleton
coefficient. -/
theorem branchAggregationStructure_of_tangentFormulaFor_branchCoeff_eq
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hformula :
      FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) :
    (branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula).branchCoeff q r =
      branchCoeffFromTangentRepParts hpath hboundary hsingle q r := rfl

/-- On full-support reached posteriors, the public coefficient of the faithful
tangent-formula `BranchAggregationStructure` is exactly the tangent scalar. -/
theorem branchAggregationStructure_of_tangentFormulaFor_branchCoeff_fullSupport_eq
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hformula :
      FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hr : r.FullSupport) :
    (branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula).branchCoeff q r =
      hpath.branchPathCoeff q r := by
  classical
  simp [branchAggregationStructure_of_tangentFormulaFor_branchCoeff_eq,
    branchCoeffFromTangentRepParts, hr]

end TraceableAgency
