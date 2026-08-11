/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.PositiveAffine

namespace TraceableAgency

universe u v

/-!
## Background-independence algebra

The paper proves that if two choices of fixed non-target continuations produce
affine branch slices with slopes `α₁` and `α₂`, then the slopes agree because
the slice difference is constant and the branch representative is nonconstant.
The following theorem is that algebraic cancellation step, independent of the
posterior-law/tangent-space formalization.
-/

/-- If two affine functions of a nonconstant base function differ by a constant,
then their slopes are equal. -/
theorem slopes_eq_of_affine_difference_constant
    {ι : Type u} (f g₁ g₂ : ι → ℝ)
    (a₁ c₁ a₂ c₂ d : ℝ)
    (hg₁ : ∀ x, g₁ x = a₁ * f x + c₁)
    (hg₂ : ∀ x, g₂ x = a₂ * f x + c₂)
    (hdiff : ∀ x, g₁ x - g₂ x = d)
    (hnonconst : ∃ x y, f x ≠ f y) :
    a₁ = a₂ := by
  rcases hnonconst with ⟨x, y, hxy⟩
  have hx := hdiff x
  have hy := hdiff y
  rw [hg₁ x, hg₂ x] at hx
  rw [hg₁ y, hg₂ y] at hy
  have hmul : (a₁ - a₂) * (f x - f y) = 0 := by
    nlinarith
  have hf : f x - f y ≠ 0 := sub_ne_zero.mpr hxy
  have ha : a₁ - a₂ = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_right hf
  linarith

/-- Narrow interface for the branch-slope background-independence step.

The pure slope-cancellation algebra is `slopes_eq_of_affine_difference_constant`.
This interface isolates the remaining branch-specific fact: changing only fixed
non-target continuations changes the aggregate branch slice by a constant,
using the affine linear part of the prior value representative. -/
structure FiniteBranchSlopeBackgroundIndependenceAssumptions : Prop where
  slope_background_independent :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (_hpos : BranchPositive P₁ q target)
      (O₂ : O₁ → Type v)
      [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
      (background₁ background₂ : ∀ o, Channel A (O₂ o))
      (slope₁ intercept₁ slope₂ intercept₂ : ℝ),
      (∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background₁ o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope₁ *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept₁) →
      (∀ (Q : ∀ o, Channel A (O₂ o)),
        (∀ o, o ≠ target → Q o = background₂ o) →
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
            slope₂ *
              hV.V (branchPosterior P₁ q target)
                (experimentOfChannel (Q target)) +
            intercept₂) →
      slope₁ = slope₂

end TraceableAgency
