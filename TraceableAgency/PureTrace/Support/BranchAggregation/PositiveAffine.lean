/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.SignPreservation

namespace TraceableAgency

universe u v

/-!
## Branch-slice positive affine uniqueness

Once the one-coordinate slice order has been established, the paper applies
finite affine-utility uniqueness to conclude that the aggregate branch slice is
a positive affine transform of the reached-posterior representative.  The
general product-slice uniqueness interfaces currently live downstream in
`TraceableAgency/PureTrace/Support/EntropyReduction.lean`; this branch-specific interface keeps the
branch proof decomposed without introducing an import cycle.
-/

/-- Positive affine form for one branch slice with fixed continuations in all
other branches.

This packages only the affine-uniqueness conclusion for a single branch slice:
for a fixed first-stage experiment, target positive branch, and fixed
background continuations, varying the target continuation changes the aggregate
value by a positive affine transform of the target branch value. -/
structure FiniteBranchSlicePositiveAffineAssumptions where
  branch_slice_positive_affine :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (target : O₁)
      (_hpos : BranchPositive P₁ q target)
      (O₂ : O₁ → Type v)
      [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
      (background : ∀ o, Channel A (O₂ o)),
      ∃ slope intercept : ℝ, 0 < slope ∧
        ∀ (Q : ∀ o, Channel A (O₂ o)),
          (∀ o, o ≠ target → Q o = background o) →
            hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
              slope *
                hV.V (branchPosterior P₁ q target)
                  (experimentOfChannel (Q target)) +
              intercept

end TraceableAgency
