/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.BackgroundIndependence

namespace TraceableAgency

universe u v

/-!
## Tangent-space and path-independence interfaces

The paper's path-independence argument uses two finite-dimensional linear
algebra facts:

1. posterior-law tangent directions are spanned by feasible differences;
2. two nonzero linear functionals with the same sign partition are positive
   scalar multiples.

The following structures state those facts in the extensional signed-law
language introduced above.
-/

/-- Legacy finite tangent-space spanning interface.

An extensional signed posterior law with zero total mass and zero barycentre is
represented, up to a positive scalar, by a feasible difference of two posterior
laws at the same full-support prior.

This interface is too broad for the current definition
`PosteriorLawSigned A = (Dist A → ℝ) → ℝ`: the two moment equations do not
imply linearity in the test function, while feasible posterior-law differences
are linear.  Faithful developments should use
`FiniteAtomicPosteriorTangentSpanningAssumptions` or an explicit
`PosteriorLawSigned.AtomicLinear` witness instead. -/
structure FinitePosteriorTangentSpaceSpanningAssumptions : Prop where
  zero_mass_barycenter_as_feasible_difference :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (r : Dist A) (_hr : r.FullSupport) (η : PosteriorLawSigned A),
      η (fun _ => 1) = 0 →
      (∀ a : A, η (fun p => p a) = 0) →
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
      ∃ (t : ℝ) (_ht : 0 < t) (E E' : FiniteExperimentOn A),
        ∀ φ : Dist A → ℝ,
          η φ = t * posteriorLawDifferenceExp r E E' φ

/-- Corrected atomic tangent-space spanning interface.

The quantified object is a finite atomic-linear signed posterior law, not an
arbitrary extensional functional.  This matches the mathematical tangent space:
the finite signed span of posterior laws with zero mass and zero barycentre. -/
structure FiniteAtomicPosteriorTangentSpanningAssumptions : Prop where
  atomic_zero_mass_barycenter_as_feasible_difference :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (r : Dist A) (_hr : r.FullSupport)
      (ν : AtomicPosteriorSignedLaw A),
      ν.totalMass = 0 →
      (∀ a : A, ν.barycenterCoord a = 0) →
      ν.eval ≠ ((fun _ => 0) : PosteriorLawSigned A) →
      ∃ (t : ℝ) (_ht : 0 < t) (E E' : FiniteExperimentOn A),
        ∀ φ : Dist A → ℝ,
          ν.eval φ = t * posteriorLawDifferenceExp r E E' φ

/-- Extensional form of the corrected atomic tangent-spanning interface.

This keeps the existing `PosteriorLawSigned` target type but requires explicit
finite atomic-linear data witnessing the extensional law. -/
structure FiniteAtomicLinearPosteriorTangentSpanningAssumptions : Prop where
  atomicLinear_zero_mass_barycenter_as_feasible_difference :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (r : Dist A) (_hr : r.FullSupport) (η : PosteriorLawSigned A)
      (hη : PosteriorLawSigned.AtomicLinear η),
      hη.witness.totalMass = 0 →
      (∀ a : A, hη.witness.barycenterCoord a = 0) →
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
      ∃ (t : ℝ) (_ht : 0 < t) (E E' : FiniteExperimentOn A),
        ∀ φ : Dist A → ℝ,
          η φ = t * posteriorLawDifferenceExp r E E' φ

/-- Atomic tangent spanning implies its extensional atomic-linear witness form. -/
theorem atomicLinearTangentSpanning_of_atomic
    (hatomic : FiniteAtomicPosteriorTangentSpanningAssumptions.{u}) :
    FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u} where
  atomicLinear_zero_mass_barycenter_as_feasible_difference := by
    intro A _ _ _ r hr η hη hmass hbary hηne
    have hνne :
        hη.witness.eval ≠ ((fun _ => 0) : PosteriorLawSigned A) := by
      intro hzero
      exact hηne (by
        rw [← hη.eval_eq]
        exact hzero)
    rcases hatomic.atomic_zero_mass_barycenter_as_feasible_difference
        r hr hη.witness hmass hbary hνne with
      ⟨t, ht, E, E', hreal⟩
    refine ⟨t, ht, E, E', ?_⟩
    intro φ
    rw [← hη.eval_eq]
    exact hreal φ

end TraceableAgency
