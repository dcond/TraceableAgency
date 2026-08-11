/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.SignedLaws

namespace TraceableAgency

universe u v

/-!
## Affine linear-part interface

This is a narrow replacement component for the first analytic step of
`Branch aggregation`: an affine posterior-value representative has a linear
part on extensional signed posterior-law differences.  It does not include A6,
branch comparison, tangent-space path-independence, boundary support handling,
or the final aggregation formula.
-/

/-- Finite posterior-law integral representation package.

The `marginalValue` and `value_eq_integral` fields express the usual finite
integral form of an affine posterior-law functional.  No coherence between
different priors or finite alphabets is included: such equalities are
gauge-dependent and must be obtained only after a representative has been
canonically normalised. -/
structure FinitePosteriorIntegralRepresentationAssumptions where
  marginalValue :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  value_eq_integral :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E : FiniteExperimentOn A),
      hV.V q E =
        posteriorLawIntegralExp q E (marginalValue F hV q)

/-- Finite affine linear-part interface for posterior-law values.

**Paper role**: if `F_q` is affine on the posterior-law set `M_q`, then
Herstein-Milnor gives an integral representation `F_q(μ) = ∫ φ_q(r) dμ(r)`
for a marginal value function `φ_q : Dist A → ℝ`.  The linear part is then
`L_q(η) := η(φ_q)`, where `η : PosteriorLawSigned A = (Dist A → ℝ) → ℝ` acts
on the test function `φ_q`.  This satisfies `F_q(μ_E) - F_q(μ_{E'}) = L_q(μ_E - μ_{E'})`.

**Construction status**: the final route does not assume this structure.
`finiteAffineLinearPartAssumptions_of_integralRepresentation` constructs it in
Lean by evaluating signed laws on the internally constructed test function.

Paper citation: Lemma postsep / integral form; the affinity of
`F_q` is the Herstein-Milnor output and the integral form is immediate from it. -/
structure FiniteAffineLinearPartAssumptions where
  linearPart :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → PosteriorLawSigned A → ℝ
  value_difference :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E E' : FiniteExperimentOn A),
      hV.V q E - hV.V q E' =
        linearPart F hV q (posteriorLawDifferenceExp q E E')
  linearPart_ext :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (η ζ : PosteriorLawSigned A),
      (∀ φ : Dist A → ℝ, η φ = ζ φ) →
        linearPart F hV q η = linearPart F hV q ζ
  linearPart_add :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (η ζ : PosteriorLawSigned A),
      linearPart F hV q (posteriorLawSignedAdd η ζ) =
        linearPart F hV q η + linearPart F hV q ζ
  linearPart_smul :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (c : ℝ) (η : PosteriorLawSigned A),
      linearPart F hV q (posteriorLawSignedSMul c η) =
        c * linearPart F hV q η

/-- The finite posterior-law integral representation gives the affine linear
part by evaluating signed posterior laws on the representing test function. -/
noncomputable def finiteAffineLinearPartAssumptions_of_integralRepresentation
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u}) :
    FiniteAffineLinearPartAssumptions.{u} where
  linearPart := fun F hV {A} [Fintype A] [DecidableEq A] [Nonempty A] q η =>
    η (hint.marginalValue F hV q)
  value_difference := by
    intro F hV A _ _ _ q E E'
    rw [hint.value_eq_integral F hV q E,
      hint.value_eq_integral F hV q E']
    rfl
  linearPart_ext := by
    intro F hV A _ _ _ q η ζ hηζ
    exact hηζ (hint.marginalValue F hV q)
  linearPart_add := by
    intro F hV A _ _ _ q η ζ
    rfl
  linearPart_smul := by
    intro F hV A _ _ _ q c η
    rfl

/-- The linear part sends the zero signed posterior law to zero. -/
theorem linearPart_zero
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    hlin.linearPart F hV q ((fun _ => 0) : PosteriorLawSigned A) = 0 := by
  have h :=
    hlin.linearPart_smul F hV q 0
      (((fun _ => 0) : PosteriorLawSigned A))
  have hext :
      hlin.linearPart F hV q ((fun _ => 0) : PosteriorLawSigned A) =
        hlin.linearPart F hV q
          (posteriorLawSignedSMul 0 ((fun _ => 0) : PosteriorLawSigned A)) :=
    hlin.linearPart_ext F hV q _ _ (by
      intro φ
      simp [posteriorLawSignedSMul])
  rw [hext]
  simpa [posteriorLawSignedSMul] using h

/-- The linear part distributes over a finite sum of signed posterior laws. -/
theorem linearPart_finsetSum
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A ι : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [DecidableEq ι]
    (q : Dist A) (s : Finset ι) (η : ι → PosteriorLawSigned A) :
    hlin.linearPart F hV q (posteriorLawSignedFinsetSum s η) =
      s.sum (fun i => hlin.linearPart F hV q (η i)) := by
  classical
  refine Finset.induction_on s ?empty ?insert
  · simp [linearPart_zero hlin F hV q]
  · intro i s hi ih
    rw [posteriorLawSignedFinsetSum_insert i s η hi]
    rw [hlin.linearPart_add F hV q]
    rw [ih]
    rw [Finset.sum_insert hi]

/-- The linear part distributes over a finite indexed sum of signed posterior
laws. -/
theorem linearPart_sum
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A ι : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype ι] [DecidableEq ι]
    (q : Dist A) (η : ι → PosteriorLawSigned A) :
    hlin.linearPart F hV q (posteriorLawSignedSum η) =
      ∑ i, hlin.linearPart F hV q (η i) := by
  simpa [posteriorLawSignedSum] using
    linearPart_finsetSum hlin F hV q Finset.univ η

end TraceableAgency
