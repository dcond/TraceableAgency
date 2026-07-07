/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Sufficiency.Spine
import TraceableAgency.External.Blackwell
import TraceableAgency.External.Relabeling

/-!
# External Branch Aggregation Assumptions

This file contains external assumptions for the branch aggregation theorem,
which derives cardinal branch coefficients from the behavioural Axiom A7
(branchwise continuation monotonicity) and the posterior value representation.

## Main definitions

* `FiniteBranchAggregationAssumptions` - a structure bundling the branch aggregation
  theorem as an external assumption.

## Status

These assumptions are:
1. Based on the paper's Lemma branchagg (lines 1830-2068)
2. NOT proved in this Lean development
3. Used as explicit, auditable external assumptions
4. No anonymous `axiom` declarations are used

The branch aggregation theorem derives:
1. Positive branch coefficients β(q, r) depending on prior and posterior
2. The aggregation formula: V_q(E₁▷{Q}) = V_q(E₁) + Σ m(o) β(q,r_o) V_{r_o}(Q^o)

## References

* empowerment_v5.tex, Lemma branchagg (lines 1830-1929)
* The proof uses A7 + Herstein-Milnor uniqueness to derive the coefficients
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
## Signed posterior-law differences

The paper's branch-aggregation proof uses the affine hull of posterior laws and
writes differences as elements of a tangent/signed-measure space.  The current
Lean development represents posterior laws extensionally by integration
against test functions.  The following lightweight type is the corresponding
finite signed posterior-law functional.
-/

/-- An extensional finite signed posterior law on `Dist A`, represented by its
action on test functions. -/
abbrev PosteriorLawSigned (A : Type u)
    [Fintype A] [DecidableEq A] [Nonempty A] :=
  (Dist A → ℝ) → ℝ

/-- A signed posterior law is tangent when it has zero total mass and zero
barycentre.  This predicate by itself does not assert linearity in the test
function; use `PosteriorLawSigned.AtomicLinear` or
`AtomicPosteriorSignedLaw` for the faithful atomic-linear tangent space. -/
def PosteriorLawTangent {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (η : PosteriorLawSigned A) : Prop :=
  η (fun _ => 1) = 0 ∧ ∀ a : A, η (fun p => p a) = 0

/-- Signed posterior law induced by a finite experiment. -/
noncomputable def posteriorLawSignedOfExperiment {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) : PosteriorLawSigned A :=
  fun φ => posteriorLawIntegralExp q E φ

/-- Difference of the posterior laws induced by two finite experiments. -/
noncomputable def posteriorLawDifferenceExp {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) : PosteriorLawSigned A :=
  fun φ => posteriorLawIntegralExp q E φ - posteriorLawIntegralExp q E' φ

/-- Addition of signed posterior laws, in extensional test-function form. -/
noncomputable def posteriorLawSignedAdd {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (η ζ : PosteriorLawSigned A) : PosteriorLawSigned A :=
  fun φ => η φ + ζ φ

/-- Scalar multiplication of signed posterior laws, in extensional
test-function form. -/
noncomputable def posteriorLawSignedSMul {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (c : ℝ) (η : PosteriorLawSigned A) : PosteriorLawSigned A :=
  fun φ => c * η φ

/-- Finite sum of signed posterior laws over a specified finite set. -/
noncomputable def posteriorLawSignedFinsetSum {ι A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (s : Finset ι) (η : ι → PosteriorLawSigned A) : PosteriorLawSigned A :=
  fun φ => s.sum (fun i => η i φ)

/-- Finite sum of signed posterior laws over all indices. -/
noncomputable def posteriorLawSignedSum {ι A : Type u}
    [Fintype ι] [Fintype A] [DecidableEq A] [Nonempty A]
    (η : ι → PosteriorLawSigned A) : PosteriorLawSigned A :=
  posteriorLawSignedFinsetSum Finset.univ η

/-- Concrete finite atomic signed posterior law.

This is the faithful finite signed-measure representation missing from the
purely extensional type `PosteriorLawSigned A`.  Evaluation is linear in test
functions by construction. -/
structure AtomicPosteriorSignedLaw (A : Type u)
    [Fintype A] [DecidableEq A] [Nonempty A] where
  I : Type u
  instFintypeI : Fintype I
  instDecidableEqI : DecidableEq I
  weight : I → ℝ
  point : I → Dist A

namespace AtomicPosteriorSignedLaw

/-- Evaluation of an atomic signed posterior law on a test function. -/
noncomputable def eval {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) : PosteriorLawSigned A := by
  letI : Fintype ν.I := ν.instFintypeI
  exact fun φ => ∑ i : ν.I, ν.weight i * φ (ν.point i)

/-- Total signed mass of an atomic signed posterior law. -/
noncomputable def totalMass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) : ℝ := by
  letI : Fintype ν.I := ν.instFintypeI
  exact ∑ i : ν.I, ν.weight i

/-- Barycentre coordinate of an atomic signed posterior law. -/
noncomputable def barycenterCoord {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (a : A) : ℝ := by
  letI : Fintype ν.I := ν.instFintypeI
  exact ∑ i : ν.I, ν.weight i * ν.point i a

/-- Total variation mass of the displayed atomic representation.  This is
representation-level data; duplicate atoms may still cancel extensionally. -/
noncomputable def variationMass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) : ℝ := by
  letI : Fintype ν.I := ν.instFintypeI
  exact ∑ i : ν.I, |ν.weight i|

/-- Positive part of the displayed atomic weight. -/
noncomputable def positiveWeight {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (i : ν.I) : ℝ :=
  max (ν.weight i) 0

/-- Negative part of the displayed atomic weight. -/
noncomputable def negativeWeight {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (i : ν.I) : ℝ :=
  max (-(ν.weight i)) 0

/-- Total positive displayed mass. -/
noncomputable def positiveMass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) : ℝ := by
  letI : Fintype ν.I := ν.instFintypeI
  exact ∑ i : ν.I, ν.positiveWeight i

/-- Total negative displayed mass. -/
noncomputable def negativeMass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) : ℝ := by
  letI : Fintype ν.I := ν.instFintypeI
  exact ∑ i : ν.I, ν.negativeWeight i

@[simp] theorem eval_apply {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (φ : Dist A → ℝ) :
    ν.eval φ = by
      letI : Fintype ν.I := ν.instFintypeI
      exact ∑ i : ν.I, ν.weight i * φ (ν.point i) := by
  rfl

theorem eval_const_one {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) :
    ν.eval (fun _ => (1 : ℝ)) = ν.totalMass := by
  simp [eval, totalMass]

theorem eval_coord {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (a : A) :
    ν.eval (fun p => p a) = ν.barycenterCoord a := by
  simp [eval, barycenterCoord]

theorem eval_add_test {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (φ ψ : Dist A → ℝ) :
    ν.eval (fun p => φ p + ψ p) = ν.eval φ + ν.eval ψ := by
  simp [eval, mul_add, Finset.sum_add_distrib]

theorem eval_smul_test {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (c : ℝ) (φ : Dist A → ℝ) :
    ν.eval (fun p => c * φ p) = c * ν.eval φ := by
  letI : Fintype ν.I := ν.instFintypeI
  simp [eval, Finset.mul_sum, mul_left_comm]

theorem eval_tangent {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hbary : ∀ a : A, ν.barycenterCoord a = 0) :
    PosteriorLawTangent ν.eval := by
  constructor
  · rw [eval_const_one, hmass]
  · intro a
    rw [eval_coord, hbary a]

theorem positiveWeight_nonneg {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (i : ν.I) :
    0 ≤ ν.positiveWeight i := by
  exact le_max_right (ν.weight i) 0

theorem negativeWeight_nonneg {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (i : ν.I) :
    0 ≤ ν.negativeWeight i := by
  exact le_max_right (-(ν.weight i)) 0

theorem weight_eq_positiveWeight_sub_negativeWeight {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (i : ν.I) :
    ν.weight i = ν.positiveWeight i - ν.negativeWeight i := by
  unfold positiveWeight negativeWeight
  by_cases h : 0 ≤ ν.weight i
  · have hneg_nonpos : -(ν.weight i) ≤ 0 := by linarith
    simp [max_eq_left h, max_eq_right hneg_nonpos]
  · have hwle : ν.weight i ≤ 0 := le_of_not_ge h
    have hneg : 0 ≤ -(ν.weight i) := by linarith
    simp [max_eq_right hwle, max_eq_left hneg]

theorem totalMass_eq_positiveMass_sub_negativeMass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) :
    ν.totalMass = ν.positiveMass - ν.negativeMass := by
  letI : Fintype ν.I := ν.instFintypeI
  calc
    ν.totalMass = ∑ i : ν.I, (ν.positiveWeight i - ν.negativeWeight i) := by
      simp [totalMass, weight_eq_positiveWeight_sub_negativeWeight]
    _ = ν.positiveMass - ν.negativeMass := by
      simp [positiveMass, negativeMass, Finset.sum_sub_distrib]

theorem positiveMass_nonneg {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) :
    0 ≤ ν.positiveMass := by
  letI : Fintype ν.I := ν.instFintypeI
  exact Finset.sum_nonneg (fun i _ => positiveWeight_nonneg ν i)

theorem negativeMass_nonneg {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) :
    0 ≤ ν.negativeMass := by
  letI : Fintype ν.I := ν.instFintypeI
  exact Finset.sum_nonneg (fun i _ => negativeWeight_nonneg ν i)

theorem positiveMass_eq_negativeMass_of_totalMass_zero {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0) :
    ν.positiveMass = ν.negativeMass := by
  have h := ν.totalMass_eq_positiveMass_sub_negativeMass
  linarith

theorem positive_barycenter_eq_negative_barycenter_of_barycenter_zero {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A) (a : A)
    (hbary : ν.barycenterCoord a = 0) :
    (by letI : Fintype ν.I := ν.instFintypeI
        exact ∑ i : ν.I, ν.positiveWeight i * ν.point i a) =
    (by letI : Fintype ν.I := ν.instFintypeI
        exact ∑ i : ν.I, ν.negativeWeight i * ν.point i a) := by
  letI : Fintype ν.I := ν.instFintypeI
  show ∑ i : ν.I, ν.positiveWeight i * ν.point i a =
       ∑ i : ν.I, ν.negativeWeight i * ν.point i a
  have hdecomp : ∀ i : ν.I,
      ν.weight i * ν.point i a =
        ν.positiveWeight i * ν.point i a - ν.negativeWeight i * ν.point i a := by
    intro i
    rw [weight_eq_positiveWeight_sub_negativeWeight, sub_mul]
  have hsum : ∑ i : ν.I, ν.weight i * ν.point i a = 0 := by
    unfold barycenterCoord at hbary; exact hbary
  rw [show ∑ i : ν.I, ν.weight i * ν.point i a =
      ∑ i : ν.I, (ν.positiveWeight i * ν.point i a - ν.negativeWeight i * ν.point i a)
    from Finset.sum_congr rfl (fun i _ => hdecomp i)] at hsum
  linarith [Finset.sum_sub_distrib (f := fun i => ν.positiveWeight i * ν.point i a)
    (g := fun i => ν.negativeWeight i * ν.point i a) (s := Finset.univ) |>.symm ▸ hsum]

theorem positiveMass_pos_of_eval_ne_zero {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hne : ν.eval ≠ ((fun _ => 0) : PosteriorLawSigned A)) :
    0 < ν.positiveMass := by
  letI : Fintype ν.I := ν.instFintypeI
  by_contra h_not_pos
  push_neg at h_not_pos
  have hpm_zero : ν.positiveMass = 0 :=
    le_antisymm h_not_pos (positiveMass_nonneg ν)
  have hnm_zero : ν.negativeMass = 0 := by
    have := positiveMass_eq_negativeMass_of_totalMass_zero ν hmass
    linarith
  have hpw_zero : ∀ i : ν.I, ν.positiveWeight i = 0 := by
    have h_sum_zero : ∑ i : ν.I, ν.positiveWeight i = 0 := by
      change ν.positiveMass = 0; exact hpm_zero
    exact summand_eq_zero_of_sum_eq_zero_of_nonneg'
      (fun i => ν.positiveWeight i)
      (fun i => positiveWeight_nonneg ν i)
      h_sum_zero
  have hnw_zero : ∀ i : ν.I, ν.negativeWeight i = 0 := by
    have h_sum_zero : ∑ i : ν.I, ν.negativeWeight i = 0 := by
      change ν.negativeMass = 0; exact hnm_zero
    exact summand_eq_zero_of_sum_eq_zero_of_nonneg'
      (fun i => ν.negativeWeight i)
      (fun i => negativeWeight_nonneg ν i)
      h_sum_zero
  have hw_zero : ∀ i : ν.I, ν.weight i = 0 := by
    intro i
    rw [weight_eq_positiveWeight_sub_negativeWeight, hpw_zero i, hnw_zero i, sub_self]
  apply hne
  funext φ
  simp [eval, hw_zero]

end AtomicPosteriorSignedLaw

namespace PosteriorLawSigned

/-- An extensional signed posterior law together with an explicit finite
atomic-linear witness. -/
structure AtomicLinear {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (η : PosteriorLawSigned A) where
  witness : AtomicPosteriorSignedLaw A
  eval_eq : witness.eval = η

theorem AtomicLinear.tangent {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    {η : PosteriorLawSigned A} (hη : AtomicLinear η)
    (hmass : hη.witness.totalMass = 0)
    (hbary : ∀ a : A, hη.witness.barycenterCoord a = 0) :
    PosteriorLawTangent η := by
  rw [← hη.eval_eq]
  exact hη.witness.eval_tangent hmass hbary

noncomputable def AtomicLinear.add {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    {η ζ : PosteriorLawSigned A}
    (hη : AtomicLinear η) (hζ : AtomicLinear ζ) :
    AtomicLinear (posteriorLawSignedAdd η ζ) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    letI : Fintype hζ.witness.I := hζ.witness.instFintypeI
    letI : DecidableEq hζ.witness.I := hζ.witness.instDecidableEqI
    exact {
      I := hη.witness.I ⊕ hζ.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := fun i => match i with
        | Sum.inl j => hη.witness.weight j
        | Sum.inr k => hζ.witness.weight k
      point := fun i => match i with
        | Sum.inl j => hη.witness.point j
        | Sum.inr k => hζ.witness.point k
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    letI : Fintype hζ.witness.I := hζ.witness.instFintypeI
    letI : DecidableEq hζ.witness.I := hζ.witness.instDecidableEqI
    funext φ
    simp only [AtomicPosteriorSignedLaw.eval_apply, posteriorLawSignedAdd]
    rw [show (∑ i : hη.witness.I ⊕ hζ.witness.I, _) =
      (∑ j : hη.witness.I, hη.witness.weight j * φ (hη.witness.point j)) +
      (∑ k : hζ.witness.I, hζ.witness.weight k * φ (hζ.witness.point k))
      from Fintype.sum_sum_type _]
    congr 1
    · have h := congrFun hη.eval_eq φ
      rw [AtomicPosteriorSignedLaw.eval_apply] at h
      linarith
    · have h := congrFun hζ.eval_eq φ
      rw [AtomicPosteriorSignedLaw.eval_apply] at h
      linarith

noncomputable def AtomicLinear.smul {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (c : ℝ) {η : PosteriorLawSigned A}
    (hη : AtomicLinear η) :
    AtomicLinear (posteriorLawSignedSMul c η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := fun i => c * hη.witness.weight i
      point := hη.witness.point
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    funext φ
    simp only [AtomicPosteriorSignedLaw.eval_apply, posteriorLawSignedSMul]
    have heval : hη.witness.eval φ = η φ := congrFun hη.eval_eq φ
    rw [AtomicPosteriorSignedLaw.eval_apply] at heval
    rw [← heval]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

end PosteriorLawSigned

/-- Concrete finite atomic posterior probability law. -/
structure AtomicPosteriorProbLaw (A : Type u)
    [Fintype A] [DecidableEq A] [Nonempty A] where
  I : Type u
  instFintypeI : Fintype I
  instDecidableEqI : DecidableEq I
  mass : I → ℝ
  point : I → Dist A
  mass_nonneg : ∀ i : I, 0 ≤ mass i
  mass_sum :
    letI : Fintype I := instFintypeI
    ∑ i : I, mass i = 1

namespace AtomicPosteriorProbLaw

/-- Evaluation of an atomic posterior probability law on a test function. -/
noncomputable def eval {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (μ : AtomicPosteriorProbLaw A) : PosteriorLawSigned A := by
  letI : Fintype μ.I := μ.instFintypeI
  exact fun φ => ∑ i : μ.I, μ.mass i * φ (μ.point i)

/-- Barycentre coordinate of an atomic posterior probability law. -/
noncomputable def barycenterCoord {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (μ : AtomicPosteriorProbLaw A) (a : A) : ℝ := by
  letI : Fintype μ.I := μ.instFintypeI
  exact ∑ i : μ.I, μ.mass i * μ.point i a

@[simp] theorem eval_apply {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (μ : AtomicPosteriorProbLaw A) (φ : Dist A → ℝ) :
    μ.eval φ = by
      letI : Fintype μ.I := μ.instFintypeI
      exact ∑ i : μ.I, μ.mass i * φ (μ.point i) := by
  rfl

theorem eval_const_one {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (μ : AtomicPosteriorProbLaw A) :
    μ.eval (fun _ => (1 : ℝ)) = 1 := by
  simp [eval, μ.mass_sum]

theorem eval_coord {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (μ : AtomicPosteriorProbLaw A) (a : A) :
    μ.eval (fun p => p a) = μ.barycenterCoord a := by
  simp [eval, barycenterCoord]

/-- Channel realizing an atomic posterior probability law with barycentre `r`.

For outcome atom `i`, Bayes' rule requires
`P(i | a) = mass i * point i a / r a`. -/
noncomputable def posteriorProbLawChannel {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (μ : AtomicPosteriorProbLaw A)
    (hbary : ∀ a : A, μ.barycenterCoord a = r a) :
    @Channel A μ.I μ.instFintypeI := by
  letI : Fintype μ.I := μ.instFintypeI
  exact fun a =>
    { prob := fun i => μ.mass i * μ.point i a / r a
      nonneg := fun i =>
        div_nonneg
          (mul_nonneg (μ.mass_nonneg i) ((μ.point i).nonneg a))
          (le_of_lt (hr a))
      sum_eq_one := by
        rw [← Finset.sum_div]
        have hb := hbary a
        unfold barycenterCoord at hb
        change (∑ i : μ.I, μ.mass i * μ.point i a) / r a = 1
        rw [hb]
        exact div_self (ne_of_gt (hr a)) }

/-- Experiment realizing an atomic posterior probability law with barycentre
equal to the full-support prior. -/
noncomputable def experimentOfPosteriorProbLaw {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (μ : AtomicPosteriorProbLaw A)
    (hbary : ∀ a : A, μ.barycenterCoord a = r a) :
    FiniteExperimentOn A := by
  letI : Fintype μ.I := μ.instFintypeI
  letI : DecidableEq μ.I := μ.instDecidableEqI
  exact experimentOfChannel (posteriorProbLawChannel r hr μ hbary)

theorem outcomeMarginal_posteriorProbLawChannel {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (μ : AtomicPosteriorProbLaw A)
    (hbary : ∀ a : A, μ.barycenterCoord a = r a)
    (i : μ.I) :
    (@Channel.outcomeMarginal A μ.I _ μ.instFintypeI
      (posteriorProbLawChannel r hr μ hbary) r) i = μ.mass i := by
  letI : Fintype μ.I := μ.instFintypeI
  calc
    (@Channel.outcomeMarginal A μ.I _ μ.instFintypeI
      (posteriorProbLawChannel r hr μ hbary) r) i
        = ∑ a : A, r a * (μ.mass i * μ.point i a / r a) := by
          rfl
    _ = ∑ a : A, μ.mass i * μ.point i a := by
      apply Finset.sum_congr rfl
      intro a _
      field_simp [ne_of_gt (hr a)]
    _ = μ.mass i * ∑ a : A, μ.point i a := by
      rw [Finset.mul_sum]
    _ = μ.mass i := by
      rw [(μ.point i).sum_eq_one, mul_one]

theorem posterior_posteriorProbLawChannel_of_pos {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (μ : AtomicPosteriorProbLaw A)
    (hbary : ∀ a : A, μ.barycenterCoord a = r a)
    (i : μ.I) (hpos : 0 < μ.mass i) :
    letI : Fintype μ.I := μ.instFintypeI
    Channel.posterior (posteriorProbLawChannel r hr μ hbary) r i = μ.point i := by
  letI : Fintype μ.I := μ.instFintypeI
  have hmarg : (Channel.outcomeMarginal
      (posteriorProbLawChannel r hr μ hbary) r) i = μ.mass i :=
    outcomeMarginal_posteriorProbLawChannel r hr μ hbary i
  have hmarg_pos : (Channel.outcomeMarginal
      (posteriorProbLawChannel r hr μ hbary) r) i > 0 := by
    rw [hmarg]; exact hpos
  ext a
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  simp only [posteriorProbLawChannel]
  have hra_ne : r a ≠ 0 := ne_of_gt (hr a)
  rw [hmarg]
  field_simp

theorem posteriorLawIntegralExp_experimentOfPosteriorProbLaw {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (μ : AtomicPosteriorProbLaw A)
    (hbary : ∀ a : A, μ.barycenterCoord a = r a)
    (φ : Dist A → ℝ) :
    posteriorLawIntegralExp r
      (μ.experimentOfPosteriorProbLaw r hr hbary) φ =
        μ.eval φ := by
  letI : Fintype μ.I := μ.instFintypeI
  letI : DecidableEq μ.I := μ.instDecidableEqI
  unfold posteriorLawIntegralExp experimentOfPosteriorProbLaw experimentOfChannel
    FiniteExperimentOn.ofChannel FiniteExperimentOn.outcomeMarginal
    FiniteExperimentOn.posterior
  change ∑ i : μ.I,
      (Channel.outcomeMarginal (posteriorProbLawChannel r hr μ hbary) r) i *
        φ (Channel.posterior (posteriorProbLawChannel r hr μ hbary) r i) =
    ∑ i : μ.I, μ.mass i * φ (μ.point i)
  apply Finset.sum_congr rfl
  intro i _
  rw [outcomeMarginal_posteriorProbLawChannel r hr μ hbary i]
  by_cases hpos : (0 : ℝ) < μ.mass i
  · rw [posterior_posteriorProbLawChannel_of_pos r hr μ hbary i hpos]
  · have hle : μ.mass i ≤ 0 := le_of_not_gt hpos
    have heq : μ.mass i = 0 := le_antisymm hle (μ.mass_nonneg i)
    rw [heq, zero_mul, zero_mul]

end AtomicPosteriorProbLaw

@[simp] theorem posteriorLawSignedOfExperiment_apply {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (φ : Dist A → ℝ) :
    posteriorLawSignedOfExperiment q E φ = posteriorLawIntegralExp q E φ :=
  rfl

@[simp] theorem posteriorLawDifferenceExp_apply {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp q E E' φ =
      posteriorLawIntegralExp q E φ - posteriorLawIntegralExp q E' φ :=
  rfl

@[simp] theorem posteriorLawSignedAdd_apply {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (η ζ : PosteriorLawSigned A) (φ : Dist A → ℝ) :
    posteriorLawSignedAdd η ζ φ = η φ + ζ φ :=
  rfl

@[simp] theorem posteriorLawSignedSMul_apply {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (c : ℝ) (η : PosteriorLawSigned A) (φ : Dist A → ℝ) :
    posteriorLawSignedSMul c η φ = c * η φ :=
  rfl

@[simp] theorem posteriorLawSignedFinsetSum_apply {ι A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (s : Finset ι) (η : ι → PosteriorLawSigned A) (φ : Dist A → ℝ) :
    posteriorLawSignedFinsetSum s η φ = s.sum (fun i => η i φ) :=
  rfl

@[simp] theorem posteriorLawSignedSum_apply {ι A : Type u}
    [Fintype ι] [Fintype A] [DecidableEq A] [Nonempty A]
    (η : ι → PosteriorLawSigned A) (φ : Dist A → ℝ) :
    posteriorLawSignedSum η φ = ∑ i, η i φ :=
  rfl

@[simp] theorem posteriorLawSignedFinsetSum_empty {ι A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (η : ι → PosteriorLawSigned A) :
    posteriorLawSignedFinsetSum (∅ : Finset ι) η =
      ((fun _ => 0) : PosteriorLawSigned A) := by
  funext φ
  simp [posteriorLawSignedFinsetSum]

theorem posteriorLawSignedFinsetSum_insert {ι A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [DecidableEq ι]
    (i : ι) (s : Finset ι) (η : ι → PosteriorLawSigned A)
    (hi : i ∉ s) :
    posteriorLawSignedFinsetSum (insert i s) η =
      posteriorLawSignedAdd (η i) (posteriorLawSignedFinsetSum s η) := by
  funext φ
  simp [posteriorLawSignedFinsetSum, posteriorLawSignedAdd, Finset.sum_insert hi]

@[simp] theorem posteriorLawDifferenceExp_self {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) :
    posteriorLawDifferenceExp q E E = ((fun _ => 0) : PosteriorLawSigned A) := by
  funext φ
  simp [posteriorLawDifferenceExp]

theorem posteriorLawDifferenceExp_swap {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    posteriorLawDifferenceExp q E' E =
  posteriorLawSignedSMul (-1) (posteriorLawDifferenceExp q E E') := by
  funext φ
  simp [posteriorLawDifferenceExp, posteriorLawSignedSMul]

/-- Pad a channel into the left side of a disjoint-sum outcome type. -/
noncomputable def outcomePadLeft {A O Y : Type u}
    [Fintype O] [Fintype Y] (P : Channel A O) : Channel A (O ⊕ Y) :=
  fun a =>
    { prob := fun oy =>
        match oy with
        | Sum.inl o => P a o
        | Sum.inr _ => 0
      nonneg := fun oy =>
        match oy with
        | Sum.inl o => (P a).nonneg o
        | Sum.inr _ => le_refl 0
      sum_eq_one := by
        simp only [Fintype.sum_sum_type, Finset.sum_const_zero, add_zero]
        exact (P a).sum_eq_one }

/-- Pad a channel into the right side of a disjoint-sum outcome type. -/
noncomputable def outcomePadRight {A O Y : Type u}
    [Fintype O] [Fintype Y] (P : Channel A Y) : Channel A (O ⊕ Y) :=
  fun a =>
    { prob := fun oy =>
        match oy with
        | Sum.inl _ => 0
        | Sum.inr y => P a y
      nonneg := fun oy =>
        match oy with
        | Sum.inl _ => le_refl 0
        | Sum.inr y => (P a).nonneg y
      sum_eq_one := by
        simp only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add]
        exact (P a).sum_eq_one }

/-- Left-padded channels preserve posterior-law integrals. -/
theorem posteriorLawIntegral_outcomePadLeft
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (outcomePadLeft (Y := Y) P) φ =
      posteriorLawIntegral q P φ := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_sum_type]
  simp only [outcomePadLeft, Channel.outcomeMarginal_apply]
  have hinl :
      (∑ x : O,
          (∑ a : A, q a * P a x) *
            φ (Channel.posterior (outcomePadLeft (Y := Y) P) q (Sum.inl x))) =
        ∑ x : O,
          (∑ a : A, q a * P a x) *
            φ (Channel.posterior P q x) := by
    apply Finset.sum_congr rfl
    intro o _ho
    simp [outcomePadLeft, Channel.posterior, Channel.outcomeMarginal_apply]
  have hinr :
      (∑ x : Y,
          (∑ a : A, q a * 0) *
            φ (Channel.posterior (outcomePadLeft (Y := Y) P) q (Sum.inr x))) = 0 := by
    simp
  rw [hinl, hinr, add_zero]

/-- Right-padded channels preserve posterior-law integrals. -/
theorem posteriorLawIntegral_outcomePadRight
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A Y) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (outcomePadRight (O := O) P) φ =
      posteriorLawIntegral q P φ := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_sum_type]
  simp only [outcomePadRight, Channel.outcomeMarginal_apply]
  have hinl :
      (∑ x : O,
          (∑ a : A, q a * 0) *
            φ (Channel.posterior (outcomePadRight (O := O) P) q (Sum.inl x))) = 0 := by
    simp
  have hinr :
      (∑ x : Y,
          (∑ a : A, q a * P a x) *
            φ (Channel.posterior (outcomePadRight (O := O) P) q (Sum.inr x))) =
        ∑ x : Y,
          (∑ a : A, q a * P a x) *
            φ (Channel.posterior P q x) := by
    apply Finset.sum_congr rfl
    intro y _hy
    simp [outcomePadRight, Channel.posterior, Channel.outcomeMarginal_apply]
  rw [hinl, zero_add, hinr]

@[simp] theorem posteriorLawIntegralExp_experimentOfChannel
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (experimentOfChannel P) φ =
      posteriorLawIntegral q P φ := by
  rfl

@[simp] theorem posteriorLawIntegralExp_eq_channel
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q E φ =
      @posteriorLawIntegral A _ _ _ E.OutcomeType E.outFintype
        q E.P φ := by
  rfl

/-- The uninformative channel induces the point-mass posterior law at the
prior. -/
theorem posteriorLawIntegral_uninformativeChannelU_eq_prior
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (Channel.uninformativeChannelU A) φ = φ q := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_eq_single PUnit.unit]
  · have hm :
        Channel.outcomeMarginal (Channel.uninformativeChannelU A) q PUnit.unit = 1 := by
      simp [Channel.outcomeMarginal, Channel.uninformativeChannelU, q.sum_eq_one]
    have hp :
        Channel.posterior (Channel.uninformativeChannelU A) q PUnit.unit = q := by
      ext a
      simp [Channel.posterior, Channel.outcomeMarginal,
        Channel.uninformativeChannelU, q.sum_eq_one]
    rw [hm, hp]
    ring
  · intro b hb
    cases b
    contradiction

/-- Experiment-level version of
`posteriorLawIntegral_uninformativeChannelU_eq_prior`. -/
theorem posteriorLawIntegralExp_uninformativeChannelU_eq_prior
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q
      (experimentOfChannel (Channel.uninformativeChannelU A)) φ = φ q := by
  rw [posteriorLawIntegralExp_experimentOfChannel]
  exact posteriorLawIntegral_uninformativeChannelU_eq_prior q φ

/-- Posterior-law integration preserves the constant-one test function. -/
theorem posteriorLawIntegral_const_one
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] (q : Dist A) (P : Channel A O) :
    posteriorLawIntegral q P (fun _ => (1 : ℝ)) = 1 := by
  unfold posteriorLawIntegral
  simp_rw [mul_one]
  exact (Channel.outcomeMarginal P q).sum_eq_one

/-- Experiment-level version of `posteriorLawIntegral_const_one`. -/
theorem posteriorLawIntegralExp_const_one
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) :
    posteriorLawIntegralExp q E (fun _ => (1 : ℝ)) = 1 := by
  letI : Fintype E.OutcomeType := E.outFintype
  rw [posteriorLawIntegralExp_eq_channel]
  exact posteriorLawIntegral_const_one q E.P

/-- Posterior-law integration of coordinate evaluation recovers the prior
coordinate. -/
theorem posteriorLawIntegral_coord
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] (q : Dist A) (P : Channel A O) (a : A) :
    posteriorLawIntegral q P (fun p => p a) = q a := by
  unfold posteriorLawIntegral
  calc
    (∑ o : O, (Channel.outcomeMarginal P q) o *
        (Channel.posterior P q o) a) =
        ∑ o : O, q a * P a o := by
      apply Finset.sum_congr rfl
      intro o _ho
      exact posterior_mul_marginal q P o a
    _ = q a * ∑ o : O, P a o := by
      rw [Finset.mul_sum]
    _ = q a := by
      rw [(P a).sum_eq_one, mul_one]

/-- Experiment-level version of `posteriorLawIntegral_coord`. -/
theorem posteriorLawIntegralExp_coord
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (a : A) :
    posteriorLawIntegralExp q E (fun p => p a) = q a := by
  letI : Fintype E.OutcomeType := E.outFintype
  rw [posteriorLawIntegralExp_eq_channel]
  exact posteriorLawIntegral_coord q E.P a

/-- Feasible differences of posterior laws are tangent signed posterior laws:
they have zero total mass and zero barycentre. -/
theorem posteriorLawDifferenceExp_tangent {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    PosteriorLawTangent (posteriorLawDifferenceExp q E E') := by
  constructor
  · unfold posteriorLawDifferenceExp
    rw [posteriorLawIntegralExp_const_one q E,
      posteriorLawIntegralExp_const_one q E']
    ring
  · intro a
    unfold posteriorLawDifferenceExp
    rw [posteriorLawIntegralExp_coord q E a,
      posteriorLawIntegralExp_coord q E' a]
    ring

/-- A posterior-law difference is atomic-linear: it admits an explicit finite
atomic signed-law witness. -/
noncomputable def posteriorLawDifferenceExp_atomicLinear {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    PosteriorLawSigned.AtomicLinear (posteriorLawDifferenceExp q E E') where
  witness := by
    letI : Fintype E.OutcomeType := E.outFintype
    letI : DecidableEq E.OutcomeType := E.outDecEq
    letI : Fintype E'.OutcomeType := E'.outFintype
    letI : DecidableEq E'.OutcomeType := E'.outDecEq
    exact {
      I := E.OutcomeType ⊕ E'.OutcomeType
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := fun i => match i with
        | Sum.inl o => (E.outcomeMarginal q) o
        | Sum.inr o' => -((E'.outcomeMarginal q) o')
      point := fun i => match i with
        | Sum.inl o => E.posterior q o
        | Sum.inr o' => E'.posterior q o'
    }
  eval_eq := by
    letI : Fintype E.OutcomeType := E.outFintype
    letI : DecidableEq E.OutcomeType := E.outDecEq
    letI : Fintype E'.OutcomeType := E'.outFintype
    letI : DecidableEq E'.OutcomeType := E'.outDecEq
    funext φ
    unfold posteriorLawDifferenceExp posteriorLawIntegralExp
    simp only [AtomicPosteriorSignedLaw.eval_apply]
    rw [show (∑ i : E.OutcomeType ⊕ E'.OutcomeType, _) =
      (∑ o : E.OutcomeType,
        (E.outcomeMarginal q) o * φ (E.posterior q o)) +
      (∑ o' : E'.OutcomeType,
        -((E'.outcomeMarginal q) o') * φ (E'.posterior q o'))
      from Fintype.sum_sum_type _]
    simp only [neg_mul, Finset.sum_neg_distrib]
    ring

/-- Tangent signed posterior laws are closed under addition. -/
theorem PosteriorLawTangent_add {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    {η ζ : PosteriorLawSigned A}
    (hη : PosteriorLawTangent η) (hζ : PosteriorLawTangent ζ) :
    PosteriorLawTangent (posteriorLawSignedAdd η ζ) := by
  constructor
  · simp [posteriorLawSignedAdd, hη.1, hζ.1]
  · intro a
    simp [posteriorLawSignedAdd, hη.2 a, hζ.2 a]

/-- Tangent signed posterior laws are closed under scalar multiplication. -/
theorem PosteriorLawTangent_smul {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (c : ℝ) {η : PosteriorLawSigned A} (hη : PosteriorLawTangent η) :
    PosteriorLawTangent (posteriorLawSignedSMul c η) := by
  constructor
  · simp [posteriorLawSignedSMul, hη.1]
  · intro a
    simp [posteriorLawSignedSMul, hη.2 a]

theorem PosteriorLawTangent_neg {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    {η : PosteriorLawSigned A} (htan : PosteriorLawTangent η) :
    PosteriorLawTangent (posteriorLawSignedSMul (-1) η) := by
  exact PosteriorLawTangent_smul (-1) htan

theorem posteriorLawSignedSMul_neg_ne_zero {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    {η : PosteriorLawSigned A}
    (hηne : η ≠ ((fun _ => 0) : PosteriorLawSigned A)) :
    posteriorLawSignedSMul (-1) η ≠ ((fun _ => 0) : PosteriorLawSigned A) := by
  intro hneg
  apply hηne
  funext φ
  have h := congrFun hneg φ
  simp [posteriorLawSignedSMul] at h
  linarith

/-!
## Affine linear-part interface

This is a narrow replacement component for the first analytic step of
`Branch aggregation`: an affine posterior-value representative has a linear
part on extensional signed posterior-law differences.  It does not include A7,
branch comparison, tangent-space path-independence, boundary support handling,
or the final aggregation formula.
-/

/-- Finite posterior-law integral representation.

This is the project-level finite specialization of the Herstein--Milnor
posterior-separable conclusion: the chosen value representative is evaluation
against a finite posterior test function.  It is global to posterior-law values,
not branch-specific. -/
structure FinitePosteriorIntegralRepresentationAssumptions.{v} where
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
  /-- **Support-face coherence of the marginal-value test function.**
      The Herstein--Milnor marginal-value function at a prior `q` agrees, on
      posteriors supported inside `supp(q)`, with the marginal-value function at
      the support-face prior `q.restrictToSupport`.  A posterior belief supported
      on the positive support is the same belief whether read in the ambient
      action space or on the support face, so the representing test function must
      agree on it.  This is a genuine coherence property of the true HM functional
      (which represents the whole order, boundary included), not a boundary
      normalization; it lets boundary support-restriction of the value be proved
      rather than assumed (see `normalizedValueSupportBoundary_of_boundaryComplete`). -/
  marginalValue_support_face :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) [Nonempty (supportSubtype q)]
      (d : Dist (supportSubtype q)),
      marginalValue F hV q (Channel.actionPushforward d (supportIncludeKernel q)) =
        marginalValue F hV q.restrictToSupport d
  /-- **Exact relabelling covariance (naturality) of the marginal-value test
      function.**
      The Herstein--Milnor marginal-value function is natural in finite action
      relabellings: relabelling the alphabet by a bijection `eA : A ≃ B` carries
      the representing test function to the test function at the relabelled prior,
      evaluated at the relabelled posterior belief. -/
  marginalValue_relabel :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A B : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (eA : A ≃ B) (q : Dist A) (d : Dist A),
      marginalValue F hV (Relabeling.relabelDist eA q)
          (Relabeling.relabelDist eA d) =
        marginalValue F hV q d

/-- Finite affine linear-part interface for posterior-law values.

**Paper role**: if `F_q` is affine on the posterior-law set `M_q`, then
Herstein-Milnor gives an integral representation `F_q(μ) = ∫ φ_q(r) dμ(r)`
for a marginal value function `φ_q : Dist A → ℝ`.  The linear part is then
`L_q(η) := η(φ_q)`, where `η : PosteriorLawSigned A = (Dist A → ℝ) → ℝ` acts
on the test function `φ_q`.  This satisfies `F_q(μ_E) - F_q(μ_{E'}) = L_q(μ_E - μ_{E'})`.

**External mathematical status**: this structure is an explicit external assumption
packaging the integral representation of `V q` and its extension to the full
signed-law tangent space.  It is a theorem, not a representative choice, that follows from
Herstein-Milnor applied to the posterior-law quotient, but formalizing the integral
representation in Lean is out of scope for the current development.

Paper citation: Lemma postsep / integral form (lines 1000-1196); the affinity of
`F_q` is the Herstein-Milnor output and the integral form is immediate from it. -/
structure FiniteAffineLinearPartAssumptions.{v} where
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

/-!
## One-branch A7 plumbing

These lemmas do not prove the branch-slice affine theorem.  They isolate the
pure A7/A3/A1 step: if two continuation profiles differ in one branch only,
then the branch comparison lifts to the aggregate comparison.
-/

/-- A1 gives reflexivity of the preference relation for a fixed channel. -/
theorem rel_refl_of_A1
    (F : PrefFamily.{u}) (hA1 : A1_WeakOrderLocalNontriviality F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel P q q := by
  exact (hA1.1 P).1 q q |>.elim id id

/-- Identical branches are weakly comparable in the duplicated block
environment, by A3 plus A1 reflexivity. -/
theorem block_duplicate_rel_refl_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel (blockChannel P P) (inlDist q) (inrDist q) := by
  exact (hax.a3.1 P q q).mp (rel_refl_of_A1 F hax.a1 P q)

/-- Weak one-branch A7 specialization.  All non-target branches are identical,
so their weak comparisons are supplied by `block_duplicate_rel_refl_of_axioms`.
-/
theorem A7_weak_one_branch_of_rel
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q R : ∀ o, Channel A (O₂ o)) (target : O₁)
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (htarget :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target))) :
    F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q) := by
  exact hax.a7.1 O₂ q P₁ Q R (fun o _hpos => by
    by_cases ho : o = target
    · subst ho
      exact htarget
    · rw [hsame o ho]
      exact block_duplicate_rel_refl_of_axioms F hax (R o) (branchPosterior P₁ q o))

/-- Strict one-branch A7 specialization.  The target branch is strictly better,
and all non-target branches are identical. -/
theorem A7_strict_one_branch_of_strict
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q R : ∀ o, Channel A (O₂ o)) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (htarget_weak :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)))
    (htarget_strict :
      F.strictRel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target))) :
    F.strictRel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q) := by
  exact hax.a7.2 O₂ q P₁ Q R
    (fun o _hpos => by
      by_cases ho : o = target
      · subst ho
        exact htarget_weak
      · rw [hsame o ho]
        exact block_duplicate_rel_refl_of_axioms F hax (R o) (branchPosterior P₁ q o))
    ⟨target, hpos, htarget_strict⟩

/-!
## Feasible branch-difference sign preservation

The tangent-space sign-preservation theorem needed for path independence is
stronger than A7 directly supplies: it talks about arbitrary signed
posterior-law directions.  A7 directly supplies the following feasible-channel
version, where the signed direction is the difference of two continuation
experiments and the aggregate experiments differ only in one branch.
-/

theorem linearPart_difference_pos_iff_value_gt
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    0 < hlin.linearPart F hV q (posteriorLawDifferenceExp q E E') ↔
      hV.V q E' < hV.V q E := by
  have hdiff := hlin.value_difference F hV q E E'
  constructor
  · intro hpos
    linarith
  · intro hgt
    linarith

theorem linearPart_difference_zero_iff_value_eq
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    hlin.linearPart F hV q (posteriorLawDifferenceExp q E E') = 0 ↔
      hV.V q E = hV.V q E' := by
  have hdiff := hlin.value_difference F hV q E E'
  constructor
  · intro hzero
    linarith
  · intro heq
    linarith

theorem linearPart_difference_swap_eq_neg
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    hlin.linearPart F hV q (posteriorLawDifferenceExp q E' E) =
      - hlin.linearPart F hV q (posteriorLawDifferenceExp q E E') := by
  rw [posteriorLawDifferenceExp_swap, hlin.linearPart_smul]
  ring

/-- A value gap between two experiments gives a nonzero affine-linear-part
witness in the corresponding signed posterior-law direction. -/
theorem branch_linear_part_nonzero_of_value_gap
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (E E' : FiniteExperimentOn A)
    (hgap : hV.V r E ≠ hV.V r E') :
    ∃ η : PosteriorLawSigned A,
      hlin.linearPart F hV r η ≠ 0 := by
  refine ⟨posteriorLawDifferenceExp r E E', ?_⟩
  intro hzero
  have hdiff := hlin.value_difference F hV r E E'
  have hVeq : hV.V r E = hV.V r E' := by
    linarith
  exact hgap hVeq

/-- Strict experiment-pair preference at a full-support prior forces a strict
gap in any posterior value representation. -/
theorem branch_value_ne_of_strict_experiment_pref
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (E₁ E₂ : FiniteExperimentOn A)
    (hpref : ExperimentPairPref F E₁ E₂ q q)
    (hnrev : ¬ ExperimentPairPref F E₂ E₁ q q) :
    hV.V q E₁ ≠ hV.V q E₂ := by
  intro heq
  have hge₂₁ : hV.V q E₂ ≥ hV.V q E₁ := by
    simp [heq]
  exact hnrev ((hV.represents_block_comparisons q hq E₂ E₁).mpr hge₂₁)

/-- A nondegenerate support witness rules out a subsingleton action type. -/
theorem not_subsingleton_of_dist_nondegenerate
    {A : Type u} [Fintype A] (r : Dist A)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ¬ Subsingleton A := by
  intro hsub
  rcases hr_nondegenerate with ⟨a, b, hab, _ha, _hb⟩
  exact hab (Subsingleton.elim a b)

/-- A1's strict full-revelation versus no-information comparison, transported
to the experiment-pair orientation used by posterior value representatives. -/
theorem branch_id_uninformativeU_experiment_strict_of_A1
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hnot_subsingleton : ¬ Subsingleton A) :
    ExperimentPairPref F
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      q q
    ∧
    ¬ ExperimentPairPref F
      (experimentOfChannel (Channel.uninformativeChannelU A))
      (experimentOfChannel (Channel.idChannel : Channel A A))
      q q := by
  classical
  haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
  have hstrict :=
    Relabeling.lifted_uninformative_strict_of_A1 F hax q hq
  constructor
  · change
      F.rel
        (blockChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A))
        (inlDist q) (inrDist q)
    exact hstrict.1
  · intro hrev
    change
      F.rel
        (blockChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel A A))
        (inlDist q) (inrDist q) at hrev
    have hrev_same :
        F.rel
          (blockChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU A))
          (inrDist q) (inlDist q) := by
      exact
        (Relabeling.block_swap_rel_of_axioms F hax
          (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A) q q).mpr hrev
    exact hstrict.2 hrev_same

/-- A1 and the value representation give a concrete value gap at every
full-support nondegenerate prior. -/
theorem branch_value_gap_of_A1
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ E E' : FiniteExperimentOn A,
      hV.V r E ≠ hV.V r E' := by
  have hnot_subsingleton : ¬ Subsingleton A :=
    not_subsingleton_of_dist_nondegenerate r hr_nondegenerate
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax r hr hnot_subsingleton
  refine ⟨experimentOfChannel (Channel.idChannel : Channel A A),
    experimentOfChannel (Channel.uninformativeChannelU A), ?_⟩
  exact branch_value_ne_of_strict_experiment_pref F hV r hr
    (experimentOfChannel (Channel.idChannel : Channel A A))
    (experimentOfChannel (Channel.uninformativeChannelU A))
    hstrict.1 hstrict.2

/-- A1 supplies the nonzero branch-linear-functional witness needed by the
same-sign scalar argument, once the affine linear part is available.

The theorem is deliberately `TraceAxioms`-aware.  The legacy
`FiniteBranchLinearPartNonzeroAssumptions` below has no `TraceAxioms` argument,
so it is stronger than what A1 can prove directly. -/
theorem branch_linear_part_nonzero_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ η : PosteriorLawSigned A, hlin.linearPart F hV r η ≠ 0 := by
  rcases branch_value_gap_of_A1 F hax hV r hr hr_nondegenerate with
    ⟨E, E', hgap⟩
  exact branch_linear_part_nonzero_of_value_gap hlin F hV r E E' hgap

/-- A1 supplies a nonzero branch-linear-functional witness inside the tangent
subspace. -/
theorem branch_linear_part_nonzero_tangent_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ η : PosteriorLawSigned A,
      PosteriorLawTangent η ∧ hlin.linearPart F hV r η ≠ 0 := by
  rcases branch_value_gap_of_A1 F hax hV r hr hr_nondegenerate with
    ⟨E, E', hgap⟩
  refine ⟨posteriorLawDifferenceExp r E E',
    posteriorLawDifferenceExp_tangent r E E', ?_⟩
  intro hzero
  have hdiff := hlin.value_difference F hV r E E'
  have hVeq : hV.V r E = hV.V r E' := by
    linarith
  exact hgap hVeq

theorem branch_linear_part_nonzero_atomicLinear_tangent_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ (η : PosteriorLawSigned A) (_hatomic : PosteriorLawSigned.AtomicLinear η),
      PosteriorLawTangent η ∧ hlin.linearPart F hV r η ≠ 0 := by
  rcases branch_value_gap_of_A1 F hax hV r hr hr_nondegenerate with
    ⟨E, E', hgap⟩
  refine ⟨posteriorLawDifferenceExp r E E',
    posteriorLawDifferenceExp_atomicLinear r E E',
    posteriorLawDifferenceExp_tangent r E E', ?_⟩
  intro hzero
  have hdiff := hlin.value_difference F hV r E E'
  have hVeq : hV.V r E = hV.V r E' := by
    linarith
  exact hgap hVeq

theorem block_rel_of_channel_value_ge
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : Channel A Y)
    (hge :
      hV.V q (experimentOfChannel P) ≥
        hV.V q (experimentOfChannel Q)) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist q) := by
  have hpref :
      ExperimentPairPref F (experimentOfChannel P) (experimentOfChannel Q) q q :=
    (hV.represents_block_comparisons q hq _ _).mpr hge
  change F.rel (blockChannel P Q) (inlDist q) (inrDist q) at hpref
  exact hpref

theorem block_strictRel_of_channel_value_gt
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : Channel A Y)
    (hgt :
      hV.V q (experimentOfChannel Q) <
        hV.V q (experimentOfChannel P)) :
    F.strictRel (blockChannel P Q) (inlDist q) (inrDist q) := by
  constructor
  · exact block_rel_of_channel_value_ge F hV q hq P Q (le_of_lt hgt)
  · intro hrev
    have hswap :
        F.rel (blockChannel Q P) (inlDist q) (inrDist q) :=
      (Relabeling.block_swap_rel_of_axioms F hax P Q q q).mp hrev
    have hpref_rev :
        ExperimentPairPref F (experimentOfChannel Q) (experimentOfChannel P) q q := by
      change F.rel (blockChannel Q P) (inlDist q) (inrDist q)
      exact hswap
    have hge_rev :
        hV.V q (experimentOfChannel Q) ≥
          hV.V q (experimentOfChannel P) :=
      (hV.represents_block_comparisons q hq _ _).mp hpref_rev
    linarith

theorem branch_feasible_difference_pos_of_branch_pos
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o))
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (hr : (branchPosterior P₁ q target).FullSupport)
    (hbranch_pos :
      0 < hlin.linearPart F hV (branchPosterior P₁ q target)
        (posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target)))) :
    0 < hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R))) := by
  have hbranch_gt :
      hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (R target)) <
        hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (Q target)) :=
    (linearPart_difference_pos_iff_value_gt hlin F hV
      (branchPosterior P₁ q target)
      (experimentOfChannel (Q target))
      (experimentOfChannel (R target))).mp hbranch_pos
  have htarget_weak :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_rel_of_channel_value_ge F hV
      (branchPosterior P₁ q target) hr (Q target) (R target)
      (le_of_lt hbranch_gt)
  have htarget_strict :
      F.strictRel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_strictRel_of_channel_value_gt F hax hV
      (branchPosterior P₁ q target) hr (Q target) (R target)
      hbranch_gt
  have hagg_strict :
      F.strictRel
        (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
        (inlDist q) (inrDist q) :=
    A7_strict_one_branch_of_strict F hax O₂ q P₁ Q R target hpos hsame
      htarget_weak htarget_strict
  have hagg_gt :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) <
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) := by
    have hpref :
        ExperimentPairPref F
          (experimentOfChannel (seqComposeDep P₁ O₂ Q))
          (experimentOfChannel (seqComposeDep P₁ O₂ R)) q q := by
      change F.rel
        (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
        (inlDist q) (inrDist q)
      exact hagg_strict.1
    have hge :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) ≥
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) :=
      (hV.represents_block_comparisons q hq _ _).mp hpref
    by_contra hnot_gt
    have hge_rev :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) ≥
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) :=
      le_of_not_gt hnot_gt
    have hpref_rev :
        ExperimentPairPref F
          (experimentOfChannel (seqComposeDep P₁ O₂ R))
          (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q :=
      (hV.represents_block_comparisons q hq _ _).mpr hge_rev
    have hrel_rev :
        F.rel
          (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q))
          (inlDist q) (inrDist q) := by
      exact hpref_rev
    have hrel_rev_same :
        F.rel
          (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
          (inrDist q) (inlDist q) :=
      (Relabeling.block_swap_rel_of_axioms F hax
        (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R) q q).mpr hrel_rev
    exact hagg_strict.2 hrel_rev_same
  exact (linearPart_difference_pos_iff_value_gt hlin F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q))
    (experimentOfChannel (seqComposeDep P₁ O₂ R))).mpr hagg_gt

theorem branch_feasible_difference_zero_of_branch_zero
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o))
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (hr : (branchPosterior P₁ q target).FullSupport)
    (hbranch_zero :
      hlin.linearPart F hV (branchPosterior P₁ q target)
        (posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target))) = 0) :
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R))) = 0 := by
  have hbranch_eq :
      hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (Q target)) =
        hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (R target)) :=
    (linearPart_difference_zero_iff_value_eq hlin F hV
      (branchPosterior P₁ q target)
      (experimentOfChannel (Q target))
      (experimentOfChannel (R target))).mp hbranch_zero
  have htarget_QR :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_rel_of_channel_value_ge F hV
      (branchPosterior P₁ q target) hr (Q target) (R target) (by
        rw [hbranch_eq])
  have htarget_RQ :
      F.rel (blockChannel (R target) (Q target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_rel_of_channel_value_ge F hV
      (branchPosterior P₁ q target) hr (R target) (Q target) (by
        rw [hbranch_eq])
  have hagg_QR :
      F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
        (inlDist q) (inrDist q) :=
    A7_weak_one_branch_of_rel F hax O₂ q P₁ Q R target hsame htarget_QR
  have hagg_RQ :
      F.rel (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q))
        (inlDist q) (inrDist q) :=
    A7_weak_one_branch_of_rel F hax O₂ q P₁ R Q target
      (fun o ho => (hsame o ho).symm) htarget_RQ
  have hpref_QR :
      ExperimentPairPref F
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R)) q q := by
    change F.rel
      (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q)
    exact hagg_QR
  have hpref_RQ :
      ExperimentPairPref F
        (experimentOfChannel (seqComposeDep P₁ O₂ R))
        (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q := by
    change F.rel
      (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q))
      (inlDist q) (inrDist q)
    exact hagg_RQ
  have hge_QR :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) ≥
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) :=
    (hV.represents_block_comparisons q hq _ _).mp hpref_QR
  have hge_RQ :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) ≥
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) :=
    (hV.represents_block_comparisons q hq _ _).mp hpref_RQ
  have hagg_eq :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) :=
    le_antisymm hge_RQ hge_QR
  exact (linearPart_difference_zero_iff_value_eq hlin F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q))
    (experimentOfChannel (seqComposeDep P₁ O₂ R))).mpr hagg_eq

/-- If two dependent continuation profiles differ only in one branch, then the
signed posterior-law difference of the compound experiments is the branch
probability times the signed posterior-law difference in that branch. -/
theorem posteriorLawDifference_seqComposeDep_one_branch
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o)) (target : O₁)
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp q
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel (seqComposeDep P₁ O₂ R)) φ =
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target)) φ := by
  classical
  unfold posteriorLawDifferenceExp
  change
    posteriorLawIntegral q (seqComposeDep P₁ O₂ Q) φ -
      posteriorLawIntegral q (seqComposeDep P₁ O₂ R) φ =
      (Channel.outcomeMarginal P₁ q) target *
        (posteriorLawIntegral (branchPosterior P₁ q target) (Q target) φ -
          posteriorLawIntegral (branchPosterior P₁ q target) (R target) φ)
  rw [posteriorLawIntegral_seqComposeDep_eq_sum q P₁ O₂ Q φ,
    posteriorLawIntegral_seqComposeDep_eq_sum q P₁ O₂ R φ]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ x : O₁,
        ((Channel.outcomeMarginal P₁ q) x *
            posteriorLawIntegral (Channel.posterior P₁ q x) (Q x) φ -
          (Channel.outcomeMarginal P₁ q) x *
            posteriorLawIntegral (Channel.posterior P₁ q x) (R x) φ))
        =
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawIntegral (Channel.posterior P₁ q target) (Q target) φ -
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawIntegral (Channel.posterior P₁ q target) (R target) φ := by
        refine Finset.sum_eq_single target ?_ ?_
        · intro o _ho hne
          rw [hsame o hne]
          ring
        · intro hnot
          exact absurd (Finset.mem_univ target) hnot
    _ =
      (Channel.outcomeMarginal P₁ q) target *
        (posteriorLawIntegral (Channel.posterior P₁ q target) (Q target) φ -
          posteriorLawIntegral (Channel.posterior P₁ q target) (R target) φ) := by
        ring
    _ =
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target)) φ := by
        rfl

/-- The signed posterior-law difference between a dependent sequential
experiment and its first-stage experiment is the sum of the branch
probabilities times the continuation posterior-law differences from the
no-information branch baseline. -/
theorem posteriorLawDifference_seqComposeDep_eq_sum_branch_differences
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q : ∀ o, Channel A (O₂ o)) (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp q
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel P₁) φ =
      posteriorLawSignedSum (fun o : O₁ =>
        posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
          (posteriorLawDifferenceExp (branchPosterior P₁ q o)
            (experimentOfChannel (Q o))
            (experimentOfChannel (Channel.uninformativeChannelU A)))) φ := by
  classical
  unfold posteriorLawDifferenceExp posteriorLawSignedSum
    posteriorLawSignedFinsetSum posteriorLawSignedSMul
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegral_seqComposeDep_eq_sum q P₁ O₂ Q φ]
  unfold posteriorLawIntegral
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro o _ho
  dsimp
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior]
  simp [posteriorLawIntegral, branchPosterior]
  ring_nf

/-- Outcome marginal of the public fixed-output sequential composition. -/
theorem outcomeMarginal_seqCompose_apply
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (o : O₁ × O₂) :
    (Channel.outcomeMarginal (P₁ ▷ Q) q) o =
      (Channel.outcomeMarginal P₁ q) o.1 *
        (Channel.outcomeMarginal (Q o.1) (Channel.posterior P₁ q o.1)) o.2 := by
  classical
  obtain ⟨o₁, o₂⟩ := o
  simp only [Channel.outcomeMarginal_apply]
  have step0 :
      ∑ a, q a * (P₁ ▷ Q) a (o₁, o₂) =
        ∑ a, q a * (P₁ a o₁ * Q o₁ a o₂) := by
    refine Finset.sum_congr rfl ?_
    intro a _ha
    rw [seqCompose_apply]
  rw [step0]
  have step1 :
      ∑ a, q a * (P₁ a o₁ * Q o₁ a o₂) =
        ∑ a, (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.posterior P₁ q o₁) a * Q o₁ a o₂) := by
    congr 1
    ext a
    have h := posterior_mul_marginal q P₁ o₁ a
    calc
      q a * (P₁ a o₁ * Q o₁ a o₂)
          = (q a * P₁ a o₁) * Q o₁ a o₂ := by ring
      _ = ((Channel.outcomeMarginal P₁ q) o₁ *
            (Channel.posterior P₁ q o₁) a) * Q o₁ a o₂ := by
            rw [h]
      _ = (Channel.outcomeMarginal P₁ q) o₁ *
            ((Channel.posterior P₁ q o₁) a * Q o₁ a o₂) := by ring
  rw [step1, ← Finset.mul_sum]
  simp only [Channel.outcomeMarginal_apply]

/-- Positive fixed-output sequential outcomes have the posterior of the
selected continuation branch. -/
theorem posterior_seqCompose_of_pos
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (o₁ : O₁) (o₂ : O₂)
    (hpos : (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) > 0) :
    Channel.posterior (P₁ ▷ Q) q (o₁, o₂) =
      Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂ := by
  classical
  have hmarg := outcomeMarginal_seqCompose_apply q P₁ Q (o₁, o₂)
  have hprod :
      (Channel.outcomeMarginal P₁ q) o₁ *
          (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ > 0 := by
    rw [hmarg] at hpos
    exact hpos
  have hm₁_nonneg : 0 ≤ (Channel.outcomeMarginal P₁ q) o₁ :=
    (Channel.outcomeMarginal P₁ q).nonneg o₁
  have hm₂_nonneg :
      0 ≤ (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ :=
    (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)).nonneg o₂
  have hm₁_pos : (Channel.outcomeMarginal P₁ q) o₁ > 0 := by nlinarith
  have hm₂_pos :
      (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ > 0 := by
    nlinarith
  ext a
  let mC := (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂)
  let m₁ := (Channel.outcomeMarginal P₁ q) o₁
  let m₂ := (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂
  let pC := Channel.posterior (P₁ ▷ Q) q (o₁, o₂)
  let p₁ := Channel.posterior P₁ q o₁
  let p₂ := Channel.posterior (Q o₁) p₁ o₂
  have hleft := posterior_mul_marginal q (P₁ ▷ Q) (o₁, o₂) a
  have hfirst := posterior_mul_marginal q P₁ o₁ a
  have hsecond := posterior_mul_marginal p₁ (Q o₁) o₂ a
  have hmarg' : mC = m₁ * m₂ := by
    simpa [mC, m₁, m₂] using hmarg
  have hcalc : mC * pC a = mC * p₂ a := by
    calc
      mC * pC a
          = q a * (P₁ ▷ Q) a (o₁, o₂) := hleft
      _ = q a * (P₁ a o₁ * Q o₁ a o₂) := by rw [seqCompose_apply]
      _ = (q a * P₁ a o₁) * Q o₁ a o₂ := by ring
      _ = (m₁ * p₁ a) * Q o₁ a o₂ := by rw [← hfirst]
      _ = m₁ * (p₁ a * Q o₁ a o₂) := by ring
      _ = m₁ * (m₂ * p₂ a) := by rw [← hsecond]
      _ = (m₁ * m₂) * p₂ a := by ring
      _ = mC * p₂ a := by rw [hmarg']
  exact mul_left_cancel₀ (ne_of_gt hpos) hcalc

/-- Public fixed-output posterior law of a sequential composition is the
first-stage marginal mixture of the branch posterior laws. -/
theorem posteriorLawIntegral_seqCompose_eq_sum
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (φ : Dist A → ℝ) :
    posteriorLawIntegral q (P₁ ▷ Q) φ =
      ∑ o₁,
        (Channel.outcomeMarginal P₁ q) o₁ *
          posteriorLawIntegral (Channel.posterior P₁ q o₁) (Q o₁) φ := by
  classical
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  congr 1
  ext o₁
  rw [Finset.mul_sum]
  congr 1
  ext o₂
  have hmarg := outcomeMarginal_seqCompose_apply q P₁ Q (o₁, o₂)
  by_cases hpos : (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) > 0
  · have hpost := posterior_seqCompose_of_pos q P₁ Q o₁ o₂ hpos
    calc
      (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) *
          φ (Channel.posterior (P₁ ▷ Q) q (o₁, o₂))
          =
        ((Channel.outcomeMarginal P₁ q) o₁ *
          (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂) *
          φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂) := by
            rw [hpost, hmarg]
      _ =
        (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ *
            φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂)) := by
            ring
  · have hzero :
      (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        ((Channel.outcomeMarginal (P₁ ▷ Q) q).nonneg (o₁, o₂))
    have hprod :
        (Channel.outcomeMarginal P₁ q) o₁ *
            (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ = 0 := by
      rw [hmarg] at hzero
      exact hzero
    calc
      (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) *
          φ (Channel.posterior (P₁ ▷ Q) q (o₁, o₂))
          = 0 := by rw [hzero, zero_mul]
      _ =
        (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ *
            φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂)) := by
            calc
              0 = ((Channel.outcomeMarginal P₁ q) o₁ *
                    (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂) *
                    φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂) := by
                    rw [hprod, zero_mul]
              _ =
                  (Channel.outcomeMarginal P₁ q) o₁ *
                    ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ *
                      φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂)) := by
                    ring

/-- Fixed-output version of the sequential posterior-law difference branch
sum identity. -/
theorem posteriorLawDifference_seqCompose_eq_sum_branch_differences
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp q
      (experimentOfChannel (P₁ ▷ Q))
      (experimentOfChannel P₁) φ =
      posteriorLawSignedSum (fun o : O₁ =>
        posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
          (posteriorLawDifferenceExp (branchPosterior P₁ q o)
            (experimentOfChannel (Q o))
            (experimentOfChannel (Channel.uninformativeChannelU A)))) φ := by
  classical
  unfold posteriorLawDifferenceExp posteriorLawSignedSum
    posteriorLawSignedFinsetSum posteriorLawSignedSMul
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegral_seqCompose_eq_sum q P₁ Q φ]
  unfold posteriorLawIntegral
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro o _ho
  dsimp
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior]
  simp [posteriorLawIntegral, branchPosterior]
  ring_nf

/-- Fixed-outcome posterior-law algebra interface for the branch formula.

The dependent sequential algebra is proved internally above.  The public branch
formula is stated for the uniform-outcome `P₁ ▷ Q`, whose outcome type is
`O₁ × O₂`; transporting the dependent sigma-outcome identity to this product
presentation is a pure finite probability/relabeling step, not a behavioral
axiom. -/
structure FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions.{v} : Prop where
  posteriorLawDifference_seqCompose_eq_sum_branch_differences :
    ∀ {A O₁ O₂ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
      (φ : Dist A → ℝ),
      posteriorLawDifferenceExp q
        (experimentOfChannel (P₁ ▷ Q))
        (experimentOfChannel P₁) φ =
        posteriorLawSignedSum (fun o : O₁ =>
          posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A)))) φ

/-- The fixed-output posterior-law algebra is internal finite channel
algebra. -/
theorem fixedOutcomePosteriorAlgebra_of_finite :
    FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions.{u} where
  posteriorLawDifference_seqCompose_eq_sum_branch_differences := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q P₁ Q φ
    exact posteriorLawDifference_seqCompose_eq_sum_branch_differences q P₁ Q φ

/-- Affine expansion of the dependent sequential value difference. -/
theorem branch_formula_affine_expansion_seqComposeDep
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q : ∀ o, Channel A (O₂ o)) :
    hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) -
      hV.V q (experimentOfChannel P₁) =
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel P₁)) :=
  hlin.value_difference F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q))
    (experimentOfChannel P₁)

/-- Affine expansion of the public fixed-output sequential value difference. -/
theorem branch_formula_affine_expansion_seqCompose
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂) :
    hV.V q (experimentOfChannel (P₁ ▷ Q)) -
      hV.V q (experimentOfChannel P₁) =
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (P₁ ▷ Q))
        (experimentOfChannel P₁)) :=
  hlin.value_difference F hV q
    (experimentOfChannel (P₁ ▷ Q))
    (experimentOfChannel P₁)

/-- Linear-part expansion of the dependent sequential branch difference as a
sum of branch continuation differences from the no-information baseline. -/
theorem branch_formula_linearPart_seqComposeDep_sum
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q : ∀ o, Channel A (O₂ o)) :
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel P₁)) =
      ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
  classical
  let branchTerm : O₁ → PosteriorLawSigned A := fun o =>
    posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
      (posteriorLawDifferenceExp (branchPosterior P₁ q o)
        (experimentOfChannel (Q o))
        (experimentOfChannel (Channel.uninformativeChannelU A)))
  have hdiff :
      ∀ φ : Dist A → ℝ,
        posteriorLawDifferenceExp q
          (experimentOfChannel (seqComposeDep P₁ O₂ Q))
          (experimentOfChannel P₁) φ =
        posteriorLawSignedSum branchTerm φ := by
    intro φ
    exact posteriorLawDifference_seqComposeDep_eq_sum_branch_differences
      q P₁ O₂ Q φ
  calc
    hlin.linearPart F hV q
        (posteriorLawDifferenceExp q
          (experimentOfChannel (seqComposeDep P₁ O₂ Q))
          (experimentOfChannel P₁))
        =
      hlin.linearPart F hV q (posteriorLawSignedSum branchTerm) :=
        hlin.linearPart_ext F hV q _ _ hdiff
    _ = ∑ o : O₁, hlin.linearPart F hV q (branchTerm o) := by
        rw [linearPart_sum hlin F hV q branchTerm]
    _ = ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
        apply Finset.sum_congr rfl
        intro o _ho
        simp [branchTerm, hlin.linearPart_smul]

/-- Linear-part expansion of the public fixed-output branch difference as a
sum of branch continuation differences from the no-information baseline. -/
theorem branch_formula_linearPart_seqCompose_sum
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂) :
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (P₁ ▷ Q))
        (experimentOfChannel P₁)) =
      ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
  classical
  let branchTerm : O₁ → PosteriorLawSigned A := fun o =>
    posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
      (posteriorLawDifferenceExp (branchPosterior P₁ q o)
        (experimentOfChannel (Q o))
        (experimentOfChannel (Channel.uninformativeChannelU A)))
  have hdiff :
      ∀ φ : Dist A → ℝ,
        posteriorLawDifferenceExp q
          (experimentOfChannel (P₁ ▷ Q))
          (experimentOfChannel P₁) φ =
        posteriorLawSignedSum branchTerm φ := by
    intro φ
    exact posteriorLawDifference_seqCompose_eq_sum_branch_differences
      q P₁ Q φ
  calc
    hlin.linearPart F hV q
        (posteriorLawDifferenceExp q
          (experimentOfChannel (P₁ ▷ Q))
          (experimentOfChannel P₁))
        =
      hlin.linearPart F hV q (posteriorLawSignedSum branchTerm) :=
        hlin.linearPart_ext F hV q _ _ hdiff
    _ = ∑ o : O₁, hlin.linearPart F hV q (branchTerm o) := by
        rw [linearPart_sum hlin F hV q branchTerm]
    _ = ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
        apply Finset.sum_congr rfl
        intro o _ho
        simp [branchTerm, hlin.linearPart_smul]

/-- Forward and zero sign transport for a common-outcome feasible branch
direction.

This is the compiled A7/posterior-law-realization core of tangent sign
agreement: if a signed branch direction `η` is a positive scalar multiple of a
common-outcome feasible difference at a reached posterior `r`, then positive
and zero branch-linear signs transport to the aggregate prior `q`.  The reverse
positive direction is left to the full tangent sign-agreement interface; it
uses the same argument applied to the swapped direction. -/
theorem branch_tangent_forward_zero_of_commonOutcome_realization
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A O O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype O₁] [DecidableEq O₁]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (η : PosteriorLawSigned A) (t : ℝ) (ht : 0 < t)
    (P R : Channel A O)
    (hη :
      ∀ φ : Dist A → ℝ,
        η φ =
          t * posteriorLawDifferenceExp r
            (experimentOfChannel P) (experimentOfChannel R) φ)
    (P₁ : Channel A O₁) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (hpost : branchPosterior P₁ q target = r) :
    (0 < hlin.linearPart F hV r η →
      0 < hlin.linearPart F hV q η) ∧
    (hlin.linearPart F hV r η = 0 →
      hlin.linearPart F hV q η = 0) := by
  classical
  let O₂ : O₁ → Type u := fun _ => O
  let Q : ∀ o, Channel A (O₂ o) := fun o =>
    if o = target then P else P
  let S : ∀ o, Channel A (O₂ o) := fun o =>
    if o = target then R else P
  let branchDiff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r
      (experimentOfChannel P) (experimentOfChannel R)
  let seqDiff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp q
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel (seqComposeDep P₁ O₂ S))
  have hsame : ∀ o, o ≠ target → Q o = S o := by
    intro o ho
    simp [Q, S, ho]
  have hbranch_full : (branchPosterior P₁ q target).FullSupport := by
    simpa [hpost] using hr
  have hη_eq : η = posteriorLawSignedSMul t branchDiff := by
    funext φ
    exact hη φ
  have hη_lin_r :
      hlin.linearPart F hV r η =
        t * hlin.linearPart F hV r branchDiff := by
    rw [hη_eq, hlin.linearPart_smul]
  have hη_lin_q :
      hlin.linearPart F hV q η =
        t * hlin.linearPart F hV q branchDiff := by
    rw [hη_eq, hlin.linearPart_smul]
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
  have htargetQ :
      Q target = P := by
    simp [Q]
  have htargetS :
      S target = R := by
    simp [S]
  have hbranch_pos_to_q_pos :
      0 < hlin.linearPart F hV r branchDiff →
        0 < hlin.linearPart F hV q branchDiff := by
    intro hbpos
    have hbpos_target :
        0 < hlin.linearPart F hV (branchPosterior P₁ q target)
          (posteriorLawDifferenceExp (branchPosterior P₁ q target)
            (experimentOfChannel (Q target))
            (experimentOfChannel (S target))) := by
      simpa [branchDiff, hpost, htargetQ, htargetS] using hbpos
    have hseq_pos :
        0 < hlin.linearPart F hV q seqDiff := by
      simpa [seqDiff] using
        (branch_feasible_difference_pos_of_branch_pos
          hlin F hax hV q hq P₁ target hpos O₂ Q S hsame
          hbranch_full hbpos_target)
    have hmpos : 0 < (Channel.outcomeMarginal P₁ q) target := hpos
    have hmul :
        0 < (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff := by
      simpa [hseq_lin_q] using hseq_pos
    nlinarith [hmpos, hmul]
  have hbranch_zero_to_q_zero :
      hlin.linearPart F hV r branchDiff = 0 →
        hlin.linearPart F hV q branchDiff = 0 := by
    intro hbzero
    have hbzero_target :
        hlin.linearPart F hV (branchPosterior P₁ q target)
          (posteriorLawDifferenceExp (branchPosterior P₁ q target)
            (experimentOfChannel (Q target))
            (experimentOfChannel (S target))) = 0 := by
      simpa [branchDiff, hpost, htargetQ, htargetS] using hbzero
    have hseq_zero :
        hlin.linearPart F hV q seqDiff = 0 := by
      simpa [seqDiff] using
        (branch_feasible_difference_zero_of_branch_zero
          hlin F hax hV q hq P₁ target O₂ Q S hsame
          hbranch_full hbzero_target)
    have hmne : (Channel.outcomeMarginal P₁ q) target ≠ 0 := ne_of_gt hpos
    have hmul :
        (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff = 0 := by
      simpa [hseq_lin_q] using hseq_zero
    exact (mul_eq_zero.mp hmul).resolve_left hmne
  constructor
  · intro hrη_pos
    have hbpos : 0 < hlin.linearPart F hV r branchDiff := by
      nlinarith [hη_lin_r, ht, hrη_pos]
    have hqpos := hbranch_pos_to_q_pos hbpos
    nlinarith [hη_lin_q, ht, hqpos]
  · intro hrη_zero
    have hbzero : hlin.linearPart F hV r branchDiff = 0 := by
      nlinarith [hη_lin_r, ht, hrη_zero]
    have hqzero := hbranch_zero_to_q_zero hbzero
    nlinarith [hη_lin_q, ht, hqzero]

/-!
## Branch-slice positive affine uniqueness

Once the one-coordinate slice order has been established, the paper applies
finite affine-utility uniqueness to conclude that the aggregate branch slice is
a positive affine transform of the reached-posterior representative.  The
general product-slice uniqueness interfaces currently live downstream in
`External/EntropyReduction.lean`; this branch-specific interface keeps the
branch proof decomposed without introducing an import cycle.
-/

/-- Positive affine form for one branch slice with fixed continuations in all
other branches.

This packages only the affine-uniqueness conclusion for a single branch slice:
for a fixed first-stage experiment, target positive branch, and fixed
background continuations, varying the target continuation changes the aggregate
value by a positive affine transform of the target branch value. -/
structure FiniteBranchSlicePositiveAffineAssumptions.{v} where
  branch_slice_positive_affine :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
structure FiniteBranchSlopeBackgroundIndependenceAssumptions.{v} : Prop where
  slope_background_independent :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
structure FinitePosteriorTangentSpaceSpanningAssumptions.{v} : Prop where
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
structure FiniteAtomicPosteriorTangentSpanningAssumptions.{v} : Prop where
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
structure FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{v} : Prop where
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

/-!
## Atomic tangent-spanning theorem

The corrected atomic tangent-spanning theorem.  Given an atomic signed
posterior law with zero mass, zero barycentre, and positive displayed
positive mass, realize its evaluation as a positive scalar multiple of a
feasible posterior-law difference. -/

namespace AtomicTangentSpanning

variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def positiveBaryCoord
    (ν : AtomicPosteriorSignedLaw A) (a : A) : ℝ := by
  letI : Fintype ν.I := ν.instFintypeI
  exact ∑ i : ν.I, ν.positiveWeight i * ν.point i a

theorem positiveBaryCoord_nonneg
    (ν : AtomicPosteriorSignedLaw A) (a : A) :
    0 ≤ positiveBaryCoord ν a := by
  letI : Fintype ν.I := ν.instFintypeI
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (AtomicPosteriorSignedLaw.positiveWeight_nonneg ν i)
    ((ν.point i).nonneg a)

theorem positiveBaryCoord_sum
    (ν : AtomicPosteriorSignedLaw A) :
    ∑ a : A, positiveBaryCoord ν a = ν.positiveMass := by
  letI : Fintype ν.I := ν.instFintypeI
  simp only [positiveBaryCoord, AtomicPosteriorSignedLaw.positiveMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, (ν.point i).sum_eq_one, mul_one]

noncomputable def smallEpsilon
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) : ℝ :=
  (Finset.univ : Finset A).inf' ⟨Classical.arbitrary A, Finset.mem_univ _⟩
    (fun a => r a / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')))

private theorem smallEpsilon_denom_pos
    (ν : AtomicPosteriorSignedLaw A) :
    (0 : ℝ) < 2 * (1 + ∑ a' : A, positiveBaryCoord ν a') := by
  have : (0 : ℝ) ≤ ∑ a' : A, positiveBaryCoord ν a' :=
    Finset.sum_nonneg (fun a _ => positiveBaryCoord_nonneg ν a)
  linarith

theorem smallEpsilon_pos
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) :
    0 < smallEpsilon r hr ν hV := by
  unfold smallEpsilon
  rw [Finset.lt_inf'_iff]
  intro a _
  exact div_pos (hr a) (smallEpsilon_denom_pos ν)

theorem smallEpsilon_le
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) (a : A) :
    smallEpsilon r hr ν hV ≤
      r a / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by
  unfold smallEpsilon
  exact Finset.inf'_le _ (Finset.mem_univ a)

theorem smallEpsilon_mul_V_lt_one
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) :
    smallEpsilon r hr ν hV * ν.positiveMass < 1 := by
  have hS := positiveBaryCoord_sum ν
  have hSge : 0 ≤ ∑ a : A, positiveBaryCoord ν a :=
    Finset.sum_nonneg (fun a _ => positiveBaryCoord_nonneg ν a)
  have hdenom_pos := smallEpsilon_denom_pos ν
  have hε_le := smallEpsilon_le r hr ν hV (Classical.arbitrary A)
  have hra_le := r.prob_le_one (Classical.arbitrary A)
  have hV_eq : ν.positiveMass = ∑ a' : A, positiveBaryCoord ν a' := hS.symm
  calc smallEpsilon r hr ν hV * ν.positiveMass
      ≤ (r (Classical.arbitrary A) / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a'))) *
          ν.positiveMass := by
        apply mul_le_mul_of_nonneg_right hε_le (le_of_lt hV)
    _ = r (Classical.arbitrary A) * ν.positiveMass /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by ring
    _ ≤ 1 * ν.positiveMass /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hdenom_pos)
        exact mul_le_mul_of_nonneg_right hra_le (le_of_lt hV)
    _ < 1 := by
        rw [one_mul, hV_eq, div_lt_one hdenom_pos]
        linarith

theorem smallEpsilon_mul_S_le_r
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) (a : A) :
    smallEpsilon r hr ν hV * positiveBaryCoord ν a ≤ r a := by
  have hdenom_pos := smallEpsilon_denom_pos ν
  have hε_le := smallEpsilon_le r hr ν hV a
  have hSa_le : positiveBaryCoord ν a ≤ ∑ a' : A, positiveBaryCoord ν a' :=
    Finset.single_le_sum (fun b _ => positiveBaryCoord_nonneg ν b) (Finset.mem_univ a)
  calc smallEpsilon r hr ν hV * positiveBaryCoord ν a
      ≤ (r a / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a'))) *
          positiveBaryCoord ν a := by
        apply mul_le_mul_of_nonneg_right hε_le (positiveBaryCoord_nonneg ν a)
    _ = r a * positiveBaryCoord ν a /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by ring
    _ ≤ r a * (∑ a' : A, positiveBaryCoord ν a') /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hdenom_pos)
        exact mul_le_mul_of_nonneg_left hSa_le (le_of_lt (hr a))
    _ ≤ r a := by
        rw [div_le_iff₀ hdenom_pos]
        have hra_nn := le_of_lt (hr a)
        have hSnn : (0 : ℝ) ≤ ∑ a' : A, positiveBaryCoord ν a' :=
          Finset.sum_nonneg (fun a' _ => positiveBaryCoord_nonneg ν a')
        nlinarith [mul_nonneg hra_nn hSnn]

noncomputable def correctionDist
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) : Dist A := by
  letI : Fintype ν.I := ν.instFintypeI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hdenom_pos : (0 : ℝ) < 1 - ε * V := by linarith
  refine ⟨fun a => (r a - ε * positiveBaryCoord ν a) / (1 - ε * V), ?_, ?_⟩
  · intro a
    apply div_nonneg
    · linarith [smallEpsilon_mul_S_le_r r hr ν hV a]
    · linarith
  · rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hdenom_pos)]
    have hr_sum := r.sum_eq_one
    have hS_sum := positiveBaryCoord_sum ν
    calc ∑ a : A, (r a - ε * positiveBaryCoord ν a)
        = (∑ a : A, r a) - ε * ∑ a : A, positiveBaryCoord ν a := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 1 - ε * V := by rw [hr_sum, hS_sum]

noncomputable def completedPositiveProbLaw
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) : AtomicPosteriorProbLaw A := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hε_pos := smallEpsilon_pos r hr ν hV
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  exact {
    I := Option ν.I
    instFintypeI := inferInstance
    instDecidableEqI := inferInstance
    mass := fun oi => match oi with
      | none => 1 - ε * V
      | some i => ε * ν.positiveWeight i
    point := fun oi => match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i
    mass_nonneg := fun oi => by
      match oi with
      | none => simp; linarith
      | some i =>
        simp
        exact mul_nonneg (le_of_lt hε_pos) (AtomicPosteriorSignedLaw.positiveWeight_nonneg ν i)
    mass_sum := by
      simp only [Fintype.sum_option]
      ring_nf
      have h1 : ∑ i : ν.I, ε * ν.positiveWeight i = ε * V := by
        rw [← Finset.mul_sum]; rfl
      linarith
  }

noncomputable def completedNegativeProbLaw
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hV : 0 < ν.positiveMass) : AtomicPosteriorProbLaw A := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hε_pos := smallEpsilon_pos r hr ν hV
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hVeq := AtomicPosteriorSignedLaw.positiveMass_eq_negativeMass_of_totalMass_zero ν hmass
  exact {
    I := Option ν.I
    instFintypeI := inferInstance
    instDecidableEqI := inferInstance
    mass := fun oi => match oi with
      | none => 1 - ε * V
      | some i => ε * ν.negativeWeight i
    point := fun oi => match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i
    mass_nonneg := fun oi => by
      match oi with
      | none => simp; linarith
      | some i =>
        simp
        exact mul_nonneg (le_of_lt hε_pos) (AtomicPosteriorSignedLaw.negativeWeight_nonneg ν i)
    mass_sum := by
      simp only [Fintype.sum_option]
      ring_nf
      have h1 : ∑ i : ν.I, ε * ν.negativeWeight i = ε * ν.negativeMass := by
        rw [← Finset.mul_sum]; rfl
      rw [← hVeq] at h1
      linarith
  }

theorem completedPositiveProbLaw_barycenter
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) (a : A) :
    (completedPositiveProbLaw r hr ν hV).barycenterCoord a = r a := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hdenom_pos : (0 : ℝ) < 1 - ε * V := by linarith
  show (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * V
      | some i => ε * ν.positiveWeight i) *
    (match oi with
      | none => (correctionDist r hr ν hV : Dist A)
      | some i => ν.point i) a) = r a
  rw [Fintype.sum_option]
  simp only []
  have h_corr_val : (correctionDist r hr ν hV : Dist A) a =
      (r a - ε * positiveBaryCoord ν a) / (1 - ε * V) := rfl
  rw [h_corr_val]
  have h_sum_eq : ∑ i : ν.I, ε * ν.positiveWeight i * (ν.point i) a =
      ε * positiveBaryCoord ν a := by
    unfold positiveBaryCoord
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h_sum_eq]
  field_simp [ne_of_gt hdenom_pos]
  ring

theorem completedNegativeProbLaw_barycenter
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hbary : ∀ a, ν.barycenterCoord a = 0)
    (hV : 0 < ν.positiveMass) (a : A) :
    (completedNegativeProbLaw r hr ν hmass hV).barycenterCoord a = r a := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hdenom_pos : (0 : ℝ) < 1 - ε * V := by linarith
  have hpb :=
    AtomicPosteriorSignedLaw.positive_barycenter_eq_negative_barycenter_of_barycenter_zero
      ν a (hbary a)
  show (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * V
      | some i => ε * ν.negativeWeight i) *
    (match oi with
      | none => (correctionDist r hr ν hV : Dist A)
      | some i => ν.point i) a) = r a
  rw [Fintype.sum_option]
  simp only []
  have hNS_eq : ∑ i : ν.I, ε * ν.negativeWeight i * (ν.point i) a =
      ε * positiveBaryCoord ν a := by
    have : ∑ i : ν.I, ε * ν.negativeWeight i * (ν.point i) a =
        ε * ∑ i : ν.I, ν.negativeWeight i * (ν.point i) a := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, show positiveBaryCoord ν a =
        ∑ i : ν.I, ν.positiveWeight i * (ν.point i) a from rfl, ← hpb]
  rw [hNS_eq]
  have h_corr_val : (correctionDist r hr ν hV : Dist A) a =
      (r a - ε * positiveBaryCoord ν a) / (1 - ε * V) := rfl
  rw [h_corr_val]
  field_simp [ne_of_gt hdenom_pos]
  ring

theorem completedProbLaw_eval_difference
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hbary : ∀ a, ν.barycenterCoord a = 0)
    (hV : 0 < ν.positiveMass) (φ : Dist A → ℝ) :
    (completedPositiveProbLaw r hr ν hV).eval φ -
      (completedNegativeProbLaw r hr ν hmass hV).eval φ =
    smallEpsilon r hr ν hV * ν.eval φ := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  show (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * ν.positiveMass
      | some i => ε * ν.positiveWeight i) *
    φ (match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i)) -
    (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * ν.positiveMass
      | some i => ε * ν.negativeWeight i) *
    φ (match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i)) =
    ε * ∑ i : ν.I, ν.weight i * φ (ν.point i)
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only []
  have h_cancel : (1 - ε * ν.positiveMass) * φ (correctionDist r hr ν hV) -
      (1 - ε * ν.positiveMass) * φ (correctionDist r hr ν hV) = 0 := by ring
  have h_sums : (∑ i : ν.I, ε * ν.positiveWeight i * φ (ν.point i)) -
      (∑ i : ν.I, ε * ν.negativeWeight i * φ (ν.point i)) =
    ε * ∑ i : ν.I, ν.weight i * φ (ν.point i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    have hw := AtomicPosteriorSignedLaw.weight_eq_positiveWeight_sub_negativeWeight ν i
    rw [hw]; ring
  linarith

end AtomicTangentSpanning

theorem atomic_zero_mass_barycenter_as_feasible_difference_of_positiveMass
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hbary : ∀ a, ν.barycenterCoord a = 0)
    (hpos : 0 < ν.positiveMass) :
    ∃ (t : ℝ) (_ : 0 < t) (E E' : FiniteExperimentOn A),
      ∀ φ : Dist A → ℝ,
        ν.eval φ = t * posteriorLawDifferenceExp r E E' φ := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := AtomicTangentSpanning.smallEpsilon r hr ν hpos
  have hε_pos := AtomicTangentSpanning.smallEpsilon_pos r hr ν hpos
  let μ_pos := AtomicTangentSpanning.completedPositiveProbLaw r hr ν hpos
  let μ_neg := AtomicTangentSpanning.completedNegativeProbLaw r hr ν hmass hpos
  have hbary_pos : ∀ a : A, μ_pos.barycenterCoord a = r a :=
    AtomicTangentSpanning.completedPositiveProbLaw_barycenter r hr ν hpos
  have hbary_neg : ∀ a : A, μ_neg.barycenterCoord a = r a :=
    AtomicTangentSpanning.completedNegativeProbLaw_barycenter r hr ν hmass hbary hpos
  let E := μ_pos.experimentOfPosteriorProbLaw r hr hbary_pos
  let E' := μ_neg.experimentOfPosteriorProbLaw r hr hbary_neg
  refine ⟨1 / ε, by positivity, E, E', ?_⟩
  intro φ
  have heval_pos :=
    AtomicPosteriorProbLaw.posteriorLawIntegralExp_experimentOfPosteriorProbLaw
      r hr μ_pos hbary_pos φ
  have heval_neg :=
    AtomicPosteriorProbLaw.posteriorLawIntegralExp_experimentOfPosteriorProbLaw
      r hr μ_neg hbary_neg φ
  have hdiff := AtomicTangentSpanning.completedProbLaw_eval_difference
    r hr ν hmass hbary hpos φ
  have hne : ε ≠ 0 := ne_of_gt hε_pos
  have hgoal : ν.eval φ = 1 / ε * (μ_pos.eval φ - μ_neg.eval φ) := by
    field_simp; linarith
  rw [hgoal]
  simp only [posteriorLawDifferenceExp_apply]
  congr 1
  rw [← heval_pos, ← heval_neg]

theorem finiteAtomicPosteriorTangentSpanning :
    FiniteAtomicPosteriorTangentSpanningAssumptions.{u} where
  atomic_zero_mass_barycenter_as_feasible_difference := by
    intro A _ _ _ r hr ν hmass hbary hne
    have hpos := AtomicPosteriorSignedLaw.positiveMass_pos_of_eval_ne_zero ν hmass hne
    obtain ⟨t, ht, E, E', hreal⟩ :=
      atomic_zero_mass_barycenter_as_feasible_difference_of_positiveMass
        r hr ν hmass hbary hpos
    exact ⟨t, ht, E, E', hreal⟩

/-- Common-outcome realization of tangent directions.

The paper's A7 step compares two continuation channels in the same branch
outcome alphabet.  The older tangent spanning interface realizes a tangent
direction by two finite experiments, whose bundled outcome types may differ.
This interface isolates the padding/realization strengthening needed before
A7 can be applied directly. -/
structure FiniteCommonOutcomeTangentRealizationAssumptions.{v} : Prop where
  tangent_as_common_outcome_difference :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (r : Dist A) (_hr : r.FullSupport) (η : PosteriorLawSigned A),
      PosteriorLawTangent η →
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
      ∃ (t : ℝ), ∃ (_ht : 0 < t), ∃ (O : Type v),
      ∃ (hO : Fintype O), ∃ (hOdec : DecidableEq O),
        letI : Fintype O := hO
        letI : DecidableEq O := hOdec
        ∃ P R : Channel A O,
          ∀ φ : Dist A → ℝ,
            η φ =
              t * posteriorLawDifferenceExp r
                (experimentOfChannel P) (experimentOfChannel R) φ

/-- Full-support branch reachability.

This is the finite-probability step that any full-support posterior `r` can be
reached with positive probability from any full-support prior `q`. -/
structure FiniteFullSupportBranchReachabilityAssumptions.{v} : Prop where
  reaches :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A), q.FullSupport → r.FullSupport →
      ∃ (O₁ : Type v), ∃ (hO₁ : Fintype O₁),
      ∃ (hO₁dec : DecidableEq O₁),
        letI : Fintype O₁ := hO₁
        letI : DecidableEq O₁ := hO₁dec
        ∃ (P₁ : Channel A O₁), ∃ target : O₁,
          BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r

/-- Tangent-space spanning by feasible differences can be upgraded to
common-outcome feasible differences by padding the two bundled outcome types into
a disjoint sum. -/
theorem commonOutcomeTangentRealization_of_tangentSpanning
    (htangent : FinitePosteriorTangentSpaceSpanningAssumptions.{u}) :
    FiniteCommonOutcomeTangentRealizationAssumptions.{u} where
  tangent_as_common_outcome_difference := by
    intro A _ _ _ r hr η htan hηne
    rcases htangent.zero_mass_barycenter_as_feasible_difference
        r hr η htan.1 htan.2 hηne with
      ⟨t, ht, E, E', hη⟩
    classical
    letI : Fintype E.OutcomeType := E.outFintype
    letI : DecidableEq E.OutcomeType := E.outDecEq
    letI : Fintype E'.OutcomeType := E'.outFintype
    letI : DecidableEq E'.OutcomeType := E'.outDecEq
    let O : Type u := E.OutcomeType ⊕ E'.OutcomeType
    refine ⟨t, ht, O, inferInstance, inferInstance, ?_⟩
    refine ⟨outcomePadLeft (Y := E'.OutcomeType) E.P,
      outcomePadRight (O := E.OutcomeType) E'.P, ?_⟩
    intro φ
    have hdiff :
        posteriorLawDifferenceExp r E E' φ =
          posteriorLawDifferenceExp r
            (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
            (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
      simp [posteriorLawDifferenceExp, posteriorLawIntegral_outcomePadLeft,
        posteriorLawIntegral_outcomePadRight, experimentOfChannel,
        FiniteExperimentOn.ofChannel, FiniteExperimentOn.P]
    calc
      η φ = t * posteriorLawDifferenceExp r E E' φ := hη φ
      _ =
          t * posteriorLawDifferenceExp r
            (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
            (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
            rw [hdiff]

/-- Atomic-linear common-outcome tangent realization from atomic-linear spanning.

Given the corrected atomic-linear spanning, every atomic-linear tangent η ≠ 0
can be realized as a positive scalar multiple of a common-outcome posterior-law
difference. -/
theorem commonOutcomeAtomicLinearTangentRealization_of_atomicLinearSpanning
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) (η : PosteriorLawSigned A)
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (htan : PosteriorLawTangent η)
    (hηne : η ≠ ((fun _ => 0) : PosteriorLawSigned A)) :
    ∃ (t : ℝ), ∃ (_ht : 0 < t), ∃ (O : Type u),
    ∃ (hO : Fintype O), ∃ (hOdec : DecidableEq O),
      letI : Fintype O := hO
      letI : DecidableEq O := hOdec
      ∃ P R : Channel A O,
        ∀ φ : Dist A → ℝ,
          η φ =
            t * posteriorLawDifferenceExp r
              (experimentOfChannel P) (experimentOfChannel R) φ := by
  have hmass : hηatomic.witness.totalMass = 0 := by
    have htan1 := htan.1
    rw [← hηatomic.eval_eq] at htan1
    rwa [AtomicPosteriorSignedLaw.eval_const_one] at htan1
  have hbary : ∀ a : A, hηatomic.witness.barycenterCoord a = 0 := by
    intro a
    have htan2 := htan.2 a
    rw [← hηatomic.eval_eq] at htan2
    rwa [AtomicPosteriorSignedLaw.eval_coord] at htan2
  rcases htangent.atomicLinear_zero_mass_barycenter_as_feasible_difference
      r hr η hηatomic hmass hbary hηne with
    ⟨t, ht, E, E', hη⟩
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype E'.OutcomeType := E'.outFintype
  letI : DecidableEq E'.OutcomeType := E'.outDecEq
  let O : Type u := E.OutcomeType ⊕ E'.OutcomeType
  refine ⟨t, ht, O, inferInstance, inferInstance, ?_⟩
  refine ⟨outcomePadLeft (Y := E'.OutcomeType) E.P,
    outcomePadRight (O := E.OutcomeType) E'.P, ?_⟩
  intro φ
  have hdiff :
      posteriorLawDifferenceExp r E E' φ =
        posteriorLawDifferenceExp r
          (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
          (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
    simp [posteriorLawDifferenceExp, posteriorLawIntegral_outcomePadLeft,
      posteriorLawIntegral_outcomePadRight, experimentOfChannel,
      FiniteExperimentOn.ofChannel, FiniteExperimentOn.P]
  calc
    η φ = t * posteriorLawDifferenceExp r E E' φ := hη φ
    _ =
        t * posteriorLawDifferenceExp r
          (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
          (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
          rw [hdiff]

/-- Common-outcome tangent realization is closed under negating the signed
tangent law: swap the two realizing experiments. -/
theorem commonOutcomeTangentRealization_neg
    (hreal : FiniteCommonOutcomeTangentRealizationAssumptions.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) (η : PosteriorLawSigned A)
    (htan : PosteriorLawTangent η)
    (hηne : η ≠ ((fun _ => 0) : PosteriorLawSigned A)) :
    ∃ (t : ℝ), ∃ (_ht : 0 < t), ∃ (O : Type u),
    ∃ (hO : Fintype O), ∃ (hOdec : DecidableEq O),
      letI : Fintype O := hO
      letI : DecidableEq O := hOdec
      ∃ P R : Channel A O,
        ∀ φ : Dist A → ℝ,
          posteriorLawSignedSMul (-1) η φ =
            t * posteriorLawDifferenceExp r
              (experimentOfChannel P) (experimentOfChannel R) φ := by
  rcases hreal.tangent_as_common_outcome_difference r hr η htan hηne with
    ⟨t, ht, O, hO, hOdec, hrealized⟩
  letI : Fintype O := hO
  letI : DecidableEq O := hOdec
  rcases hrealized with ⟨P, R, hη⟩
  refine ⟨t, ht, O, hO, hOdec, R, P, ?_⟩
  intro φ
  calc
    posteriorLawSignedSMul (-1) η φ = -η φ := by
      simp [posteriorLawSignedSMul]
    _ = -(t * posteriorLawDifferenceExp r
            (experimentOfChannel P) (experimentOfChannel R) φ) := by
      rw [hη φ]
    _ = t * posteriorLawDifferenceExp r
            (experimentOfChannel R) (experimentOfChannel P) φ := by
      unfold posteriorLawDifferenceExp
      ring

/-!
### Full-support branch reachability

The finite construction is binary: choose a positive branch mass `ε` dominated
by `q` relative to the target posterior `r`, set
`P(a, target) = ε r(a) / q(a)`, and put the remaining probability on the other
branch.
-/

/-- A narrow finite-order interface: for any two full-support finite
distributions, choose a positive branch mass `ε` small enough that
`ε r(a) ≤ q(a)` for every action. -/
structure FinitePositiveBranchMassDominatedAssumptions.{v} : Prop where
  exists_dominated_mass :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A), q.FullSupport → r.FullSupport →
      ∃ ε : ℝ, 0 < ε ∧ ∀ a : A, ε * r a ≤ q a

/-- A full-support finite distribution has a positive uniform lower bound on
all coordinates. -/
theorem exists_positive_lower_bound_fullSupport {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : A, δ ≤ q a := by
  classical
  let vals : Finset ℝ := Finset.univ.image (fun a : A => q a)
  have hvals_nonempty : vals.Nonempty := by
    rcases (inferInstance : Nonempty A) with ⟨a0⟩
    exact ⟨q a0, by simp [vals]⟩
  let δ : ℝ := vals.min' hvals_nonempty
  refine ⟨δ, ?_, ?_⟩
  · have hmem : δ ∈ vals := Finset.min'_mem vals hvals_nonempty
    rcases Finset.mem_image.mp hmem with ⟨a, _ha, haeq⟩
    rw [← haeq]
    exact hq a
  · intro a
    have hmem : q a ∈ vals := by simp [vals]
    exact Finset.min'_le vals (q a) hmem

/-- Full-support finite distributions have a positive branch mass dominated by
the source prior relative to the target posterior. -/
theorem exists_positive_branch_mass_dominated {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (_hr : r.FullSupport) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : A, ε * r a ≤ q a := by
  rcases exists_positive_lower_bound_fullSupport q hq with ⟨δ, hδ_pos, hδ_le⟩
  refine ⟨δ / 2, by linarith, ?_⟩
  intro a
  have hε_nonneg : 0 ≤ δ / 2 := by linarith
  have hr_le_one : r a ≤ 1 := Dist.prob_le_one r a
  have hmul_le : (δ / 2) * r a ≤ δ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr_le_one hε_nonneg]
  have hhalf_le_delta : δ / 2 ≤ δ := by linarith
  exact le_trans hmul_le (le_trans hhalf_le_delta (hδ_le a))

/-- Full-support source priors have a positive branch mass dominated by any
finite target posterior, including boundary posteriors. -/
theorem exists_positive_branch_mass_dominated_target {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : A, ε * r a ≤ q a := by
  rcases exists_positive_lower_bound_fullSupport q hq with ⟨δ, hδ_pos, hδ_le⟩
  refine ⟨δ / 2, by linarith, ?_⟩
  intro a
  have hε_nonneg : 0 ≤ δ / 2 := by linarith
  have hr_le_one : r a ≤ 1 := Dist.prob_le_one r a
  have hmul_le : (δ / 2) * r a ≤ δ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr_le_one hε_nonneg]
  have hhalf_le_delta : δ / 2 ≤ δ := by linarith
  exact le_trans hmul_le (le_trans hhalf_le_delta (hδ_le a))

/-- The finite dominated-mass interface is internally proved by taking half of
the positive minimum of the source prior's coordinates. -/
theorem positiveBranchMassDominated_of_finite :
    FinitePositiveBranchMassDominatedAssumptions.{u} where
  exists_dominated_mass := by
    intro A _ _ _ q r hq hr
    exact exists_positive_branch_mass_dominated q r hq hr

/-- Binary first-stage channel with target branch posterior `r`, assuming a
positive dominated branch mass has been chosen. -/
noncomputable def binaryReachChannel {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) : Channel A (ULift.{u} Bool) :=
  fun a =>
    { prob := fun b => if b.down then ε * r a / q a else 1 - ε * r a / q a
      nonneg := by
        intro b
        by_cases hb : b.down = true
        · simp [hb]
          exact div_nonneg (mul_nonneg hε_nonneg (r.nonneg a)) (q.nonneg a)
        · have hble : ε * r a / q a ≤ 1 := by
            by_cases hqpos : 0 < q a
            · rw [div_le_iff₀ hqpos]
              simpa using hdom a
            · have hqzero : q a = 0 := le_antisymm (le_of_not_gt hqpos) (q.nonneg a)
              have hmul_nonneg : 0 ≤ ε * r a := mul_nonneg hε_nonneg (r.nonneg a)
              have hmul_zero : ε * r a = 0 := by
                exact le_antisymm (by simpa [hqzero] using hdom a) hmul_nonneg
              simp [hqzero, hmul_zero]
          simp [hb, hble]
      sum_eq_one := by
        have huniv :
            (Finset.univ : Finset (ULift.{u} Bool)) =
              {ULift.up false, ULift.up true} := by
          ext b
          cases b with
          | up b =>
            cases b <;> simp
        rw [huniv]
        simp }

/-- Under a dominated positive branch mass, the binary reachability channel has
target branch marginal `ε`. -/
theorem outcomeMarginal_binaryReachChannel_true {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    (Channel.outcomeMarginal (binaryReachChannel q r ε hε_nonneg hdom) q) (ULift.up true) =
      ε := by
  unfold Channel.outcomeMarginal binaryReachChannel
  simp
  calc
    (∑ a : A, q a * (ε * r a / q a)) =
        ∑ a : A, ε * r a := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hqpos : q a = 0
      · have hmul_nonneg : 0 ≤ ε * r a := mul_nonneg hε_nonneg (r.nonneg a)
        have hmul_zero : ε * r a = 0 :=
          le_antisymm (by simpa [hqpos] using hdom a) hmul_nonneg
        simp [hqpos, hmul_zero]
      · field_simp [hqpos]
    _ = ε * ∑ a : A, r a := by
      simp [Finset.mul_sum]
    _ = ε := by
      rw [r.sum_eq_one]
      ring

/-- The dominated binary channel reaches the target full-support posterior on
the `true` branch. -/
theorem branchPosterior_binaryReachChannel_true {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (ε : ℝ) (hε_pos : 0 < ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    branchPosterior (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q (ULift.up true) = r := by
  ext a
  unfold branchPosterior Channel.posterior
  have hmarg :
      (Channel.outcomeMarginal (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q) (ULift.up true) =
        ε :=
    outcomeMarginal_binaryReachChannel_true q r ε (le_of_lt hε_pos) hdom
  have hmarg_pos :
      (Channel.outcomeMarginal (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q) (ULift.up true) > 0 := by
    rw [hmarg]
    exact hε_pos
  rw [dif_pos hmarg_pos]
  change
    q a * (ε * r a / q a) /
      (Channel.outcomeMarginal (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q) (ULift.up true) =
        r a
  rw [hmarg]
  by_cases hqzero : q a = 0
  · have hmul_nonneg : 0 ≤ ε * r a := mul_nonneg (le_of_lt hε_pos) (r.nonneg a)
    have hmul_zero : ε * r a = 0 :=
      le_antisymm (by simpa [hqzero] using hdom a) hmul_nonneg
    have hra_zero : r a = 0 := by
      nlinarith
    simp [hqzero, hra_zero]
  · field_simp [hqzero, ne_of_gt hε_pos]

/-- A dominated positive branch mass gives the required full-support branch
reachability witness. -/
theorem fullSupportBranchReachability_of_dominated_mass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (ε : ℝ) (hε_pos : 0 < ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    ∃ (O₁ : Type u), ∃ (hO₁ : Fintype O₁),
    ∃ (hO₁dec : DecidableEq O₁),
      letI : Fintype O₁ := hO₁
      letI : DecidableEq O₁ := hO₁dec
      ∃ (P₁ : Channel A O₁), ∃ target : O₁,
        BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r := by
  refine ⟨ULift.{u} Bool, inferInstance, inferInstance,
    binaryReachChannel q r ε (le_of_lt hε_pos) hdom, ULift.up true, ?_, ?_⟩
  · unfold BranchPositive
    rw [outcomeMarginal_binaryReachChannel_true q r ε (le_of_lt hε_pos) hdom]
    exact hε_pos
  · exact branchPosterior_binaryReachChannel_true q r ε hε_pos hdom

/-- A dominated positive branch mass reaches any target posterior from a
full-support source prior.  This is the boundary-capable version of
`fullSupportBranchReachability_of_dominated_mass`; the construction itself never
uses full support of the target. -/
theorem branchReachability_of_dominated_mass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport)
    (ε : ℝ) (hε_pos : 0 < ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    ∃ (O₁ : Type u), ∃ (hO₁ : Fintype O₁),
    ∃ (hO₁dec : DecidableEq O₁),
      letI : Fintype O₁ := hO₁
      letI : DecidableEq O₁ := hO₁dec
      ∃ (P₁ : Channel A O₁), ∃ target : O₁,
        BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r := by
  refine ⟨ULift.{u} Bool, inferInstance, inferInstance,
    binaryReachChannel q r ε (le_of_lt hε_pos) hdom, ULift.up true, ?_, ?_⟩
  · unfold BranchPositive
    rw [outcomeMarginal_binaryReachChannel_true q r ε (le_of_lt hε_pos) hdom]
    exact hε_pos
  · exact branchPosterior_binaryReachChannel_true q r ε hε_pos hdom

/-- Every finite target posterior, full-support or boundary, is reachable with
positive probability from any full-support source prior. -/
theorem branchReachability_of_fullSupport_prior {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) :
    ∃ (O₁ : Type u), ∃ (hO₁ : Fintype O₁),
    ∃ (hO₁dec : DecidableEq O₁),
      letI : Fintype O₁ := hO₁
      letI : DecidableEq O₁ := hO₁dec
      ∃ (P₁ : Channel A O₁), ∃ target : O₁,
        BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r := by
  rcases exists_positive_branch_mass_dominated_target q r hq with
    ⟨ε, hε_pos, hdom⟩
  exact branchReachability_of_dominated_mass q r hq ε hε_pos hdom

/-- The full-support reachability package follows from the finite dominated
positive branch-mass choice interface. -/
theorem fullSupportBranchReachability_of_dominatedMass
    (hmass : FinitePositiveBranchMassDominatedAssumptions.{u}) :
    FiniteFullSupportBranchReachabilityAssumptions.{u} where
  reaches := by
    intro A _ _ _ q r hq hr
    rcases hmass.exists_dominated_mass q r hq hr with ⟨ε, hε_pos, hdom⟩
    exact fullSupportBranchReachability_of_dominated_mass q r hq hr ε hε_pos hdom

/-- Full-support branch reachability is internal: choose a finite dominated
positive branch mass, then use the explicit binary reachability channel. -/
theorem fullSupportBranchReachability_of_finite :
    FiniteFullSupportBranchReachabilityAssumptions.{u} :=
  fullSupportBranchReachability_of_dominatedMass positiveBranchMassDominated_of_finite

/-- Finite linear-functional same-sign scalar interface.

For linear functionals on signed posterior laws, agreement of the positive
half-space and of the zero set forces a positive scalar multiple relation. -/
structure FiniteLinearFunctionalSameSignScalarAssumptions.{v} : Prop where
  same_sign_scalar :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (L₁ L₂ : PosteriorLawSigned A → ℝ),
      (∀ η ζ : PosteriorLawSigned A,
        L₁ (posteriorLawSignedAdd η ζ) = L₁ η + L₁ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₁ (posteriorLawSignedSMul c η) = c * L₁ η) →
      (∀ η ζ : PosteriorLawSigned A,
        L₂ (posteriorLawSignedAdd η ζ) = L₂ η + L₂ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₂ (posteriorLawSignedSMul c η) = c * L₂ η) →
      (∀ η : PosteriorLawSigned A,
        η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
          (0 < L₁ η ↔ 0 < L₂ η) ∧ (L₁ η = 0 ↔ L₂ η = 0)) →
      (∃ η : PosteriorLawSigned A, L₂ η ≠ 0) →
      ∃ β : ℝ, 0 < β ∧ ∀ η : PosteriorLawSigned A, L₁ η = β * L₂ η

/-- Tangent-subspace version of the same-sign scalar theorem.

This is the faithful linear-algebra interface for the branch path argument:
A7 supplies sign agreement only on genuine tangent signed posterior laws, not
on all extensional functionals `PosteriorLawSigned A`. -/
structure FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{v} : Prop where
  same_sign_scalar_on_tangent :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (L₁ L₂ : PosteriorLawSigned A → ℝ),
      (∀ η ζ : PosteriorLawSigned A,
        L₁ (posteriorLawSignedAdd η ζ) = L₁ η + L₁ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₁ (posteriorLawSignedSMul c η) = c * L₁ η) →
      (∀ η ζ : PosteriorLawSigned A,
        L₂ (posteriorLawSignedAdd η ζ) = L₂ η + L₂ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₂ (posteriorLawSignedSMul c η) = c * L₂ η) →
      (∀ η : PosteriorLawSigned A,
        PosteriorLawTangent η →
        η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
          (0 < L₁ η ↔ 0 < L₂ η) ∧ (L₁ η = 0 ↔ L₂ η = 0)) →
      (∃ η : PosteriorLawSigned A, PosteriorLawTangent η ∧ L₂ η ≠ 0) →
      ∃ β : ℝ, 0 < β ∧
        ∀ η : PosteriorLawSigned A, PosteriorLawTangent η → L₁ η = β * L₂ η

/-- Zero scalar multiplication preserves the custom zero signed posterior law. -/
private theorem posteriorLawSignedSMul_zero_zero {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] :
    posteriorLawSignedSMul 0 ((fun _ => 0) : PosteriorLawSigned A) =
      ((fun _ => 0) : PosteriorLawSigned A) := by
  funext φ
  simp [posteriorLawSignedSMul]

/-- A custom-linear functional sends the custom zero signed posterior law to
zero. -/
private theorem posteriorLawLinear_zero_of_smul {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (L : PosteriorLawSigned A → ℝ)
    (hsmul : ∀ c : ℝ, ∀ η : PosteriorLawSigned A,
      L (posteriorLawSignedSMul c η) = c * L η) :
    L ((fun _ => 0) : PosteriorLawSigned A) = 0 := by
  simpa [posteriorLawSignedSMul_zero_zero] using
    hsmul 0 ((fun _ => 0) : PosteriorLawSigned A)

/-- Direct finite-dimensional ratio proof of the tangent same-sign scalar
theorem.

This discharges the linear-algebra part of the branch path argument on the
tangent subspace.  It deliberately uses the project's custom signed-law
addition and scalar multiplication operations rather than introducing a
separate mathlib linear-map wrapper. -/
theorem finiteLinearFunctionalSameSignScalarOnTangent_of_direct :
    FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u} where
  same_sign_scalar_on_tangent := by
    intro A _ _ _ L₁ L₂ hL₁add hL₁smul hL₂add hL₂smul hsign hnonzero
    classical
    let zeroη : PosteriorLawSigned A := (fun _ => 0)
    have hL₁_zero : L₁ zeroη = 0 := by
      simpa [zeroη] using posteriorLawLinear_zero_of_smul L₁ hL₁smul
    have hL₂_zero : L₂ zeroη = 0 := by
      simpa [zeroη] using posteriorLawLinear_zero_of_smul L₂ hL₂smul
    rcases hnonzero with ⟨x0, hx0_tan, hx0_L₂_ne⟩
    let x : PosteriorLawSigned A :=
      if 0 < L₂ x0 then x0 else posteriorLawSignedSMul (-1) x0
    have hx_tan : PosteriorLawTangent x := by
      dsimp [x]
      split_ifs
      · exact hx0_tan
      · exact PosteriorLawTangent_smul (-1) hx0_tan
    have hx_L₂_pos : 0 < L₂ x := by
      dsimp [x]
      split_ifs with hpos
      · exact hpos
      · have hx0_le : L₂ x0 ≤ 0 := le_of_not_gt hpos
        have hx0_lt : L₂ x0 < 0 := lt_of_le_of_ne hx0_le hx0_L₂_ne
        rw [hL₂smul]
        linarith
    have hx_L₂_ne : L₂ x ≠ 0 := ne_of_gt hx_L₂_pos
    have hx_ne : x ≠ zeroη := by
      intro hx_eq
      have : L₂ x = 0 := by
        simpa [hx_eq, zeroη] using hL₂_zero
      exact hx_L₂_ne this
    have hx_L₁_pos : 0 < L₁ x := (hsign x hx_tan hx_ne).1.mpr hx_L₂_pos
    let β : ℝ := L₁ x / L₂ x
    have hβ_pos : 0 < β := div_pos hx_L₁_pos hx_L₂_pos
    refine ⟨β, hβ_pos, ?_⟩
    intro y hy_tan
    let c : ℝ := -(L₂ y / L₂ x)
    let z : PosteriorLawSigned A :=
      posteriorLawSignedAdd y (posteriorLawSignedSMul c x)
    have hz_tan : PosteriorLawTangent z := by
      exact PosteriorLawTangent_add hy_tan (PosteriorLawTangent_smul c hx_tan)
    have hz_L₂_zero : L₂ z = 0 := by
      calc
        L₂ z = L₂ y + L₂ (posteriorLawSignedSMul c x) := by
          simp [z, hL₂add]
        _ = L₂ y + c * L₂ x := by
          rw [hL₂smul]
        _ = 0 := by
          dsimp [c]
          field_simp [hx_L₂_ne]
          ring_nf
    have hz_L₁_zero : L₁ z = 0 := by
      by_cases hz_zero : z = zeroη
      · simpa [hz_zero, zeroη] using hL₁_zero
      · exact (hsign z hz_tan hz_zero).2.mpr hz_L₂_zero
    have hz_L₁_expand : L₁ z = L₁ y + c * L₁ x := by
      calc
        L₁ z = L₁ y + L₁ (posteriorLawSignedSMul c x) := by
          simp [z, hL₁add]
        _ = L₁ y + c * L₁ x := by
          rw [hL₁smul]
    have hsum : L₁ y + c * L₁ x = 0 := by
      simpa [hz_L₁_expand] using hz_L₁_zero
    change L₁ y = β * L₂ y
    dsimp [β, c] at hsum ⊢
    field_simp [hx_L₂_ne] at hsum ⊢
    ring_nf at hsum ⊢
    linarith

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

This is the A7/realization part after tangent-space spanning has reduced the
problem to signed posterior-law directions: on nonzero tangent directions, the
aggregate prior linear part and the reached-posterior linear part have the same
positive half-space and zero set. -/
structure FiniteBranchTangentSignPreservationAssumptions.{v}
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
structure FiniteBranchTangentSignAgreementAssumptions.{v}
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

/-- Faithful A7-aware tangent-domain sign agreement for a fixed
representation.

Unlike the legacy `FiniteBranchTangentSignAgreementAssumptions`, this package
carries `TraceAxioms F` and restricts the assertion to genuine tangent signed
posterior laws. -/
structure BranchTangentSignAgreementOnTangentFor
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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

This is exactly what the one-branch A7 plumbing proves directly.  The reverse
positive direction is the remaining swapped-direction realization step. -/
structure BranchTangentForwardZeroOnTangentFor
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
faithful A7-aware tangent-domain sign agreement package. -/
theorem branchTangentSignAgreementOnTangentFor_of_realization_and_reachability
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hreal : FiniteCommonOutcomeTangentRealizationAssumptions.{u})
    (hreach : FiniteFullSupportBranchReachabilityAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchTangentSignAgreementOnTangentFor F hax hV hlin :=
  branchTangentSignAgreementOnTangentFor_of_realization_and_reachability hlin
    (commonOutcomeTangentRealization_of_tangentSpanning htangent)
    fullSupportBranchReachability_of_finite F hax hV

/-- Nonzero branch-linear-functional witness for nondegenerate full-support
posterior values. -/
structure FiniteBranchLinearPartNonzeroAssumptions.{v}
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  branch_linear_nonzero :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      ∃ η : PosteriorLawSigned A, hlin.linearPart F hV r η ≠ 0

/-- A1-aware nonzero branch-linear-functional witness.

This is the faithful version of the nonzero witness proved in this stage.  The
legacy `FiniteBranchLinearPartNonzeroAssumptions` above omits `TraceAxioms F`;
without some nontriviality hypothesis on `F`, a constant value representation
and zero linear part would satisfy the representation/linearity interfaces but
make the nonzero conclusion false. -/
structure FiniteBranchLinearPartNonzeroFromA1Assumptions.{v}
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  branch_linear_nonzero_of_axioms :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
supplied from A1 by `branch_linear_part_nonzero_of_A1`. -/
structure BranchTangentSignPreservationFor
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
structure BranchPathScalarStructure.{v}
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
tangent directions.  This is the faithful object produced by the corrected A7
tangent-sign route; the broader `BranchPathScalarStructure` asserts the scalar
relation on all extensional signed laws. -/
structure BranchPathTangentScalarStructure.{v}
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
functional comes from A1 through `branch_linear_part_nonzero_of_A1`. -/
theorem branch_linear_scalar_exists_of_A1_tangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
A1's nonzero branch-linear witness, and the finite same-sign scalar theorem. -/
noncomputable def branchPathScalarStructure_of_A1_tangentSign
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (hsign : FiniteBranchTangentSignAgreementAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
structure FiniteBranchFullSupportSlopeIdentityAssumptions.{v}
    (hlin : FiniteAffineLinearPartAssumptions.{v}) : Prop where
  branch_slice_slope_eq_probability_mul_scalar :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
structure FiniteBranchFullSupportSlopeIdentityWithValueGapAssumptions.{v}
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
structure BranchFullSupportPathIndependenceStructure.{v}
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
    ∀ (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
A1 nontriviality to full-support path independence.  It bypasses the old
hax-free `FiniteBranchTangentSignPreservationAssumptions`. -/
noncomputable def branchFullSupportPathIndependence_of_A1_scalar
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hsignscalar : FiniteLinearFunctionalSameSignScalarAssumptions.{u})
    (hsign : FiniteBranchTangentSignAgreementAssumptions.{u} hlin)
    (hslope : FiniteBranchFullSupportSlopeIdentityAssumptions.{u} hlin)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchFullSupportPathIndependenceStructure F hV :=
  branchFullSupportPathIndependence_of_scalar hlin hslope F hax hV
    (branchPathScalarStructure_of_A1_tangentSign
      hlin hsignscalar hsign F hax hV)

/-- Path-independent branch slope coefficient interface.

This isolates the paper claim that the one-branch affine slope divided by the
branch probability depends only on the prior and reached posterior, not on the
first-stage experiment or fixed continuations. -/
structure FiniteBranchPathIndependenceAssumptions.{v} where
  branchPathCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  branchPathCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      0 < branchPathCoeff q r
  branch_slice_slope_eq_probability_mul_coeff :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
structure FiniteBranchBoundaryFaceScaleAssumptions.{v} where
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
structure FiniteBranchBoundaryValueTransportAssumptions.{v} where
  boundary_value_transport :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBranchBoundaryValueTransportFor F hax hV where
  boundary_value_transport := hvalue.boundary_value_transport F hax hV

/-- Explicit normalization that representatives on a boundary face are chosen
coherently with the intrinsic positive-support representative.

This is a renamed/classified version of boundary value transport.  It is not a
posterior-law theorem: the equality crosses from the ambient boundary prior to
the intrinsic support-face prior. -/
structure FiniteSupportFaceRepresentativeTransportAssumptions.{v} where
  support_face_value_transport :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
structure FiniteBoundaryCoefficientScaleNormalizationAssumptions.{v} where
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
structure FiniteBranchBoundaryCoefficientTransportAssumptions.{v}
    (hlin : FiniteAffineLinearPartAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  boundary_linear_part_scalar :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
structure FiniteBoundaryLinearPartTransportAssumptions.{v}
    (hlin : FiniteAffineLinearPartAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  boundary_linear_part_scalar :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
structure FiniteSupportFaceMarginalValueTransportAssumptions.{v}
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  support_face_marginalValue_scalar :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
structure FiniteBranchFormulaBoundarySummandAssumptions.{v}
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
support-face value transport requires `TraceAxioms F`, so the older hax-free
`FiniteBranchFormulaBoundarySummandAssumptions` is too strong as a derived
target. -/
structure FiniteBranchFormulaBoundarySummandFor
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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

/-- If two finite channels are mutual outcome postprocessings, then A4 plus
A1/A3 allows replacing one by the other in any pairwise comparison. -/
theorem rel_of_mutual_postprocess_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    exact hax.a4 P T q
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist q) (inrDist q) := by
    rw [hS]
    exact hax.a4 P' S q
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r) := by
    rw [hT]
    exact hax.a4 P T r
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist r) (inrDist r) := by
    rw [hS]
    exact hax.a4 P' S r
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
Both directions use only A1/A3/A4/A5 through relabeling, outcome
postprocessing, and support restriction. -/
theorem boundary_block_rel_iff_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
      A7_strict_one_branch_of_strict F hax O₂ q P₁ Q S target hpos hsame
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
      A7_weak_one_branch_of_rel F hax O₂ q P₁ Q S target hsame htarget_QR
    have hagg_RQ :
        F.rel (blockChannel (seqComposeDep P₁ O₂ S) (seqComposeDep P₁ O₂ Q))
          (inlDist q) (inrDist q) :=
      A7_weak_one_branch_of_rel F hax O₂ q P₁ S Q target
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

/-- A1/A7 plus atomic tangent spanning construct the boundary support-face
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
to exist from A1/A7 and atomic tangent spanning. -/
noncomputable def boundaryCoefficientScaleNormalization_of_A1_atomicLinearTangentSpanning
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
structure FiniteBranchSingletonScaleNormalizationAssumptions.{v} where
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
structure FiniteBranchAggregationFormulaAssumptions.{v}
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

/-- Positivity for the representation-level assembled branch coefficient. -/
theorem branchCoeffFromRepParts_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    (hpath : BranchFullSupportPathIndependenceStructure F hV)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hpath : BranchFullSupportPathIndependenceStructure F hV)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u}) where
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hpath : BranchFullSupportPathIndependenceStructure F hV)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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

/-- Positivity for the faithful tangent-scalar assembled branch coefficient. -/
theorem branchCoeffFromTangentRepParts_pos
    {F : PrefFamily.{u}} {hV : PosteriorValueRepresentation F}
    {hlin : FiniteAffineLinearPartAssumptions.{u}}
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q r : Dist A) (m : ℝ)
    (hr_singleton_support :
      ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a)
    (Q : Channel A O) :
    m * branchCoeffFromTangentRepParts hpath hboundary hsingle q r *
        hV.V r (experimentOfChannel Q) = 0 := by
  rw [hsingle.singleton_branch_value_zero F hV r hr_singleton_support Q]
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

/-- The singleton branch package is canonically supplied by the posterior-law
integral representation.

The coefficient is fixed to `1`; the value-zero clause is no longer a boundary
normalization.  It follows by transporting the value to the positive support face
using the marginal-value support-face coherence in `hint`; on a singleton support
face every posterior value is zero by the full-support subsingleton theorem. -/
noncomputable def branchSingletonScaleNormalization_of_integralRepresentation
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u}) :
    FiniteBranchSingletonScaleNormalizationAssumptions.{u} where
  singletonCoeff := fun _ _ => 1
  singletonCoeff_pos := by
    intro A _ _ _ q r _hq _hr_singleton
    exact zero_lt_one
  singleton_branch_value_zero := by
    intro F hV A O _ _ _ _ _ r hr_singleton P
    classical
    haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
    haveI : Subsingleton (supportSubtype r) :=
      supportSubtype_subsingleton_of_singleton_support r hr_singleton
    have hsupport :
        hV.V r (experimentOfChannel P) =
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport P r)) := by
      rw [hint.value_eq_integral F hV r (experimentOfChannel P)]
      rw [hint.value_eq_integral F hV r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P r))]
      rw [posteriorLawIntegralExp_experimentOfChannel,
        posteriorLawIntegralExp_experimentOfChannel]
      rw [posteriorLawIntegral_restrictToSupport P r]
      unfold posteriorLawIntegral
      apply Finset.sum_congr rfl
      intro o _ho
      dsimp
      rw [hint.marginalValue_support_face F hV r
        (Channel.posterior (Channel.restrictToSupport P r) r.restrictToSupport o)]
    rw [hsupport]
    exact branchValue_channel_eq_zero_of_subsingleton F hV
      r.restrictToSupport (Dist.restrictToSupport_fullSupport r)
      (Channel.restrictToSupport P r)

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
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u}) : Prop where
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u}) where
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hboundarySummand :
      FiniteBranchFormulaBoundarySummandAssumptions hlin hboundary) :
    FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle :=
  branchAggregationFormulaTangentFor_of_summands
    F hax hV hlin hpath hboundary hsingle
    (branchFormulaSummands_of_boundary
      F hax hV hlin hpath hboundary hsingle hboundarySummand)

/-- Formula bridge reassembly from the hax-aware boundary summand package. -/
theorem branchAggregationFormulaTangentFor_of_boundarySummandsFor
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hpath :
      BranchPathTangentScalarStructure F hV
        (finiteAffineLinearPartAssumptions_of_integralRepresentation hint))
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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

/-!
## Branch Aggregation External Assumption

The branch aggregation theorem states that given:
1. Axiom A7 (branchwise continuation monotonicity)
2. A posterior value representation V from Herstein-Milnor

There exist positive branch coefficients β(q, r) such that the value of a
sequential experiment decomposes into first-stage value plus expected scaled
continuation values.

Paper proof sketch:
1. Fix first-stage channel P₁ with branch structure (m(o), r_o)
2. For a positive-probability branch o̅, define g(ν) = F_q(T_H(ν)) where T_H
   embeds branch law ν into the full posterior law
3. A7 implies g and F_r represent the same weak order on M_r
4. Herstein-Milnor uniqueness gives g = αF_r + γ with α > 0
5. Path-independence argument shows α/m depends only on (q, r), not on P₁
6. Define β(q, r) := α/m to get the aggregation formula
-/

/--
**Finite Branch Aggregation Assumptions**

External assumption that Axiom A7 (branchwise continuation monotonicity)
combined with a posterior value representation yields a branch aggregation
structure with positive coefficients.

Paper: Lemma branchagg (lines 1830-2068).

**Key mathematical content:**
- From A7 + posterior value representation, derive positive β(q, r)
- β(q, r) depends only on prior q and reached posterior r, not on the
  specific first-stage channel
- The value decomposes as: V_q(P₁▷{Q}) = V_q(P₁) + Σ m(o) β(q,r_o) V_{r_o}(Q^o)

We state this as an external assumption because the proof involves:
- Tangent-space arguments on the space of posterior laws
- Path-independence via affine-hull decomposition
- Case analysis for boundary/degenerate posteriors
-/
structure FiniteBranchAggregationAssumptions.{v} where
  /-- Given A7 and a posterior value representation, construct a branch
      aggregation structure. This is the main theorem of Lemma branchagg.

      Note: This returns a data-carrying structure (BranchAggregationStructure),
      so FiniteBranchAggregationAssumptions is Type, not Prop. -/
  of_A7 :
    ∀ (F : PrefFamily.{v}),
      A7_BranchwiseContinuationMonotonicity F →
      PosteriorValueRepresentation F →
      BranchAggregationStructure F

/-!
## Bridge Theorems

These theorems show how to use the branch aggregation assumption in the
sufficiency spine.
-/

/--
**Branch Aggregation from A7 Assumption**

Given the external branch aggregation assumption, A7, and a posterior value
representation, derive a branch aggregation structure.
-/
noncomputable def branchAggregation_of_assumption
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u})
    (hA7 : A7_BranchwiseContinuationMonotonicity F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationStructure F :=
  hbranch.of_A7 F hA7 hV

/--
**Branch Aggregation from TraceAxioms**

Given the external branch aggregation assumption and full TraceAxioms,
derive a branch aggregation structure.
-/
noncomputable def branchAggregation_of_traceAxioms
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationStructure F :=
  hbranch.of_A7 F hax.a7 hV

/--
**Branch Aggregation from All External Assumptions**

Given all three external assumptions (Blackwell, Herstein-Milnor, Branch Aggregation)
and TraceAxioms, derive a branch aggregation structure.

This composes the first three sufficiency bridges:
1. TraceAxioms → PosteriorLawSufficiency (via Blackwell)
2. PosteriorLawSufficiency → PosteriorValueRepresentation (via Herstein-Milnor)
3. PosteriorValueRepresentation → BranchAggregationStructure (via Branch Aggregation)

Paper: Lemmas blockcoh--blackwell + postsep + branchagg (lines 810-2068).
-/
noncomputable def branchAggregation_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F) :
    BranchAggregationStructure F :=
  let hpls : PosteriorLawSufficiency F := from_axioms_to_posterior_of_blackwell F hblackwell hax
  let hV : PosteriorValueRepresentation F := posteriorValueRep_of_HersteinMilnor F hhm hpls
  hbranch.of_A7 F hax.a7 hV

/-!
## Spine Integration Helper

Shows how to fill the `value_rep_to_branch` field of `SufficiencySpineAssumptions`.
-/

/--
**Value Rep to Branch Bridge**

Given A7 and the branch aggregation external assumption, provides the bridge
from PosteriorValueRepresentation to BranchAggregationStructure.

This can be used to fill the `value_rep_to_branch` field when constructing
`SufficiencySpineAssumptions`.
-/
noncomputable def value_rep_to_branch_of_assumption
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u})
    (hA7 : A7_BranchwiseContinuationMonotonicity F) :
    PosteriorValueRepresentation F → BranchAggregationStructure F :=
  fun hV => hbranch.of_A7 F hA7 hV

end TraceableAgency
