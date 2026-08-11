/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Proof.Spine
import TraceableAgency.PureTrace.Support.Blackwell
import TraceableAgency.PureTrace.Support.Relabeling
import TraceableAgency.PureTrace.Support.SupportRestriction

namespace TraceableAgency

universe u v

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
  push Not at h_not_pos
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

end TraceableAgency
