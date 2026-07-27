/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Channel

/-!
# Convergence for Distributions and Channels

Sequential convergence definitions for finite-dimensional distributions and channels.
Used in Axiom A2 (Continuity).

## Key types

- `FiniteExperimentOn A` bundles (O, P : Channel A O) where O is finite
- `posteriorLawIntegralExp` integrates φ : Dist A → ℝ against the posterior law
- `PosteriorLawConvergesAtExp` is genuine weak convergence: convergence for all Continuous φ
-/

set_option linter.style.header false

namespace TraceableAgency

open Filter Topology

variable {A : Type*} [Fintype A]

/-- Pointwise convergence of distributions: qₙ → q iff qₙ(a) → q(a) for all a. -/
def DistConverges (qₙ : ℕ → Dist A) (q : Dist A) : Prop :=
  ∀ a, Tendsto (fun n => qₙ n a) atTop (𝓝 (q a))

/-!
## Finite experiments with varying outcome alphabets

For A2, the sequence of channels (Pₙ) may have different outcome types Oₙ.
We bundle (O, P) into a structure that hides O existentially.
-/

universe u

/-- A finite experiment on action set A bundles a finite outcome type with a channel.
    This allows sequences of experiments with varying outcome alphabets. -/
structure FiniteExperimentOn (A : Type u) [Fintype A] where
  OutcomeType : Type u
  outFintype : Fintype OutcomeType
  outDecEq : DecidableEq OutcomeType
  channel : Channel A OutcomeType

namespace FiniteExperimentOn

variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Shorthand for the channel. -/
abbrev P (E : FiniteExperimentOn A) : @Channel A E.OutcomeType E.outFintype := E.channel

/-- Package a channel with known outcome type into an experiment. -/
def ofChannel {Out : Type u} [Fintype Out] [DecidableEq Out]
    (P : Channel A Out) : FiniteExperimentOn A :=
  { OutcomeType := Out
    outFintype := inferInstance
    outDecEq := inferInstance
    channel := P }

/-- The outcome marginal m(o) = Σ_a q(a) P(o|a) for an experiment. -/
noncomputable def outcomeMarginal (E : FiniteExperimentOn A) (q : Dist A) :
    @Dist E.OutcomeType E.outFintype :=
  @Channel.outcomeMarginal A E.OutcomeType _ E.outFintype E.P q

/-- The posterior r_o = q(·) P(o|·) / m(o) for an experiment. -/
noncomputable def posterior (E : FiniteExperimentOn A) (q : Dist A)
    (o : E.OutcomeType) : Dist A :=
  @Channel.posterior A E.OutcomeType _ E.outFintype E.P q _ _ o

end FiniteExperimentOn

/-!
## Posterior law integration for experiments
-/

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- The posterior-law integral for an experiment:
    ∫ φ(r) dμ_{q,E}(r) = Σ_o m(o) * φ(r_o). -/
noncomputable def posteriorLawIntegralExp (q : Dist A)
    (E : FiniteExperimentOn A) (φ : Dist A → ℝ) : ℝ :=
  @Finset.sum E.OutcomeType ℝ _ (@Finset.univ E.OutcomeType E.outFintype)
    (fun o => (E.outcomeMarginal q) o * φ (E.posterior q o))

/-- Weak convergence of posterior laws for a sequence of experiments with varying outcome types.
    μ_{q,Eₙ} ⇒ μ_{q,E} iff ∫φ dμ_{q,Eₙ} → ∫φ dμ_{q,E} for all CONTINUOUS φ : Dist A → ℝ.

    This is genuine weak convergence on the finite-dimensional simplex Dist A.
    The topology on Dist A is induced by the coordinate embedding into A → ℝ. -/
def PosteriorLawConvergesAtExp (q : Dist A)
    (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A) : Prop :=
  ∀ φ : Dist A → ℝ, Continuous φ →
    Tendsto (fun n => posteriorLawIntegralExp q (Eₙ n) φ) atTop
            (𝓝 (posteriorLawIntegralExp q E φ))

/-- Two experiments induce the same posterior law at q iff they give the same
    posterior-law integral for all continuous test functions φ.
    This is the key equivalence relation for posterior-law sufficiency. -/
def SamePosteriorLawExp (q : Dist A) (E E' : FiniteExperimentOn A) : Prop :=
  ∀ φ : Dist A → ℝ, Continuous φ →
    posteriorLawIntegralExp q E φ = posteriorLawIntegralExp q E' φ

/-!
## Finite posterior-law extensionality

A finite experiment induces a finitely supported posterior law. Consequently,
equality against continuous test functions already gives equality against an
arbitrary test function: interpolate that function continuously on the finite
union of the two posterior supports.

The construction below is explicit. For a finite set `s` of beliefs, it uses
the multivariate Lagrange basis built from the squared coordinate distance
`∑ a, (x a - y a)^2`.
-/

/-- Squared Euclidean coordinate distance between two finite distributions. -/
noncomputable def posteriorSquaredDistance
    (x y : Dist A) : ℝ :=
  ∑ a : A, (x a - y a) ^ 2

@[simp]
theorem posteriorSquaredDistance_self
    (x : Dist A) :
    posteriorSquaredDistance x x = 0 := by
  simp [posteriorSquaredDistance]

theorem posteriorSquaredDistance_ne_zero
    {x y : Dist A} (hxy : x ≠ y) :
    posteriorSquaredDistance x y ≠ 0 := by
  intro hzero
  have hall :
      ∀ a : A, (x a - y a) ^ 2 = 0 := by
    intro a
    have hfun :=
      (Fintype.sum_eq_zero_iff_of_nonneg
        (fun a => sq_nonneg (x a - y a))).mp hzero
    exact congrFun hfun a
  apply hxy
  ext a
  have ha := hall a
  nlinarith [sq_nonneg (x a - y a)]

theorem continuous_posteriorSquaredDistance_right
    (z : Dist A) :
    Continuous (fun y : Dist A => posteriorSquaredDistance y z) := by
  unfold posteriorSquaredDistance
  apply continuous_finsetSum
  intro a _ha
  exact ((Dist.continuous_prob_apply a).sub continuous_const).pow 2

/-- Lagrange basis function attached to `x` in a finite set of beliefs. -/
noncomputable def finitePosteriorInterpolationBasis
    (s : Finset (Dist A)) (x y : Dist A) : ℝ := by
  classical
  exact
    (∏ z ∈ s.erase x, posteriorSquaredDistance y z) /
      (∏ z ∈ s.erase x, posteriorSquaredDistance x z)

@[simp]
theorem finitePosteriorInterpolationBasis_self
    (s : Finset (Dist A)) (x : Dist A) :
    finitePosteriorInterpolationBasis s x x = 1 := by
  classical
  unfold finitePosteriorInterpolationBasis
  apply div_self
  rw [Finset.prod_ne_zero_iff]
  intro z hz
  exact posteriorSquaredDistance_ne_zero
    (Finset.ne_of_mem_erase hz).symm

theorem finitePosteriorInterpolationBasis_eq_zero
    {s : Finset (Dist A)} {x y : Dist A}
    (hy : y ∈ s) (hyx : y ≠ x) :
    finitePosteriorInterpolationBasis s x y = 0 := by
  classical
  unfold finitePosteriorInterpolationBasis
  rw [show (∏ z ∈ s.erase x, posteriorSquaredDistance y z) = 0 by
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hyx, hy⟩)
      (posteriorSquaredDistance_self y)]
  exact zero_div _

theorem continuous_finitePosteriorInterpolationBasis
    (s : Finset (Dist A)) (x : Dist A) :
    Continuous (finitePosteriorInterpolationBasis s x) := by
  classical
  unfold finitePosteriorInterpolationBasis
  apply Continuous.div_const
  apply continuous_finsetProd
  intro z _hz
  exact continuous_posteriorSquaredDistance_right z

/-- Continuous extension of arbitrary prescribed values on a finite set of
beliefs. -/
noncomputable def finitePosteriorContinuousInterpolation
    (s : Finset (Dist A)) (φ : Dist A → ℝ) (y : Dist A) : ℝ := by
  classical
  exact
    ∑ x ∈ s, φ x * finitePosteriorInterpolationBasis s x y

theorem continuous_finitePosteriorContinuousInterpolation
    (s : Finset (Dist A)) (φ : Dist A → ℝ) :
    Continuous (finitePosteriorContinuousInterpolation s φ) := by
  classical
  unfold finitePosteriorContinuousInterpolation
  apply continuous_finsetSum
  intro x _hx
  exact continuous_const.mul
    (continuous_finitePosteriorInterpolationBasis s x)

theorem finitePosteriorContinuousInterpolation_eq
    (s : Finset (Dist A)) (φ : Dist A → ℝ)
    {y : Dist A} (hy : y ∈ s) :
    finitePosteriorContinuousInterpolation s φ y = φ y := by
  classical
  unfold finitePosteriorContinuousInterpolation
  rw [Finset.sum_eq_single y]
  · rw [finitePosteriorInterpolationBasis_self, mul_one]
  · intro x _hx hxy
    rw [finitePosteriorInterpolationBasis_eq_zero hy hxy.symm, mul_zero]
  · exact fun h => (h hy).elim

/-- Finite posterior laws are determined by their integrals against
continuous tests.

This is proved in Lean by continuous interpolation on the finite union of the
two posterior supports; it is not an external assumption. -/
theorem samePosteriorLawExp_all_test_functions
    (q : Dist A) (E E' : FiniteExperimentOn A)
    (hsame : SamePosteriorLawExp q E E')
    (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q E φ =
      posteriorLawIntegralExp q E' φ := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype E'.OutcomeType := E'.outFintype
  letI : DecidableEq E'.OutcomeType := E'.outDecEq
  let sE : Finset (Dist A) :=
    Finset.univ.image (E.posterior q)
  let sE' : Finset (Dist A) :=
    Finset.univ.image (E'.posterior q)
  let s := sE ∪ sE'
  let ψ := finitePosteriorContinuousInterpolation s φ
  have hψ_cont : Continuous ψ :=
    continuous_finitePosteriorContinuousInterpolation s φ
  have hsameψ := hsame ψ hψ_cont
  calc
    posteriorLawIntegralExp q E φ =
        posteriorLawIntegralExp q E ψ := by
      unfold posteriorLawIntegralExp
      apply Finset.sum_congr rfl
      intro o _ho
      congr 1
      change φ (E.posterior q o) =
        finitePosteriorContinuousInterpolation s φ (E.posterior q o)
      exact
        (finitePosteriorContinuousInterpolation_eq s φ
          (Finset.mem_union_left sE'
            (Finset.mem_image.mpr
              ⟨o, Finset.mem_univ o, rfl⟩))).symm
    _ = posteriorLawIntegralExp q E' ψ := hsameψ
    _ = posteriorLawIntegralExp q E' φ := by
      unfold posteriorLawIntegralExp
      apply Finset.sum_congr rfl
      intro o _ho
      congr 1
      change finitePosteriorContinuousInterpolation s φ
          (E'.posterior q o) =
        φ (E'.posterior q o)
      exact
        finitePosteriorContinuousInterpolation_eq s φ
          (Finset.mem_union_right sE
            (Finset.mem_image.mpr
              ⟨o, Finset.mem_univ o, rfl⟩))

/-!
## Legacy fixed-outcome-type convergence (for convenience)

When all channels share the same outcome type, we can use the simpler definition.
-/

variable {Out : Type*} [Fintype Out] [DecidableEq Out]

/-- Pointwise convergence of channels: Pₙ → P iff Pₙ(a)(o) → P(a)(o) for all a, o. -/
def ChannelConverges (Pₙ : ℕ → Channel A Out) (P : Channel A Out) : Prop :=
  ∀ a o, Tendsto (fun n => Pₙ n a o) atTop (𝓝 (P a o))

/-- The posterior-law integral: ∫ φ(r) dμ_{q,P}(r) = Σ_o m(o) * φ(r_o).
    This is the expected value of φ under the posterior law induced by (q, P). -/
noncomputable def posteriorLawIntegral (q : Dist A) (P : Channel A Out)
    (φ : Dist A → ℝ) : ℝ :=
  ∑ o, (Channel.outcomeMarginal P q) o * φ (Channel.posterior P q o)

/-- Weak convergence of posterior laws at a fixed prior q (fixed outcome type version).
    μ_{q,Pₙ} ⇒ μ_{q,P} iff ∫φ dμ_{q,Pₙ} → ∫φ dμ_{q,P} for all continuous φ. -/
def PosteriorLawConvergesAt (q : Dist A) (Pₙ : ℕ → Channel A Out)
    (P : Channel A Out) : Prop :=
  ∀ φ : Dist A → ℝ, Continuous φ →
    Tendsto (fun n => posteriorLawIntegral q (Pₙ n) φ) atTop
            (𝓝 (posteriorLawIntegral q P φ))

end TraceableAgency
