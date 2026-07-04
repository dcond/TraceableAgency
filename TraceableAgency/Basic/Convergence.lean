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
