/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Channel

/-!
# Sequential Composition of Channels

Two-stage composition P₁ ▷ {Q^o} where:
- P₁ : A → Δ(O₁) is the first-stage channel
- For each first-stage outcome o ∈ O₁, Q^o : A → Δ(Y^o) is a continuation channel
  with potentially branch-dependent outcome type Y^o

The combined channel produces outcomes in Σ o, Y o (dependent sum).
-/

set_option linter.style.header false

namespace TraceableAgency

universe u v

variable {A O₁ : Type u}
variable [Fintype A] [Fintype O₁]

/-!
## Uniform Continuation Outcome Type

For cases where all continuation channels share the same outcome type.
-/

variable {O₂ : Type u} [Fintype O₂]

/-- Two-stage composition with uniform continuation outcome type.
    (P₁ ▷ Q)(o₁, o₂ | a) = P₁(o₁|a) * Q^{o₁}(o₂|a)

    Paper notation: P₁ ▷ {Q^o}_{o ∈ O₁} -/
noncomputable def seqCompose (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂) :
    Channel A (O₁ × O₂) :=
  fun a =>
    { prob := fun ⟨o₁, o₂⟩ => P₁ a o₁ * Q o₁ a o₂
      nonneg := fun ⟨o₁, o₂⟩ => mul_nonneg ((P₁ a).nonneg o₁) ((Q o₁ a).nonneg o₂)
      sum_eq_one := by
        simp only [Fintype.sum_prod_type, ← Finset.mul_sum]
        have h : ∀ o₁, ∑ o₂, Q o₁ a o₂ = 1 := fun o₁ => (Q o₁ a).sum_eq_one
        simp_rw [h, mul_one]
        exact (P₁ a).sum_eq_one }

notation:65 P₁ " ▷ " Q => seqCompose P₁ Q

theorem seqCompose_apply (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (a : A) (o₁ : O₁) (o₂ : O₂) :
    (P₁ ▷ Q) a (o₁, o₂) = P₁ a o₁ * Q o₁ a o₂ := rfl

/-!
## Dependent Continuation Outcome Types

For the paper's A7, where continuation channels Q^o, R^o may have different
outcome types Y^o, Z^o for each first-stage outcome o.
-/

/-- Probability mass function for dependent sequential composition. -/
noncomputable def seqComposeDepProb
    (P₁ : Channel A O₁) (Y : O₁ → Type v) [∀ o, Fintype (Y o)]
    (Q : ∀ o, Channel A (Y o)) (a : A) (oy : (o : O₁) × Y o) : ℝ :=
  P₁ a oy.1 * Q oy.1 a oy.2

/-- Two-stage composition with branch-dependent continuation outcome types.
    (P₁ ▷ Q) a ⟨o₁, y⟩ = P₁(o₁|a) * Q^{o₁}(y|a)

    The outcome space is Σ o, Y o (dependent sum over first-stage outcomes). -/
noncomputable def seqComposeDep
    (P₁ : Channel A O₁) (Y : O₁ → Type v)
    [∀ o, Fintype (Y o)] [∀ o, DecidableEq (Y o)]
    (Q : ∀ o, Channel A (Y o)) :
    Channel A ((o : O₁) × Y o) :=
  fun a =>
    { prob := seqComposeDepProb P₁ Y Q a
      nonneg := fun oy => by
        unfold seqComposeDepProb
        exact mul_nonneg ((P₁ a).nonneg oy.1) ((Q oy.1 a).nonneg oy.2)
      sum_eq_one := by
        unfold seqComposeDepProb
        trans (∑ o₁ : O₁, P₁ a o₁ * ∑ y : Y o₁, Q o₁ a y)
        · simp only [Fintype.sum_sigma]
          congr 1
          ext o₁
          rw [Finset.mul_sum]
        · simp_rw [(Q _ a).sum_eq_one, mul_one]
          exact (P₁ a).sum_eq_one }

theorem seqComposeDep_apply
    (P₁ : Channel A O₁) (Y : O₁ → Type v)
    [∀ o, Fintype (Y o)] [∀ o, DecidableEq (Y o)]
    (Q : ∀ o, Channel A (Y o)) (a : A) (o₁ : O₁) (y : Y o₁) :
    (seqComposeDep P₁ Y Q) a ⟨o₁, y⟩ = P₁ a o₁ * Q o₁ a y := rfl

/-!
## Branch Posteriors
-/

variable [DecidableEq A] [Nonempty A]

/-- Predicate: first-stage outcome o₁ has positive probability under (q, P₁). -/
def BranchPositive (P₁ : Channel A O₁) (q : Dist A) (o₁ : O₁) : Prop :=
  (Channel.outcomeMarginal P₁ q) o₁ > 0

/-- The posterior at a positive-probability branch. -/
noncomputable def branchPosterior (P₁ : Channel A O₁) (q : Dist A) (o₁ : O₁) : Dist A :=
  Channel.posterior P₁ q o₁

end TraceableAgency
