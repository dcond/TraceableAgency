/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Channel

/-!
# Product Distributions and Channels

Product distributions q₁ ⊗ q₂ and product channels P₁ ⊗ P₂ for
statistically independent components and derived background inertness.
-/

namespace TraceableAgency

variable {A₁ A₂ O₁ O₂ : Type*}
variable [Fintype A₁] [Fintype A₂] [Fintype O₁] [Fintype O₂]

/-- Product distribution: (q₁ ⊗ q₂)(a₁, a₂) = q₁(a₁) * q₂(a₂). -/
noncomputable def prodDist (q₁ : Dist A₁) (q₂ : Dist A₂) : Dist (A₁ × A₂) where
  prob := fun p => q₁ p.1 * q₂ p.2
  nonneg := fun p => mul_nonneg (q₁.nonneg p.1) (q₂.nonneg p.2)
  sum_eq_one := by
    simp only [Fintype.sum_prod_type, ← Finset.mul_sum, q₂.sum_eq_one, mul_one]
    exact q₁.sum_eq_one

notation:70 q₁ " ⊗ " q₂ => prodDist q₁ q₂

theorem prodDist_apply (q₁ : Dist A₁) (q₂ : Dist A₂) (p : A₁ × A₂) :
    (q₁ ⊗ q₂) p = q₁ p.1 * q₂ p.2 := rfl

@[simp]
theorem prodDist_apply_pair (q₁ : Dist A₁) (q₂ : Dist A₂) (a₁ : A₁) (a₂ : A₂) :
    (q₁ ⊗ q₂) (a₁, a₂) = q₁ a₁ * q₂ a₂ := rfl

/-- Product channel: (P₁ ⊗ P₂)(o₁, o₂ | a₁, a₂) = P₁(o₁|a₁) * P₂(o₂|a₂). -/
noncomputable def prodChannel (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂) :
    Channel (A₁ × A₂) (O₁ × O₂) :=
  fun a =>
    { prob := fun o => P₁ a.1 o.1 * P₂ a.2 o.2
      nonneg := fun o => mul_nonneg ((P₁ a.1).nonneg o.1) ((P₂ a.2).nonneg o.2)
      sum_eq_one := by
        simp only [Fintype.sum_prod_type, ← Finset.mul_sum, (P₂ a.2).sum_eq_one, mul_one]
        exact (P₁ a.1).sum_eq_one }

notation:70 P₁ " ⊗ᶜ " P₂ => prodChannel P₁ P₂

theorem prodChannel_apply (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂) (a : A₁ × A₂) (o : O₁ × O₂) :
    (P₁ ⊗ᶜ P₂) a o = P₁ a.1 o.1 * P₂ a.2 o.2 := rfl

@[simp]
theorem prodChannel_apply_pair (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂)
    (a₁ : A₁) (a₂ : A₂) (o₁ : O₁) (o₂ : O₂) :
    (P₁ ⊗ᶜ P₂) (a₁, a₂) (o₁, o₂) = P₁ a₁ o₁ * P₂ a₂ o₂ := rfl

/-- A row of a product channel is the product of the component rows. -/
theorem prodChannel_row_eq_prodDist (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂)
    (a : A₁ × A₂) :
    (P₁ ⊗ᶜ P₂) a = prodDist (P₁ a.1) (P₂ a.2) := by
  ext ⟨o₁, o₂⟩
  rfl

/-- Full support of a product distribution. -/
theorem prodDist_fullSupport (q₁ : Dist A₁) (q₂ : Dist A₂)
    (h₁ : q₁.FullSupport) (h₂ : q₂.FullSupport) : (q₁ ⊗ q₂).FullSupport := by
  intro p
  rw [prodDist_apply]
  exact mul_pos (h₁ p.1) (h₂ p.2)

/-!
## Outcome Marginal of Product Channel
-/

/-- Finite-sum product factorization helper. -/
theorem sum_prod_mul_eq_mul_sum_sum
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → ℝ) (g : β → ℝ) :
    (∑ x : α × β, f x.1 * g x.2) = (∑ a : α, f a) * (∑ b : β, g b) := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, Finset.sum_mul]

/-- The outcome marginal of a product channel under a product prior
    is the product of the component outcome marginals. -/
theorem outcomeMarginal_prod (q₁ : Dist A₁) (q₂ : Dist A₂)
    (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂) :
    Channel.outcomeMarginal (P₁ ⊗ᶜ P₂) (q₁ ⊗ q₂) =
    prodDist (Channel.outcomeMarginal P₁ q₁) (Channel.outcomeMarginal P₂ q₂) := by
  ext ⟨o₁, o₂⟩
  simp only [Channel.outcomeMarginal_apply, prodDist_apply]
  have h : ∀ a : A₁ × A₂, q₁ a.1 * q₂ a.2 * (P₁ ⊗ᶜ P₂) a (o₁, o₂) =
      (q₁ a.1 * P₁ a.1 o₁) * (q₂ a.2 * P₂ a.2 o₂) := fun a => by
    simp only [prodChannel_apply]; ring
  conv_lhs => arg 2; ext a; rw [h a]
  exact sum_prod_mul_eq_mul_sum_sum
    (fun a₁ => q₁ a₁ * P₁ a₁ o₁)
    (fun a₂ => q₂ a₂ * P₂ a₂ o₂)

end TraceableAgency
