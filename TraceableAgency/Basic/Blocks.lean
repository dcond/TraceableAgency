/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Channel

/-!
# Labelled Block Environments

Block environments for cross-channel comparisons.
The paper's comparison environment P ⊔ Q : A⁰ ⊔ B¹ → Δ((O × {0}) ⊔ (Y × {1}))
is implemented using Sum types for two blocks.

For general finite block environments ⨆_{k∈K} P_k, we use Sigma types.
-/

set_option linter.style.header false

namespace TraceableAgency

variable {A B O Y : Type*}
variable [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
variable [DecidableEq A] [DecidableEq B] [DecidableEq O] [DecidableEq Y]

/-- Two-block channel P ⊔ Q : (A ⊕ B) → Δ(O ⊕ Y).
    Actions from A use channel P to outcomes in O (left).
    Actions from B use channel Q to outcomes in Y (right).
    Cross-block outcomes have zero probability. -/
noncomputable def blockChannel (P : Channel A O) (Q : Channel B Y) : Channel (A ⊕ B) (O ⊕ Y) :=
  fun ab =>
    match ab with
    | Sum.inl a =>
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
    | Sum.inr b =>
      { prob := fun oy =>
          match oy with
          | Sum.inl _ => 0
          | Sum.inr y => Q b y
        nonneg := fun oy =>
          match oy with
          | Sum.inl _ => le_refl 0
          | Sum.inr y => (Q b).nonneg y
        sum_eq_one := by
          simp only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add]
          exact (Q b).sum_eq_one }

notation:65 P " ⊔ " Q => blockChannel P Q

/-- Left block lottery embedding: q^0 ∈ Δ(A ⊕ B) from q ∈ Δ(A). -/
noncomputable def inlDist (q : Dist A) : Dist (A ⊕ B) where
  prob := fun ab =>
    match ab with
    | Sum.inl a => q a
    | Sum.inr _ => 0
  nonneg := fun ab =>
    match ab with
    | Sum.inl a => q.nonneg a
    | Sum.inr _ => le_refl 0
  sum_eq_one := by
    simp only [Fintype.sum_sum_type, Finset.sum_const_zero, add_zero]
    exact q.sum_eq_one

/-- Right block lottery embedding: p^1 ∈ Δ(A ⊕ B) from p ∈ Δ(B). -/
noncomputable def inrDist (p : Dist B) : Dist (A ⊕ B) where
  prob := fun ab =>
    match ab with
    | Sum.inl _ => 0
    | Sum.inr b => p b
  nonneg := fun ab =>
    match ab with
    | Sum.inl _ => le_refl 0
    | Sum.inr b => p.nonneg b
  sum_eq_one := by
    simp only [Fintype.sum_sum_type, Finset.sum_const_zero, zero_add]
    exact p.sum_eq_one

notation:max q "^0" => inlDist q
notation:max p "^1" => inrDist p

/-!
## Two-Block Simp Lemmas
-/

section TwoBlockSimp

variable (P : Channel A O) (Q : Channel B Y) (q : Dist A) (r : Dist B)

@[simp]
theorem inlDist_apply_inl (a : A) : (inlDist q : Dist (A ⊕ B)) (Sum.inl a) = q a := rfl

@[simp]
theorem inlDist_apply_inr (b : B) : (inlDist q : Dist (A ⊕ B)) (Sum.inr b) = 0 := rfl

@[simp]
theorem inrDist_apply_inl (a : A) : (inrDist r : Dist (A ⊕ B)) (Sum.inl a) = 0 := rfl

@[simp]
theorem inrDist_apply_inr (b : B) : (inrDist r : Dist (A ⊕ B)) (Sum.inr b) = r b := rfl

@[simp]
theorem blockChannel_apply_inl_inl (a : A) (o : O) :
    blockChannel P Q (Sum.inl a) (Sum.inl o) = P a o := rfl

@[simp]
theorem blockChannel_apply_inl_inr (a : A) (y : Y) :
    blockChannel P Q (Sum.inl a) (Sum.inr y) = 0 := rfl

@[simp]
theorem blockChannel_apply_inr_inl (b : B) (o : O) :
    blockChannel P Q (Sum.inr b) (Sum.inl o) = 0 := rfl

@[simp]
theorem blockChannel_apply_inr_inr (b : B) (y : Y) :
    blockChannel P Q (Sum.inr b) (Sum.inr y) = Q b y := rfl

end TwoBlockSimp

/-!
## Two-Block Outcome Marginal Lemmas
-/

section TwoBlockMarginal

variable [DecidableEq A] [DecidableEq B]
variable (P : Channel A O) (Q : Channel B Y) (q : Dist A) (r : Dist B)

@[simp]
theorem outcomeMarginal_block_inl_inl (o : O) :
    Channel.outcomeMarginal (blockChannel P Q) (inlDist q) (Sum.inl o)
    = Channel.outcomeMarginal P q o := by
  simp only [Channel.outcomeMarginal_apply]
  rw [Fintype.sum_sum_type]
  simp only [inlDist_apply_inl, blockChannel_apply_inl_inl, inlDist_apply_inr,
             blockChannel_apply_inr_inl, mul_zero, Finset.sum_const_zero, add_zero]

@[simp]
theorem outcomeMarginal_block_inl_inr (y : Y) :
    Channel.outcomeMarginal (blockChannel P Q) (inlDist q) (Sum.inr y) = 0 := by
  simp only [Channel.outcomeMarginal_apply]
  rw [Fintype.sum_sum_type]
  simp only [inlDist_apply_inl, blockChannel_apply_inl_inr, mul_zero,
             inlDist_apply_inr, zero_mul, Finset.sum_const_zero, zero_add]

@[simp]
theorem outcomeMarginal_block_inr_inl (o : O) :
    Channel.outcomeMarginal (blockChannel P Q) (inrDist r) (Sum.inl o) = 0 := by
  simp only [Channel.outcomeMarginal_apply]
  rw [Fintype.sum_sum_type]
  simp only [inrDist_apply_inl, zero_mul, inrDist_apply_inr,
             blockChannel_apply_inr_inl, mul_zero, Finset.sum_const_zero, add_zero]

@[simp]
theorem outcomeMarginal_block_inr_inr (y : Y) :
    Channel.outcomeMarginal (blockChannel P Q) (inrDist r) (Sum.inr y)
    = Channel.outcomeMarginal Q r y := by
  simp only [Channel.outcomeMarginal_apply]
  rw [Fintype.sum_sum_type]
  simp only [inrDist_apply_inl, blockChannel_apply_inl_inr, mul_zero,
             inrDist_apply_inr, blockChannel_apply_inr_inr,
             Finset.sum_const_zero, zero_add]

end TwoBlockMarginal

/-!
## General Finite Block Environments

For the paper's ⨆_{k∈K} P_k construction with dependent action and outcome types.
-/

universe u v w

variable {K : Type u} [Fintype K] [DecidableEq K]

/-- Probability mass function for a block-family channel at action ⟨k,a⟩ and outcome ⟨k',o⟩.
    Returns P_k(o|a) if k = k', else 0. -/
noncomputable def blockFamilyProb
    (Act : K → Type v) (Out : K → Type w)
    [∀ k, Fintype (Act k)] [∀ k, Fintype (Out k)]
    (P : ∀ k, Channel (Act k) (Out k))
    (ka : (k : K) × Act k) (ko : (k : K) × Out k) : ℝ :=
  if h : ka.1 = ko.1 then P ka.1 ka.2 (h ▸ ko.2) else 0

/-- General finite block channel: ⨆_{k∈K} P_k.
    Action ⟨k,a⟩ produces outcome ⟨k,o⟩ with probability P_k(o|a).
    Cross-block outcomes have zero probability. -/
noncomputable def blockFamilyChannel
    (Act : K → Type v) (Out : K → Type w)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
    (P : ∀ k, Channel (Act k) (Out k)) :
    Channel ((k : K) × Act k) ((k : K) × Out k) :=
  fun ka =>
    { prob := blockFamilyProb Act Out P ka
      nonneg := fun ko => by
        unfold blockFamilyProb
        split_ifs with h
        · exact (P ka.1 ka.2).nonneg (h ▸ ko.2)
        · exact le_refl 0
      sum_eq_one := by
        unfold blockFamilyProb
        trans (∑ o : Out ka.1, P ka.1 ka.2 o)
        · simp only [Fintype.sum_sigma]
          rw [Finset.sum_eq_single ka.1]
          · simp [dif_pos rfl]
          · intro k' _ hne
            apply Finset.sum_eq_zero
            intro o _
            simp [dif_neg (Ne.symm hne)]
          · intro h
            exact absurd (Finset.mem_univ _) h
        · exact (P ka.1 ka.2).sum_eq_one }

/-- Probability mass function for block-embedded distribution. -/
noncomputable def blockEmbedProb
    (Act : K → Type v) [∀ k, Fintype (Act k)]
    (i : K) (q : Dist (Act i))
    (ka : (k : K) × Act k) : ℝ :=
  if h : ka.1 = i then q (h ▸ ka.2) else 0

/-- Block-supported lottery embedding: q_i^i in the unified action space.
    Puts mass q(a) on ⟨i,a⟩ and zero on other blocks. -/
noncomputable def blockEmbedDist
    (Act : K → Type v)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (i : K) (q : Dist (Act i)) :
    Dist ((k : K) × Act k) where
  prob := blockEmbedProb Act i q
  nonneg := fun ka => by
    unfold blockEmbedProb
    split_ifs with h
    · exact q.nonneg (h ▸ ka.2)
    · exact le_refl 0
  sum_eq_one := by
    unfold blockEmbedProb
    trans (∑ a : Act i, q a)
    · simp only [Fintype.sum_sigma]
      rw [Finset.sum_eq_single i]
      · simp [dif_pos rfl]
      · intro k _ hne
        apply Finset.sum_eq_zero
        intro a _
        simp [dif_neg hne]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · exact q.sum_eq_one

/-!
## Dependent Finite-Block Simp Lemmas
-/

section DependentBlockSimp

variable {K : Type u} [Fintype K] [DecidableEq K]
variable (Act : K → Type u) (Out : K → Type u)
variable [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
variable [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
variable (P : ∀ k, Channel (Act k) (Out k))

@[simp]
theorem blockEmbedDist_apply_same (i : K) (q : Dist (Act i)) (a : Act i) :
    blockEmbedDist Act i q ⟨i, a⟩ = q a := by
  unfold blockEmbedDist blockEmbedProb
  simp only [dite_eq_ite, ite_true]

theorem blockEmbedDist_apply_ne {i j : K} (hij : j ≠ i) (q : Dist (Act i)) (a : Act j) :
    blockEmbedDist Act i q ⟨j, a⟩ = 0 := by
  unfold blockEmbedDist blockEmbedProb
  simp only [dif_neg hij]

@[simp]
theorem blockFamilyProb_same (i : K) (a : Act i) (o : Out i) :
    blockFamilyProb Act Out P ⟨i, a⟩ ⟨i, o⟩ = P i a o := by
  unfold blockFamilyProb
  simp only [dite_eq_ite, ite_true]

theorem blockFamilyProb_ne {i j : K} (hij : i ≠ j) (a : Act i) (o : Out j) :
    blockFamilyProb Act Out P ⟨i, a⟩ ⟨j, o⟩ = 0 := by
  unfold blockFamilyProb
  simp only [dif_neg hij]

@[simp]
theorem blockFamilyChannel_apply_same (i : K) (a : Act i) (o : Out i) :
    blockFamilyChannel Act Out P ⟨i, a⟩ ⟨i, o⟩ = P i a o := by
  simp only [blockFamilyChannel, blockFamilyProb_same]

theorem blockFamilyChannel_apply_ne {i j : K} (hij : i ≠ j) (a : Act i) (o : Out j) :
    blockFamilyChannel Act Out P ⟨i, a⟩ ⟨j, o⟩ = 0 := by
  simp only [blockFamilyChannel, blockFamilyProb_ne _ _ _ hij]

end DependentBlockSimp

/-!
## Dependent Finite-Block Outcome Marginal Lemmas
-/

section DependentBlockMarginal

variable {K : Type u} [Fintype K] [DecidableEq K]
variable (Act : K → Type u) (Out : K → Type u)
variable [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
variable [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
variable (P : ∀ k, Channel (Act k) (Out k))

@[simp]
theorem outcomeMarginal_blockFamily_embed_same (i : K) (q : Dist (Act i)) (o : Out i) :
    Channel.outcomeMarginal
      (blockFamilyChannel Act Out P)
      (blockEmbedDist Act i q)
      ⟨i, o⟩
    = Channel.outcomeMarginal (P i) q o := by
  simp only [Channel.outcomeMarginal_apply]
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [blockEmbedDist_apply_same, blockFamilyChannel_apply_same]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro a _
    have h : blockEmbedDist Act i q ⟨j, a⟩ = 0 := blockEmbedDist_apply_ne Act hji q a
    rw [h, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

theorem outcomeMarginal_blockFamily_embed_ne {i j : K} (hij : j ≠ i)
    (q : Dist (Act i)) (o : Out j) :
    Channel.outcomeMarginal
      (blockFamilyChannel Act Out P)
      (blockEmbedDist Act i q)
      ⟨j, o⟩
    = 0 := by
  simp only [Channel.outcomeMarginal_apply]
  rw [Fintype.sum_sigma]
  apply Finset.sum_eq_zero
  intro k _
  apply Finset.sum_eq_zero
  intro a _
  by_cases hki : k = i
  · have hne : k ≠ j := hki ▸ (Ne.symm hij)
    have h : blockFamilyChannel Act Out P ⟨k, a⟩ ⟨j, o⟩ = 0 :=
      blockFamilyChannel_apply_ne Act Out P hne a o
    rw [h, mul_zero]
  · have h : blockEmbedDist Act i q ⟨k, a⟩ = 0 := blockEmbedDist_apply_ne Act hki q a
    rw [h, zero_mul]

end DependentBlockMarginal

end TraceableAgency
