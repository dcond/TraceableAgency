/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Info.MutualInfo
import TraceableAgency.Basic.Blocks
import TraceableAgency.Basic.Products
import TraceableAgency.Basic.Sequential
import TraceableAgency.Basic.Convergence

/-!
# Information Identities

Standard identities for entropy and mutual information with block constructions.
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

variable {A B O Y : Type*}
variable [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
variable [DecidableEq A] [DecidableEq B] [DecidableEq O] [DecidableEq Y]

/-!
## Entropy Congruence
-/

theorem entropy_congr {A : Type*} [Fintype A] (p r : Dist A) (h : ∀ a, p a = r a) :
    H(p) = H(r) := by
  unfold entropy
  congr 1
  ext a
  rw [h]

/-!
## Entropy of Dirac Distribution
-/

/-- Entropy of Dirac distribution is zero: H(δ_a) = 0. -/
theorem entropy_pure' {A : Type*} [Fintype A] [DecidableEq A] (a : A) :
    H(Dist.pure a) = 0 := by
  unfold entropy
  have h : ∀ b : A, entropyTerm ((Dist.pure a) b) = 0 := fun b => by
    by_cases hab : b = a
    · rw [hab, Dist.pure_apply_self, entropyTerm_one]
    · rw [Dist.pure_apply_ne _ _ hab, entropyTerm_zero]
  simp_rw [h, Finset.sum_const_zero]

/-!
## Entropy of Unit Distribution
-/

/-- Any distribution on Unit has entropy zero. -/
theorem entropy_unit (p : Dist Unit) : H(p) = 0 := by
  unfold entropy
  simp only [Fintype.sum_unique, Finset.univ_unique, Finset.sum_singleton]
  have h : p () = 1 := by
    have := p.sum_eq_one
    simp only [Fintype.sum_unique, Finset.univ_unique, Finset.sum_singleton] at this
    exact this
  rw [h, entropyTerm_one]

/-!
## Entropy Positivity Under Full Support
-/

/-- Entropy term is strictly positive for probabilities in (0, 1). -/
theorem entropyTerm_pos_of_pos_of_lt_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    0 < entropyTerm p := by
  unfold entropyTerm
  rw [if_neg (not_le.mpr hp0)]
  have hlog_neg : Real.log p < 0 := Real.log_neg hp0 hp1
  nlinarith

/-- Entropy is strictly positive for full-support distributions on nontrivial types. -/
theorem entropy_pos_of_fullSupport_nontrivial {A : Type*} [Fintype A] [DecidableEq A] [Nontrivial A]
    (q : Dist A) (hq : q.FullSupport) :
    0 < H(q) := by
  unfold entropy
  obtain ⟨a, b, hab⟩ := Nontrivial.exists_pair_ne (α := A)
  have ha_pos : 0 < q a := hq a
  have hb_pos : 0 < q b := hq b
  have ha_lt_one : q a < 1 := by
    have hsum := q.sum_eq_one
    by_contra hge
    push_neg at hge
    have ha_ge_one : q a ≥ 1 := hge
    have hb_le : q b ≤ ∑ x, q x - q a := by
      have : q b ≤ ∑ x ∈ Finset.univ.erase a, q x :=
        Finset.single_le_sum (fun x _ => q.nonneg x)
          (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩)
      have herase : ∑ x ∈ Finset.univ.erase a, q x = ∑ x, q x - q a :=
        Finset.sum_erase_eq_sub (Finset.mem_univ a)
      linarith
    have : q b ≤ 0 := by linarith
    linarith
  have h_term_pos : 0 < entropyTerm (q a) := entropyTerm_pos_of_pos_of_lt_one ha_pos ha_lt_one
  apply Finset.sum_pos'
  · intro i _
    exact entropyTerm_nonneg (q i) (q.nonneg i) (q.prob_le_one i)
  · exact ⟨a, Finset.mem_univ a, h_term_pos⟩

/-!
## Outcome Marginal of Identity Channel
-/

/-- Outcome marginal under identity channel equals the prior. -/
theorem outcomeMarginal_idChannel' {A : Type*} [Fintype A] [DecidableEq A]
    (q : Dist A) :
    Channel.outcomeMarginal Channel.idChannel q = q := by
  ext b
  simp only [Channel.outcomeMarginal_apply, Channel.idChannel, Dist.pure_apply]
  have h : ∀ a : A, q a * (if b = a then 1 else 0) = if a = b then q a else 0 := fun a => by
    by_cases hab : a = b
    · rw [hab, if_pos rfl, mul_one, if_pos rfl]
    · have hba : b ≠ a := fun h => hab h.symm
      rw [if_neg hba, mul_zero, if_neg hab]
  simp_rw [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-!
## Mutual Information of Identity Channel
-/

/-- Mutual information of identity channel equals entropy: I(q, Id) = H(q). -/
theorem mutualInfo_idChannel' {A : Type*} [Fintype A] [DecidableEq A]
    (q : Dist A) :
    mutualInfo q Channel.idChannel = H(q) := by
  unfold mutualInfo
  rw [outcomeMarginal_idChannel']
  simp only [Channel.idChannel]
  have h : ∀ a : A, H(Dist.pure a) = 0 := fun a => entropy_pure' a
  simp_rw [h, mul_zero, Finset.sum_const_zero, sub_zero]

/-!
## Outcome Marginal and Mutual Information of Uninformative Channel
-/

/-- The outcome marginal of the uninformative channel is the unique Unit distribution. -/
theorem outcomeMarginal_uninformativeChannel {A : Type*} [Fintype A]
    (q : Dist A) :
    Channel.outcomeMarginal (Channel.uninformativeChannel A) q = ⟨fun _ => 1, fun _ => by norm_num, by simp⟩ := by
  ext u
  simp only [Channel.outcomeMarginal_apply, Channel.uninformativeChannel]
  simp only [mul_one, q.sum_eq_one]

/-- Mutual information of uninformative channel is zero: I(q, U) = 0. -/
theorem mutualInfo_uninformativeChannel {A : Type*} [Fintype A]
    (q : Dist A) :
    mutualInfo q (Channel.uninformativeChannel A) = 0 := by
  unfold mutualInfo
  rw [outcomeMarginal_uninformativeChannel]
  have h_marginal_entropy : H((⟨fun _ : Unit => 1, fun _ => by norm_num, by simp⟩ : Dist Unit)) = 0 :=
    entropy_unit _
  have h_row_entropy : ∀ a : A, H((Channel.uninformativeChannel A) a) = 0 := fun a => entropy_unit _
  simp_rw [h_marginal_entropy, h_row_entropy, mul_zero, Finset.sum_const_zero, sub_zero]

/-!
## Entropy of Two-Block Embeddings

The key fact: entropyTerm 0 = 0, so zero-padded blocks don't contribute.
-/

theorem entropyTerm_eq_zero_of_nonpos {p : ℝ} (hp : p ≤ 0) : entropyTerm p = 0 := by
  unfold entropyTerm
  simp [hp]

@[simp]
theorem entropyTerm_zero' : entropyTerm 0 = 0 := entropyTerm_eq_zero_of_nonpos (le_refl 0)

theorem entropy_inlDist (q : Dist A) :
    H(@inlDist A B _ _ q) = H(q) := by
  unfold entropy
  rw [Fintype.sum_sum_type]
  simp only [inlDist_apply_inl, inlDist_apply_inr, entropyTerm_zero', Finset.sum_const_zero,
             add_zero]

theorem entropy_inrDist (r : Dist B) :
    H(@inrDist A B _ _ r) = H(r) := by
  unfold entropy
  rw [Fintype.sum_sum_type]
  simp only [inrDist_apply_inl, inrDist_apply_inr, entropyTerm_zero', Finset.sum_const_zero,
             zero_add]

/-!
## Block Channel Row Entropy

The rows of a block channel are embedded versions of the original channel rows.
-/

theorem entropy_blockChannel_row_inl (P : Channel A O) (Q : Channel B Y) (a : A) :
    H(blockChannel P Q (Sum.inl a)) = H(P a) := by
  unfold entropy
  rw [Fintype.sum_sum_type]
  simp only [blockChannel_apply_inl_inl, blockChannel_apply_inl_inr, entropyTerm_zero',
             Finset.sum_const_zero, add_zero]

theorem entropy_blockChannel_row_inr (P : Channel A O) (Q : Channel B Y) (b : B) :
    H(blockChannel P Q (Sum.inr b)) = H(Q b) := by
  unfold entropy
  rw [Fintype.sum_sum_type]
  simp only [blockChannel_apply_inr_inl, blockChannel_apply_inr_inr, entropyTerm_zero',
             Finset.sum_const_zero, zero_add]

/-!
## Outcome Marginal Distribution Equality for Blocks

The outcome marginal of a block-embedded prior is itself a block-embedded distribution.
-/

theorem outcomeMarginal_block_inl_eq (P : Channel A O) (Q : Channel B Y) (q : Dist A) :
    Channel.outcomeMarginal (blockChannel P Q) (inlDist q) =
    @inlDist O Y _ _ (Channel.outcomeMarginal P q) := by
  ext oy
  cases oy with
  | inl o => simp only [outcomeMarginal_block_inl_inl, inlDist_apply_inl]
  | inr y => simp only [outcomeMarginal_block_inl_inr, inlDist_apply_inr]

theorem outcomeMarginal_block_inr_eq (P : Channel A O) (Q : Channel B Y) (r : Dist B) :
    Channel.outcomeMarginal (blockChannel P Q) (inrDist r) =
    @inrDist O Y _ _ (Channel.outcomeMarginal Q r) := by
  ext oy
  cases oy with
  | inl o => simp only [outcomeMarginal_block_inr_inl, inrDist_apply_inl]
  | inr y => simp only [outcomeMarginal_block_inr_inr, inrDist_apply_inr]

/-!
## Outcome Marginal Entropy for Blocks
-/

theorem entropy_outcomeMarginal_block_inl (P : Channel A O) (Q : Channel B Y) (q : Dist A) :
    H(Channel.outcomeMarginal (blockChannel P Q) (inlDist q)) =
    H(Channel.outcomeMarginal P q) := by
  rw [outcomeMarginal_block_inl_eq]
  exact entropy_inlDist (Channel.outcomeMarginal P q)

theorem entropy_outcomeMarginal_block_inr (P : Channel A O) (Q : Channel B Y) (r : Dist B) :
    H(Channel.outcomeMarginal (blockChannel P Q) (inrDist r)) =
    H(Channel.outcomeMarginal Q r) := by
  rw [outcomeMarginal_block_inr_eq]
  exact entropy_inrDist (Channel.outcomeMarginal Q r)

/-!
## Conditional Entropy Sum for Blocks
-/

theorem condEntropySum_block_inl (P : Channel A O) (Q : Channel B Y) (q : Dist A) :
    (∑ x : A ⊕ B, (inlDist q) x * H(blockChannel P Q x)) =
    ∑ a : A, q a * H(P a) := by
  rw [Fintype.sum_sum_type]
  simp only [inlDist_apply_inl, inlDist_apply_inr, zero_mul, Finset.sum_const_zero, add_zero]
  congr 1
  ext a
  rw [entropy_blockChannel_row_inl]

theorem condEntropySum_block_inr (P : Channel A O) (Q : Channel B Y) (r : Dist B) :
    (∑ x : A ⊕ B, (inrDist r) x * H(blockChannel P Q x)) =
    ∑ b : B, r b * H(Q b) := by
  rw [Fintype.sum_sum_type]
  simp only [inrDist_apply_inl, inrDist_apply_inr, zero_mul, Finset.sum_const_zero, zero_add]
  congr 1
  ext b
  rw [entropy_blockChannel_row_inr]

/-!
## Two-Block Mutual Information Identities
-/

theorem mutualInfo_block_inl (P : Channel A O) (Q : Channel B Y) (q : Dist A) :
    mutualInfo (inlDist q) (blockChannel P Q) = mutualInfo q P := by
  unfold mutualInfo
  rw [entropy_outcomeMarginal_block_inl, condEntropySum_block_inl]

theorem mutualInfo_block_inr (P : Channel A O) (Q : Channel B Y) (r : Dist B) :
    mutualInfo (inrDist r) (blockChannel P Q) = mutualInfo r Q := by
  unfold mutualInfo
  rw [entropy_outcomeMarginal_block_inr, condEntropySum_block_inr]

/-!
## Dependent Finite-Block Entropy Identities

For the general ⨆_{k∈K} P_k construction.
-/

section DependentBlockEntropy

variable {K : Type u} [Fintype K] [DecidableEq K]
variable (Act : K → Type u) (Out : K → Type u)
variable [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
variable [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
variable (P : ∀ k, Channel (Act k) (Out k))

theorem entropy_blockEmbedDist (i : K) (q : Dist (Act i)) :
    H(blockEmbedDist Act i q) = H(q) := by
  unfold entropy
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [blockEmbedDist_apply_same]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro a _
    rw [blockEmbedDist_apply_ne Act hji q a, entropyTerm_zero']
  · intro hi
    exact absurd (Finset.mem_univ _) hi

theorem entropy_blockFamilyChannel_row (i : K) (a : Act i) :
    H(blockFamilyChannel Act Out P ⟨i, a⟩) = H(P i a) := by
  unfold entropy
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · simp only [blockFamilyChannel_apply_same]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro o _
    rw [blockFamilyChannel_apply_ne Act Out P (Ne.symm hji) a o, entropyTerm_zero']
  · intro hi
    exact absurd (Finset.mem_univ _) hi

/-!
## Outcome Marginal Entropy for Dependent Blocks

We avoid stating an equality of distributions (which involves dependent types)
and instead prove the entropy equality directly.
-/

theorem entropy_outcomeMarginal_blockFamily_embed (i : K) (q : Dist (Act i)) :
    H(Channel.outcomeMarginal
      (blockFamilyChannel Act Out P)
      (blockEmbedDist Act i q))
    = H(Channel.outcomeMarginal (P i) q) := by
  unfold entropy
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · congr 1
    ext o
    rw [outcomeMarginal_blockFamily_embed_same]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro o _
    rw [outcomeMarginal_blockFamily_embed_ne Act Out P hji q o, entropyTerm_zero']
  · intro hi
    exact absurd (Finset.mem_univ _) hi

/-!
## Conditional Entropy Sum for Dependent Blocks
-/

theorem condEntropySum_blockFamily_embed (i : K) (q : Dist (Act i)) :
    (∑ ka : (k : K) × Act k,
      blockEmbedDist Act i q ka * H(blockFamilyChannel Act Out P ka))
    = ∑ a : Act i, q a * H(P i a) := by
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · congr 1
    ext a
    rw [blockEmbedDist_apply_same, entropy_blockFamilyChannel_row]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro a _
    rw [blockEmbedDist_apply_ne Act hji q a, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ _) hi

/-!
## Dependent Finite-Block Mutual Information Identity
-/

theorem mutualInfo_blockFamily_embed (i : K) (q : Dist (Act i)) :
    mutualInfo
      (blockEmbedDist Act i q)
      (blockFamilyChannel Act Out P)
    = mutualInfo q (P i) := by
  unfold mutualInfo
  rw [entropy_outcomeMarginal_blockFamily_embed, condEntropySum_blockFamily_embed]

end DependentBlockEntropy

/-!
## Product Distribution Entropy Identities

For A7 (independent-background separability), we need entropy additivity
for product distributions: H(q₁ ⊗ q₂) = H(q₁) + H(q₂).
-/

section ProductEntropy

variable {A₁ A₂ O₁ O₂ : Type*}
variable [Fintype A₁] [Fintype A₂] [Fintype O₁] [Fintype O₂]

/-- Entropy term product identity for nonnegative probabilities.
    For x,y ≥ 0: entropyTerm(xy) = y * entropyTerm(x) + x * entropyTerm(y).

    Key cases:
    - If x = 0 or y = 0: both sides are 0
    - If x,y > 0: -xy log(xy) = -xy(log x + log y) = y(-x log x) + x(-y log y) -/
theorem entropyTerm_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entropyTerm (x * y) = y * entropyTerm x + x * entropyTerm y := by
  unfold entropyTerm
  by_cases hx0 : x ≤ 0
  · have hx_eq : x = 0 := le_antisymm hx0 hx
    simp [hx_eq]
  · push_neg at hx0
    by_cases hy0 : y ≤ 0
    · have hy_eq : y = 0 := le_antisymm hy0 hy
      simp [hy_eq]
    · push_neg at hy0
      have hxy : x * y > 0 := mul_pos hx0 hy0
      rw [if_neg (not_le_of_gt hx0), if_neg (not_le_of_gt hy0), if_neg (not_le_of_gt hxy)]
      rw [Real.log_mul (ne_of_gt hx0) (ne_of_gt hy0)]
      ring

/-- Entropy is additive for product distributions:
    H(q₁ ⊗ q₂) = H(q₁) + H(q₂). -/
theorem entropy_prodDist (q₁ : Dist A₁) (q₂ : Dist A₂) :
    H(prodDist q₁ q₂) = H(q₁) + H(q₂) := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  conv_lhs =>
    arg 2; ext a₁
    arg 2; ext a₂
    rw [prodDist_apply_pair, entropyTerm_mul (q₁.nonneg a₁) (q₂.nonneg a₂)]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [q₁.sum_eq_one, q₂.sum_eq_one]
  ring

/-- A row of a product channel has entropy equal to the sum of the component entropies. -/
theorem entropy_prodChannel_row (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂)
    (a : A₁ × A₂) :
    H((P₁ ⊗ᶜ P₂) a) = H(P₁ a.1) + H(P₂ a.2) := by
  rw [prodChannel_row_eq_prodDist]
  exact entropy_prodDist (P₁ a.1) (P₂ a.2)

/-- The entropy of the outcome marginal of a product channel is the sum of
    the individual marginal entropies. -/
theorem entropy_outcomeMarginal_prod (q₁ : Dist A₁) (q₂ : Dist A₂)
    (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂) :
    H(Channel.outcomeMarginal (P₁ ⊗ᶜ P₂) (q₁ ⊗ q₂)) =
    H(Channel.outcomeMarginal P₁ q₁) + H(Channel.outcomeMarginal P₂ q₂) := by
  rw [outcomeMarginal_prod]
  exact entropy_prodDist _ _

/-- Conditional entropy sum for product channel decomposes additively. -/
theorem condEntropySum_prod (q₁ : Dist A₁) (q₂ : Dist A₂)
    (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂) :
    (∑ a : A₁ × A₂, (q₁ ⊗ q₂) a * H((P₁ ⊗ᶜ P₂) a)) =
    (∑ a₁ : A₁, q₁ a₁ * H(P₁ a₁)) + (∑ a₂ : A₂, q₂ a₂ * H(P₂ a₂)) := by
  have step1 : ∀ a₁ a₂, (q₁ ⊗ q₂) (a₁, a₂) * H((P₁ ⊗ᶜ P₂) (a₁, a₂)) =
      q₁ a₁ * q₂ a₂ * H(P₁ a₁) + q₁ a₁ * q₂ a₂ * H(P₂ a₂) := fun a₁ a₂ => by
    rw [prodDist_apply_pair, entropy_prodChannel_row]; ring
  rw [Fintype.sum_prod_type]
  simp_rw [step1, Finset.sum_add_distrib]
  have left_sum : ∀ a₁, ∑ a₂, q₁ a₁ * q₂ a₂ * H(P₁ a₁) = q₁ a₁ * H(P₁ a₁) := fun a₁ => by
    have h : ∀ a₂, q₁ a₁ * q₂ a₂ * H(P₁ a₁) = q₂ a₂ * (q₁ a₁ * H(P₁ a₁)) := fun _ => by ring
    simp_rw [h, ← Finset.sum_mul, q₂.sum_eq_one, one_mul]
  have right_sum : ∀ a₁, ∑ a₂, q₁ a₁ * q₂ a₂ * H(P₂ a₂) = q₁ a₁ * (∑ a₂, q₂ a₂ * H(P₂ a₂)) :=
    fun a₁ => by
      have h : ∀ a₂, q₁ a₁ * q₂ a₂ * H(P₂ a₂) = q₁ a₁ * (q₂ a₂ * H(P₂ a₂)) := fun _ => by ring
      simp_rw [h, ← Finset.mul_sum]
  simp_rw [left_sum, right_sum, ← Finset.sum_mul, q₁.sum_eq_one, one_mul]

/-- Mutual information is additive for independent products:
    I(q₁ ⊗ q₂, P₁ ⊗ P₂) = I(q₁, P₁) + I(q₂, P₂). -/
theorem mutualInfo_prod (q₁ : Dist A₁) (q₂ : Dist A₂)
    (P₁ : Channel A₁ O₁) (P₂ : Channel A₂ O₂) :
    mutualInfo (prodDist q₁ q₂) (prodChannel P₁ P₂) =
    mutualInfo q₁ P₁ + mutualInfo q₂ P₂ := by
  unfold mutualInfo
  rw [entropy_outcomeMarginal_prod, condEntropySum_prod]
  ring

end ProductEntropy

/-!
## A7 Product Background Cancellation Helpers

For Independent-Background Separability: comparing P₁ vs Q₁ in the first
component is independent of the background channel in the second component.
-/

section A7ProductHelpers

/-- Left-background cancellation: comparing P₁ vs Q₁ is independent of the
    second-component background channel. -/
theorem mutualInfo_prod_same_background_left
    {A₁ A₂ O₁ O₂R O₂S : Type*}
    [Fintype A₁] [Fintype A₂] [Fintype O₁] [Fintype O₂R] [Fintype O₂S]
    (q₁ : Dist A₁) (q₂ : Dist A₂)
    (P₁ Q₁ : Channel A₁ O₁)
    (R₂ : Channel A₂ O₂R) (S₂ : Channel A₂ O₂S) :
    mutualInfo (prodDist q₁ q₂) (prodChannel P₁ R₂) ≥
      mutualInfo (prodDist q₁ q₂) (prodChannel Q₁ R₂)
    ↔
    mutualInfo (prodDist q₁ q₂) (prodChannel P₁ S₂) ≥
      mutualInfo (prodDist q₁ q₂) (prodChannel Q₁ S₂) := by
  rw [mutualInfo_prod, mutualInfo_prod, mutualInfo_prod, mutualInfo_prod]
  constructor <;> intro h <;> linarith

/-- Right-background cancellation: comparing P₂ vs Q₂ is independent of the
    first-component background channel. -/
theorem mutualInfo_prod_same_background_right
    {A₁ A₂ O₁R O₁S O₂ : Type*}
    [Fintype A₁] [Fintype A₂] [Fintype O₁R] [Fintype O₁S] [Fintype O₂]
    (q₁ : Dist A₁) (q₂ : Dist A₂)
    (R₁ : Channel A₁ O₁R) (S₁ : Channel A₁ O₁S)
    (P₂ Q₂ : Channel A₂ O₂) :
    mutualInfo (prodDist q₁ q₂) (prodChannel R₁ P₂) ≥
      mutualInfo (prodDist q₁ q₂) (prodChannel R₁ Q₂)
    ↔
    mutualInfo (prodDist q₁ q₂) (prodChannel S₁ P₂) ≥
      mutualInfo (prodDist q₁ q₂) (prodChannel S₁ Q₂) := by
  rw [mutualInfo_prod, mutualInfo_prod, mutualInfo_prod, mutualInfo_prod]
  constructor <;> intro h <;> linarith

end A7ProductHelpers

/-!
## Sequential Composition Chain Rule

For A6 (Dynamic Consistency), we need the mutual information chain rule
for sequential composition:
  I(q, P₁ ▷ Q) = I(q, P₁) + Σ_{o₁} m(o₁) * I(posterior(o₁), Q^{o₁})
-/

section SequentialChainRule

/-!
### Key Bayes Identity

The posterior times marginal equals the joint probability.
-/

/-- Helper: if a sum of nonnegative terms equals zero, each term is zero. -/
theorem summand_eq_zero_of_sum_eq_zero_of_nonneg'
    {α : Type*} [Fintype α] (f : α → ℝ)
    (h_nonneg : ∀ a, 0 ≤ f a) (h_sum : ∑ a, f a = 0) :
    ∀ a, f a = 0 := by
  intro a
  by_contra h
  have hpos : 0 < f a := lt_of_le_of_ne (h_nonneg a) (Ne.symm h)
  have hle : f a ≤ ∑ a', f a' := Finset.single_le_sum (fun a' _ => h_nonneg a') (Finset.mem_univ a)
  linarith

/-- Bayes identity: marginal(o) * posterior(o)(a) = q(a) * P(o|a).
    This holds even for zero-probability branches. -/
theorem posterior_mul_marginal {A O : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O]
    (q : Dist A) (P : Channel A O) (o : O) (a : A) :
    (Channel.outcomeMarginal P q) o * (Channel.posterior P q o) a = q a * P a o := by
  let m := Channel.outcomeMarginal P q
  by_cases hpos : m o > 0
  · unfold Channel.posterior
    rw [dif_pos hpos]
    have hne : m o ≠ 0 := ne_of_gt hpos
    calc m o * (q a * P a o / m o) = (q a * P a o / m o) * m o := by ring
      _ = q a * P a o := div_mul_cancel₀ _ hne
  · have hm_eq : m o = 0 := le_antisymm (le_of_not_gt hpos) (m.nonneg o)
    have h_summand : ∀ a', q a' * P a' o = 0 := by
      apply summand_eq_zero_of_sum_eq_zero_of_nonneg'
      · intro a'; exact mul_nonneg (q.nonneg a') ((P a').nonneg o)
      · exact hm_eq
    rw [hm_eq, h_summand a]
    ring

/-- Marginal times posterior, with arguments swapped. -/
theorem marginal_mul_posterior {A O : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O]
    (q : Dist A) (P : Channel A O) (o : O) (a : A) :
    (Channel.posterior P q o) a * (Channel.outcomeMarginal P q) o = q a * P a o := by
  rw [mul_comm]
  exact posterior_mul_marginal q P o a

/-!
### Sigma Distribution

A distribution on dependent pairs (o₁, y) where o₁ is drawn from m
and y is drawn from R(o₁).
-/

/-- Distribution on dependent pairs: (m ⊗_σ R)(o₁, y) = m(o₁) * R(o₁)(y). -/
noncomputable def sigmaDist {O₁ : Type*} [Fintype O₁] {Y : O₁ → Type*}
    [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (m : Dist O₁) (R : ∀ o₁, Dist (Y o₁)) :
    Dist ((o₁ : O₁) × Y o₁) where
  prob := fun oy => m oy.1 * R oy.1 oy.2
  nonneg := fun oy => mul_nonneg (m.nonneg oy.1) ((R oy.1).nonneg oy.2)
  sum_eq_one := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum, (R _).sum_eq_one, mul_one]
    exact m.sum_eq_one

@[simp]
theorem sigmaDist_apply {O₁ : Type*} [Fintype O₁] {Y : O₁ → Type*}
    [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (m : Dist O₁) (R : ∀ o₁, Dist (Y o₁)) (o₁ : O₁) (y : Y o₁) :
    sigmaDist m R ⟨o₁, y⟩ = m o₁ * R o₁ y := rfl

/-!
### Entropy Chain Rule for Sigma Distributions

H(m ⊗_σ R) = H(m) + Σ_{o₁} m(o₁) * H(R(o₁))
-/

theorem entropy_sigma_chain {O₁ : Type*} [Fintype O₁] {Y : O₁ → Type*}
    [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (m : Dist O₁) (R : ∀ o₁, Dist (Y o₁)) :
    H(sigmaDist m R) = H(m) + ∑ o₁, m o₁ * H(R o₁) := by
  simp only [entropy]
  rw [Fintype.sum_sigma]
  have step1 : ∀ o₁, ∑ y : Y o₁, entropyTerm (sigmaDist m R ⟨o₁, y⟩) =
      ∑ y, (R o₁ y * entropyTerm (m o₁) + m o₁ * entropyTerm (R o₁ y)) := fun o₁ => by
    congr 1; ext y
    simp only [sigmaDist_apply]
    rw [entropyTerm_mul (m.nonneg o₁) ((R o₁).nonneg y)]
  simp_rw [step1, Finset.sum_add_distrib]
  have left_term : ∀ o₁, ∑ y : Y o₁, R o₁ y * entropyTerm (m o₁) = entropyTerm (m o₁) := fun o₁ => by
    rw [← Finset.sum_mul, (R o₁).sum_eq_one, one_mul]
  have right_term : ∀ o₁, ∑ y : Y o₁, m o₁ * entropyTerm (R o₁ y) =
      m o₁ * ∑ a, entropyTerm (R o₁ a) := fun o₁ => by
    rw [← Finset.mul_sum]
  simp_rw [left_term, right_term]

end SequentialChainRule

/-!
## Outcome padding and posterior-law preservation

These elementary identities live here because padding is needed both by the
derived public-coin argument and by the later branch-aggregation construction.
-/

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

/-!
## Sequential Composition Mutual Information Chain Rule

For A6 (Branchwise Continuation Monotonicity), we need the chain rule:
  I(q, P₁ ▷ Q) = I(q, P₁) + Σ_{o₁} m(o₁) * I(posterior(o₁), Q^{o₁})

We use explicit universe annotations to match seqComposeDep.
-/

section SeqComposeChainRule

universe u_seq v_seq

variable {A O₁ : Type u_seq}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype O₁] [DecidableEq O₁]

/-- Each row of seqComposeDep equals the sigma distribution of the component rows. -/
theorem seqComposeDep_row_eq_sigmaDist
    (P₁ : Channel A O₁) (Y : O₁ → Type v_seq)
    [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) (a : A) :
    seqComposeDep P₁ Y Q a = sigmaDist (P₁ a) (fun o₁ => Q o₁ a) := by
  ext ⟨o₁, y⟩
  simp only [seqComposeDep_apply, sigmaDist_apply]

/-- Entropy of a row of seqComposeDep decomposes via the chain rule. -/
theorem entropy_seqComposeDep_row
    (P₁ : Channel A O₁) (Y : O₁ → Type v_seq)
    [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) (a : A) :
    H(seqComposeDep P₁ Y Q a) = H(P₁ a) + ∑ o₁, (P₁ a) o₁ * H(Q o₁ a) := by
  rw [seqComposeDep_row_eq_sigmaDist]
  exact entropy_sigma_chain (P₁ a) (fun o₁ => Q o₁ a)

/-- Outcome marginal of seqComposeDep at a point equals the product of marginals
    weighted by the posterior. -/
theorem outcomeMarginal_seqComposeDep_apply
    (q : Dist A) (P₁ : Channel A O₁)
    (Y : O₁ → Type v_seq) [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁))
    (oy : (o₁ : O₁) × Y o₁) :
    (Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) oy =
    (Channel.outcomeMarginal P₁ q) oy.1 *
    (Channel.outcomeMarginal (Q oy.1) (Channel.posterior P₁ q oy.1)) oy.2 := by
  obtain ⟨o₁, y⟩ := oy
  simp only [Channel.outcomeMarginal_apply]
  have step0 : ∑ a, q a * (seqComposeDep P₁ Y Q a) ⟨o₁, y⟩ =
      ∑ a, q a * (P₁ a o₁ * Q o₁ a y) := Finset.sum_congr rfl (fun a _ => by
    simp only [seqComposeDep_apply])
  rw [step0]
  have step1 : ∑ a, q a * (P₁ a o₁ * Q o₁ a y) =
      ∑ a, (Channel.outcomeMarginal P₁ q) o₁ *
        ((Channel.posterior P₁ q o₁) a * Q o₁ a y) := by
    congr 1; ext a
    have h := posterior_mul_marginal q P₁ o₁ a
    calc q a * (P₁ a o₁ * Q o₁ a y)
        = (q a * P₁ a o₁) * Q o₁ a y := by ring
      _ = ((Channel.outcomeMarginal P₁ q) o₁ * (Channel.posterior P₁ q o₁) a) *
            Q o₁ a y := by rw [h]
      _ = (Channel.outcomeMarginal P₁ q) o₁ *
            ((Channel.posterior P₁ q o₁) a * Q o₁ a y) := by ring
  rw [step1, ← Finset.mul_sum]
  simp only [Channel.outcomeMarginal_apply]

/-- Positive compound outcomes have the branch posterior of the selected
continuation channel. -/
theorem posterior_seqComposeDep_of_pos
    (q : Dist A) (P₁ : Channel A O₁)
    (Y : O₁ → Type v_seq) [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) (o₁ : O₁) (y : Y o₁)
    (hpos :
      (Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) ⟨o₁, y⟩ > 0) :
    Channel.posterior (seqComposeDep P₁ Y Q) q ⟨o₁, y⟩ =
      Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) y := by
  have hmarg :=
    outcomeMarginal_seqComposeDep_apply q P₁ Y Q ⟨o₁, y⟩
  have hprod :
      (Channel.outcomeMarginal P₁ q) o₁ *
          (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y > 0 := by
    rw [hmarg] at hpos
    exact hpos
  have hm₁_nonneg : 0 ≤ (Channel.outcomeMarginal P₁ q) o₁ :=
    (Channel.outcomeMarginal P₁ q).nonneg o₁
  have hm₂_nonneg :
      0 ≤ (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y :=
    (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)).nonneg y
  have hm₁_pos : (Channel.outcomeMarginal P₁ q) o₁ > 0 := by nlinarith
  have hm₂_pos :
      (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y > 0 := by
    nlinarith
  ext a
  let mC := (Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) ⟨o₁, y⟩
  let m₁ := (Channel.outcomeMarginal P₁ q) o₁
  let m₂ := (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y
  let pC := Channel.posterior (seqComposeDep P₁ Y Q) q ⟨o₁, y⟩
  let p₁ := Channel.posterior P₁ q o₁
  let p₂ := Channel.posterior (Q o₁) p₁ y
  have hleft := posterior_mul_marginal q (seqComposeDep P₁ Y Q) ⟨o₁, y⟩ a
  have hfirst := posterior_mul_marginal q P₁ o₁ a
  have hsecond := posterior_mul_marginal p₁ (Q o₁) y a
  have hmarg' : mC = m₁ * m₂ := by
    simpa [mC, m₁, m₂] using hmarg
  have hcalc : mC * pC a = mC * p₂ a := by
    calc
      mC * pC a
          = q a * (seqComposeDep P₁ Y Q a) ⟨o₁, y⟩ := hleft
      _ = q a * (P₁ a o₁ * Q o₁ a y) := by rw [seqComposeDep_apply]
      _ = (q a * P₁ a o₁) * Q o₁ a y := by ring
      _ = (m₁ * p₁ a) * Q o₁ a y := by rw [← hfirst]
      _ = m₁ * (p₁ a * Q o₁ a y) := by ring
      _ = m₁ * (m₂ * p₂ a) := by rw [← hsecond]
      _ = (m₁ * m₂) * p₂ a := by ring
      _ = mC * p₂ a := by rw [hmarg']
  exact mul_left_cancel₀ (ne_of_gt hpos) hcalc

/-- Outcome marginal of seqComposeDep equals the sigma distribution of
    first-stage marginal and continuation marginals. -/
theorem outcomeMarginal_seqComposeDep_eq_sigmaDist
    (q : Dist A) (P₁ : Channel A O₁)
    (Y : O₁ → Type v_seq) [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) :
    Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q =
    sigmaDist
      (Channel.outcomeMarginal P₁ q)
      (fun o₁ => Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) := by
  ext ⟨o₁, y⟩
  rw [outcomeMarginal_seqComposeDep_apply, sigmaDist_apply]

/-- The posterior law of a dependent sequential composition is the
first-stage marginal mixture of the branch posterior laws. This is the
extensional posterior-law integral form of the paper identity
`μ_{q,P₁▷{Q^o}} = Σ_o m(o) μ_{r_o,Q^o}`. -/
theorem posteriorLawIntegral_seqComposeDep_eq_sum
    (q : Dist A) (P₁ : Channel A O₁)
    (Y : O₁ → Type v_seq) [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (seqComposeDep P₁ Y Q) φ =
      ∑ o₁,
        (Channel.outcomeMarginal P₁ q) o₁ *
          posteriorLawIntegral (Channel.posterior P₁ q o₁) (Q o₁) φ := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_sigma]
  congr 1
  ext o₁
  rw [Finset.mul_sum]
  congr 1
  ext y
  have hmarg :=
    outcomeMarginal_seqComposeDep_apply q P₁ Y Q ⟨o₁, y⟩
  by_cases hpos :
      (Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) ⟨o₁, y⟩ > 0
  · have hpost :=
      posterior_seqComposeDep_of_pos q P₁ Y Q o₁ y hpos
    calc
      (Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) ⟨o₁, y⟩ *
          φ (Channel.posterior (seqComposeDep P₁ Y Q) q ⟨o₁, y⟩)
          =
        ((Channel.outcomeMarginal P₁ q) o₁ *
          (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y) *
          φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) y) := by
            rw [hpost, hmarg]
      _ =
        (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y *
            φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) y)) := by
            ring
  · have hzero :
      (Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) ⟨o₁, y⟩ = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        ((Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q).nonneg ⟨o₁, y⟩)
    have hprod :
        (Channel.outcomeMarginal P₁ q) o₁ *
            (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y = 0 := by
      rw [hmarg] at hzero
      exact hzero
    calc
      (Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) ⟨o₁, y⟩ *
          φ (Channel.posterior (seqComposeDep P₁ Y Q) q ⟨o₁, y⟩)
          = 0 := by rw [hzero, zero_mul]
      _ =
        (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y *
            φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) y)) := by
            calc
              0 = ((Channel.outcomeMarginal P₁ q) o₁ *
                    (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y) *
                    φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) y) := by
                    rw [hprod, zero_mul]
              _ =
                  (Channel.outcomeMarginal P₁ q) o₁ *
                    ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) y *
                      φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) y)) := by
                    ring

/-- Entropy of outcome marginal of seqComposeDep via chain rule. -/
theorem entropy_outcomeMarginal_seqComposeDep
    (q : Dist A) (P₁ : Channel A O₁)
    (Y : O₁ → Type v_seq) [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) :
    H(Channel.outcomeMarginal (seqComposeDep P₁ Y Q) q) =
    H(Channel.outcomeMarginal P₁ q) +
    ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
      H(Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) := by
  rw [outcomeMarginal_seqComposeDep_eq_sigmaDist]
  exact entropy_sigma_chain _ _

/-- Conditional entropy sum for seqComposeDep decomposes into first-stage
    and continuation contributions. -/
theorem condEntropySum_seqComposeDep
    (q : Dist A) (P₁ : Channel A O₁)
    (Y : O₁ → Type v_seq) [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) :
    (∑ a : A, q a * H(seqComposeDep P₁ Y Q a)) =
    (∑ a : A, q a * H(P₁ a)) +
    ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
      (∑ a : A, (Channel.posterior P₁ q o₁) a * H(Q o₁ a)) := by
  simp_rw [entropy_seqComposeDep_row]
  simp_rw [mul_add, Finset.sum_add_distrib]
  congr 1
  have step1 : ∑ a : A, q a * ∑ o₁, (P₁ a) o₁ * H(Q o₁ a) =
      ∑ a : A, ∑ o₁ : O₁, q a * ((P₁ a) o₁ * H(Q o₁ a)) := by
    congr 1; ext a; rw [Finset.mul_sum]
  have key : ∀ a o₁, q a * ((P₁ a) o₁ * H(Q o₁ a)) =
      (Channel.outcomeMarginal P₁ q) o₁ * ((Channel.posterior P₁ q o₁) a * H(Q o₁ a)) := by
    intro a o₁
    have h := posterior_mul_marginal q P₁ o₁ a
    calc q a * (P₁ a o₁ * H(Q o₁ a))
        = (q a * P₁ a o₁) * H(Q o₁ a) := by ring
      _ = ((Channel.outcomeMarginal P₁ q) o₁ * (Channel.posterior P₁ q o₁) a) * H(Q o₁ a) := by rw [h]
      _ = (Channel.outcomeMarginal P₁ q) o₁ * ((Channel.posterior P₁ q o₁) a * H(Q o₁ a)) := by ring
  have step2 : ∑ a : A, ∑ o₁ : O₁, q a * ((P₁ a) o₁ * H(Q o₁ a)) =
      ∑ a : A, ∑ o₁ : O₁, (Channel.outcomeMarginal P₁ q) o₁ *
        ((Channel.posterior P₁ q o₁) a * H(Q o₁ a)) := by
    congr 1; ext a; congr 1; ext o₁; exact key a o₁
  have step3 : ∑ a : A, ∑ o₁ : O₁, (Channel.outcomeMarginal P₁ q) o₁ *
        ((Channel.posterior P₁ q o₁) a * H(Q o₁ a)) =
      ∑ o₁ : O₁, ∑ a : A, (Channel.outcomeMarginal P₁ q) o₁ *
        ((Channel.posterior P₁ q o₁) a * H(Q o₁ a)) := Finset.sum_comm
  have step4 : ∑ o₁ : O₁, ∑ a : A, (Channel.outcomeMarginal P₁ q) o₁ *
        ((Channel.posterior P₁ q o₁) a * H(Q o₁ a)) =
      ∑ o₁ : O₁, (Channel.outcomeMarginal P₁ q) o₁ *
        ∑ a : A, (Channel.posterior P₁ q o₁) a * H(Q o₁ a) := by
    congr 1; ext o₁; rw [Finset.mul_sum]
  rw [step1, step2, step3, step4]

/-- Mutual information chain rule for dependent sequential composition:
    I(q, P₁ ▷ Q) = I(q, P₁) + Σ_{o₁} m(o₁) * I(posterior(o₁), Q^{o₁})

    This is the key identity for A6 (Branchwise Continuation Monotonicity). -/
theorem mutualInfo_seqComposeDep
    (q : Dist A) (P₁ : Channel A O₁)
    (Y : O₁ → Type v_seq) [∀ o₁, Fintype (Y o₁)] [∀ o₁, DecidableEq (Y o₁)]
    (Q : ∀ o₁, Channel A (Y o₁)) :
    mutualInfo q (seqComposeDep P₁ Y Q) =
    mutualInfo q P₁ +
    ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
      mutualInfo (Channel.posterior P₁ q o₁) (Q o₁) := by
  unfold mutualInfo
  rw [entropy_outcomeMarginal_seqComposeDep, condEntropySum_seqComposeDep]
  have expand : ∀ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
      (H(Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) -
       ∑ a, (Channel.posterior P₁ q o₁) a * H(Q o₁ a)) =
      (Channel.outcomeMarginal P₁ q) o₁ *
        H(Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) -
      (Channel.outcomeMarginal P₁ q) o₁ *
        ∑ a, (Channel.posterior P₁ q o₁) a * H(Q o₁ a) := fun o₁ => by ring
  have goal_eq : ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
      (H(Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) -
       ∑ a, (Channel.posterior P₁ q o₁) a * H(Q o₁ a)) =
      ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        H(Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) -
      ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        ∑ a, (Channel.posterior P₁ q o₁) a * H(Q o₁ a) := by
    conv_lhs => arg 2; ext o₁; rw [expand o₁]
    rw [← Finset.sum_sub_distrib]
  rw [goal_eq]
  ring

end SeqComposeChainRule

/-!
## Entropy Reduction Formula

The entropy-reduction form of mutual information:
  I(q, P) = H(q) - Σ_o m(o) * H(r_o)

where m is the outcome marginal and r_o is the posterior.

This is derived from the joint entropy identity:
  H(q) + Σ_a q(a) H(P_a) = H(m) + Σ_o m(o) H(r_o)

Both sides equal the entropy of the joint distribution on A × O.
-/

section EntropyReduction

variable {A O : Type*} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]

/-- The joint distribution on A × O induced by prior q and channel P.
    joint(a, o) = q(a) * P(o|a) -/
noncomputable def jointDist (q : Dist A) (P : Channel A O) : Dist (A × O) where
  prob := fun ao => q ao.1 * P ao.1 ao.2
  nonneg := fun ao => mul_nonneg (q.nonneg ao.1) ((P ao.1).nonneg ao.2)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, (P _).sum_eq_one, mul_one]
    exact q.sum_eq_one

@[simp]
theorem jointDist_apply (q : Dist A) (P : Channel A O) (a : A) (o : O) :
    jointDist q P (a, o) = q a * P a o := rfl

/-- Joint entropy from the prior side: H(joint) = H(q) + Σ_a q(a) H(P_a). -/
theorem entropy_jointDist_prior (q : Dist A) (P : Channel A O) :
    H(jointDist q P) = H(q) + ∑ a, q a * H(P a) := by
  unfold entropy
  rw [Fintype.sum_prod_type]
  have h : ∀ a, ∑ o, entropyTerm (jointDist q P (a, o)) =
      ∑ o, (P a o * entropyTerm (q a) + q a * entropyTerm (P a o)) := fun a => by
    congr 1; ext o
    simp only [jointDist_apply]
    rw [entropyTerm_mul (q.nonneg a) ((P a).nonneg o)]
  conv_lhs => arg 2; ext a; rw [h a, Finset.sum_add_distrib]
  have left_term : ∀ a, ∑ o, P a o * entropyTerm (q a) = entropyTerm (q a) := fun a => by
    rw [← Finset.sum_mul, (P a).sum_eq_one, one_mul]
  have right_term : ∀ a, ∑ o, q a * entropyTerm (P a o) = q a * ∑ o, entropyTerm (P a o) := fun a => by
    rw [← Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [left_term a, right_term a]
  rw [Finset.sum_add_distrib]

/-- Joint entropy from the marginal side: H(joint) = H(m) + Σ_o m(o) H(r_o). -/
theorem entropy_jointDist_marginal (q : Dist A) (P : Channel A O) :
    H(jointDist q P) = H(Channel.outcomeMarginal P q) +
      ∑ o, (Channel.outcomeMarginal P q) o * H(Channel.posterior P q o) := by
  unfold entropy
  have h_sum_swap : ∑ ao : A × O, entropyTerm (jointDist q P ao) =
      ∑ o, ∑ a, entropyTerm (jointDist q P (a, o)) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
  rw [h_sum_swap]
  let m := Channel.outcomeMarginal P q
  let r := Channel.posterior P q
  have h : ∀ o, ∑ a, entropyTerm (jointDist q P (a, o)) =
      ∑ a, (r o a * entropyTerm (m o) + m o * entropyTerm (r o a)) := fun o => by
    congr 1; ext a
    simp only [jointDist_apply]
    have h_bayes := posterior_mul_marginal q P o a
    by_cases hm : m o > 0
    · have hm_ne : m o ≠ 0 := ne_of_gt hm
      have h_prod : q a * P a o = m o * r o a := h_bayes.symm
      rw [h_prod, entropyTerm_mul (m.nonneg o) ((r o).nonneg a)]
    · have hm_eq : m o = 0 := le_antisymm (le_of_not_gt hm) (m.nonneg o)
      have h_zero : q a * P a o = 0 := by
        have := h_bayes; rw [hm_eq, zero_mul] at this; exact this.symm
      simp [h_zero, hm_eq, entropyTerm_zero]
  conv_lhs => arg 2; ext o; rw [h o, Finset.sum_add_distrib]
  have left_term : ∀ o, ∑ a, r o a * entropyTerm (m o) = entropyTerm (m o) := fun o => by
    rw [← Finset.sum_mul, (r o).sum_eq_one, one_mul]
  have right_term : ∀ o, ∑ a, m o * entropyTerm (r o a) = m o * ∑ a, entropyTerm (r o a) := fun o => by
    rw [← Finset.mul_sum]
  conv_lhs => arg 2; ext o; rw [left_term o, right_term o]
  rw [Finset.sum_add_distrib]

/-- The joint entropy identity: the two decompositions of H(joint) are equal. -/
theorem joint_entropy_identity (q : Dist A) (P : Channel A O) :
    H(q) + ∑ a, q a * H(P a) =
    H(Channel.outcomeMarginal P q) + ∑ o, (Channel.outcomeMarginal P q) o *
      H(Channel.posterior P q o) := by
  rw [← entropy_jointDist_prior, ← entropy_jointDist_marginal]

/-- Entropy reduction form of mutual information:
    I(q, P) = H(q) - Σ_o m(o) * H(r_o)

    This follows from rearranging the joint entropy identity. -/
theorem mutualInfo_entropyReduction (q : Dist A) (P : Channel A O) :
    mutualInfo q P = H(q) - ∑ o, (Channel.outcomeMarginal P q) o *
      H(Channel.posterior P q o) := by
  unfold mutualInfo
  have h := joint_entropy_identity q P
  linarith

end EntropyReduction

end TraceableAgency
