/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Behaviour.Preferences
import TraceableAgency.PureTrace.Behaviour.Conditions
import TraceableAgency.Info.Identities
import TraceableAgency.PureTrace.Support.Blackwell

/-!
# Mutual Information Preference

The benchmark preference family: q ≽_P q' ↔ I(q,P) ≥ I(q',P).
-/

namespace TraceableAgency

universe u v

/-- The mutual-information preference family.
    q ≽^I_P q' ↔ I_{q,P}(A;O) ≥ I_{q',P}(A;O) -/
noncomputable def MIPrefFamily : PrefFamily.{u} where
  rel := fun {A O} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A) =>
    mutualInfo q P ≥ mutualInfo q' P

/-- Predicate: F is represented by mutual information. -/
def PureTraceMIRepresentation (F : PrefFamily.{u}) : Prop :=
  ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A),
    F.rel P q q' ↔ mutualInfo q P ≥ mutualInfo q' P

theorem MIPrefFamily_is_MIRep : PureTraceMIRepresentation MIPrefFamily := by
  intro A O _ _ _ _ P q q'
  rfl

/-!
## Transfer from an arbitrary MI representation

If a preference family is extensionally represented by mutual information, every
occurrence of its relation can be replaced by the canonical MI preference
relation. These small lemmas keep the benchmark transfer explicit and avoid
fragile global rewriting through dependent block environments.
-/

/-- Relation transfer from an arbitrary `PureTraceMIRepresentation F` to the canonical MI family. -/
theorem rel_iff_MIPrefFamily_of_MIRep {F : PrefFamily.{u}} (hrep : PureTraceMIRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A) :
    F.rel P q q' ↔ MIPrefFamily.rel P q q' := by
  rw [hrep P q q']
  rfl

/-- Strict-relation transfer from an arbitrary `PureTraceMIRepresentation F` to the canonical MI family. -/
theorem strictRel_iff_MIPrefFamily_of_MIRep {F : PrefFamily.{u}} (hrep : PureTraceMIRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A) :
    F.strictRel P q q' ↔ MIPrefFamily.strictRel P q q' := by
  unfold PrefFamily.strictRel
  rw [rel_iff_MIPrefFamily_of_MIRep hrep P q q']
  rw [rel_iff_MIPrefFamily_of_MIRep hrep P q' q]

/-- Transfer for the bundled block-experiment predicate used in closed-graph condition. -/
theorem experimentPairPref_iff_MIPrefFamily_of_MIRep {F : PrefFamily.{u}} (hrep : PureTraceMIRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A]
    (E₁ E₂ : FiniteExperimentOn A) (q r : Dist A) :
    ExperimentPairPref F E₁ E₂ q r ↔
      ExperimentPairPref MIPrefFamily E₁ E₂ q r := by
  unfold ExperimentPairPref
  exact @rel_iff_MIPrefFamily_of_MIRep F hrep
    (A ⊕ A) (E₁.OutcomeType ⊕ E₂.OutcomeType)
    inferInstance inferInstance
    (@instFintypeSum E₁.OutcomeType E₂.OutcomeType E₁.outFintype E₂.outFintype)
    (@instDecidableEqSum E₁.OutcomeType E₂.OutcomeType E₁.outDecEq E₂.outDecEq)
    (blockExperimentChannel E₁ E₂) (inlDist q) (inrDist r)

/-!
## Strict Preference Characterization
-/

/-- MIPrefFamily strict preference is equivalent to strict MI inequality. -/
theorem MIPrefFamily_strictRel_iff_gt {A O : Type u}
    [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A) :
    MIPrefFamily.strictRel P q q' ↔ mutualInfo q P > mutualInfo q' P := by
  simp only [PrefFamily.strictRel, MIPrefFamily]
  constructor
  · intro ⟨hge, hnotge⟩
    by_contra hle
    push Not at hle
    exact hnotge hle
  · intro hgt
    exact ⟨le_of_lt hgt, not_le.mpr hgt⟩

/-!
## weak-order condition Benchmark Component

MIPrefFamily satisfies weak-order condition (Weak Order and Local Nontriviality).
-/

/-- MIPrefFamily is a weak order: MI comparison is complete and transitive. -/
theorem MIPrefFamily_isWeakOrder {A O : Type u}
    [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) : MIPrefFamily.IsWeakOrder P := by
  constructor
  · intro q q'
    simp only [MIPrefFamily]
    exact le_total (mutualInfo q' P) (mutualInfo q P)
  · intro q q' q''
    simp only [MIPrefFamily]
    intro hqq' hq'q''
    exact le_trans hq'q'' hqq'

/-- MIPrefFamily satisfies weak-order condition (Weak Order and Local Nontriviality). -/
theorem MIPrefFamily_weakOrderAndNontriviality : PureTraceWeakOrderAndNontriviality MIPrefFamily := by
  constructor
  · intro A O _ _ _ _ P
    exact MIPrefFamily_isWeakOrder P
  · intro A _ _ _ q hq
    rw [MIPrefFamily_strictRel_iff_gt]
    rw [mutualInfo_block_inl, mutualInfo_block_inr]
    rw [mutualInfo_idChannel', mutualInfo_uninformativeChannel]
    exact entropy_pos_of_fullSupport_nontrivial q hq

/-!
## block-coherence condition Benchmark Component

MIPrefFamily satisfies block-coherence condition (Block-Comparison Coherence).
-/

theorem MIPrefFamily_blockCoherence : PureTraceBlockCoherence MIPrefFamily := by
  refine
    { duplication := ?_
      finite_block := ?_ }
  · intro A O _ _ _ _ P q q'
    simp only [MIPrefFamily]
    rw [mutualInfo_block_inl P P q, mutualInfo_block_inr P P q']
  · intro K _ _ Act Out _ _ _ _ P i j _hij qᵢ qⱼ
    simp only [MIPrefFamily]
    rw [mutualInfo_blockFamily_embed Act Out P i qᵢ,
        mutualInfo_blockFamily_embed Act Out P j qⱼ,
        mutualInfo_block_inl (P i) (P j) qᵢ,
        mutualInfo_block_inr (P i) (P j) qⱼ]

/-!
## branch-continuation condition Benchmark Component

MIPrefFamily satisfies branch-continuation condition (Branchwise Continuation Monotonicity).
-/

/-- Weighted sum monotonicity: if weights are nonneg and pointwise ≥ holds for positive weights,
    then the weighted sum inequality holds. -/
theorem sum_mul_ge_sum_mul_of_nonneg_of_pos_imp
    {ι : Type*} [Fintype ι] (w x y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hxy : ∀ i, w i > 0 → x i ≥ y i) :
    ∑ i, w i * x i ≥ ∑ i, w i * y i := by
  apply Finset.sum_le_sum
  intro i _
  by_cases h : w i > 0
  · exact mul_le_mul_of_nonneg_left (hxy i h) (hw i)
  · push Not at h
    have hw_eq : w i = 0 := le_antisymm h (hw i)
    simp [hw_eq]

/-- Strict weighted sum monotonicity: if weights are nonneg, pointwise ≥ holds for positive weights,
    and one positive-weight index is strict, then the weighted sum is strict. -/
theorem sum_mul_gt_sum_mul_of_nonneg_of_exists_strict
    {ι : Type*} [Fintype ι] (w x y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hxy : ∀ i, w i > 0 → x i ≥ y i)
    (hstrict : ∃ i, w i > 0 ∧ x i > y i) :
    ∑ i, w i * x i > ∑ i, w i * y i := by
  have h_diff_nonneg : ∀ i, 0 ≤ w i * (x i - y i) := fun i => by
    by_cases h : w i > 0
    · exact mul_nonneg (hw i) (sub_nonneg.mpr (hxy i h))
    · push Not at h
      have hw_eq : w i = 0 := le_antisymm h (hw i)
      simp [hw_eq]
  obtain ⟨i₀, hi₀_pos, hi₀_strict⟩ := hstrict
  have h_diff_pos : 0 < w i₀ * (x i₀ - y i₀) :=
    mul_pos hi₀_pos (sub_pos.mpr hi₀_strict)
  have h_sum_pos : 0 < ∑ i, w i * (x i - y i) := by
    apply Finset.sum_pos'
    · intro i _
      exact h_diff_nonneg i
    · exact ⟨i₀, Finset.mem_univ i₀, h_diff_pos⟩
  calc ∑ i, w i * x i
      = ∑ i, (w i * y i + w i * (x i - y i)) := by
        congr 1; ext i; ring
    _ = ∑ i, w i * y i + ∑ i, w i * (x i - y i) := Finset.sum_add_distrib
    _ > ∑ i, w i * y i + 0 := by linarith
    _ = ∑ i, w i * y i := by ring

/-- Strong weak branch-continuation condition: branchwise weak preference implies aggregate weak preference.
    This is the auxiliary strong version with different Y and Z. -/
theorem MIPrefFamily_branchContinuationStrong_weak : ExpandedBranchContinuationWeak MIPrefFamily := by
  intro A O₁ _ _ _ _ _ Y Z _ _ _ _ q P₁ Q R h_branch
  simp only [MIPrefFamily]
  rw [mutualInfo_block_inl, mutualInfo_block_inr]
  rw [mutualInfo_seqComposeDep, mutualInfo_seqComposeDep]
  have h_cancel : mutualInfo q P₁ + ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (Q o₁) ≥
      mutualInfo q P₁ + ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (R o₁) ↔
      ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (Q o₁) ≥
      ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (R o₁) := by
    constructor <;> intro h <;> linarith
  rw [h_cancel]
  apply sum_mul_ge_sum_mul_of_nonneg_of_pos_imp
  · intro o₁
    exact (Channel.outcomeMarginal P₁ q).nonneg o₁
  · intro o₁ h_pos
    have h_branch_o₁ := h_branch o₁ h_pos
    simp only [MIPrefFamily, branchPosterior] at h_branch_o₁
    rw [mutualInfo_block_inl, mutualInfo_block_inr] at h_branch_o₁
    exact h_branch_o₁

/-- Strong strict branch-continuation condition: if one branch is strict, aggregate is strict.
    This is the auxiliary strong version with different Y and Z. -/
theorem MIPrefFamily_branchContinuationStrong_strict : ExpandedBranchContinuationStrict MIPrefFamily := by
  intro A O₁ _ _ _ _ _ Y Z _ _ _ _ q P₁ Q R h_branch h_strict
  rw [MIPrefFamily_strictRel_iff_gt]
  rw [mutualInfo_block_inl, mutualInfo_block_inr]
  rw [mutualInfo_seqComposeDep, mutualInfo_seqComposeDep]
  have h_cancel : mutualInfo q P₁ + ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (Q o₁) >
      mutualInfo q P₁ + ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (R o₁) ↔
      ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (Q o₁) >
      ∑ o₁, (Channel.outcomeMarginal P₁ q) o₁ *
        mutualInfo (Channel.posterior P₁ q o₁) (R o₁) := by
    constructor <;> intro h <;> linarith
  rw [h_cancel]
  apply sum_mul_gt_sum_mul_of_nonneg_of_exists_strict
  · intro o₁
    exact (Channel.outcomeMarginal P₁ q).nonneg o₁
  · intro o₁ h_pos
    have h_branch_o₁ := h_branch o₁ h_pos
    simp only [MIPrefFamily, branchPosterior] at h_branch_o₁
    rw [mutualInfo_block_inl, mutualInfo_block_inr] at h_branch_o₁
    exact h_branch_o₁
  · obtain ⟨o₀, h_pos₀, h_strict₀⟩ := h_strict
    use o₀
    constructor
    · exact h_pos₀
    · rw [MIPrefFamily_strictRel_iff_gt] at h_strict₀
      simp only [branchPosterior] at h_strict₀
      rw [mutualInfo_block_inl, mutualInfo_block_inr] at h_strict₀
      exact h_strict₀

/-- MIPrefFamily satisfies the strong branch-continuation condition (auxiliary). -/
theorem MIPrefFamily_branchContinuationStrong : ExpandedBranchContinuationMonotonicity MIPrefFamily :=
  ⟨MIPrefFamily_branchContinuationStrong_weak, MIPrefFamily_branchContinuationStrong_strict⟩

/-- Weak branch-continuation condition (paper-faithful): branchwise weak preference implies aggregate weak preference.
    Uses common branch outcome family O₂. -/
theorem MIPrefFamily_branchContinuation_weak : PureTraceBranchContinuationWeak MIPrefFamily :=
  (pureTraceBranchContinuation_of_expanded MIPrefFamily MIPrefFamily_branchContinuationStrong).1

/-- Strict branch-continuation condition (paper-faithful): if one branch is strict, aggregate is strict.
    Uses common branch outcome family O₂. -/
theorem MIPrefFamily_branchContinuation_strict : PureTraceBranchContinuationStrict MIPrefFamily :=
  (pureTraceBranchContinuation_of_expanded MIPrefFamily MIPrefFamily_branchContinuationStrong).2

/-- MIPrefFamily satisfies branch-continuation condition (paper-faithful Branchwise Continuation Monotonicity). -/
theorem MIPrefFamily_branchContinuation : PureTraceBranchContinuationMonotonicity MIPrefFamily :=
  pureTraceBranchContinuation_of_expanded MIPrefFamily MIPrefFamily_branchContinuationStrong

/-!
## Benchmark Background-Separability Consequence

Mutual-information preferences satisfy the derived background-separability
predicate used internally by the pure-trace proof.
-/

theorem MIPrefFamily_independentBackgroundSeparability :
    IndependentBackgroundSeparability MIPrefFamily := by
  constructor
  · intro A₁ A₂ O₁ O₂R O₂S _ _ _ _ _ _ _ _ _ _ q₁ q₂ _hq₁ _hq₂ P₁ Q₁ R₂ S₂
    simp only [MIPrefFamily]
    rw [mutualInfo_block_inl, mutualInfo_block_inr, mutualInfo_block_inl, mutualInfo_block_inr]
    exact mutualInfo_prod_same_background_left q₁ q₂ P₁ Q₁ R₂ S₂
  · intro A₁ A₂ O₁R O₁S O₂ _ _ _ _ _ _ _ _ _ _ q₁ q₂ _hq₁ _hq₂ R₁ S₁ P₂ Q₂
    simp only [MIPrefFamily]
    rw [mutualInfo_block_inl, mutualInfo_block_inr, mutualInfo_block_inl, mutualInfo_block_inr]
    exact mutualInfo_prod_same_background_right q₁ q₂ R₁ S₁ P₂ Q₂

/-!
## branch-continuation condition Benchmark Component

MIPrefFamily satisfies branch-continuation condition (Public-Coin Independence).

We need to prove that mutual information is affine in public-coin mixtures:
  I(q, t·P ⊕ (1-t)·R) = t·I(q,P) + (1-t)·I(q,R)

This then immediately gives the invariance:
  I(q,P) ≥ I(q,Q) ↔ I(q, t·P⊕(1-t)·R) ≥ I(q, t·Q⊕(1-t)·R)
-/

section PublicMixInfrastructure

variable {A O Y : Type u}
variable [Fintype A] [DecidableEq A]
variable [Fintype O] [DecidableEq O]
variable [Fintype Y] [DecidableEq Y]

/-- Entropy term scaling: entropyTerm(tx) = t*entropyTerm(x) + x*entropyTerm(t)
    for 0 < t < 1 and 0 ≤ x ≤ 1. -/
theorem entropyTerm_mul_const {t x : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hx0 : 0 ≤ x) (_hx1 : x ≤ 1) :
    entropyTerm (t * x) = t * entropyTerm x + x * entropyTerm t := by
  unfold entropyTerm
  by_cases hx_zero : x ≤ 0
  · have hx_eq : x = 0 := le_antisymm hx_zero hx0
    simp [hx_eq]
  · push Not at hx_zero
    have htx_pos : t * x > 0 := mul_pos ht0 hx_zero
    rw [if_neg (not_le.mpr htx_pos), if_neg (not_le.mpr hx_zero), if_neg (not_le.mpr ht0)]
    have htx_ne : t * x ≠ 0 := ne_of_gt htx_pos
    have ht_ne : t ≠ 0 := ne_of_gt ht0
    have hx_ne : x ≠ 0 := ne_of_gt hx_zero
    rw [Real.log_mul ht_ne hx_ne]
    ring

/-- Entropy term scaling for (1-t). -/
theorem entropyTerm_one_sub_mul_const {t x : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    entropyTerm ((1 - t) * x) = (1 - t) * entropyTerm x + x * entropyTerm (1 - t) := by
  have h1t0 : 0 < 1 - t := by linarith
  have h1t1 : 1 - t < 1 := by linarith
  exact entropyTerm_mul_const h1t0 h1t1 hx0 hx1

/-- Public-coin mixture distribution on O ⊕ Y. -/
noncomputable def publicMixDist
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (p : Dist O) (r : Dist Y) : Dist (O ⊕ Y) where
  prob := fun oy =>
    match oy with
    | Sum.inl o => t * p o
    | Sum.inr y => (1 - t) * r y
  nonneg := fun oy =>
    match oy with
    | Sum.inl o => mul_nonneg (le_of_lt ht0) (p.nonneg o)
    | Sum.inr y => mul_nonneg (by linarith) (r.nonneg y)
  sum_eq_one := by
    simp only [Fintype.sum_sum_type, ← Finset.mul_sum]
    rw [p.sum_eq_one, r.sum_eq_one]
    ring

@[simp]
theorem publicMixDist_inl (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (p : Dist O) (r : Dist Y) (o : O) :
    publicMixDist t ht0 ht1 p r (Sum.inl o) = t * p o := rfl

@[simp]
theorem publicMixDist_inr (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (p : Dist O) (r : Dist Y) (y : Y) :
    publicMixDist t ht0 ht1 p r (Sum.inr y) = (1 - t) * r y := rfl

/-- Entropy of public-coin mixture distribution. -/
theorem entropy_publicMixDist
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (p : Dist O) (r : Dist Y) :
    H(publicMixDist t ht0 ht1 p r) =
    entropyTerm t + entropyTerm (1 - t) + t * H(p) + (1 - t) * H(r) := by
  unfold entropy
  rw [Fintype.sum_sum_type]
  have h_inl : ∑ o : O, entropyTerm (publicMixDist t ht0 ht1 p r (Sum.inl o)) =
      entropyTerm t + t * ∑ o, entropyTerm (p o) := by
    simp only [publicMixDist_inl]
    have h : ∀ o, entropyTerm (t * p o) = t * entropyTerm (p o) + p o * entropyTerm t := fun o =>
      entropyTerm_mul_const ht0 ht1 (p.nonneg o) (p.prob_le_one o)
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, p.sum_eq_one, one_mul]
    ring
  have h_inr : ∑ y : Y, entropyTerm (publicMixDist t ht0 ht1 p r (Sum.inr y)) =
      entropyTerm (1 - t) + (1 - t) * ∑ y, entropyTerm (r y) := by
    simp only [publicMixDist_inr]
    have h : ∀ y, entropyTerm ((1 - t) * r y) =
        (1 - t) * entropyTerm (r y) + r y * entropyTerm (1 - t) := fun y =>
      entropyTerm_one_sub_mul_const ht0 ht1 (r.nonneg y) (r.prob_le_one y)
    simp_rw [h, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, r.sum_eq_one, one_mul]
    ring
  rw [h_inl, h_inr]
  ring

/-- Row of publicMixChannel equals publicMixDist of row distributions. -/
theorem publicMixChannel_row_eq_publicMixDist
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (R : Channel A Y) (a : A) :
    publicMixChannel t ht0 ht1 P R a = publicMixDist t ht0 ht1 (P a) (R a) := by
  ext oy
  cases oy with
  | inl o => simp [publicMixChannel, publicMixDist]
  | inr y => simp [publicMixChannel, publicMixDist]

/-- Entropy of publicMixChannel row. -/
theorem entropy_publicMixChannel_row
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (R : Channel A Y) (a : A) :
    H(publicMixChannel t ht0 ht1 P R a) =
    entropyTerm t + entropyTerm (1 - t) + t * H(P a) + (1 - t) * H(R a) := by
  rw [publicMixChannel_row_eq_publicMixDist]
  exact entropy_publicMixDist t ht0 ht1 (P a) (R a)

/-- Outcome marginal of publicMixChannel equals publicMixDist of marginals. -/
theorem outcomeMarginal_publicMixChannel
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (R : Channel A Y) :
    Channel.outcomeMarginal (publicMixChannel t ht0 ht1 P R) q =
    publicMixDist t ht0 ht1 (Channel.outcomeMarginal P q) (Channel.outcomeMarginal R q) := by
  ext oy
  cases oy with
  | inl o =>
    simp only [Channel.outcomeMarginal_apply, publicMixChannel, publicMixDist_inl,
               Channel.outcomeMarginal_apply]
    rw [Finset.mul_sum]
    congr 1; ext a; ring
  | inr y =>
    simp only [Channel.outcomeMarginal_apply, publicMixChannel, publicMixDist_inr,
               Channel.outcomeMarginal_apply]
    rw [Finset.mul_sum]
    congr 1; ext a; ring

/-- Mutual information is affine in public-coin mixtures. -/
theorem mutualInfo_publicMixChannel
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (R : Channel A Y) :
    mutualInfo q (publicMixChannel t ht0 ht1 P R) =
    t * mutualInfo q P + (1 - t) * mutualInfo q R := by
  unfold mutualInfo
  rw [outcomeMarginal_publicMixChannel, entropy_publicMixDist]
  have h_row : ∑ a, q a * H(publicMixChannel t ht0 ht1 P R a) =
      (entropyTerm t + entropyTerm (1 - t)) +
      t * ∑ a, q a * H(P a) + (1 - t) * ∑ a, q a * H(R a) := by
    have h : ∀ a, q a * H(publicMixChannel t ht0 ht1 P R a) =
        q a * (entropyTerm t + entropyTerm (1 - t)) +
        q a * (t * H(P a)) + q a * ((1 - t) * H(R a)) := fun a => by
      rw [entropy_publicMixChannel_row]; ring
    simp_rw [h, Finset.sum_add_distrib]
    have h_base : ∑ a, q a * (entropyTerm t + entropyTerm (1 - t)) =
        entropyTerm t + entropyTerm (1 - t) := by
      rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
    have hp : ∑ a, q a * (t * H(P a)) = t * ∑ a, q a * H(P a) := by
      rw [Finset.mul_sum]; congr 1; ext a; ring
    have hr : ∑ a, q a * ((1 - t) * H(R a)) = (1 - t) * ∑ a, q a * H(R a) := by
      rw [Finset.mul_sum]; congr 1; ext a; ring
    rw [h_base, hp, hr]
  rw [h_row]
  ring

/-- Public-mix common background comparison invariance. -/
theorem mutualInfo_publicMix_common_background_iff
    {O_P O_Q O_R : Type u}
    [Fintype O_P] [DecidableEq O_P]
    [Fintype O_Q] [DecidableEq O_Q]
    [Fintype O_R] [DecidableEq O_R]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O_P) (Q : Channel A O_Q) (R : Channel A O_R) :
    mutualInfo q P ≥ mutualInfo q Q ↔
    mutualInfo q (publicMixChannel t ht0 ht1 P R) ≥
      mutualInfo q (publicMixChannel t ht0 ht1 Q R) := by
  rw [mutualInfo_publicMixChannel, mutualInfo_publicMixChannel]
  constructor <;> intro h <;> nlinarith

end PublicMixInfrastructure

/-!
## closed-graph condition Benchmark Component

MIPrefFamily satisfies closed-graph condition (Continuity).

closed-graph condition has two parts:
1. Closed preference graph under sequential coordinatewise convergence
2. Posterior-law continuity for block comparisons

We avoid channel topology by working directly with ChannelConverges and DistConverges.
-/

section ClosedGraphInfrastructure

open Filter Topology

variable {A O : Type u}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype O] [DecidableEq O]

/-!
### Entropy Reduction via Posterior Law Integral
-/

/-- Entropy reduction in terms of posteriorLawIntegral. -/
theorem mutualInfo_eq_entropy_sub_posteriorLawIntegral (q : Dist A) (P : Channel A O) :
    mutualInfo q P = H(q) - posteriorLawIntegral q P entropy := by
  unfold posteriorLawIntegral
  exact mutualInfo_entropyReduction q P

/-- Entropy reduction for experiments. -/
theorem mutualInfo_entropyReductionExp (q : Dist A) (E : FiniteExperimentOn A) :
    @mutualInfo A E.OutcomeType _ E.outFintype q E.P =
    H(q) - posteriorLawIntegralExp q E entropy := by
  unfold posteriorLawIntegralExp
  exact @mutualInfo_entropyReduction A E.OutcomeType _ _ _ E.outFintype E.outDecEq q E.P

/-!
### Direct Sequential Continuity of Mutual Information

We prove that MI converges under coordinatewise convergence of distributions and channels,
without defining a topology on Channel A O.
-/

/-- Outcome marginal converges under dist and channel convergence. -/
theorem tendsto_outcomeMarginal_of_converges
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) (o : O) :
    Tendsto (fun n => (Channel.outcomeMarginal (Pₙ n) (qₙ n)) o) atTop
            (𝓝 ((Channel.outcomeMarginal P q) o)) := by
  simp only [Channel.outcomeMarginal_apply]
  apply tendsto_finsetSum
  intro a _
  apply Tendsto.mul (hq a) (hP a o)

/-- Entropy of outcome marginal converges. -/
theorem tendsto_entropy_outcomeMarginal_of_converges
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) :
    Tendsto (fun n => H(Channel.outcomeMarginal (Pₙ n) (qₙ n))) atTop
            (𝓝 (H(Channel.outcomeMarginal P q))) := by
  unfold entropy
  apply tendsto_finsetSum
  intro o _
  apply continuous_entropyTerm.continuousAt.tendsto.comp
  exact tendsto_outcomeMarginal_of_converges Pₙ P qₙ q hP hq o

/-- Channel row entropy converges. -/
theorem tendsto_entropy_channel_row_of_converges
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (hP : ChannelConverges Pₙ P) (a : A) :
    Tendsto (fun n => H(Pₙ n a)) atTop (𝓝 (H(P a))) := by
  unfold entropy
  apply tendsto_finsetSum
  intro o _
  apply continuous_entropyTerm.continuousAt.tendsto.comp
  exact hP a o

/-- Conditional entropy sum converges. -/
theorem tendsto_condEntropySum_of_converges
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) :
    Tendsto (fun n => ∑ a, (qₙ n) a * H(Pₙ n a)) atTop
            (𝓝 (∑ a, q a * H(P a))) := by
  apply tendsto_finsetSum
  intro a _
  apply Tendsto.mul (hq a)
  exact tendsto_entropy_channel_row_of_converges Pₙ P hP a

/-- Mutual information converges under dist and channel convergence. -/
theorem tendsto_mutualInfo_of_converges
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) :
    Tendsto (fun n => mutualInfo (qₙ n) (Pₙ n)) atTop (𝓝 (mutualInfo q P)) := by
  unfold mutualInfo
  apply Tendsto.sub
  · exact tendsto_entropy_outcomeMarginal_of_converges Pₙ P qₙ q hP hq
  · exact tendsto_condEntropySum_of_converges Pₙ P qₙ q hP hq

end ClosedGraphInfrastructure

/-!
### Closed Preference Graph
-/

section ClosedGraphNonemptyFree

open Filter Topology

variable {A O : Type u}
variable [Fintype A] [DecidableEq A]
variable [Fintype O] [DecidableEq O]

/-- Outcome marginal converges under dist and channel convergence. -/
theorem tendsto_outcomeMarginal_of_converges'
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) (o : O) :
    Tendsto (fun n => (Channel.outcomeMarginal (Pₙ n) (qₙ n)) o) atTop
            (𝓝 ((Channel.outcomeMarginal P q) o)) := by
  simp only [Channel.outcomeMarginal_apply]
  apply tendsto_finsetSum
  intro a _
  apply Tendsto.mul (hq a) (hP a o)

/-- Entropy of outcome marginal converges (no Nonempty requirement). -/
theorem tendsto_entropy_outcomeMarginal_of_converges'
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) :
    Tendsto (fun n => H(Channel.outcomeMarginal (Pₙ n) (qₙ n))) atTop
            (𝓝 (H(Channel.outcomeMarginal P q))) := by
  unfold entropy
  apply tendsto_finsetSum
  intro o _
  apply continuous_entropyTerm.continuousAt.tendsto.comp
  exact tendsto_outcomeMarginal_of_converges' Pₙ P qₙ q hP hq o

/-- Channel row entropy converges (no Nonempty requirement). -/
theorem tendsto_entropy_channel_row_of_converges'
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (hP : ChannelConverges Pₙ P) (a : A) :
    Tendsto (fun n => H(Pₙ n a)) atTop (𝓝 (H(P a))) := by
  unfold entropy
  apply tendsto_finsetSum
  intro o _
  apply continuous_entropyTerm.continuousAt.tendsto.comp
  exact hP a o

/-- Conditional entropy sum converges (no Nonempty requirement). -/
theorem tendsto_condEntropySum_of_converges'
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) :
    Tendsto (fun n => ∑ a, (qₙ n) a * H(Pₙ n a)) atTop
            (𝓝 (∑ a, q a * H(P a))) := by
  apply tendsto_finsetSum
  intro a _
  apply Tendsto.mul (hq a)
  exact tendsto_entropy_channel_row_of_converges' Pₙ P hP a

/-- Mutual information converges (no Nonempty requirement). -/
theorem tendsto_mutualInfo_of_converges'
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ : ℕ → Dist A) (q : Dist A)
    (hP : ChannelConverges Pₙ P) (hq : DistConverges qₙ q) :
    Tendsto (fun n => mutualInfo (qₙ n) (Pₙ n)) atTop (𝓝 (mutualInfo q P)) := by
  unfold mutualInfo
  apply Tendsto.sub
  · exact tendsto_entropy_outcomeMarginal_of_converges' Pₙ P qₙ q hP hq
  · exact tendsto_condEntropySum_of_converges' Pₙ P qₙ q hP hq

end ClosedGraphNonemptyFree

/-- MIPrefFamily has closed preference graph under coordinatewise convergence. -/
theorem MIPrefFamily_closedPreferenceGraph : ClosedPreferenceGraph MIPrefFamily := by
  intro A O instFA instDA instFO instDO Pₙ P qₙ rₙ q r hP hq hr h_ineq
  simp only [MIPrefFamily] at h_ineq ⊢
  have h_left := tendsto_mutualInfo_of_converges' Pₙ P qₙ q hP hq
  have h_right := tendsto_mutualInfo_of_converges' Pₙ P rₙ r hP hr
  exact le_of_tendsto_of_tendsto h_right h_left (Filter.Eventually.of_forall h_ineq)

/-!
### Posterior-Law Continuity Clause

For the second part of closed-graph condition, we use entropy reduction plus weak convergence against H.
-/

section PosteriorLawContinuity

open Filter Topology

variable {A : Type u}
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Helper: if posteriorLawIntegralExp with test function H converges,
    then MI values converge. -/
theorem tendsto_mutualInfo_of_posteriorLaw_entropy_converges
    (q : Dist A) (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A)
    (h : Tendsto (fun n => posteriorLawIntegralExp q (Eₙ n) entropy) atTop
                 (𝓝 (posteriorLawIntegralExp q E entropy))) :
    Tendsto (fun n => @mutualInfo A (Eₙ n).OutcomeType _ (Eₙ n).outFintype q (Eₙ n).P)
            atTop
            (𝓝 (@mutualInfo A E.OutcomeType _ E.outFintype q E.P)) := by
  have h_Eₙ : ∀ n, @mutualInfo A (Eₙ n).OutcomeType _ (Eₙ n).outFintype q (Eₙ n).P =
      H(q) - posteriorLawIntegralExp q (Eₙ n) entropy := fun n =>
    mutualInfo_entropyReductionExp q (Eₙ n)
  have h_E : @mutualInfo A E.OutcomeType _ E.outFintype q E.P =
      H(q) - posteriorLawIntegralExp q E entropy := mutualInfo_entropyReductionExp q E
  simp_rw [h_Eₙ, h_E]
  exact Tendsto.const_sub _ h

end PosteriorLawContinuity

/-- MIPrefFamily satisfies posterior-law continuity (paper `lem:plcont`).  This is
the benchmark witness of the derived predicate `PosteriorLawContinuity`; for the
MI family it also holds directly from entropy reduction and continuity of `H`. -/
theorem MIPrefFamily_posteriorLawContinuity :
    PosteriorLawContinuity MIPrefFamily := by
  intro A instFA instDA instNA q _hq Eₙ E Fₙ G hE hF h_ineq
  simp only [ExperimentPairPref, MIPrefFamily] at h_ineq ⊢
  letI instFO_E := E.outFintype
  letI instFO_G := G.outFintype
  letI instDO_E := E.outDecEq
  letI instDO_G := G.outDecEq
  unfold blockExperimentChannel at h_ineq ⊢
  rw [mutualInfo_block_inl, mutualInfo_block_inr]
  have h_ineq' : ∀ n, @mutualInfo A (Eₙ n).OutcomeType _ (Eₙ n).outFintype q (Eₙ n).P ≥
      @mutualInfo A (Fₙ n).OutcomeType _ (Fₙ n).outFintype q (Fₙ n).P := by
    intro n
    letI := (Eₙ n).outFintype
    letI := (Fₙ n).outFintype
    letI := (Eₙ n).outDecEq
    letI := (Fₙ n).outDecEq
    have := h_ineq n
    rw [mutualInfo_block_inl, mutualInfo_block_inr] at this
    exact this
  have hE_entropy := hE entropy continuous_entropy
  have hF_entropy := hF entropy continuous_entropy
  have h_left := @tendsto_mutualInfo_of_posteriorLaw_entropy_converges A _ _ instNA q Eₙ E hE_entropy
  have h_right := @tendsto_mutualInfo_of_posteriorLaw_entropy_converges A _ _ instNA q Fₙ G hF_entropy
  exact le_of_tendsto_of_tendsto h_right h_left (Filter.Eventually.of_forall h_ineq')

/-- `MIPrefFamily` satisfies the closed-graph condition.  Posterior-law
continuity is the separate derived result
`MIPrefFamily_posteriorLawContinuity`. -/
theorem MIPrefFamily_closedGraph : PureTraceClosedGraph MIPrefFamily :=
  MIPrefFamily_closedPreferenceGraph

/-!
## record-processing condition and action-processing condition: Internally proved data processing

The remaining axioms record-processing condition (outcome post-processing aversion) and action-processing condition (action coarsening
aversion) follow from the finite data-processing theorems proved in
`TraceableAgency.Info.DataProcessing`.
-/

section DataProcessing

/-- MIPrefFamily satisfies record-processing condition (Outcome Post-processing Aversion).

record-processing condition requires: for any P : A → Δ(O), T : O → Δ(O'), q ∈ Δ(A),
  q^0 ≽_{P ⊔ PT} q^1

For MIPrefFamily this becomes: I(q, P) ≥ I(q, P∘T),
which is exactly the outcome post-processing DPI. -/
theorem MIPrefFamily_recordProcessing :
    PureTraceRecordProcessing.{v} MIPrefFamily := by
  unfold PureTraceRecordProcessing
  intro A O O' _ _ _ _ _ _ P T q
  simp only [MIPrefFamily]
  rw [mutualInfo_block_inl, mutualInfo_block_inr]
  exact mutualInfo_outcome_postprocess_le q P T

/-- MIPrefFamily satisfies action-processing condition (Action Coarsening Aversion).

action-processing condition requires: for S : A → Δ(A'), P : A → Δ(O), q ∈ Δ(A), and valid completion P̂,
  q^0 ≽_{P ⊔ P̂} (qS)^1

For MIPrefFamily this becomes: I(q, P) ≥ I(qS, P̂),
which is exactly the action Bayes-pushforward DPI. -/
theorem MIPrefFamily_actionProcessing :
    PureTraceActionProcessing.{v} MIPrefFamily := by
  unfold PureTraceActionProcessing
  intro A A' O _ _ _ _ _ _ _ P q S P_hat hcompl
  simp only [MIPrefFamily]
  rw [mutualInfo_block_inl, mutualInfo_block_inr]
  exact mutualInfo_action_bayes_pushforward_le P q S P_hat hcompl

/-- MIPrefFamily satisfies all PureTraceConditions. -/
theorem MIPrefFamily_conditions :
    PureTraceConditions.{v} MIPrefFamily :=
  { weakOrder := MIPrefFamily_weakOrderAndNontriviality
    closedGraph := MIPrefFamily_closedGraph
    blockCoherence := MIPrefFamily_blockCoherence
    recordProcessing := MIPrefFamily_recordProcessing.{v}
    actionProcessing := MIPrefFamily_actionProcessing.{v}
    branchContinuation := MIPrefFamily_branchContinuation }

/-- Any mutual-information representation satisfies weak-order condition. -/
theorem MIRep_weakOrderAndNontriviality {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    PureTraceWeakOrderAndNontriviality F := by
  constructor
  · intro A O _ _ _ _ P
    constructor
    · intro q q'
      rcases (MIPrefFamily_weakOrderAndNontriviality.1 P).1 q q' with h | h
      · exact Or.inl ((rel_iff_MIPrefFamily_of_MIRep hrep P q q').mpr h)
      · exact Or.inr ((rel_iff_MIPrefFamily_of_MIRep hrep P q' q).mpr h)
    · intro q q' q'' hqq' hq'q''
      apply (rel_iff_MIPrefFamily_of_MIRep hrep P q q'').mpr
      exact (MIPrefFamily_weakOrderAndNontriviality.1 P).2 q q' q''
        ((rel_iff_MIPrefFamily_of_MIRep hrep P q q').mp hqq')
        ((rel_iff_MIPrefFamily_of_MIRep hrep P q' q'').mp hq'q'')
  · intro A _ _ _ q hq
    apply (strictRel_iff_MIPrefFamily_of_MIRep hrep _ _ _).mpr
    exact MIPrefFamily_weakOrderAndNontriviality.2 q hq

/-- Any mutual-information representation satisfies closed-graph condition (= `ClosedPreferenceGraph`). -/
theorem MIRep_closedGraph {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    PureTraceClosedGraph F := by
  intro A O _ _ _ _ Pₙ P qₙ rₙ q r hP hq hr hrel
  apply (rel_iff_MIPrefFamily_of_MIRep hrep P q r).mpr
  apply MIPrefFamily_closedGraph Pₙ P qₙ rₙ q r hP hq hr
  intro n
  exact (rel_iff_MIPrefFamily_of_MIRep hrep (Pₙ n) (qₙ n) (rₙ n)).mp (hrel n)

/-- Any mutual-information representation satisfies posterior-law continuity
(paper `lem:plcont`).  This transfers `MIPrefFamily_posteriorLawContinuity`
across the ordinal equivalence of `PureTraceMIRepresentation`. -/
theorem MIRep_posteriorLawContinuity {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    PosteriorLawContinuity F := by
  intro A _ _ _ q hq Eₙ E Fₙ G hE hF hrel
  apply (experimentPairPref_iff_MIPrefFamily_of_MIRep hrep E G q q).mpr
  apply MIPrefFamily_posteriorLawContinuity q hq Eₙ E Fₙ G hE hF
  intro n
  exact (experimentPairPref_iff_MIPrefFamily_of_MIRep hrep (Eₙ n) (Fₙ n) q q).mp
    (hrel n)

/-- Any mutual-information representation satisfies block-coherence condition. -/
theorem MIRep_blockCoherence {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    PureTraceBlockCoherence F := by
  refine
    { duplication := ?_
      finite_block := ?_ }
  · intro A O _ _ _ _ P q q'
    constructor
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep (blockChannel P P) (inlDist q) (inrDist q')).mpr
      exact (MIPrefFamily_blockCoherence.duplication P q q').mp
        ((rel_iff_MIPrefFamily_of_MIRep hrep P q q').mp h)
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep P q q').mpr
      exact (MIPrefFamily_blockCoherence.duplication P q q').mpr
        ((rel_iff_MIPrefFamily_of_MIRep hrep (blockChannel P P) (inlDist q) (inrDist q')).mp h)
  · intro K _ _ Act Out _ _ _ _ P i j hij qᵢ qⱼ
    constructor
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep
        (blockChannel (P i) (P j)) (inlDist qᵢ) (inrDist qⱼ)).mpr
      exact (MIPrefFamily_blockCoherence.finite_block Act Out P i j hij qᵢ qⱼ).mp
        ((rel_iff_MIPrefFamily_of_MIRep hrep
          (blockFamilyChannel Act Out P)
          (blockEmbedDist Act i qᵢ)
          (blockEmbedDist Act j qⱼ)).mp h)
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep
        (blockFamilyChannel Act Out P)
        (blockEmbedDist Act i qᵢ)
        (blockEmbedDist Act j qⱼ)).mpr
      exact (MIPrefFamily_blockCoherence.finite_block Act Out P i j hij qᵢ qⱼ).mpr
        ((rel_iff_MIPrefFamily_of_MIRep hrep
          (blockChannel (P i) (P j)) (inlDist qᵢ) (inrDist qⱼ)).mp h)
/-- Any mutual-information representation satisfies record-processing condition. -/
theorem MIRep_recordProcessing {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    PureTraceRecordProcessing F := by
  intro A O O' _ _ _ _ _ _ P T q
  apply (rel_iff_MIPrefFamily_of_MIRep hrep
    (blockChannel P (Channel.postprocess P T)) (inlDist q) (inrDist q)).mpr
  exact MIPrefFamily_recordProcessing P T q

/-- Any mutual-information representation satisfies action-processing condition. -/
theorem MIRep_actionProcessing {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    PureTraceActionProcessing F := by
  intro A A' O _ _ _ _ _ _ _ P q S P_hat hcompl
  apply (rel_iff_MIPrefFamily_of_MIRep hrep
    (blockChannel P P_hat) (inlDist q) (inrDist (Channel.actionPushforward q S))).mpr
  exact MIPrefFamily_actionProcessing P q S P_hat hcompl

/-- Any mutual-information representation satisfies branch-continuation condition. -/
theorem MIRep_branchContinuation {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    PureTraceBranchContinuationMonotonicity F := by
  constructor
  · intro A O₁ _ _ _ _ _ O₂ _ _ q P₁ Q R hbranch
    apply (rel_iff_MIPrefFamily_of_MIRep hrep
      (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q)).mpr
    apply MIPrefFamily_branchContinuation_weak O₂ q P₁ Q R
    intro o₁ hpos
    exact (rel_iff_MIPrefFamily_of_MIRep hrep
      (blockChannel (Q o₁) (R o₁))
      (inlDist (branchPosterior P₁ q o₁))
      (inrDist (branchPosterior P₁ q o₁))).mp (hbranch o₁ hpos)
  · intro A O₁ _ _ _ _ _ O₂ _ _ q P₁ Q R hbranch hstrict
    apply (strictRel_iff_MIPrefFamily_of_MIRep hrep
      (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q)).mpr
    apply MIPrefFamily_branchContinuation_strict O₂ q P₁ Q R
    · intro o₁ hpos
      exact (rel_iff_MIPrefFamily_of_MIRep hrep
        (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁))
        (inrDist (branchPosterior P₁ q o₁))).mp (hbranch o₁ hpos)
    · rcases hstrict with ⟨o₁, hpos, hstr⟩
      exact ⟨o₁, hpos,
        (strictRel_iff_MIPrefFamily_of_MIRep hrep
          (blockChannel (Q o₁) (R o₁))
          (inlDist (branchPosterior P₁ q o₁))
          (inrDist (branchPosterior P₁ q o₁))).mp hstr⟩

/-- Any mutual-information representation satisfies the legacy background
separability predicate. -/
theorem MIRep_independentBackgroundSeparability
    {F : PrefFamily.{v}} (hrep : PureTraceMIRepresentation F) :
    IndependentBackgroundSeparability F := by
  constructor
  · intro A₁ A₂ O₁ O₂R O₂S _ _ _ _ _ _ _ _ _ _ q₁ q₂ hq₁ hq₂ P₁ Q₁ R₂ S₂
    let prodPR := prodChannel P₁ R₂
    let prodQR := prodChannel Q₁ R₂
    let prodPS := prodChannel P₁ S₂
    let prodQS := prodChannel Q₁ S₂
    let prodQ := prodDist q₁ q₂
    constructor
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep
        (blockChannel prodPS prodQS) (inlDist prodQ) (inrDist prodQ)).mpr
      exact (MIPrefFamily_independentBackgroundSeparability.1
        q₁ q₂ hq₁ hq₂ P₁ Q₁ R₂ S₂).mp
        ((rel_iff_MIPrefFamily_of_MIRep hrep
          (blockChannel prodPR prodQR) (inlDist prodQ) (inrDist prodQ)).mp h)
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep
        (blockChannel prodPR prodQR) (inlDist prodQ) (inrDist prodQ)).mpr
      exact (MIPrefFamily_independentBackgroundSeparability.1
        q₁ q₂ hq₁ hq₂ P₁ Q₁ R₂ S₂).mpr
        ((rel_iff_MIPrefFamily_of_MIRep hrep
          (blockChannel prodPS prodQS) (inlDist prodQ) (inrDist prodQ)).mp h)
  · intro A₁ A₂ O₁R O₁S O₂ _ _ _ _ _ _ _ _ _ _ q₁ q₂ hq₁ hq₂ R₁ S₁ P₂ Q₂
    let prodRP := prodChannel R₁ P₂
    let prodRQ := prodChannel R₁ Q₂
    let prodSP := prodChannel S₁ P₂
    let prodSQ := prodChannel S₁ Q₂
    let prodQ := prodDist q₁ q₂
    constructor
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep
        (blockChannel prodSP prodSQ) (inlDist prodQ) (inrDist prodQ)).mpr
      exact (MIPrefFamily_independentBackgroundSeparability.2
        q₁ q₂ hq₁ hq₂ R₁ S₁ P₂ Q₂).mp
        ((rel_iff_MIPrefFamily_of_MIRep hrep
          (blockChannel prodRP prodRQ) (inlDist prodQ) (inrDist prodQ)).mp h)
    · intro h
      apply (rel_iff_MIPrefFamily_of_MIRep hrep
        (blockChannel prodRP prodRQ) (inlDist prodQ) (inrDist prodQ)).mpr
      exact (MIPrefFamily_independentBackgroundSeparability.2
        q₁ q₂ hq₁ hq₂ R₁ S₁ P₂ Q₂).mpr
        ((rel_iff_MIPrefFamily_of_MIRep hrep
          (blockChannel prodSP prodSQ) (inlDist prodQ) (inrDist prodQ)).mp h)

/-- Necessity/benchmark transfer: every MI-representable family satisfies the
axioms. -/
theorem MIRep_conditions
    (F : PrefFamily.{v}) (hrep : PureTraceMIRepresentation F) :
    PureTraceConditions F :=
  { weakOrder := MIRep_weakOrderAndNontriviality hrep
    closedGraph := MIRep_closedGraph hrep
    blockCoherence := MIRep_blockCoherence hrep
    recordProcessing := MIRep_recordProcessing hrep
    actionProcessing := MIRep_actionProcessing hrep
    branchContinuation := MIRep_branchContinuation hrep }

end DataProcessing

end TraceableAgency
