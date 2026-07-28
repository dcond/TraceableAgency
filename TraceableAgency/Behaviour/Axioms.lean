/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Behaviour.Preferences
import TraceableAgency.Basic.Blocks
import TraceableAgency.Basic.Products
import TraceableAgency.Basic.Sequential
import TraceableAgency.Basic.Convergence

/-!
# Axioms A1-A6

The behavioural axioms for traceable agency from `empowerment_v7.tex`.
Each axiom is a predicate on `PrefFamily`:

- A1: weak order and local non-triviality;
- A2: closed preference graph;
- A3: finite block-comparison coherence;
- A4: outcome post-processing aversion;
- A5: action-coarsening aversion;
- A6: branchwise continuation monotonicity.

Public-coin independence and independent-background separability are not
primitive.  The latter's v6 predicate is retained below as a named derived
consequence for compatibility and is proved from A1/A3--A6 in
`External/EntropyReduction.lean`.
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

variable (F : PrefFamily.{u})

/-- Pure relational replacement by two-sided weak equivalence.  This elementary
lemma lives with the behavioural primitives so structural relabelling can be
derived without importing any downstream sufficiency file. -/
theorem rel_replace_by_equiv
    {α : Type*} (R : α → α → Prop)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    {x x' y y' : α}
    (hxx' : R x x') (hx'x : R x' x)
    (hyy' : R y y') (hy'y : R y' y) :
    (R x y ↔ R x' y') := by
  constructor
  · intro hxy
    exact htrans x' y y' (htrans x' x y hx'x hxy) hyy'
  · intro hx'y'
    exact htrans x y' y (htrans x x' y' hxx' hx'y') hy'y

/-!
## A1: Weak Order and Local Non-triviality

Paper (lines 410-416):
For every finite channel P:A→Δ(O), ≽_P is complete and transitive on Δ(A).
For |A|≥2 and full-support q: q^0 ≻_{Id_A ⊔ U_A} q^1.
-/

def A1_WeakOrderLocalNontriviality : Prop :=
  (∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
     (P : Channel A O), F.IsWeakOrder P) ∧
  (∀ {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
     (q : Dist A), q.FullSupport →
     let P_id : Channel A A := Channel.idChannel
     let P_uninf : Channel A Unit := Channel.uninformativeChannel A
     let blockP := blockChannel P_id P_uninf
     F.strictRel blockP (inlDist q) (inrDist q))

/-!
## A2: Continuity

Paper `empowerment_v7.tex` (Axiom A2): the set {(P,q,q') : q ≽_P q'} is closed.

**Change from v5 → v6.** In v5 Axiom A2 had a second clause — continuity of block
comparisons under posterior-law convergence at a fixed full-support prior.  In v6
that clause is **demoted to a derived lemma** (`lem:plcont`): it follows from the
primitive first clause together with A1, A3, A4.  Accordingly `A2_Continuity` is
now just `ClosedPreferenceGraph`.  The derived predicate `PosteriorLawContinuity`
is retained as a standalone notion for internal interfaces, and any place that
used to project `hax.a2.2` now takes a supplied `PosteriorLawContinuity F`
instead.

Note: P_n, Q_n may have different outcome alphabets (paper allows comparing
channels on same action set with different outcome sets). We use FiniteExperimentOn
to bundle each (Oₙ, Pₙ) into a single structure.
-/

def ClosedPreferenceGraph : Prop :=
  ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (qₙ rₙ : ℕ → Dist A) (q r : Dist A),
    ChannelConverges Pₙ P →
    DistConverges qₙ q →
    DistConverges rₙ r →
    (∀ n, F.rel (Pₙ n) (qₙ n) (rₙ n)) →
    F.rel P q r

/-- Helper: build the block channel for a pair of experiments on the same action type A.
    The block channel has type Channel (A ⊕ A) (O₁ ⊕ O₂). -/
noncomputable def blockExperimentChannel {A : Type u} [Fintype A]
    (E₁ E₂ : FiniteExperimentOn A) :
    @Channel (A ⊕ A) (E₁.OutcomeType ⊕ E₂.OutcomeType)
      (@instFintypeSum E₁.OutcomeType E₂.OutcomeType E₁.outFintype E₂.outFintype) :=
  @blockChannel A A E₁.OutcomeType E₂.OutcomeType E₁.outFintype E₂.outFintype E₁.P E₂.P

/-- Predicate for experiment-pair preference at a prior q.
    This wraps blockExperimentChannel usage with proper instance handling. -/
def ExperimentPairPref (F : PrefFamily.{u}) {A : Type u} [Fintype A] [DecidableEq A]
    (E₁ E₂ : FiniteExperimentOn A) (q r : Dist A) : Prop :=
  @F.rel (A ⊕ A) (E₁.OutcomeType ⊕ E₂.OutcomeType)
    inferInstance inferInstance
    (@instFintypeSum E₁.OutcomeType E₂.OutcomeType E₁.outFintype E₂.outFintype)
    (@instDecidableEqSum E₁.OutcomeType E₂.OutcomeType E₁.outDecEq E₂.outDecEq)
    (blockExperimentChannel E₁ E₂)
    (inlDist q) (inrDist r)

def A2_Continuity (F : PrefFamily.{u}) : Prop :=
  ClosedPreferenceGraph F

/-- **Posterior-law continuity** (paper `lem:plcont`), the clause that was A2's
second conjunct in v5.  In v6 it is a *derived* notion, not an axiom.  It is kept
here as a standalone predicate so downstream files that previously consumed
`hax.a2.2` can take a supplied `PosteriorLawContinuity F` instead. -/
def PosteriorLawContinuity (F : PrefFamily.{u}) : Prop :=
  ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (_hq : q.FullSupport)
    (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A)
    (Fₙ : ℕ → FiniteExperimentOn A) (G : FiniteExperimentOn A),
    PosteriorLawConvergesAtExp q Eₙ E →
    PosteriorLawConvergesAtExp q Fₙ G →
    (∀ n, ExperimentPairPref F (Eₙ n) (Fₙ n) q q) →
    ExperimentPairPref F E G q q

/-!
## A3: Block-Comparison Coherence

Paper (lines 448-463):
1. q ≽_P q' ↔ q^0 ≽_{P ⊔ P} (q')^1
2. For any finite block environment ⨆_{k∈K} P_k, distinct blocks i,j, and
   q_i ∈ Δ(A_i), q_j ∈ Δ(A_j):
     q_i^i ≽_{⨆_k P_k} q_j^j ↔ q_i^0 ≽_{P_i ⊔ P_j} q_j^1
-/

structure A3_BlockComparisonCoherence : Prop where
  duplication :
    ∀ {A O : Type u} [Fintype A] [DecidableEq A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q q' : Dist A),
      F.rel P q q' ↔
        F.rel (blockChannel P P) (inlDist q) (inrDist q')
  finite_block :
    ∀ {K : Type u} [Fintype K] [DecidableEq K]
      (Act : K → Type u) (Out : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
      (P : ∀ k, Channel (Act k) (Out k))
      (i j : K) (hij : i ≠ j)
      (qᵢ : Dist (Act i)) (qⱼ : Dist (Act j)),
      F.rel (blockFamilyChannel Act Out P)
          (blockEmbedDist Act i qᵢ)
          (blockEmbedDist Act j qⱼ)
        ↔
      F.rel (blockChannel (P i) (P j))
          (inlDist qᵢ)
          (inrDist qⱼ)

/-!
## A4: Outcome Post-processing Aversion

Paper (lines 469-473):
For any P:A→Δ(O), T:O→Δ(O'), and q∈Δ(A): q^0 ≽_{P ⊔ PT} q^1.
-/

def A4_OutcomePostprocessingAversion : Prop :=
  ∀ {A O O' : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    [Fintype O'] [DecidableEq O']
    (P : Channel A O) (T : Channel O O') (q : Dist A),
    F.rel (blockChannel P (Channel.postprocess P T)) (inlDist q) (inrDist q)

/-!
## A5: Action-Coarsening Aversion

Paper (lines 478-486):
For S:A→Δ(A'), P:A→Δ(O), q∈Δ(A), and every completion P̂ of S^q P:
  q^0 ≽_{P ⊔ P̂} (qS)^1.
-/

def A5_ActionCoarseningAversion : Prop :=
  ∀ {A A' O : Type u} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    [Fintype O] [DecidableEq O] [Nonempty A]
    (P : Channel A O) (q : Dist A) (S : Channel.ActionKernel A A')
    (P_hat : Channel A' O),
    Channel.IsBayesPushforwardCompletion P q S P_hat →
    F.rel (blockChannel P P_hat) (inlDist q) (inrDist (Channel.actionPushforward q S))

/-!
## Public-coin channel

Public-coin independence is not an axiom in v6.  The channel constructor is
kept here because `lem:publiccoin` is derived later from A1, A3, A4, and the
weak/strict clauses of branchwise continuation monotonicity.
-/

noncomputable def publicMixChannel {A O_P O_Q : Type u}
    [Fintype A] [Fintype O_P] [Fintype O_Q]
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O_P) (Q : Channel A O_Q) : Channel A (O_P ⊕ O_Q) :=
  fun a =>
    { prob := fun oy =>
        match oy with
        | Sum.inl o => t * P a o
        | Sum.inr y => (1 - t) * Q a y
      nonneg := fun oy =>
        match oy with
        | Sum.inl o => mul_nonneg (le_of_lt ht0) ((P a).nonneg o)
        | Sum.inr y => mul_nonneg (by linarith) ((Q a).nonneg y)
      sum_eq_one := by
        simp only [Fintype.sum_sum_type, ← Finset.mul_sum]
        rw [(P a).sum_eq_one, (Q a).sum_eq_one]
        ring }

/-!
## A6: Branchwise Continuation Monotonicity

Paper (lines 505-520):
Fix q∈Δ(A) and P₁:A→Δ(O₁). For branches o with m(o)>0, let r_o be the posterior.
For each such branch, let Q^o, R^o : A → Δ(O₂^o) be continuation channels.

**Critical faithfulness note**: The paper specifies that Q^o and R^o share the same
outcome type O₂^o for each branch o. The Lean formalization uses a common branch
outcome family O₂ : O₁ → Type, with both Q and R indexed by this same family.

If r_o^0 ≽_{Q^o ⊔ R^o} r_o^1 for all o with m(o)>0, then
  q^0 ≽_{(P₁▷{Q^o}) ⊔ (P₁▷{R^o})} q^1.

If one branch is strict with positive probability, the aggregate is strict.
-/

/-- **Strong A6 (auxiliary)**: allows different branch outcome families Y and Z
    for the two continuation profiles. This is stronger than the paper's A6.
    Useful as an auxiliary strengthening; not part of TraceAxioms. -/
def A6Strong_BranchwiseContinuationMonotonicity_Weak : Prop :=
  ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (Y Z : O₁ → Type u)
    [∀ o, Fintype (Y o)] [∀ o, DecidableEq (Y o)]
    [∀ o, Fintype (Z o)] [∀ o, DecidableEq (Z o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q : ∀ o, Channel A (Y o)) (R : ∀ o, Channel A (Z o)),
    (∀ o₁, BranchPositive P₁ q o₁ →
      F.rel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁))
        (inrDist (branchPosterior P₁ q o₁))) →
    F.rel (blockChannel (seqComposeDep P₁ Y Q) (seqComposeDep P₁ Z R))
      (inlDist q) (inrDist q)

/-- **Strong A6 strict (auxiliary)**: allows different branch outcome families. -/
def A6Strong_BranchwiseContinuationMonotonicity_Strict : Prop :=
  ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (Y Z : O₁ → Type u)
    [∀ o, Fintype (Y o)] [∀ o, DecidableEq (Y o)]
    [∀ o, Fintype (Z o)] [∀ o, DecidableEq (Z o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q : ∀ o, Channel A (Y o)) (R : ∀ o, Channel A (Z o)),
    (∀ o₁, BranchPositive P₁ q o₁ →
      F.rel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁))
        (inrDist (branchPosterior P₁ q o₁))) →
    (∃ o₁, BranchPositive P₁ q o₁ ∧
      F.strictRel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁))
        (inrDist (branchPosterior P₁ q o₁))) →
    F.strictRel (blockChannel (seqComposeDep P₁ Y Q) (seqComposeDep P₁ Z R))
      (inlDist q) (inrDist q)

/-- **Strong A6 combined (auxiliary)**: useful for benchmark proofs. -/
def A6Strong_BranchwiseContinuationMonotonicity : Prop :=
  A6Strong_BranchwiseContinuationMonotonicity_Weak F ∧
  A6Strong_BranchwiseContinuationMonotonicity_Strict F

/-- **Paper-faithful A6 weak**: Both continuation channels Q and R share the same
    branch outcome family O₂ : O₁ → Type. This matches the paper exactly:
    "For each such branch, let Q^o, R^o : A → Δ(O₂^o)". -/
def A6_BranchwiseContinuationMonotonicity_Weak : Prop :=
  ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q R : ∀ o, Channel A (O₂ o)),
    (∀ o₁, BranchPositive P₁ q o₁ →
      F.rel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁))
        (inrDist (branchPosterior P₁ q o₁))) →
    F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q)

/-- **Paper-faithful A6 strict**: Both continuation channels share the same
    branch outcome family O₂. -/
def A6_BranchwiseContinuationMonotonicity_Strict : Prop :=
  ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q R : ∀ o, Channel A (O₂ o)),
    (∀ o₁, BranchPositive P₁ q o₁ →
      F.rel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁))
        (inrDist (branchPosterior P₁ q o₁))) →
    (∃ o₁, BranchPositive P₁ q o₁ ∧
      F.strictRel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁))
        (inrDist (branchPosterior P₁ q o₁))) →
    F.strictRel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q)

/-- **Paper-faithful A6**: Branchwise continuation monotonicity with common
    branch outcome family O₂. This is the version used in TraceAxioms. -/
def A6_BranchwiseContinuationMonotonicity : Prop :=
  A6_BranchwiseContinuationMonotonicity_Weak F ∧
  A6_BranchwiseContinuationMonotonicity_Strict F

/-- Strong A6 implies paper-faithful A6 by specializing Y = Z = O₂. -/
theorem A6_of_A6Strong :
    A6Strong_BranchwiseContinuationMonotonicity F →
    A6_BranchwiseContinuationMonotonicity F := by
  intro ⟨hstrong_weak, hstrong_strict⟩
  constructor
  · intro A O₁ _ _ _ _ _ O₂ _ _ q P₁ Q R h_branch
    exact hstrong_weak O₂ O₂ q P₁ Q R h_branch
  · intro A O₁ _ _ _ _ _ O₂ _ _ q P₁ Q R h_branch h_strict
    exact hstrong_strict O₂ O₂ q P₁ Q R h_branch h_strict

/-!
## Derived target: Independent-Background Separability

This statement was called A7 in paper v6.  It is not a field of `TraceAxioms`
in v7: theorem `independentBackgroundSeparability_of_axioms` derives it from
A1/A3--A6.
For full-support q₁∈Δ(A₁), q₂∈Δ(A₂):

First component:
  (q₁⊗q₂)^0 ≽_{(P₁⊗R₂)⊔(Q₁⊗R₂)} (q₁⊗q₂)^1 ↔
  (q₁⊗q₂)^0 ≽_{(P₁⊗S₂)⊔(Q₁⊗S₂)} (q₁⊗q₂)^1

Second component (symmetric):
  (q₁⊗q₂)^0 ≽_{(R₁⊗P₂)⊔(R₁⊗Q₂)} (q₁⊗q₂)^1 ↔
  (q₁⊗q₂)^0 ≽_{(S₁⊗P₂)⊔(S₁⊗Q₂)} (q₁⊗q₂)^1

The background alternatives may have different outcome alphabets. This follows
the paper's "any channels" wording for R₂,S₂ and, symmetrically, R₁,S₁.
-/

def IndependentBackgroundSeparability : Prop :=
  (∀ {A₁ A₂ O₁ O₂R O₂S : Type u}
     [Fintype A₁] [DecidableEq A₁] [Fintype A₂] [DecidableEq A₂]
     [Fintype O₁] [DecidableEq O₁]
     [Fintype O₂R] [DecidableEq O₂R] [Fintype O₂S] [DecidableEq O₂S]
     (q₁ : Dist A₁) (q₂ : Dist A₂) (_hq₁ : q₁.FullSupport) (_hq₂ : q₂.FullSupport)
     (P₁ Q₁ : Channel A₁ O₁) (R₂ : Channel A₂ O₂R) (S₂ : Channel A₂ O₂S),
     let prodPR := prodChannel P₁ R₂
     let prodQR := prodChannel Q₁ R₂
     let prodPS := prodChannel P₁ S₂
     let prodQS := prodChannel Q₁ S₂
     let prodQ := prodDist q₁ q₂
     F.rel (blockChannel prodPR prodQR) (inlDist prodQ) (inrDist prodQ) ↔
     F.rel (blockChannel prodPS prodQS) (inlDist prodQ) (inrDist prodQ)) ∧
  (∀ {A₁ A₂ O₁R O₁S O₂ : Type u}
     [Fintype A₁] [DecidableEq A₁] [Fintype A₂] [DecidableEq A₂]
     [Fintype O₁R] [DecidableEq O₁R] [Fintype O₁S] [DecidableEq O₁S]
     [Fintype O₂] [DecidableEq O₂]
     (q₁ : Dist A₁) (q₂ : Dist A₂) (_hq₁ : q₁.FullSupport) (_hq₂ : q₂.FullSupport)
     (R₁ : Channel A₁ O₁R) (S₁ : Channel A₁ O₁S) (P₂ Q₂ : Channel A₂ O₂),
     let prodRP := prodChannel R₁ P₂
     let prodRQ := prodChannel R₁ Q₂
     let prodSP := prodChannel S₁ P₂
     let prodSQ := prodChannel S₁ Q₂
     let prodQ := prodDist q₁ q₂
     F.rel (blockChannel prodRP prodRQ) (inlDist prodQ) (inrDist prodQ) ↔
     F.rel (blockChannel prodSP prodSQ) (inlDist prodQ) (inrDist prodQ))

/-!
## Combined Axiom Structure
-/

structure TraceAxioms (F : PrefFamily.{u}) : Prop where
  a1 : A1_WeakOrderLocalNontriviality F
  a2 : A2_Continuity F
  a3 : A3_BlockComparisonCoherence F
  a4 : A4_OutcomePostprocessingAversion F
  a5 : A5_ActionCoarseningAversion F
  a6 : A6_BranchwiseContinuationMonotonicity F

end TraceableAgency
