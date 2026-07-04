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
# Axioms A1-A8

The behavioural axioms for traceable agency from empowerment_v5.tex.
Each axiom is a predicate on PrefFamily.

Paper line references (empowerment_v5.tex):
- A1: lines 410-420
- A2: lines 422-446
- A3: lines 448-467
- A4: lines 469-476
- A5: lines 478-491
- A6: lines 493-503
- A7: lines 505-524
- A8: lines 526-543
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

variable (F : PrefFamily.{u})

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

Paper (lines 422-443):
1. The set {(P,q,q') : q ≽_P q'} is closed.
2. Block comparisons are continuous in posterior-law convergence at fixed full-support prior:
   if q has full support, μ_{q,P_n} ⇒ μ_{q,P}, μ_{q,Q_n} ⇒ μ_{q,Q},
   and q^0 ≽_{P_n ⊔ Q_n} q^1 for all n, then q^0 ≽_{P ⊔ Q} q^1.

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
  ClosedPreferenceGraph F ∧
  (∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
     (q : Dist A) (_hq : q.FullSupport)
     (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A)
     (Fₙ : ℕ → FiniteExperimentOn A) (G : FiniteExperimentOn A),
     PosteriorLawConvergesAtExp q Eₙ E →
     PosteriorLawConvergesAtExp q Fₙ G →
     (∀ n, ExperimentPairPref F (Eₙ n) (Fₙ n) q q) →
     ExperimentPairPref F E G q q)

/-!
## A3: Block-Comparison Coherence

Paper (lines 448-463):
1. q ≽_P q' ↔ q^0 ≽_{P ⊔ P} (q')^1
2. For any finite block environment ⨆_{k∈K} P_k, distinct blocks i,j, and
   q_i ∈ Δ(A_i), q_j ∈ Δ(A_j):
     q_i^i ≽_{⨆_k P_k} q_j^j ↔ q_i^0 ≽_{P_i ⊔ P_j} q_j^1
-/

def A3_BlockComparisonCoherence : Prop :=
  (∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
     (P : Channel A O) (q q' : Dist A),
     F.rel P q q' ↔ F.rel (blockChannel P P) (inlDist q) (inrDist q')) ∧
  (∀ {K : Type u} [Fintype K] [DecidableEq K]
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
       (inrDist qⱼ))

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
## A6: Public-Coin Independence

Paper (lines 493-499):
At fixed q∈Δ(A), for channels P,Q,R on A and λ∈(0,1):
  q^0 ≽_{P ⊔ Q} q^1 ↔ q^0 ≽_{(λP⊕(1-λ)R) ⊔ (λQ⊕(1-λ)R)} q^1.
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

def A6_PublicCoinIndependence : Prop :=
  ∀ {A O_P O_Q O_R : Type u} [Fintype A] [DecidableEq A]
    [Fintype O_P] [DecidableEq O_P] [Fintype O_Q] [DecidableEq O_Q]
    [Fintype O_R] [DecidableEq O_R]
    (q : Dist A) (P : Channel A O_P) (Q : Channel A O_Q) (R : Channel A O_R)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
    let mixPR := publicMixChannel t ht0 ht1 P R
    let mixQR := publicMixChannel t ht0 ht1 Q R
    F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
    F.rel (blockChannel mixPR mixQR) (inlDist q) (inrDist q)

/-!
## A7: Branchwise Continuation Monotonicity

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

/-- **Strong A7 (auxiliary)**: allows different branch outcome families Y and Z
    for the two continuation profiles. This is stronger than the paper's A7.
    Useful as an auxiliary strengthening; not part of TraceAxioms. -/
def A7Strong_BranchwiseContinuationMonotonicity_Weak : Prop :=
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

/-- **Strong A7 strict (auxiliary)**: allows different branch outcome families. -/
def A7Strong_BranchwiseContinuationMonotonicity_Strict : Prop :=
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

/-- **Strong A7 combined (auxiliary)**: useful for benchmark proofs. -/
def A7Strong_BranchwiseContinuationMonotonicity : Prop :=
  A7Strong_BranchwiseContinuationMonotonicity_Weak F ∧
  A7Strong_BranchwiseContinuationMonotonicity_Strict F

/-- **Paper-faithful A7 weak**: Both continuation channels Q and R share the same
    branch outcome family O₂ : O₁ → Type. This matches the paper exactly:
    "For each such branch, let Q^o, R^o : A → Δ(O₂^o)". -/
def A7_BranchwiseContinuationMonotonicity_Weak : Prop :=
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

/-- **Paper-faithful A7 strict**: Both continuation channels share the same
    branch outcome family O₂. -/
def A7_BranchwiseContinuationMonotonicity_Strict : Prop :=
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

/-- **Paper-faithful A7**: Branchwise continuation monotonicity with common
    branch outcome family O₂. This is the version used in TraceAxioms. -/
def A7_BranchwiseContinuationMonotonicity : Prop :=
  A7_BranchwiseContinuationMonotonicity_Weak F ∧
  A7_BranchwiseContinuationMonotonicity_Strict F

/-- Strong A7 implies paper-faithful A7 by specializing Y = Z = O₂. -/
theorem A7_of_A7Strong :
    A7Strong_BranchwiseContinuationMonotonicity F →
    A7_BranchwiseContinuationMonotonicity F := by
  intro ⟨hstrong_weak, hstrong_strict⟩
  constructor
  · intro A O₁ _ _ _ _ _ O₂ _ _ q P₁ Q R h_branch
    exact hstrong_weak O₂ O₂ q P₁ Q R h_branch
  · intro A O₁ _ _ _ _ _ O₂ _ _ q P₁ Q R h_branch h_strict
    exact hstrong_strict O₂ O₂ q P₁ Q R h_branch h_strict

/-!
## A8: Independent-Background Separability

Paper (lines 526-538):
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

def A8_IndependentBackgroundSeparability : Prop :=
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
  a6 : A6_PublicCoinIndependence F
  a7 : A7_BranchwiseContinuationMonotonicity F
  a8 : A8_IndependentBackgroundSeparability F

end TraceableAgency
