/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.Axioms

/-!
# Formal statement of Trace-Tempered Choice, Theorem 1

This file contains only the mathematical domain, the eight behavioral
conditions, the represented value, and the single proposition corresponding to
Theorem 1 (including its same-scale block "moreover" clause).  It contains no
proof of that proposition.

The payoff alphabet is fixed across the entire preference family.  Action and
record alphabets vary over all nonempty finite types.  Cross-environment
comparisons remain ordinary comparisons inside common-payoff block channels;
there is no primitive preference relation on channel/prior pairs.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

/-- A dependent finite sum is inhabited when its index and every fibre are
inhabited.  Lean does not synthesize this elementary instance automatically. -/
instance dependentSigmaNonempty
    {I : Type u} [Nonempty I] (X : I → Type u)
    [∀ i, Nonempty (X i)] : Nonempty ((i : I) × X i) := by
  let i : I := Classical.choice (inferInstance : Nonempty I)
  exact ⟨⟨i, Classical.choice (inferInstance : Nonempty (X i))⟩⟩

/-! ## Primitive family and relational notation -/

/-- A preference family for one fixed payoff alphabet `O`.

For every nonempty finite action type `A`, nonempty finite explicit-record type
`R`, and joint channel `K : A → Δ(O × R)`, `rel K q p` is the primitive
within-environment comparison `q ≽_K p`. -/
structure FixedPayoffPrefFamily (O : Type u) [Fintype O] where
  rel : ∀ {A R : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype R] [DecidableEq R] [Nonempty R],
    Channel A (O × R) → TraceableAgency.Dist A → TraceableAgency.Dist A → Prop

namespace FixedPayoffPrefFamily

variable {O : Type u} [Fintype O]
variable (F : FixedPayoffPrefFamily O)
variable {A R : Type u}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- The asymmetric part of the primitive relation in one fixed environment. -/
def strictRel (K : Channel A (O × R)) (q p : TraceableAgency.Dist A) : Prop :=
  F.rel K q p ∧ ¬ F.rel K p q

/-- The symmetric part of the primitive relation in one fixed environment. -/
def indiffRel (K : Channel A (O × R)) (q p : TraceableAgency.Dist A) : Prop :=
  F.rel K q p ∧ F.rel K p q

end FixedPayoffPrefFamily

/-! ## Common-payoff block environments -/

/-- The canonical bijection that keeps the common payoff coordinate untagged
and moves a two-block tag into the explicit-record coordinate. -/
def sumPayoffRecordEquiv (O R S : Type u) :
    ((O × R) ⊕ (O × S)) ≃ (O × (R ⊕ S)) where
  toFun z :=
    match z with
    | Sum.inl or => (or.1, Sum.inl or.2)
    | Sum.inr os => (os.1, Sum.inr os.2)
  invFun z :=
    match z.2 with
    | Sum.inl r => Sum.inl (z.1, r)
    | Sum.inr s => Sum.inr (z.1, s)
  left_inv := by
    intro z
    cases z <;> rfl
  right_inv := by
    intro z
    rcases z with ⟨o, rs⟩
    cases rs <;> rfl

/-- The corresponding bijection for an arbitrary finite family of blocks. -/
def sigmaPayoffRecordEquiv (I O : Type u) (Rec : I → Type u) :
    ((i : I) × (O × Rec i)) ≃ (O × ((i : I) × Rec i)) where
  toFun z := (z.2.1, ⟨z.1, z.2.2⟩)
  invFun z := ⟨z.2.1, (z.1, z.2.2)⟩
  left_inv := by
    intro z
    rcases z with ⟨i, o, r⟩
    rfl
  right_inv := by
    intro z
    rcases z with ⟨o, i, r⟩
    rfl

/-- Paper's two-block joint channel `K ⊔ L`: actions and records are tagged,
while both blocks retain the same payoff alphabet `O`. -/
noncomputable def commonPayoffBlockChannel
    {O A B R S : Type u}
    [Fintype O] [Fintype A] [Fintype B] [Fintype R] [Fintype S]
    [DecidableEq O] [DecidableEq A] [DecidableEq B]
    [DecidableEq R] [DecidableEq S]
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    Channel (A ⊕ B) (O × (R ⊕ S)) :=
  Relabeling.relabelChannel (Equiv.refl (A ⊕ B))
    (sumPayoffRecordEquiv O R S) (blockChannel K L)

/-- Left block-supported copy `q⁰`. -/
noncomputable def leftBlockDist
    {A B : Type u} [Fintype A] [Fintype B]
    (q : TraceableAgency.Dist A) : TraceableAgency.Dist (A ⊕ B) :=
  inlDist q

/-- Right block-supported copy `p¹`. -/
noncomputable def rightBlockDist
    {A B : Type u} [Fintype A] [Fintype B]
    (p : TraceableAgency.Dist B) : TraceableAgency.Dist (A ⊕ B) :=
  inrDist p

/-- General common-payoff block channel `⨆_i K_i`. -/
noncomputable def commonPayoffBlockFamilyChannel
    {I O : Type u} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    (K : ∀ i, Channel (Act i) (O × Rec i)) :
    Channel ((i : I) × Act i) (O × ((i : I) × Rec i)) :=
  Relabeling.relabelChannel (Equiv.refl ((i : I) × Act i))
    (sigmaPayoffRecordEquiv I O Rec)
    (blockFamilyChannel Act (fun i => O × Rec i) K)

/-- General block-supported copy `q_i^i`. -/
noncomputable def commonPayoffBlockEmbed
    {I : Type u} [Fintype I] [DecidableEq I]
    (Act : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (i : I) (q : TraceableAgency.Dist (Act i)) : TraceableAgency.Dist ((i : I) × Act i) :=
  blockEmbedDist Act i q

/-- The paper's shorthand `(q,K) ≽ (p,L)`, expanded as one comparison
inside `K ⊔ L`. -/
def pairWeak
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) : Prop :=
  F.rel (commonPayoffBlockChannel K L) (leftBlockDist q) (rightBlockDist p)

/-- The asymmetric part of a cross-channel block comparison.  The reverse
comparison is taken in the same block environment, exactly as in the paper. -/
def pairStrict
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) : Prop :=
  let C := commonPayoffBlockChannel K L
  F.rel C (leftBlockDist q) (rightBlockDist p) ∧
    ¬ F.rel C (rightBlockDist p) (leftBlockDist q)

/-- The symmetric part of a cross-channel block comparison. -/
def pairIndiff
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) : Prop :=
  let C := commonPayoffBlockChannel K L
  F.rel C (leftBlockDist q) (rightBlockDist p) ∧
    F.rel C (rightBlockDist p) (leftBlockDist q)

/-! ## Record processing, action reporting, and compounding -/

/-- A payoff-preserving record processor.  Its stochastic record rewrite may
depend on the realized payoff, as required by equation (record-processing). -/
abbrev RecordProcessor (O R S : Type u) [Fintype S] :=
  O × R → TraceableAgency.Dist S

/-- A record processor regarded as a channel on visible payoff-record pairs;
the payoff coordinate is copied without alteration. -/
noncomputable def payoffPreservingRecordKernel
    {O R S : Type u}
    [Fintype O] [DecidableEq O] [Fintype R]
    [Fintype S] [DecidableEq S]
    (T : RecordProcessor O R S) : Channel (O × R) (O × S) :=
  fun z =>
    { prob := fun z' => if z'.1 = z.1 then T z z'.2 else 0
      nonneg := fun z' => by
        split_ifs
        · exact (T z).nonneg z'.2
        · exact le_rfl
      sum_eq_one := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single z.1]
        · simp [(T z).sum_eq_one]
        · intro o _ hone
          simp [hone]
        · simp }

/-- `(KT)(o,s|a) = Σ_r K(o,r|a) T(s|o,r)`. -/
noncomputable def recordPostprocess
    {O A R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R]
    [Fintype S] [DecidableEq S]
    (K : Channel A (O × R)) (T : RecordProcessor O R S) :
    Channel A (O × S) :=
  Channel.postprocess K (payoffPreservingRecordKernel T)

/-- Exact joint-law equation for the paper's action report.  It also records
that the axiom ranges over every completion on a zero-probability reported
action. -/
def IsActionReportCompletion
    {O A B R : Type u}
    [Fintype O] [Fintype A]
    [Fintype B] [DecidableEq B] [Fintype R]
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R)) : Prop :=
  ∀ b z,
    (Channel.actionPushforward q S) b * Khat b z =
      ∑ a, q a * S a b * K a z

/-- The canonical bijection that makes the first-stage branch label part of
the record while leaving the terminal payoff coordinate first. -/
def compoundPayoffRecordEquiv (Y O : Type u) (Rec : Y → Type u) :
    ((y : Y) × (O × Rec y)) ≃ (O × ((y : Y) × Rec y)) :=
  sigmaPayoffRecordEquiv Y O Rec

/-- Paper's compound environment
`(P ▷ {Kʸ})(o,⟨y,r⟩|a) = P(y|a) Kʸ(o,r|a)`. -/
noncomputable def commonPayoffCompound
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (K : ∀ y, Channel A (O × Rec y)) :
    Channel A (O × ((y : Y) × Rec y)) :=
  Relabeling.relabelChannel (Equiv.refl A)
    (compoundPayoffRecordEquiv Y O Rec)
    (seqComposeDep P (fun y => O × Rec y) K)

/-! ## Axioms A1--A8 -/

/-- A1: every fixed joint channel carries a complete and transitive order. -/
def A1_WeakOrder
    {O : Type u} [Fintype O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)),
      (∀ q p : TraceableAgency.Dist A, F.rel K q p ∨ F.rel K p q) ∧
      (∀ q p s : TraceableAgency.Dist A, F.rel K q p → F.rel K p s → F.rel K q s)

/-- A2: sequential closedness of the preference graph for each fixed triple of
finite alphabets.  In finite Euclidean spaces this is equivalent to the paper's
closed-set formulation. -/
def A2_Continuity
    {O : Type u} [Fintype O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (Kseq : ℕ → Channel A (O × R)) (K : Channel A (O × R))
    (qseq pseq : ℕ → TraceableAgency.Dist A) (q p : TraceableAgency.Dist A),
    ChannelConverges Kseq K →
    DistConverges qseq q →
    DistConverges pseq p →
    (∀ n, F.rel (Kseq n) (qseq n) (pseq n)) →
    F.rel K q p

/-- A3: duplication and irrelevant-block coherence. -/
structure A3_BlockComparisonCoherence
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop where
  duplication :
    ∀ {A R : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype R] [DecidableEq R] [Nonempty R]
      (K : Channel A (O × R)) (q p : TraceableAgency.Dist A),
      F.rel K q p ↔ pairWeak F q K p K
  irrelevant_blocks :
    ∀ {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
      (Act Rec : I → Type u)
      [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
      [∀ i, Nonempty (Act i)]
      [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
      [∀ i, Nonempty (Rec i)]
      (K : ∀ i, Channel (Act i) (O × Rec i))
      (i j : I) (_hij : i ≠ j)
      (qi : TraceableAgency.Dist (Act i)) (qj : TraceableAgency.Dist (Act j)),
      F.rel (commonPayoffBlockFamilyChannel Act Rec K)
          (commonPayoffBlockEmbed Act i qi)
          (commonPayoffBlockEmbed Act j qj)
        ↔ pairWeak F qi (K i) qj (K j)

/-- A4: garbling the explicit record, conditional on payoff if desired, cannot
improve a pair. -/
def A4_RecordDataProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (K : Channel A (O × R)) (T : RecordProcessor O R S) (q : TraceableAgency.Dist A),
    pairWeak F q K q (recordPostprocess K T)

/-- A5: a stochastic report of the realized action cannot improve a pair,
for every channel satisfying the exact joint-law completion equation. -/
def A5_ActionDataProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A B R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R)),
    IsActionReportCompletion K q S Khat →
    pairWeak F q K (Channel.actionPushforward q S) Khat

/-- Paper-faithful weak part of A6.  Both continuation profiles share the same
branch-dependent record family `Rec`; allowing two unrelated families would be
a stronger premise than the weakest reading of v3. -/
def A6_BranchwiseContinuationConsistency_Weak
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (P : Channel A Y) (K L : ∀ y, Channel A (O × Rec y))
    (q : TraceableAgency.Dist A),
    (∀ y, BranchPositive P q y →
      pairWeak F (branchPosterior P q y) (K y)
        (branchPosterior P q y) (L y)) →
    pairWeak F q (commonPayoffCompound Rec P K)
      q (commonPayoffCompound Rec P L)

/-- Strict part of A6: a strict comparison in at least one reached branch,
in addition to weak improvement in every reached branch, makes the compound
comparison strict. -/
def A6_BranchwiseContinuationConsistency_Strict
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (P : Channel A Y) (K L : ∀ y, Channel A (O × Rec y))
    (q : TraceableAgency.Dist A),
    (∀ y, BranchPositive P q y →
      pairWeak F (branchPosterior P q y) (K y)
        (branchPosterior P q y) (L y)) →
    (∃ y, BranchPositive P q y ∧
      pairStrict F (branchPosterior P q y) (K y)
        (branchPosterior P q y) (L y)) →
    pairStrict F q (commonPayoffCompound Rec P K)
      q (commonPayoffCompound Rec P L)

/-- A6 with its weak and strict clauses. -/
def A6_BranchwiseContinuationConsistency
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  A6_BranchwiseContinuationConsistency_Weak F ∧
    A6_BranchwiseContinuationConsistency_Strict F

/-- One-action, uninformative-record channel delivering payoff `o` surely. -/
noncomputable def deterministicPayoffChannel
    {O : Type u} [Fintype O] [DecidableEq O]
    (o : O) : Channel PUnit (O × PUnit) :=
  fun _ => TraceableAgency.Dist.pure (o, PUnit.unit)

/-- Constant-payoff channel whose record fully reveals the action. -/
noncomputable def fullRevealAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (o : O) : Channel A (O × A) :=
  fun a => TraceableAgency.Dist.pure (o, a)

/-- Constant-payoff channel with an uninformative one-point record. -/
noncomputable def uninformativeAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O] [Fintype A]
    (o : O) : Channel A (O × PUnit) :=
  fun _ => TraceableAgency.Dist.pure (o, PUnit.unit)

/-- Explicit paper-level meaning of a constant payoff index. -/
def IsConstantPayoffIndex {O : Type u} (u : O → ℝ) : Prop :=
  ∃ c : ℝ, ∀ o : O, u o = c

/-- A7: at least two deterministic material outcomes are strictly ranked. -/
def A7_MaterialRelevance
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∃ oplus ominus : O,
    pairStrict F (TraceableAgency.Dist.pure PUnit.unit)
      (deterministicPayoffChannel oplus)
      (TraceableAgency.Dist.pure PUnit.unit)
      (deterministicPayoffChannel ominus)

/-- A8: for every genuinely uncertain full-support action lottery and every
constant payoff, full revelation is strictly preferred to no record. -/
def A8_PositiveTraceOrientation
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A : Type u}
    [Fintype A] [DecidableEq A] [Nontrivial A]
    (q : TraceableAgency.Dist A), q.FullSupport →
    ∀ o : O,
      pairStrict F q (fullRevealAtPayoff (A := A) o)
        q (uninformativeAtPayoff (A := A) o)

/-- The eight behavioral conditions in Theorem 1. -/
structure TraceTemperedAxioms
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop where
  a1 : A1_WeakOrder F
  a2 : A2_Continuity F
  a3 : A3_BlockComparisonCoherence F
  a4 : A4_RecordDataProcessing F
  a5 : A5_ActionDataProcessing F
  a6 : A6_BranchwiseContinuationConsistency F
  a7 : A7_MaterialRelevance F
  a8 : A8_PositiveTraceOrientation F

/-! ## Represented value and theorem conclusion -/

/-- Expected utility of the payoff coordinate under the joint law `q(a)K(o,r|a)`. -/
noncomputable def expectedPayoffUtility
    {O A R : Type u}
    [Fintype O] [Fintype A] [Fintype R]
    (u : O → ℝ) (q : TraceableAgency.Dist A) (K : Channel A (O × R)) : ℝ :=
  ∑ a, q a * ∑ z, K a z * u z.1

/-- The represented value in Theorem 1.  `mutualInfo q K` is mutual
information between the action and the whole visible pair `(O,R)`, and uses
Lean's natural logarithm. -/
noncomputable def traceTemperedValue
    {O A R : Type u}
    [Fintype O] [Fintype A] [Fintype R]
    (u : O → ℝ) (lambda : ℝ)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) : ℝ :=
  expectedPayoffUtility u q K + lambda * mutualInfo q K

/-- The within-channel representation clause, with one fixed `u` and `lambda`
used for every nonempty finite action and record alphabet. -/
def WithinChannelRepresentation
    {O : Type u} [Fintype O]
    (F : FixedPayoffPrefFamily O) (u : O → ℝ) (lambda : ℝ) : Prop :=
  ∀ {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q p : TraceableAgency.Dist A),
    F.rel K q p ↔
      traceTemperedValue u lambda q K ≥
        traceTemperedValue u lambda p K

/-- The theorem's "moreover" clause for the very same `u` and `lambda` that
represent within-channel comparisons. -/
def SameWitnessBlockRepresentation
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (u : O → ℝ) (lambda : ℝ) : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Nonempty (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    [∀ i, Nonempty (Rec i)]
    (K : ∀ i, Channel (Act i) (O × Rec i))
    (i j : I) (_hij : i ≠ j)
    (qi : TraceableAgency.Dist (Act i)) (qj : TraceableAgency.Dist (Act j)),
    F.rel (commonPayoffBlockFamilyChannel Act Rec K)
        (commonPayoffBlockEmbed Act i qi)
        (commonPayoffBlockEmbed Act j qj)
      ↔
    traceTemperedValue u lambda qi (K i) ≥
      traceTemperedValue u lambda qj (K j)

/-- Exact single-proposition reading of Theorem 1.

The payoff alphabet is chosen first and is required to have at least two
elements.  The first conjunct is the displayed equivalence.  The second is the
weakest literal reading of the "moreover" clause: under the axioms there are
particular witnesses `u, lambda` that simultaneously represent within-channel
and block-supported cross-channel comparisons. -/
def Theorem1Statement : Prop :=
  ∀ (O : Type u) [Fintype O] [DecidableEq O],
    2 ≤ Fintype.card O →
    ∀ F : FixedPayoffPrefFamily O,
      (TraceTemperedAxioms F ↔
        ∃ (u : O → ℝ) (lambda : ℝ),
          ¬ IsConstantPayoffIndex u ∧
          0 < lambda ∧
          WithinChannelRepresentation F u lambda) ∧
      (TraceTemperedAxioms F →
        ∃ (u : O → ℝ) (lambda : ℝ),
          ¬ IsConstantPayoffIndex u ∧
          0 < lambda ∧
          WithinChannelRepresentation F u lambda ∧
          SameWitnessBlockRepresentation F u lambda)

end TraceTemperedChoiceVerification
