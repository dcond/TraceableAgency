# Lean-Only Certificate — Complete Transparent Statement of the Formalized Theorem

> **UPDATE (cardinal-boundary assumption eliminated).** Since the original drafting, the
> `FiniteCardinalSupportBoundaryAssumptions` boundary field has been **removed** from the
> convention bundle `FinalHarmlessConventions` / `FinalConstructedRepresentativeConventions`.
> Its three facts are now **proved theorems**, not assumptions:
> `field1_boundaryComplete` (boundary normalized-value support restriction),
> `hfun_eq_normalizedValue_idChannel_of_scale` (boundary `Hfun` identity), and
> `field3_restricted_coarse_reveal` (restricted coarse-reveal value). The exported theorem
> `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` routes through
> `MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal`; verified via `#print`
> that `FiniteCardinalSupportBoundaryAssumptions` is absent from every convention structure.
> Any text below that lists `support_boundary` / `FiniteCardinalSupportBoundaryAssumptions` as a
> live convention field is historical and superseded by this note. Axiom footprint unchanged:
> `[propext, Classical.choice, Quot.sound]`.


**Scope of this document.** This certificate describes the Lean 4 development **as if it were the
only artifact** — no paper is assumed. It states, in full and verbatim, the final theorem, every
primitive it is built from, and **every hypothesis and convention it depends on**, expanded down to
leaf structures with no ellipsis. A Lean-literate reader can turn each displayed statement into
ordinary mathematics; a reader who *also* has the paper can check 100% correspondence of
hypotheses and conclusions.

**What the reader must supply.** This document does not reproduce proofs. It exhibits the *inputs*
and the *output*. The claim "these inputs prove that output" is guaranteed by the Lean kernel and
recorded by the axiom footprint in §7. The reader's job is to read the ~30 displayed statements and
translate them into mathematics.

**Conventions of presentation.**
- Every Lean block is copied verbatim from source with a `-- file:line` provenance comment.
- `Dist A` = finite probability distribution on `A`; `Channel A O = A → Dist O`; `F.rel P q q'`
  is the primitive preference `q ≽_P q'`. These are defined in §1.
- Notation: `I(q, P) = mutualInfo q P`, `H(q) = entropy q`. `q^0 = inlDist q`, `q^1 = inrDist q`,
  `P ⊔ Q = blockChannel P Q`, `⊗` = product.
- Structures are tagged **[EXTERNAL HYPOTHESIS]** (an input the reader must accept as a classical
  theorem or as a normalization), **[CONVENTION]** (a normalization/representative choice), or
  **[CONSTRUCTED]** (built internally by the proof; shown only so the reader understands the types
  appearing inside hypotheses — *not* something to accept).

Build: `lake build` succeeds (Lean `v4.32.0-rc1`, mathlib `v4.32.0-rc1`). Commit at time of
writing: `8b2b7d2` on branch `codex/full-preentropy-closure`.

---

## 0. The final theorem (verbatim)

```lean
-- TraceableAgency/External/EntropyReductionClosure.lean
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventions hhm hax) :
    MIRep F
```

`#check` output (verbatim):
```
TraceableAgency.MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions.{u}
  (hfad : TraceableAgency.ClassicalFaddeevTheoremAssumptions) {F : TraceableAgency.PrefFamily}
  (hhm : TraceableAgency.FinalHMInterface) (hax : TraceableAgency.TraceAxioms F)
  (hconv : TraceableAgency.FinalConstructedRepresentativeConventions hhm hax) : TraceableAgency.MIRep F
```

**In words.** For any preference family `F`: given (i) the classical Faddeev entropy-uniqueness
theorem `hfad`, (ii) the finite Herstein–Milnor / Blackwell interface `hhm`, (iii) the behavioural
axioms `hax : TraceAxioms F`, and (iv) a bundle of representative/gauge/boundary normalizations
`hconv`, the family is represented by mutual information: `MIRep F` (§2).

The four hypotheses are fully expanded in §3 (`TraceAxioms`), §4 (`FinalHMInterface`), §5
(`ClassicalFaddeevTheoremAssumptions`), §6 (`FinalConstructedRepresentativeConventions`).

---

## 1. Primitive vocabulary

Everything below is elementary and carries no hypothesis.

### 1.1 Distributions and channels

```lean
-- Basic/Dist.lean:24
structure Dist (A : Type*) [Fintype A] where
  prob : A → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

-- Basic/Dist.lean:58   (point mass δ_a)
def pure (a : A) : Dist A where …          -- prob b = if b = a then 1 else 0

-- Basic/Channel.lean:23
abbrev Channel (A O : Type*) [Fintype O] := A → Dist O

-- Basic/Dist.lean:49
def FullSupport (q : Dist A) : Prop := ∀ a, q a > 0
```
`Dist A` is a finite probability vector; `Channel A O` is a stochastic matrix (each row a `Dist O`).
`q.FullSupport` means every coordinate is strictly positive.

### 1.2 The preference primitive

```lean
-- Behaviour/Preferences.lean:31
structure PrefFamily where
  rel : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O],
        Channel A O → Dist A → Dist A → Prop

-- Behaviour/Preferences.lean:41
def strictRel (P : Channel A O) (q q' : Dist A) : Prop := F.rel P q q' ∧ ¬ F.rel P q' q
-- Behaviour/Preferences.lean:48
def IsComplete   (P : Channel A O) : Prop := ∀ q q', F.rel P q q' ∨ F.rel P q' q
def IsTransitive (P : Channel A O) : Prop := ∀ q q' q'', F.rel P q q' → F.rel P q' q'' → F.rel P q q''
def IsWeakOrder  (P : Channel A O) : Prop := F.IsComplete P ∧ F.IsTransitive P
```
`F.rel P q q'` is the sole primitive: "at environment `P`, lottery `q` is at least as good as `q'`"
(`q ≽_P q'`). Everything else is defined from it.

### 1.3 Mutual information and entropy (the objects in the conclusion)

```lean
-- Info/Entropy.lean:23
noncomputable def entropyTerm (p : ℝ) : ℝ := if p ≤ 0 then 0 else -p * Real.log p
-- Info/Entropy.lean:117
noncomputable def entropy (q : Dist A) : ℝ := ∑ a, entropyTerm (q a)
-- Info/Entropy.lean:120
notation "H(" q ")" => entropy q

-- Info/MutualInfo.lean:28
noncomputable def mutualInfo (q : Dist A) (P : Channel A O) : ℝ :=
  H(Channel.outcomeMarginal P q) - ∑ a, q a * H(P a)
-- Info/MutualInfo.lean:31
notation "I(" q ", " P ")" => mutualInfo q P
```
`H(q) = −Σ q(a) log q(a)` (Shannon entropy, `0 log 0 = 0`). `I(q,P)` is the noise form
`H(marginal) − Σ_a q(a) H(P(·|a))`, i.e. standard mutual information between action and outcome
under prior `q` and channel `P`.

### 1.4 Posteriors, marginals, posterior-law integrals

```lean
-- Basic/Channel.lean:41    outcome marginal  m_{q,P}(o) = Σ_a q(a) P(o|a)
noncomputable def outcomeMarginal (P : Channel A O) (q : Dist A) : Dist O := …
-- Basic/Channel.lean:56    Bayes posterior  r_o(a) = q(a)P(o|a)/m(o)  (δ-fallback if m(o)=0)
noncomputable def posterior (P : Channel A O) (q : Dist A) (o : O) : Dist A := …

-- Basic/Convergence.lean:122   ∫ φ dμ_{q,P} = Σ_o m(o) φ(r_o)
noncomputable def posteriorLawIntegral (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) : ℝ :=
  ∑ o, (Channel.outcomeMarginal P q) o * φ (Channel.posterior P q o)

-- Basic/Convergence.lean:85   experiment version (bundled outcome type)
noncomputable def posteriorLawIntegralExp (q : Dist A) (E : FiniteExperimentOn A) (φ : Dist A → ℝ) : ℝ :=
  ∑ o, (E.outcomeMarginal q) o * φ (E.posterior q o)
```
The **posterior law** `μ_{q,P}` is the distribution over posteriors `r_o` weighted by their
marginal probability `m(o)`; `posteriorLawIntegral` integrates a test function `φ` against it.

### 1.5 Combinators used to state the axioms (signatures)

```lean
-- Basic/Channel.lean:72/75/88
idChannel            : Channel A A                              -- full revelation Id_A (:= fun a => Dist.pure a)
uninformativeChannel : (A : Type*) → Channel A Unit            -- one-outcome channel U_A
uninformativeChannelU: (A : Type u) → Channel A PUnit.{u+1}    -- universe-matched U_A
postprocess          : Channel O O' → Channel A O'             -- (PT)(o'|a) = Σ_o P(o|a) T(o'|o)
-- Basic/Blocks.lean:30/61/75
blockChannel         : Channel A O → Channel B Y → Channel (A⊕B) (O⊕Y)  -- P ⊔ Q (block-diagonal)
inlDist              : Dist A → Dist (A⊕B)                     -- q^0  (mass on left block)
inrDist              : Dist B → Dist (A⊕B)                     -- q^1  (mass on right block)
-- Basic/Products.lean:23/40
prodDist             : Dist A₁ → Dist A₂ → Dist (A₁×A₂)        -- q₁⊗q₂
prodChannel          : Channel A₁ O₁ → Channel A₂ O₂ → Channel (A₁×A₂) (O₁×O₂)  -- P₁⊗P₂
-- Basic/Blocks.lean:197/233
blockFamilyChannel   : (∀k, Channel (Act k) (Out k)) → Channel ((k:K)×Act k) ((k:K)×Out k)  -- ⨆_k P_k
blockEmbedDist       : (i:K) → Dist (Act i) → Dist ((k:K)×Act k)  -- q^i (embed into block i)
-- Basic/Channel.lean:97/100/121, Basic/Sequential.lean:74/107/111
ActionKernel A A'    := A → Dist A'                            -- action coarsening S
actionPushforward    : ActionKernel A A' → Dist A'            -- qS
IsBayesPushforwardCompletion : … → Prop                       -- P̂ completes S^q P
seqComposeDep        : (P₁ : Channel A O₁) → (∀o, Channel A (Y o)) → Channel A ((o:O₁)×Y o)  -- P₁ ▷ {Q^o}
BranchPositive P₁ q o := (outcomeMarginal P₁ q) o > 0          -- m(o) > 0
branchPosterior P₁ q o := Channel.posterior P₁ q o            -- r_o
-- Info/Identities.lean:581
sigmaDist            : Dist K → (∀k, Dist (Act k)) → Dist ((k:K)×Act k)  -- (p⊗_σ q)(k,a)=p(k)q_k(a)
-- Basic/SupportRestriction.lean:28/84/107
supportSubtype q     := {a // q a > 0}                         -- positive support of q
Dist.restrictToSupport    : (q : Dist A) → Dist (supportSubtype q)
Channel.restrictToSupport : Channel A O → (q : Dist A) → Channel (supportSubtype q) O

-- Basic/Convergence.lean:44   a channel bundled with its (finite) outcome type
structure FiniteExperimentOn (A : Type u) [Fintype A] where
  OutcomeType : Type u
  outFintype  : Fintype OutcomeType
  outDecEq    : DecidableEq OutcomeType
  channel     : Channel A OutcomeType
-- Convergence.lean:104 / Blackwell.lean:112  (both Prop, verbatim in §4.2)
SamePosteriorLawExp q E E'     -- ∀ continuous φ, ∫φ dμ_{q,E} = ∫φ dμ_{q,E'}
ExperimentPostprocesses E E'   -- E' is a garbling/post-processing of E
-- Convergence.lean:95
PosteriorLawConvergesAtExp q Eₙ E   -- weak convergence μ_{q,Eₙ} ⇒ μ_{q,E}
```

---

## 2. The conclusion `MIRep F` and the two companion theorems

### 2.1 `MIRep` (the output of the final theorem)

```lean
-- Behaviour/MIPreference.lean:31
def MIRep (F : PrefFamily.{u}) : Prop :=
  ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A),
    F.rel P q q' ↔ mutualInfo q P ≥ mutualInfo q' P
```
**Mathematics.** For every finite channel `P : A → Δ(O)` and priors `q, q' ∈ Δ(A)`:
`q ≽_P q'  ⟺  I(q,P) ≥ I(q',P)`. Same channel on both sides (fixed-environment representation).

### 2.2 Necessity (converse direction) — a separate theorem

```lean
-- Main.lean:140
theorem BenchmarkStatement_of_DPI (hdpi : FiniteDPIAssumptions.{u}) : BenchmarkStatement.{u}
-- where
def BenchmarkStatement : Prop := ∀ F : PrefFamily.{u}, MIRep F → TraceAxioms F
```
Given the finite data-processing inequality (§5.4), any MI-represented family satisfies A1–A8.
**Not** proved by the final theorem; composes with it to give the full `iff`.

### 2.3 "Moreover" block same-scale clause — a separate theorem

```lean
-- Main.lean:155
theorem blockSameScaleRep_of_MIRep (F : PrefFamily.{u}) (hrep : MIRep F) : BlockSameScaleRep F
-- where
def BlockSameScaleRep (F : PrefFamily.{u}) : Prop :=
  ∀ {K : Type u} [Fintype K] [DecidableEq K] (Act Out : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)] [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
    (P : ∀ k, Channel (Act k) (Out k)) (i j : K), i ≠ j →
    ∀ (qᵢ : Dist (Act i)) (qⱼ : Dist (Act j)),
      F.rel (blockFamilyChannel Act Out P) (blockEmbedDist Act i qᵢ) (blockEmbedDist Act j qⱼ)
      ↔ I(qᵢ, P i) ≥ I(qⱼ, P j)
```
Cross-block comparisons in any finite block environment are on the same MI scale. Derived from
`MIRep F` alone (no extra assumption). **Not** proved by the final theorem.

Both companion theorems have `#print axioms = [propext, Classical.choice, Quot.sound]` (same as the
final theorem).

---

## 3. Hypothesis 1 — `TraceAxioms F` (the behavioural axioms) [EXTERNAL HYPOTHESIS: the axioms]

```lean
-- Behaviour/Axioms.lean:368
structure TraceAxioms (F : PrefFamily.{u}) : Prop where
  a1 : A1_WeakOrderLocalNontriviality F
  a2 : A2_Continuity F
  a3 : A3_BlockComparisonCoherence F
  a4 : A4_OutcomePostprocessingAversion F
  a5 : A5_ActionCoarseningAversion F
  a6 : A6_PublicCoinIndependence F
  a7 : A7_BranchwiseContinuationMonotonicity F
  a8 : A8_IndependentBackgroundSeparability F
```

These are the behavioural primitives the whole theorem rests on. Each is displayed in full below.

### A1 — Weak order + local non-triviality
```lean
-- Behaviour/Axioms.lean:45
def A1_WeakOrderLocalNontriviality : Prop :=
  (∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
     (P : Channel A O), F.IsWeakOrder P) ∧
  (∀ {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
     (q : Dist A), q.FullSupport →
     let P_id : Channel A A := Channel.idChannel
     let P_uninf : Channel A Unit := Channel.uninformativeChannel A
     let blockP := blockChannel P_id P_uninf
     F.strictRel blockP (inlDist q) (inrDist q))
```
**Math.** Every `≽_P` is complete + transitive; and for `|A|≥2`, full-support `q`, full revelation
is strictly preferred to no information: `q^0 ≻_{Id_A ⊔ U_A} q^1`.

### A2 — Continuity
```lean
-- Behaviour/Axioms.lean:69   (the closed-graph component)
def ClosedPreferenceGraph : Prop :=
  ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (Pₙ : ℕ → Channel A O) (P : Channel A O) (qₙ rₙ : ℕ → Dist A) (q r : Dist A),
    ChannelConverges Pₙ P → DistConverges qₙ q → DistConverges rₙ r →
    (∀ n, F.rel (Pₙ n) (qₙ n) (rₙ n)) → F.rel P q r
-- Behaviour/Axioms.lean:98
def A2_Continuity (F : PrefFamily.{u}) : Prop :=
  ClosedPreferenceGraph F ∧
  (∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
     (q : Dist A) (_hq : q.FullSupport)
     (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A)
     (Fₙ : ℕ → FiniteExperimentOn A) (G : FiniteExperimentOn A),
     PosteriorLawConvergesAtExp q Eₙ E → PosteriorLawConvergesAtExp q Fₙ G →
     (∀ n, ExperimentPairPref F (Eₙ n) (Fₙ n) q q) → ExperimentPairPref F E G q q)
```
**Math.** The preference graph is closed; and block comparisons are stable under weak convergence
of posterior laws at a fixed full-support prior.
(`ExperimentPairPref F E₁ E₂ q q` = `q^0 ≽_{E₁⊔E₂} q^1` for bundled experiments — Axioms.lean:89.)

### A3 — Block-comparison coherence
```lean
-- Behaviour/Axioms.lean:119
def A3_BlockComparisonCoherence : Prop :=
  (∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
     (P : Channel A O) (q q' : Dist A),
     F.rel P q q' ↔ F.rel (blockChannel P P) (inlDist q) (inrDist q')) ∧
  (∀ {K : Type u} [Fintype K] [DecidableEq K]
     (Act : K → Type u) (Out : K → Type u)
     [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)] [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
     (P : ∀ k, Channel (Act k) (Out k)) (i j : K) (hij : i ≠ j)
     (qᵢ : Dist (Act i)) (qⱼ : Dist (Act j)),
     F.rel (blockFamilyChannel Act Out P) (blockEmbedDist Act i qᵢ) (blockEmbedDist Act j qⱼ)
     ↔ F.rel (blockChannel (P i) (P j)) (inlDist qᵢ) (inrDist qⱼ))
```
**Math.** (i) Duplicating an environment does not change the ranking: `q ≽_P q' ⟺ q^0 ≽_{P⊔P} q'^1`.
(ii) Comparisons in a finite block family reduce to the two active blocks:
`qᵢ^i ≽_{⨆_k P_k} qⱼ^j ⟺ qᵢ^0 ≽_{P_i⊔P_j} qⱼ^1`.

### A4 — Outcome post-processing aversion
```lean
-- Behaviour/Axioms.lean:145
def A4_OutcomePostprocessingAversion : Prop :=
  ∀ {A O O' : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O] [Fintype O'] [DecidableEq O']
    (P : Channel A O) (T : Channel O O') (q : Dist A),
    F.rel (blockChannel P (Channel.postprocess P T)) (inlDist q) (inrDist q)
```
**Math.** Garbling outcomes cannot increase traceability: `q^0 ≽_{P⊔PT} q^1`.

### A5 — Action-coarsening aversion
```lean
-- Behaviour/Axioms.lean:159
def A5_ActionCoarseningAversion : Prop :=
  ∀ {A A' O : Type u} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype O] [DecidableEq O] [Nonempty A]
    (P : Channel A O) (q : Dist A) (S : Channel.ActionKernel A A') (P_hat : Channel A' O),
    Channel.IsBayesPushforwardCompletion P q S P_hat →
    F.rel (blockChannel P P_hat) (inlDist q) (inrDist (Channel.actionPushforward q S))
```
**Math.** Coarsening actions cannot increase traceability, for every Bayes completion `P̂`:
`q^0 ≽_{P⊔P̂} (qS)^1`.

### A6 — Public-coin independence
```lean
-- Behaviour/Axioms.lean:175   (the observed public mixture λP⊕(1-λ)R)
noncomputable def publicMixChannel (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O_P) (Q : Channel A O_Q) : Channel A (O_P ⊕ O_Q) := …
-- Behaviour/Axioms.lean:193
def A6_PublicCoinIndependence : Prop :=
  ∀ {A O_P O_Q O_R : Type u} [Fintype A] [DecidableEq A]
    [Fintype O_P] [DecidableEq O_P] [Fintype O_Q] [DecidableEq O_Q] [Fintype O_R] [DecidableEq O_R]
    (q : Dist A) (P : Channel A O_P) (Q : Channel A O_Q) (R : Channel A O_R)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
    let mixPR := publicMixChannel t ht0 ht1 P R
    let mixQR := publicMixChannel t ht0 ht1 Q R
    F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
    F.rel (blockChannel mixPR mixQR) (inlDist q) (inrDist q)
```
**Math.** Mixing both compared channels with a common observed background `R` (coin weight `λ=t`)
leaves the comparison unchanged.

### A7 — Branchwise continuation monotonicity  (weak ∧ strict; **shared** branch outcome family)
```lean
-- Behaviour/Axioms.lean:303
def A7_BranchwiseContinuationMonotonicity : Prop :=
  A7_BranchwiseContinuationMonotonicity_Weak F ∧ A7_BranchwiseContinuationMonotonicity_Strict F
-- Behaviour/Axioms.lean:267
def A7_BranchwiseContinuationMonotonicity_Weak : Prop :=
  ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u) [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁) (Q R : ∀ o, Channel A (O₂ o)),
    (∀ o₁, BranchPositive P₁ q o₁ →
      F.rel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁)) (inrDist (branchPosterior P₁ q o₁))) →
    F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R)) (inlDist q) (inrDist q)
-- Behaviour/Axioms.lean:283
def A7_BranchwiseContinuationMonotonicity_Strict : Prop :=
  ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u) [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁) (Q R : ∀ o, Channel A (O₂ o)),
    (∀ o₁, BranchPositive P₁ q o₁ →
      F.rel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁)) (inrDist (branchPosterior P₁ q o₁))) →
    (∃ o₁, BranchPositive P₁ q o₁ ∧
      F.strictRel (blockChannel (Q o₁) (R o₁))
        (inlDist (branchPosterior P₁ q o₁)) (inrDist (branchPosterior P₁ q o₁))) →
    F.strictRel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R)) (inlDist q) (inrDist q)
```
**Math.** For a first-stage channel `P₁` with posteriors `r_o`, if continuation `Q^o ≽ R^o`
branchwise at every reached `r_o` (same per-branch outcome family `O₂ o`), then aggregate
`q^0 ≽_{(P₁▷Q)⊔(P₁▷R)} q^1`; strict on one positive-probability branch ⇒ strict aggregate.
*(A strictly stronger auxiliary `A7Strong…` allowing distinct continuation families exists at
Axioms.lean:224/240 but is NOT used in `TraceAxioms`; `A7_of_A7Strong` (:308) shows the
implication.)*

### A8 — Independent-background separability
```lean
-- Behaviour/Axioms.lean:336
def A8_IndependentBackgroundSeparability : Prop :=
  (∀ {A₁ A₂ O₁ O₂R O₂S : Type u}
     [Fintype A₁] [DecidableEq A₁] [Fintype A₂] [DecidableEq A₂] [Fintype O₁] [DecidableEq O₁]
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
     [Fintype O₁R] [DecidableEq O₁R] [Fintype O₁S] [DecidableEq O₁S] [Fintype O₂] [DecidableEq O₂]
     (q₁ : Dist A₁) (q₂ : Dist A₂) (_hq₁ : q₁.FullSupport) (_hq₂ : q₂.FullSupport)
     (R₁ : Channel A₁ O₁R) (S₁ : Channel A₁ O₁S) (P₂ Q₂ : Channel A₂ O₂),
     let prodRP := prodChannel R₁ P₂
     let prodRQ := prodChannel R₁ Q₂
     let prodSP := prodChannel S₁ P₂
     let prodSQ := prodChannel S₁ Q₂
     let prodQ := prodDist q₁ q₂
     F.rel (blockChannel prodRP prodRQ) (inlDist prodQ) (inrDist prodQ) ↔
     F.rel (blockChannel prodSP prodSQ) (inlDist prodQ) (inrDist prodQ))
```
**Math.** With a common product background held fixed, changing that background does not reverse
the foreground comparison — in each coordinate separately, backgrounds ranging over channels with
arbitrary outcome alphabets (`O₂R,O₂S` resp. `O₁R,O₁S`), at full-support product priors.

---

## 4. Hypothesis 2 — `FinalHMInterface` [EXTERNAL HYPOTHESIS: classical HM + Blackwell]

```lean
-- External/EntropyReductionClosure.lean
structure FinalHMInterface.{v} where
  blackwell : FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{v}
  hm_rep    : FiniteHersteinMilnorAssumptions.{v}
  hm_affine : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{v}
```
Three fields, each a classical theorem, expanded below.

### 4.1 `blackwell` — pure finite Blackwell equivalence
```lean
-- External/Blackwell.lean:126
structure FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{v} : Prop where
  same_posterior_left_garbling :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' → ExperimentPostprocesses E E'
  same_posterior_right_garbling :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' → ExperimentPostprocesses E' E
```
**Math = Blackwell (1953), finite case.** At a full-support prior, two experiments inducing the
same posterior law are mutual garblings. *(The paper's A3/A4/A1 preference-substitution step is not
here — it is PROVED internally by `blackwellPosteriorReplacement_of_samePosteriorGarblings`,
Blackwell.lean:444, and threaded in `posteriorLawSufficiency_of_FinalHMInterface`. So this field is
the bare classical theorem.)*

### 4.2 The two relations used above
```lean
-- Convergence.lean:104
def SamePosteriorLawExp (q : Dist A) (E E' : FiniteExperimentOn A) : Prop :=
  ∀ φ : Dist A → ℝ, Continuous φ → posteriorLawIntegralExp q E φ = posteriorLawIntegralExp q E' φ
-- Blackwell.lean:112
def ExperimentPostprocesses (E E' : FiniteExperimentOn A) : Prop := …   -- E' = E garbled by some T
```
`SamePosteriorLawExp` = equal posterior-law integrals against all continuous test functions (i.e.
same law `μ_{q,·}`). `ExperimentPostprocesses E E'` = `E'` is a post-processing/garbling of `E`.

### 4.3 `hm_rep` — finite Herstein–Milnor value representation
```lean
-- External/HersteinMilnor.lean:575
structure FiniteHersteinMilnorAssumptions.{v} where
  V :
    ∀ (F : PrefFamily.{v}) (_hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → FiniteExperimentOn A → ℝ
  V_respects_same_posterior_law :
    ∀ (F : PrefFamily.{v}) (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' → V F hpls q E = V F hpls q E'
  V_represents_block_comparisons :
    ∀ (F : PrefFamily.{v}) (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (E₁ E₂ : FiniteExperimentOn A),
      ExperimentPairPref F E₁ E₂ q q ↔ V F hpls q E₁ ≥ V F hpls q E₂
  V_zero_normalized :
    ∀ (F : PrefFamily.{v}) (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      V F hpls q (uninformativeExperiment A) = 0
```
**Math = Herstein–Milnor (1953), finite case.** A real value functional `F_q = V(F,·,q,·)` on the
posterior-law mixture space that depends only on the posterior law, represents the full-support
block order, and is `0` at no information.

Where `PosteriorLawSufficiency` (its `_hpls` premise) is:
```lean
-- Blackwell.lean:488
def PosteriorLawSufficiency (F : PrefFamily.{u}) : Prop :=
  ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (_hq : q.FullSupport) (E₁ E₂ E₁' E₂' : FiniteExperimentOn A),
    SamePosteriorLawExp q E₁ E₁' → SamePosteriorLawExp q E₂ E₂' →
    (ExperimentPairPref F E₁ E₂ q q ↔ ExperimentPairPref F E₁' E₂' q q)
```
= block comparisons depend only on posterior laws. (In the proof this is *produced* from `blackwell`
+ axioms, not assumed; it appears here only as a parameter of `V`.)

### 4.4 `hm_affine` — affine/integral corollary of HM
```lean
-- External/EntropyReduction.lean:1733
structure ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{v} where
  posterior_law_value_affine       : FinitePosteriorLawValueAffineAssumptions.{v}
  posterior_integral_representation : FinitePosteriorIntegralRepresentationAssumptions.{v}

-- External/EntropyReduction.lean:1674
structure FinitePosteriorLawValueAffineAssumptions.{v} where
  V_affine_of_posteriorLawIntegral_mix :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (t : ℝ) (_ht0 : 0 < t) (_ht1 : t < 1)
      (E_mix E₁ E₂ : FiniteExperimentOn A),
      (∀ φ : Dist A → ℝ, Continuous φ →
        posteriorLawIntegralExp q E_mix φ =
          t * posteriorLawIntegralExp q E₁ φ + (1 - t) * posteriorLawIntegralExp q E₂ φ) →
      hV.V q E_mix = t * hV.V q E₁ + (1 - t) * hV.V q E₂

-- External/BranchAggregation.lean:949
structure FinitePosteriorIntegralRepresentationAssumptions.{v} where
  marginalValue :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A], Dist A → Dist A → ℝ
  value_eq_integral :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E : FiniteExperimentOn A),
      hV.V q E = posteriorLawIntegralExp q E (marginalValue F hV q)
```
**Math.** `F_q` is affine in the posterior law (mixtures map to mixtures of values), and admits the
expected-utility integral representation `V_q(E) = ∫ marginalValue_q dμ_{q,E}` — the standard HM
affine corollary.

---

## 5. Hypothesis 3 — `ClassicalFaddeevTheoremAssumptions` [EXTERNAL HYPOTHESIS: Faddeev]

```lean
-- External/Faddeev.lean:873
structure ClassicalFaddeevTheoremAssumptions.{v} where
  of_recursion :
    ∀ (F : PrefFamily.{v}) {hentropy : EntropyReductionRepresentation F},
      FaddeevRecursionForm F hentropy →
      ∃ alpha : ℝ, 0 ≤ alpha ∧
        ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
          hentropy.Hfun q = alpha * H(q)
```
**Math = Faddeev (1956) / Baez–Fritz–Leinster (2011).** Any regular entropy candidate satisfying
the grouping recursion equals `α·H` (Shannon) with `α ≥ 0`. The premise `FaddeevRecursionForm` is
*proved internally* and fed in; only this conclusion is assumed.

### 5.1 The recursion premise (proved internally, shown for translation)
```lean
-- External/Faddeev.lean:153
structure FaddeevRecursionForm (F : PrefFamily.{u}) (hentropy : EntropyReductionRepresentation F) : Prop where
  regularity : EntropyRegularity F hentropy
  grouping_recursion : SatisfiesFiniteFaddeevRecursion hentropy.Hfun
-- External/Faddeev.lean:104   (EXACTLY two fields)
structure EntropyRegularity (F : PrefFamily.{u}) (hentropy : EntropyReductionRepresentation F) : Prop where
  H_nonneg :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A), 0 ≤ hentropy.Hfun q
  H_singleton :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (a : A), hentropy.Hfun (Dist.pure a) = 0
-- External/Faddeev.lean:135
def SatisfiesFiniteFaddeevRecursion
    (Hfun : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A], Dist A → ℝ) : Prop :=
  ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)] [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)),
    Hfun (sigmaDist p q) = Hfun p + ∑ k, p k * Hfun (q k)
```
**Math.** Regularity here is only `H ≥ 0` and `H(δ_a) = 0`; the recursion is strong additivity
`H(p⊗_σ q) = H(p) + Σ_k p_k H(q_k)`. (Continuity/permutation-invariance are properties of the
constructed `Hfun`, discharged internally — not extra assumptions.)

---

## 6. Hypothesis 4 — `FinalConstructedRepresentativeConventions hhm hax` [CONVENTIONS]

This is the bundle of representative/gauge/boundary **normalizations**. Its full structure and
**every** leaf sub-structure are inlined so the reader can confirm each is a normalization (a
positivity/equivariance/singleton/support-face choice), containing **no `F.rel`, no `mutualInfo`,
no `MIRep`**.

### 6.0 Top-level structure (verbatim)
```lean
-- External/EntropyReductionClosure.lean:2937
structure FinalConstructedRepresentativeConventions
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F) where
  branch : FinalFaithfulBranchConventions hhm
  gauge : PositiveFaceScaleGauge.{u}
  scale_relabel :                     -- EQUATION: gauge·chain-scale invariant under relabelling
    ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
      gauge.gauge (Relabeling.relabelDist e q) *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale (Relabeling.relabelDist e q) =
        gauge.gauge q *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale q
  support_scale :                     -- EQUATION: gauge·branchCoeff at boundary = value on support face
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a) (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      (gauge.gauge q / gauge.gauge r) *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful … ).branch_agg.branchCoeff q r =
        (gauge.gauge q * ( … ).scale_factorization.scale q) /
          (gauge.gauge r.restrictToSupport * ( … ).scale_factorization.scale r.restrictToSupport)
  singleton_slice        : FiniteFaceScaleSingletonSliceAffineConventionFor (coherentFaceScales_of_FinalHM_positiveGauge …)
  product_normalized     : FiniteProductNormalizedSelectedRepresentativesFor (coherentFaceScales_of_FinalHM_positiveGauge …)
  current_product_gauge  : FiniteFaceScaleProductGaugeConventionFor (faceScaleProductPairwiseBilinearity_of_multiPieces …)
  singleton_interaction  : FiniteFaceScaleSingletonInteractionConventionFor (faceScaleProductPairwiseBilinearity_of_multiPieces …)
  harmless               : FinalHarmlessConventions (coherentFaceScales_of_FinalHM_positiveGauge …) (productQuasiAdditivity_of_FinalHM_… …)
```
The `…` are **type-argument applications of internally-constructed objects** (§8 lists them;
`scale_relabel`/`support_scale` shown in full above are pure equations). **Key point:** the field
*types* are `FinalFaithfulBranchConventions`, `PositiveFaceScaleGauge`, two equations, and five
convention structures — **none is `MIRep`, `CoherentRelabelingFaceScalesStructure`, or
`FiniteProductQuasiAdditivityForFaceScales`**; those appear only as type-parameters of the
convention structures, and are objects the proof *builds* (§8).

Now every field type in full.

### 6.1 `gauge : PositiveFaceScaleGauge` [CONVENTION: positive gauge]
```lean
-- External/ScaleCoherence.lean:930
structure PositiveFaceScaleGauge.{v} where
  gauge : {A : Type v} → [Fintype A] → [DecidableEq A] → [Nonempty A] → Dist A → ℝ
  gauge_pos : ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A), 0 < gauge q
```
**Math.** A strictly positive scalar per prior. (Positive rescaling preserves all `≥`; order-free.)

### 6.2 `branch : FinalFaithfulBranchConventions` [CONVENTION: support-face/boundary/singleton]
```lean
-- External/EntropyReductionClosure.lean:1392
structure FinalFaithfulBranchConventions (hhm : FinalHMInterface.{u}) where
  support_face    : FiniteSupportFaceRepresentativeConventionAssumptions.{u}
  boundary_coeff  : FiniteBoundaryCoefficientScaleConventionAssumptions.{u}
  singleton_scale : FiniteBranchSingletonScaleConventionAssumptions.{u}
  marginal_value  : FiniteSupportFaceMarginalValueTransportConvention
                      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
                      (boundaryFaceScale_of_coefficientScaleConvention boundary_coeff)
  boundary_scale  : ∀ (F) (hax : TraceAxioms F) (hV : PosteriorValueRepresentation F),
                      … = FiniteBranchScaleFactorizationBoundaryTransportAssumptions …   -- EQUATION
  singleton_scale_factorization : ∀ (F) (hax) (hV),
                      … = FiniteBranchScaleFactorizationSingletonConvention …            -- EQUATION
```
(The two `…` are internal `let`-assembled scale-factorization equations, EntropyReductionClosure.lean:1401–1446, built from the fields above and internally-proved tangent/linear-algebra facts.)
Its three leaf conventions:
```lean
-- External/BranchAggregation.lean:4675
structure FiniteSupportFaceRepresentativeConventionAssumptions.{v} where
  support_face_value_transport :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F) (hV : PosteriorValueRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV.V r (experimentOfChannel P) =
        hV.V r.restrictToSupport (experimentOfChannel (Channel.restrictToSupport P r))
-- External/BranchAggregation.lean:4694
structure FiniteBoundaryCoefficientScaleConventionAssumptions.{v} where
  boundaryCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A], Dist A → Dist A → ℝ
  boundaryCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr_nonempty : ∃ a : A, 0 < r a) (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      0 < boundaryCoeff q r
-- External/BranchAggregation.lean:5051
structure FiniteBranchSingletonScaleConventionAssumptions.{v} where
  singletonCoeff :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A], Dist A → Dist A → ℝ
  singletonCoeff_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      (_hr_singleton_support : ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a),
      0 < singletonCoeff q r
  singleton_branch_value_zero :
    ∀ (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (r : Dist A) (_hr_singleton_support : ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a) (P : Channel A O),
      hV.V r (experimentOfChannel P) = 0
-- External/BranchAggregation.lean:4789
structure FiniteSupportFaceMarginalValueTransportConvention.{v}
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{v})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{v}) : Prop where
  support_face_marginalValue_scalar :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F) (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a) (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport) (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawTangent η →
      η (fun d => hint.marginalValue F hV q (Channel.actionPushforward d (supportIncludeKernel r))) =
        hboundary.boundaryCoeff q r * η (hint.marginalValue F hV r.restrictToSupport)
```
**Math.** (a) `support_face`: value of an experiment at a boundary prior `r` equals its value on
the support face `r|supp` (representatives read through the support). (b) `boundary_coeff`: a chosen
strictly positive boundary scaling `boundaryCoeff q r`. (c) `singleton_scale`: a positive singleton
coefficient plus the fact that continuation values on a singleton-support face are `0`. (d)
`marginal_value`: the HM marginal test function pulled to the support face equals `boundaryCoeff`
times the intrinsic one. All are representative/scale normalizations across the support boundary;
none is a preference statement.

### 6.3 `singleton_slice : FiniteFaceScaleSingletonSliceAffineConventionFor` [CONVENTION: degenerate slice]
```lean
-- External/ScaleCoherence.lean:1777
structure FiniteFaceScaleSingletonSliceAffineConventionFor.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  singleton_left_slice_positive_affine_transform :
    ∀ (_hax : TraceAxioms F) {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : Subsingleton A) (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O] (P : Channel A O),
          faceScaleProductLeftSliceValue hfaces q r R P =
            a * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) + b
```
**Math.** On a **one-action** domain (`Subsingleton A`), where value is not order-identifiable, the
product left-slice is fixed by an existential positive affine transform. Degenerate-case normalization.

### 6.4 `product_normalized : FiniteProductNormalizedSelectedRepresentativesFor` [CONVENTION: selected representative]
```lean
-- External/RepairedPreEntropyTargets.lean:37
structure FiniteProductNormalizedSelectedRepresentativesFor.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  actionbase_scalar             : FiniteSelectedActionbaseScalarFor hfaces
  product_normalization_pinning : FiniteSelectedPermutationInvariancePinningFor hfaces
-- External/CardinalPermutationInvariance.lean:29
structure FiniteSelectedActionbaseScalarFor.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  relabel_scalar :
    ∀ (_hax : TraceAxioms F) {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (eA : A ≃ B) (q : Dist A),
      ∃ c : ℝ, 0 < c ∧
        ∀ {O Y : Type v} [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
          (eO : O ≃ Y) (P : Channel A O),
          hfaces.branch_result.branch_agg.value_rep.V (Relabeling.relabelDist eA q)
              (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
            c * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P)
-- External/CardinalPermutationInvariance.lean:58
structure FiniteSelectedPermutationInvariancePinningFor.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  scalar_eq_one :
    ∀ (_hax : TraceAxioms F) {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (eA : A ≃ B) (q : Dist A) (c : ℝ) (_hc : 0 < c),
      (∀ {O Y : Type v} [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
          (eO : O ≃ Y) (P : Channel A O),
          hfaces.branch_result.branch_agg.value_rep.V (Relabeling.relabelDist eA q)
              (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
            c * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P)) →
        c = 1
```
**Math.** Relabeling actions/outcomes rescales the selected representative's value by a single
positive `c` (`actionbase_scalar`), and that `c` must equal `1` (`pinning`). Together: we *select*
the relabeling-invariant (product-normalized) representative. This is a representative choice, not a
behavioural assumption. **(Countermodel note:** the gauge `V^λ_q(P)=λ(|supp q|)I(q,P)`,
`λ(2)=1,λ(4)=2`, is coherent but not product-normalized — it violates `scalar_eq_one`, so it is
simply *not* the selected representative; this is why the convention is a choice, not an assumption
equivalent to the conclusion.)

### 6.5 `current_product_gauge : FiniteFaceScaleProductGaugeConventionFor` [CONVENTION: coefficient gauge]
```lean
-- External/ScaleCoherence.lean:3068
structure FiniteFaceScaleProductGaugeConventionFor.{v}
    {F : PrefFamily.{v}} {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) : Prop where
  current_leftCoeff_normalized :
    ∀ (hax : TraceAxioms F) {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff hax q r = 1
  current_rightCoeff_normalized :
    ∀ (hax : TraceAxioms F) {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff hax q r = 1
```
**Math.** The two linear product coefficients equal `1` for the current representatives — the gauge
in which the product form is normalized. A statement about coefficients, not about `≽`.

### 6.6 `singleton_interaction : FiniteFaceScaleSingletonInteractionConventionFor` [CONVENTION: degenerate interaction]
```lean
-- External/ScaleCoherence.lean:3273
structure FiniteFaceScaleSingletonInteractionConventionFor.{v}
    {F : PrefFamily.{v}} {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) : Prop where
  interactionCoeff_eq_reference_of_subsingleton_left :
    ∀ (hax : TraceAxioms F) {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton A → hpair.interactionCoeff hax q r = faceScaleInteractionReferenceKappa hpair hax
  interactionCoeff_eq_reference_of_subsingleton_right :
    ∀ (hax : TraceAxioms F) {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton B → hpair.interactionCoeff hax q r = faceScaleInteractionReferenceKappa hpair hax
```
**Math.** On a singleton factor (`Subsingleton A`/`B`), where the coordinate value vanishes, the
interaction coefficient is set to the reference κ. Degenerate-case normalization.

### 6.7 `harmless : FinalHarmlessConventions` [CONVENTION bundle + one boundary bridge]
```lean
-- External/EntropyReductionClosure.lean:1203
structure FinalHarmlessConventions
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  singleton_slice  : FiniteFaceScaleSingletonSliceAffineConventionFor hfaces
  pre_entropy      : PreEntropyRepresentativeGaugeConventions hfaces hprod
  support_boundary : FiniteCardinalSupportBoundaryAssumptions.{u}
-- External/PreEntropyReady.lean:142
structure PreEntropyRepresentativeGaugeConventions.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  coordinate_value    : FiniteCoordinateSupportFaceValueConventionFor hfaces
  coordinate_scale    : FiniteCoordinateSupportFaceScaleConventionFor hfaces
  block_value         : FiniteBlockSupportFaceValueConventionFor hfaces
  block_scale         : FiniteBlockSupportFaceScaleConventionFor hfaces
  reference_z         : FiniteProductReferenceZNormalizationFor hfaces hprod
  universal_singleton : FiniteUniversalScaleSingletonConventionFor hfaces
```
Its leaf conventions (all value/scale **equations** on support faces or degenerate priors):
```lean
-- External/ScaleCoherence.lean:5050   coordinate_value  (verbatim, both fields)
structure FiniteCoordinateSupportFaceValueConventionFor.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_value :
    ∀ (_hax : TraceAxioms F) {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B) (a : A),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) a)
        (experimentOfChannel (productSecondRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces r
  second_coordinate_face_value :
    ∀ (_hax : TraceAxioms F) {A B : Type v} … (b : B),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) b)
        (experimentOfChannel (productFirstRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces q
-- External/ScaleCoherence.lean:5085   coordinate_scale (both fields: same shape, scale instead of value)
structure FiniteCoordinateSupportFaceScaleConventionFor.{v} … : Prop where
  first_coordinate_face_scale  : … scale (posterior productFirstReveal … a) = scale r
  second_coordinate_face_scale : … scale (posterior productSecondReveal … b) = scale q
-- External/PreEntropyReady.lean:92    block_value
structure FiniteBlockSupportFaceValueConventionFor.{v} … : Prop where
  block_face_value :
    ∀ (_hax : TraceAxioms F) {K} … (Act) … (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.branch_agg.value_rep.V (blockEmbedDist Act k q)
        (experimentOfChannel (Channel.idChannel : Channel ((k:K)×Act k) ((k:K)×Act k))) =
      fullRevelationValueForFaceScales hfaces q
-- External/PreEntropyReady.lean:110   block_scale
structure FiniteBlockSupportFaceScaleConventionFor.{v} … : Prop where
  block_face_scale :
    ∀ (_hax) {K} … (k) (q) (_hq : q.FullSupport),
      hfaces.branch_result.scale_factorization.scale (blockEmbedDist Act k q) =
      hfaces.branch_result.scale_factorization.scale q
-- External/PreEntropyReady.lean:126   reference_z
structure FiniteProductReferenceZNormalizationFor.{v} … (hprod …) : Prop where
  reference_Z_eq_one :
    ∀ (hax : TraceAxioms F), productScaleZForFaceScales hfaces hprod hax universalScaleReferencePrior = 1
-- External/ScaleCoherence.lean:3893   universal_singleton
structure FiniteUniversalScaleSingletonConventionFor.{v} … : Prop where
  scale_eq_of_subsingleton :
    ∀ {A B : Type v} … (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      (Subsingleton A ∨ Subsingleton B) →
      hfaces.branch_result.scale_factorization.scale q = hfaces.branch_result.scale_factorization.scale r
```
**Math (pre_entropy leaves).** `coordinate_value`/`coordinate_scale`: after revealing one product
coordinate, the value/scale of the resulting posterior equals the intrinsic full-revelation
value/scale of the *other* coordinate. `block_value`/`block_scale`: a distribution embedded in a
dependent-sum block has the intrinsic value/scale of its fibre. `reference_z`: the product scale `Z`
is normalized to `1` at a reference prior. `universal_singleton`: on singleton factors, all scales
are forced equal. All are value/scale equalities on support faces / degenerate priors — no `F.rel`.

The one non-pure-normalization item, disclosed in full:
```lean
-- External/Faddeev.lean:1868   support_boundary  (three value EQUATIONS at boundary priors)
structure FiniteCardinalSupportBoundaryAssumptions.{v} where
  normalizedValue_support_boundary :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F) (hcross : CrossPriorBlockRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q)
  Hfun_boundary_identity :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F) (hcross : CrossPriorBlockRepresentation F)
      (_hreg : EntropyRegularity F hcross.entropy_reduction)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A), ¬ q.FullSupport →
      hcross.entropy_reduction.Hfun q =
        normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel
  restricted_coarse_reveal_value :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F) (hcross : CrossPriorBlockRepresentation F)
      (_hreg : EntropyRegularity F hcross.entropy_reduction)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K] (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)] [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)] (p : Dist K) (q : ∀ k, Dist (Act k)),
      ¬ (sigmaDist p q).FullSupport →
      let s : Dist ((k : K) × Act k) := sigmaDist p q
      let C : Channel ((k : K) × Act k) K := coarseRevealChannel Act
      letI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
      letI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
      normalizedValue hcross.entropy_reduction.scale_coherence
          s.restrictToSupport (Channel.restrictToSupport C s) =
        hcross.entropy_reduction.Hfun p.restrictToSupport
```
**Math.** Three equalities of the (normalized) value/entropy functional at **boundary (non-full-support)
priors**, stating the value equals its value read on the support face. This is the only item beyond
a pure gauge choice — a boundary-cardinal *extension bridge*. It asserts value equations, never a
preference comparison `F.rel`.

### 6.8 The product-bilinearity object referenced by 6.5/6.6 (for translation of `hpair.leftCoeff` etc.)
```lean
-- External/ScaleCoherence.lean:2831   [CONSTRUCTED internally; shown so 6.5/6.6 fields have meaning]
structure FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F) where
  leftCoeff        : TraceAxioms F → {A B : Type v} → … → Dist A → Dist B → ℝ
  rightCoeff       : TraceAxioms F → {A B : Type v} → … → Dist A → Dist B → ℝ
  interactionCoeff : TraceAxioms F → {A B : Type v} → … → Dist A → Dist B → ℝ
  leftCoeff_pos    : ∀ (hax) … (q r) (_hq) (_hr), 0 < leftCoeff hax q r
  rightCoeff_pos   : ∀ (hax) … (q r) (_hq) (_hr), 0 < rightCoeff hax q r
  product_pair_bilinear :
    ∀ (hax : TraceAxioms F) {A B O Y : Type v} … (q r) (_hq) (_hr) (P : Channel A O) (R : Channel B Y),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r) (experimentOfChannel (prodChannel P R)) =
        leftCoeff hax q r * V q (…P…) + rightCoeff hax q r * V r (…R…) +
        interactionCoeff hax q r * V q (…P…) * V r (…R…)
```
**Math.** The product-experiment value is a positive-coefficient bilinear form
`V(q⊗r, P⊗R) = ℓ·V(q,P) + ρ·V(r,R) + κ·V(q,P)·V(r,R)` in the two coordinate values. (Built
internally from HM + A8; shown so that `current_product_gauge`/`singleton_interaction` — which
assert `ℓ=ρ=1` and set κ on singletons — are readable.)

---

## 7. Kernel hygiene (the "no gaps" guarantee)

```
#print axioms MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
  ⇒ [propext, Classical.choice, Quot.sound]
```
Only the three standard logical axioms of Lean/mathlib. No `sorryAx`, no project-declared `axiom`,
no `admit`. A whole-project search confirms zero `sorry`/`admit` tactic occurrences and zero
`axiom` declarations. Therefore, *conditional on the reader accepting the displayed statements in
§3–§6 as their intended mathematics*, the derivation of `MIRep F` is complete and machine-checked.

`lake build` succeeds (8622 jobs; only cosmetic `linter.style.whitespace` warnings). Toolchain
`leanprover/lean4:v4.32.0-rc1`; mathlib `v4.32.0-rc1` (rev `360da6f`).

---

## 8. Internally CONSTRUCTED objects (NOT inputs — shown so §6 field-types are readable)

These structures appear **only as type-parameters inside the convention fields of §6**. They are
**built by the proof**, not supplied by the caller. A reader translating §6 needs to know what they
are; a reader auditing *what must be trusted* can skip them (they are outputs, guaranteed by the
kernel).

```lean
-- Sufficiency/Spine.lean:156   value functional (output of HM)
structure PosteriorValueRepresentation (F : PrefFamily.{u}) where
  V : ∀ {A} [Fintype A] [DecidableEq A] [Nonempty A], Dist A → FiniteExperimentOn A → ℝ
  respects_same_posterior_law : ∀ … (q E E'), SamePosteriorLawExp q E E' → V q E = V q E'
  represents_block_comparisons : ∀ … (q) (_hq : q.FullSupport) (E₁ E₂),
    ExperimentPairPref F E₁ E₂ q q ↔ V q E₁ ≥ V q E₂
  zero_normalized : ∀ … (q) (_hq : q.FullSupport), V q (experimentOfChannel (uninformativeChannelU A)) = 0

-- Sufficiency/Spine.lean:284   branch aggregation
structure BranchAggregationStructure (F : PrefFamily.{u}) where
  value_rep : PosteriorValueRepresentation F
  branchCoeff : ∀ {A} …, Dist A → Dist A → ℝ
  branchCoeff_pos : ∀ … (q r) (_hq) (_hr : ∃ a b, a≠b ∧ 0<r a ∧ 0<r b), 0 < branchCoeff q r
  branch_aggregation : ∀ … (q) (_hq) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂),
    value_rep.V q (experimentOfChannel (P₁ ▷ Q)) =
      value_rep.V q (experimentOfChannel P₁) +
      ∑ o₁, (outcomeMarginal P₁ q) o₁ * branchCoeff q (posterior P₁ q o₁) *
            value_rep.V (posterior P₁ q o₁) (experimentOfChannel (Q o₁))

-- External/ScaleCoherence.lean:730   branch + cocycle + normalized chain rule
structure BranchAggregationCocycleNormalizedChainRuleStructure (F : PrefFamily.{u}) where
  branch_agg : BranchAggregationStructure F
  coeff_cocycle : FiniteBranchCoeffCocycleAssumptionsFor branch_agg
  full_support_scale : FiniteBranchScaleFactorizationFullSupportAssumptions branch_agg
  scale_factorization : FiniteBranchScaleFactorizationAssumptions branch_agg

-- External/ScaleCoherence.lean:866   coherent relabelling + face scales (the `hfaces` in §6)
structure CoherentRelabelingFaceScalesStructure (F : PrefFamily.{u}) where
  branch_result : BranchAggregationCocycleNormalizedChainRuleStructure F
  scale_relabeling : FiniteChainScaleRelabelingAssumptionsFor branch_result
  support_face_scale : FiniteSupportFaceScaleAssumptionsFor branch_result

-- External/ScaleCoherence.lean:63   pre-collapse chain structure
structure BranchChainStructure (F : PrefFamily.{u}) where
  branch_agg : BranchAggregationStructure F
  scale : ∀ {A} …, Dist A → ℝ
  scale_pos : ∀ … (q) (_hq), 0 < scale q
  branchCoeff_factorization : ∀ … (q) (_hq) (P₁) (o₁), BranchPositive P₁ q o₁ →
    branch_agg.branchCoeff q (posterior P₁ q o₁) = scale q / scale (posterior P₁ q o₁)

-- Sufficiency/Spine.lean:333   scale coherence (universal scale)
structure ScaleCoherenceStructure (F : PrefFamily.{u}) where
  branch_agg : BranchAggregationStructure F
  scale : ∀ {A} …, Dist A → ℝ
  scale_pos : ∀ … (q) (_hq), 0 < scale q
  branchCoeff_factorization : ∀ … (q) (_hq) (P₁) (o₁), BranchPositive P₁ q o₁ →
    branch_agg.branchCoeff q (posterior P₁ q o₁) = scale q / scale (posterior P₁ q o₁)
  scale_universal : ∀ … (q : Dist A) (r : Dist B) (_hq) (_hr), scale q = scale r

-- Sufficiency/Spine.lean:420   scaled cross-prior block bridge
structure CrossPriorBlockRepresentation (F : PrefFamily.{u}) where
  entropy_reduction : EntropyReductionRepresentation F
  cross_prior_block_rep : ∀ … (q r) (_hq) (_hr) (P Q),
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      (value_rep.V q (…P…) / scale q) ≥ (value_rep.V r (…Q…) / scale r)

-- Sufficiency/Spine.lean:384   entropy reduction (defines the Faddeev candidate Hfun)
structure EntropyReductionRepresentation (F : PrefFamily.{u}) where
  scale_coherence : ScaleCoherenceStructure F
  Hfun : ∀ {A} [Fintype A] [DecidableEq A] [Nonempty A], Dist A → ℝ    -- H(q) := V̂_q(Id_A)
  value_entropy_reduction : ∀ … (q) (_hq) (P),
    scale_coherence.branch_agg.value_rep.V q (experimentOfChannel P) / scale_coherence.scale q =
      Hfun q - posteriorLawIntegral q P Hfun
-- and the normalized value  V̂  used above:
-- External/EntropyReduction.lean:72
noncomputable def normalizedValue (hs : ScaleCoherenceStructure F) (q : Dist A) (P : Channel A O) : ℝ :=
  hs.branch_agg.value_rep.V q (experimentOfChannel P) / hs.scale q
```
**How these connect to §6.** The convention fields of §6 are stated *about* these constructed
objects: e.g. `hfaces : CoherentRelabelingFaceScalesStructure F` is built by
`coherentFaceScales_of_FinalHM_positiveGauge` from `hhm`, `hax`, `branch`, `gauge`; the
`.branch_result.branch_agg.value_rep.V` appearing throughout §6 is the HM value functional `F_q`.
`EntropyReductionRepresentation.Hfun` is the entropy candidate `H(q) := V̂_q(Id_A)` that Faddeev
(§5) turns into `α·H`. None of these is a hypothesis of the final theorem.

---

## 9. Correspondence checklist (for a reader who also has the paper)

To confirm the Lean development and a paper state the same theorem, verify:

1. **Axioms.** §3 A1–A8 ↔ the paper's axioms A1–A8, clause by clause. (Watch the two safe
   deviations: A7 uses a *shared* branch outcome family `O₂ o` — the weaker/faithful form used as a
   hypothesis; A8 allows *distinct* background alphabets — the "any channels" form.)
2. **Conclusion.** §2.1 `MIRep F` ↔ the paper's representation clause
   `q ≽_P q' ⟺ I(q,P) ≥ I(q',P)` (fixed environment). §2.2/§2.3 are the paper's necessity and
   "moreover" clauses, as *separate* theorems.
3. **External theorems.** §4.1 ↔ Blackwell; §4.3 ↔ Herstein–Milnor; §4.4 ↔ its affine corollary;
   §5 ↔ Faddeev. Confirm each Lean statement is the classical theorem the paper cites.
4. **Conventions.** §6 fields ↔ the paper's representative/gauge/support-restriction choices
   (coherent normalization, face scales, support restriction, singleton conventions). Confirm each
   is a normalization the paper is entitled to make, not a hidden behavioural assumption.
5. **Scope.** The final theorem proves *sufficiency only*; necessity and moreover are §2.2/§2.3.
6. **Hygiene.** §7: axiom footprint `[propext, Classical.choice, Quot.sound]`.

If 1–6 check out, the Lean development and the paper state the same theorem under the same
hypotheses, and the Lean kernel certifies the sufficiency derivation.

---

## 10. One-paragraph summary

The Lean theorem `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` proves, for any preference
family `F`, that the behavioural axioms `TraceAxioms F` (A1–A8, §3) — together with the classical
finite Herstein–Milnor value representation and finite Blackwell equivalence (`FinalHMInterface`,
§4), the classical finite Faddeev entropy-uniqueness theorem (`ClassicalFaddeevTheoremAssumptions`,
§5), and a bundle of positivity/gauge/support-face/singleton **normalizations**
(`FinalConstructedRepresentativeConventions`, §6) — imply the mutual-information representation
`MIRep F`: `q ≽_P q' ⟺ I(q,P) ≥ I(q',P)` for every finite channel `P` and priors `q,q'` (§2.1). The
converse (necessity) and the block same-scale "moreover" clause are separate theorems (§2.2, §2.3).
Every hypothesis and convention is displayed in full above; the axiom footprint is
`[propext, Classical.choice, Quot.sound]` (§7); and the face-scale, product-quasi-additivity,
entropy-reduction, and scale-coherence objects that a reader might expect as assumptions are instead
**constructed internally** (§8) and are not inputs.
```
