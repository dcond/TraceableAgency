/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence
import TraceableAgency.PureTrace.Support.EntropyReduction
import TraceableAgency.PureTrace.Support.EntropyReduction.Spine
import TraceableAgency.PureTrace.Support.BranchAggregation.Compatibility
import TraceableAgency.PureTrace.Support.ScaleCoherence.Compatibility
import TraceableAgency.PureTrace.Support.SupportRestriction
import TraceableAgency.PureTrace.Support.Blackwell

/-!
# Faddeev Entropy Characterisation Interface and Paper-Specific Bridges

This file states the generic finite Faddeev interface and proves the
paper-specific bridges showing that the entropy function derived from the
sufficiency proof satisfies it. The generic interface is discharged by the
Lean proof in `TraceableAgency.PureTrace.Support.GenericFaddeev`.

## Main definitions

* `EntropyRegularity` - nonnegativity and point-mass zero for the entropy function.
* `FaddeevRecursionForm` - the finite grouping recursion for that entropy function.
* `FiniteFaddeevStandardHypotheses` - the ordinary, preference-free hypotheses.
* `ClassicalFaddeevTheoremAssumptions` - the classical theorem, stated only for
  an abstract entropy functional.
* `relabel_rel_of_axioms` - finite action/outcome relabeling invariance, now
  proved from main-text A6, A7, A5, and A1 transitivity.

## Status

The audit schema and paper-specific derivations are:
1. Based on the paper's Lemma faddeevsketch, Faddeev-recursion part
2. Matches Faddeev's classical theorem (1956), now formally proved in
   `TraceableAgency.PureTrace.Support.GenericFaddeev`
3. Split into explicit, auditable assumptions, with relabeling internalized
4. No anonymous `axiom` declarations are used

The Faddeev entropy theorem derives:
0. **Entropy regularity**: H is nonnegative and zero on point masses/singletons
1. **Faddeev recursion**: H satisfies the grouping/strong-additivity recursion
2. **Strict positivity witness**: pure-trace nontriviality and internally proved finite relabeling invariance
   give H(q) > 0 at a fixed two-point full-support prior
3. **Shannon form**: H(q) = α Sh(q) for some α > 0
4. **Block equivalence**: proved directly from `PureTraceConditions.blockCoherence`

## References

* Paper/appendix_a_pure_trace_v10.tex, Lemma `pt:lem:faddeevsketch`
* Faddeev (1956), "On the concept of entropy of a finite probabilistic scheme"
* Baez-Fritz-Leinster (2011), Theorem 6

The proof structure:
- Derive Faddeev's grouping recursion from entropy reduction and action-processing neutrality
- Apply Faddeev's classical theorem
- Local pure-trace nontriviality plus reverse block orientation forces α > 0
-/

namespace TraceableAgency

universe u

open Filter Topology

/-!
## Faddeev Entropy External Assumption

The Faddeev theorem states that a function H on finite probability distributions
satisfying:
1. Continuity on each simplex
2. Invariance under relabelling (permutation)
3. Expansibility: H(q, 0) = H(q)
4. Strong additivity / grouping recursion

is a non-negative multiple of Shannon entropy.

The paper-specific work is:
- Show that the entropy function Hfun from EntropyReductionRepresentation
  has the regularity properties needed by Faddeev, including nonnegativity and
  singleton-zero
- The grouping recursion follows from entropy reduction and action-processing neutrality
- Local pure-trace nontriviality, via the cross-prior representation and reverse
  block orientation, forces α > 0

Stage 9D splits the paper-specific derivations from the classical theorem.
-/

/--
**Duplicate-Block Equivalence from PureTraceConditions**

The duplicate-environment clause needed by `FaddeevEntropyForm` is exactly the
`blockCoherence.duplication` field (main-text A5), so it is internal and no longer part of any Faddeev
external assumption.
-/
theorem a3_block_equivalence_of_traceAxioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    ∀ {A O : Type u} [Fintype A] [DecidableEq A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q q' : Dist A),
      F.rel P q q' ↔ F.rel (blockChannel P P) (inlDist q) (inrDist q') := by
  exact hax.blockCoherence.duplication

/--
**Entropy Regularity**

Regularity hypotheses on the entropy function attached to a fixed
`EntropyReductionRepresentation`.
-/
structure EntropyRegularity
    (F : PrefFamily.{u}) (hentropy : EntropyReductionRepresentation F) : Prop where
  H_nonneg :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      0 ≤ hentropy.Hfun q
  H_singleton :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (a : A),
      hentropy.Hfun (Dist.pure a) = 0

/--
**Finite Entropy Regularity from Axioms Assumption**

Paper-specific bridge: PureTraceConditions plus the constructed entropy-reduction
representation give the Faddeev regularity hypotheses.
-/
structure FiniteEntropyRegularityFromAxiomsAssumptions.{v} where
  of_entropy_reduction :
    ∀ (F : PrefFamily.{v}),
      PureTraceConditions F →
      ∀ (hentropy : EntropyReductionRepresentation F),
      EntropyRegularity F hentropy

/--
**Finite Faddeev Recursion Predicate**

The strong-additivity/grouping equation for a polymorphic entropy candidate.
It uses the project's dependent `sigmaDist`: draw a block `k ~ p`, then draw
an element from the within-block distribution `q k`.
-/
def SatisfiesFiniteFaddeevRecursion
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ) : Prop :=
  ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)),
    Hfun (sigmaDist p q) =
      Hfun p + ∑ k, p k * Hfun (q k)

/--
**Faddeev Recursion Form**

The entropy function is regular and satisfies the finite grouping recursion.
-/
structure FaddeevRecursionForm
    (F : PrefFamily.{u}) (hentropy : EntropyReductionRepresentation F) : Prop where
  regularity : EntropyRegularity F hentropy
  grouping_recursion : SatisfiesFiniteFaddeevRecursion hentropy.Hfun

/-!
## The preference-free classical Faddeev boundary

The next definitions contain no preference family, channel, posterior value,
or paper-specific representation.  They state the usual finite Faddeev input
for an abstract entropy functional.  We use the standard "binary interior
continuity + expansibility" variant: expansibility reads boundary faces in
lower dimension, while continuity is needed only on the positive binary
simplex.  This is equivalent to the familiar formulation with continuity on
closed simplices.
-/

/-- The binary probability vector `(t, 1-t)`, on a universe-polymorphic
two-point type. -/
noncomputable def faddeevBinaryDist
    (t : Set.Icc (0 : ℝ) 1) : Dist (ULift.{u, 0} Bool) where
  prob := fun b => if b.down then t.1 else 1 - t.1
  nonneg := by
    intro b
    split
    · exact t.2.1
    · linarith [t.2.2]
  sum_eq_one := by
    rw [← (Equiv.ulift (α := Bool)).symm.sum_comp
      (fun b : ULift.{u, 0} Bool => if b.down then t.1 else 1 - t.1)]
    simp [Fintype.sum_bool, Equiv.ulift]

/-- Restrict the binary path to the positive (full-support) simplex. -/
noncomputable def faddeevBinaryDistInterior
    (t : Set.Ioo (0 : ℝ) 1) : Dist (ULift.{u, 0} Bool) :=
  faddeevBinaryDist ⟨t.1, le_of_lt t.2.1, le_of_lt t.2.2⟩

theorem faddeevBinaryDistInterior_fullSupport
    (t : Set.Ioo (0 : ℝ) 1) :
    (faddeevBinaryDistInterior t).FullSupport := by
  intro b
  rcases b with ⟨b⟩
  cases b <;> simp [faddeevBinaryDistInterior, faddeevBinaryDist, t.2.1, t.2.2]

/-- Standard finite Faddeev hypotheses for an abstract entropy functional.

`support_restriction` is expansibility in support-face form: deleting all
zero-probability labels leaves the value unchanged.  Together with
`fullSupport_relabel`, it is exactly invariance under finite bijections and
adjoining/deleting zero-probability states. -/
structure FiniteFaddeevStandardHypotheses
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ) : Prop where
  nonnegative :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      0 ≤ Hfun q
  pointMass_zero :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (a : A),
      Hfun (Dist.pure a) = 0
  fullSupport_relabel :
    ∀ {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A),
      q.FullSupport →
      Hfun (Relabeling.relabelDist e q) = Hfun q
  support_restriction :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      Hfun q = Hfun q.restrictToSupport
  binary_continuous :
    Continuous
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        Hfun (faddeevBinaryDistInterior t))
  strong_additivity :
    SatisfiesFiniteFaddeevRecursion Hfun

/--
**Coarse Block-Reveal Channel**

On a dependent sigma action space, this channel reveals only the outer block
index.
-/
noncomputable def coarseRevealChannel
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] :
    Channel ((k : K) × Act k) K :=
  fun ka => Dist.pure ka.1

@[simp]
theorem coarseRevealChannel_apply_same
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)]
    (ka : (k : K) × Act k) :
    coarseRevealChannel Act ka ka.1 = 1 := by
  simp [coarseRevealChannel]

theorem coarseRevealChannel_apply_ne
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)]
    (ka : (k : K) × Act k) {j : K} (h : j ≠ ka.1) :
    coarseRevealChannel Act ka j = 0 := by
  simp [coarseRevealChannel, Dist.pure_apply_ne, h]

/--
Deterministic action kernel that projects a sigma action to its coarse block.
It is the same stochastic matrix as `coarseRevealChannel`, used in the action
kernel role required by main-text A7.
-/
noncomputable def coarseProjectKernel
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] :
    Channel.ActionKernel ((k : K) × Act k) K :=
  fun ka => Dist.pure ka.1

@[simp]
theorem coarseProjectKernel_apply_same
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)]
    (ka : (k : K) × Act k) :
    coarseProjectKernel Act ka ka.1 = 1 := by
  simp [coarseProjectKernel]

theorem coarseProjectKernel_apply_ne
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)]
    (ka : (k : K) × Act k) {j : K} (h : j ≠ ka.1) :
    coarseProjectKernel Act ka j = 0 := by
  simp [coarseProjectKernel, Dist.pure_apply_ne, h]

/-- The coarse reveal marginal of a sigma distribution is the coarse prior. -/
theorem outcomeMarginal_coarseReveal_sigmaDist
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Channel.outcomeMarginal (coarseRevealChannel Act) (sigmaDist p q) = p := by
  ext k
  simp only [Channel.outcomeMarginal_apply]
  rw [Fintype.sum_sigma]
  trans ∑ a : Act k, p k * q k a
  · rw [Finset.sum_eq_single k]
    · simp [coarseRevealChannel, sigmaDist_apply]
    · intro j _ hjk
      apply Finset.sum_eq_zero
      intro a _
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [coarseRevealChannel, sigmaDist_apply, hkj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · rw [← Finset.mul_sum, (q k).sum_eq_one, mul_one]

/-- Projecting a sigma distribution to its coarse block recovers the coarse prior. -/
theorem actionPushforward_sigmaDist_coarseProject
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Channel.actionPushforward (sigmaDist p q) (coarseProjectKernel Act) = p := by
  ext k
  simp only [Channel.actionPushforward]
  rw [Fintype.sum_sigma]
  trans ∑ a : Act k, p k * q k a
  · rw [Finset.sum_eq_single k]
    · simp [coarseProjectKernel, sigmaDist_apply]
    · intro j _ hjk
      apply Finset.sum_eq_zero
      intro a _
      have hkj : k ≠ j := fun h => hjk h.symm
      simp [coarseProjectKernel, sigmaDist_apply, hkj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · rw [← Finset.mul_sum, (q k).sum_eq_one, mul_one]

/--
The coarse identity channel is the Bayesian completion obtained by projecting
sigma actions and observing the coarse-reveal channel.
-/
theorem coarseReveal_isBayesPushforwardCompletion_project
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Channel.IsBayesPushforwardCompletion
      (coarseRevealChannel Act) (sigmaDist p q) (coarseProjectKernel Act)
      (Channel.idChannel : Channel K K) := by
  intro k hk o
  have hpush :
      (Channel.actionPushforward (sigmaDist p q) (coarseProjectKernel Act)) k = p k := by
    exact congrArg (fun d : Dist K => d k)
      (actionPushforward_sigmaDist_coarseProject Act p q)
  have hk_pos : p k > 0 := by
    rw [← hpush]
    exact hk
  by_cases hok : o = k
  · subst o
    simp only [Channel.idChannel, Dist.pure_apply_self]
    rw [hpush]
    have hnum :
        (∑ ka : (k : K) × Act k,
          (sigmaDist p q) ka *
            coarseProjectKernel Act ka k *
            coarseRevealChannel Act ka k) = p k := by
      rw [Fintype.sum_sigma]
      trans ∑ a : Act k, p k * q k a
      · rw [Finset.sum_eq_single k]
        · simp [coarseProjectKernel, coarseRevealChannel, sigmaDist_apply]
        · intro j _ hjk
          apply Finset.sum_eq_zero
          intro a _
          have hkj : k ≠ j := fun h => hjk h.symm
          simp [coarseProjectKernel, coarseRevealChannel, sigmaDist_apply, hkj]
        · intro hk_mem
          exact absurd (Finset.mem_univ k) hk_mem
      · rw [← Finset.mul_sum, (q k).sum_eq_one, mul_one]
    rw [hnum]
    field_simp [ne_of_gt hk_pos]
  · rw [Channel.idChannel, Dist.pure_apply_ne k o hok]
    rw [Fintype.sum_sigma]
    have hsum_zero :
        (∑ j : K, ∑ a : Act j,
          (sigmaDist p q) ⟨j, a⟩ *
            coarseProjectKernel Act ⟨j, a⟩ k *
            coarseRevealChannel Act ⟨j, a⟩ o) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      apply Finset.sum_eq_zero
      intro a _
      by_cases hjk : j = k
      · subst j
        simp [coarseProjectKernel, coarseRevealChannel, sigmaDist_apply, hok]
      · have hkj : k ≠ j := fun h => hjk h.symm
        simp [coarseProjectKernel, coarseRevealChannel, sigmaDist_apply, hkj]
    rw [hsum_zero]
    simp

/--
Stochastic refinement kernel: from a coarse block `k`, sample an action inside
the fibre according to `q k`.
-/
noncomputable def coarseRefineKernel
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (q : ∀ k, Dist (Act k)) :
    Channel.ActionKernel K ((k : K) × Act k) :=
  fun k => blockEmbedDist Act k (q k)

/-- Refining the coarse prior by the fibre distributions gives `sigmaDist`. -/
theorem actionPushforward_coarseRefine
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Channel.actionPushforward p (coarseRefineKernel Act q) = sigmaDist p q := by
  ext ka
  rcases ka with ⟨j, a⟩
  change (∑ k : K, p k * blockEmbedDist Act k (q k) ⟨j, a⟩) = p j * q j a
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [blockEmbedDist_apply_ne Act (fun h : j = k => hkj h.symm) (q k) a]
    simp
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/--
The coarse-reveal channel is the Bayesian completion obtained by refining a
coarse action and then fully revealing the original coarse action.
-/
theorem coarseReveal_isBayesPushforwardCompletion_refine
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Channel.IsBayesPushforwardCompletion
      (Channel.idChannel : Channel K K) p (coarseRefineKernel Act q)
      (coarseRevealChannel Act) := by
  intro ka hka o
  rcases ka with ⟨j, a⟩
  have hpush :
      (Channel.actionPushforward p (coarseRefineKernel Act q)) ⟨j, a⟩ =
        sigmaDist p q ⟨j, a⟩ := by
    exact congrArg (fun d : Dist ((k : K) × Act k) => d ⟨j, a⟩)
      (actionPushforward_coarseRefine Act p q)
  have hden_pos : p j * q j a > 0 := by
    rw [← sigmaDist_apply, ← hpush]
    exact hka
  by_cases hoj : o = j
  · subst o
    simp only [coarseRevealChannel, Dist.pure_apply_self]
    rw [hpush]
    unfold coarseRefineKernel
    rw [Finset.sum_eq_single j]
    · simp only [blockEmbedDist_apply_same, Channel.idChannel, Dist.pure_apply_self,
        sigmaDist_apply, mul_one]
      rw [div_self (ne_of_gt hden_pos)]
    · intro k _ hkj
      rw [blockEmbedDist_apply_ne Act (fun h : j = k => hkj h.symm) (q k) a]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · rw [coarseRevealChannel, Dist.pure_apply_ne j o hoj]
    rw [hpush]
    unfold coarseRefineKernel
    rw [Finset.sum_eq_zero]
    · simp
    · intro k _
      by_cases hkj : k = j
      · subst k
        simp [Channel.idChannel, hoj]
      · rw [blockEmbedDist_apply_ne Act (fun h : j = k => hkj h.symm) (q k) a]
        simp

/-- Positive coarse marginals expose the corresponding embedded fibre prior. -/
theorem posterior_coarseReveal_sigmaDist_of_pos
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    (k : K) (hk : p k > 0) :
    Channel.posterior (coarseRevealChannel Act) (sigmaDist p q) k =
      blockEmbedDist Act k (q k) := by
  ext ka
  rcases ka with ⟨j, a⟩
  have hmarg :
      (Channel.outcomeMarginal (coarseRevealChannel Act) (sigmaDist p q)) k = p k := by
    exact congrArg (fun m : Dist K => m k)
      (outcomeMarginal_coarseReveal_sigmaDist Act p q)
  have hmpos :
      (Channel.outcomeMarginal (coarseRevealChannel Act) (sigmaDist p q)) k > 0 := by
    rw [hmarg]
    exact hk
  unfold Channel.posterior
  rw [dif_pos hmpos]
  by_cases h : j = k
  · subst j
    rw [blockEmbedDist_apply_same]
    simp only [sigmaDist_apply, coarseRevealChannel, Dist.pure_apply_self]
    rw [hmarg]
    field_simp [ne_of_gt hk]
  · have hkj : k ≠ j := fun hkj => h hkj.symm
    rw [blockEmbedDist_apply_ne Act h (q k) a]
    simp [coarseRevealChannel, sigmaDist_apply, hkj]

/--
The posterior-law integral of the coarse reveal is the weighted sum of fibre
entropies, provided the entropy candidate is invariant under embedding a fibre
as a block-supported distribution.
-/
theorem posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    (hblock :
      ∀ k, Hfun (blockEmbedDist Act k (q k)) = Hfun (q k)) :
    posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act) Hfun =
      ∑ k, p k * Hfun (q k) := by
  unfold posteriorLawIntegral
  apply Finset.sum_congr rfl
  intro k _
  have hmarg :
      (Channel.outcomeMarginal (coarseRevealChannel Act) (sigmaDist p q)) k = p k := by
    exact congrArg (fun m : Dist K => m k)
      (outcomeMarginal_coarseReveal_sigmaDist Act p q)
  by_cases hk : p k > 0
  · rw [hmarg, posterior_coarseReveal_sigmaDist_of_pos Act p q k hk, hblock k]
  · have hk_zero : p k = 0 := by
      exact le_antisymm (le_of_not_gt hk) (p.nonneg k)
    rw [hmarg, hk_zero]
    ring

/-- Full support of `sigmaDist p q` implies full support of the coarse prior. -/
theorem sigmaDist_coarse_fullSupport
    {K : Type u} [Fintype K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    (hsigma : (sigmaDist p q).FullSupport) :
    p.FullSupport := by
  intro k
  let a : Act k := Classical.choice (inferInstance : Nonempty (Act k))
  have hsig : (sigmaDist p q) ⟨k, a⟩ > 0 := hsigma ⟨k, a⟩
  rw [sigmaDist_apply] at hsig
  by_contra hnot
  have hp_zero : p k = 0 := le_antisymm (le_of_not_gt hnot) (p.nonneg k)
  rw [hp_zero, zero_mul] at hsig
  linarith

/-- Action processing: coarse reveal weakly dominates the projected coarse identity. -/
theorem coarseReveal_rel_id_of_A5
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    F.rel
      (blockChannel (coarseRevealChannel Act) (Channel.idChannel : Channel K K))
      (inlDist (sigmaDist p q)) (inrDist p) := by
  have h :=
    hax.actionProcessing (coarseRevealChannel Act) (sigmaDist p q)
      (coarseProjectKernel Act) (Channel.idChannel : Channel K K)
      (coarseReveal_isBayesPushforwardCompletion_project Act p q)
  simpa [actionPushforward_sigmaDist_coarseProject Act p q] using h

/-- Action processing: the coarse identity weakly dominates the refined coarse-reveal channel. -/
theorem id_rel_coarseReveal_of_A5
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    F.rel
      (blockChannel (Channel.idChannel : Channel K K) (coarseRevealChannel Act))
      (inlDist p) (inrDist (sigmaDist p q)) := by
  have h :=
    hax.actionProcessing (Channel.idChannel : Channel K K) p
      (coarseRefineKernel Act q) (coarseRevealChannel Act)
      (coarseReveal_isBayesPushforwardCompletion_refine Act p q)
  simpa [actionPushforward_coarseRefine Act p q] using h

/--
For full-support sigma priors, action processing in both projection/refinement directions plus
the cross-prior value representation identify coarse reveal with full
revelation of the coarse prior.
-/
theorem coarseReveal_value_eq_Hfun_of_axioms_fullSupport
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    (hsigma : (sigmaDist p q).FullSupport) :
    normalizedValue hcross.entropy_reduction.scale_coherence
      (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p := by
  have hp : p.FullSupport := sigmaDist_coarse_fullSupport Act p q hsigma
  have hrel₁ := coarseReveal_rel_id_of_A5 F hax Act p q
  have hrel₂ := id_rel_coarseReveal_of_A5 F hax Act p q
  have hge₁ :
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) ≥
        normalizedValue hcross.entropy_reduction.scale_coherence
          p (Channel.idChannel : Channel K K) := by
    have h :=
      (hcross.cross_prior_block_rep (sigmaDist p q) p hsigma hp
        (coarseRevealChannel Act) (Channel.idChannel : Channel K K)).mp hrel₁
    simpa [normalizedValue] using h
  have hge₂ :
      normalizedValue hcross.entropy_reduction.scale_coherence
          p (Channel.idChannel : Channel K K) ≥
        normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) := by
    have h :=
      (hcross.cross_prior_block_rep p (sigmaDist p q) hp hsigma
        (Channel.idChannel : Channel K K) (coarseRevealChannel Act)).mp hrel₂
    simpa [normalizedValue] using h
  have hvalue_eq :
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        normalizedValue hcross.entropy_reduction.scale_coherence
          p (Channel.idChannel : Channel K K) :=
    le_antisymm hge₂ hge₁
  have hpost :
      posteriorLawIntegral p (Channel.idChannel : Channel K K)
          hcross.entropy_reduction.Hfun = 0 := by
    rw [posteriorLawIntegral_idChannel_eq_sum_pure]
    apply Finset.sum_eq_zero
    intro k _
    rw [hreg.H_singleton k]
    ring
  have hid :=
    hcross.entropy_reduction.value_entropy_reduction
      p hp (Channel.idChannel : Channel K K)
  rw [hpost, sub_zero] at hid
  rw [hvalue_eq]
  simpa [normalizedValue] using hid

/--
**Hfun Block-Embedding Invariance Assumption**

Paper-specific face/neutrality statement: embedding a fibre distribution as the
unique supported block of a dependent sigma action space does not change the
constructed entropy value.
-/
structure FiniteHfunBlockEmbeddingInvarianceAssumptions.{v} where
  Hfun_blockEmbed :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      {hentropy : EntropyReductionRepresentation F}
      (_hreg : EntropyRegularity F hentropy)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hentropy.Hfun (blockEmbedDist Act k qk) = hentropy.Hfun qk

/--
**Coarse-Reveal Entropy-Reduction Assumption**

Boundary-specialized entropy-reduction statement for the single coarse-reveal
experiment. The general entropy-reduction representation is currently exposed
only for full-support priors, while the Faddeev recursion quantifies over all
finite distributions.
-/
structure FiniteCoarseRevealEntropyReductionAssumptions.{v} where
  coarse_reveal_entropy_reduction :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      {hentropy : EntropyReductionRepresentation F}
      (_hreg : EntropyRegularity F hentropy)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hentropy.Hfun (sigmaDist p q) =
        normalizedValue hentropy.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hentropy.Hfun

/--
For full-support priors, support restriction preserves normalized value. The
proof uses the action-processing support comparisons in both directions and the full-support
cross-prior block representation.
-/
theorem normalizedValue_support_restrict_fullSupport_of_crossPrior
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (hq : q.FullSupport) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    normalizedValue hcross.entropy_reduction.scale_coherence q P =
      normalizedValue hcross.entropy_reduction.scale_coherence
        q.restrictToSupport (Channel.restrictToSupport P q) := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hrel₁ := rel_ambient_to_support F hax P q
  have hrel₂ := rel_support_to_ambient F hax P q
  have hge₁ :
      normalizedValue hcross.entropy_reduction.scale_coherence q P ≥
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    have h :=
      (hcross.cross_prior_block_rep q q.restrictToSupport hq
        (Dist.restrictToSupport_fullSupport q) P (Channel.restrictToSupport P q)).mp hrel₁
    simpa [normalizedValue] using h
  have hge₂ :
      normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) ≥
        normalizedValue hcross.entropy_reduction.scale_coherence q P := by
    have h :=
      (hcross.cross_prior_block_rep q.restrictToSupport q
        (Dist.restrictToSupport_fullSupport q) hq (Channel.restrictToSupport P q) P).mp hrel₂
    simpa [normalizedValue] using h
  exact le_antisymm hge₂ hge₁

/--
**Boundary Normalized-Value Support-Restriction Assumption**

The full-support case is proved above. What remains external is the cardinal
normalized-value support transport when the ambient prior itself is not full
support, because `CrossPriorBlockRepresentation.cross_prior_block_rep` is
full-support guarded.
-/
structure FiniteNormalizedValueSupportBoundaryAssumptions.{v} where
  normalizedValue_support_restrict_boundary :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hcross : CrossPriorBlockRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A),
      ¬ q.FullSupport →
      letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q)

/-- Normalized-value support restriction from the proved full-support case and
the boundary-only support-value bridge. -/
theorem normalizedValue_support_restrict_of_boundary
    (hboundary : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    normalizedValue hcross.entropy_reduction.scale_coherence q P =
      normalizedValue hcross.entropy_reduction.scale_coherence
        q.restrictToSupport (Channel.restrictToSupport P q) := by
  by_cases hq : q.FullSupport
  · exact normalizedValue_support_restrict_fullSupport_of_crossPrior F hax hcross P q hq
  · exact hboundary.normalizedValue_support_restrict_boundary F hax hcross P q hq

/--
**Hfun Support-Restriction Assumption**

This is kept separate from normalized value support restriction. For arbitrary
`EntropyReductionRepresentation`, `Hfun` is not definitionally tied to
`Hcandidate`; the full-support entropy-reduction formula only identifies it
with full revelation under full-support guards and extra regularity.
-/
structure FiniteHfunSupportRestrictionAssumptions.{v} where
  Hfun_support_restrict :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hcross : CrossPriorBlockRepresentation F)
      (_hreg : EntropyRegularity F hcross.entropy_reduction)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport

/--
**Restricted Coarse-Reveal Value Assumption**

After deleting zero-probability sigma actions, the restricted coarse-reveal
experiment has full support. What remains external here is the identification
of that restricted experiment's normalized value with the entropy of its
support-restricted coarse prior.
-/
structure FiniteRestrictedCoarseRevealValueAssumptions.{v} where
  restricted_coarse_reveal_value :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hcross : CrossPriorBlockRepresentation F)
      (_hreg : EntropyRegularity F hcross.entropy_reduction)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      ¬ (sigmaDist p q).FullSupport →
      let s : Dist ((k : K) × Act k) := sigmaDist p q
      let C : Channel ((k : K) × Act k) K := coarseRevealChannel Act
      letI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
      letI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
      normalizedValue hcross.entropy_reduction.scale_coherence
          s.restrictToSupport (Channel.restrictToSupport C s) =
        hcross.entropy_reduction.Hfun p.restrictToSupport

/--
Boundary coarse-reveal value identity from value-level support restriction and
the restricted-support coarse-reveal value identity.
-/
theorem coarseReveal_value_boundary_of_support
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    (hhfun : FiniteHfunSupportRestrictionAssumptions.{u})
    (hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    (hnot : ¬ (sigmaDist p q).FullSupport) :
    normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
        (coarseRevealChannel Act) =
      hcross.entropy_reduction.Hfun p := by
  let s : Dist ((k : K) × Act k) := sigmaDist p q
  let C : Channel ((k : K) × Act k) K := coarseRevealChannel Act
  haveI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
  haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
  have hval :
      normalizedValue hcross.entropy_reduction.scale_coherence s C =
        normalizedValue hcross.entropy_reduction.scale_coherence
          s.restrictToSupport (Channel.restrictToSupport C s) :=
    hnorm.normalizedValue_support_restrict_boundary F hax hcross C s hnot
  have hrestricted_val :
      normalizedValue hcross.entropy_reduction.scale_coherence
          s.restrictToSupport (Channel.restrictToSupport C s) =
        hcross.entropy_reduction.Hfun p.restrictToSupport :=
    hrestricted.restricted_coarse_reveal_value F hax hcross hreg Act p q hnot
  have hH :
      hcross.entropy_reduction.Hfun p =
        hcross.entropy_reduction.Hfun p.restrictToSupport :=
    hhfun.Hfun_support_restrict F hax hcross hreg p
  calc
    normalizedValue hcross.entropy_reduction.scale_coherence
        (sigmaDist p q) (coarseRevealChannel Act)
        = normalizedValue hcross.entropy_reduction.scale_coherence
            s.restrictToSupport (Channel.restrictToSupport C s) := by
          simpa [s, C] using hval
    _ = hcross.entropy_reduction.Hfun p.restrictToSupport := hrestricted_val
    _ = hcross.entropy_reduction.Hfun p := hH.symm

/--
Coarse-reveal value identity from the proved full-support case and the
support-reduced boundary extension.
-/
theorem coarseReveal_value_eq_Hfun_of_axioms
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    (hhfun : FiniteHfunSupportRestrictionAssumptions.{u})
    (hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    normalizedValue hcross.entropy_reduction.scale_coherence
      (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p := by
  by_cases hsigma : (sigmaDist p q).FullSupport
  · exact coarseReveal_value_eq_Hfun_of_axioms_fullSupport
      F hax hcross hreg Act p q hsigma
  · exact coarseReveal_value_boundary_of_support hnorm hhfun hrestricted
      F hax hcross hreg Act p q hsigma

/-- Assemble the Faddeev recursion from the sharpened coarse-reveal pieces. -/
theorem satisfiesFaddeevRecursion_of_coarseReveal_parts
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    (hhfun : FiniteHfunSupportRestrictionAssumptions.{u})
    (hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction) :
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  intro K _ _ _ Act _ _ _ _ p q
  have hER :=
    hred.coarse_reveal_entropy_reduction F hax hreg Act p q
  have hV :=
    coarseReveal_value_eq_Hfun_of_axioms hnorm hhfun hrestricted F hax hcross hreg Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) := by
    exact posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k => hblock.Hfun_blockEmbed F hax hreg Act k (q k))
  change hcross.entropy_reduction.Hfun (sigmaDist p q) =
    hcross.entropy_reduction.Hfun p +
      ∑ k, p k * hcross.entropy_reduction.Hfun (q k)
  rw [hER, hV, hInt]

/-- Build `FaddeevRecursionForm` from the sharpened recursion components. -/
theorem faddeevRecursionForm_of_coarseReveal_parts
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    (hhfun : FiniteHfunSupportRestrictionAssumptions.{u})
    (hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction) :
    FaddeevRecursionForm F hcross.entropy_reduction where
  regularity := hreg
  grouping_recursion :=
    satisfiesFaddeevRecursion_of_coarseReveal_parts
      hblock hred hnorm hhfun hrestricted F hax hcross hreg

/--
**Classical Faddeev Theorem Audit Schema**

Preference-free statement of the exact theorem consumed by the downstream
proof: an abstract finite entropy functional satisfying the standard Faddeev
hypotheses is a nonnegative multiple of Shannon entropy. The schema has a
closed inhabitant in `TraceableAgency.PureTrace.Support.GenericFaddeev`.

This bridge intentionally returns only `0 ≤ alpha`; strict positivity is split
out because the paper obtains it from pure-trace nontriviality.
-/
structure ClassicalFaddeevTheoremAssumptions.{v} where
  of_standard_hypotheses :
    ∀ (Hfun :
        ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
          Dist A → ℝ),
      FiniteFaddeevStandardHypotheses Hfun →
      ∃ alpha : ℝ, 0 ≤ alpha ∧
        ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
          (q : Dist A),
          Hfun q = alpha * H(q)

/--
**Distribution Relabeling**

Push a finite distribution forward through a bijection of labels.
-/
noncomputable def relabelDist
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) : Dist B where
  prob := fun b => q (e.symm b)
  nonneg := fun b => q.nonneg (e.symm b)
  sum_eq_one := by
    rw [Equiv.sum_comp e.symm (fun a : A => q a)]
    exact q.sum_eq_one

@[simp]
theorem relabelDist_apply
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) (b : B) :
    relabelDist e q b = q (e.symm b) := rfl

@[simp]
theorem relabelDist_refl
    {A : Type u} [Fintype A] (q : Dist A) :
    relabelDist (Equiv.refl A) q = q := by
  ext a
  rfl

/--
**Channel Relabeling**

Transport both action and outcome labels through bijections.
-/
noncomputable def relabelChannel
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) : Channel B Y :=
  fun b => relabelDist eO (P (eA.symm b))

@[simp]
theorem relabelChannel_apply
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) (b : B) (y : Y) :
    relabelChannel eA eO P b y = P (eA.symm b) (eO.symm y) := rfl

@[simp]
theorem relabelChannel_refl_refl
    {A O : Type u} [Fintype A] [Fintype O]
    (P : Channel A O) :
    relabelChannel (Equiv.refl A) (Equiv.refl O) P = P := by
  ext a o
  rfl

@[simp]
theorem relabelDist_symm
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) :
    relabelDist e.symm (relabelDist e q) = q := by
  ext a
  simp [relabelDist]

@[simp]
theorem relabelChannel_symm
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) :
    relabelChannel eA.symm eO.symm (relabelChannel eA eO P) = P := by
  ext a o
  simp [relabelChannel]

@[simp]
theorem relabelChannel_action_then_outcome
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) :
    relabelChannel (Equiv.refl B) eO
        (relabelChannel eA (Equiv.refl O) P) =
      relabelChannel eA eO P := by
  ext b y
  rfl

/-!
## Deterministic kernels for relabeling
-/

/-- Deterministic outcome relabeling kernel induced by an equivalence. -/
noncomputable def outcomeEquivKernel
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) : Channel O Y :=
  fun o => Dist.pure (e o)

/-- Deterministic action relabeling kernel induced by an equivalence. -/
noncomputable def actionEquivKernel
    {A B : Type u} [Fintype B] [DecidableEq B]
    (e : A ≃ B) : Channel.ActionKernel A B :=
  fun a => Dist.pure (e a)

@[simp]
theorem outcomeEquivKernel_apply
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (o : O) (y : Y) :
    outcomeEquivKernel e o y = if y = e o then 1 else 0 := rfl

@[simp]
theorem actionEquivKernel_apply
    {A B : Type u} [Fintype B] [DecidableEq B]
    (e : A ≃ B) (a : A) (b : B) :
    actionEquivKernel e a b = if b = e a then 1 else 0 := rfl

/-- Postprocessing by a deterministic outcome equivalence is outcome relabeling. -/
theorem postprocess_outcomeEquiv_eq_relabel
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (P : Channel A O) :
    Channel.postprocess P (outcomeEquivKernel eO) =
      relabelChannel (Equiv.refl A) eO P := by
  ext a y
  change (∑ o : O, P a o * Dist.pure (eO o) y) = P a (eO.symm y)
  rw [Fintype.sum_eq_single (eO.symm y)]
  · simp
  · intro o hone
    have hne : y ≠ eO o := by
      intro hy
      apply hone
      exact eO.injective (by simpa using hy.symm)
    simp [Dist.pure_apply_ne _ _ hne]

/-- Reversing a deterministic outcome relabeling recovers the original channel. -/
theorem postprocess_outcomeEquiv_symm_eq_original
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (P : Channel A O) :
    Channel.postprocess (relabelChannel (Equiv.refl A) eO P)
        (outcomeEquivKernel eO.symm) =
      P := by
  rw [postprocess_outcomeEquiv_eq_relabel]
  ext a o
  simp [relabelChannel]

/-- Pushing a prior through a deterministic action equivalence is distribution relabeling. -/
theorem actionPushforward_equiv
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (eA : A ≃ B) (q : Dist A) :
    Channel.actionPushforward q (actionEquivKernel eA) =
      relabelDist eA q := by
  ext b
  change (∑ a : A, q a * Dist.pure (eA a) b) = q (eA.symm b)
  rw [Fintype.sum_eq_single (eA.symm b)]
  · simp
  · intro a hane
    have hne : b ≠ eA a := by
      intro hb
      apply hane
      exact eA.injective (by simpa using hb.symm)
    simp [Dist.pure_apply_ne _ _ hne]

/-- A relabeled channel is the Bayesian pushforward completion under an action equivalence. -/
theorem relabelChannel_isBayesPushforwardCompletion
    {A B O : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (P : Channel A O) (q : Dist A) :
    Channel.IsBayesPushforwardCompletion
      P q (actionEquivKernel eA)
      (relabelChannel eA (Equiv.refl O) P) := by
  intro b hb o
  have hpush := congrArg (fun d : Dist B => d b) (actionPushforward_equiv eA q)
  have hbq : q (eA.symm b) > 0 := by
    simpa [relabelDist] using (by simpa [hpush] using hb)
  have hnum :
      (∑ a : A, q a * Dist.pure (eA a) b * P a o) =
        q (eA.symm b) * P (eA.symm b) o := by
    rw [Fintype.sum_eq_single (eA.symm b)]
    · simp
    · intro a hane
      have hne : b ≠ eA a := by
        intro hb'
        apply hane
        exact eA.injective (by simpa using hb'.symm)
      simp [Dist.pure_apply_ne _ _ hne]
  change P (eA.symm b) o =
    (∑ a : A, q a * Dist.pure (eA a) b * P a o) /
      (Channel.actionPushforward q (actionEquivKernel eA)) b
  rw [hnum, hpush]
  simp [relabelDist, hbq.ne']

/-- Reversing an action relabeling is also a valid Bayesian pushforward completion. -/
theorem relabelChannel_symm_isBayesPushforwardCompletion
    {A B O : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (P : Channel A O) (q : Dist A) :
    Channel.IsBayesPushforwardCompletion
      (relabelChannel eA (Equiv.refl O) P)
      (relabelDist eA q)
      (actionEquivKernel eA.symm)
      P := by
  have h :=
    (relabelChannel_isBayesPushforwardCompletion
      (eA := eA.symm)
      (P := relabelChannel eA (Equiv.refl O) P)
      (q := relabelDist eA q))
  convert h using 1
  ext b o
  simp [relabelChannel]

/-!
## Common-block assembly for equivalent environments
-/

/-- Four labels for replacing an environment by an equivalent relabeled copy. -/
inductive RelabelReplacementBlock : Type u
  | oldLeft
  | newLeft
  | oldRight
  | newRight
  deriving DecidableEq, Fintype

open RelabelReplacementBlock

/-- Action alphabets for the common four-block relabeling-replacement environment. -/
def relabelReplacementAct
    (A B : Type u) : RelabelReplacementBlock → Type u
  | oldLeft => A
  | newLeft => B
  | oldRight => A
  | newRight => B

noncomputable instance relabelReplacementActFintype
    {A B : Type u} [Fintype A] [Fintype B] :
    ∀ k : RelabelReplacementBlock, Fintype (relabelReplacementAct A B k)
  | oldLeft => show Fintype A from inferInstance
  | newLeft => show Fintype B from inferInstance
  | oldRight => show Fintype A from inferInstance
  | newRight => show Fintype B from inferInstance

instance relabelReplacementActDecidableEq
    {A B : Type u} [DecidableEq A] [DecidableEq B] :
    ∀ k : RelabelReplacementBlock, DecidableEq (relabelReplacementAct A B k)
  | oldLeft => show DecidableEq A from inferInstance
  | newLeft => show DecidableEq B from inferInstance
  | oldRight => show DecidableEq A from inferInstance
  | newRight => show DecidableEq B from inferInstance

/-- Outcome alphabets for the common four-block relabeling-replacement environment. -/
def relabelReplacementOut
    (O Y : Type u) : RelabelReplacementBlock → Type u
  | oldLeft => O
  | newLeft => Y
  | oldRight => O
  | newRight => Y

noncomputable instance relabelReplacementOutFintype
    {O Y : Type u} [Fintype O] [Fintype Y] :
    ∀ k : RelabelReplacementBlock, Fintype (relabelReplacementOut O Y k)
  | oldLeft => show Fintype O from inferInstance
  | newLeft => show Fintype Y from inferInstance
  | oldRight => show Fintype O from inferInstance
  | newRight => show Fintype Y from inferInstance

instance relabelReplacementOutDecidableEq
    {O Y : Type u} [DecidableEq O] [DecidableEq Y] :
    ∀ k : RelabelReplacementBlock, DecidableEq (relabelReplacementOut O Y k)
  | oldLeft => show DecidableEq O from inferInstance
  | newLeft => show DecidableEq Y from inferInstance
  | oldRight => show DecidableEq O from inferInstance
  | newRight => show DecidableEq Y from inferInstance

/-- Channels for the common four-block relabeling-replacement environment. -/
noncomputable def relabelReplacementChannel
    {A B O Y : Type u} [Fintype O] [Fintype Y]
    (P : Channel A O) (P' : Channel B Y) :
    ∀ k : RelabelReplacementBlock,
      Channel (relabelReplacementAct A B k) (relabelReplacementOut O Y k)
  | oldLeft => show Channel A O from P
  | newLeft => show Channel B Y from P'
  | oldRight => show Channel A O from P
  | newRight => show Channel B Y from P'

/--
Common-block assembly: if each of two lotteries is weakly equivalent between an
environment and a replacement environment, then every pairwise comparison is
preserved by replacement.
-/
theorem pairwise_relabel_replacement_from_weak_equiv
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (P' : Channel B Y)
    (q r : Dist A) (q' r' : Dist B)
    (hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q'))
    (hq_to_old :
      F.rel (blockChannel P' P) (inlDist q') (inrDist q))
    (hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r'))
    (hr_to_old :
      F.rel (blockChannel P' P) (inlDist r') (inrDist r)) :
    F.rel P q r ↔ F.rel P' q' r' := by
  classical
  let k0 : RelabelReplacementBlock.{u} := oldLeft
  let k1 : RelabelReplacementBlock.{u} := newLeft
  let k2 : RelabelReplacementBlock.{u} := oldRight
  let k3 : RelabelReplacementBlock.{u} := newRight
  let Act := relabelReplacementAct A B
  let Out := relabelReplacementOut O Y
  let C := relabelReplacementChannel P P'
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act k0 q
  let x' := blockEmbedDist Act k1 q'
  let y := blockEmbedDist Act k2 r
  let y' := blockEmbedDist Act k3 r'
  have htrans :
      ∀ a b c : Dist ((k : RelabelReplacementBlock) × Act k),
        F.rel commonP a b → F.rel commonP b c → F.rel commonP a c :=
    (hax.weakOrder.1 commonP).2
  have h02_ne : k0 ≠ k2 := by decide
  have h01_ne : k0 ≠ k1 := by decide
  have h10_ne : k1 ≠ k0 := by decide
  have h23_ne : k2 ≠ k3 := by decide
  have h32_ne : k3 ≠ k2 := by decide
  have h13_ne : k1 ≠ k3 := by decide
  have hleft_dup :
      F.rel P q r ↔
        F.rel (blockChannel P P) (inlDist q) (inrDist r) :=
    hax.blockCoherence.duplication P q r
  have hright_dup :
      F.rel P' q' r' ↔
        F.rel (blockChannel P' P') (inlDist q') (inrDist r') :=
    hax.blockCoherence.duplication P' q' r'
  have hcommon_02 :
      F.rel commonP x y ↔
        F.rel (blockChannel P P) (inlDist q) (inrDist r) := by
    simpa [commonP, x, y, k0, k2, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using
      (hax.blockCoherence.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k2) h02_ne
        (qᵢ := q) (qⱼ := r))
  have hcommon_01 : F.rel commonP x x' := by
    have h :=
      (hax.blockCoherence.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k1) h01_ne
        (qᵢ := q) (qⱼ := q')).mpr hq_to_new
    simpa [commonP, x, x', k0, k1, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hcommon_10 : F.rel commonP x' x := by
    have h :=
      (hax.blockCoherence.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k0) h10_ne
        (qᵢ := q') (qⱼ := q)).mpr hq_to_old
    simpa [commonP, x, x', k0, k1, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hcommon_23 : F.rel commonP y y' := by
    have h :=
      (hax.blockCoherence.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k2) (j := k3) h23_ne
        (qᵢ := r) (qⱼ := r')).mpr hr_to_new
    simpa [commonP, y, y', k2, k3, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hcommon_32 : F.rel commonP y' y := by
    have h :=
      (hax.blockCoherence.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k3) (j := k2) h32_ne
        (qᵢ := r') (qⱼ := r)).mpr hr_to_old
    simpa [commonP, y, y', k2, k3, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hreplace : F.rel commonP x y ↔ F.rel commonP x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonP a b) htrans
      hcommon_01 hcommon_10 hcommon_23 hcommon_32
  have hcommon_13 :
      F.rel commonP x' y' ↔
        F.rel (blockChannel P' P') (inlDist q') (inrDist r') := by
    simpa [commonP, x', y', k1, k3, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using
      (hax.blockCoherence.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k3) h13_ne
        (qᵢ := q') (qⱼ := r'))
  exact hleft_dup.trans
    (hcommon_02.symm.trans (hreplace.trans (hcommon_13.trans hright_dup.symm)))

/-- A finite probability distribution can exist only on a nonempty finite type. -/
theorem nonempty_of_dist {A : Type u} [Fintype A] (q : Dist A) : Nonempty A := by
  by_contra h
  have hzero : (∑ a : A, q a) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact False.elim (h ⟨a⟩)
  linarith [q.sum_eq_one]

/-- Outcome relabeling invariance follows from reversible record postprocessing (main-text A6). -/
theorem relabel_rel_outcome_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (P : Channel A O) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (relabelChannel (Equiv.refl A) eO P) q r := by
  let P' := relabelChannel (Equiv.refl A) eO P
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q) := by
    have h := hax.recordProcessing P (outcomeEquivKernel eO) q
    simpa [P', postprocess_outcomeEquiv_eq_relabel] using h
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist q) (inrDist q) := by
    have h := hax.recordProcessing P' (outcomeEquivKernel eO.symm) q
    simpa [P', postprocess_outcomeEquiv_symm_eq_original] using h
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r) := by
    have h := hax.recordProcessing P (outcomeEquivKernel eO) r
    simpa [P', postprocess_outcomeEquiv_eq_relabel] using h
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist r) (inrDist r) := by
    have h := hax.recordProcessing P' (outcomeEquivKernel eO.symm) r
    simpa [P', postprocess_outcomeEquiv_symm_eq_original] using h
  exact
    pairwise_relabel_replacement_from_weak_equiv F hax P P' q r q r
      hq_to_new hq_to_old hr_to_new hr_to_old

/-- Action relabeling invariance follows from reversible deterministic action kernels (main-text A7). -/
theorem relabel_rel_action_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (P : Channel A O) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (relabelChannel eA (Equiv.refl O) P)
        (relabelDist eA q) (relabelDist eA r) := by
  have hA : Nonempty A := nonempty_of_dist q
  haveI : Nonempty A := hA
  haveI : Nonempty B := ⟨eA (Classical.choice hA)⟩
  let P' := relabelChannel eA (Equiv.refl O) P
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist (relabelDist eA q)) := by
    have h :=
      hax.actionProcessing P q (actionEquivKernel eA) P'
        (relabelChannel_isBayesPushforwardCompletion eA P q)
    simpa [P', actionPushforward_equiv] using h
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist (relabelDist eA q)) (inrDist q) := by
    have h :=
      hax.actionProcessing P' (relabelDist eA q) (actionEquivKernel eA.symm) P
        (relabelChannel_symm_isBayesPushforwardCompletion eA P q)
    simpa [P', actionPushforward_equiv, relabelDist_symm] using h
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist (relabelDist eA r)) := by
    have h :=
      hax.actionProcessing P r (actionEquivKernel eA) P'
        (relabelChannel_isBayesPushforwardCompletion eA P r)
    simpa [P', actionPushforward_equiv] using h
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist (relabelDist eA r)) (inrDist r) := by
    have h :=
      hax.actionProcessing P' (relabelDist eA r) (actionEquivKernel eA.symm) P
        (relabelChannel_symm_isBayesPushforwardCompletion eA P r)
    simpa [P', actionPushforward_equiv, relabelDist_symm] using h
  exact
    pairwise_relabel_replacement_from_weak_equiv F hax P P'
      q r (relabelDist eA q) (relabelDist eA r)
      hq_to_new hq_to_old hr_to_new hr_to_old

/-- Full finite action/outcome relabeling invariance from main-text A6, A7, A5, and A1 transitivity. -/
theorem relabel_rel_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (P : Channel A O) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (relabelChannel eA eO P) (relabelDist eA q) (relabelDist eA r) := by
  let P₁ := relabelChannel eA (Equiv.refl O) P
  have hact := relabel_rel_action_of_axioms F hax eA P q r
  have hout :=
    relabel_rel_outcome_of_axioms F hax eO P₁
      (relabelDist eA q) (relabelDist eA r)
  exact hact.trans (by simpa [P₁, relabelChannel_action_then_outcome] using hout)

/--
**Finite Relabeling Invariance Assumption**

The remaining label-invariance bridge: finite bijective relabelings of actions
and outcomes preserve preference comparisons after pushing the two lotteries and
the channel through the same relabeling.
-/
structure FiniteRelabelingInvarianceAssumptions.{v} where
  relabel_rel :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A]
      [Fintype B] [DecidableEq B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (eA : A ≃ B) (eO : O ≃ Y)
      (P : Channel A O) (q r : Dist A),
      F.rel P q r ↔
        F.rel (relabelChannel eA eO P) (relabelDist eA q) (relabelDist eA r)

/-- Package the internally proved relabeling theorem in the former assumption structure. -/
theorem finiteRelabelingInvariance_of_axioms :
    FiniteRelabelingInvarianceAssumptions.{u} :=
  { relabel_rel := relabel_rel_of_axioms }

/-- Pure relational strict replacement on the right by a two-sided weak equivalence. -/
theorem strict_replace_right_by_equiv
    {α : Type*} (R : α → α → Prop)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    {x y z : α}
    (hxy_strict : R x y ∧ ¬ R y x)
    (hyz : R y z) (_hzy : R z y) :
    R x z ∧ ¬ R z x := by
  constructor
  · exact htrans x y z hxy_strict.1 hyz
  · intro hzx
    exact hxy_strict.2 (htrans y z x hyz hzx)

/-- The unique channel from `Unit` to the universe-lifted one-point type. -/
def unitToPUnitChannel : Channel Unit PUnit.{u + 1} :=
  fun _ =>
    { prob := fun _ => 1
      nonneg := fun _ => by norm_num
      sum_eq_one := by simp }

/-- The unique channel from the universe-lifted one-point type to `Unit`. -/
def punitToUnitChannel : Channel PUnit.{u + 1} Unit :=
  fun _ =>
    { prob := fun _ => 1
      nonneg := fun _ => by norm_num
      sum_eq_one := by simp }

@[simp]
theorem postprocess_uninformativeChannel_unitToPUnit
    {A : Type u} [Fintype A] :
    Channel.postprocess (Channel.uninformativeChannel A) unitToPUnitChannel =
      Channel.uninformativeChannelU A := by
  ext a p
  simp [Channel.postprocess, Channel.uninformativeChannel,
    Channel.uninformativeChannelU, unitToPUnitChannel]

@[simp]
theorem postprocess_uninformativeChannelU_punitToUnit
    {A : Type u} [Fintype A] :
    Channel.postprocess (Channel.uninformativeChannelU A) punitToUnitChannel =
      Channel.uninformativeChannel A := by
  ext a p
  simp [Channel.postprocess, Channel.uninformativeChannel,
    Channel.uninformativeChannelU, punitToUnitChannel]

/-- Relabel the right one-point outcome in `A ⊕ Unit` to `A ⊕ PUnit.{u+1}`. -/
def blockUnitPUnitOutcomeEquiv (A : Type u) : (A ⊕ Unit) ≃ (A ⊕ PUnit.{u + 1}) where
  toFun
    | Sum.inl a => Sum.inl a
    | Sum.inr _ => Sum.inr PUnit.unit
  invFun
    | Sum.inl a => Sum.inl a
    | Sum.inr _ => Sum.inr ()
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

@[simp]
theorem relabel_block_id_uninformativeChannel_eq
    {A : Type u} [Fintype A] [DecidableEq A] :
    relabelChannel (Equiv.refl (A ⊕ A)) (blockUnitPUnitOutcomeEquiv A)
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A)) =
        blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A) := by
  ext x y
  cases x <;> cases y <;> simp [relabelChannel, blockUnitPUnitOutcomeEquiv,
    Channel.idChannel, Channel.uninformativeChannel, Channel.uninformativeChannelU]

@[simp]
theorem relabelDist_sumComm_inr
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : Dist B) :
    relabelDist (Equiv.sumComm A B) (inrDist r : Dist (A ⊕ B)) =
      (inlDist r : Dist (B ⊕ A)) := by
  ext x
  cases x <;> rfl

@[simp]
theorem relabelDist_sumComm_inl
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (q : Dist A) :
    relabelDist (Equiv.sumComm A B) (inlDist q : Dist (A ⊕ B)) =
      (inrDist q : Dist (B ⊕ A)) := by
  ext x
  cases x <;> rfl

@[simp]
theorem relabel_blockChannel_sumComm_eq
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (Q : Channel B Y) :
    relabelChannel (Equiv.sumComm A B) (Equiv.sumComm O Y) (blockChannel P Q) =
      blockChannel Q P := by
  ext x y
  cases x <;> cases y <;> rfl

/-- Lift pure-trace nontriviality to the value-facing one-point outcome. -/
theorem lifted_uninformative_strict_of_relabeling
    (hrelabel : FiniteRelabelingInvarianceAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    (q : Dist A) (hq : q.FullSupport) :
    F.strictRel
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A))
      (inlDist q) (inrDist q) := by
  have hstrict :
      F.strictRel
        (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A))
        (inlDist q) (inrDist q) :=
    hax.weakOrder.2 q hq
  have hiff :=
    hrelabel.relabel_rel F hax (Equiv.refl (A ⊕ A)) (blockUnitPUnitOutcomeEquiv A)
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A))
      (inlDist q) (inrDist q)
  have hiff_rev :=
    hrelabel.relabel_rel F hax (Equiv.refl (A ⊕ A)) (blockUnitPUnitOutcomeEquiv A)
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A))
      (inrDist q) (inlDist q)
  constructor
  · simpa using hiff.mp hstrict.1
  · intro hrev
    exact hstrict.2 (hiff_rev.mpr (by simpa using hrev))

/-- Lifted no-information strictness, now derived directly from the axioms. -/
theorem lifted_uninformative_strict_of_A1
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    (q : Dist A) (hq : q.FullSupport) :
    F.strictRel
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A))
      (inlDist q) (inrDist q) :=
  lifted_uninformative_strict_of_relabeling
    finiteRelabelingInvariance_of_axioms F hax q hq

/-- Reverse orientation for two-block comparisons follows from finite relabeling invariance. -/
theorem block_swap_rel_of_relabeling
    (hrelabel : FiniteRelabelingInvarianceAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (Q : Channel B Y)
    (q : Dist A) (r : Dist B) :
    F.rel (blockChannel P Q) (inrDist r) (inlDist q) ↔
      F.rel (blockChannel Q P) (inlDist r) (inrDist q) := by
  have hiff :=
    hrelabel.relabel_rel F hax (Equiv.sumComm A B) (Equiv.sumComm O Y)
      (blockChannel P Q) (inrDist r) (inlDist q)
  simpa using hiff

/-- Reverse orientation for two-block comparisons, now derived directly from the axioms. -/
theorem block_swap_rel_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (Q : Channel B Y)
    (q : Dist A) (r : Dist B) :
    F.rel (blockChannel P Q) (inrDist r) (inlDist q) ↔
      F.rel (blockChannel Q P) (inlDist r) (inrDist q) :=
  block_swap_rel_of_relabeling finiteRelabelingInvariance_of_axioms F hax P Q q r

/-- Reverse-orientation cross-prior representation inside the same block. -/
theorem cross_prior_reverse_in_same_block
    (hrelabel : FiniteRelabelingInvarianceAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inrDist r) (inlDist q) ↔
      normalizedValue hcross.entropy_reduction.scale_coherence r Q ≥
        normalizedValue hcross.entropy_reduction.scale_coherence q P := by
  rw [block_swap_rel_of_relabeling hrelabel F hax P Q q r]
  simpa [normalizedValue] using
    (hcross.cross_prior_block_rep r q hr hq Q P)

/-- Strict block preference implies strict normalized-value inequality. -/
theorem strict_block_value_gt
    (hrelabel : FiniteRelabelingInvarianceAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y)
    (hstrict : F.strictRel (blockChannel P Q) (inlDist q) (inrDist r)) :
    normalizedValue hcross.entropy_reduction.scale_coherence q P >
      normalizedValue hcross.entropy_reduction.scale_coherence r Q := by
  have hnotge :
      ¬ normalizedValue hcross.entropy_reduction.scale_coherence r Q ≥
        normalizedValue hcross.entropy_reduction.scale_coherence q P := by
    intro hge
    have hrev :
        F.rel (blockChannel P Q) (inrDist r) (inlDist q) :=
      (cross_prior_reverse_in_same_block hrelabel F hax hcross q r hq hr P Q).mpr hge
    exact hstrict.2 hrev
  exact lt_of_not_ge hnotge

/-- The posterior of the universe-lifted no-information channel is the prior. -/
theorem posterior_uninformativeChannelU_eq_prior
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (star : PUnit.{u + 1}) :
    Channel.posterior (Channel.uninformativeChannelU A) q star = q := by
  ext a
  unfold Channel.posterior
  have hm :
      (Channel.outcomeMarginal (Channel.uninformativeChannelU A) q) star = 1 := by
    simp [Channel.outcomeMarginal_apply, Channel.uninformativeChannelU, q.sum_eq_one]
  rw [dif_pos (by rw [hm]; norm_num)]
  change q a * (Channel.uninformativeChannelU A a) star /
      (Channel.outcomeMarginal (Channel.uninformativeChannelU A) q) star = q a
  rw [hm]
  simp [Channel.uninformativeChannelU]

/-- The posterior-law integral of the lifted no-information channel evaluates at the prior. -/
theorem posteriorLawIntegral_uninformativeChannelU_eq
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (Channel.uninformativeChannelU A) φ = φ q := by
  simp [posteriorLawIntegral, posterior_uninformativeChannelU_eq_prior,
    Channel.outcomeMarginal_apply, Channel.uninformativeChannelU, q.sum_eq_one]

/-- The full-revelation posterior integral of a regular entropy candidate is zero. -/
theorem posteriorLawIntegral_idChannel_Hfun_eq_zero
    {F : PrefFamily.{u}} {hentropy : EntropyReductionRepresentation F}
    (hreg : EntropyRegularity F hentropy)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    posteriorLawIntegral q Channel.idChannel hentropy.Hfun = 0 := by
  rw [posteriorLawIntegral_idChannel_eq_sum_pure]
  apply Finset.sum_eq_zero
  intro a _
  rw [hreg.H_singleton a, mul_zero]

/-- The lifted no-information posterior integral of an entropy candidate is the prior value. -/
theorem posteriorLawIntegral_uninformativeChannelU_Hfun_eq_self
    {F : PrefFamily.{u}} {hentropy : EntropyReductionRepresentation F}
    (_hreg : EntropyRegularity F hentropy)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    posteriorLawIntegral q (Channel.uninformativeChannelU A) hentropy.Hfun =
      hentropy.Hfun q := by
  rw [posteriorLawIntegral_uninformativeChannelU_eq]

/-- Full revelation has normalized value equal to the entropy candidate. -/
theorem normalizedValue_idChannel_eq_Hfun
    {F : PrefFamily.{u}} (hentropy : EntropyReductionRepresentation F)
    (hreg : EntropyRegularity F hentropy)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    normalizedValue hentropy.scale_coherence q Channel.idChannel =
      hentropy.Hfun q := by
  have h := hentropy.value_entropy_reduction q hq Channel.idChannel
  rw [posteriorLawIntegral_idChannel_Hfun_eq_zero hreg q] at h
  simpa [normalizedValue] using h

/-- No information has normalized value zero. -/
theorem normalizedValue_uninformativeChannel_eq_zero
    {F : PrefFamily.{u}} (hentropy : EntropyReductionRepresentation F)
    (hreg : EntropyRegularity F hentropy)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    normalizedValue hentropy.scale_coherence q (Channel.uninformativeChannelU A) = 0 := by
  have h := hentropy.value_entropy_reduction q hq (Channel.uninformativeChannelU A)
  rw [posteriorLawIntegral_uninformativeChannelU_Hfun_eq_self hreg q] at h
  simpa [normalizedValue] using h

/-- Identity-channel value formula, in the orientation used by support transport. -/
theorem Hfun_eq_normalizedValue_id_fullSupport
    {F : PrefFamily.{u}} (hentropy : EntropyReductionRepresentation F)
    (hreg : EntropyRegularity F hentropy)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    hentropy.Hfun q =
      normalizedValue hentropy.scale_coherence q Channel.idChannel :=
  (normalizedValue_idChannel_eq_Hfun hentropy hreg q hq).symm

/-- For the support-restricted identity channel, a positive ambient label gives
the corresponding point mass on the support subtype. -/
theorem posterior_restrict_idChannel_eq_pure_of_pos
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) {a : A} (ha : q a > 0) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    Channel.posterior
      (Channel.restrictToSupport (Channel.idChannel : Channel A A) q)
      q.restrictToSupport a =
        Dist.pure (⟨a, ha⟩ : supportSubtype q) := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  ext b
  have hmarg :
      Channel.outcomeMarginal
          (Channel.restrictToSupport (Channel.idChannel : Channel A A) q)
          q.restrictToSupport a = q a := by
    rw [Channel.outcomeMarginal_restrictToSupport, outcomeMarginal_idChannel']
  unfold Channel.posterior
  rw [dif_pos (by rw [hmarg]; exact ha)]
  change q.restrictToSupport b *
      (Channel.restrictToSupport (Channel.idChannel : Channel A A) q b) a /
        Channel.outcomeMarginal
          (Channel.restrictToSupport (Channel.idChannel : Channel A A) q)
          q.restrictToSupport a =
    (Dist.pure (⟨a, ha⟩ : supportSubtype q)) b
  rw [hmarg]
  by_cases hba : b.1 = a
  · have hb : b = (⟨a, ha⟩ : supportSubtype q) := Subtype.ext hba
    subst b
    simp [Channel.restrictToSupport, Channel.idChannel, Dist.restrictToSupport_apply,
      div_self (ne_of_gt ha)]
  · have hb : b ≠ (⟨a, ha⟩ : supportSubtype q) := by
      intro h
      exact hba (congrArg Subtype.val h)
    have hleft_ne : a ≠ b.1 := by
      intro h
      exact hba h.symm
    have hleft0 : (Dist.pure b.1) a = 0 := Dist.pure_apply_ne b.1 a hleft_ne
    have hright0 :
        (Dist.pure (⟨a, ha⟩ : supportSubtype q)) b = 0 :=
      Dist.pure_apply_ne (⟨a, ha⟩ : supportSubtype q) b hb
    simp [Channel.restrictToSupport, Channel.idChannel, Dist.restrictToSupport_apply,
      hleft0, hright0]

/--
On the positive support, the ambient-label identity channel and the true
identity channel have the same posterior law.
-/
theorem posteriorLawIntegral_restrict_idChannel_eq_idSupport
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (φ : Dist (supportSubtype q) → ℝ) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    posteriorLawIntegral q.restrictToSupport
        (Channel.restrictToSupport (Channel.idChannel : Channel A A) q) φ =
      posteriorLawIntegral q.restrictToSupport
        (Channel.idChannel : Channel (supportSubtype q) (supportSubtype q)) φ := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  rw [posteriorLawIntegral_idChannel_eq_sum_pure]
  unfold posteriorLawIntegral
  rw [Channel.outcomeMarginal_restrictToSupport, outcomeMarginal_idChannel']
  let f : A → ℝ := fun a =>
    if ha : q a > 0 then
      q a * φ (Dist.pure (⟨a, ha⟩ : supportSubtype q))
    else
      0
  have hleft :
      (∑ a : A,
          q a *
            φ (Channel.posterior
              (Channel.restrictToSupport (Channel.idChannel : Channel A A) q)
              q.restrictToSupport a)) =
        ∑ a : A, f a := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : q a > 0
    · rw [posterior_restrict_idChannel_eq_pure_of_pos q ha]
      unfold f
      rw [dif_pos ha]
      congr 2
    · have hzero : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
      simp [f, hzero]
  rw [hleft]
  rw [← sum_supportSubtype_eq_sum_of_zero q f]
  · apply Finset.sum_congr rfl
    intro b _
    simp [f, Dist.restrictToSupport_apply, b.2]
  · intro a hzero
    simp [f, hzero]

/-- The two support identity presentations induce the same posterior law. -/
theorem samePosteriorLaw_restrict_idChannel_idSupport
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    SamePosteriorLawExp q.restrictToSupport
      (experimentOfChannel
        (Channel.restrictToSupport (Channel.idChannel : Channel A A) q))
      (experimentOfChannel
        (Channel.idChannel : Channel (supportSubtype q) (supportSubtype q))) := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  intro φ _hφ
  unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
  exact posteriorLawIntegral_restrict_idChannel_eq_idSupport q φ

/-- The ambient-label identity restricted to support has the same normalized value
as the true identity channel on the support subtype. -/
theorem normalizedValue_restrict_idChannel_eq_idSupport
    {F : PrefFamily.{u}} (hentropy : EntropyReductionRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    normalizedValue hentropy.scale_coherence q.restrictToSupport
        (Channel.restrictToSupport (Channel.idChannel : Channel A A) q) =
      normalizedValue hentropy.scale_coherence q.restrictToSupport
        (Channel.idChannel : Channel (supportSubtype q) (supportSubtype q)) := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hV :=
    hentropy.scale_coherence.branch_agg.value_rep.respects_same_posterior_law
      q.restrictToSupport
      (experimentOfChannel
        (Channel.restrictToSupport (Channel.idChannel : Channel A A) q))
      (experimentOfChannel
        (Channel.idChannel : Channel (supportSubtype q) (supportSubtype q)))
      (samePosteriorLaw_restrict_idChannel_idSupport q)
  simpa [normalizedValue] using congrArg
    (fun x => x / hentropy.scale_coherence.scale q.restrictToSupport) hV

/-- Full-support `Hfun` support restriction follows from identity-channel value
and the full-support normalized-value support theorem. -/
theorem Hfun_support_restrict_fullSupport_of_identity
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    hcross.entropy_reduction.Hfun q =
      hcross.entropy_reduction.Hfun q.restrictToSupport := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  calc
    hcross.entropy_reduction.Hfun q =
        normalizedValue hcross.entropy_reduction.scale_coherence q
          (Channel.idChannel : Channel A A) := by
          exact Hfun_eq_normalizedValue_id_fullSupport
            hcross.entropy_reduction hreg q hq
    _ = normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport
          (Channel.restrictToSupport (Channel.idChannel : Channel A A) q) := by
          exact normalizedValue_support_restrict_fullSupport_of_crossPrior
            F hax hcross (Channel.idChannel : Channel A A) q hq
    _ = normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport
          (Channel.idChannel : Channel (supportSubtype q) (supportSubtype q)) := by
          exact normalizedValue_restrict_idChannel_eq_idSupport
            hcross.entropy_reduction q
    _ = hcross.entropy_reduction.Hfun q.restrictToSupport := by
          exact normalizedValue_idChannel_eq_Hfun hcross.entropy_reduction hreg
            q.restrictToSupport (Dist.restrictToSupport_fullSupport q)

/--
**Boundary Hfun Identity Assumption**

The full-support identity-channel characterization is proved internally above.
The remaining interface says only that boundary `Hfun` is still the normalized
value of full revelation.
-/
structure FiniteHfunBoundaryIdentityAssumptions.{v} where
  Hfun_eq_normalizedValue_id_boundary :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hcross : CrossPriorBlockRepresentation F)
      (_hreg : EntropyRegularity F hcross.entropy_reduction)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      ¬ q.FullSupport →
      hcross.entropy_reduction.Hfun q =
        normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel

/--
**Cardinal Support Boundary Assumption**

Single faithful boundary/cardinal interface for extending the full-support
cardinal value representation across deletion of zero-probability actions.
It bundles the three remaining boundary-value facts needed by the Faddeev
recursion path, without pretending that they have been proved internally.
-/
structure FiniteCardinalSupportBoundaryAssumptions.{v} where
  normalizedValue_support_boundary :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hcross : CrossPriorBlockRepresentation F)
      {A O : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A),
      ¬ q.FullSupport →
      letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q)
  Hfun_boundary_identity :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hcross : CrossPriorBlockRepresentation F)
      (_hreg : EntropyRegularity F hcross.entropy_reduction)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      ¬ q.FullSupport →
      hcross.entropy_reduction.Hfun q =
        normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel
  restricted_coarse_reveal_value :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hcross : CrossPriorBlockRepresentation F)
      (_hreg : EntropyRegularity F hcross.entropy_reduction)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      ¬ (sigmaDist p q).FullSupport →
      let s : Dist ((k : K) × Act k) := sigmaDist p q
      let C : Channel ((k : K) × Act k) K := coarseRevealChannel Act
      letI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
      letI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
      normalizedValue hcross.entropy_reduction.scale_coherence
          s.restrictToSupport (Channel.restrictToSupport C s) =
        hcross.entropy_reduction.Hfun p.restrictToSupport

/-- Recover the boundary normalized-value support interface from the unified
cardinal support boundary assumption. -/
theorem normalizedValueSupportBoundary_of_cardinalBoundary
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u}) :
    FiniteNormalizedValueSupportBoundaryAssumptions.{u} where
  normalizedValue_support_restrict_boundary := hcard.normalizedValue_support_boundary

/-- Recover the boundary Hfun identity interface from the unified cardinal
support boundary assumption. -/
theorem hfunBoundaryIdentity_of_cardinalBoundary
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u}) :
    FiniteHfunBoundaryIdentityAssumptions.{u} where
  Hfun_eq_normalizedValue_id_boundary := hcard.Hfun_boundary_identity

/-- Recover the restricted coarse-reveal value interface from the unified
cardinal support boundary assumption. -/
theorem restrictedCoarseRevealValue_of_cardinalBoundary
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u}) :
    FiniteRestrictedCoarseRevealValueAssumptions.{u} where
  restricted_coarse_reveal_value := hcard.restricted_coarse_reveal_value

/-- Hfun support restriction from boundary Hfun identity and normalized-value
support restriction. -/
theorem Hfun_support_restrict_of_boundary_identity
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    (hid : FiniteHfunBoundaryIdentityAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    hcross.entropy_reduction.Hfun q =
      hcross.entropy_reduction.Hfun q.restrictToSupport := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  by_cases hq : q.FullSupport
  · exact Hfun_support_restrict_fullSupport_of_identity F hax hcross hreg q hq
  · calc
      hcross.entropy_reduction.Hfun q =
          normalizedValue hcross.entropy_reduction.scale_coherence q
            (Channel.idChannel : Channel A A) := by
            exact hid.Hfun_eq_normalizedValue_id_boundary F hax hcross hreg q hq
      _ = normalizedValue hcross.entropy_reduction.scale_coherence
            q.restrictToSupport
            (Channel.restrictToSupport (Channel.idChannel : Channel A A) q) := by
            exact normalizedValue_support_restrict_of_boundary hnorm F hax hcross
              (Channel.idChannel : Channel A A) q
      _ = normalizedValue hcross.entropy_reduction.scale_coherence
            q.restrictToSupport
            (Channel.idChannel : Channel (supportSubtype q) (supportSubtype q)) := by
            exact normalizedValue_restrict_idChannel_eq_idSupport
              hcross.entropy_reduction q
      _ = hcross.entropy_reduction.Hfun q.restrictToSupport := by
            exact normalizedValue_idChannel_eq_Hfun hcross.entropy_reduction hreg
              q.restrictToSupport (Dist.restrictToSupport_fullSupport q)

/-- Package the old Hfun support interface from the narrower boundary identity
assumption. -/
theorem hfunSupportRestriction_of_boundaryIdentity
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    (hid : FiniteHfunBoundaryIdentityAssumptions.{u}) :
    FiniteHfunSupportRestrictionAssumptions.{u} where
  Hfun_support_restrict := by
    intro F hax hcross hreg A _ _ _ q
    exact Hfun_support_restrict_of_boundary_identity hnorm hid F hax hcross hreg q

/--
Pure-trace nontriviality, cross-prior representation, reverse block orientation,
and entropy regularity produce the fixed positive Bool/uniform entropy witness.
-/
theorem uniform_ulift_bool_Hfun_pos_of_A1
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hrec : FaddeevRecursionForm F hcross.entropy_reduction) :
    0 < hcross.entropy_reduction.Hfun (Dist.uniform (A := ULift.{u, 0} Bool)) := by
  let hrelabel : FiniteRelabelingInvarianceAssumptions.{u} :=
    finiteRelabelingInvariance_of_axioms
  let A := ULift.{u, 0} Bool
  let q : Dist A := Dist.uniform
  have hq : q.FullSupport := Dist.uniform_fullSupport (A := A)
  have hstrict :
      F.strictRel
        (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A))
        (inlDist q) (inrDist q) := by
    exact lifted_uninformative_strict_of_relabeling hrelabel F hax q hq
  have hgt :
      normalizedValue hcross.entropy_reduction.scale_coherence q
          (Channel.idChannel : Channel A A) >
        normalizedValue hcross.entropy_reduction.scale_coherence q
          (Channel.uninformativeChannelU A) :=
    strict_block_value_gt hrelabel F hax hcross q q hq hq
      (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A) hstrict
  have hid :
      normalizedValue hcross.entropy_reduction.scale_coherence q
          (Channel.idChannel : Channel A A) =
        hcross.entropy_reduction.Hfun q :=
    normalizedValue_idChannel_eq_Hfun hcross.entropy_reduction hrec.regularity q hq
  have huninf :
      normalizedValue hcross.entropy_reduction.scale_coherence q
          (Channel.uninformativeChannelU A) = 0 :=
    normalizedValue_uninformativeChannel_eq_zero hcross.entropy_reduction hrec.regularity q hq
  rw [hid, huninf] at hgt
  simpa [q] using hgt

/-- The uniform prior on a universe-lifted Bool has positive Shannon entropy. -/
theorem entropy_uniform_ulift_bool_pos : 0 < H(Dist.uniform (A := ULift.{u, 0} Bool)) := by
  exact entropy_pos_of_fullSupport_nontrivial
    (A := ULift.{u, 0} Bool) (Dist.uniform (A := ULift.{u, 0} Bool))
    (Dist.uniform_fullSupport (A := ULift.{u, 0} Bool))

/-- Strict positivity of the Shannon coefficient from a positive entropy value
and the classical Faddeev equality. -/
theorem alpha_strict_pos_of_positive_Hfun_witness
    (F : PrefFamily.{u}) (_hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (_hrec : FaddeevRecursionForm F hcross.entropy_reduction)
    (hHfun_pos :
      0 < hcross.entropy_reduction.Hfun (Dist.uniform (A := ULift.{u, 0} Bool)))
    (alpha : ℝ)
    (hH :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        hcross.entropy_reduction.Hfun q = alpha * H(q)) :
    0 < alpha := by
  have hSh_pos : 0 < H(Dist.uniform (A := ULift.{u, 0} Bool)) :=
    entropy_uniform_ulift_bool_pos
  have hH_bool := hH (A := ULift.{u, 0} Bool) (Dist.uniform (A := ULift.{u, 0} Bool))
  rw [hH_bool] at hHfun_pos
  nlinarith

/-!
## Internal verification of the standard Faddeev hypotheses

The erasure-calibrator argument below is the formal counterpart of the binary
continuity paragraph in the paper.  It is deliberately downstream of the
preference and entropy-reduction development: none of it is part of the
classical Faddeev assumption.
-/

/-- A finite full-support prior whose entropy value is a prescribed natural
multiple of a fixed binary entropy value.  The carrier is allowed to vary with
the exponent, avoiding any hidden identification of differently parenthesised
finite products. -/
structure FiniteEntropyPowerWitness
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (baseValue : ℝ) (n : ℕ) where
  Carrier : Type u
  carrierFintype : Fintype Carrier
  carrierDecidableEq : DecidableEq Carrier
  carrierNonempty : Nonempty Carrier
  prior : @Dist Carrier carrierFintype
  prior_fullSupport : prior.FullSupport
  entropy_eq : @Hfun Carrier carrierFintype carrierDecidableEq carrierNonempty prior =
    (n : ℝ) * baseValue

/-- Iterating the strong-additivity equation constructs the `n`-fold binary
calibrator and proves its entropy is exactly `n` times the binary value. -/
noncomputable def finiteEntropyPowerWitness
    {F : PrefFamily.{u}}
    (hcross : CrossPriorBlockRepresentation F)
    (hrec : FaddeevRecursionForm F hcross.entropy_reduction)
    (base : Dist (ULift.{u, 0} Bool))
    (hbase : base.FullSupport) :
    ∀ n : ℕ,
      FiniteEntropyPowerWitness hcross.entropy_reduction.Hfun
        (hcross.entropy_reduction.Hfun base) n
  | 0 =>
      { Carrier := PUnit.{u + 1}
        carrierFintype := inferInstance
        carrierDecidableEq := inferInstance
        carrierNonempty := inferInstance
        prior := Dist.pure PUnit.unit
        prior_fullSupport := by
          intro x
          simpa using Dist.pure_apply_self x
        entropy_eq := by
          rw [hrec.regularity.H_singleton]
          norm_num }
  | n + 1 => by
      let prev := finiteEntropyPowerWitness hcross hrec base hbase n
      letI : Fintype prev.Carrier := prev.carrierFintype
      letI : DecidableEq prev.Carrier := prev.carrierDecidableEq
      letI : Nonempty prev.Carrier := prev.carrierNonempty
      let Act : ULift.{u, 0} Bool → Type u := fun _ => prev.Carrier
      letI : ∀ b, Fintype (Act b) := fun _ => inferInstance
      letI : ∀ b, DecidableEq (Act b) := fun _ => inferInstance
      letI : ∀ b, Nonempty (Act b) := fun _ => inferInstance
      letI : Nonempty ((b : ULift.{u, 0} Bool) × Act b) :=
        ⟨⟨Classical.arbitrary (ULift.{u, 0} Bool),
          Classical.arbitrary prev.Carrier⟩⟩
      let q : ∀ b, Dist (Act b) := fun _ => prev.prior
      let w := sigmaDist base q
      have hw : w.FullSupport :=
        sigmaDist_fullSupport base q hbase (fun _ => prev.prior_fullSupport)
      refine
        { Carrier := (b : ULift.{u, 0} Bool) × Act b
          carrierFintype := inferInstance
          carrierDecidableEq := inferInstance
          carrierNonempty := inferInstance
          prior := w
          prior_fullSupport := hw
          entropy_eq := ?_ }
      have hadd := hrec.grouping_recursion Act base q
      change hcross.entropy_reduction.Hfun w =
        ((n + 1 : ℕ) : ℝ) * hcross.entropy_reduction.Hfun base
      change hcross.entropy_reduction.Hfun (sigmaDist base q) =
        ((n + 1 : ℕ) : ℝ) * hcross.entropy_reduction.Hfun base
      have hsum :
          (∑ b, base b * hcross.entropy_reduction.Hfun (q b)) =
            (n : ℝ) * hcross.entropy_reduction.Hfun base := by
        simp only [q, prev.entropy_eq]
        rw [← Finset.sum_mul, base.sum_eq_one, one_mul]
      calc
        hcross.entropy_reduction.Hfun (sigmaDist base q) =
            hcross.entropy_reduction.Hfun base +
              ∑ b, base b * hcross.entropy_reduction.Hfun (q b) := hadd
        _ = hcross.entropy_reduction.Hfun base +
              (n : ℝ) * hcross.entropy_reduction.Hfun base := by rw [hsum]
        _ = ((n + 1 : ℕ) : ℝ) *
              hcross.entropy_reduction.Hfun base := by
          push_cast
          ring

/-- A fixed experiment, at a fixed full-support prior, whose normalized value
is the requested nonnegative real number. -/
structure FiniteEntropyErasureCalibrator
    {F : PrefFamily.{u}} (hcross : CrossPriorBlockRepresentation F)
    (c : ℝ) where
  Carrier : Type u
  carrierFintype : Fintype Carrier
  carrierDecidableEq : DecidableEq Carrier
  carrierNonempty : Nonempty Carrier
  Outcome : Type u
  outcomeFintype : Fintype Outcome
  outcomeDecidableEq : DecidableEq Outcome
  prior : @Dist Carrier carrierFintype
  prior_fullSupport : prior.FullSupport
  channel : @Channel Carrier Outcome outcomeFintype
  value_eq :
    @normalizedValue F hcross.entropy_reduction.scale_coherence Carrier Outcome
        carrierFintype carrierDecidableEq carrierNonempty outcomeFintype
        outcomeDecidableEq prior channel = c

/-- Every `c ≥ 0` has a prior-independent erasure calibrator. -/
noncomputable def finiteEntropyErasureCalibrator
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hrec : FaddeevRecursionForm F hcross.entropy_reduction)
    (c : ℝ) (hc : 0 ≤ c) :
    FiniteEntropyErasureCalibrator hcross c := by
  let base : Dist (ULift.{u, 0} Bool) := Dist.uniform
  have hbase : base.FullSupport := Dist.uniform_fullSupport
  have hu :
      0 < hcross.entropy_reduction.Hfun base :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrec
  by_cases hc0 : c = 0
  · subst c
    refine
      { Carrier := ULift.{u, 0} Bool
        carrierFintype := inferInstance
        carrierDecidableEq := inferInstance
        carrierNonempty := inferInstance
        Outcome := PUnit.{u + 1}
        outcomeFintype := inferInstance
        outcomeDecidableEq := inferInstance
        prior := base
        prior_fullSupport := hbase
        channel := Channel.uninformativeChannelU _
        value_eq := ?_ }
    exact normalizedValue_uninformativeChannel_eq_zero
      hcross.entropy_reduction hrec.regularity base hbase
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    let n : ℕ :=
      Classical.choose
        (exists_nat_gt (c / hcross.entropy_reduction.Hfun base))
    have hn :
        c / hcross.entropy_reduction.Hfun base < (n : ℝ) :=
      Classical.choose_spec
        (exists_nat_gt (c / hcross.entropy_reduction.Hfun base))
    have hnpos : 0 < n := by
      have hnreal : (0 : ℝ) < (n : ℝ) :=
        lt_of_le_of_lt (div_nonneg hc (le_of_lt hu)) hn
      exact_mod_cast hnreal
    let power := finiteEntropyPowerWitness hcross hrec base hbase n
    letI : Fintype power.Carrier := power.carrierFintype
    letI : DecidableEq power.Carrier := power.carrierDecidableEq
    letI : Nonempty power.Carrier := power.carrierNonempty
    have hpower_pos :
        0 < hcross.entropy_reduction.Hfun power.prior := by
      rw [power.entropy_eq]
      exact mul_pos (by exact_mod_cast hnpos) hu
    have hc_lt_power :
        c < hcross.entropy_reduction.Hfun power.prior := by
      rw [power.entropy_eq]
      have := (div_lt_iff₀ hu).mp hn
      simpa [mul_comm] using this
    let lam := c / hcross.entropy_reduction.Hfun power.prior
    have hlam0 : 0 < lam := div_pos hcpos hpower_pos
    have hlam1 : lam < 1 := (div_lt_one hpower_pos).mpr hc_lt_power
    let P :=
      publicMixChannel lam hlam0 hlam1
        (Channel.idChannel : Channel power.Carrier power.Carrier)
        (Channel.uninformativeChannelU power.Carrier)
    refine
      { Carrier := power.Carrier
        carrierFintype := inferInstance
        carrierDecidableEq := inferInstance
        carrierNonempty := inferInstance
        Outcome := power.Carrier ⊕ PUnit.{u + 1}
        outcomeFintype := inferInstance
        outcomeDecidableEq := inferInstance
        prior := power.prior
        prior_fullSupport := power.prior_fullSupport
        channel := P
        value_eq := ?_ }
    have hred :=
      hcross.entropy_reduction.value_entropy_reduction
        power.prior power.prior_fullSupport P
    have hint :
        posteriorLawIntegral power.prior P hcross.entropy_reduction.Hfun =
          lam * 0 +
            (1 - lam) * hcross.entropy_reduction.Hfun power.prior := by
      rw [show P = publicMixChannel lam hlam0 hlam1
          (Channel.idChannel : Channel power.Carrier power.Carrier)
          (Channel.uninformativeChannelU power.Carrier) from rfl]
      rw [posteriorLawIntegral_publicMixChannel,
        posteriorLawIntegral_idChannel_Hfun_eq_zero hrec.regularity,
        posteriorLawIntegral_uninformativeChannelU_Hfun_eq_self hrec.regularity]
    rw [hint] at hred
    change normalizedValue hcross.entropy_reduction.scale_coherence power.prior P = c
    unfold normalizedValue
    rw [hred]
    dsimp [lam]
    field_simp [ne_of_gt hpower_pos]
    ring

/-- Coordinate convergence of the binary probability path. -/
theorem faddeevBinaryDistInterior_converges
    (tseq : ℕ → Set.Ioo (0 : ℝ) 1)
    (t : Set.Ioo (0 : ℝ) 1)
    (ht : Tendsto tseq atTop (𝓝 t)) :
    DistConverges
      (fun n => faddeevBinaryDistInterior (tseq n))
      (faddeevBinaryDistInterior t) := by
  have hval :
      Tendsto (fun n => (tseq n : ℝ)) atTop (𝓝 (t : ℝ)) :=
    (continuous_subtype_val.tendsto t).comp ht
  intro b
  rcases b with ⟨b⟩
  cases b
  · simpa [faddeevBinaryDistInterior, faddeevBinaryDist] using
      (tendsto_const_nhds.sub hval)
  · simpa [faddeevBinaryDistInterior, faddeevBinaryDist] using hval

/-- Convergence after embedding the varying binary prior in the left side of
a fixed two-block comparison. -/
theorem inl_faddeevBinaryDistInterior_converges
    {B : Type u} [Fintype B]
    (tseq : ℕ → Set.Ioo (0 : ℝ) 1)
    (t : Set.Ioo (0 : ℝ) 1)
    (ht : Tendsto tseq atTop (𝓝 t)) :
    DistConverges
      (fun n => inlDist (B := B) (faddeevBinaryDistInterior (tseq n)))
      (inlDist (B := B) (faddeevBinaryDistInterior t)) := by
  have hbin := faddeevBinaryDistInterior_converges tseq t ht
  intro x
  cases x with
  | inl b => exact hbin b
  | inr b => simp [inlDist]

/-- Binary continuity derived from primitive A2 by the erasure-calibrator
argument.  Every real threshold is represented by one fixed experiment;
primitive closed-graph continuity therefore makes every sublevel and
superlevel set of the binary entropy closed. -/
theorem faddeevBinaryEntropy_continuous_of_axioms
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hrec : FaddeevRecursionForm F hcross.entropy_reduction) :
    Continuous
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        hcross.entropy_reduction.Hfun (faddeevBinaryDistInterior t)) := by
  let hbin := fun t : Set.Ioo (0 : ℝ) 1 =>
    hcross.entropy_reduction.Hfun (faddeevBinaryDistInterior t)
  rw [continuous_iff_lower_upperSemicontinuous]
  constructor
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : 0 ≤ c
    · let cal := finiteEntropyErasureCalibrator hax hcross hrec c hc
      letI : Fintype cal.Carrier := cal.carrierFintype
      letI : DecidableEq cal.Carrier := cal.carrierDecidableEq
      letI : Nonempty cal.Carrier := cal.carrierNonempty
      letI : Fintype cal.Outcome := cal.outcomeFintype
      letI : DecidableEq cal.Outcome := cal.outcomeDecidableEq
      rw [← isSeqClosed_iff_isClosed]
      intro tseq t htmem htt
      have hrel :
          ∀ n,
            F.rel
              (blockChannel
                (Channel.idChannel :
                  Channel (ULift.{u, 0} Bool) (ULift.{u, 0} Bool))
                cal.channel)
              (inrDist cal.prior)
              (inlDist (faddeevBinaryDistInterior (tseq n))) := by
        intro n
        apply
          (cross_prior_reverse_in_same_block
            finiteRelabelingInvariance_of_axioms F hax hcross
            (faddeevBinaryDistInterior (tseq n)) cal.prior
            (faddeevBinaryDistInterior_fullSupport (tseq n))
            cal.prior_fullSupport Channel.idChannel cal.channel).mpr
        rw [cal.value_eq,
          normalizedValue_idChannel_eq_Hfun
            hcross.entropy_reduction hrec.regularity
            (faddeevBinaryDistInterior (tseq n))
            (faddeevBinaryDistInterior_fullSupport (tseq n))]
        exact htmem n
      have hclosed :=
        hax.closedGraph
          (fun _ =>
            blockChannel
              (Channel.idChannel :
                Channel (ULift.{u, 0} Bool) (ULift.{u, 0} Bool))
              cal.channel)
          (blockChannel
            (Channel.idChannel :
              Channel (ULift.{u, 0} Bool) (ULift.{u, 0} Bool))
            cal.channel)
          (fun _ => inrDist cal.prior)
          (fun n => inlDist (faddeevBinaryDistInterior (tseq n)))
          (inrDist cal.prior)
          (inlDist (faddeevBinaryDistInterior t))
          (by intro a o; exact tendsto_const_nhds)
          (by intro x; exact tendsto_const_nhds)
          (inl_faddeevBinaryDistInterior_converges tseq t htt)
          hrel
      have hge :=
        (cross_prior_reverse_in_same_block
          finiteRelabelingInvariance_of_axioms F hax hcross
          (faddeevBinaryDistInterior t) cal.prior
          (faddeevBinaryDistInterior_fullSupport t)
          cal.prior_fullSupport Channel.idChannel cal.channel).mp hclosed
      change
        normalizedValue hcross.entropy_reduction.scale_coherence
            (faddeevBinaryDistInterior t) Channel.idChannel ≤
          normalizedValue hcross.entropy_reduction.scale_coherence
            cal.prior cal.channel at hge
      change hbin t ≤ c
      calc
        hbin t =
            normalizedValue hcross.entropy_reduction.scale_coherence
              (faddeevBinaryDistInterior t) Channel.idChannel :=
          (normalizedValue_idChannel_eq_Hfun
            hcross.entropy_reduction hrec.regularity
            (faddeevBinaryDistInterior t)
            (faddeevBinaryDistInterior_fullSupport t)).symm
        _ ≤ normalizedValue hcross.entropy_reduction.scale_coherence
              cal.prior cal.channel := hge
        _ = c := cal.value_eq
    · have hcneg : c < 0 := lt_of_not_ge hc
      have hempty : hbin ⁻¹' Set.Iic c = ∅ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
        exact not_le_of_gt (lt_of_lt_of_le hcneg (hrec.regularity.H_nonneg _))
      rw [hempty]
      exact isClosed_empty
  · rw [upperSemicontinuous_iff_isClosed_preimage]
    intro c
    by_cases hc : 0 ≤ c
    · let cal := finiteEntropyErasureCalibrator hax hcross hrec c hc
      letI : Fintype cal.Carrier := cal.carrierFintype
      letI : DecidableEq cal.Carrier := cal.carrierDecidableEq
      letI : Nonempty cal.Carrier := cal.carrierNonempty
      letI : Fintype cal.Outcome := cal.outcomeFintype
      letI : DecidableEq cal.Outcome := cal.outcomeDecidableEq
      rw [← isSeqClosed_iff_isClosed]
      intro tseq t htmem htt
      have hrel :
          ∀ n,
            F.rel
              (blockChannel
                (Channel.idChannel :
                  Channel (ULift.{u, 0} Bool) (ULift.{u, 0} Bool))
                cal.channel)
              (inlDist (faddeevBinaryDistInterior (tseq n)))
              (inrDist cal.prior) := by
        intro n
        apply
          (hcross.cross_prior_block_rep
            (faddeevBinaryDistInterior (tseq n)) cal.prior
            (faddeevBinaryDistInterior_fullSupport (tseq n))
            cal.prior_fullSupport Channel.idChannel cal.channel).mpr
        change
          normalizedValue hcross.entropy_reduction.scale_coherence
              (faddeevBinaryDistInterior (tseq n)) Channel.idChannel ≥
            normalizedValue hcross.entropy_reduction.scale_coherence
              cal.prior cal.channel
        rw [normalizedValue_idChannel_eq_Hfun
          hcross.entropy_reduction hrec.regularity
          (faddeevBinaryDistInterior (tseq n))
          (faddeevBinaryDistInterior_fullSupport (tseq n)),
          cal.value_eq]
        exact htmem n
      have hclosed :=
        hax.closedGraph
          (fun _ =>
            blockChannel
              (Channel.idChannel :
                Channel (ULift.{u, 0} Bool) (ULift.{u, 0} Bool))
              cal.channel)
          (blockChannel
            (Channel.idChannel :
              Channel (ULift.{u, 0} Bool) (ULift.{u, 0} Bool))
            cal.channel)
          (fun n => inlDist (faddeevBinaryDistInterior (tseq n)))
          (fun _ => inrDist cal.prior)
          (inlDist (faddeevBinaryDistInterior t))
          (inrDist cal.prior)
          (by intro a o; exact tendsto_const_nhds)
          (inl_faddeevBinaryDistInterior_converges tseq t htt)
          (by intro x; exact tendsto_const_nhds)
          hrel
      have hge :=
        (hcross.cross_prior_block_rep
          (faddeevBinaryDistInterior t) cal.prior
          (faddeevBinaryDistInterior_fullSupport t)
          cal.prior_fullSupport Channel.idChannel cal.channel).mp hclosed
      change
        normalizedValue hcross.entropy_reduction.scale_coherence
            (faddeevBinaryDistInterior t) Channel.idChannel ≥
          normalizedValue hcross.entropy_reduction.scale_coherence
            cal.prior cal.channel at hge
      change c ≤ hbin t
      calc
        c = normalizedValue hcross.entropy_reduction.scale_coherence
              cal.prior cal.channel := cal.value_eq.symm
        _ ≤ normalizedValue hcross.entropy_reduction.scale_coherence
              (faddeevBinaryDistInterior t) Channel.idChannel := hge
        _ = hbin t :=
          normalizedValue_idChannel_eq_Hfun
            hcross.entropy_reduction hrec.regularity
            (faddeevBinaryDistInterior t)
            (faddeevBinaryDistInterior_fullSupport t)
    · have hcneg : c < 0 := lt_of_not_ge hc
      have hall : hbin ⁻¹' Set.Ici c = Set.univ := by
        ext t
        simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_univ, iff_true]
        exact le_trans (le_of_lt hcneg) (hrec.regularity.H_nonneg _)
      rw [hall]
      exact isClosed_univ

/-- Normalized values are invariant under a bijective action relabeling.  This
is derived from action processing in both directions and the cross-prior value bridge. -/
theorem normalizedValue_actionRelabel_of_crossPrior
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    haveI : Nonempty B := ⟨eA (Classical.arbitrary A)⟩
    normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel eA (Equiv.refl O) P) =
      normalizedValue hcross.entropy_reduction.scale_coherence q P := by
  haveI : Nonempty B := ⟨eA (Classical.arbitrary A)⟩
  set P' : Channel B O :=
    Relabeling.relabelChannel eA (Equiv.refl O) P with hP'
  have hqB : (Relabeling.relabelDist eA q).FullSupport :=
    Relabeling.relabelDist_fullSupport eA q hq
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q)
        (inrDist (Relabeling.relabelDist eA q)) := by
    have h := hax.actionProcessing P q (Relabeling.actionEquivKernel eA) P'
      (Relabeling.relabelChannel_isBayesPushforwardCompletion eA P q)
    simpa [P', Relabeling.actionPushforward_equiv] using h
  have hq_to_old :
      F.rel (blockChannel P' P)
        (inlDist (Relabeling.relabelDist eA q)) (inrDist q) := by
    have h :=
      hax.actionProcessing P' (Relabeling.relabelDist eA q)
        (Relabeling.actionEquivKernel eA.symm) P
        (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion eA P q)
    simpa [P', Relabeling.actionPushforward_equiv,
      Relabeling.relabelDist_symm] using h
  have hge₁ :=
    (hcross.cross_prior_block_rep q (Relabeling.relabelDist eA q)
      hq hqB P P').mp hq_to_new
  have hge₂ :=
    (hcross.cross_prior_block_rep (Relabeling.relabelDist eA q) q
      hqB hq P' P).mp hq_to_old
  have e₁ :
      normalizedValue hcross.entropy_reduction.scale_coherence q P ≥
        normalizedValue hcross.entropy_reduction.scale_coherence
          (Relabeling.relabelDist eA q) P' := by
    simpa [normalizedValue] using hge₁
  have e₂ :
      normalizedValue hcross.entropy_reduction.scale_coherence
          (Relabeling.relabelDist eA q) P' ≥
        normalizedValue hcross.entropy_reduction.scale_coherence q P := by
    simpa [normalizedValue] using hge₂
  exact le_antisymm e₁ e₂

/-- Merely relabeling outcomes preserves normalized value, because the two
channels induce the same posterior law. -/
theorem normalizedValue_outcomeRelabel
    {F : PrefFamily.{u}}
    (hcross : CrossPriorBlockRepresentation F)
    {A O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (q : Dist A) (P : Channel A O) :
    normalizedValue hcross.entropy_reduction.scale_coherence q
        (Relabeling.relabelChannel (Equiv.refl A) eO P) =
      normalizedValue hcross.entropy_reduction.scale_coherence q P := by
  have hchan :
      Channel.postprocess P (posteriorLawEquivKernel eO) =
        Relabeling.relabelChannel (Equiv.refl A) eO P := by
    ext a y
    change (∑ o : O, P a o * Dist.pure (eO o) y) = P a (eO.symm y)
    rw [Fintype.sum_eq_single (eO.symm y)]
    · simp
    · intro o hone
      have hne : y ≠ eO o := by
        intro hy
        apply hone
        exact eO.injective (by simpa using hy.symm)
      simp [Dist.pure_apply_ne _ _ hne]
  have hsame :=
    samePosteriorLawExp_of_bijective_postprocess q P eO
  rw [hchan] at hsame
  let hVrep :=
    hcross.entropy_reduction.scale_coherence.branch_agg.value_rep
  have hV := hVrep.respects_same_posterior_law q _ _ hsame
  unfold normalizedValue
  change
    hVrep.V q
          (experimentOfChannel
            (Relabeling.relabelChannel (Equiv.refl A) eO P)) /
        hcross.entropy_reduction.scale_coherence.scale q =
      hVrep.V q (experimentOfChannel P) /
        hcross.entropy_reduction.scale_coherence.scale q
  exact congrArg
    (fun x => x / hcross.entropy_reduction.scale_coherence.scale q) hV.symm

/-- Simultaneous action/outcome relabeling preserves normalized value. -/
theorem normalizedValue_relabel_of_crossPrior
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel eA eO P) =
      normalizedValue hcross.entropy_reduction.scale_coherence q P := by
  let P₁ : Channel B O :=
    Relabeling.relabelChannel eA (Equiv.refl O) P
  calc
    normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel eA eO P) =
      normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel (Equiv.refl B) eO P₁) := by
          rw [Relabeling.relabelChannel_action_then_outcome]
    _ = normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist eA q) P₁ :=
      normalizedValue_outcomeRelabel hcross eO _ P₁
    _ = normalizedValue hcross.entropy_reduction.scale_coherence q P :=
      normalizedValue_actionRelabel_of_crossPrior F hax hcross eA q hq P

/-- Full-support relabeling invariance of the entropy candidate, derived from
the ordinal action-relabeling axioms and the identity-channel characterization. -/
theorem Hfun_fullSupport_relabel_of_crossPrior
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    hcross.entropy_reduction.Hfun (Relabeling.relabelDist e q) =
      hcross.entropy_reduction.Hfun q := by
  have hqB : (Relabeling.relabelDist e q).FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  calc
    hcross.entropy_reduction.Hfun (Relabeling.relabelDist e q) =
        normalizedValue hcross.entropy_reduction.scale_coherence
          (Relabeling.relabelDist e q)
          (Channel.idChannel : Channel B B) :=
      Hfun_eq_normalizedValue_id_fullSupport
        hcross.entropy_reduction hreg _ hqB
    _ = normalizedValue hcross.entropy_reduction.scale_coherence q
          (Channel.idChannel : Channel A A) := by
      have h :=
        normalizedValue_relabel_of_crossPrior
          F hax hcross e e q hq
          (Channel.idChannel : Channel A A)
      have hid :
          Relabeling.relabelChannel e e
              (Channel.idChannel : Channel A A) =
            (Channel.idChannel : Channel B B) := by
        ext b o
        simp only [Relabeling.relabelChannel, Channel.idChannel,
          Relabeling.relabelDist_apply]
        rw [Dist.pure_apply, Dist.pure_apply]
        simp
      rw [hid] at h
      exact h
    _ = hcross.entropy_reduction.Hfun q :=
      normalizedValue_idChannel_eq_Hfun
        hcross.entropy_reduction hreg q hq

/-- Assemble exactly the preference-free standard Faddeev hypotheses from the
internally proved project facts. -/
theorem finiteFaddeevStandardHypotheses_of_axioms
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hrec : FaddeevRecursionForm F hcross.entropy_reduction)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
        hcross.entropy_reduction.Hfun q =
          hcross.entropy_reduction.Hfun q.restrictToSupport) :
    FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun where
  nonnegative := hrec.regularity.H_nonneg
  pointMass_zero := hrec.regularity.H_singleton
  fullSupport_relabel := by
    intro A B _ _ _ _ _ _ e q hq
    exact Hfun_fullSupport_relabel_of_crossPrior hax hcross hrec.regularity e q hq
  support_restriction := hsupport
  binary_continuous :=
    faddeevBinaryEntropy_continuous_of_axioms hax hcross hrec
  strong_additivity := hrec.grouping_recursion

/--
**Faddeev Entropy Form from Split Components**

Assemble the downstream `FaddeevEntropyForm` from the split assumptions.
-/
noncomputable def FaddeevEntropyForm_of_parts
    (hreg : FiniteEntropyRegularityFromAxiomsAssumptions.{u})
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F) :
    FaddeevEntropyForm F := by
  let hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u} :=
    restrictedCoarseRevealValue_of_cardinalBoundary hcard
  let hregular : EntropyRegularity F hcross.entropy_reduction :=
    hreg.of_entropy_reduction F hax hcross.entropy_reduction
  let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
    hfunSupportRestriction_of_boundaryIdentity hnorm hid
  let hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    faddeevRecursionForm_of_coarseReveal_parts
      hblock hred hnorm hhfun hrestricted F hax hcross hregular
  let hstandard :
      FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun :=
    finiteFaddeevStandardHypotheses_of_axioms hax hcross hrecForm
      (fun q => hhfun.Hfun_support_restrict F hax hcross hregular q)
  let hex :=
    hfad.of_standard_hypotheses
      hcross.entropy_reduction.Hfun hstandard
  let alpha := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hH :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        hcross.entropy_reduction.Hfun q = alpha * H(q) :=
    hspec.2
  have hHfun_pos :
      0 < hcross.entropy_reduction.Hfun (Dist.uniform (A := ULift.{u, 0} Bool)) :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrecForm
  exact
    { cross_prior := hcross
      alpha := alpha
      alpha_pos :=
        alpha_strict_pos_of_positive_Hfun_witness F hax hcross hrecForm hHfun_pos alpha hH
      H_eq_alpha_shannon := hH
      a3_block_equivalence := a3_block_equivalence_of_traceAxioms F hax }

/-!
## Bridge Theorems

These theorems show how to use the Faddeev assumption in the sufficiency spine.
-/

/--
**Faddeev Entropy Form from Split Assumptions**

Given the split Faddeev assumptions, PureTraceConditions, and cross-prior block
representation, derive Faddeev entropy form.
-/
noncomputable def faddeevEntropyForm_of_assumption
    (hreg : FiniteEntropyRegularityFromAxiomsAssumptions.{u})
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F) :
    FaddeevEntropyForm F :=
  FaddeevEntropyForm_of_parts hreg hblock hred hcard hfad F hax hcross

/--
**Faddeev Entropy Form from All External Assumptions**

Given the external assumptions through scale coherence, Cross-Prior Block,
Faddeev, and PureTraceConditions,
derive Faddeev entropy form.

This composes the first six sufficiency bridges:
1. PureTraceConditions → PosteriorLawSufficiency (via Blackwell)
2. PosteriorLawSufficiency → PosteriorValueRepresentation (via Herstein-Milnor)
3. PosteriorValueRepresentation → BranchAggregationStructure (via Branch Aggregation)
4. BranchAggregationStructure → ScaleCoherenceStructure (via Scale Coherence)
5. ScaleCoherenceStructure → EntropyReductionRepresentation
   (via internal normalized chain rule)
6. EntropyReductionRepresentation → CrossPriorBlockRepresentation (via blockbridge)
7. CrossPriorBlockRepresentation → FaddeevEntropyForm (via entropy regularity,
   Faddeev recursion, classical Faddeev, and internal relabeling/nontriviality positivity)

Paper: Full sufficiency proof.
-/
noncomputable def faddeevEntropyForm_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (hreg : FiniteEntropyRegularityFromAxiomsAssumptions.{u})
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hax : PureTraceConditions F) :
    FaddeevEntropyForm F :=
  let hentropyStruct :=
    entropyReduction_of_axioms F hblackwell hhm hbranch hscale hax
  let hcrossStruct := crossPriorBlockRepresentation_of_unscaled hcross F hax hentropyStruct
  FaddeevEntropyForm_of_parts hreg hblock hred hcard hfad F hax hcrossStruct

/-!
## Full-Support Sufficiency from Assumptions

Combine external assumptions to derive full-support MI representation.
-/

/--
**Full-Support Sufficiency MI Package from All Assumptions**

Given all sufficiency external assumptions and PureTraceConditions, derive the
full-support MI representation: F.rel P q q' ↔ α·I(q,P) ≥ α·I(q',P) for
full-support q, q'.

This uses:
1. `faddeevEntropyForm_of_axioms` to get FaddeevEntropyForm
2. `FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm` (proved in pure Lean)
-/
theorem fullSupportSufficiency_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (hreg : FiniteEntropyRegularityFromAxiomsAssumptions.{u})
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hax : PureTraceConditions F) :
    FullSupportSufficiencyMIPackage F :=
  let hfadStruct :=
    faddeevEntropyForm_of_axioms F hblackwell hhm hbranch hscale hcross
      hreg hblock hred hcard hfad hax
  FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F hfadStruct

/-!
## Spine Integration Helper

Shows how to fill the `entropy_to_faddeev` field of `SufficiencySpineAssumptions`.
-/

/--
**Cross-Prior to Faddeev Bridge from Split Assumptions**

Given PureTraceConditions and the split Faddeev external assumptions, provides the
bridge from CrossPriorBlockRepresentation to FaddeevEntropyForm.

This can be used to fill the `entropy_to_faddeev` field when constructing
`SufficiencySpineAssumptions`.
-/
noncomputable def entropy_to_faddeev_of_assumption
    (hreg : FiniteEntropyRegularityFromAxiomsAssumptions.{u})
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F) :
    CrossPriorBlockRepresentation F → FaddeevEntropyForm F :=
  fun hcross =>
    FaddeevEntropyForm_of_parts hreg hblock hred hcard hfad F hax hcross

end TraceableAgency
