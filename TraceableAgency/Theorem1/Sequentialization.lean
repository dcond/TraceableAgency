/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.Benchmark
import TraceableAgency.Theorem1.PairOrder

/-!
# Terminal-payoff sequentialization

An arbitrary joint payoff-record channel can be read as a first-stage record
channel whose branch is the observed pair `(o,r)`, followed by a terminal
continuation that pays `o` surely and reveals no further record.  This module
constructs that compound explicitly and proves, using exact record processors,
that it is behaviorally equivalent to the original channel.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-! ## The one-action terminal continuation and its same-action lift -/

/-- Every terminal branch has a one-point explicit-record alphabet. -/
abbrev sequentialTerminalRecord
    {O R : Type u} (_y : O × R) : Type u := PUnit

/-- The literal one-action continuation attached to branch `y=(o,r)`: it pays
`o` surely and emits the uninformative one-point record. -/
noncomputable def sequentialTerminalOneAction
    {O R : Type u}
    [Fintype O] [DecidableEq O]
    (y : O × R) : Channel PUnit (O × sequentialTerminalRecord y) :=
  deterministicPayoffChannel y.1

/-- The same terminal continuation on the action alphabet of the first stage.
It ignores the action, pays the branch payoff surely, and emits `PUnit`. -/
noncomputable def sequentialTerminalContinuation
    {O A R : Type u}
    [Fintype O] [DecidableEq O] [Fintype A]
    (y : O × R) : Channel A (O × sequentialTerminalRecord y) :=
  uninformativeAtPayoff y.1

/-- Report every action as the unique one-action label. -/
noncomputable def collapseToOneActionKernel
    {A : Type u} [Fintype A] : Channel.ActionKernel A PUnit :=
  fun _ => TraceableAgency.Dist.pure PUnit.unit

/-- Starting at the unique action, redraw an action with law `q`. -/
noncomputable def redrawFromOneActionKernel
    {A : Type u} [Fintype A]
    (q : TraceableAgency.Dist A) : Channel.ActionKernel PUnit A :=
  fun _ => q

theorem actionPushforward_collapseToOneAction
    {A : Type u} [Fintype A]
    (q : TraceableAgency.Dist A) :
    Channel.actionPushforward q (collapseToOneActionKernel (A := A)) =
      TraceableAgency.Dist.pure PUnit.unit := by
  ext b
  cases b
  simp [Channel.actionPushforward, collapseToOneActionKernel, q.sum_eq_one]

theorem actionPushforward_redrawFromOneAction
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : TraceableAgency.Dist A) :
    Channel.actionPushforward (TraceableAgency.Dist.pure PUnit.unit)
        (redrawFromOneActionKernel q) = q := by
  ext a
  simp [Channel.actionPushforward, redrawFromOneActionKernel]

/-- Collapsing the same-action terminal continuation to its literal one-action
form satisfies A5's exact joint-law equation. -/
theorem collapseTerminal_isActionProcessorCompletion
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : TraceableAgency.Dist A) (y : O × R) :
    IsActionProcessorCompletion (sequentialTerminalContinuation (A := A) y) q
      (collapseToOneActionKernel (A := A))
      (sequentialTerminalOneAction y) := by
  intro b z
  cases b
  rw [show Channel.actionPushforward q
      (collapseToOneActionKernel (A := A)) PUnit.unit = 1 by
    rw [actionPushforward_collapseToOneAction]
    exact TraceableAgency.Dist.pure_apply_self PUnit.unit]
  simp [sequentialTerminalContinuation, sequentialTerminalOneAction,
    collapseToOneActionKernel, uninformativeAtPayoff,
    deterministicPayoffChannel, ← Finset.sum_mul, q.sum_eq_one]

/-- Redrawing `q` from the literal one-action continuation recovers the
same-action continuation and satisfies A5's exact joint-law equation. -/
theorem redrawTerminal_isActionProcessorCompletion
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : TraceableAgency.Dist A) (y : O × R) :
    IsActionProcessorCompletion (sequentialTerminalOneAction y)
      (TraceableAgency.Dist.pure PUnit.unit)
      (redrawFromOneActionKernel q)
      (sequentialTerminalContinuation (A := A) y) := by
  intro a z
  rw [show Channel.actionPushforward
      (TraceableAgency.Dist.pure PUnit.unit)
      (redrawFromOneActionKernel q) a = q a by
    rw [actionPushforward_redrawFromOneAction]]
  simp [sequentialTerminalContinuation, sequentialTerminalOneAction,
    redrawFromOneActionKernel, uninformativeAtPayoff,
    deterministicPayoffChannel]

/-- A5 identifies the lifted terminal continuation with its literal
one-action form, in both oriented pair comparisons. -/
theorem terminalContinuation_pairWeakEquiv_oneAction
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : FixedPayoffPrefFamily O) (h5 : A5_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (y : O × R) :
    pairWeak F q (sequentialTerminalContinuation (A := A) y)
        (TraceableAgency.Dist.pure PUnit.unit)
        (sequentialTerminalOneAction y) ∧
      pairWeak F (TraceableAgency.Dist.pure PUnit.unit)
        (sequentialTerminalOneAction y)
        q (sequentialTerminalContinuation (A := A) y) := by
  constructor
  · have hh := h5 (sequentialTerminalContinuation (A := A) y) q
      (collapseToOneActionKernel (A := A))
      (sequentialTerminalOneAction y)
      (collapseTerminal_isActionProcessorCompletion q y)
    simpa [actionPushforward_collapseToOneAction] using hh
  · have hh := h5 (sequentialTerminalOneAction y)
      (TraceableAgency.Dist.pure PUnit.unit)
      (redrawFromOneActionKernel q)
      (sequentialTerminalContinuation (A := A) y)
      (redrawTerminal_isActionProcessorCompletion q y)
    simpa [actionPushforward_redrawFromOneAction] using hh

/-! ## The sequentialized channel and its two record processors -/

/-- Sequentialize `K`: first announce `y=(o,r)` according to `K`, then pay
`o` terminally and reveal only a one-point continuation record. -/
noncomputable def sequentializedChannel
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R] [DecidableEq R]
    (K : Channel A (O × R)) :
    Channel A (O × ((y : O × R) × sequentialTerminalRecord y)) :=
  commonPayoffCompound sequentialTerminalRecord K
    (fun y => sequentialTerminalContinuation (A := A) y)

/-- A channel on a nonempty action alphabet supplies an actual payoff label.
Thus the behavioral sequentialization theorems below do not assume separately
that the finite payoff alphabet is inhabited. -/
theorem payoffNonemptyOfChannel
    {O A R : Type u}
    [Fintype O] [Fintype A] [Nonempty A] [Fintype R]
    (K : Channel A (O × R)) : Nonempty O := by
  let a : A := Classical.choice (inferInstance : Nonempty A)
  let z : O × R := Classical.choice (Relabeling.nonempty_of_dist (K a))
  exact ⟨z.1⟩

/-- Copy the already observed pair `(o,r)` into the compound record. -/
noncomputable def copyObservedPairRecordProcessor
    {O R : Type u}
    [Fintype O] [DecidableEq O] [Fintype R] [DecidableEq R] :
    RecordProcessor O R ((y : O × R) × sequentialTerminalRecord y) :=
  fun z => TraceableAgency.Dist.pure ⟨z, PUnit.unit⟩

/-- Delete the copied branch label, retaining its original record component. -/
noncomputable def deleteObservedPairRecordProcessor
    {O R : Type u}
    [Fintype R] [DecidableEq R] :
    RecordProcessor O ((y : O × R) × sequentialTerminalRecord y) R :=
  fun z => TraceableAgency.Dist.pure z.2.1.2

/-- Copying the observed payoff-record pair is exactly the sequentialized
compound, not merely an equality at one prior. -/
theorem recordPostprocess_copyObservedPair
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R] [DecidableEq R]
    (K : Channel A (O × R)) :
    recordPostprocess K copyObservedPairRecordProcessor =
      sequentializedChannel K := by
  classical
  ext a z
  rcases z with ⟨o, ⟨⟨o', r⟩, s⟩⟩
  cases s
  by_cases h : o = o'
  · subst o'
    simp [recordPostprocess, payoffPreservingRecordKernel,
      copyObservedPairRecordProcessor, Channel.postprocess,
      sequentializedChannel, commonPayoffCompound,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      compoundPayoffRecordEquiv, sigmaPayoffRecordEquiv,
      seqComposeDep, seqComposeDepProb,
      sequentialTerminalContinuation, uninformativeAtPayoff,
      Fintype.sum_prod_type, TraceableAgency.Dist.pure_apply]
  · have h' : o' ≠ o := fun heq => h heq.symm
    simp [recordPostprocess, payoffPreservingRecordKernel,
      copyObservedPairRecordProcessor, Channel.postprocess,
      sequentializedChannel, commonPayoffCompound,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      compoundPayoffRecordEquiv, sigmaPayoffRecordEquiv,
      seqComposeDep, seqComposeDepProb,
      sequentialTerminalContinuation, uninformativeAtPayoff,
      Fintype.sum_prod_type, TraceableAgency.Dist.pure_apply, h, h']

/-- Deleting the copied pair from the sequentialized compound recovers `K`
exactly, again channelwise and independently of the prior. -/
theorem recordPostprocess_deleteObservedPair
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R] [DecidableEq R]
    (K : Channel A (O × R)) :
    recordPostprocess (sequentializedChannel K)
        deleteObservedPairRecordProcessor = K := by
  classical
  ext a z
  rcases z with ⟨o, r⟩
  simp [recordPostprocess, payoffPreservingRecordKernel,
    deleteObservedPairRecordProcessor, Channel.postprocess,
    sequentializedChannel, commonPayoffCompound,
    Relabeling.relabelChannel, Relabeling.relabelDist,
    compoundPayoffRecordEquiv, sigmaPayoffRecordEquiv,
    seqComposeDep, seqComposeDepProb,
    sequentialTerminalContinuation, uninformativeAtPayoff,
    Fintype.sum_prod_type, Fintype.sum_sigma,
    TraceableAgency.Dist.pure_apply]

/-! ## Behavioral equivalence -/

/-- A4 gives both oriented weak comparisons between a channel and its
terminal-payoff sequentialization. -/
theorem sequentialization_pairWeakEquiv
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h4 : A4_RecordDataProcessing F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    letI : Nonempty O := payoffNonemptyOfChannel K
    pairWeak F q K q (sequentializedChannel K) ∧
      pairWeak F q (sequentializedChannel K) q K := by
  letI : Nonempty O := payoffNonemptyOfChannel K
  constructor
  · rw [← recordPostprocess_copyObservedPair K]
    exact h4 K copyObservedPairRecordProcessor q
  · have hh := h4 (sequentializedChannel K)
      deleteObservedPairRecordProcessor q
    rw [recordPostprocess_deleteObservedPair K] at hh
    exact hh

/-- In the paper's same oriented block, sequentialization is genuine
indifference.  A1/A5/A7 enter only to identify the reverse oriented pair
comparison with the reverse comparison inside this block. -/
theorem sequentialization_pairIndiff
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F) (h5 : A5_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    letI : Nonempty O := payoffNonemptyOfChannel K
    pairIndiff F q K q (sequentializedChannel K) := by
  letI : Nonempty O := payoffNonemptyOfChannel K
  let hpair := sequentialization_pairWeakEquiv F h4 q K
  exact ⟨hpair.1,
    (sameBlock_reverse_iff_pairWeak_swap F h1 h3 h4 h5
      q K q (sequentializedChannel K)).2 hpair.2⟩

/-! ## Terminal payoff and information identities -/

/-- Sequentialization preserves terminal expected payoff exactly. -/
theorem expectedPayoffUtility_sequentializedChannel
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R]
    (u : O → ℝ) (q : TraceableAgency.Dist A)
    (K : Channel A (O × R)) :
    expectedPayoffUtility u q (sequentializedChannel K) =
      expectedPayoffUtility u q K := by
  rw [← recordPostprocess_copyObservedPair K]
  exact expectedPayoffUtility_recordPostprocess
    u q K copyObservedPairRecordProcessor

/-- The one-point terminal continuation contributes no further action
information, so sequentialization preserves the mutual information in `K`. -/
theorem mutualInfo_sequentializedChannel
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R]
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    mutualInfo q (sequentializedChannel K) = mutualInfo q K := by
  apply le_antisymm
  · rw [← recordPostprocess_copyObservedPair K]
    exact mutualInfo_outcome_postprocess_le q K
      (payoffPreservingRecordKernel copyObservedPairRecordProcessor)
  · have hh := mutualInfo_outcome_postprocess_le q (sequentializedChannel K)
      (payoffPreservingRecordKernel deleteObservedPairRecordProcessor)
    change mutualInfo q (recordPostprocess (sequentializedChannel K)
        deleteObservedPairRecordProcessor) ≤
      mutualInfo q (sequentializedChannel K) at hh
    rw [recordPostprocess_deleteObservedPair K] at hh
    exact hh

end TraceableAgency.Theorem1
