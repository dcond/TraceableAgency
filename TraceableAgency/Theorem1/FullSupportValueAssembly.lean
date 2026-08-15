/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PayoffBranchTelescope
import TraceableAgency.Theorem1.ConstantTraceAnchorGeneral
import TraceableAgency.Theorem1.SingletonActionValue
import TraceableAgency.Theorem1.Sequentialization
import TraceableAgency.Theorem1.RepresentationAssembly

/-!
# Assembly of the normalized value at full-support priors

This file isolates the last numerical calculation.  Its only non-structural
input is the payoff increment from changing one reached deterministic-payoff
branch away from the separate v5 trace anchor.  Zero-mass branches are handled
directly at the level of marked terminal laws; finite telescoping then gives
the value of every deterministic-payoff profile, and A6 sequentialization
reduces an arbitrary payoff-record channel to such a profile.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-! ## The one remaining numerical input -/

/-- At a positive first-stage branch, changing the deterministic terminal
payoff from the trace anchor to `o` changes normalized value by the branch
probability times `u(o) - u(o_*)`.

The action alphabet is required to be nontrivial because the singleton case
is already covered independently by
`normalizedMarkedUtility_eq_traceTemperedValue_of_subsingleton`. -/
def PositiveBranchPayoffIncrementFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor) : Prop :=
  ∀ {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (_htarget : 0 < Channel.outcomeMarginal P q target) (o : O),
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff
            (fun _ ↦ h.traceAnchor) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ h.traceAnchor)) =
      Channel.outcomeMarginal P q target *
        (materialPayoffUtility F h o -
          materialPayoffUtility F h h.traceAnchor)

/-! ## Zero-mass branches -/

/-- Altering the deterministic payoff attached to an unreached first-stage
branch leaves the complete marked terminal law unchanged. -/
theorem sameMarkedTerminalLaw_payoffBranch_update_of_zeroMass
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o o0 : O)
    (hzero : Channel.outcomeMarginal P q target = 0) :
    SameMarkedTerminalLaw q
      (payoffBranchExperiment P
        (updateBranchPayoff (fun _ ↦ o0) target o))
      (payoffBranchExperiment P (fun _ ↦ o0)) := by
  classical
  intro phi
  change
    markedChannelIntegral q
        (payoffBranchCompound P
          (updateBranchPayoff (fun _ ↦ o0) target o)) phi =
      markedChannelIntegral q
        (payoffBranchCompound P (fun _ ↦ o0)) phi
  simp only [payoffBranchCompound]
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hy : y = target
  · subst y
    rw [hzero]
    simp
  · simp [payoffBranchContinuation, updateBranchPayoff_of_ne _ _ _ _ hy]

/-- The single-branch increment formula extends automatically from positive
branches to zero-mass branches. -/
theorem payoffBranchIncrementFormula_allBranches
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (hpositive : PositiveBranchPayoffIncrementFormula F h)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (o : O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff
            (fun _ ↦ h.traceAnchor) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ h.traceAnchor)) =
      Channel.outcomeMarginal P q target *
        (materialPayoffUtility F h o -
          materialPayoffUtility F h h.traceAnchor) := by
  by_cases htarget : 0 < Channel.outcomeMarginal P q target
  · exact hpositive q hq P target htarget o
  · have hzero : Channel.outcomeMarginal P q target = 0 :=
      le_antisymm (le_of_not_gt htarget)
        ((Channel.outcomeMarginal P q).nonneg target)
    have hsame :=
      sameMarkedTerminalLaw_payoffBranch_update_of_zeroMass
        q P target o (h.traceAnchor) hzero
    have hvalue := normalizedMarkedUtility_respects_sameMarkedTerminalLaw
      F h q hq _ _ hsame
    rw [hvalue, sub_self, hzero, zero_mul]

/-! ## Deterministic payoff profiles -/

/-- Under the positive-branch increment formula, every deterministic-payoff
compound has its trace-tempered numerical value. -/
theorem normalizedMarkedUtility_payoffBranchFormula
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (hpositive : PositiveBranchPayoffIncrementFormula F h)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (payoff : Y → O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P payoff) =
      traceTemperedValue (materialPayoffUtility F h)
        (globalTraceLambda F h) q (payoffBranchCompound P payoff) := by
  have htelescope := normalizedMarkedUtility_payoffBranch_sum
    F h q hq P (h.traceAnchor) payoff
      (materialPayoffUtility F h)
      (fun target ↦
        payoffBranchIncrementFormula_allBranches
          F h hpositive q hq P target (payoff target))
  have hAnchor : ∀ (a : A) (o : O)
      (r : (payoffBranchExperiment P
        (fun _ ↦ h.traceAnchor)).RecordType),
      o ≠ h.traceAnchor →
        (payoffBranchExperiment P
          (fun _ ↦ h.traceAnchor)).K a (o, r) = 0 := by
    classical
    intro a o r ho
    simp [payoffBranchExperiment, payoffBranchCompound,
      commonPayoffCompound, Relabeling.relabelChannel,
      Relabeling.relabelDist, compoundPayoffRecordEquiv,
      sigmaPayoffRecordEquiv, seqComposeDep, seqComposeDepProb,
      payoffBranchContinuation, uninformativeAtPayoff, ho]
  have hbaseline :=
    normalizedMarkedUtility_eq_materialUtility_add_globalTraceLambda_mul_mutualInfo_of_sureTraceAnchor
      F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ h.traceAnchor)) hAnchor
  change
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ h.traceAnchor)) =
      materialPayoffUtility F h h.traceAnchor +
        globalTraceLambda F h *
        mutualInfo q
          (payoffBranchCompound P
            (fun _ ↦ h.traceAnchor)) at hbaseline
  rw [mutualInfo_payoffBranchCompound] at hbaseline
  rw [htelescope, hbaseline]
  rw [traceTemperedValue_payoffBranchCompound]
  have hmass : ∑ y : Y, Channel.outcomeMarginal P q y = 1 :=
    (Channel.outcomeMarginal P q).sum_eq_one
  have hsum :
      (∑ y : Y, Channel.outcomeMarginal P q y *
        (materialPayoffUtility F h (payoff y) -
          materialPayoffUtility F h h.traceAnchor)) =
        (∑ y : Y, Channel.outcomeMarginal P q y *
          materialPayoffUtility F h (payoff y)) -
          materialPayoffUtility F h h.traceAnchor := by
    calc
      (∑ y : Y, Channel.outcomeMarginal P q y *
          (materialPayoffUtility F h (payoff y) -
            materialPayoffUtility F h h.traceAnchor)) =
          ∑ y : Y,
            (Channel.outcomeMarginal P q y *
                materialPayoffUtility F h (payoff y) -
              Channel.outcomeMarginal P q y *
                materialPayoffUtility F h h.traceAnchor) := by
            apply Finset.sum_congr rfl
            intro y _hy
            ring
      _ = (∑ y : Y, Channel.outcomeMarginal P q y *
              materialPayoffUtility F h (payoff y)) -
            ∑ y : Y, Channel.outcomeMarginal P q y *
              materialPayoffUtility F h h.traceAnchor := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ y : Y, Channel.outcomeMarginal P q y *
              materialPayoffUtility F h (payoff y)) -
            (∑ y : Y, Channel.outcomeMarginal P q y) *
              materialPayoffUtility F h h.traceAnchor := by
            rw [Finset.sum_mul]
      _ = (∑ y : Y, Channel.outcomeMarginal P q y *
              materialPayoffUtility F h (payoff y)) -
            materialPayoffUtility F h h.traceAnchor := by
            rw [hmass, one_mul]
  rw [hsum]
  ring

/-! ## Arbitrary full-support channels -/

/-- A channel and its terminal-payoff sequentialization have the same
normalized marked utility. -/
theorem normalizedMarkedUtility_sequentializedChannel
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (K : Channel A (O × R)) :
    letI : Nonempty O := payoffNonemptyOfChannel K
    normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) =
      normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (sequentializedChannel K)) := by
  letI : Nonempty O := payoffNonemptyOfChannel K
  have hpair := sequentialization_pairWeakEquiv F h.a4 q K
  have hforward :=
    (pairWeak_markedExperiments_iff_normalizedMarkedUtility
      F h q q hq hq
        (markedExperimentOfChannel K)
        (markedExperimentOfChannel (sequentializedChannel K))).1 hpair.1
  have hbackward :=
    (pairWeak_markedExperiments_iff_normalizedMarkedUtility
      F h q q hq hq
        (markedExperimentOfChannel (sequentializedChannel K))
        (markedExperimentOfChannel K)).1 hpair.2
  exact le_antisymm hbackward hforward

/-- The positive reached-branch payoff increment, together with the already
proved singleton-action case, implies the complete normalized numerical
formula at every full-support prior. -/
theorem fullSupportNormalizedValueFormula_of_positiveBranchPayoffIncrement
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (hpositive : PositiveBranchPayoffIncrementFormula F h) :
    FullSupportNormalizedValueFormula F h := by
  intro A R _ _ _ _ _ _ q hq K
  classical
  letI : Nonempty O := payoffNonemptyOfChannel K
  cases subsingleton_or_nontrivial A with
  | inl hsubsingleton =>
      letI : Subsingleton A := hsubsingleton
      exact normalizedMarkedUtility_eq_traceTemperedValue_of_subsingleton
        F h q hq K
  | inr hnontrivial =>
      letI : Nontrivial A := hnontrivial
      have hseq := normalizedMarkedUtility_sequentializedChannel
        F h q hq K
      have hprofile := normalizedMarkedUtility_payoffBranchFormula
        F h hpositive q hq K (fun y : O × R ↦ y.1)
      change
        normalizedMarkedUtility F h q hq
            (markedExperimentOfChannel K) =
          traceTemperedValue (materialPayoffUtility F h)
            (globalTraceLambda F h) q K
      calc
        normalizedMarkedUtility F h q hq
            (markedExperimentOfChannel K) =
            normalizedMarkedUtility F h q hq
              (markedExperimentOfChannel (sequentializedChannel K)) := hseq
        _ = normalizedMarkedUtility F h q hq
              (payoffBranchExperiment K (fun y : O × R ↦ y.1)) := by
            rfl
        _ = traceTemperedValue (materialPayoffUtility F h)
              (globalTraceLambda F h) q
                (payoffBranchCompound K (fun y : O × R ↦ y.1)) := hprofile
        _ = traceTemperedValue (materialPayoffUtility F h)
              (globalTraceLambda F h) q K := by
            change traceTemperedValue (materialPayoffUtility F h)
                (globalTraceLambda F h) q (sequentializedChannel K) =
              traceTemperedValue (materialPayoffUtility F h)
                (globalTraceLambda F h) q K
            unfold traceTemperedValue
            rw [expectedPayoffUtility_sequentializedChannel,
              mutualInfo_sequentializedChannel]

end TraceableAgency.Theorem1
