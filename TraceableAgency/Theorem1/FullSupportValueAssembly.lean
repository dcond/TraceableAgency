/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PayoffBranchTelescope
import TraceableAgency.Theorem1.ConstantLowGeneral
import TraceableAgency.Theorem1.SingletonActionValue
import TraceableAgency.Theorem1.Sequentialization
import TraceableAgency.Theorem1.RepresentationAssembly

/-!
# Assembly of the normalized value at full-support priors

This file isolates the last numerical calculation.  Its only non-structural
input is the payoff increment from changing one reached deterministic-payoff
branch away from the normalized low outcome.  Zero-mass branches are handled
directly at the level of marked terminal laws; finite telescoping then gives
the value of every deterministic-payoff profile, and A4 sequentialization
reduces an arbitrary payoff-record channel to such a profile.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-! ## The one remaining numerical input -/

/-- At a positive first-stage branch, changing the deterministic terminal
payoff from the normalized low outcome to `o` changes normalized value by the
branch probability times the common material utility of `o`.

The action alphabet is required to be nontrivial because the singleton case
is already covered independently by
`normalizedMarkedUtility_eq_traceTemperedValue_of_subsingleton`. -/
def PositiveBranchPayoffIncrementFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) : Prop :=
  ∀ {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (_htarget : 0 < Channel.outcomeMarginal P q target) (o : O),
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff
            (fun _ ↦ materialLowOutcome F h) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ materialLowOutcome F h)) =
      Channel.outcomeMarginal P q target * materialPayoffUtility F h o

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
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (hpositive : PositiveBranchPayoffIncrementFormula F h)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (o : O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff
            (fun _ ↦ materialLowOutcome F h) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ materialLowOutcome F h)) =
      Channel.outcomeMarginal P q target * materialPayoffUtility F h o := by
  by_cases htarget : 0 < Channel.outcomeMarginal P q target
  · exact hpositive q hq P target htarget o
  · have hzero : Channel.outcomeMarginal P q target = 0 :=
      le_antisymm (le_of_not_gt htarget)
        ((Channel.outcomeMarginal P q).nonneg target)
    have hsame :=
      sameMarkedTerminalLaw_payoffBranch_update_of_zeroMass
        q P target o (materialLowOutcome F h) hzero
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
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (hpositive : PositiveBranchPayoffIncrementFormula F h)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (payoff : Y → O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P payoff) =
      traceTemperedValue (materialPayoffUtility F h)
        (globalTraceLambda F h) q (payoffBranchCompound P payoff) := by
  have htelescope := normalizedMarkedUtility_payoffBranch_sum
    F h q hq P (materialLowOutcome F h) payoff
      (materialPayoffUtility F h)
      (fun target ↦
        payoffBranchIncrementFormula_allBranches
          F h hpositive q hq P target (payoff target))
  have hLow : ∀ (a : A) (o : O)
      (r : (payoffBranchExperiment P
        (fun _ ↦ materialLowOutcome F h)).RecordType),
      o ≠ materialLowOutcome F h →
        (payoffBranchExperiment P
          (fun _ ↦ materialLowOutcome F h)).K a (o, r) = 0 := by
    classical
    intro a o r ho
    simp [payoffBranchExperiment, payoffBranchCompound,
      commonPayoffCompound, Relabeling.relabelChannel,
      Relabeling.relabelDist, compoundPayoffRecordEquiv,
      sigmaPayoffRecordEquiv, seqComposeDep, seqComposeDepProb,
      payoffBranchContinuation, uninformativeAtPayoff, ho]
  have hbaseline :=
    normalizedMarkedUtility_eq_globalTraceLambda_mul_mutualInfo_of_sureLow
      F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ materialLowOutcome F h)) hLow
  change
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ materialLowOutcome F h)) =
      globalTraceLambda F h *
        mutualInfo q
          (payoffBranchCompound P
            (fun _ ↦ materialLowOutcome F h)) at hbaseline
  rw [mutualInfo_payoffBranchCompound] at hbaseline
  rw [htelescope, hbaseline]
  exact (traceTemperedValue_payoffBranchCompound
    (materialPayoffUtility F h) (globalTraceLambda F h)
      q P payoff).symm

/-! ## Arbitrary full-support channels -/

/-- A channel and its terminal-payoff sequentialization have the same
normalized marked utility. -/
theorem normalizedMarkedUtility_sequentializedChannel
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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
