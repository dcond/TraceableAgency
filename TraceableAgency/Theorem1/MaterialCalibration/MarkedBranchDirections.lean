/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MaterialCalibration.MarkedDirections
import TraceableAgency.Theorem1.SupportBranchInsertion
import TraceableAgency.Theorem1.PayoffBranchBackground

/-!
# Exact marked-law differences on a branch

Changing one continuation changes the marked terminal law by the branch mass
times the local change.  These identities concern finite laws alone.  Combined
with affine marked values, they provide pre-entropy comparisons between the
numerical effects of reaching the same posterior in different ways.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y Z : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]
variable [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- Replacing the distinguished continuation changes marked integration by
exactly the reached mass times the local marked-integral difference. -/
theorem markedTerminalIntegral_branchInsertion_difference
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (E G : MarkedTerminalExperiment O A)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q (branchInsertionExperiment P target o0 E) phi -
        markedTerminalIntegral q (branchInsertionExperiment P target o0 G) phi =
      Channel.outcomeMarginal P q target *
        (markedTerminalIntegral (branchPosterior P q target) E phi -
          markedTerminalIntegral (branchPosterior P q target) G phi) := by
  classical
  change
    markedChannelIntegral q
        (commonPayoffCompound (branchInsertionRecord target E) P
          (branchInsertionContinuation target o0 E)) phi -
      markedChannelIntegral q
        (commonPayoffCompound (branchInsertionRecord target G) P
          (branchInsertionContinuation target o0 G)) phi = _
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single target]
  · rw [markedChannelIntegral_branchInsertionContinuation_target,
      markedChannelIntegral_branchInsertionContinuation_target]
    simp only [branchPosterior]
    ring
  · intro y _hy hyt
    rw [markedChannelIntegral_branchInsertionContinuation_of_ne _ _ _ _ _ hyt,
      markedChannelIntegral_branchInsertionContinuation_of_ne _ _ _ _ _ hyt]
    ring
  · simp

/-- The same identity for a continuation defined only on the reached
posterior's support.  The local posterior is included back into the ambient
action alphabet inside the test function. -/
theorem markedTerminalIntegral_supportBranchInsertion_difference
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O)
    (E G : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target)))
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q
        (supportBranchInsertionExperiment q P target o0 E) phi -
      markedTerminalIntegral q
        (supportBranchInsertionExperiment q P target o0 G) phi =
      Channel.outcomeMarginal P q target *
        (markedTerminalIntegral (branchPosterior P q target).restrictToSupport E
            (fun op ↦ phi (op.1,
              supportPushforwardPosterior (branchPosterior P q target) op.2)) -
          markedTerminalIntegral (branchPosterior P q target).restrictToSupport G
            (fun op ↦ phi (op.1,
              supportPushforwardPosterior (branchPosterior P q target) op.2))) := by
  rw [supportBranchInsertionExperiment, supportBranchInsertionExperiment,
    markedTerminalIntegral_branchInsertion_difference,
    markedTerminalIntegral_supportExtend, markedTerminalIntegral_supportExtend]

/-- A deterministic payoff change on one branch is the atom difference at
that branch's posterior, multiplied by its probability.  Other branch payoffs
cancel without any behavioural assumption. -/
theorem markedTerminalIntegral_payoffBranch_update_difference
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o o0 : O) (payoff : Y → O)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q
        (payoffBranchExperiment P (updateBranchPayoff payoff target o)) phi -
      markedTerminalIntegral q
        (payoffBranchExperiment P (updateBranchPayoff payoff target o0)) phi =
      Channel.outcomeMarginal P q target *
        (phi (o, branchPosterior P q target) -
          phi (o0, branchPosterior P q target)) := by
  classical
  change
    markedChannelIntegral q
        (payoffBranchCompound P (updateBranchPayoff payoff target o)) phi -
      markedChannelIntegral q
        (payoffBranchCompound P (updateBranchPayoff payoff target o0)) phi = _
  simp only [payoffBranchCompound]
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single target]
  · simp only [payoffBranchContinuation, updateBranchPayoff_target,
      markedChannelIntegral_uninformativeAtPayoff, branchPosterior]
    ring
  · intro y _hy hyt
    simp only [payoffBranchContinuation,
      updateBranchPayoff_of_ne _ _ _ _ hyt, sub_self]
  · simp

/-- At a fixed prior, two branches with the same posterior give proportional
payoff-change values, with the proportions equal to their reached masses.
This is path independence of the material direction before entropy is known. -/
theorem normalizedMarkedUtility_payoffBranch_samePosterior_scaled_difference
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (Q : Channel A Z)
    (target : Y) (other : Z)
    (htarget : BranchPositive P q target)
    (hother : BranchPositive Q q other)
    (hposterior : branchPosterior P q target = branchPosterior Q q other)
    (o o0 : O) (payoff : Y → O) (payoff' : Z → O) :
    Channel.outcomeMarginal Q q other *
        (normalizedMarkedUtility F h q hq
            (payoffBranchExperiment P (updateBranchPayoff payoff target o)) -
          normalizedMarkedUtility F h q hq
            (payoffBranchExperiment P (updateBranchPayoff payoff target o0))) =
      Channel.outcomeMarginal P q target *
        (normalizedMarkedUtility F h q hq
            (payoffBranchExperiment Q (updateBranchPayoff payoff' other o)) -
          normalizedMarkedUtility F h q hq
            (payoffBranchExperiment Q (updateBranchPayoff payoff' other o0))) := by
  apply normalizedMarkedUtility_scaled_difference F h q hq
    (Channel.outcomeMarginal Q q other)
    (Channel.outcomeMarginal P q target) hother htarget
  intro phi
  rw [markedTerminalIntegral_payoffBranch_update_difference,
    markedTerminalIntegral_payoffBranch_update_difference, hposterior]
  ring

end TraceableAgency.Theorem1
