/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.BranchInsertion
import TraceableAgency.Theorem1.PayoffBranchBackground

/-!
# Branch insertion for a deterministic payoff

Inserting an action-independent degenerate payoff lottery at one branch gives
exactly the same marked terminal law as the corresponding deterministic-payoff
branch profile.  This law-level bridge avoids any dependence on record labels.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- A degenerate payoff lottery inserted at `target` is the corresponding
one-branch deterministic-payoff compound, at the level of the complete marked
terminal law. -/
theorem sameMarkedTerminalLaw_branchInsertion_purePayoff
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 o : O) :
    SameMarkedTerminalLaw q
      (branchInsertionExperiment P target o0
        (markedPayoffLotteryExperiment
          (TraceableAgency.Dist.pure o)))
      (payoffBranchExperiment P
        (updateBranchPayoff (fun _ ↦ o0) target o)) := by
  classical
  intro phi
  change
    markedChannelIntegral q
        (commonPayoffCompound
          (branchInsertionRecord target
            (markedPayoffLotteryExperiment
              (TraceableAgency.Dist.pure o))) P
          (branchInsertionContinuation target o0
            (markedPayoffLotteryExperiment
              (TraceableAgency.Dist.pure o)))) phi =
      markedChannelIntegral q
        (payoffBranchCompound P
          (updateBranchPayoff (fun _ ↦ o0) target o)) phi
  rw [payoffBranchCompound,
    markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyt : y = target
  · subst y
    rw [markedChannelIntegral_branchInsertionContinuation_target,
      markedTerminalIntegral_markedPayoffLottery]
    simp only [payoffBranchContinuation, updateBranchPayoff_target]
    rw [markedChannelIntegral_uninformativeAtPayoff]
    have hpure : payoffLotteryExpected
        (fun x ↦ phi (x, Channel.posterior P q target))
          (TraceableAgency.Dist.pure o) =
        phi (o, Channel.posterior P q target) := by
      unfold payoffLotteryExpected
      rw [Finset.sum_eq_single o]
      · simp
      · intro x _hx hxo
        rw [TraceableAgency.Dist.pure_apply_ne o x hxo]
        simp
      · simp
    rw [hpure]
  · rw [markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt,
      markedChannelIntegral_uninformativeAtPayoff]
    simp only [payoffBranchContinuation,
      updateBranchPayoff_of_ne _ _ _ _ hyt]
    rw [markedChannelIntegral_uninformativeAtPayoff]

/-- Consequently the two concrete experiments receive the same normalized
marked utility on every full-support outer fibre. -/
theorem normalizedMarkedUtility_branchInsertion_purePayoff
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (o0 o : O) :
    normalizedMarkedUtility F h q hq
        (branchInsertionExperiment P target o0
          (markedPayoffLotteryExperiment
            (TraceableAgency.Dist.pure o))) =
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ o0) target o)) := by
  exact normalizedMarkedUtility_respects_sameMarkedTerminalLaw
    F h q hq _ _
      (sameMarkedTerminalLaw_branchInsertion_purePayoff
        q P target o0 o)

end TraceableAgency.Theorem1
