/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.NormalizedMarked
import Theorem1Verification.PayoffBranches

/-!
# Background independence for deterministic-payoff branch changes

Affinity of the marked-terminal representative makes the value difference
created by changing one terminal payoff independent of the payoffs assigned
to all other branches.  The proof uses the exact crossed-mixture identity:
at probability one half, swapping the changed branch between two backgrounds
does not change the aggregate marked terminal law.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Replace the payoff attached to one branch. -/
def updateBranchPayoff
    (payoff : Y → O) (target : Y) (o : O) : Y → O :=
  fun y ↦ if y = target then o else payoff y

@[simp]
theorem updateBranchPayoff_target
    (payoff : Y → O) (target : Y) (o : O) :
    updateBranchPayoff payoff target o target = o := by
  simp [updateBranchPayoff]

@[simp]
theorem updateBranchPayoff_of_ne
    (payoff : Y → O) (target : Y) (o : O)
    (y : Y) (hy : y ≠ target) :
    updateBranchPayoff payoff target o y = payoff y := by
  simp [updateBranchPayoff, hy]

/-- Marked integration of a deterministic, uninformative terminal payoff. -/
theorem markedChannelIntegral_uninformativeAtPayoff
    (r : TraceableAgency.Dist A) (o : O)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral r (uninformativeAtPayoff (A := A) o) phi =
      phi (o, r) := by
  classical
  unfold markedChannelIntegral
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  rw [Finset.sum_eq_single o]
  · have hmarg : Channel.outcomeMarginal
        (uninformativeAtPayoff (A := A) o) r (o, PUnit.unit) = 1 := by
      rw [outcomeMarginal_uninformativeAtPayoff]
      simp
    have hpost : Channel.posterior
        (uninformativeAtPayoff (A := A) o) r (o, PUnit.unit) = r := by
      have hp : 0 < Channel.outcomeMarginal
          (uninformativeAtPayoff (A := A) o) r (o, PUnit.unit) := by
        rw [hmarg]
        norm_num
      apply TraceableAgency.Dist.ext
      intro a
      unfold Channel.posterior
      rw [dif_pos hp]
      simp [uninformativeAtPayoff, Channel.outcomeMarginal_apply,
        ← Finset.sum_mul, r.sum_eq_one]
    rw [hmarg, hpost, one_mul]
  · intro o' _ho' hne
    rw [outcomeMarginal_uninformativeAtPayoff]
    simp [hne]
  · simp

/-- Crossed one-half public mixtures have exactly the same marked terminal
law.  This is the finite-law form of cancellation of all other branches. -/
theorem sameMarkedTerminalLaw_crossedPayoffBackgrounds
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o o0 : O) (payoff payoff' : Y → O) :
    SameMarkedTerminalLaw q
      (markedPublicMixExperiment (1 / 2 : ℝ) (by norm_num) (by norm_num)
        (payoffBranchExperiment P (updateBranchPayoff payoff target o))
        (payoffBranchExperiment P (updateBranchPayoff payoff' target o0)))
      (markedPublicMixExperiment (1 / 2 : ℝ) (by norm_num) (by norm_num)
        (payoffBranchExperiment P (updateBranchPayoff payoff target o0))
        (payoffBranchExperiment P (updateBranchPayoff payoff' target o))) := by
  classical
  intro phi
  rw [markedTerminalIntegral_publicMix,
    markedTerminalIntegral_publicMix]
  change
    (1 / 2 : ℝ) * markedChannelIntegral q
        (payoffBranchCompound P (updateBranchPayoff payoff target o)) phi +
      (1 - (1 / 2 : ℝ)) * markedChannelIntegral q
        (payoffBranchCompound P (updateBranchPayoff payoff' target o0)) phi =
    (1 / 2 : ℝ) * markedChannelIntegral q
        (payoffBranchCompound P (updateBranchPayoff payoff target o0)) phi +
      (1 - (1 / 2 : ℝ)) * markedChannelIntegral q
        (payoffBranchCompound P (updateBranchPayoff payoff' target o)) phi
  simp only [payoffBranchCompound]
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound]
  have hhalf : (1 - (1 / 2 : ℝ)) = 1 / 2 := by norm_num
  rw [hhalf]
  rw [Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hy : y = target
  · subst y
    simp only [payoffBranchContinuation, updateBranchPayoff_target]
    ring
  · simp only [payoffBranchContinuation,
      updateBranchPayoff_of_ne _ _ _ _ hy]

/-- Changing the payoff at one branch has a normalized-value effect that is
independent of the payoff profile in every other branch. -/
theorem normalizedMarkedUtility_branchPayoff_difference_background_independent
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (o o0 : O)
    (payoff payoff' : Y → O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (updateBranchPayoff payoff target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (updateBranchPayoff payoff target o0)) =
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (updateBranchPayoff payoff' target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (updateBranchPayoff payoff' target o0)) := by
  let ht0 : (0 : ℝ) < 1 / 2 := by norm_num
  let ht1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hsame := sameMarkedTerminalLaw_crossedPayoffBackgrounds
    q P target o o0 payoff payoff'
  have hvalue := normalizedMarkedUtility_respects_sameMarkedTerminalLaw
    F h q hq _ _ hsame
  rw [normalizedMarkedUtility_publicMix,
    normalizedMarkedUtility_publicMix] at hvalue
  norm_num at hvalue ⊢
  linarith

end TraceTemperedChoiceVerification
