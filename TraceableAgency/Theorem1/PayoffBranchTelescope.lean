/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PayoffBranchBackground

/-!
# Finite aggregation of deterministic-payoff branch changes

Background independence makes the normalized-value increments from changing
distinct terminal branches add.  This file isolates the finite telescoping
argument: a formula for each one-branch change from a constant baseline is
enough to obtain the formula for an arbitrary deterministic-payoff profile.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- The payoff profile obtained by changing precisely the branches in `s`
away from the constant baseline `o0`. -/
def partialPayoffProfile
    (o0 : O) (payoff : Y → O) (s : Finset Y) : Y → O :=
  fun y ↦ if y ∈ s then payoff y else o0

@[simp]
theorem partialPayoffProfile_empty
    (o0 : O) (payoff : Y → O) :
    partialPayoffProfile o0 payoff ∅ = fun _ ↦ o0 := by
  funext y
  simp [partialPayoffProfile]

@[simp]
theorem partialPayoffProfile_univ
    (o0 : O) (payoff : Y → O) :
    partialPayoffProfile o0 payoff Finset.univ = payoff := by
  funext y
  simp [partialPayoffProfile]

theorem partialPayoffProfile_insert
    (o0 : O) (payoff : Y → O) (s : Finset Y) (target : Y)
    (htarget : target ∉ s) :
    partialPayoffProfile o0 payoff (insert target s) =
      updateBranchPayoff (partialPayoffProfile o0 payoff s)
        target (payoff target) := by
  funext y
  by_cases hy : y = target
  · subst y
    simp [partialPayoffProfile]
  · simp [partialPayoffProfile, updateBranchPayoff, hy]

theorem updateBranchPayoff_partial_baseline
    (o0 : O) (payoff : Y → O) (s : Finset Y) (target : Y)
    (htarget : target ∉ s) :
    updateBranchPayoff (partialPayoffProfile o0 payoff s) target o0 =
      partialPayoffProfile o0 payoff s := by
  funext y
  by_cases hy : y = target
  · subst y
    simp [partialPayoffProfile, htarget]
  · simp [updateBranchPayoff, hy]

/-- Finite branch telescoping for the normalized marked utility.  The
hypothesis supplies the increment from changing each branch away from a
constant baseline.  The conclusion aggregates those increments for the full
payoff profile. -/
theorem normalizedMarkedUtility_payoffBranch_telescope
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (o0 : O) (payoff : Y → O)
    (increment : Y → ℝ)
    (hsingle : ∀ target : Y,
      normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (updateBranchPayoff (fun _ ↦ o0) target (payoff target))) -
        normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P (fun _ ↦ o0)) =
        increment target) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P payoff) =
      normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P (fun _ ↦ o0)) +
        ∑ target : Y, increment target := by
  let V : (Y → O) → ℝ := fun profile ↦
    normalizedMarkedUtility F h q hq
      (payoffBranchExperiment P profile)
  have hs : ∀ s : Finset Y,
      V (partialPayoffProfile o0 payoff s) =
        V (fun _ ↦ o0) + ∑ target ∈ s, increment target := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        simp [V]
    | @insert target s htarget ih =>
        have hbackground :=
          normalizedMarkedUtility_branchPayoff_difference_background_independent
            F h q hq P target (payoff target) o0
              (partialPayoffProfile o0 payoff s) (fun _ ↦ o0)
        change
          V (updateBranchPayoff (partialPayoffProfile o0 payoff s)
                target (payoff target)) -
              V (updateBranchPayoff (partialPayoffProfile o0 payoff s)
                target o0) =
            V (updateBranchPayoff (fun _ ↦ o0)
                target (payoff target)) -
              V (updateBranchPayoff (fun _ ↦ o0) target o0) at hbackground
        have hbaseUpdate :
            updateBranchPayoff (fun _ : Y ↦ o0) target o0 =
              (fun _ ↦ o0) := by
          funext y
          by_cases hy : y = target
          · subst y
            simp
          · simp [updateBranchPayoff, hy]
        rw [updateBranchPayoff_partial_baseline o0 payoff s target htarget,
          hbaseUpdate] at hbackground
        rw [partialPayoffProfile_insert o0 payoff s target htarget,
          Finset.sum_insert htarget]
        change
          V (updateBranchPayoff (partialPayoffProfile o0 payoff s)
              target (payoff target)) =
            V (fun _ ↦ o0) +
              (increment target + ∑ x ∈ s, increment x)
        have hsingle' := hsingle target
        change
          V (updateBranchPayoff (fun _ ↦ o0)
                target (payoff target)) - V (fun _ ↦ o0) =
            increment target at hsingle'
        linarith
  simpa [V] using hs Finset.univ

/-- Expected-utility-shaped specialization relative to a possibly nonzero
baseline payoff. -/
theorem normalizedMarkedUtility_payoffBranch_sum
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (o0 : O) (payoff : Y → O) (u : O → ℝ)
    (hsingle : ∀ target : Y,
      normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (updateBranchPayoff (fun _ ↦ o0) target (payoff target))) -
        normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P (fun _ ↦ o0)) =
        Channel.outcomeMarginal P q target *
          (u (payoff target) - u o0)) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P payoff) =
        normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P (fun _ ↦ o0)) +
        ∑ target : Y,
          Channel.outcomeMarginal P q target *
            (u (payoff target) - u o0) := by
  exact normalizedMarkedUtility_payoffBranch_telescope
    F h q hq P o0 payoff
      (fun target ↦ Channel.outcomeMarginal P q target *
        (u (payoff target) - u o0))
      hsingle

end TraceableAgency.Theorem1
