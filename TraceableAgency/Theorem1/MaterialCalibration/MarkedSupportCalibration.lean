/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MaterialCalibration.MarkedInsertionCalibration

/-!
# Material calibration on reached support faces

The material-direction comparison works without assuming a full-support branch
posterior in the ambient action alphabet.  Local full revelation is performed
on its positive support and its pure posterior is included into the ambient
simplex.  Singleton supports are covered by the same proof.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Inserting a local full-revelation payoff upgrade changes only the marked
atom at the corresponding ambient pure action. -/
theorem markedTerminalIntegral_supportInsertion_revealPayoff_difference
    (q : TraceableAgency.Dist A) (P : Channel A Y) (target : Y)
    (background o0 o : O)
    (a : supportSubtype (branchPosterior P q target))
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q
        (supportBranchInsertionExperiment q P target background
          (markedRevealPayoffExperiment o0 o a)) phi -
      markedTerminalIntegral q
        (supportBranchInsertionExperiment q P target background
          (markedRevealPayoffExperiment o0 o0 a)) phi =
      Channel.outcomeMarginal P q target *
        (branchPosterior P q target).restrictToSupport a *
        (phi (o, TraceableAgency.Dist.pure a.1) -
          phi (o0, TraceableAgency.Dist.pure a.1)) := by
  rw [markedTerminalIntegral_supportBranchInsertion_difference,
    markedTerminalIntegral_revealPayoff_difference
      (branchPosterior P q target).restrictToSupport a
      (TraceableAgency.Dist.restrictToSupport_fullSupport
        (branchPosterior P q target) a)]
  simp only [supportPushforwardPosterior_pure_materialCalibration]
  ring

/-- A support-face insertion slope is the reached mass times the ratio of
ambient and local material full-revelation units.  The division-free formula
also states exactly which cancellation is needed once the local unit is
known to be positive.  There is no nontrivial-support restriction. -/
theorem supportBranchInsertionScale_mul_materialUnit
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (background o0 o : O)
    (a : supportSubtype (branchPosterior P q target)) (aq ar : ℝ)
    (houter :
      normalizedMarkedUtility F h q hq (markedRevealPayoffExperiment o0 o a.1) -
        normalizedMarkedUtility F h q hq (markedRevealPayoffExperiment o0 o0 a.1) =
        q a.1 * aq)
    (hlocal :
      normalizedMarkedUtility F h
          (branchPosterior P q target).restrictToSupport
          (TraceableAgency.Dist.restrictToSupport_fullSupport
            (branchPosterior P q target))
          (markedRevealPayoffExperiment o0 o a) -
        normalizedMarkedUtility F h
          (branchPosterior P q target).restrictToSupport
          (TraceableAgency.Dist.restrictToSupport_fullSupport
            (branchPosterior P q target))
          (markedRevealPayoffExperiment o0 o0 a) =
        (branchPosterior P q target).restrictToSupport a * ar) :
    supportBranchInsertionScale F h q hq P target htarget background * ar =
      Channel.outcomeMarginal P q target * aq := by
  let r := branchPosterior P q target
  let rs := r.restrictToSupport
  let hrs := TraceableAgency.Dist.restrictToSupport_fullSupport r
  let m := Channel.outcomeMarginal P q target
  let E := markedRevealPayoffExperiment o0 o a
  let E0 := markedRevealPayoffExperiment o0 o0 a
  let G := markedRevealPayoffExperiment o0 o a.1
  let G0 := markedRevealPayoffExperiment o0 o0 a.1
  have hm : 0 < m := htarget
  have hra : 0 < rs a := hrs a
  have hscaled := normalizedMarkedUtility_scaled_difference F h q hq
    (q a.1) (m * rs a) (hq a.1) (mul_pos hm hra)
    (supportBranchInsertionExperiment q P target background E)
    (supportBranchInsertionExperiment q P target background E0) G G0 (by
      intro phi
      rw [markedTerminalIntegral_supportInsertion_revealPayoff_difference,
        markedTerminalIntegral_revealPayoff_difference q a.1 (hq a.1)]
      change q a.1 * (m * rs a * _) = (m * rs a) * (q a.1 * _)
      ring)
  have hinsert :
      normalizedMarkedUtility F h q hq
          (supportBranchInsertionExperiment q P target background E) -
        normalizedMarkedUtility F h q hq
          (supportBranchInsertionExperiment q P target background E0) =
      supportBranchInsertionScale F h q hq P target htarget background * (rs a * ar) := by
    rw [normalizedMarkedUtility_supportBranchInsertion F h q hq P target htarget background E,
      normalizedMarkedUtility_supportBranchInsertion F h q hq P target htarget background E0]
    calc
      _ = supportBranchInsertionScale F h q hq P target htarget background *
          (normalizedMarkedUtility F h rs hrs E -
            normalizedMarkedUtility F h rs hrs E0) := by ring
      _ = _ := by rw [hlocal]
  rw [hinsert, houter] at hscaled
  apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt (hq a.1)) (ne_of_gt hra))
  calc
    (q a.1 * rs a) *
        (supportBranchInsertionScale F h q hq P target htarget background * ar) =
      q a.1 * (supportBranchInsertionScale F h q hq P target htarget background *
        (rs a * ar)) := by ring
    _ = (m * rs a) * (q a.1 * aq) := hscaled
    _ = (q a.1 * rs a) * (Channel.outcomeMarginal P q target * aq) := by
      change (m * rs a) * (q a.1 * aq) = (q a.1 * rs a) * (m * aq)
      ring

end TraceableAgency.Theorem1
