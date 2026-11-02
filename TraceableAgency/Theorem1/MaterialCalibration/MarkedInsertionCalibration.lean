/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MaterialCalibration.MarkedBranchDirections

/-!
# Calibrating insertion by one material direction

Compare a payoff upgrade after full revelation with the same upgrade inserted
into a reached branch.  Their marked-law differences are positive multiples
of the same atom difference.  Affinity therefore identifies the insertion
slope from material full-revelation units, without an information formula.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Full revelation, with an upgrade from `o0` to `o` only at action `a`. -/
noncomputable abbrev markedRevealPayoffExperiment
    (o0 o : O) (a : A) : MarkedTerminalExperiment O A :=
  payoffBranchExperiment (Channel.idChannel : Channel A A)
    (updateBranchPayoff (fun _ ↦ o0) a o)

/-- A reached full-revelation posterior is the revealed pure action.  This
elementary identity is proved here without importing a trace-coherence module. -/
theorem materialCalibration_branchPosterior_idChannel
    (q : TraceableAgency.Dist A) (a : A) (ha : 0 < q a) :
    branchPosterior (Channel.idChannel : Channel A A) q a =
      TraceableAgency.Dist.pure a := by
  change Channel.posterior (Channel.idChannel : Channel A A) q a = _
  ext b
  have hm : (Channel.outcomeMarginal (Channel.idChannel : Channel A A) q) a = q a := by
    rw [outcomeMarginal_idChannel']
  unfold Channel.posterior
  rw [dif_pos (by rw [hm]; exact ha)]
  by_cases hb : b = a
  · subst b
    simp only [Channel.idChannel, TraceableAgency.Dist.pure_apply_self, mul_one]
    rw [hm]
    field_simp [ne_of_gt ha]
  · have hab : a ≠ b := fun hab ↦ hb hab.symm
    simp [Channel.idChannel, TraceableAgency.Dist.pure_apply_ne _ _ hb,
      TraceableAgency.Dist.pure_apply_ne _ _ hab]

/-- A full-revelation payoff upgrade has exactly one marked atom direction. -/
theorem markedTerminalIntegral_revealPayoff_difference
    (q : TraceableAgency.Dist A) (a : A) (ha : 0 < q a)
    (o0 o : O) (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q (markedRevealPayoffExperiment o0 o a) phi -
      markedTerminalIntegral q (markedRevealPayoffExperiment o0 o0 a) phi =
      q a * (phi (o, TraceableAgency.Dist.pure a) -
        phi (o0, TraceableAgency.Dist.pure a)) := by
  rw [markedTerminalIntegral_payoffBranch_update_difference,
    outcomeMarginal_idChannel', materialCalibration_branchPosterior_idChannel q a ha]

/-- Support inclusion sends a pure local posterior to its ambient pure action. -/
@[simp]
theorem supportPushforwardPosterior_pure_materialCalibration
    (r : TraceableAgency.Dist A) (a : supportSubtype r) :
    supportPushforwardPosterior r (TraceableAgency.Dist.pure a) =
      TraceableAgency.Dist.pure a.1 := by
  classical
  ext b
  change (∑ x : supportSubtype r,
    TraceableAgency.Dist.pure a x * TraceableAgency.Dist.pure x.1 b) =
      TraceableAgency.Dist.pure a.1 b
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _hx hxa
    simp [TraceableAgency.Dist.pure_apply, hxa]
  · simp

/-- Material full-revelation units calibrate a full-support insertion slope.
Only the payoff-upgrade formula at one action is needed on each side. -/
theorem branchInsertionAffineSlope_mul_materialUnit
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (background o0 o : O) (a : A) (aq ar : ℝ)
    (houter :
      normalizedMarkedUtility F h q hq (markedRevealPayoffExperiment o0 o a) -
        normalizedMarkedUtility F h q hq (markedRevealPayoffExperiment o0 o0 a) =
        q a * aq)
    (hlocal :
      normalizedMarkedUtility F h (branchPosterior P q target) hr
          (markedRevealPayoffExperiment o0 o a) -
        normalizedMarkedUtility F h (branchPosterior P q target) hr
          (markedRevealPayoffExperiment o0 o0 a) =
        (branchPosterior P q target) a * ar) :
    branchInsertionAffineSlope F h q hq P target htarget hr background * ar =
      Channel.outcomeMarginal P q target * aq := by
  let r := branchPosterior P q target
  let m := Channel.outcomeMarginal P q target
  let E := markedRevealPayoffExperiment o0 o a
  let E0 := markedRevealPayoffExperiment o0 o0 a
  have hm : 0 < m := htarget
  have hra : 0 < r a := hr a
  have hscaled := normalizedMarkedUtility_scaled_difference F h q hq
    (q a) (m * r a) (hq a) (mul_pos hm hra)
    (branchInsertionExperiment P target background E)
    (branchInsertionExperiment P target background E0) E E0 (by
      intro phi
      rw [markedTerminalIntegral_branchInsertion_difference,
        markedTerminalIntegral_revealPayoff_difference r a hra,
        markedTerminalIntegral_revealPayoff_difference q a (hq a)]
      change q a * (m * (r a * _)) = (m * r a) * (q a * _)
      ring)
  have hinsert :
      normalizedMarkedUtility F h q hq
          (branchInsertionExperiment P target background E) -
        normalizedMarkedUtility F h q hq
          (branchInsertionExperiment P target background E0) =
      branchInsertionAffineSlope F h q hq P target htarget hr background * (r a * ar) := by
    rw [normalizedMarkedUtility_branchInsertion F h q hq P target htarget hr background E,
      normalizedMarkedUtility_branchInsertion F h q hq P target htarget hr background E0]
    calc
      _ = branchInsertionAffineSlope F h q hq P target htarget hr background *
          (normalizedMarkedUtility F h r hr E -
            normalizedMarkedUtility F h r hr E0) := by ring
      _ = _ := by rw [hlocal]
  rw [hinsert, houter] at hscaled
  apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt (hq a)) (ne_of_gt hra))
  calc
    (q a * r a) *
        (branchInsertionAffineSlope F h q hq P target htarget hr background * ar) =
      q a * (branchInsertionAffineSlope F h q hq P target htarget hr background *
        (r a * ar)) := by ring
    _ = (m * r a) * (q a * aq) := hscaled
    _ = (q a * r a) * (Channel.outcomeMarginal P q target * aq) := by
      change (m * r a) * (q a * aq) = (q a * r a) * (m * aq)
      ring

end TraceableAgency.Theorem1
