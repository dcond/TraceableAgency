/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TraceableAgency.Theorem1.MaterialCalibration.FullRevelation
import TraceableAgency.Theorem1.MaterialCalibration.Relabeling
import TraceableAgency.Theorem1.MaterialCalibration.MarkedBranchDirections

/-!
# Material increments at fully revealing experiments

The unit at a pure posterior is calibrated using payoff changes while keeping
the action record. Uniform-prior symmetry and a reached uniform posterior
transport the same unit to each action under an arbitrary full-support prior.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Change the payoff at one fully revealed action from the low material
anchor to the high material anchor. -/
noncomputable def revealUpgrade
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (a : A) : ℝ :=
  normalizedMarkedUtility F h q hq
      (fullRevealWithPayoffExperiment
        (Function.update (fun _ : A ↦ materialLowOutcome F h) a
          (materialHighOutcome F h))) -
    normalizedMarkedUtility F h q hq
      (fullRevealWithPayoffExperiment (fun _ : A ↦ materialLowOutcome F h))

theorem fullRevealWithPayoff_actionRecordEquiv
    (e : A ≃ A) (g : A → O) :
    Relabeling.relabelChannel e (Equiv.prodCongr (Equiv.refl O) e)
        (fullRevealWithPayoff g) =
      fullRevealWithPayoff (fun a ↦ g (e.symm a)) := by
  ext a z
  rcases z with ⟨o, b⟩
  simp [Relabeling.relabelChannel, Relabeling.relabelDist,
    fullRevealWithPayoff, Dist.pure_apply, e.symm.injective.eq_iff]

theorem revealUpgrade_uniform_eq
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (a b : A) :
    revealUpgrade F h Dist.uniform Dist.uniform_fullSupport a =
      revealUpgrade F h Dist.uniform Dist.uniform_fullSupport b := by
  classical
  let e : A ≃ A := Equiv.swap a b
  let g : A → O := Function.update (fun _ ↦ materialLowOutcome F h) a
    (materialHighOutcome F h)
  have hg : (fun x ↦ g (e.symm x)) =
      Function.update (fun _ : A ↦ materialLowOutcome F h) b
        (materialHighOutcome F h) := by
    funext x
    simp [g, e, Function.update, Equiv.swap_apply_eq_iff]
  have hv := normalizedMarkedUtility_actionRecordEquiv F h e e
    (Dist.uniform (A := A)) Dist.uniform_fullSupport (fullRevealWithPayoff g)
  have hv' : normalizedMarkedUtility F h Dist.uniform Dist.uniform_fullSupport
      (fullRevealWithPayoffExperiment
        (Function.update (fun _ : A ↦ materialLowOutcome F h) b
          (materialHighOutcome F h))) =
      normalizedMarkedUtility F h Dist.uniform Dist.uniform_fullSupport
        (fullRevealWithPayoffExperiment g) := by
    simpa only [fullRevealWithPayoff_actionRecordEquiv, hg,
      materialCalibration_relabelDist_uniform, fullRevealWithPayoffExperiment] using hv
  unfold revealUpgrade
  exact congrArg (fun x ↦ x - normalizedMarkedUtility F h Dist.uniform
    Dist.uniform_fullSupport
      (fullRevealWithPayoffExperiment (fun _ : A ↦ materialLowOutcome F h))) hv'.symm

/-- Revealed-action upgrades have the same value per unit of prior mass.
A reached uniform posterior supplies a common affine comparison; all remaining
steps compare scaled marked-law differences at the fixed outer prior. -/
theorem revealUpgrade_cross_mul
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (a b : A) :
    q b * revealUpgrade F h q hq a =
      q a * revealUpgrade F h q hq b := by
  classical
  let r : Dist A := Dist.uniform
  have hr : r.FullSupport := Dist.uniform_fullSupport
  obtain ⟨eps, heps, hdom⟩ := exists_positive_branch_mass_dominated q r hq hr
  let P := binaryReachChannel q r eps (le_of_lt heps) hdom
  let target : ULift.{u} Bool := ULift.up true
  have hm : Channel.outcomeMarginal P q target = eps :=
    outcomeMarginal_binaryReachChannel_true q r eps (le_of_lt heps) hdom
  have hp : BranchPositive P q target := by
    change 0 < Channel.outcomeMarginal P q target
    rw [hm]
    exact heps
  have hpost : branchPosterior P q target = r :=
    branchPosterior_binaryReachChannel_true q r eps heps hdom
  have hpr : (branchPosterior P q target).FullSupport := by
    simpa only [hpost] using hr
  let low := materialLowOutcome F h
  let high := materialHighOutcome F h
  let slope := branchInsertionAffineSlope F h q hq P target hp hpr low
  have hscaled (x : A) :
      (eps * r x) * revealUpgrade F h q hq x =
        q x * (slope * revealUpgrade F h r hr x) := by
    let E := fullRevealWithPayoffExperiment (Function.update (fun _ : A ↦ low) x high)
    let G := fullRevealWithPayoffExperiment (fun _ : A ↦ low)
    have hdir (s : Dist A) (phi : O × Dist A → ℝ) :
        markedTerminalIntegral s E phi - markedTerminalIntegral s G phi =
          s x * (phi (high, Dist.pure x) - phi (low, Dist.pure x)) := by
      exact markedChannelIntegral_fullRevealWithPayoff_update_sub
        (fun _ ↦ low) s x high phi
    have hnum := normalizedMarkedUtility_scaled_difference F h q hq
      (eps * r x) (q x) (mul_pos heps (hr x)) (hq x)
      E G (branchInsertionExperiment P target low E)
        (branchInsertionExperiment P target low G) (by
          intro phi
          rw [hdir, markedTerminalIntegral_branchInsertion_difference,
            hm, hpost, hdir]
          ring)
    have hinsert :
        normalizedMarkedUtility F h q hq (branchInsertionExperiment P target low E) -
          normalizedMarkedUtility F h q hq (branchInsertionExperiment P target low G) =
          slope * revealUpgrade F h r hr x := by
      rw [normalizedMarkedUtility_branchInsertion F h q hq P target hp hpr,
        normalizedMarkedUtility_branchInsertion F h q hq P target hp hpr]
      simp only [hpost]
      change slope * normalizedMarkedUtility F h r hr E + _ -
        (slope * normalizedMarkedUtility F h r hr G + _) =
        slope * (normalizedMarkedUtility F h r hr E -
          normalizedMarkedUtility F h r hr G)
      ring
    rw [hinsert] at hnum
    exact hnum
  have ha := hscaled a
  have hb := hscaled b
  have hrab : r b = r a := rfl
  have huab : revealUpgrade F h r hr b = revealUpgrade F h r hr a :=
    revealUpgrade_uniform_eq F h b a
  rw [hrab, huab] at hb
  apply mul_left_cancel₀ (ne_of_gt (mul_pos heps (hr a)))
  calc
    (eps * r a) * (q b * revealUpgrade F h q hq a) =
        q b * ((eps * r a) * revealUpgrade F h q hq a) := by ring
    _ = q b * (q a * (slope * revealUpgrade F h r hr a)) := by rw [ha]
    _ = q a * (q b * (slope * revealUpgrade F h r hr a)) := by ring
    _ = q a * ((eps * r a) * revealUpgrade F h q hq b) := by rw [hb]
    _ = (eps * r a) * (q a * revealUpgrade F h q hq b) := by ring

/-- The common material unit attached to fully revealing action posteriors. -/
noncomputable def revealMaterialUnit
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) : ℝ :=
  ∑ a, revealUpgrade F h q hq a

/-- Every individual revealed-action upgrade has its prior probability as
weight, times a single as-yet-unidentified unit for that prior. -/
theorem revealUpgrade_eq_probability_mul_unit
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (a : A) :
    revealUpgrade F h q hq a = q a * revealMaterialUnit F h q hq := by
  calc
    revealUpgrade F h q hq a =
        (∑ b, q b) * revealUpgrade F h q hq a := by rw [q.sum_eq_one, one_mul]
    _ = ∑ b, q b * revealUpgrade F h q hq a := Finset.sum_mul _ _ _
    _ = ∑ b, q a * revealUpgrade F h q hq b := by
      apply Finset.sum_congr rfl
      intro b _
      exact revealUpgrade_cross_mul F h q hq a b
    _ = q a * revealMaterialUnit F h q hq := by
      rw [revealMaterialUnit, Finset.mul_sum]

end TraceableAgency.Theorem1.MaterialCalibration
