/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TraceableAgency.Theorem1.MarkedHM
import TraceableAgency.Theorem1.MarkedTransport

/-!
# Full revelation with an action-dependent material payoff

These are finite channel and marked-law identities.  No information-value
representation or trace-scale calibration is used.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A]

/-- Reveal the realized action and pay the deterministic payoff attached to it. -/
noncomputable def fullRevealWithPayoff (g : A → O) : Channel A (O × A) :=
  fun a ↦ Dist.pure (g a, a)

@[simp]
theorem fullRevealWithPayoff_const (o : O) :
    fullRevealWithPayoff (fun _ : A ↦ o) = fullRevealAtPayoff o := rfl

/-- The probability of a payoff-record pair in the fully revealing experiment. -/
theorem fullRevealWithPayoff_outcomeMarginal
    (g : A → O) (q : Dist A) (o : O) (a : A) :
    Channel.outcomeMarginal (fullRevealWithPayoff g) q (o, a) =
      if o = g a then q a else 0 := by
  classical
  rw [Channel.outcomeMarginal_apply, Finset.sum_eq_single a]
  · simp [fullRevealWithPayoff, Dist.pure_apply]
  · intro b _hb hne
    have hab : a ≠ b := Ne.symm hne
    simp [fullRevealWithPayoff, hab]
  · simp

variable [Nonempty A]

/-- At a reached revealed action, the posterior is the corresponding point mass. -/
theorem fullRevealWithPayoff_posterior_of_pos
    (g : A → O) (q : Dist A) (a : A) (ha : 0 < q a) :
    Channel.posterior (fullRevealWithPayoff g) q (g a, a) = Dist.pure a := by
  classical
  have hm : Channel.outcomeMarginal (fullRevealWithPayoff g) q (g a, a) = q a := by
    rw [fullRevealWithPayoff_outcomeMarginal, if_pos rfl]
  have hmpos : 0 < Channel.outcomeMarginal (fullRevealWithPayoff g) q (g a, a) := by
    rw [hm]
    exact ha
  unfold Channel.posterior
  rw [dif_pos hmpos]
  apply Dist.ext
  intro b
  change q b * (fullRevealWithPayoff g b) (g a, a) /
      Channel.outcomeMarginal (fullRevealWithPayoff g) q (g a, a) =
    Dist.pure a b
  rw [hm]
  by_cases hb : b = a
  · subst b
    simp [fullRevealWithPayoff, ne_of_gt ha]
  · have hab : a ≠ b := Ne.symm hb
    simp [fullRevealWithPayoff, hb, hab]

/-- The joint law of material payoffs and action posteriors under full revelation.
The formula holds for boundary priors as well: null records contribute zero. -/
theorem markedChannelIntegral_fullRevealWithPayoff
    (g : A → O) (q : Dist A) (phi : O × Dist A → ℝ) :
    markedChannelIntegral q (fullRevealWithPayoff g) phi =
      ∑ a, q a * phi (g a, Dist.pure a) := by
  classical
  unfold markedChannelIntegral
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_eq_single (g a)]
  · by_cases hqa : 0 < q a
    · rw [fullRevealWithPayoff_outcomeMarginal, if_pos rfl,
        fullRevealWithPayoff_posterior_of_pos g q a hqa]
    · have hzero : q a = 0 := le_antisymm (le_of_not_gt hqa) (q.nonneg a)
      rw [fullRevealWithPayoff_outcomeMarginal, if_pos rfl, hzero]
      simp
  · intro o _ho hne
    rw [fullRevealWithPayoff_outcomeMarginal, if_neg hne, zero_mul]
  · simp

/-- Changing the material payoff at one revealed action changes the marked
law only by that action's prior mass times the corresponding payoff direction. -/
theorem markedChannelIntegral_fullRevealWithPayoff_update_sub
    (g : A → O) (q : Dist A) (a : A) (o : O)
    (phi : O × Dist A → ℝ) :
    markedChannelIntegral q (fullRevealWithPayoff (Function.update g a o)) phi -
        markedChannelIntegral q (fullRevealWithPayoff g) phi =
      q a * (phi (o, Dist.pure a) - phi (g a, Dist.pure a)) := by
  classical
  rw [markedChannelIntegral_fullRevealWithPayoff,
    markedChannelIntegral_fullRevealWithPayoff, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single a]
  · simp [← mul_sub]
  · intro b _hb hne
    rw [Function.update_of_ne hne, sub_self]
  · simp

/-- Full revelation with a payoff profile, packaged as a marked experiment. -/
noncomputable def fullRevealWithPayoffExperiment
    (g : A → O) : MarkedTerminalExperiment O A :=
  markedExperimentOfChannel (fullRevealWithPayoff g)

@[simp]
theorem fullRevealWithPayoffExperiment_K (g : A → O) :
    (fullRevealWithPayoffExperiment g).K = fullRevealWithPayoff g := rfl

/-- Bundled-experiment version of the full-revelation marked-law identity. -/
theorem markedTerminalIntegral_fullRevealWithPayoffExperiment
    (g : A → O) (q : Dist A) (phi : O × Dist A → ℝ) :
    markedTerminalIntegral q (fullRevealWithPayoffExperiment g) phi =
      ∑ a, q a * phi (g a, Dist.pure a) := by
  exact markedChannelIntegral_fullRevealWithPayoff g q phi

end TraceableAgency.Theorem1.MaterialCalibration
