/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TraceableAgency.Theorem1.MaterialCalibration.Units
import TraceableAgency.Theorem1.MaterialCalibration.FullRevelationValue

/-!
# Positivity and the singleton normalization of material units

Both facts use only material relevance and the affine utility normalization.
No formula for information value is used.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Every revealed-action material upgrade is strictly valuable. -/
theorem revealUpgrade_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (a : A) :
    0 < revealUpgrade F h q hq a := by
  exact normalizedMarkedUtility_fullReveal_materialUpgrade_pos F h q hq a

/-- The common material unit at any full-support prior is strictly positive. -/
theorem revealMaterialUnit_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) :
    0 < revealMaterialUnit F h q hq := by
  unfold revealMaterialUnit
  exact Finset.sum_pos (fun a _ha ↦ revealUpgrade_pos F h q hq a)
    Finset.univ_nonempty

/-- A prior on a singleton action type assigns mass one to its action. -/
theorem dist_apply_eq_one_of_subsingleton [Subsingleton A]
    (q : Dist A) (a : A) : q a = 1 := by
  have hsum : (∑ b, q b) = q a := by
    apply Finset.sum_eq_single a
    · intro b _hb hne
      exact False.elim (hne (Subsingleton.elim b a))
    · simp
  exact hsum.symm.trans q.sum_eq_one

/-- There is only one prior on a singleton action type. -/
theorem dist_eq_pure_of_subsingleton [Subsingleton A]
    (q : Dist A) (a : A) : q = Dist.pure a := by
  apply Dist.ext
  intro b
  have hba : b = a := Subsingleton.elim b a
  subst b
  rw [dist_apply_eq_one_of_subsingleton, Dist.pure_apply_self]

/-- On a singleton action type, full revelation with a constant payoff has
exactly the same marked law as that uninformative deterministic payoff. -/
theorem sameMarkedTerminalLaw_fullReveal_const_of_subsingleton
    [Subsingleton A] (q : Dist A) (o : O) :
    SameMarkedTerminalLaw q
      (fullRevealWithPayoffExperiment (fun _ : A ↦ o))
      (markedPayoffLotteryExperiment (Dist.pure o)) := by
  intro phi
  rw [markedTerminalIntegral_fullRevealWithPayoffExperiment,
    markedTerminalIntegral_markedPayoffLottery]
  have hpure : ∀ a : A, Dist.pure a = q :=
    fun a ↦ (dist_eq_pure_of_subsingleton q a).symm
  simp_rw [hpure]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  simp [payoffLotteryExpected, Dist.pure_apply]

/-- The normalized value transports across the preceding singleton identity. -/
theorem normalizedMarkedUtility_fullReveal_const_eq_payoffLottery_of_subsingleton
    [Subsingleton A]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (o : O) :
    normalizedMarkedUtility F h q hq
        (fullRevealWithPayoffExperiment (fun _ : A ↦ o)) =
      normalizedMarkedUtility F h q hq
        (markedPayoffLotteryExperiment (Dist.pure o)) := by
  exact normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _
    (sameMarkedTerminalLaw_fullReveal_const_of_subsingleton q o)

/-- The material unit on a singleton action type is one, because its sole
revealed-action upgrade is exactly the normalized low-to-high payoff change. -/
theorem revealMaterialUnit_eq_one_of_subsingleton
    [Subsingleton A]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) :
    revealMaterialUnit F h q hq = 1 := by
  classical
  let a : A := Classical.arbitrary A
  have hupgrade := revealUpgrade_eq_probability_mul_unit F h q hq a
  rw [dist_apply_eq_one_of_subsingleton, one_mul] at hupgrade
  rw [← hupgrade]
  unfold revealUpgrade
  have hprofile :
      Function.update (fun _ : A ↦ materialLowOutcome F h)
          a (materialHighOutcome F h) =
        (fun _ : A ↦ materialHighOutcome F h) := by
    funext b
    have hba : b = a := Subsingleton.elim b a
    subst b
    simp
  rw [hprofile,
    normalizedMarkedUtility_fullReveal_const_eq_payoffLottery_of_subsingleton,
    normalizedMarkedUtility_fullReveal_const_eq_payoffLottery_of_subsingleton]
  change normalizedMarkedUtility F h q hq (markedMaterialHighExperiment F h) -
      normalizedMarkedUtility F h q hq (markedMaterialLowExperiment F h) = 1
  rw [normalizedMarkedUtility_high, normalizedMarkedUtility_low, sub_zero]

end TraceableAgency.Theorem1.MaterialCalibration
