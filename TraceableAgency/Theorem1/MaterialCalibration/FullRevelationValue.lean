/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TraceableAgency.Theorem1.MaterialCalibration.FullRevelation
import TraceableAgency.Theorem1.PayoffBranchBackground
import TraceableAgency.Theorem1.FiniteBranchExtension

/-!
# Material values of full-revelation payoff profiles

This connects the direct fully revealing channel to the deterministic branch
construction.  It uses only marked-law identities and the normalized affine
representative, without an information-value formula.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- The branch-profile update agrees with the standard function update. -/
theorem updateBranchPayoff_eq_update
    {Y : Type u} [Fintype Y] [DecidableEq Y]
    (g : Y → O) (target : Y) (o : O) :
    updateBranchPayoff g target o = Function.update g target o := by
  funext y
  simp [updateBranchPayoff, Function.update_apply]

/-- The fully revealing first-stage record has marginal equal to the prior. -/
theorem identityChannel_outcomeMarginal (q : Dist A) (a : A) :
    Channel.outcomeMarginal (Channel.idChannel : Channel A A) q a = q a := by
  simp [Channel.outcomeMarginal_apply, Channel.idChannel, Dist.pure_apply,
    mul_ite]

/-- A reached identity-channel record has its pure action as posterior. -/
theorem identityChannel_posterior_of_pos
    (q : Dist A) (a : A) (ha : 0 < q a) :
    Channel.posterior (Channel.idChannel : Channel A A) q a = Dist.pure a := by
  have hm := identityChannel_outcomeMarginal q a
  unfold Channel.posterior
  rw [dif_pos (by rw [hm]; exact ha)]
  apply Dist.ext
  intro b
  change q b * Channel.idChannel b a /
      Channel.outcomeMarginal (Channel.idChannel : Channel A A) q a =
    Dist.pure a b
  rw [hm]
  by_cases hb : b = a
  · subst b
    simp [Channel.idChannel, ne_of_gt ha]
  · have hab : a ≠ b := Ne.symm hb
    simp [Channel.idChannel, hb, hab]

/-- Direct full revelation and identity-stage payoff branches have the same
joint law of material payoff and posterior. -/
theorem sameMarkedTerminalLaw_fullRevealWithPayoff_payoffBranch
    (q : Dist A) (g : A → O) :
    SameMarkedTerminalLaw q (fullRevealWithPayoffExperiment g)
      (payoffBranchExperiment (Channel.idChannel : Channel A A) g) := by
  intro phi
  rw [markedTerminalIntegral_fullRevealWithPayoffExperiment]
  change (∑ a, q a * phi (g a, Dist.pure a)) =
    markedChannelIntegral q
      (payoffBranchCompound (Channel.idChannel : Channel A A) g) phi
  rw [payoffBranchCompound, markedChannelIntegral_commonPayoffCompound]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [identityChannel_outcomeMarginal]
  simp only [payoffBranchContinuation, markedChannelIntegral_uninformativeAtPayoff]
  by_cases ha : 0 < q a
  · rw [identityChannel_posterior_of_pos q a ha]
  · have hz : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
    rw [hz, zero_mul, zero_mul]

/-- Consequently the normalized values of these two concrete experiments agree. -/
theorem normalizedMarkedUtility_fullRevealWithPayoff_eq_payoffBranch
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (g : A → O) :
    normalizedMarkedUtility F h q hq (fullRevealWithPayoffExperiment g) =
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment (Channel.idChannel : Channel A A) g) := by
  exact normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _
    (sameMarkedTerminalLaw_fullRevealWithPayoff_payoffBranch q g)

/-- A degenerate payoff lottery is the deterministic uninformative channel. -/
theorem payoffLotteryChannel_pure_eq_uninformative (o : O) :
    payoffLotteryChannel (A := A) (Dist.pure o) =
      uninformativeAtPayoff (A := A) o := by
  funext a
  apply Dist.ext
  rintro ⟨o', r⟩
  cases r
  simp [payoffLotteryChannel_apply, uninformativeAtPayoff, Dist.pure_apply]

/-- Material relevance and A8 make an anchor upgrade strictly valuable after
any reached record.  This requires no posterior-support nontriviality and no
formula for the coefficient of the upgrade. -/
theorem normalizedMarkedUtility_payoffBranch_materialUpgrade_pos
    {Y : Type u} [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (htarget : BranchPositive P q target)
    (g : Y → O) :
    0 < normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (updateBranchPayoff g target (materialHighOutcome F h))) -
        normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (updateBranchPayoff g target (materialLowOutcome F h))) := by
  classical
  let Q := payoffBranchContinuation
    (A := A) (updateBranchPayoff g target (materialHighOutcome F h))
  let L := payoffBranchContinuation
    (A := A) (updateBranchPayoff g target (materialLowOutcome F h))
  have hoff : ∀ y, y ≠ target → Q y = L y := by
    intro y hy
    simp [Q, L, payoffBranchContinuation, updateBranchPayoff_of_ne _ _ _ _ hy]
  have hbranch : pairStrict F (branchPosterior P q target) (Q target)
      (branchPosterior P q target) (L target) := by
    simp only [Q, L, payoffBranchContinuation, updateBranchPayoff_target]
    rw [← payoffLotteryChannel_pure_eq_uninformative,
      ← payoffLotteryChannel_pure_eq_uninformative]
    exact materialChosenAnchors_strict_everyPrior F h
      (branchPosterior P q target) (branchPosterior P q target)
  have hweak : ∀ y, BranchPositive P q y →
      pairWeak F (branchPosterior P q y) (Q y)
        (branchPosterior P q y) (L y) := by
    intro y _hy
    by_cases hyt : y = target
    · subst y
      exact (pairStrict_iff_pairWeak_not_swap F h.a1 h.a3 h.a4 h.a5
        _ _ _ _).mp hbranch |>.1
    · rw [hoff y hyt]
      exact pairWeak_refl_of_structural F h.a1 h.a3 _ _
  have hstrict := h.a6.2 payoffBranchRecord P Q L q hweak
    ⟨target, htarget, hbranch⟩
  have hnot := (pairStrict_iff_pairWeak_not_swap F h.a1 h.a3 h.a4 h.a5
    q (commonPayoffCompound payoffBranchRecord P Q)
    q (commonPayoffCompound payoffBranchRecord P L)).mp hstrict
  apply sub_pos.mpr
  apply lt_of_not_ge
  intro hle
  apply hnot.2
  exact (normalizedMarkedUtility_represents F h q hq
    (payoffBranchExperiment P
      (updateBranchPayoff g target (materialLowOutcome F h)))
    (payoffBranchExperiment P
      (updateBranchPayoff g target (materialHighOutcome F h)))).mpr hle

/-- In particular, upgrading one revealed action from the low material anchor
to the high one has strictly positive value under every full-support prior. -/
theorem normalizedMarkedUtility_fullReveal_materialUpgrade_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (a : A) :
    0 < normalizedMarkedUtility F h q hq
          (fullRevealWithPayoffExperiment
            (Function.update (fun _ : A ↦ materialLowOutcome F h)
              a (materialHighOutcome F h))) -
        normalizedMarkedUtility F h q hq
          (fullRevealWithPayoffExperiment
            (fun _ : A ↦ materialLowOutcome F h)) := by
  have hpos : BranchPositive (Channel.idChannel : Channel A A) q a := by
    change 0 < Channel.outcomeMarginal (Channel.idChannel : Channel A A) q a
    rw [identityChannel_outcomeMarginal]
    exact hq a
  have hp := normalizedMarkedUtility_payoffBranch_materialUpgrade_pos
    F h q hq (Channel.idChannel : Channel A A) a hpos
      (fun _ : A ↦ materialLowOutcome F h)
  have hbase : updateBranchPayoff (fun _ : A ↦ materialLowOutcome F h)
      a (materialLowOutcome F h) = (fun _ : A ↦ materialLowOutcome F h) := by
    funext b
    simp [updateBranchPayoff]
  rw [hbase, updateBranchPayoff_eq_update] at hp
  rw [normalizedMarkedUtility_fullRevealWithPayoff_eq_payoffBranch,
    normalizedMarkedUtility_fullRevealWithPayoff_eq_payoffBranch]
  exact hp

end TraceableAgency.Theorem1.MaterialCalibration
