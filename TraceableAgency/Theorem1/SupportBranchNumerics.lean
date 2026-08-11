/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.SupportBranchInsertion
import TraceableAgency.Theorem1.BranchInformation
import TraceableAgency.Theorem1.ConstantLowGeneral
import TraceableAgency.Theorem1.BranchPayoffLaw

/-!
# Numerical identities for support-face branch insertion

This file records the numerical and law-level facts needed to calibrate a
reached branch whose posterior may lie on the boundary of the ambient action
simplex.  Support extension preserves the continuation's mutual information,
sure-low property, and action-independent pure-payoff law.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-! ## Mutual information -/

/-- Exact chain-rule formula for inserting a marked experiment from the
support face of the reached posterior. -/
theorem mutualInfo_supportBranchInsertionExperiment
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target))) :
    @mutualInfo A
        (O × (supportBranchInsertionExperiment
          q P target o0 E).RecordType)
        inferInstance
        (@instFintypeProd O
          (supportBranchInsertionExperiment q P target o0 E).RecordType
          inferInstance
          (supportBranchInsertionExperiment q P target o0 E).recordFintype)
        q (supportBranchInsertionExperiment q P target o0 E).K =
      mutualInfo q P +
        Channel.outcomeMarginal P q target *
          @mutualInfo (supportSubtype (branchPosterior P q target))
            (O × E.RecordType) inferInstance
            (@instFintypeProd O E.RecordType inferInstance E.recordFintype)
            (branchPosterior P q target).restrictToSupport E.K := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  unfold supportBranchInsertionExperiment
  rw [mutualInfo_branchInsertionExperiment]
  congr 1
  congr 1
  change mutualInfo (branchPosterior P q target)
      (supportExtendChannel (branchPosterior P q target) E.K) =
    mutualInfo (branchPosterior P q target).restrictToSupport E.K
  rw [← mutualInfo_restrictToSupport
      (supportExtendChannel (branchPosterior P q target) E.K)
      (branchPosterior P q target),
    restrictToSupport_supportExtendChannel]

/-! ## Preservation of a sure payoff -/

/-- Support extension preserves a pointwise sure-payoff property. -/
theorem supportExtendMarkedExperiment_surePayoff
    (r : TraceableAgency.Dist A) (o0 : O)
    (E : MarkedTerminalExperiment O (supportSubtype r))
    (hE : ∀ (a : supportSubtype r) (o : O) (s : E.RecordType),
      o ≠ o0 → E.K a (o, s) = 0) :
    ∀ (a : A) (o : O)
      (s : (supportExtendMarkedExperiment r E).RecordType),
      o ≠ o0 → (supportExtendMarkedExperiment r E).K a (o, s) = 0 := by
  intro a o s ho
  exact hE (supportProject r a) o s ho

/-- If the support-face continuation is surely the normalized material-low
payoff, then inserting it with the same low baseline is pointwise surely low.
This is exactly the premise used by the general constant-low value theorem. -/
theorem supportBranchInsertionExperiment_sureLow
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y)
    (E : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target)))
    (hE : ∀ (a : supportSubtype (branchPosterior P q target))
      (o : O) (s : E.RecordType),
      o ≠ materialLowOutcome F h → E.K a (o, s) = 0) :
    ∀ (a : A) (o : O)
      (s : (supportBranchInsertionExperiment q P target
        (materialLowOutcome F h) E).RecordType),
      o ≠ materialLowOutcome F h →
        (supportBranchInsertionExperiment q P target
          (materialLowOutcome F h) E).K a (o, s) = 0 := by
  classical
  let r := branchPosterior P q target
  let SE := supportExtendMarkedExperiment r E
  have hSE : ∀ (a : A) (o : O) (s : SE.RecordType),
      o ≠ materialLowOutcome F h → SE.K a (o, s) = 0 := by
    exact supportExtendMarkedExperiment_surePayoff
      r (materialLowOutcome F h) E hE
  intro a o s ho
  rcases s with ⟨y, sy⟩
  change P a y *
      (branchInsertionContinuation target (materialLowOutcome F h) SE y)
        a (o, sy) = 0
  by_cases hy : y = target
  · subst y
    unfold branchInsertionContinuation
    simp only [eq_self, dite_true, Relabeling.relabelChannel_apply]
    change P a target * SE.K a (o, (Equiv.cast _).symm sy) = 0
    rw [hSE a o _ ho, mul_zero]
  · unfold branchInsertionContinuation
    simp only [dif_neg hy, Relabeling.relabelChannel_apply]
    change P a y *
      (uninformativeAtPayoff (A := A) (materialLowOutcome F h)) a
        (o, (Equiv.cast _).symm sy) = 0
    simp [uninformativeAtPayoff, ho]

/-! ## Pure payoff insertion -/

/-- Extending an action-independent payoff lottery from a support face does
not change its channel. -/
theorem supportExtendMarkedExperiment_markedPayoffLottery_channel
    (r : TraceableAgency.Dist A) (ell : TraceableAgency.Dist O) :
    (supportExtendMarkedExperiment r
      (markedPayoffLotteryExperiment
        (A := supportSubtype r) ell)).K =
      (markedPayoffLotteryExperiment (A := A) ell).K := by
  funext a
  rfl

/-- Consequently the support-extended payoff lottery has exactly the ambient
payoff lottery's marked terminal law. -/
theorem sameMarkedTerminalLaw_supportExtend_markedPayoffLottery
    (r : TraceableAgency.Dist A) (ell : TraceableAgency.Dist O) :
    SameMarkedTerminalLaw r
      (supportExtendMarkedExperiment r
        (markedPayoffLotteryExperiment
          (A := supportSubtype r) ell))
      (markedPayoffLotteryExperiment (A := A) ell) := by
  let SX := supportExtendMarkedExperiment r
    (markedPayoffLotteryExperiment (A := supportSubtype r) ell)
  letI : Fintype SX.RecordType := SX.recordFintype
  intro phi
  change markedChannelIntegral r SX.K phi =
    markedChannelIntegral r
      (markedPayoffLotteryExperiment (A := A) ell).K phi
  rw [show SX.K =
      (markedPayoffLotteryExperiment (A := A) ell).K from
    supportExtendMarkedExperiment_markedPayoffLottery_channel r ell]
  rfl

/-- Support-face insertion of a pure payoff lottery is the same marked law as
changing precisely the distinguished deterministic-payoff branch. -/
theorem sameMarkedTerminalLaw_supportBranchInsertion_purePayoff
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 o : O) :
    SameMarkedTerminalLaw q
      (supportBranchInsertionExperiment q P target o0
        (markedPayoffLotteryExperiment
          (A := supportSubtype (branchPosterior P q target))
          (TraceableAgency.Dist.pure o)))
      (payoffBranchExperiment P
        (updateBranchPayoff (fun _ ↦ o0) target o)) := by
  let r := branchPosterior P q target
  have hext : SameMarkedTerminalLaw r
      (supportExtendMarkedExperiment r
        (markedPayoffLotteryExperiment
          (A := supportSubtype r) (TraceableAgency.Dist.pure o)))
      (markedPayoffLotteryExperiment
        (A := A) (TraceableAgency.Dist.pure o)) :=
    sameMarkedTerminalLaw_supportExtend_markedPayoffLottery
      r (TraceableAgency.Dist.pure o)
  have hins : SameMarkedTerminalLaw q
      (supportBranchInsertionExperiment q P target o0
        (markedPayoffLotteryExperiment
          (A := supportSubtype r) (TraceableAgency.Dist.pure o)))
      (branchInsertionExperiment P target o0
        (markedPayoffLotteryExperiment
          (A := A) (TraceableAgency.Dist.pure o))) := by
    exact sameMarkedTerminalLaw_branchInsertion
      q P target o0 _ _ hext
  have hpay := sameMarkedTerminalLaw_branchInsertion_purePayoff
    (A := A) q P target o0 o
  intro phi
  exact (hins phi).trans (hpay phi)

/-- The corresponding normalized marked values are equal on every
full-support outer fibre. -/
theorem normalizedMarkedUtility_supportBranchInsertion_purePayoff
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y) (o0 o : O) :
    normalizedMarkedUtility F h q hq
        (supportBranchInsertionExperiment q P target o0
          (markedPayoffLotteryExperiment
            (A := supportSubtype (branchPosterior P q target))
            (TraceableAgency.Dist.pure o))) =
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff (fun _ ↦ o0) target o)) := by
  exact normalizedMarkedUtility_respects_sameMarkedTerminalLaw
    F h q hq _ _
      (sameMarkedTerminalLaw_supportBranchInsertion_purePayoff
        q P target o0 o)

end TraceableAgency.Theorem1
