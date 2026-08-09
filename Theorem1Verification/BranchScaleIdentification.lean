/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.SupportBranchNumerics

/-!
# Identifying the probability scale of branch insertion

On a nontrivial reached support face, compare the constant-low full-revelation
experiment with the constant-low uninformative experiment.  The local value
difference is the global trace coefficient times the support entropy, while
the value difference after insertion is additionally multiplied by the
probability of reaching the branch.  Positive-affine uniqueness therefore
forces the selected insertion scale to equal that branch probability.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-! ## Constant-low calibration pair on a support face -/

/-- Full revelation on a support face, with the normalized material-low payoff
attached deterministically. -/
noncomputable def supportLowFullRevealExperiment
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (r : TraceableAgency.Dist A) :
    MarkedTerminalExperiment O (supportSubtype r) := by
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  exact markedExperimentOfChannel
    (fullRevealAtPayoff
      (A := supportSubtype r) (materialLowOutcome F h))

/-- The uninformative support-face experiment with the same normalized
material-low payoff. -/
noncomputable def supportLowUninformativeExperiment
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (r : TraceableAgency.Dist A) :
    MarkedTerminalExperiment O (supportSubtype r) :=
  markedExperimentOfChannel
    (uninformativeAtPayoff
      (A := supportSubtype r) (materialLowOutcome F h))

@[simp]
theorem supportLowFullRevealExperiment_K
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (r : TraceableAgency.Dist A) :
    (supportLowFullRevealExperiment F h r).K =
      fullRevealAtPayoff
        (A := supportSubtype r) (materialLowOutcome F h) := by
  rfl

@[simp]
theorem supportLowUninformativeExperiment_K
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (r : TraceableAgency.Dist A) :
    (supportLowUninformativeExperiment F h r).K =
      uninformativeAtPayoff
        (A := supportSubtype r) (materialLowOutcome F h) := by
  rfl

theorem supportLowFullRevealExperiment_sureLow
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (r : TraceableAgency.Dist A) :
    ∀ (a : supportSubtype r) (o : O)
      (s : (supportLowFullRevealExperiment F h r).RecordType),
      o ≠ materialLowOutcome F h →
        (supportLowFullRevealExperiment F h r).K a (o, s) = 0 := by
  classical
  intro a o s ho
  change
    (TraceableAgency.Dist.pure
      (materialLowOutcome F h, a)) (o, s) = 0
  apply TraceableAgency.Dist.pure_apply_ne
  intro heq
  exact ho (by simpa using congrArg Prod.fst heq)

theorem supportLowUninformativeExperiment_sureLow
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (r : TraceableAgency.Dist A) :
    ∀ (a : supportSubtype r) (o : O)
      (s : (supportLowUninformativeExperiment F h r).RecordType),
      o ≠ materialLowOutcome F h →
        (supportLowUninformativeExperiment F h r).K a (o, s) = 0 := by
  classical
  intro a o s ho
  change
    (TraceableAgency.Dist.pure
      (materialLowOutcome F h, PUnit.unit)) (o, s) = 0
  apply TraceableAgency.Dist.pure_apply_ne
  intro heq
  exact ho (by simpa using congrArg Prod.fst heq)

/-! ## Numerical identification -/

/-- The positive affine scale selected for support-face branch insertion is
exactly the probability of reaching that branch, provided the reached support
contains at least two actions. -/
theorem supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    [Nontrivial (supportSubtype (branchPosterior P q target))] :
    supportBranchInsertionScale F h q hq P target htarget
        (materialLowOutcome F h) =
      Channel.outcomeMarginal P q target := by
  classical
  let r := branchPosterior P q target
  let rs := r.restrictToSupport
  let hrs : rs.FullSupport := Dist.restrictToSupport_fullSupport r
  let Efull : MarkedTerminalExperiment O (supportSubtype r) :=
    supportLowFullRevealExperiment F h r
  let Euninf : MarkedTerminalExperiment O (supportSubtype r) :=
    supportLowUninformativeExperiment F h r
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  letI : Nontrivial A := Function.Injective.nontrivial
    (f := fun x : supportSubtype r ↦ x.1) Subtype.val_injective
  have hEfullLow : ∀ (a : supportSubtype r) (o : O)
      (s : Efull.RecordType), o ≠ materialLowOutcome F h →
        Efull.K a (o, s) = 0 := by
    simpa [Efull] using supportLowFullRevealExperiment_sureLow F h r
  have hEuninfLow : ∀ (a : supportSubtype r) (o : O)
      (s : Euninf.RecordType), o ≠ materialLowOutcome F h →
        Euninf.K a (o, s) = 0 := by
    simpa [Euninf] using supportLowUninformativeExperiment_sureLow F h r
  have hlocalFull :=
    normalizedMarkedUtility_eq_globalTraceLambda_mul_mutualInfo_of_sureLow
      F h rs hrs Efull hEfullLow
  have hlocalUninf :=
    normalizedMarkedUtility_eq_globalTraceLambda_mul_mutualInfo_of_sureLow
      F h rs hrs Euninf hEuninfLow
  have hmiLocalFull :
      @mutualInfo (supportSubtype r) (O × Efull.RecordType)
          inferInstance
          (@instFintypeProd O Efull.RecordType inferInstance
            Efull.recordFintype)
          rs Efull.K = entropy rs := by
    change mutualInfo rs
      (fullRevealAtPayoff
        (A := supportSubtype r) (materialLowOutcome F h)) = entropy rs
    exact mutualInfo_fullRevealAtPayoff rs (materialLowOutcome F h)
  have hmiLocalUninf :
      @mutualInfo (supportSubtype r) (O × Euninf.RecordType)
          inferInstance
          (@instFintypeProd O Euninf.RecordType inferInstance
            Euninf.recordFintype)
          rs Euninf.K = 0 := by
    change mutualInfo rs
      (uninformativeAtPayoff
        (A := supportSubtype r) (materialLowOutcome F h)) = 0
    exact mutualInfo_uninformativeAtPayoff rs (materialLowOutcome F h)
  rw [hmiLocalFull] at hlocalFull
  rw [hmiLocalUninf, mul_zero] at hlocalUninf
  have houterFull :=
    normalizedMarkedUtility_eq_globalTraceLambda_mul_mutualInfo_of_sureLow
      F h q hq
        (supportBranchInsertionExperiment q P target
          (materialLowOutcome F h) Efull)
        (supportBranchInsertionExperiment_sureLow
          F h q P target Efull hEfullLow)
  have houterUninf :=
    normalizedMarkedUtility_eq_globalTraceLambda_mul_mutualInfo_of_sureLow
      F h q hq
        (supportBranchInsertionExperiment q P target
          (materialLowOutcome F h) Euninf)
        (supportBranchInsertionExperiment_sureLow
          F h q P target Euninf hEuninfLow)
  have hmiOuterFull := mutualInfo_supportBranchInsertionExperiment
    q P target (materialLowOutcome F h) Efull
  have hmiOuterUninf := mutualInfo_supportBranchInsertionExperiment
    q P target (materialLowOutcome F h) Euninf
  rw [hmiLocalFull] at hmiOuterFull
  rw [hmiLocalUninf, mul_zero, add_zero] at hmiOuterUninf
  rw [hmiOuterFull] at houterFull
  rw [hmiOuterUninf] at houterUninf
  have haffFull := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (materialLowOutcome F h) Efull
  have haffUninf := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (materialLowOutcome F h) Euninf
  rw [hlocalFull] at haffFull
  rw [hlocalUninf, mul_zero, zero_add] at haffUninf
  have htrace : 0 < globalTraceLambda F h := globalTraceLambda_pos F h
  have hentropy : 0 < entropy rs :=
    entropy_pos_of_fullSupport_nontrivial rs hrs
  have hfactor : globalTraceLambda F h * entropy rs ≠ 0 :=
    mul_ne_zero (ne_of_gt htrace) (ne_of_gt hentropy)
  have hscaled :
      (globalTraceLambda F h * entropy rs) *
          supportBranchInsertionScale F h q hq P target htarget
            (materialLowOutcome F h) =
        (globalTraceLambda F h * entropy rs) *
          Channel.outcomeMarginal P q target := by
    rw [haffFull] at houterFull
    rw [haffUninf] at houterUninf
    nlinarith
  exact mul_left_cancel₀ hfactor hscaled

/-! ## Deterministic-payoff increment -/

/-- On a reached branch with nontrivial support, replacing the normalized
material-low continuation by a deterministic payoff `o` changes normalized
value by the reached mass times the common material payoff index. -/
theorem positiveBranchPayoffIncrement_of_nontrivialSupport
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    [Nontrivial (supportSubtype (branchPosterior P q target))]
    (o : O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff
            (fun _ ↦ materialLowOutcome F h) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ materialLowOutcome F h)) =
      Channel.outcomeMarginal P q target * materialPayoffUtility F h o := by
  classical
  let r := branchPosterior P q target
  let rs := r.restrictToSupport
  let hrs : rs.FullSupport := Dist.restrictToSupport_fullSupport r
  let Eo : MarkedTerminalExperiment O (supportSubtype r) :=
    markedPayoffLotteryExperiment (TraceableAgency.Dist.pure o)
  let Elow : MarkedTerminalExperiment O (supportSubtype r) :=
    markedPayoffLotteryExperiment
      (TraceableAgency.Dist.pure (materialLowOutcome F h))
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  have hlocalO : normalizedMarkedUtility F h rs hrs Eo =
      materialPayoffUtility F h o := by
    have hvalue := normalizedMarkedUtility_payoffLottery
      (A := supportSubtype r) F h rs hrs
        (TraceableAgency.Dist.pure o)
    rw [expectedPayoffUtility_payoffLotteryChannel] at hvalue
    have hpure : payoffLotteryExpected (materialPayoffUtility F h)
        (TraceableAgency.Dist.pure o) = materialPayoffUtility F h o := by
      unfold payoffLotteryExpected
      rw [Finset.sum_eq_single o]
      · simp
      · intro x _hx hxo
        rw [TraceableAgency.Dist.pure_apply_ne o x hxo]
        simp
      · simp
    rw [hpure] at hvalue
    simpa [Eo] using hvalue
  have hlocalLow : normalizedMarkedUtility F h rs hrs Elow = 0 := by
    simpa [Elow] using normalizedMarkedUtility_low F h rs hrs
  have haffO := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (materialLowOutcome F h) Eo
  have haffLow := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (materialLowOutcome F h) Elow
  have hpureO := normalizedMarkedUtility_supportBranchInsertion_purePayoff
    F h q hq P target (materialLowOutcome F h) o
  have hpureLow :=
    normalizedMarkedUtility_supportBranchInsertion_purePayoff
      F h q hq P target (materialLowOutcome F h)
        (materialLowOutcome F h)
  have hupdateLow :
      updateBranchPayoff (fun _ : Y ↦ materialLowOutcome F h) target
          (materialLowOutcome F h) =
        (fun _ : Y ↦ materialLowOutcome F h) := by
    funext y
    by_cases hy : y = target
    · subst y
      simp
    · simp [updateBranchPayoff, hy]
  rw [hupdateLow] at hpureLow
  rw [hlocalO] at haffO
  rw [hlocalLow, mul_zero, zero_add] at haffLow
  rw [
    supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport
      F h q hq P target htarget] at haffO
  calc
    normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (updateBranchPayoff
              (fun _ ↦ materialLowOutcome F h) target o)) -
        normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (fun _ ↦ materialLowOutcome F h)) =
        normalizedMarkedUtility F h q hq
            (supportBranchInsertionExperiment q P target
              (materialLowOutcome F h) Eo) -
          normalizedMarkedUtility F h q hq
            (supportBranchInsertionExperiment q P target
              (materialLowOutcome F h) Elow) := by
      rw [hpureO, hpureLow]
    _ = Channel.outcomeMarginal P q target *
          materialPayoffUtility F h o := by
      rw [haffO, haffLow]
      ring

end TraceTemperedChoiceVerification
