/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.SupportBranchNumerics

/-!
# Identifying the probability scale of branch insertion

On a nontrivial reached support face, compare full revelation with silence at
the separate v5 trace anchor.  The local value
difference is the global trace coefficient times the support entropy, while
the value difference after insertion is additionally multiplied by the
probability of reaching the branch.  Positive-affine uniqueness therefore
forces the selected insertion scale to equal that branch probability.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-! ## Constant-trace-anchor calibration pair on a support face -/

/-- Full revelation on a support face, with the v5 trace-anchor payoff
attached deterministically. -/
noncomputable def supportTraceAnchorFullRevealExperiment
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) :
    MarkedTerminalExperiment O (supportSubtype r) := by
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  exact markedExperimentOfChannel
    (fullRevealAtPayoff
      (A := supportSubtype r) (h.traceAnchor))

/-- The uninformative support-face experiment with the same trace-anchor
payoff. -/
noncomputable def supportTraceAnchorUninformativeExperiment
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) :
    MarkedTerminalExperiment O (supportSubtype r) :=
  markedExperimentOfChannel
    (uninformativeAtPayoff
      (A := supportSubtype r) (h.traceAnchor))

@[simp]
theorem supportTraceAnchorFullRevealExperiment_K
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) :
    (supportTraceAnchorFullRevealExperiment F h r).K =
      fullRevealAtPayoff
        (A := supportSubtype r) (h.traceAnchor) := by
  rfl

@[simp]
theorem supportTraceAnchorUninformativeExperiment_K
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) :
    (supportTraceAnchorUninformativeExperiment F h r).K =
      uninformativeAtPayoff
        (A := supportSubtype r) (h.traceAnchor) := by
  rfl

theorem supportTraceAnchorFullRevealExperiment_sureTraceAnchor
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) :
    ∀ (a : supportSubtype r) (o : O)
      (s : (supportTraceAnchorFullRevealExperiment F h r).RecordType),
      o ≠ h.traceAnchor →
        (supportTraceAnchorFullRevealExperiment F h r).K a (o, s) = 0 := by
  classical
  intro a o s ho
  change
    (TraceableAgency.Dist.pure
      (h.traceAnchor, a)) (o, s) = 0
  apply TraceableAgency.Dist.pure_apply_ne
  intro heq
  exact ho (by simpa using congrArg Prod.fst heq)

theorem supportTraceAnchorUninformativeExperiment_sureTraceAnchor
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) :
    ∀ (a : supportSubtype r) (o : O)
      (s : (supportTraceAnchorUninformativeExperiment F h r).RecordType),
      o ≠ h.traceAnchor →
        (supportTraceAnchorUninformativeExperiment F h r).K a (o, s) = 0 := by
  classical
  intro a o s ho
  change
    (TraceableAgency.Dist.pure
      (h.traceAnchor, PUnit.unit)) (o, s) = 0
  apply TraceableAgency.Dist.pure_apply_ne
  intro heq
  exact ho (by simpa using congrArg Prod.fst heq)

/-! ## Numerical identification -/

/-- The positive affine scale selected for support-face branch insertion is
exactly the probability of reaching that branch, provided the reached support
contains at least two actions. -/
theorem supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    [Nontrivial (supportSubtype (branchPosterior P q target))] :
    supportBranchInsertionScale F h q hq P target htarget
        (h.traceAnchor) =
      Channel.outcomeMarginal P q target := by
  classical
  let r := branchPosterior P q target
  let rs := r.restrictToSupport
  let hrs : rs.FullSupport := Dist.restrictToSupport_fullSupport r
  let Efull : MarkedTerminalExperiment O (supportSubtype r) :=
    supportTraceAnchorFullRevealExperiment F h r
  let Euninf : MarkedTerminalExperiment O (supportSubtype r) :=
    supportTraceAnchorUninformativeExperiment F h r
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  letI : Nontrivial A := Function.Injective.nontrivial
    (f := fun x : supportSubtype r ↦ x.1) Subtype.val_injective
  have hEfullLow : ∀ (a : supportSubtype r) (o : O)
      (s : Efull.RecordType), o ≠ h.traceAnchor →
        Efull.K a (o, s) = 0 := by
    simpa [Efull] using supportTraceAnchorFullRevealExperiment_sureTraceAnchor F h r
  have hEuninfLow : ∀ (a : supportSubtype r) (o : O)
      (s : Euninf.RecordType), o ≠ h.traceAnchor →
        Euninf.K a (o, s) = 0 := by
    simpa [Euninf] using supportTraceAnchorUninformativeExperiment_sureTraceAnchor F h r
  have hlocalFull :=
    normalizedMarkedUtility_eq_materialUtility_add_globalTraceLambda_mul_mutualInfo_of_sureTraceAnchor
      F h rs hrs Efull hEfullLow
  have hlocalUninf :=
    normalizedMarkedUtility_eq_materialUtility_add_globalTraceLambda_mul_mutualInfo_of_sureTraceAnchor
      F h rs hrs Euninf hEuninfLow
  have hmiLocalFull :
      @mutualInfo (supportSubtype r) (O × Efull.RecordType)
          inferInstance
          (@instFintypeProd O Efull.RecordType inferInstance
            Efull.recordFintype)
          rs Efull.K = entropy rs := by
    change mutualInfo rs
      (fullRevealAtPayoff
        (A := supportSubtype r) (h.traceAnchor)) = entropy rs
    exact mutualInfo_fullRevealAtPayoff rs (h.traceAnchor)
  have hmiLocalUninf :
      @mutualInfo (supportSubtype r) (O × Euninf.RecordType)
          inferInstance
          (@instFintypeProd O Euninf.RecordType inferInstance
            Euninf.recordFintype)
          rs Euninf.K = 0 := by
    change mutualInfo rs
      (uninformativeAtPayoff
        (A := supportSubtype r) (h.traceAnchor)) = 0
    exact mutualInfo_uninformativeAtPayoff rs (h.traceAnchor)
  rw [hmiLocalFull] at hlocalFull
  rw [hmiLocalUninf, mul_zero, add_zero] at hlocalUninf
  have houterFull :=
    normalizedMarkedUtility_eq_materialUtility_add_globalTraceLambda_mul_mutualInfo_of_sureTraceAnchor
      F h q hq
        (supportBranchInsertionExperiment q P target
          (h.traceAnchor) Efull)
        (supportBranchInsertionExperiment_sureTraceAnchor
          F h q P target Efull hEfullLow)
  have houterUninf :=
    normalizedMarkedUtility_eq_materialUtility_add_globalTraceLambda_mul_mutualInfo_of_sureTraceAnchor
      F h q hq
        (supportBranchInsertionExperiment q P target
          (h.traceAnchor) Euninf)
        (supportBranchInsertionExperiment_sureTraceAnchor
          F h q P target Euninf hEuninfLow)
  have hmiOuterFull := mutualInfo_supportBranchInsertionExperiment
    q P target (h.traceAnchor) Efull
  have hmiOuterUninf := mutualInfo_supportBranchInsertionExperiment
    q P target (h.traceAnchor) Euninf
  rw [hmiLocalFull] at hmiOuterFull
  rw [hmiLocalUninf, mul_zero, add_zero] at hmiOuterUninf
  rw [hmiOuterFull] at houterFull
  rw [hmiOuterUninf] at houterUninf
  have haffFull := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (h.traceAnchor) Efull
  have haffUninf := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (h.traceAnchor) Euninf
  rw [hlocalFull] at haffFull
  rw [hlocalUninf] at haffUninf
  have htrace : 0 < globalTraceLambda F h := globalTraceLambda_pos F h
  have hentropy : 0 < entropy rs :=
    entropy_pos_of_fullSupport_nontrivial rs hrs
  have hfactor : globalTraceLambda F h * entropy rs ≠ 0 :=
    mul_ne_zero (ne_of_gt htrace) (ne_of_gt hentropy)
  have hscaled :
      (globalTraceLambda F h * entropy rs) *
          supportBranchInsertionScale F h q hq P target htarget
            (h.traceAnchor) =
        (globalTraceLambda F h * entropy rs) *
          Channel.outcomeMarginal P q target := by
    rw [haffFull] at houterFull
    rw [haffUninf] at houterUninf
    nlinarith
  exact mul_left_cancel₀ hfactor hscaled

/-! ## Deterministic-payoff increment -/

/-- On a reached branch with nontrivial support, replacing the trace-anchor
continuation by a deterministic payoff `o` changes normalized value by the
reached mass times `u(o) - u(o_*)`. -/
theorem positiveBranchPayoffIncrement_of_nontrivialSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    [Nontrivial (supportSubtype (branchPosterior P q target))]
    (o : O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (updateBranchPayoff
            (fun _ ↦ h.traceAnchor) target o)) -
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P
          (fun _ ↦ h.traceAnchor)) =
      Channel.outcomeMarginal P q target *
        (materialPayoffUtility F h o -
          materialPayoffUtility F h h.traceAnchor) := by
  classical
  let r := branchPosterior P q target
  let rs := r.restrictToSupport
  let hrs : rs.FullSupport := Dist.restrictToSupport_fullSupport r
  let Eo : MarkedTerminalExperiment O (supportSubtype r) :=
    markedPayoffLotteryExperiment (TraceableAgency.Dist.pure o)
  let Elow : MarkedTerminalExperiment O (supportSubtype r) :=
    markedPayoffLotteryExperiment
      (TraceableAgency.Dist.pure (h.traceAnchor))
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
  have hlocalLow : normalizedMarkedUtility F h rs hrs Elow =
      materialPayoffUtility F h h.traceAnchor := by
    have hvalue := normalizedMarkedUtility_payoffLottery
      (A := supportSubtype r) F h rs hrs
        (TraceableAgency.Dist.pure h.traceAnchor)
    rw [expectedPayoffUtility_payoffLotteryChannel] at hvalue
    simpa [Elow, payoffLotteryExpected,
      TraceableAgency.Dist.pure_apply] using hvalue
  have haffO := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (h.traceAnchor) Eo
  have haffLow := normalizedMarkedUtility_supportBranchInsertion
    F h q hq P target htarget (h.traceAnchor) Elow
  have hpureO := normalizedMarkedUtility_supportBranchInsertion_purePayoff
    F h q hq P target (h.traceAnchor) o
  have hpureLow :=
    normalizedMarkedUtility_supportBranchInsertion_purePayoff
      F h q hq P target (h.traceAnchor)
        (h.traceAnchor)
  have hupdateLow :
      updateBranchPayoff (fun _ : Y ↦ h.traceAnchor) target
          (h.traceAnchor) =
        (fun _ : Y ↦ h.traceAnchor) := by
    funext y
    by_cases hy : y = target
    · subst y
      simp
    · simp [updateBranchPayoff, hy]
  rw [hupdateLow] at hpureLow
  rw [hlocalO] at haffO
  rw [hlocalLow] at haffLow
  rw [
    supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport
      F h q hq P target htarget] at haffO haffLow
  calc
    normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (updateBranchPayoff
              (fun _ ↦ h.traceAnchor) target o)) -
        normalizedMarkedUtility F h q hq
          (payoffBranchExperiment P
            (fun _ ↦ h.traceAnchor)) =
        normalizedMarkedUtility F h q hq
            (supportBranchInsertionExperiment q P target
              (h.traceAnchor) Eo) -
          normalizedMarkedUtility F h q hq
            (supportBranchInsertionExperiment q P target
              (h.traceAnchor) Elow) := by
      rw [hpureO, hpureLow]
    _ = Channel.outcomeMarginal P q target *
          (materialPayoffUtility F h o -
            materialPayoffUtility F h h.traceAnchor) := by
      rw [haffO, haffLow]
      ring

end TraceableAgency.Theorem1
