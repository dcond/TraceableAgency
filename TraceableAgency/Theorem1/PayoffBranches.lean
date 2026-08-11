/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.Benchmark
import TraceableAgency.Theorem1.MarkedTransport

/-!
# Deterministic-payoff continuation profiles

The terminal-payoff sequentialization used in the proof has a particularly
simple continuation profile: after a first-stage record `y`, the continuation
pays a deterministic outcome `payoff y` and emits a one-point record.  This
file names that profile and records its exact expected-payoff, information,
and independent-dummy identities.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Every deterministic terminal branch uses a one-point explicit record. -/
abbrev payoffBranchRecord (_y : Y) : Type u := PUnit.{u + 1}

/-- The action-independent terminal continuation paying `payoff y`. -/
noncomputable def payoffBranchContinuation
    (payoff : Y → O) (y : Y) :
    Channel A (O × payoffBranchRecord y) :=
  uninformativeAtPayoff (payoff y)

/-- First run `P`, then pay the outcome attached to the reached branch. -/
noncomputable def payoffBranchCompound
    (P : Channel A Y) (payoff : Y → O) :
    Channel A (O × ((y : Y) × payoffBranchRecord y)) :=
  commonPayoffCompound payoffBranchRecord P
    (payoffBranchContinuation payoff)

/-- Bundled marked experiment associated with a deterministic-payoff profile. -/
noncomputable abbrev payoffBranchExperiment
    (P : Channel A Y) (payoff : Y → O) :
    MarkedTerminalExperiment O A :=
  markedExperimentOfChannel (payoffBranchCompound P payoff)

/-- A terminal deterministic-payoff continuation has no conditional action
information. -/
@[simp]
theorem mutualInfo_payoffBranchContinuation
    (r : TraceableAgency.Dist A) (payoff : Y → O) (y : Y) :
    mutualInfo r (payoffBranchContinuation payoff y) = 0 := by
  exact mutualInfo_uninformativeAtPayoff r (payoff y)

/-- The whole deterministic-payoff profile carries exactly the information
already revealed by the first-stage record. -/
theorem mutualInfo_payoffBranchCompound
    (q : TraceableAgency.Dist A) (P : Channel A Y) (payoff : Y → O) :
    mutualInfo q (payoffBranchCompound P payoff) = mutualInfo q P := by
  rw [payoffBranchCompound, mutualInfo_commonCompound]
  simp

/-- Expected material utility aggregates at the reached branch masses. -/
theorem expectedPayoffUtility_payoffBranchCompound
    (u : O → ℝ) (q : TraceableAgency.Dist A)
    (P : Channel A Y) (payoff : Y → O) :
    expectedPayoffUtility u q (payoffBranchCompound P payoff) =
      ∑ y : Y, Channel.outcomeMarginal P q y * u (payoff y) := by
  rw [payoffBranchCompound, expectedPayoffUtility_commonCompound]
  apply Finset.sum_congr rfl
  intro y _hy
  simp only [payoffBranchContinuation,
    expectedPayoffUtility_uninformativeAtPayoff]

/-- The target trace-tempered value of a deterministic-payoff profile. -/
theorem traceTemperedValue_payoffBranchCompound
    (u : O → ℝ) (lambda : ℝ)
    (q : TraceableAgency.Dist A) (P : Channel A Y) (payoff : Y → O) :
    traceTemperedValue u lambda q (payoffBranchCompound P payoff) =
      lambda * mutualInfo q P +
        ∑ y : Y, Channel.outcomeMarginal P q y * u (payoff y) := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_payoffBranchCompound,
    mutualInfo_payoffBranchCompound]
  ring

/-- A constant terminal payoff turns the compound into the usual
constant-payoff lift of the first-stage experiment, up to the canonical
dependent-record association already built into `commonPayoffCompound`. -/
theorem payoffBranchCompound_const
    (P : Channel A Y) (o : O) :
    payoffBranchCompound P (fun _ ↦ o) =
      commonPayoffCompound payoffBranchRecord P
        (fun y ↦ uninformativeAtPayoff (A := A) o) := by
  rfl

/-- Adding an ignored independent action coordinate commutes definitionally
with every terminal deterministic-payoff continuation. -/
theorem independentDummy_payoffBranchContinuation
    {B : Type u} [Fintype B]
    (payoff : Y → O) (y : Y) :
    independentDummyChannel (B := B)
        (payoffBranchContinuation (A := A) payoff y) =
      payoffBranchContinuation (A := A × B) payoff y := by
  rfl

/-- Generic ignored-dummy lift for a first-stage channel. -/
noncomputable def independentDummyFirstStage
    {B : Type u} [Fintype B]
    (P : Channel A Y) : Channel (A × B) Y :=
  fun ab ↦ P ab.1

theorem outcomeMarginal_independentDummyFirstStage
    {B : Type u} [Fintype B]
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (r : TraceableAgency.Dist B) :
    Channel.outcomeMarginal (independentDummyFirstStage (B := B) P)
        (prodDist q r) = Channel.outcomeMarginal P q := by
  ext y
  simp only [Channel.outcomeMarginal_apply, independentDummyFirstStage]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∑ b, prodDist q r (a, b) * P a y) =
        q a * P a y * ∑ b, r b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [prodDist_apply_pair]
      ring
    _ = q a * P a y := by rw [r.sum_eq_one, mul_one]

theorem mutualInfo_independentDummyFirstStage
    {B : Type u} [Fintype B]
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (r : TraceableAgency.Dist B) :
    mutualInfo (prodDist q r)
        (independentDummyFirstStage (B := B) P) = mutualInfo q P := by
  unfold mutualInfo
  rw [outcomeMarginal_independentDummyFirstStage]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∑ b, prodDist q r (a, b) *
        entropy (independentDummyFirstStage P (a, b))) =
        q a * entropy (P a) * ∑ b, r b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [prodDist_apply_pair, independentDummyFirstStage]
      ring
    _ = q a * entropy (P a) := by rw [r.sum_eq_one, mul_one]

theorem posterior_independentDummyFirstStage_of_pos
    {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B]
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (r : TraceableAgency.Dist B) (y : Y)
    (hy : 0 < Channel.outcomeMarginal P q y) :
    Channel.posterior (independentDummyFirstStage (B := B) P)
        (prodDist q r) y = prodDist (Channel.posterior P q y) r := by
  classical
  have hmarg : Channel.outcomeMarginal
      (independentDummyFirstStage (B := B) P) (prodDist q r) y =
        Channel.outcomeMarginal P q y := by
    rw [outcomeMarginal_independentDummyFirstStage]
  have hy' : 0 < Channel.outcomeMarginal
      (independentDummyFirstStage (B := B) P) (prodDist q r) y := by
    rw [hmarg]
    exact hy
  ext ab
  rcases ab with ⟨a, b⟩
  have hleft :
      Channel.posterior (independentDummyFirstStage (B := B) P)
          (prodDist q r) y (a, b) =
        (prodDist q r (a, b) *
            independentDummyFirstStage (B := B) P (a, b) y) /
          Channel.outcomeMarginal
            (independentDummyFirstStage (B := B) P) (prodDist q r) y := by
    unfold Channel.posterior
    rw [dif_pos hy']
  have hright : Channel.posterior P q y a =
      q a * P a y / Channel.outcomeMarginal P q y := by
    unfold Channel.posterior
    rw [dif_pos hy]
  rw [hleft, hmarg]
  simp only [prodDist_apply_pair, independentDummyFirstStage]
  rw [hright]
  ring

/-- Adding an ignored independent action coordinate commutes with the entire
deterministic-payoff compound when the first-stage channel is lifted in the
same way. -/
theorem independentDummy_payoffBranchCompound
    {B : Type u} [Fintype B]
    (P : Channel A Y) (payoff : Y → O) :
    independentDummyChannel (B := B) (payoffBranchCompound P payoff) =
      payoffBranchCompound (independentDummyFirstStage (B := B) P)
        payoff := by
  rfl

end TraceableAgency.Theorem1
