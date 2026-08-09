/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.MarkedTerminal
import Theorem1Verification.RightDummy

/-!
# Marked-terminal transport along independent dummy actions

The product bridge compares alternatives after adjoining an independently
distributed dummy action.  This file records the exact effect on the marked
terminal law: `(o,p)` is sent to `(o,p ⊗ r)`.  Zero-probability records are
handled inside the integral, so no convention about their arbitrary posterior
is used.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

/-- Bundle an ordinary payoff-record channel as a marked experiment. -/
def markedExperimentOfChannel
    {O A R : Type u}
    [Fintype O] [Fintype A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) : MarkedTerminalExperiment O A where
  RecordType := R
  recordFintype := inferInstance
  recordDecEq := inferInstance
  recordNonempty := inferInstance
  channel := K

@[simp]
theorem markedExperimentOfChannel_K
    {O A R : Type u}
    [Fintype O] [Fintype A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) :
    (markedExperimentOfChannel K).K = K := rfl

/-- Bundle the channel obtained by adjoining an ignored dummy action. -/
noncomputable def independentDummyMarkedExperiment
    {O A B : Type u}
    [Fintype O] [Fintype A] [Fintype B]
    (E : MarkedTerminalExperiment O A) :
    MarkedTerminalExperiment O (A × B) where
  RecordType := E.RecordType
  recordFintype := E.recordFintype
  recordDecEq := E.recordDecEq
  recordNonempty := E.recordNonempty
  channel := by
    letI : Fintype E.RecordType := E.recordFintype
    exact independentDummyChannel (B := B) E.K

theorem independentDummyMarkedExperiment_outcomeMarginal
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O A) (z : O × E.RecordType) :
    (independentDummyMarkedExperiment (B := B) E).outcomeMarginal
        (independentDummyPrior q r) z = E.outcomeMarginal q z := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  unfold MarkedTerminalExperiment.outcomeMarginal
  simp only [Channel.outcomeMarginal_apply,
    independentDummyPrior, independentDummyChannel]
  rw [Fintype.sum_prod_type]
  calc
    (∑ a, ∑ b, prodDist q r (a, b) * E.K a z) =
        ∑ a, q a * E.K a z * ∑ b, r b := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [prodDist_apply_pair]
      ring
    _ = ∑ a, q a * E.K a z := by rw [r.sum_eq_one]; simp

theorem independentDummyMarkedExperiment_posterior_of_pos
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O A) (z : O × E.RecordType)
    (hz : 0 < E.outcomeMarginal q z) :
    (independentDummyMarkedExperiment (B := B) E).posterior
        (independentDummyPrior q r) z =
      prodDist (E.posterior q z) r := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  change Channel.posterior
      (independentDummyChannel (B := B) E.K) (prodDist q r) z =
    prodDist (Channel.posterior E.K q z) r
  have hout :
      Channel.outcomeMarginal
          (independentDummyChannel (B := B) E.K) (prodDist q r) z =
        Channel.outcomeMarginal E.K q z := by
    exact independentDummyMarkedExperiment_outcomeMarginal q r E z
  have hprod :
      0 < Channel.outcomeMarginal
        (independentDummyChannel (B := B) E.K) (prodDist q r) z := by
    rw [hout]
    exact hz
  ext ab
  rcases ab with ⟨a, b⟩
  have hleft :
      Channel.posterior
          (independentDummyChannel (B := B) E.K) (prodDist q r) z (a, b) =
        (prodDist q r (a, b) *
            independentDummyChannel (B := B) E.K (a, b) z) /
          Channel.outcomeMarginal
            (independentDummyChannel (B := B) E.K) (prodDist q r) z := by
    unfold Channel.posterior
    rw [dif_pos hprod]
  have hright :
      Channel.posterior E.K q z a =
        q a * E.K a z / Channel.outcomeMarginal E.K q z := by
    have hz' : 0 < Channel.outcomeMarginal E.K q z := hz
    simp only [Channel.posterior, dif_pos hz']
  rw [hleft, hout]
  simp only [prodDist_apply_pair]
  rw [hright]
  simp only [independentDummyChannel]
  ring

/-- Integral identity for dummy lifting.  It is formulated directly at the
law level so arbitrary posteriors on null records disappear by multiplication
with zero. -/
theorem markedTerminalIntegral_independentDummy
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O A)
    (phi : O × TraceableAgency.Dist (A × B) → ℝ) :
    markedTerminalIntegral (independentDummyPrior q r)
        (independentDummyMarkedExperiment (B := B) E) phi =
      markedTerminalIntegral q E
        (fun op ↦ phi (op.1, prodDist op.2 r)) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  unfold markedTerminalIntegral
  apply Finset.sum_congr rfl
  intro z _hzmem
  rw [independentDummyMarkedExperiment_outcomeMarginal q r E z]
  by_cases hz : 0 < E.outcomeMarginal q z
  · rw [independentDummyMarkedExperiment_posterior_of_pos q r E z hz]
  · have hz0 : E.outcomeMarginal q z = 0 :=
      le_antisymm (le_of_not_gt hz) ((E.outcomeMarginal q).nonneg z)
    simp [hz0]

/-- Marked-terminal-law equality is preserved by adjoining the same
independent dummy prior. -/
theorem sameMarkedTerminalLaw_independentDummy
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    {E G : MarkedTerminalExperiment O A}
    (hsame : SameMarkedTerminalLaw q E G) :
    SameMarkedTerminalLaw (independentDummyPrior q r)
      (independentDummyMarkedExperiment (B := B) E)
      (independentDummyMarkedExperiment (B := B) G) := by
  intro phi
  rw [markedTerminalIntegral_independentDummy,
    markedTerminalIntegral_independentDummy]
  exact hsame (fun op ↦ phi (op.1, prodDist op.2 r))

/-! ## Right-coordinate dummy transport -/

/-- Bundle the right-coordinate lift of a marked experiment. -/
noncomputable def rightIndependentDummyMarkedExperiment
    {O A B : Type u}
    [Fintype O] [Fintype A] [Fintype B]
    (E : MarkedTerminalExperiment O B) :
    MarkedTerminalExperiment O (A × B) where
  RecordType := E.RecordType
  recordFintype := E.recordFintype
  recordDecEq := E.recordDecEq
  recordNonempty := E.recordNonempty
  channel := by
    letI : Fintype E.RecordType := E.recordFintype
    exact rightIndependentDummyChannel (A := A) E.K

theorem rightIndependentDummyMarkedExperiment_outcomeMarginal
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O B) (z : O × E.RecordType) :
    (rightIndependentDummyMarkedExperiment (A := A) E).outcomeMarginal
        (prodDist q p) z = E.outcomeMarginal p z := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  unfold MarkedTerminalExperiment.outcomeMarginal
  simp only [Channel.outcomeMarginal_apply, rightIndependentDummyChannel]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  calc
    (∑ a, prodDist q p (a, b) * E.K b z) =
        (∑ a, q a) * (p b * E.K b z) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [prodDist_apply_pair]
      ring
    _ = p b * E.K b z := by rw [q.sum_eq_one, one_mul]

theorem rightIndependentDummyMarkedExperiment_posterior_of_pos
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O B) (z : O × E.RecordType)
    (hz : 0 < E.outcomeMarginal p z) :
    (rightIndependentDummyMarkedExperiment (A := A) E).posterior
        (prodDist q p) z = prodDist q (E.posterior p z) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  change Channel.posterior
      (rightIndependentDummyChannel (A := A) E.K) (prodDist q p) z =
    prodDist q (Channel.posterior E.K p z)
  have hout :
      Channel.outcomeMarginal
          (rightIndependentDummyChannel (A := A) E.K) (prodDist q p) z =
        Channel.outcomeMarginal E.K p z := by
    exact rightIndependentDummyMarkedExperiment_outcomeMarginal q p E z
  have hprod :
      0 < Channel.outcomeMarginal
        (rightIndependentDummyChannel (A := A) E.K) (prodDist q p) z := by
    rw [hout]
    exact hz
  ext ab
  rcases ab with ⟨a, b⟩
  have hleft :
      Channel.posterior
          (rightIndependentDummyChannel (A := A) E.K) (prodDist q p) z (a, b) =
        (prodDist q p (a, b) *
            rightIndependentDummyChannel (A := A) E.K (a, b) z) /
          Channel.outcomeMarginal
            (rightIndependentDummyChannel (A := A) E.K) (prodDist q p) z := by
    unfold Channel.posterior
    rw [dif_pos hprod]
  have hright :
      Channel.posterior E.K p z b =
        p b * E.K b z / Channel.outcomeMarginal E.K p z := by
    have hz' : 0 < Channel.outcomeMarginal E.K p z := hz
    simp only [Channel.posterior, dif_pos hz']
  rw [hleft, hout]
  simp only [prodDist_apply_pair]
  rw [hright]
  simp only [rightIndependentDummyChannel]
  ring

theorem markedTerminalIntegral_rightIndependentDummy
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B)
    (E : MarkedTerminalExperiment O B)
    (phi : O × TraceableAgency.Dist (A × B) → ℝ) :
    markedTerminalIntegral (prodDist q p)
        (rightIndependentDummyMarkedExperiment (A := A) E) phi =
      markedTerminalIntegral p E
        (fun op ↦ phi (op.1, prodDist q op.2)) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  unfold markedTerminalIntegral
  apply Finset.sum_congr rfl
  intro z _hzmem
  rw [rightIndependentDummyMarkedExperiment_outcomeMarginal q p E z]
  by_cases hz : 0 < E.outcomeMarginal p z
  · rw [rightIndependentDummyMarkedExperiment_posterior_of_pos q p E z hz]
  · have hz0 : E.outcomeMarginal p z = 0 :=
      le_antisymm (le_of_not_gt hz) ((E.outcomeMarginal p).nonneg z)
    simp [hz0]

theorem sameMarkedTerminalLaw_rightIndependentDummy
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B)
    {E G : MarkedTerminalExperiment O B}
    (hsame : SameMarkedTerminalLaw p E G) :
    SameMarkedTerminalLaw (prodDist q p)
      (rightIndependentDummyMarkedExperiment (A := A) E)
      (rightIndependentDummyMarkedExperiment (A := A) G) := by
  intro phi
  rw [markedTerminalIntegral_rightIndependentDummy,
    markedTerminalIntegral_rightIndependentDummy]
  exact hsame (fun op ↦ phi (op.1, prodDist q op.2))

end TraceTemperedChoiceVerification
