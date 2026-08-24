/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.NormalizedMarked
import TraceableAgency.Theorem1.MarkedTransport

/-!
# Inserting one marked continuation into a reached branch

Fix a full-support prior `q`, a first-stage experiment `P`, and a reached
branch `target` whose posterior is again full support.  A marked experiment at
that posterior can be inserted into `target`, while every other branch is
completed by a deterministic, uninformative baseline payoff.  This file proves
that insertion descends to marked terminal laws, is affine, and is an exact
order embedding.  Only the full-support local-posterior case is treated here.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-! ## Representative-level insertion -/

/-- Relabeling only the explicit record leaves the integral of
`(payoff, posterior)` unchanged. -/
theorem markedChannelIntegral_relabelRecord
    {R S : Type u} [Fintype R] [Fintype S]
    (e : R ≃ S) (q : TraceableAgency.Dist A)
    (K : Channel A (O × R))
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral q
        (Relabeling.relabelChannel (Equiv.refl A)
          (Equiv.prodCongr (Equiv.refl O) e) K) phi =
      markedChannelIntegral q K phi := by
  classical
  unfold markedChannelIntegral
  rw [← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl O) e)]
  apply Finset.sum_congr rfl
  intro z _hz
  rcases z with ⟨o, r⟩
  have hmarg :
      Channel.outcomeMarginal
          (Relabeling.relabelChannel (Equiv.refl A)
            (Equiv.prodCongr (Equiv.refl O) e) K) q
          ((Equiv.prodCongr (Equiv.refl O) e) (o, r)) =
        Channel.outcomeMarginal K q (o, r) := by
    simp [Channel.outcomeMarginal_apply, Relabeling.relabelChannel,
      Relabeling.relabelDist]
  have hpost :
      Channel.posterior
          (Relabeling.relabelChannel (Equiv.refl A)
            (Equiv.prodCongr (Equiv.refl O) e) K) q
          ((Equiv.prodCongr (Equiv.refl O) e) (o, r)) =
        Channel.posterior K q (o, r) := by
    by_cases hp : Channel.outcomeMarginal K q (o, r) > 0
    · have hp' :
          Channel.outcomeMarginal
              (Relabeling.relabelChannel (Equiv.refl A)
                (Equiv.prodCongr (Equiv.refl O) e) K) q
              ((Equiv.prodCongr (Equiv.refl O) e) (o, r)) > 0 := by
        simpa only [hmarg] using hp
      unfold Channel.posterior
      simp only [dif_pos hp, dif_pos hp']
      apply TraceableAgency.Dist.ext
      intro a
      simp [hmarg, Relabeling.relabelChannel, Relabeling.relabelDist]
    · have hp' : ¬
          Channel.outcomeMarginal
              (Relabeling.relabelChannel (Equiv.refl A)
                (Equiv.prodCongr (Equiv.refl O) e) K) q
              ((Equiv.prodCongr (Equiv.refl O) e) (o, r)) > 0 := by
        simpa only [hmarg] using hp
      unfold Channel.posterior
      simp only [dif_neg hp, dif_neg hp']
  rw [hmarg, hpost]
  rfl

/-- The branch-dependent record alphabet: the inserted experiment's record at
`target`, and a singleton record at every other branch. -/
def branchInsertionRecord
    (target : Y) (E : MarkedTerminalExperiment O A) (y : Y) : Type u :=
  if y = target then E.RecordType else PUnit.{u + 1}

noncomputable instance branchInsertionRecord.instFintype
    (target : Y) (E : MarkedTerminalExperiment O A) (y : Y) :
    Fintype (branchInsertionRecord target E y) := by
  classical
  by_cases hy : y = target
  · subst y
    simpa [branchInsertionRecord] using E.recordFintype
  · simpa [branchInsertionRecord, hy] using
      (inferInstance : Fintype PUnit.{u + 1})

noncomputable instance branchInsertionRecord.instDecidableEq
    (target : Y) (E : MarkedTerminalExperiment O A) (y : Y) :
    DecidableEq (branchInsertionRecord target E y) := by
  classical
  by_cases hy : y = target
  · subst y
    simpa [branchInsertionRecord] using E.recordDecEq
  · simpa [branchInsertionRecord, hy] using
      (inferInstance : DecidableEq PUnit.{u + 1})

noncomputable instance branchInsertionRecord.instNonempty
    (target : Y) (E : MarkedTerminalExperiment O A) (y : Y) :
    Nonempty (branchInsertionRecord target E y) := by
  classical
  by_cases hy : y = target
  · subst y
    simpa [branchInsertionRecord] using E.recordNonempty
  · simpa [branchInsertionRecord, hy] using
      (inferInstance : Nonempty PUnit.{u + 1})

/-- The continuation profile used by branch insertion. -/
noncomputable def branchInsertionContinuation
    (target : Y) (o0 : O) (E : MarkedTerminalExperiment O A) :
    ∀ y, Channel A (O × branchInsertionRecord target E y) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  intro y
  by_cases hy : y = target
  · subst y
    let hRec : E.RecordType = branchInsertionRecord target E target := by
      simp [branchInsertionRecord]
    exact Relabeling.relabelChannel (Equiv.refl A)
      (Equiv.prodCongr (Equiv.refl O) (Equiv.cast hRec)) E.K
  · let hRec : PUnit.{u + 1} = branchInsertionRecord target E y := by
      simp [branchInsertionRecord, hy]
    exact Relabeling.relabelChannel (Equiv.refl A)
      (Equiv.prodCongr (Equiv.refl O) (Equiv.cast hRec))
      (uninformativeAtPayoff (A := A) o0)

/-- Insert `E` after `target` and use payoff `o0` with an uninformative record
after every other first-stage outcome. -/
noncomputable def branchInsertionExperiment
    (P : Channel A Y) (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O A) : MarkedTerminalExperiment O A where
  RecordType := (y : Y) × branchInsertionRecord target E y
  recordFintype := inferInstance
  recordDecEq := inferInstance
  recordNonempty := inferInstance
  channel := commonPayoffCompound (branchInsertionRecord target E) P
    (branchInsertionContinuation target o0 E)

/-- At the distinguished branch, insertion has exactly the source marked
terminal law. -/
theorem markedChannelIntegral_branchInsertionContinuation_target
    (r : TraceableAgency.Dist A) (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O A)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral r
        (branchInsertionContinuation target o0 E target) phi =
      markedTerminalIntegral r E phi := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  unfold branchInsertionContinuation
  simp only [eq_self, dite_true]
  rw [markedChannelIntegral_relabelRecord]
  rfl

/-- Away from the distinguished branch, insertion has exactly the baseline
marked terminal law. -/
theorem markedChannelIntegral_branchInsertionContinuation_of_ne
    (r : TraceableAgency.Dist A) (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O A) (y : Y) (hy : y ≠ target)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral r
        (branchInsertionContinuation target o0 E y) phi =
      markedChannelIntegral r
        (uninformativeAtPayoff (A := A) o0) phi := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  unfold branchInsertionContinuation
  simp only [dif_neg hy]
  rw [markedChannelIntegral_relabelRecord]

/-! A common-record variant used to compare two inserted representatives.
Its target alphabet is supplied independently of a bundled experiment, so
two padded channels can literally share one dependent record family in the
finite-branch form of A8. -/

private theorem markedChannelIntegral_uninformativeAtPayoff_forInsertion
    (r : TraceableAgency.Dist A) (o : O)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral r (uninformativeAtPayoff (A := A) o) phi =
      phi (o, r) := by
  classical
  unfold markedChannelIntegral
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  rw [Finset.sum_eq_single o]
  · have hmarg : Channel.outcomeMarginal
        (uninformativeAtPayoff (A := A) o) r (o, PUnit.unit) = 1 := by
      simp [Channel.outcomeMarginal_apply, uninformativeAtPayoff,
        ← Finset.sum_mul, r.sum_eq_one]
    have hpost : Channel.posterior
        (uninformativeAtPayoff (A := A) o) r (o, PUnit.unit) = r := by
      have hp : 0 < Channel.outcomeMarginal
          (uninformativeAtPayoff (A := A) o) r (o, PUnit.unit) := by
        rw [hmarg]
        norm_num
      apply TraceableAgency.Dist.ext
      intro a
      unfold Channel.posterior
      rw [dif_pos hp]
      simp [uninformativeAtPayoff, Channel.outcomeMarginal_apply,
        ← Finset.sum_mul, r.sum_eq_one]
    rw [hmarg, hpost, one_mul]
  · intro o' _ho' hne
    simp [Channel.outcomeMarginal_apply, uninformativeAtPayoff, hne]
  · simp

abbrev branchInsertionCommonRecord
    (_target : Y) (R : Type u) (_y : Y) : Type u := R

/-- A deterministic payoff with an arbitrary fixed record in `R`.  The record
is action independent, so its marked posterior is the incoming prior. -/
noncomputable def branchInsertionCommonBaseline
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (o0 : O) : Channel A (O × R) :=
  fun _ => TraceableAgency.Dist.pure
    (o0, Classical.choice (inferInstance : Nonempty R))

noncomputable def branchInsertionCommonContinuation
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (target : Y) (o0 : O) (K : Channel A (O × R)) :
    ∀ y, Channel A (O × branchInsertionCommonRecord target R y) := by
  classical
  intro y
  by_cases hy : y = target
  · simpa only [branchInsertionCommonRecord] using K
  · simpa only [branchInsertionCommonRecord] using
      (branchInsertionCommonBaseline (A := A) (R := R) o0)

theorem markedChannelIntegral_branchInsertionCommonContinuation_target
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (r : TraceableAgency.Dist A) (target : Y) (o0 : O)
    (K : Channel A (O × R))
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral r
        (branchInsertionCommonContinuation target o0 K target) phi =
      markedChannelIntegral r K phi := by
  classical
  unfold branchInsertionCommonContinuation
  simp only [eq_self, dite_true, id_eq]

theorem markedChannelIntegral_branchInsertionCommonContinuation_of_ne
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (r : TraceableAgency.Dist A) (target : Y) (o0 : O)
    (K : Channel A (O × R)) (y : Y) (hy : y ≠ target)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedChannelIntegral r
        (branchInsertionCommonContinuation target o0 K y) phi =
      markedChannelIntegral r
        (uninformativeAtPayoff (A := A) o0) phi := by
  classical
  unfold branchInsertionCommonContinuation
  simp only [dif_neg hy, id_eq]
  unfold branchInsertionCommonBaseline markedChannelIntegral
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single o0]
  · let r0 : R := Classical.choice (inferInstance : Nonempty R)
    rw [Finset.sum_eq_single r0]
    · have hmarg : Channel.outcomeMarginal
          (fun _ : A => TraceableAgency.Dist.pure (o0, r0)) r (o0, r0) = 1 := by
        simp [Channel.outcomeMarginal_apply, ← Finset.sum_mul,
          r.sum_eq_one]
      have hpost : Channel.posterior
          (fun _ : A => TraceableAgency.Dist.pure (o0, r0)) r (o0, r0) = r := by
        have hp : 0 < Channel.outcomeMarginal
            (fun _ : A => TraceableAgency.Dist.pure (o0, r0)) r
              (o0, r0) := by
          rw [hmarg]
          norm_num
        apply TraceableAgency.Dist.ext
        intro a
        unfold Channel.posterior
        rw [dif_pos hp]
        simp [Channel.outcomeMarginal_apply, ← Finset.sum_mul,
          r.sum_eq_one]
      change Channel.outcomeMarginal
          (fun _ : A => TraceableAgency.Dist.pure (o0, r0)) r (o0, r0) *
          phi (o0, Channel.posterior
            (fun _ : A => TraceableAgency.Dist.pure (o0, r0)) r (o0, r0)) = _
      rw [hmarg, hpost, one_mul]
      exact
        (markedChannelIntegral_uninformativeAtPayoff_forInsertion r o0 phi).symm
    · intro r' _hr' hne
      simp [Channel.outcomeMarginal_apply, r0, hne]
    · simp
  · intro o' _ho' hne
    simp [Channel.outcomeMarginal_apply, hne]
  · simp

/-- Common-record insertion of a raw marked continuation channel. -/
noncomputable def branchInsertionCommonExperiment
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (P : Channel A Y) (target : Y) (o0 : O)
    (K : Channel A (O × R)) : MarkedTerminalExperiment O A where
  RecordType := (y : Y) × branchInsertionCommonRecord target R y
  recordFintype := inferInstance
  recordDecEq := inferInstance
  recordNonempty := inferInstance
  channel := commonPayoffCompound (branchInsertionCommonRecord target R) P
    (branchInsertionCommonContinuation target o0 K)

/-- The common-record and bundled forms of insertion have the same marked
terminal law. -/
theorem sameMarkedTerminalLaw_branchInsertionCommon
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (E : MarkedTerminalExperiment O A) :
    SameMarkedTerminalLaw q
      (by
        letI : Fintype E.RecordType := E.recordFintype
        letI : DecidableEq E.RecordType := E.recordDecEq
        letI : Nonempty E.RecordType := E.recordNonempty
        exact branchInsertionCommonExperiment P target o0 E.K)
      (branchInsertionExperiment P target o0 E) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  intro phi
  change
    markedChannelIntegral q
        (commonPayoffCompound
          (branchInsertionCommonRecord target E.RecordType) P
          (branchInsertionCommonContinuation target o0 E.K)) phi =
      markedChannelIntegral q
        (commonPayoffCompound (branchInsertionRecord target E) P
          (branchInsertionContinuation target o0 E)) phi
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyt : y = target
  · subst y
    rw [markedChannelIntegral_branchInsertionCommonContinuation_target,
      markedChannelIntegral_branchInsertionContinuation_target]
    rfl
  · rw [markedChannelIntegral_branchInsertionCommonContinuation_of_ne
        _ _ _ _ _ hyt,
      markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt]

@[simp]
theorem branchInsertionExperiment_K
    (P : Channel A Y) (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O A) :
    (branchInsertionExperiment P target o0 E).K =
      commonPayoffCompound (branchInsertionRecord target E) P
        (branchInsertionContinuation target o0 E) := rfl

/-- Branch insertion depends only on the source marked terminal law at the
branch posterior. -/
theorem sameMarkedTerminalLaw_branchInsertion
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (E G : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw (branchPosterior P q target) E G) :
    SameMarkedTerminalLaw q
      (branchInsertionExperiment P target o0 E)
      (branchInsertionExperiment P target o0 G) := by
  classical
  intro phi
  change
    markedChannelIntegral q
        (commonPayoffCompound (branchInsertionRecord target E) P
          (branchInsertionContinuation target o0 E)) phi =
      markedChannelIntegral q
        (commonPayoffCompound (branchInsertionRecord target G) P
          (branchInsertionContinuation target o0 G)) phi
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyt : y = target
  · subst y
    rw [markedChannelIntegral_branchInsertionContinuation_target,
      markedChannelIntegral_branchInsertionContinuation_target]
    congr 1
    simpa only [branchPosterior] using hsame phi
  · rw [markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt,
      markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt]

/-! ## Descent to the marked-law quotient -/

/-- Insert a marked terminal law, rather than a chosen representative, into
the distinguished branch. -/
noncomputable def branchInsertionMixtureMap
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) :
    MarkedTerminalMixtureSpace (O := O) (A := A)
        (branchPosterior P q target) →
      MarkedTerminalMixtureSpace (O := O) (A := A) q :=
  Quotient.map
    (branchInsertionExperiment P target o0)
    (fun {_ _} hsame =>
      sameMarkedTerminalLaw_branchInsertion q P target o0 _ _ hsame)

@[simp]
theorem branchInsertionMixtureMap_mk
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (E : MarkedTerminalExperiment O A) :
    branchInsertionMixtureMap q P target o0
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A)
          (branchPosterior P q target)) =
      (⟦branchInsertionExperiment P target o0 E⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) q) := rfl

/-- Representative-level insertion commutes with a public mixture at the
level of marked terminal laws.  Outside `target`, the two identical baseline
copies combine back to one copy. -/
theorem sameMarkedTerminalLaw_branchInsertion_publicMix
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E G : MarkedTerminalExperiment O A) :
    SameMarkedTerminalLaw q
      (branchInsertionExperiment P target o0
        (markedPublicMixExperiment t ht0 ht1 E G))
      (markedPublicMixExperiment t ht0 ht1
        (branchInsertionExperiment P target o0 E)
        (branchInsertionExperiment P target o0 G)) := by
  classical
  intro phi
  change
    markedChannelIntegral q
        (commonPayoffCompound
          (branchInsertionRecord target
            (markedPublicMixExperiment t ht0 ht1 E G)) P
          (branchInsertionContinuation target o0
            (markedPublicMixExperiment t ht0 ht1 E G))) phi =
      markedTerminalIntegral q
        (markedPublicMixExperiment t ht0 ht1
          (branchInsertionExperiment P target o0 E)
          (branchInsertionExperiment P target o0 G)) phi
  rw [markedChannelIntegral_commonPayoffCompound,
    markedTerminalIntegral_publicMix]
  change
    (∑ y : Y, Channel.outcomeMarginal P q y *
      markedChannelIntegral (Channel.posterior P q y)
        (branchInsertionContinuation target o0
          (markedPublicMixExperiment t ht0 ht1 E G) y) phi) =
      t * markedChannelIntegral q
        (commonPayoffCompound (branchInsertionRecord target E) P
          (branchInsertionContinuation target o0 E)) phi +
      (1 - t) * markedChannelIntegral q
        (commonPayoffCompound (branchInsertionRecord target G) P
          (branchInsertionContinuation target o0 G)) phi
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyt : y = target
  · subst y
    rw [markedChannelIntegral_branchInsertionContinuation_target,
      markedTerminalIntegral_publicMix,
      markedChannelIntegral_branchInsertionContinuation_target,
      markedChannelIntegral_branchInsertionContinuation_target]
    ring
  · rw [markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt,
      markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt,
      markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt]
    ring

/-- The quotient insertion map preserves the marked-law mixture operation. -/
theorem branchInsertionMixtureMap_mix
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A)
      (branchPosterior P q target)) :
    branchInsertionMixtureMap q P target o0
        (markedTerminalMixture (branchPosterior P q target) t x y) =
      markedTerminalMixture q t
        (branchInsertionMixtureMap q P target o0 x)
        (branchInsertionMixtureMap q P target o0 y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      apply Quotient.sound
      exact sameMarkedTerminalLaw_branchInsertion_publicMix
        q P target o0 t.1 t.2.1 t.2.2 E G

/-- The same affinity statement in the abstract mixture-space API. -/
theorem branchInsertionMixtureMap_affine
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A)
      (branchPosterior P q target)) :
    branchInsertionMixtureMap q P target o0
        ((markedTerminalAbstractConvexMixtureSpace
          (branchPosterior P q target)).mix t x y) =
      (markedTerminalAbstractConvexMixtureSpace q).mix t
        (branchInsertionMixtureMap q P target o0 x)
        (branchInsertionMixtureMap q P target o0 y) :=
  branchInsertionMixtureMap_mix q P target o0 t x y

/-! ## Exact order embedding -/

/-- Raw same-record core of branch insertion.  This is the direct
finite-branch cancellation lemma and does not require full support of either
prior: the forward direction uses the weak clause, while the reverse direction
uses local completeness and the strict clause at the reached branch. -/
theorem pairWeak_branchInsertionCommon_iff
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (htarget : BranchPositive P q target) (o0 : O)
    (K L : Channel A (O × R)) :
    pairWeak F (branchPosterior P q target) K
        (branchPosterior P q target) L ↔
      MarkedPairWeak F q
        (branchInsertionCommonExperiment P target o0 K) q
        (branchInsertionCommonExperiment P target o0 L) := by
  classical
  let r := branchPosterior P q target
  let Rec := branchInsertionCommonRecord target R
  let QK : ∀ y, Channel A (O × Rec y) :=
    branchInsertionCommonContinuation target o0 K
  let QL : ∀ y, Channel A (O × Rec y) :=
    branchInsertionCommonContinuation target o0 L
  have hbaseline (y : Y) (hy : y ≠ target) : QK y = QL y := by
    dsimp [QK, QL]
    unfold branchInsertionCommonContinuation
    simp only [dif_neg hy]
  constructor
  · intro hKL
    have htargetWeak : pairWeak F r (QK target) r (QL target) := by
      simpa [r, QK, QL, branchInsertionCommonContinuation,
        branchInsertionCommonRecord] using hKL
    have hbranch : ∀ y, BranchPositive P q y →
        pairWeak F (branchPosterior P q y) (QK y)
          (branchPosterior P q y) (QL y) := by
      intro y _hy
      by_cases hyt : y = target
      · subst y
        simpa [r] using htargetWeak
      · rw [← hbaseline y hyt]
        exact pairWeak_refl F h (branchPosterior P q y) (QK y)
    have hraw := h.a6.1 Rec P QK QL q hbranch
    simpa [MarkedPairWeak, Rec, QK, QL,
      branchInsertionCommonExperiment] using hraw
  · intro hins
    have hraw : pairWeak F q (commonPayoffCompound Rec P QK) q
        (commonPayoffCompound Rec P QL) := by
      simpa [MarkedPairWeak, Rec, QK, QL,
        branchInsertionCommonExperiment] using hins
    by_contra hnot
    have hLK : pairWeak F r L r K := by
      rcases pairWeak_complete F h r K r L with hKL | hLK
      · exact False.elim (hnot (by simpa [r] using hKL))
      · simpa [r] using hLK
    have hstrict : pairStrict F r L r K := by
      exact (pairStrict_iff_pairWeak_not_swap
        F h.a1 h.a3 h.a4 h.a5 r L r K).2
          ⟨hLK, by simpa [r] using hnot⟩
    have htargetStrict : pairStrict F r (QL target) r (QK target) := by
      simpa [r, QK, QL, branchInsertionCommonContinuation,
        branchInsertionCommonRecord] using hstrict
    have hbranchRev : ∀ y, BranchPositive P q y →
        pairWeak F (branchPosterior P q y) (QL y)
          (branchPosterior P q y) (QK y) := by
      intro y _hy
      by_cases hyt : y = target
      · subst y
        have hw := (pairStrict_iff_pairWeak_not_swap
          F h.a1 h.a3 h.a4 h.a5 r (QL target) r (QK target)).1
            htargetStrict
        simpa [r] using hw.1
      · rw [← hbaseline y hyt]
        exact pairWeak_refl F h (branchPosterior P q y) (QK y)
    have hstrictRaw := h.a6.2 Rec P QL QK q hbranchRev
      ⟨target, htarget, by simpa [r] using htargetStrict⟩
    have hparts := (pairStrict_iff_pairWeak_not_swap
      F h.a1 h.a3 h.a4 h.a5 q
        (commonPayoffCompound Rec P QL) q
        (commonPayoffCompound Rec P QK)).1 hstrictRaw
    exact hparts.2 hraw

/-- A reached branch with full-support posterior is order-isomorphic to its
image under insertion.  Sum padding gives the finite-branch property one
common target record type; the reverse implication uses completeness locally
and its strict clause. -/
theorem markedPairWeak_branchInsertion_iff
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O) (E G : MarkedTerminalExperiment O A) :
    MarkedPairWeak F (branchPosterior P q target) E
        (branchPosterior P q target) G ↔
      MarkedPairWeak F q (branchInsertionExperiment P target o0 E) q
        (branchInsertionExperiment P target o0 G) := by
  classical
  let r := branchPosterior P q target
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  let Epad := markedPadLeftExperiment E G.RecordType
  let Gpad := markedPadRightExperiment E.RecordType G
  let R := E.RecordType ⊕ G.RecordType
  letI : Fintype R := inferInstance
  letI : DecidableEq R := inferInstance
  letI : Nonempty R := inferInstance
  let Rec := branchInsertionCommonRecord target R
  let QE : ∀ y, Channel A (O × Rec y) :=
    branchInsertionCommonContinuation target o0 Epad.K
  let QG : ∀ y, Channel A (O × Rec y) :=
    branchInsertionCommonContinuation target o0 Gpad.K
  let Ecomp : MarkedTerminalExperiment O A :=
    branchInsertionCommonExperiment P target o0 Epad.K
  let Gcomp : MarkedTerminalExperiment O A :=
    branchInsertionCommonExperiment P target o0 Gpad.K
  let EQtarget : MarkedTerminalExperiment O A :=
    markedExperimentOfChannel (QE target)
  let GQtarget : MarkedTerminalExperiment O A :=
    markedExperimentOfChannel (QG target)
  have hEpad : SameMarkedTerminalLaw r E Epad := by
    exact sameMarkedTerminalLaw_markedPadLeft r E
  have hGpad : SameMarkedTerminalLaw r G Gpad := by
    exact sameMarkedTerminalLaw_markedPadRight r G
  have hEcommon : SameMarkedTerminalLaw q Ecomp
      (branchInsertionExperiment P target o0 Epad) := by
    simpa [Ecomp] using
      (sameMarkedTerminalLaw_branchInsertionCommon
        q P target o0 Epad)
  have hGcommon : SameMarkedTerminalLaw q Gcomp
      (branchInsertionExperiment P target o0 Gpad) := by
    simpa [Gcomp] using
      (sameMarkedTerminalLaw_branchInsertionCommon
        q P target o0 Gpad)
  have hEinsertPad : SameMarkedTerminalLaw q
      (branchInsertionExperiment P target o0 E)
      (branchInsertionExperiment P target o0 Epad) := by
    exact sameMarkedTerminalLaw_branchInsertion
      q P target o0 E Epad hEpad
  have hGinsertPad : SameMarkedTerminalLaw q
      (branchInsertionExperiment P target o0 G)
      (branchInsertionExperiment P target o0 Gpad) := by
    exact sameMarkedTerminalLaw_branchInsertion
      q P target o0 G Gpad hGpad
  have hEcompOriginal : SameMarkedTerminalLaw q Ecomp
      (branchInsertionExperiment P target o0 E) := by
    intro phi
    exact (hEcommon phi).trans (hEinsertPad phi).symm
  have hGcompOriginal : SameMarkedTerminalLaw q Gcomp
      (branchInsertionExperiment P target o0 G) := by
    intro phi
    exact (hGcommon phi).trans (hGinsertPad phi).symm
  have hEQtarget : SameMarkedTerminalLaw r Epad EQtarget := by
    intro phi
    change markedTerminalIntegral r Epad phi =
      markedChannelIntegral r (QE target) phi
    rw [show QE target =
        branchInsertionCommonContinuation target o0 Epad.K target by rfl,
      markedChannelIntegral_branchInsertionCommonContinuation_target]
    rfl
  have hGQtarget : SameMarkedTerminalLaw r Gpad GQtarget := by
    intro phi
    change markedTerminalIntegral r Gpad phi =
      markedChannelIntegral r (QG target) phi
    rw [show QG target =
        branchInsertionCommonContinuation target o0 Gpad.K target by rfl,
      markedChannelIntegral_branchInsertionCommonContinuation_target]
    rfl
  have hpad :
      MarkedPairWeak F r E r G ↔ MarkedPairWeak F r Epad r Gpad :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 r r hr hr E Epad G Gpad hEpad hGpad
  have hcomp :
      MarkedPairWeak F q Ecomp q Gcomp ↔
        MarkedPairWeak F q
          (branchInsertionExperiment P target o0 E) q
          (branchInsertionExperiment P target o0 G) :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 q q hq hq
        Ecomp (branchInsertionExperiment P target o0 E)
        Gcomp (branchInsertionExperiment P target o0 G)
        hEcompOriginal hGcompOriginal
  have htargetIff :
      MarkedPairWeak F r Epad r Gpad ↔
        MarkedPairWeak F r EQtarget r GQtarget :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 r r hr hr
        Epad EQtarget Gpad GQtarget hEQtarget hGQtarget
  have hbaseline (y : Y) (hy : y ≠ target) : QE y = QG y := by
    dsimp [QE, QG]
    unfold branchInsertionCommonContinuation
    simp only [dif_neg hy]
  constructor
  · intro hEG
    have htargetWeak : pairWeak F r (QE target) r (QG target) := by
      have hb := htargetIff.mp (hpad.mp hEG)
      simpa [MarkedPairWeak, EQtarget, GQtarget,
        markedExperimentOfChannel] using hb
    have hbranch : ∀ y, BranchPositive P q y →
        pairWeak F (branchPosterior P q y) (QE y)
          (branchPosterior P q y) (QG y) := by
      intro y _hy
      by_cases hyt : y = target
      · subst y
        simpa [r] using htargetWeak
      · rw [← hbaseline y hyt]
        exact pairWeak_refl F h (branchPosterior P q y) (QE y)
    have hraw := h.a6.1 Rec P QE QG q hbranch
    have hbundled : MarkedPairWeak F q Ecomp q Gcomp := by
      simpa [MarkedPairWeak, Ecomp, Gcomp, Rec, QE, QG,
        branchInsertionCommonExperiment] using hraw
    exact hcomp.mp hbundled
  · intro hins
    have hbundled : MarkedPairWeak F q Ecomp q Gcomp := hcomp.mpr hins
    have hraw : pairWeak F q (commonPayoffCompound Rec P QE)
        q (commonPayoffCompound Rec P QG) := by
      simpa [MarkedPairWeak, Ecomp, Gcomp, Rec, QE, QG,
        branchInsertionCommonExperiment] using hbundled
    by_contra hnot
    have hGE : MarkedPairWeak F r G r E := by
      rcases pairWeak_complete F h r E.K r G.K with hEG | hGE
      · exact False.elim (hnot (by simpa [MarkedPairWeak] using hEG))
      · simpa [MarkedPairWeak] using hGE
    have hGpadEpad : MarkedPairWeak F r Gpad r Epad := by
      exact (pairWeak_respects_sameMarkedTerminalLaw
        F h.a1 h.a3 h.a4 r r hr hr
          G Gpad E Epad hGpad hEpad).mp hGE
    have hnotEpadGpad : ¬ MarkedPairWeak F r Epad r Gpad := by
      intro hp
      exact hnot (hpad.mpr hp)
    have hstrictPad : pairStrict F r Gpad.K r Epad.K := by
      exact (pairStrict_iff_pairWeak_not_swap
        F h.a1 h.a3 h.a4 h.a5 r Gpad.K r Epad.K).2
          ⟨by simpa [MarkedPairWeak] using hGpadEpad,
            by simpa [MarkedPairWeak] using hnotEpadGpad⟩
    have htargetGE : MarkedPairWeak F r GQtarget r EQtarget := by
      exact (pairWeak_respects_sameMarkedTerminalLaw
        F h.a1 h.a3 h.a4 r r hr hr
          Gpad GQtarget Epad EQtarget hGQtarget hEQtarget).mp hGpadEpad
    have hnotTargetEG : ¬ MarkedPairWeak F r EQtarget r GQtarget := by
      intro hp
      exact hnotEpadGpad (htargetIff.mpr hp)
    have hstrictTarget : pairStrict F r (QG target) r (QE target) := by
      apply (pairStrict_iff_pairWeak_not_swap
        F h.a1 h.a3 h.a4 h.a5 r (QG target) r (QE target)).2
      constructor
      · simpa [MarkedPairWeak, EQtarget, GQtarget,
          markedExperimentOfChannel] using htargetGE
      · simpa [MarkedPairWeak, EQtarget, GQtarget,
          markedExperimentOfChannel] using hnotTargetEG
    have hbranchRev : ∀ y, BranchPositive P q y →
        pairWeak F (branchPosterior P q y) (QG y)
          (branchPosterior P q y) (QE y) := by
      intro y _hy
      by_cases hyt : y = target
      · subst y
        have hw := (pairStrict_iff_pairWeak_not_swap
          F h.a1 h.a3 h.a4 h.a5 r (QG target) r (QE target)).1
            hstrictTarget
        simpa [r] using hw.1
      · rw [← hbaseline y hyt]
        exact pairWeak_refl F h (branchPosterior P q y) (QE y)
    have hstrictRaw := h.a6.2 Rec P QG QE q hbranchRev
      ⟨target, htarget, by simpa [r] using hstrictTarget⟩
    have hstrictParts := (pairStrict_iff_pairWeak_not_swap
      F h.a1 h.a3 h.a4 h.a5 q
        (commonPayoffCompound Rec P QG) q
        (commonPayoffCompound Rec P QE)).1 hstrictRaw
    exact hstrictParts.2 hraw

/-- Exact order embedding on the marked-terminal-law quotients. -/
theorem branchInsertionMixtureMap_rel_iff
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A)
      (branchPosterior P q target)) :
    markedTerminalMixtureRel F h (branchPosterior P q target) hr x y ↔
      markedTerminalMixtureRel F h q hq
        (branchInsertionMixtureMap q P target o0 x)
        (branchInsertionMixtureMap q P target o0 y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      simpa [markedTerminalMixtureRel_mk] using
        markedPairWeak_branchInsertion_iff
          F h q hq P target htarget hr o0 E G

/-! ## Affine pullback and its selected positive scale -/

/-- Pull the normalized marked utility on the outer prior back along branch
insertion.  Exact order reflection and public-mixture preservation make this
an affine representation of the local marked order. -/
noncomputable def branchInsertionPullbackAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O) :
    AffineUtilityRepresentation
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A)
        (branchPosterior P q target))
      (markedTerminalMixtureRel (O := O) (A := A) F h
        (branchPosterior P q target) hr) :=
  pullbackAffineUtility
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A)
      (branchPosterior P q target))
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
    (markedTerminalMixtureRel (O := O) (A := A) F h
      (branchPosterior P q target) hr)
    (markedTerminalMixtureRel (O := O) (A := A) F h q hq)
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (branchInsertionMixtureMap q P target o0)
    (branchInsertionMixtureMap_rel_iff
      F h q hq P target htarget hr o0)
    (branchInsertionMixtureMap_affine q P target o0)

/-- The local normalized marked representative is nonconstant, witnessed by
the material high and low anchors. -/
theorem normalizedMarkedAffineUtility_nonconstant
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) (hr : r.FullSupport) :
    ∃ x y : MarkedTerminalMixtureSpace (O := O) (A := A) r,
      (normalizedMarkedAffineUtilityRepresentation F h r hr).utility x ≠
        (normalizedMarkedAffineUtilityRepresentation F h r hr).utility y := by
  let high := markedPayoffLotteryEmbedding (O := O) r
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
  let low := markedPayoffLotteryEmbedding (O := O) r
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
  refine ⟨high, low, ?_⟩
  have hone : (1 : ℝ) ≠ 0 := one_ne_zero
  simpa [high, low] using hone

/-- Positive-affine uniqueness supplies a slope and intercept relating the
outer pullback to the locally normalized marked representative. -/
theorem branchInsertionPullback_positiveAffine_exists
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O) :
    ∃ a b : ℝ, 0 < a ∧
      ∀ x : MarkedTerminalMixtureSpace (O := O) (A := A)
          (branchPosterior P q target),
        (branchInsertionPullbackAffineUtilityRepresentation
          F h q hq P target htarget hr o0).utility x =
          a * (normalizedMarkedAffineUtilityRepresentation F h
            (branchPosterior P q target) hr).utility x + b := by
  exact affineUtilityRepresentation_positiveAffine_unique
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A)
      (branchPosterior P q target))
    (markedTerminalMixtureRel (O := O) (A := A) F h
      (branchPosterior P q target) hr)
    (normalizedMarkedAffineUtilityRepresentation F h
      (branchPosterior P q target) hr)
    (branchInsertionPullbackAffineUtilityRepresentation
      F h q hq P target htarget hr o0)
    (normalizedMarkedAffineUtility_nonconstant F h
      (branchPosterior P q target) hr)

/-- The selected positive slope of the branch-insertion affine pullback. -/
noncomputable def branchInsertionAffineSlope
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O) : ℝ :=
  Classical.choose
    (branchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget hr o0)

/-- The selected intercept paired with `branchInsertionAffineSlope`. -/
noncomputable def branchInsertionAffineIntercept
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O) : ℝ :=
  Classical.choose (Classical.choose_spec
    (branchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget hr o0))

theorem branchInsertionAffineSlope_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O) :
    0 < branchInsertionAffineSlope F h q hq P target htarget hr o0 := by
  have hs := Classical.choose_spec (Classical.choose_spec
    (branchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget hr o0))
  simpa [branchInsertionAffineSlope, branchInsertionAffineIntercept] using hs.1

/-- Pointwise positive-affine formula on the local marked-law quotient. -/
theorem branchInsertionAffineFormula
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O)
    (x : MarkedTerminalMixtureSpace (O := O) (A := A)
      (branchPosterior P q target)) :
    (normalizedMarkedAffineUtilityRepresentation F h q hq).utility
        (branchInsertionMixtureMap q P target o0 x) =
      branchInsertionAffineSlope F h q hq P target htarget hr o0 *
        (normalizedMarkedAffineUtilityRepresentation F h
          (branchPosterior P q target) hr).utility x +
      branchInsertionAffineIntercept F h q hq P target htarget hr o0 := by
  have hs := Classical.choose_spec (Classical.choose_spec
    (branchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget hr o0))
  have hx := hs.2 x
  simpa [branchInsertionPullbackAffineUtilityRepresentation,
    pullbackAffineUtility, branchInsertionAffineSlope,
    branchInsertionAffineIntercept] using hx

/-- The same affine formula specialized to a raw marked experiment. -/
theorem normalizedMarkedUtility_branchInsertion
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target)
    (hr : (branchPosterior P q target).FullSupport)
    (o0 : O) (E : MarkedTerminalExperiment O A) :
    normalizedMarkedUtility F h q hq
        (branchInsertionExperiment P target o0 E) =
      branchInsertionAffineSlope F h q hq P target htarget hr o0 *
        normalizedMarkedUtility F h (branchPosterior P q target) hr E +
      branchInsertionAffineIntercept F h q hq P target htarget hr o0 := by
  simpa [normalizedMarkedUtility] using
    (branchInsertionAffineFormula
      F h q hq P target htarget hr o0
      (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A)
        (branchPosterior P q target)))

end TraceableAgency.Theorem1
