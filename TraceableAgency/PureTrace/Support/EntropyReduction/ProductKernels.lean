/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.ProductLifts

namespace TraceableAgency

universe u

/-!
## Product projection and embedding kernels
-/

/-- Projection kernel `(a, b) ↦ a`. -/
noncomputable def fstProjectionKernel
    {A B : Type u} [Fintype A] [DecidableEq A] :
    Channel.ActionKernel (A × B) A :=
  fun ab => Dist.pure ab.1

/-- Projection kernel `(a, b) ↦ b`. -/
noncomputable def sndProjectionKernel
    {A B : Type u} [Fintype B] [DecidableEq B] :
    Channel.ActionKernel (A × B) B :=
  fun ab => Dist.pure ab.2

/-- Embedding kernel `a ↦ (a, b)` with background draw `b ~ r`. -/
noncomputable def leftEmbedKernel
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    (r : Dist B) : Channel.ActionKernel A (A × B) :=
  fun a => prodDist (Dist.pure a) r

/-- Embedding kernel `b ↦ (a, b)` with background draw `a ~ q`. -/
noncomputable def rightEmbedKernel
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (q : Dist A) : Channel.ActionKernel B (A × B) :=
  fun b => prodDist q (Dist.pure b)

/-- Outcome relabeling kernel `o ↦ (o, *)`. -/
noncomputable def outcomeRightUnitKernel
    {O : Type u} [Fintype O] [DecidableEq O] :
    Channel O (O × PUnit.{u + 1}) :=
  fun o => Dist.pure (o, PUnit.unit)

/-- Outcome projection kernel `(o, *) ↦ o`. -/
noncomputable def outcomeRightUnitProjectKernel
    {O : Type u} [Fintype O] [DecidableEq O] :
    Channel (O × PUnit.{u + 1}) O :=
  fun ou => Dist.pure ou.1

/-- Outcome relabeling kernel `y ↦ (*, y)`. -/
noncomputable def outcomeLeftUnitKernel
    {Y : Type u} [Fintype Y] [DecidableEq Y] :
    Channel Y (PUnit.{u + 1} × Y) :=
  fun y => Dist.pure (PUnit.unit, y)

/-- Outcome projection kernel `(*, y) ↦ y`. -/
noncomputable def outcomeLeftUnitProjectKernel
    {Y : Type u} [Fintype Y] [DecidableEq Y] :
    Channel (PUnit.{u + 1} × Y) Y :=
  fun uy => Dist.pure uy.2

/-- Copy a channel into the outcome type `O × PUnit`. -/
noncomputable def leftUnitOutcomeChannel
    {A O : Type u} [Fintype O] [DecidableEq O]
    (P : Channel A O) : Channel A (O × PUnit.{u + 1}) :=
  fun a => prodDist (P a) (Dist.pure PUnit.unit)

/-- Copy a channel into the outcome type `PUnit × Y`. -/
noncomputable def rightUnitOutcomeChannel
    {B Y : Type u} [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) : Channel B (PUnit.{u + 1} × Y) :=
  fun b => prodDist (Dist.pure PUnit.unit) (Q b)

@[simp]
theorem leftUnitOutcomeChannel_apply
    {A O : Type u} [Fintype O] [DecidableEq O]
    (P : Channel A O) (a : A) (o : O) :
    leftUnitOutcomeChannel P a (o, PUnit.unit) = P a o := by
  simp [leftUnitOutcomeChannel]

@[simp]
theorem rightUnitOutcomeChannel_apply
    {B Y : Type u} [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (b : B) (y : Y) :
    rightUnitOutcomeChannel Q b (PUnit.unit, y) = Q b y := by
  simp [rightUnitOutcomeChannel]

theorem postprocess_outcomeRightUnit_eq_leftUnitOutcome
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) :
    Channel.postprocess P outcomeRightUnitKernel =
      leftUnitOutcomeChannel P := by
  ext a ou
  rcases ou with ⟨o, u⟩
  cases u
  unfold Channel.postprocess outcomeRightUnitKernel leftUnitOutcomeChannel
  change (∑ o' : O, P a o' * Dist.pure (o', PUnit.unit) (o, PUnit.unit)) =
    (prodDist (P a) (Dist.pure PUnit.unit)) (o, PUnit.unit)
  rw [Fintype.sum_eq_single o]
  · simp
  · intro o' ho'ne
    have hne :
        (o', (PUnit.unit : PUnit.{u + 1})) ≠
          (o, (PUnit.unit : PUnit.{u + 1})) := by
      intro h
      exact ho'ne (Prod.ext_iff.mp h).1
    have hpure :
        (Dist.pure (o', (PUnit.unit : PUnit.{u + 1})) :
          Dist (O × PUnit.{u + 1})) (o, PUnit.unit) = 0 :=
      Dist.pure_apply_ne _ _ hne.symm
    rw [hpure]
    ring

theorem postprocess_leftUnitOutcome_project_eq
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) :
    Channel.postprocess (leftUnitOutcomeChannel P) outcomeRightUnitProjectKernel =
      P := by
  ext a o
  unfold Channel.postprocess outcomeRightUnitProjectKernel
  change (∑ ou : O × PUnit.{u + 1},
      leftUnitOutcomeChannel P a ou * Dist.pure ou.1 o) = P a o
  rw [Fintype.sum_prod_type]
  simp [leftUnitOutcomeChannel, prodDist_apply_pair]
  rw [Fintype.sum_eq_single o]
  · simp
  · intro x hxne
    have hne : o ≠ x := fun h => hxne h.symm
    simp [Dist.pure_apply_ne _ _ hne]

theorem postprocess_outcomeLeftUnit_eq_rightUnitOutcome
    {B Y : Type u} [Fintype B] [DecidableEq B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) :
    Channel.postprocess Q outcomeLeftUnitKernel =
      rightUnitOutcomeChannel Q := by
  ext b uy
  rcases uy with ⟨u, y⟩
  cases u
  unfold Channel.postprocess outcomeLeftUnitKernel rightUnitOutcomeChannel
  change (∑ y' : Y, Q b y' * Dist.pure (PUnit.unit, y') (PUnit.unit, y)) =
    (prodDist (Dist.pure PUnit.unit) (Q b)) (PUnit.unit, y)
  rw [Fintype.sum_eq_single y]
  · simp
  · intro y' hy'ne
    have hne :
        ((PUnit.unit : PUnit.{u + 1}), y') ≠
          ((PUnit.unit : PUnit.{u + 1}), y) := by
      intro h
      exact hy'ne (Prod.ext_iff.mp h).2
    have hpure :
        (Dist.pure ((PUnit.unit : PUnit.{u + 1}), y') :
          Dist (PUnit.{u + 1} × Y)) (PUnit.unit, y) = 0 :=
      Dist.pure_apply_ne _ _ hne.symm
    rw [hpure]
    ring

theorem postprocess_rightUnitOutcome_project_eq
    {B Y : Type u} [Fintype B] [DecidableEq B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) :
    Channel.postprocess (rightUnitOutcomeChannel Q) outcomeLeftUnitProjectKernel =
      Q := by
  ext b y
  unfold Channel.postprocess outcomeLeftUnitProjectKernel
  change (∑ uy : PUnit.{u + 1} × Y,
      rightUnitOutcomeChannel Q b uy * Dist.pure uy.2 y) = Q b y
  rw [Fintype.sum_prod_type]
  simp [rightUnitOutcomeChannel, prodDist_apply_pair]
  rw [Fintype.sum_eq_single y]
  · simp
  · intro x hxne
    have hne : y ≠ x := fun h => hxne h.symm
    simp [Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_prod_fst
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward (prodDist q r) (fstProjectionKernel (A := A) (B := B)) = q := by
  ext a
  change (∑ ab : A × B, (prodDist q r) ab * Dist.pure ab.1 a) = q a
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single a]
  · simp [prodDist_apply_pair, ← Finset.mul_sum, r.sum_eq_one]
  · intro a' ha'ne
    apply Finset.sum_eq_zero
    intro b _
    have hne : a ≠ a' := fun h => ha'ne h.symm
    simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_prod_snd
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward (prodDist q r) (sndProjectionKernel (A := A) (B := B)) = r := by
  ext b
  change (∑ ab : A × B, (prodDist q r) ab * Dist.pure ab.2 b) = r b
  rw [Fintype.sum_prod_type]
  simp_rw [prodDist_apply_pair]
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single b]
  · simp only [Dist.pure_apply_self, mul_one]
    calc
      (∑ i : A, q i * r b) = (∑ i : A, q i) * r b := by
        rw [Finset.sum_mul]
      _ = r b := by
        rw [q.sum_eq_one, one_mul]
  · intro b' hb'ne
    apply Finset.sum_eq_zero
    intro a _
    have hne : b ≠ b' := fun h => hb'ne h.symm
    simp [Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_leftEmbed
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward q (leftEmbedKernel (A := A) r) = prodDist q r := by
  ext ab
  rcases ab with ⟨a, b⟩
  change (∑ a' : A, q a' * prodDist (Dist.pure a') r (a, b)) =
    prodDist q r (a, b)
  rw [Fintype.sum_eq_single a]
  · simp [prodDist_apply_pair]
  · intro a' ha'ne
    have hne : a ≠ a' := fun h => ha'ne h.symm
    simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_rightEmbed
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward r (rightEmbedKernel (B := B) q) = prodDist q r := by
  ext ab
  rcases ab with ⟨a, b⟩
  change (∑ b' : B, r b' * prodDist q (Dist.pure b') (a, b)) =
    prodDist q r (a, b)
  rw [Fintype.sum_eq_single b]
  · simp [prodDist_apply_pair, mul_comm]
  · intro b' hb'ne
    have hne : b ≠ b' := fun h => hb'ne h.symm
    simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]

theorem leftProductLift_isBayesPushforwardCompletion_fst
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (leftProductLiftChannel (B := B) P)
      (prodDist q r)
      (fstProjectionKernel (A := A) (B := B))
      (leftUnitOutcomeChannel P) := by
  intro a ha ou
  rcases ou with ⟨o, u⟩
  cases u
  have hpush := congrArg (fun d : Dist A => d a) (actionPushforward_prod_fst q r)
  have hqa : q a > 0 := by simpa [hpush] using ha
  have hnum :
      (∑ ab : A × B,
          prodDist q r ab * Dist.pure ab.1 a *
            leftProductLiftChannel (B := B) P ab (o, PUnit.unit)) =
        q a * P a o := by
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single a]
    · simp only [leftProductLiftChannel, prodDist_apply_pair, prodChannel_apply_pair,
        Channel.uninformativeChannelU, Dist.pure_apply_self, mul_one]
      have hsum :
          (∑ x : B, q a * r x * P a o) =
          (q a * P a o) * (∑ x : B, r x) := by
        simp_rw [show ∀ x : B, q a * r x * P a o = r x * (q a * P a o) by
          intro x
          ring]
        calc
          (∑ x : B, r x * (q a * P a o)) =
              (∑ x : B, r x) * (q a * P a o) := by
            rw [Finset.sum_mul]
          _ = (q a * P a o) * (∑ x : B, r x) := by
            ring
      rw [hsum, r.sum_eq_one]
      ring
    · intro a' ha'ne
      apply Finset.sum_eq_zero
      intro b _
      have hne : a ≠ a' := fun h => ha'ne h.symm
      simp [leftProductLiftChannel, prodDist_apply_pair, prodChannel_apply_pair,
        Dist.pure_apply_ne _ _ hne]
  change leftUnitOutcomeChannel P a (o, PUnit.unit) =
    (∑ ab : A × B,
        prodDist q r ab * Dist.pure ab.1 a *
          leftProductLiftChannel (B := B) P ab (o, PUnit.unit)) /
      (Channel.actionPushforward (prodDist q r) (fstProjectionKernel (A := A) (B := B))) a
  rw [hnum, hpush]
  simp [hqa.ne']

theorem rightProductLift_isBayesPushforwardCompletion_snd
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (rightProductLiftChannel (A := A) Q)
      (prodDist q r)
      (sndProjectionKernel (A := A) (B := B))
      (rightUnitOutcomeChannel Q) := by
  intro b hb uy
  rcases uy with ⟨u, y⟩
  cases u
  have hpush := congrArg (fun d : Dist B => d b) (actionPushforward_prod_snd q r)
  have hrb : r b > 0 := by simpa [hpush] using hb
  have hnum :
      (∑ ab : A × B,
          prodDist q r ab * Dist.pure ab.2 b *
            rightProductLiftChannel (A := A) Q ab (PUnit.unit, y)) =
        r b * Q b y := by
    rw [Fintype.sum_prod_type]
    simp_rw [prodDist_apply_pair]
    rw [Finset.sum_comm]
    rw [Fintype.sum_eq_single b]
    · simp only [rightProductLiftChannel, prodChannel_apply_pair,
        Channel.uninformativeChannelU, Dist.pure_apply_self, one_mul, mul_one]
      calc
        (∑ i : A, q i * r b * Q b y) =
            (∑ i : A, q i) * (r b * Q b y) := by
          simp_rw [show ∀ i : A, q i * r b * Q b y = q i * (r b * Q b y) by
            intro i
            ring]
          rw [Finset.sum_mul]
        _ = r b * Q b y := by
          rw [q.sum_eq_one, one_mul]
    · intro b' hb'ne
      apply Finset.sum_eq_zero
      intro a _
      have hne : b ≠ b' := fun h => hb'ne h.symm
      simp [rightProductLiftChannel, prodChannel_apply_pair,
        Dist.pure_apply_ne _ _ hne]
  change rightUnitOutcomeChannel Q b (PUnit.unit, y) =
    (∑ ab : A × B,
        prodDist q r ab * Dist.pure ab.2 b *
          rightProductLiftChannel (A := A) Q ab (PUnit.unit, y)) /
      (Channel.actionPushforward (prodDist q r) (sndProjectionKernel (A := A) (B := B))) b
  rw [hnum, hpush]
  simp [hrb.ne']

theorem leftUnitOutcome_isBayesPushforwardCompletion_leftEmbed
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (leftUnitOutcomeChannel P)
      q
      (leftEmbedKernel (A := A) r)
      (leftProductLiftChannel (B := B) P) := by
  intro ab hab ou
  rcases ab with ⟨a, b⟩
  rcases ou with ⟨o, u⟩
  cases u
  have hpush := congrArg (fun d : Dist (A × B) => d (a, b))
    (actionPushforward_leftEmbed q r)
  have hprod : q a * r b > 0 := by simpa [hpush, prodDist_apply_pair] using hab
  have hnum :
      (∑ a' : A,
          q a' * prodDist (Dist.pure a') r (a, b) *
            leftUnitOutcomeChannel P a' (o, PUnit.unit)) =
        q a * r b * P a o := by
    rw [Fintype.sum_eq_single a]
    · simp [prodDist_apply_pair, mul_assoc]
    · intro a' ha'ne
      have hne : a ≠ a' := fun h => ha'ne h.symm
      simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]
  change leftProductLiftChannel (B := B) P (a, b) (o, PUnit.unit) =
    (∑ a' : A,
        q a' * prodDist (Dist.pure a') r (a, b) *
          leftUnitOutcomeChannel P a' (o, PUnit.unit)) /
      (Channel.actionPushforward q (leftEmbedKernel (A := A) r)) (a, b)
  rw [hnum, hpush]
  simp [leftProductLiftChannel, prodChannel_apply_pair, Channel.uninformativeChannelU,
    prodDist_apply_pair, hprod.ne']

theorem rightUnitOutcome_isBayesPushforwardCompletion_rightEmbed
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (rightUnitOutcomeChannel Q)
      r
      (rightEmbedKernel (B := B) q)
      (rightProductLiftChannel (A := A) Q) := by
  intro ab hab uy
  rcases ab with ⟨a, b⟩
  rcases uy with ⟨u, y⟩
  cases u
  have hpush := congrArg (fun d : Dist (A × B) => d (a, b))
    (actionPushforward_rightEmbed q r)
  have hprod : q a * r b > 0 := by simpa [hpush, prodDist_apply_pair] using hab
  have hnum :
      (∑ b' : B,
          r b' * prodDist q (Dist.pure b') (a, b) *
            rightUnitOutcomeChannel Q b' (PUnit.unit, y)) =
        q a * r b * Q b y := by
    rw [Fintype.sum_eq_single b]
    · simp [prodDist_apply_pair, mul_comm, mul_assoc]
    · intro b' hb'ne
      have hne : b ≠ b' := fun h => hb'ne h.symm
      simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]
  change rightProductLiftChannel (A := A) Q (a, b) (PUnit.unit, y) =
    (∑ b' : B,
        r b' * prodDist q (Dist.pure b') (a, b) *
          rightUnitOutcomeChannel Q b' (PUnit.unit, y)) /
      (Channel.actionPushforward r (rightEmbedKernel (B := B) q)) (a, b)
  rw [hnum, hpush]
  simp only [rightProductLiftChannel, prodChannel_apply_pair, Channel.uninformativeChannelU,
    one_mul]
  field_simp [hprod.ne']
  rw [prodDist_apply_pair]
  ring

end TraceableAgency
