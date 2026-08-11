/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Blocks
import TraceableAgency.Basic.Products

/-!
# Finite relabeling

Definitions and algebraic identities for transporting finite distributions and
channels through equivalences.  This module contains no preference assumptions.
-/

namespace TraceableAgency
namespace Relabeling

universe u

/-- Push a finite distribution forward through a bijection of labels. -/
noncomputable def relabelDist
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) : Dist B where
  prob := fun b => q (e.symm b)
  nonneg := fun b => q.nonneg (e.symm b)
  sum_eq_one := by
    rw [Equiv.sum_comp e.symm (fun a : A => q a)]
    exact q.sum_eq_one

@[simp]
theorem relabelDist_apply
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) (b : B) :
    relabelDist e q b = q (e.symm b) := rfl

@[simp]
theorem relabelDist_refl
    {A : Type u} [Fintype A] (q : Dist A) :
    relabelDist (Equiv.refl A) q = q := by
  ext a
  rfl

/-- Full support is preserved by finite relabeling. -/
theorem relabelDist_fullSupport
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (relabelDist e q).FullSupport := by
  intro b
  exact hq (e.symm b)

/-- Transport both action and outcome labels through bijections. -/
noncomputable def relabelChannel
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) : Channel B Y :=
  fun b => relabelDist eO (P (eA.symm b))

@[simp]
theorem relabelChannel_apply
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) (b : B) (y : Y) :
    relabelChannel eA eO P b y = P (eA.symm b) (eO.symm y) := rfl

@[simp]
theorem relabelChannel_refl_refl
    {A O : Type u} [Fintype A] [Fintype O]
    (P : Channel A O) :
    relabelChannel (Equiv.refl A) (Equiv.refl O) P = P := by
  ext a o
  rfl

@[simp]
theorem relabelDist_symm
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) :
    relabelDist e.symm (relabelDist e q) = q := by
  ext a
  simp [relabelDist]

@[simp]
theorem relabelChannel_symm
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) :
    relabelChannel eA.symm eO.symm (relabelChannel eA eO P) = P := by
  ext a o
  simp [relabelChannel]

@[simp]
theorem relabelChannel_action_then_outcome
    {A B O Y : Type u} [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P : Channel A O) :
    relabelChannel (Equiv.refl B) eO
        (relabelChannel eA (Equiv.refl O) P) =
      relabelChannel eA eO P := by
  ext b y
  rfl

/-- Product distributions commute with componentwise relabeling. -/
theorem relabelDist_prodCongr
    {A B C D : Type u}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (eA : A ≃ B) (eC : C ≃ D) (q : Dist A) (r : Dist C) :
    relabelDist (Equiv.prodCongr eA eC) (prodDist q r) =
      prodDist (relabelDist eA q) (relabelDist eC r) := by
  ext bd
  cases bd with
  | mk b d => rfl

/-- Product channels commute with componentwise action/outcome relabeling. -/
theorem relabelChannel_prodCongr
    {A B C D O Y Z W : Type u}
    [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Fintype O] [Fintype Y] [Fintype Z] [Fintype W]
    (eA : A ≃ B) (eC : C ≃ D) (eO : O ≃ Y) (eZ : Z ≃ W)
    (P : Channel A O) (R : Channel C Z) :
    relabelChannel (Equiv.prodCongr eA eC) (Equiv.prodCongr eO eZ)
        (prodChannel P R) =
      prodChannel (relabelChannel eA eO P) (relabelChannel eC eZ R) := by
  ext bd yw
  cases bd with
  | mk b d =>
      cases yw with
      | mk y w => rfl

/-- Relabeling both copies of a two-block left prior is the left prior of the
relabelled distribution. -/
theorem relabelDist_sumCongr_inl
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (q : Dist A) :
    relabelDist (Equiv.sumCongr e e) (inlDist q : Dist (A ⊕ A)) =
      (inlDist (relabelDist e q) : Dist (B ⊕ B)) := by
  ext x
  cases x with
  | inl b => rfl
  | inr b => rfl

/-- Relabeling both copies of a two-block right prior is the right prior of the
relabelled distribution. -/
theorem relabelDist_sumCongr_inr
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (e : A ≃ B) (q : Dist A) :
    relabelDist (Equiv.sumCongr e e) (inrDist q : Dist (A ⊕ A)) =
      (inrDist (relabelDist e q) : Dist (B ⊕ B)) := by
  ext x
  cases x with
  | inl b => rfl
  | inr b => rfl

/-- Relabeling both sides of a two-block channel relabels the two component
channels. -/
theorem relabel_blockChannel_sumCongr_eq
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y) (P Q : Channel A O) :
    relabelChannel (Equiv.sumCongr eA eA) (Equiv.sumCongr eO eO)
        (blockChannel P Q) =
      blockChannel (relabelChannel eA eO P) (relabelChannel eA eO Q) := by
  ext b y
  cases b with
  | inl b =>
      cases y with
      | inl y => rfl
      | inr y => rfl
  | inr b =>
      cases y with
      | inl y => rfl
      | inr y => rfl

/-- Deterministic outcome relabeling kernel induced by an equivalence. -/
noncomputable def outcomeEquivKernel
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) : Channel O Y :=
  fun o => Dist.pure (e o)

/-- Deterministic action relabeling kernel induced by an equivalence. -/
noncomputable def actionEquivKernel
    {A B : Type u} [Fintype B] [DecidableEq B]
    (e : A ≃ B) : Channel.ActionKernel A B :=
  fun a => Dist.pure (e a)

@[simp]
theorem outcomeEquivKernel_apply
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (o : O) (y : Y) :
    outcomeEquivKernel e o y = if y = e o then 1 else 0 := rfl

@[simp]
theorem actionEquivKernel_apply
    {A B : Type u} [Fintype B] [DecidableEq B]
    (e : A ≃ B) (a : A) (b : B) :
    actionEquivKernel e a b = if b = e a then 1 else 0 := rfl

/-- Postprocessing by a deterministic outcome equivalence is outcome relabeling. -/
theorem postprocess_outcomeEquiv_eq_relabel
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (P : Channel A O) :
    Channel.postprocess P (outcomeEquivKernel eO) =
      relabelChannel (Equiv.refl A) eO P := by
  ext a y
  change (∑ o : O, P a o * Dist.pure (eO o) y) = P a (eO.symm y)
  rw [Fintype.sum_eq_single (eO.symm y)]
  · simp
  · intro o hone
    have hne : y ≠ eO o := by
      intro hy
      apply hone
      exact eO.injective (by simpa using hy.symm)
    simp [Dist.pure_apply_ne _ _ hne]

/-- Reversing a deterministic outcome relabeling recovers the original channel. -/
theorem postprocess_outcomeEquiv_symm_eq_original
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (P : Channel A O) :
    Channel.postprocess (relabelChannel (Equiv.refl A) eO P)
        (outcomeEquivKernel eO.symm) =
      P := by
  rw [postprocess_outcomeEquiv_eq_relabel]
  ext a o
  simp [relabelChannel]

/-- Pushing a prior through a deterministic action equivalence is distribution relabeling. -/
theorem actionPushforward_equiv
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (eA : A ≃ B) (q : Dist A) :
    Channel.actionPushforward q (actionEquivKernel eA) =
      relabelDist eA q := by
  ext b
  change (∑ a : A, q a * Dist.pure (eA a) b) = q (eA.symm b)
  rw [Fintype.sum_eq_single (eA.symm b)]
  · simp
  · intro a hane
    have hne : b ≠ eA a := by
      intro hb
      apply hane
      exact eA.injective (by simpa using hb.symm)
    simp [Dist.pure_apply_ne _ _ hne]

/-- A relabeled channel is the Bayesian pushforward completion under an action equivalence. -/
theorem relabelChannel_isBayesPushforwardCompletion
    {A B O : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (P : Channel A O) (q : Dist A) :
    Channel.IsBayesPushforwardCompletion
      P q (actionEquivKernel eA)
      (relabelChannel eA (Equiv.refl O) P) := by
  intro b hb o
  have hpush := congrArg (fun d : Dist B => d b) (actionPushforward_equiv eA q)
  have hbq : q (eA.symm b) > 0 := by
    simpa [relabelDist] using (by simpa [hpush] using hb)
  have hnum :
      (∑ a : A, q a * Dist.pure (eA a) b * P a o) =
        q (eA.symm b) * P (eA.symm b) o := by
    rw [Fintype.sum_eq_single (eA.symm b)]
    · simp
    · intro a hane
      have hne : b ≠ eA a := by
        intro hb'
        apply hane
        exact eA.injective (by simpa using hb'.symm)
      simp [Dist.pure_apply_ne _ _ hne]
  change P (eA.symm b) o =
    (∑ a : A, q a * Dist.pure (eA a) b * P a o) /
      (Channel.actionPushforward q (actionEquivKernel eA)) b
  rw [hnum, hpush]
  simp [relabelDist, hbq.ne']

/-- Reversing an action relabeling is also a valid Bayesian pushforward completion. -/
theorem relabelChannel_symm_isBayesPushforwardCompletion
    {A B O : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (P : Channel A O) (q : Dist A) :
    Channel.IsBayesPushforwardCompletion
      (relabelChannel eA (Equiv.refl O) P)
      (relabelDist eA q)
      (actionEquivKernel eA.symm)
      P := by
  have h :=
    (relabelChannel_isBayesPushforwardCompletion
      (eA := eA.symm)
      (P := relabelChannel eA (Equiv.refl O) P)
      (q := relabelDist eA q))
  convert h using 1
  ext b o
  simp [relabelChannel]


end Relabeling
end TraceableAgency
