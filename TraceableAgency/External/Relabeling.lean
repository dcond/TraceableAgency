/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Behaviour.Axioms

/-!
# Structural Relabeling Lemmas

Reusable finite relabeling and block-swap plumbing derived from A3/A4/A5 and
A1 transitivity.  These lemmas are kept upstream of the Faddeev files so that
earlier cardinal/value bridges can use Unit/PUnit no-information and block-swap
transfers without importing downstream entropy or Faddeev material.
-/

set_option linter.style.header false

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

/-- Four labels for replacing an environment by an equivalent relabeled copy. -/
inductive RelabelReplacementBlock : Type u
  | oldLeft
  | newLeft
  | oldRight
  | newRight
  deriving DecidableEq, Fintype

open RelabelReplacementBlock

/-- Action alphabets for the common four-block relabeling-replacement environment. -/
def relabelReplacementAct
    (A B : Type u) : RelabelReplacementBlock → Type u
  | oldLeft => A
  | newLeft => B
  | oldRight => A
  | newRight => B

noncomputable instance relabelReplacementActFintype
    {A B : Type u} [Fintype A] [Fintype B] :
    ∀ k : RelabelReplacementBlock, Fintype (relabelReplacementAct A B k)
  | oldLeft => show Fintype A from inferInstance
  | newLeft => show Fintype B from inferInstance
  | oldRight => show Fintype A from inferInstance
  | newRight => show Fintype B from inferInstance

instance relabelReplacementActDecidableEq
    {A B : Type u} [DecidableEq A] [DecidableEq B] :
    ∀ k : RelabelReplacementBlock, DecidableEq (relabelReplacementAct A B k)
  | oldLeft => show DecidableEq A from inferInstance
  | newLeft => show DecidableEq B from inferInstance
  | oldRight => show DecidableEq A from inferInstance
  | newRight => show DecidableEq B from inferInstance

/-- Outcome alphabets for the common four-block relabeling-replacement environment. -/
def relabelReplacementOut
    (O Y : Type u) : RelabelReplacementBlock → Type u
  | oldLeft => O
  | newLeft => Y
  | oldRight => O
  | newRight => Y

noncomputable instance relabelReplacementOutFintype
    {O Y : Type u} [Fintype O] [Fintype Y] :
    ∀ k : RelabelReplacementBlock, Fintype (relabelReplacementOut O Y k)
  | oldLeft => show Fintype O from inferInstance
  | newLeft => show Fintype Y from inferInstance
  | oldRight => show Fintype O from inferInstance
  | newRight => show Fintype Y from inferInstance

instance relabelReplacementOutDecidableEq
    {O Y : Type u} [DecidableEq O] [DecidableEq Y] :
    ∀ k : RelabelReplacementBlock, DecidableEq (relabelReplacementOut O Y k)
  | oldLeft => show DecidableEq O from inferInstance
  | newLeft => show DecidableEq Y from inferInstance
  | oldRight => show DecidableEq O from inferInstance
  | newRight => show DecidableEq Y from inferInstance

/-- Channels for the common four-block relabeling-replacement environment. -/
noncomputable def relabelReplacementChannel
    {A B O Y : Type u} [Fintype O] [Fintype Y]
    (P : Channel A O) (P' : Channel B Y) :
    ∀ k : RelabelReplacementBlock,
      Channel (relabelReplacementAct A B k) (relabelReplacementOut O Y k)
  | oldLeft => show Channel A O from P
  | newLeft => show Channel B Y from P'
  | oldRight => show Channel A O from P
  | newRight => show Channel B Y from P'

/--
Common-block assembly: if each of two lotteries is weakly equivalent between an
environment and a replacement environment, then every pairwise comparison is
preserved by replacement.
-/
theorem pairwise_relabel_replacement_from_weak_equiv
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (P' : Channel B Y)
    (q r : Dist A) (q' r' : Dist B)
    (hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q'))
    (hq_to_old :
      F.rel (blockChannel P' P) (inlDist q') (inrDist q))
    (hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r'))
    (hr_to_old :
      F.rel (blockChannel P' P) (inlDist r') (inrDist r)) :
    F.rel P q r ↔ F.rel P' q' r' := by
  classical
  let k0 : RelabelReplacementBlock.{u} := oldLeft
  let k1 : RelabelReplacementBlock.{u} := newLeft
  let k2 : RelabelReplacementBlock.{u} := oldRight
  let k3 : RelabelReplacementBlock.{u} := newRight
  let Act := relabelReplacementAct A B
  let Out := relabelReplacementOut O Y
  let C := relabelReplacementChannel P P'
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act k0 q
  let x' := blockEmbedDist Act k1 q'
  let y := blockEmbedDist Act k2 r
  let y' := blockEmbedDist Act k3 r'
  have htrans :
      ∀ a b c : Dist ((k : RelabelReplacementBlock) × Act k),
        F.rel commonP a b → F.rel commonP b c → F.rel commonP a c :=
    (hax.a1.1 commonP).2
  have h02_ne : k0 ≠ k2 := by decide
  have h01_ne : k0 ≠ k1 := by decide
  have h10_ne : k1 ≠ k0 := by decide
  have h23_ne : k2 ≠ k3 := by decide
  have h32_ne : k3 ≠ k2 := by decide
  have h13_ne : k1 ≠ k3 := by decide
  have hleft_dup :
      F.rel P q r ↔
        F.rel (blockChannel P P) (inlDist q) (inrDist r) :=
    hax.a3.duplication P q r
  have hright_dup :
      F.rel P' q' r' ↔
        F.rel (blockChannel P' P') (inlDist q') (inrDist r') :=
    hax.a3.duplication P' q' r'
  have hcommon_02 :
      F.rel commonP x y ↔
        F.rel (blockChannel P P) (inlDist q) (inrDist r) := by
    simpa [commonP, x, y, k0, k2, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using
      (hax.a3.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k2) h02_ne
        (qᵢ := q) (qⱼ := r))
  have hcommon_01 : F.rel commonP x x' := by
    have h :=
      (hax.a3.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k1) h01_ne
        (qᵢ := q) (qⱼ := q')).mpr hq_to_new
    simpa [commonP, x, x', k0, k1, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hcommon_10 : F.rel commonP x' x := by
    have h :=
      (hax.a3.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k0) h10_ne
        (qᵢ := q') (qⱼ := q)).mpr hq_to_old
    simpa [commonP, x, x', k0, k1, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hcommon_23 : F.rel commonP y y' := by
    have h :=
      (hax.a3.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k2) (j := k3) h23_ne
        (qᵢ := r) (qⱼ := r')).mpr hr_to_new
    simpa [commonP, y, y', k2, k3, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hcommon_32 : F.rel commonP y' y := by
    have h :=
      (hax.a3.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k3) (j := k2) h32_ne
        (qᵢ := r') (qⱼ := r)).mpr hr_to_old
    simpa [commonP, y, y', k2, k3, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using h
  have hreplace : F.rel commonP x y ↔ F.rel commonP x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonP a b) htrans
      hcommon_01 hcommon_10 hcommon_23 hcommon_32
  have hcommon_13 :
      F.rel commonP x' y' ↔
        F.rel (blockChannel P' P') (inlDist q') (inrDist r') := by
    simpa [commonP, x', y', k1, k3, Act, Out, C, relabelReplacementAct,
      relabelReplacementOut, relabelReplacementChannel] using
      (hax.a3.finite_block (K := RelabelReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k3) h13_ne
        (qᵢ := q') (qⱼ := r'))
  exact hleft_dup.trans
    (hcommon_02.symm.trans (hreplace.trans (hcommon_13.trans hright_dup.symm)))

/-- A finite probability distribution can exist only on a nonempty finite type. -/
theorem nonempty_of_dist {A : Type u} [Fintype A] (q : Dist A) : Nonempty A := by
  by_contra h
  have hzero : (∑ a : A, q a) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact False.elim (h ⟨a⟩)
  linarith [q.sum_eq_one]

/-- Outcome relabeling invariance follows from reversible deterministic postprocessing and A4. -/
theorem relabel_rel_outcome_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eO : O ≃ Y) (P : Channel A O) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (relabelChannel (Equiv.refl A) eO P) q r := by
  let P' := relabelChannel (Equiv.refl A) eO P
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q) := by
    have h := hax.a4 P (outcomeEquivKernel eO) q
    simpa [P', postprocess_outcomeEquiv_eq_relabel] using h
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist q) (inrDist q) := by
    have h := hax.a4 P' (outcomeEquivKernel eO.symm) q
    simpa [P', postprocess_outcomeEquiv_symm_eq_original] using h
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r) := by
    have h := hax.a4 P (outcomeEquivKernel eO) r
    simpa [P', postprocess_outcomeEquiv_eq_relabel] using h
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist r) (inrDist r) := by
    have h := hax.a4 P' (outcomeEquivKernel eO.symm) r
    simpa [P', postprocess_outcomeEquiv_symm_eq_original] using h
  exact
    pairwise_relabel_replacement_from_weak_equiv F hax P P' q r q r
      hq_to_new hq_to_old hr_to_new hr_to_old

/-- Action relabeling invariance follows from reversible deterministic action kernels and A5. -/
theorem relabel_rel_action_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (P : Channel A O) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (relabelChannel eA (Equiv.refl O) P)
        (relabelDist eA q) (relabelDist eA r) := by
  have hA : Nonempty A := nonempty_of_dist q
  haveI : Nonempty A := hA
  haveI : Nonempty B := ⟨eA (Classical.choice hA)⟩
  let P' := relabelChannel eA (Equiv.refl O) P
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist (relabelDist eA q)) := by
    have h :=
      hax.a5 P q (actionEquivKernel eA) P'
        (relabelChannel_isBayesPushforwardCompletion eA P q)
    simpa [P', actionPushforward_equiv] using h
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist (relabelDist eA q)) (inrDist q) := by
    have h :=
      hax.a5 P' (relabelDist eA q) (actionEquivKernel eA.symm) P
        (relabelChannel_symm_isBayesPushforwardCompletion eA P q)
    simpa [P', actionPushforward_equiv, relabelDist_symm] using h
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist (relabelDist eA r)) := by
    have h :=
      hax.a5 P r (actionEquivKernel eA) P'
        (relabelChannel_isBayesPushforwardCompletion eA P r)
    simpa [P', actionPushforward_equiv] using h
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist (relabelDist eA r)) (inrDist r) := by
    have h :=
      hax.a5 P' (relabelDist eA r) (actionEquivKernel eA.symm) P
        (relabelChannel_symm_isBayesPushforwardCompletion eA P r)
    simpa [P', actionPushforward_equiv, relabelDist_symm] using h
  exact
    pairwise_relabel_replacement_from_weak_equiv F hax P P'
      q r (relabelDist eA q) (relabelDist eA r)
      hq_to_new hq_to_old hr_to_new hr_to_old

/-- Full finite action/outcome relabeling invariance from A4, A5, A3, and A1 transitivity. -/
theorem relabel_rel_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (P : Channel A O) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (relabelChannel eA eO P) (relabelDist eA q) (relabelDist eA r) := by
  let P₁ := relabelChannel eA (Equiv.refl O) P
  have hact := relabel_rel_action_of_axioms F hax eA P q r
  have hout :=
    relabel_rel_outcome_of_axioms F hax eO P₁
      (relabelDist eA q) (relabelDist eA r)
  exact hact.trans (by simpa [P₁, relabelChannel_action_then_outcome] using hout)

/-- Packaged relabeling invariance for structural transfers. -/
structure FiniteRelabelingInvarianceAssumptions.{v} where
  relabel_rel :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A]
      [Fintype B] [DecidableEq B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (eA : A ≃ B) (eO : O ≃ Y)
      (P : Channel A O) (q r : Dist A),
      F.rel P q r ↔
        F.rel (relabelChannel eA eO P) (relabelDist eA q) (relabelDist eA r)

/-- Package the internally proved relabeling theorem. -/
theorem finiteRelabelingInvariance_of_axioms :
    FiniteRelabelingInvarianceAssumptions.{u} :=
  { relabel_rel := relabel_rel_of_axioms }

/-- The unique channel from `Unit` to the universe-lifted one-point type. -/
def unitToPUnitChannel : Channel Unit PUnit.{u + 1} :=
  fun _ =>
    { prob := fun _ => 1
      nonneg := fun _ => by norm_num
      sum_eq_one := by simp }

/-- The unique channel from the universe-lifted one-point type to `Unit`. -/
def punitToUnitChannel : Channel PUnit.{u + 1} Unit :=
  fun _ =>
    { prob := fun _ => 1
      nonneg := fun _ => by norm_num
      sum_eq_one := by simp }

@[simp]
theorem postprocess_uninformativeChannel_unitToPUnit
    {A : Type u} [Fintype A] :
    Channel.postprocess (Channel.uninformativeChannel A) unitToPUnitChannel =
      Channel.uninformativeChannelU A := by
  ext a p
  simp [Channel.postprocess, Channel.uninformativeChannel,
    Channel.uninformativeChannelU, unitToPUnitChannel]

@[simp]
theorem postprocess_uninformativeChannelU_punitToUnit
    {A : Type u} [Fintype A] :
    Channel.postprocess (Channel.uninformativeChannelU A) punitToUnitChannel =
      Channel.uninformativeChannel A := by
  ext a p
  simp [Channel.postprocess, Channel.uninformativeChannel,
    Channel.uninformativeChannelU, punitToUnitChannel]

/-- Relabel the right one-point outcome in `A ⊕ Unit` to `A ⊕ PUnit.{u+1}`. -/
def blockUnitPUnitOutcomeEquiv (A : Type u) : (A ⊕ Unit) ≃ (A ⊕ PUnit.{u + 1}) where
  toFun
    | Sum.inl a => Sum.inl a
    | Sum.inr _ => Sum.inr PUnit.unit
  invFun
    | Sum.inl a => Sum.inl a
    | Sum.inr _ => Sum.inr ()
  left_inv := by
    intro x
    cases x <;> rfl
  right_inv := by
    intro x
    cases x <;> rfl

@[simp]
theorem relabel_block_id_uninformativeChannel_eq
    {A : Type u} [Fintype A] [DecidableEq A] :
    relabelChannel (Equiv.refl (A ⊕ A)) (blockUnitPUnitOutcomeEquiv A)
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A)) =
        blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A) := by
  ext x y
  cases x <;> cases y <;> simp [relabelChannel, blockUnitPUnitOutcomeEquiv,
    Channel.idChannel, Channel.uninformativeChannel, Channel.uninformativeChannelU]

@[simp]
theorem relabelDist_sumComm_inr
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (r : Dist B) :
    relabelDist (Equiv.sumComm A B) (inrDist r : Dist (A ⊕ B)) =
      (inlDist r : Dist (B ⊕ A)) := by
  ext x
  cases x <;> rfl

@[simp]
theorem relabelDist_sumComm_inl
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (q : Dist A) :
    relabelDist (Equiv.sumComm A B) (inlDist q : Dist (A ⊕ B)) =
      (inrDist q : Dist (B ⊕ A)) := by
  ext x
  cases x <;> rfl

@[simp]
theorem relabel_blockChannel_sumComm_eq
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (Q : Channel B Y) :
    relabelChannel (Equiv.sumComm A B) (Equiv.sumComm O Y) (blockChannel P Q) =
      blockChannel Q P := by
  ext x y
  cases x <;> cases y <;> rfl

/-- Lift A1's ordinary no-information strictness to the value-facing one-point outcome. -/
theorem lifted_uninformative_strict_of_relabeling
    (hrelabel : FiniteRelabelingInvarianceAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    (q : Dist A) (hq : q.FullSupport) :
    F.strictRel
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A))
      (inlDist q) (inrDist q) := by
  have hstrict :
      F.strictRel
        (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A))
        (inlDist q) (inrDist q) :=
    hax.a1.2 q hq
  have hiff :=
    hrelabel.relabel_rel F hax (Equiv.refl (A ⊕ A)) (blockUnitPUnitOutcomeEquiv A)
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A))
      (inlDist q) (inrDist q)
  have hiff_rev :=
    hrelabel.relabel_rel F hax (Equiv.refl (A ⊕ A)) (blockUnitPUnitOutcomeEquiv A)
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannel A))
      (inrDist q) (inlDist q)
  constructor
  · simpa using hiff.mp hstrict.1
  · intro hrev
    exact hstrict.2 (hiff_rev.mpr (by simpa using hrev))

/-- Lifted no-information strictness, derived directly from the axioms. -/
theorem lifted_uninformative_strict_of_A1
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    (q : Dist A) (hq : q.FullSupport) :
    F.strictRel
      (blockChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU A))
      (inlDist q) (inrDist q) :=
  lifted_uninformative_strict_of_relabeling
    finiteRelabelingInvariance_of_axioms F hax q hq

/-- Reverse orientation for two-block comparisons follows from finite relabeling invariance. -/
theorem block_swap_rel_of_relabeling
    (hrelabel : FiniteRelabelingInvarianceAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (Q : Channel B Y)
    (q : Dist A) (r : Dist B) :
    F.rel (blockChannel P Q) (inrDist r) (inlDist q) ↔
      F.rel (blockChannel Q P) (inlDist r) (inrDist q) := by
  have hiff :=
    hrelabel.relabel_rel F hax (Equiv.sumComm A B) (Equiv.sumComm O Y)
      (blockChannel P Q) (inrDist r) (inlDist q)
  simpa using hiff

/-- Reverse orientation for two-block comparisons, derived directly from the axioms. -/
theorem block_swap_rel_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (Q : Channel B Y)
    (q : Dist A) (r : Dist B) :
    F.rel (blockChannel P Q) (inrDist r) (inlDist q) ↔
      F.rel (blockChannel Q P) (inlDist r) (inrDist q) :=
  block_swap_rel_of_relabeling finiteRelabelingInvariance_of_axioms F hax P Q q r

end Relabeling
end TraceableAgency
