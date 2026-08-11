/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Blocks
import TraceableAgency.Basic.SupportRestriction
import TraceableAgency.PureTrace.Proof.Spine

/-!
# External Support Restriction Assumptions

This file isolates the remaining paper-specific boundary step from the pure
finite-probability support-restriction algebra.

The pure lemmas in `Basic.SupportRestriction` prove that deleting zero-prior
action rows preserves full support on the reduced support, outcome marginals,
conditional entropy sums, and mutual information.

What remains external here is not those algebraic facts. The one-sided weak
comparisons between an ambient row and its positive-support restriction are
proved below from A5, using the Bayesian-completion lemmas in
`Basic.SupportRestriction`. The A1/A3 assembly step that transports those weak
equivalences into the common block comparison between two possibly different
support faces is also proved below.
-/

namespace TraceableAgency

universe u

/-- A5 gives that an ambient experiment weakly dominates its positive-support
restriction: deleting zero-prior rows by support projection is an action
coarsening. -/
theorem rel_ambient_to_support
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel
      (blockChannel P (Channel.restrictToSupport P q))
      (inlDist q)
      (inrDist q.restrictToSupport) := by
  haveI : Nonempty A := ⟨(Classical.choice (supportSubtype_nonempty q)).1⟩
  have hrel :=
    hax.actionProcessing P q (supportProjectKernel q) (Channel.restrictToSupport P q)
      (restrictToSupport_isBayesPushforwardCompletion P q)
  simpa [actionPushforward_project q] using hrel

/-- A5 also gives the reverse weak comparison: adding zero-prior ambient rows is
an action coarsening of the support-restricted problem by inclusion, and the
completion is unconstrained off the pushed support. -/
theorem rel_support_to_ambient
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel
      (blockChannel (Channel.restrictToSupport P q) P)
      (inlDist q.restrictToSupport)
      (inrDist q) := by
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hrel :=
    hax.actionProcessing (Channel.restrictToSupport P q) q.restrictToSupport
      (supportIncludeKernel q) P
      (ambient_isBayesPushforwardCompletion_of_restrict P q)
  simpa [actionPushforward_restrict_include q] using hrel

/-- The four labels used in the common finite block support-restriction
environment.  There are two ambient copies of `P`, one for the left prior and
one for the right prior, plus the two corresponding support faces. -/
inductive SupportRestrictionBlock : Type u
  | ambientLeft
  | supportLeft
  | ambientRight
  | supportRight
  deriving DecidableEq, Fintype

open SupportRestrictionBlock

/-- Action alphabets for the common four-block support-restriction environment. -/
def supportRestrictionAct
    {A : Type u} [Fintype A] (q r : Dist A) :
    SupportRestrictionBlock → Type u
  | ambientLeft => A
  | supportLeft => supportSubtype q
  | ambientRight => A
  | supportRight => supportSubtype r

noncomputable instance supportRestrictionActFintype
    {A : Type u} [Fintype A] (q r : Dist A) :
    ∀ k : SupportRestrictionBlock, Fintype (supportRestrictionAct q r k)
  | ambientLeft => show Fintype A from inferInstance
  | supportLeft => show Fintype (supportSubtype q) from inferInstance
  | ambientRight => show Fintype A from inferInstance
  | supportRight => show Fintype (supportSubtype r) from inferInstance

instance supportRestrictionActDecidableEq
    {A : Type u} [Fintype A] [DecidableEq A] (q r : Dist A) :
    ∀ k : SupportRestrictionBlock, DecidableEq (supportRestrictionAct q r k)
  | ambientLeft => show DecidableEq A from inferInstance
  | supportLeft => show DecidableEq (supportSubtype q) from inferInstance
  | ambientRight => show DecidableEq A from inferInstance
  | supportRight => show DecidableEq (supportSubtype r) from inferInstance

/-- Channels for the common four-block support-restriction environment. -/
noncomputable def supportRestrictionChannel
    {A O : Type u} [Fintype A] [Fintype O]
    (P : Channel A O) (q r : Dist A) :
    ∀ k : SupportRestrictionBlock,
      Channel (supportRestrictionAct q r k) O
  | ambientLeft => P
  | supportLeft => Channel.restrictToSupport P q
  | ambientRight => P
  | supportRight => Channel.restrictToSupport P r

/-- Common four-block channel used to assemble support-restriction comparisons. -/
noncomputable def supportRestrictionCommonChannel
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q r : Dist A) :
    Channel
      ((k : SupportRestrictionBlock) × supportRestrictionAct q r k)
      ((_ : SupportRestrictionBlock) × O) :=
  blockFamilyChannel (supportRestrictionAct q r) (fun _ => O)
    (supportRestrictionChannel P q r)

/-- A1/A3 common-block assembly from the four A5 support-face weak comparisons
to pairwise preference invariance under deleting zero-prior rows. -/
theorem pairwise_support_restriction_from_weak_equiv
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q r : Dist A)
    (hq_to_support :
      F.rel
        (blockChannel P (Channel.restrictToSupport P q))
        (inlDist q)
        (inrDist q.restrictToSupport))
    (hq_to_ambient :
      F.rel
        (blockChannel (Channel.restrictToSupport P q) P)
        (inlDist q.restrictToSupport)
        (inrDist q))
    (hr_to_support :
      F.rel
        (blockChannel P (Channel.restrictToSupport P r))
        (inlDist r)
        (inrDist r.restrictToSupport))
    (hr_to_ambient :
      F.rel
        (blockChannel (Channel.restrictToSupport P r) P)
        (inlDist r.restrictToSupport)
        (inrDist r)) :
    (F.rel P q r ↔
      F.rel
        (blockChannel (Channel.restrictToSupport P q)
          (Channel.restrictToSupport P r))
        (inlDist q.restrictToSupport)
        (inrDist r.restrictToSupport)) := by
  classical
  let k0 : SupportRestrictionBlock.{u} := ambientLeft
  let k1 : SupportRestrictionBlock.{u} := supportLeft
  let k2 : SupportRestrictionBlock.{u} := ambientRight
  let k3 : SupportRestrictionBlock.{u} := supportRight
  let Act := supportRestrictionAct q r
  let Out : SupportRestrictionBlock → Type u := fun _ => O
  let C := supportRestrictionChannel P q r
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act k0 q
  let x' := blockEmbedDist Act k1 q.restrictToSupport
  let y := blockEmbedDist Act k2 r
  let y' := blockEmbedDist Act k3 r.restrictToSupport
  have htrans :
      ∀ a b c : Dist ((k : SupportRestrictionBlock) × Act k),
        F.rel commonP a b → F.rel commonP b c → F.rel commonP a c :=
    (hax.weakOrder.1 commonP).2
  have h02_ne : k0 ≠ k2 := by decide
  have h01_ne : k0 ≠ k1 := by decide
  have h10_ne : k1 ≠ k0 := by decide
  have h23_ne : k2 ≠ k3 := by decide
  have h32_ne : k3 ≠ k2 := by decide
  have h13_ne : k1 ≠ k3 := by decide
  have hleft_dup :
      F.rel P q r ↔
        F.rel (blockChannel P P) (inlDist q) (inrDist r) :=
    hax.blockCoherence.duplication P q r
  have hcommon_02 :
      F.rel commonP x y ↔
        F.rel (blockChannel P P) (inlDist q) (inrDist r) := by
    simpa [commonP, x, y, k0, k2, Act, Out, C, supportRestrictionAct,
      supportRestrictionChannel] using
      (hax.blockCoherence.finite_block (K := SupportRestrictionBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k2) h02_ne
        (qᵢ := q) (qⱼ := r))
  have hcommon_01 : F.rel commonP x x' := by
    have h :=
      (hax.blockCoherence.finite_block (K := SupportRestrictionBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k1) h01_ne
        (qᵢ := q) (qⱼ := q.restrictToSupport)).mpr hq_to_support
    simpa [commonP, x, x', k0, k1, Act, Out, C, supportRestrictionAct,
      supportRestrictionChannel] using h
  have hcommon_10 : F.rel commonP x' x := by
    have h :=
      (hax.blockCoherence.finite_block (K := SupportRestrictionBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k0) h10_ne
        (qᵢ := q.restrictToSupport) (qⱼ := q)).mpr hq_to_ambient
    simpa [commonP, x, x', k0, k1, Act, Out, C, supportRestrictionAct,
      supportRestrictionChannel] using h
  have hcommon_23 : F.rel commonP y y' := by
    have h :=
      (hax.blockCoherence.finite_block (K := SupportRestrictionBlock) (Act := Act) (Out := Out) (P := C)
        (i := k2) (j := k3) h23_ne
        (qᵢ := r) (qⱼ := r.restrictToSupport)).mpr hr_to_support
    simpa [commonP, y, y', k2, k3, Act, Out, C, supportRestrictionAct,
      supportRestrictionChannel] using h
  have hcommon_32 : F.rel commonP y' y := by
    have h :=
      (hax.blockCoherence.finite_block (K := SupportRestrictionBlock) (Act := Act) (Out := Out) (P := C)
        (i := k3) (j := k2) h32_ne
        (qᵢ := r.restrictToSupport) (qⱼ := r)).mpr hr_to_ambient
    simpa [commonP, y, y', k2, k3, Act, Out, C, supportRestrictionAct,
      supportRestrictionChannel] using h
  have hreplace : F.rel commonP x y ↔ F.rel commonP x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonP a b) htrans
      hcommon_01 hcommon_10 hcommon_23 hcommon_32
  have hcommon_13 :
      F.rel commonP x' y' ↔
        F.rel
          (blockChannel (Channel.restrictToSupport P q)
            (Channel.restrictToSupport P r))
          (inlDist q.restrictToSupport)
          (inrDist r.restrictToSupport) := by
    simpa [commonP, x', y', k1, k3, Act, Out, C, supportRestrictionAct,
      supportRestrictionChannel] using
      (hax.blockCoherence.finite_block (K := SupportRestrictionBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k3) h13_ne
        (qᵢ := q.restrictToSupport) (qⱼ := r.restrictToSupport))
  exact hleft_dup.trans (hcommon_02.symm.trans (hreplace.trans hcommon_13))

/-- Named support-restriction preference equivalence, assembled from the A5
projection/inclusion weak comparisons and the A1/A3 common-block replacement
theorem above. -/
theorem preference_support_restriction_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q r : Dist A) :
    (F.rel P q r ↔
      F.rel
        (blockChannel (Channel.restrictToSupport P q)
          (Channel.restrictToSupport P r))
        (inlDist q.restrictToSupport)
        (inrDist r.restrictToSupport)) :=
  pairwise_support_restriction_from_weak_equiv F hax P q r
    (rel_ambient_to_support F hax P q)
    (rel_support_to_ambient F hax P q)
    (rel_ambient_to_support F hax P r)
    (rel_support_to_ambient F hax P r)

/--
Boundary extension from A5 support comparisons, A1/A3 common-block assembly,
and full-support block MI.

This assembles `FullSupportBlockMI F` with the pure support-restriction facts:
`Dist.restrictToSupport_fullSupport`, `mutualInfo_restrictToSupport`, the
A5-derived one-sided support weak comparisons, and the A1/A3 pairwise support
replacement theorem above.
-/
theorem FullSupportMIRepExtendsToBoundary_of_supportRestriction
    (F : PrefFamily.{u})
    (hblockMI : FullSupportBlockMI F) :
    FullSupportMIRepExtendsToBoundary F := by
  intro hax _hfull
  obtain ⟨alpha, hα, hblock⟩ := hblockMI
  refine ⟨alpha, hα, ?_⟩
  intro A O _ _ _ _ P q r
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  have hblock_restricted :
      F.rel
          (blockChannel (Channel.restrictToSupport P q)
            (Channel.restrictToSupport P r))
          (inlDist q.restrictToSupport)
          (inrDist r.restrictToSupport) ↔
        alpha * mutualInfo q.restrictToSupport (Channel.restrictToSupport P q) ≥
          alpha * mutualInfo r.restrictToSupport (Channel.restrictToSupport P r) :=
    hblock (P := Channel.restrictToSupport P q) (Q := Channel.restrictToSupport P r)
      (q := q.restrictToSupport) (r := r.restrictToSupport)
      (Dist.restrictToSupport_fullSupport q)
      (Dist.restrictToSupport_fullSupport r)
  have hpref :
      F.rel P q r ↔
        F.rel
          (blockChannel (Channel.restrictToSupport P q)
            (Channel.restrictToSupport P r))
          (inlDist q.restrictToSupport)
          (inrDist r.restrictToSupport) := by
    exact preference_support_restriction_of_axioms F hax P q r
  rw [hpref]
  rw [hblock_restricted]
  rw [mutualInfo_restrictToSupport, mutualInfo_restrictToSupport]

end TraceableAgency
