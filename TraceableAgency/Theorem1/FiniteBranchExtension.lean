/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PayoffLotteries

/-!
# Binary A8 and its finite-branch extension

This file proves the v5 finite-branch lemma.  The public A8 is the binary
recordwise sure-thing biconditional.  The derived property is the dependent
finite-branch form used by the representation proof.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-! ## Splitting one finite branch from its complement -/

/-- The deterministic binary record that distinguishes `target` from its
complement. -/
noncomputable def branchIndicator
    {Y : Type u} [Fintype Y] [DecidableEq Y]
    (target : Y) : Channel Y (RelevanceBit.{u}) :=
  fun y => TraceableAgency.Dist.pure
    (ULift.up (decide (y = target)))

@[simp]
theorem branchIndicator_apply_true
    {Y : Type u} [Fintype Y] [DecidableEq Y]
    (target y : Y) :
    branchIndicator target y (ULift.up true) = if y = target then 1 else 0 := by
  by_cases h : y = target <;>
    simp [branchIndicator, h, TraceableAgency.Dist.pure_apply]

@[simp]
theorem branchIndicator_apply_false
    {Y : Type u} [Fintype Y] [DecidableEq Y]
    (target y : Y) :
    branchIndicator target y (ULift.up false) = if y = target then 0 else 1 := by
  by_cases h : y = target <;>
    simp [branchIndicator, h, TraceableAgency.Dist.pure_apply]

/-- Collapse a finite first-stage record to `target` versus its complement. -/
noncomputable def binaryCollapse
    {A Y : Type u} [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A Y) (target : Y) : Channel A RelevanceBit :=
  fun a => Channel.outcomeMarginal (branchIndicator target) (P a)

@[simp]
theorem binaryCollapse_true
    {A Y : Type u} [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A Y) (target : Y) (a : A) :
    binaryCollapse P target a (ULift.up true) = P a target := by
  classical
  simp [binaryCollapse, Channel.outcomeMarginal_apply]

theorem outcomeMarginal_binaryCollapse_true
    {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A Y) (q : TraceableAgency.Dist A) (target : Y) :
    Channel.outcomeMarginal (binaryCollapse P target) q (ULift.up true) =
      Channel.outcomeMarginal P q target := by
  simp [Channel.outcomeMarginal_apply]

theorem branchPosterior_binaryCollapse_true
    {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A Y) (q : TraceableAgency.Dist A) (target : Y) :
    branchPosterior (binaryCollapse P target) q (ULift.up true) =
      branchPosterior P q target := by
  apply TraceableAgency.Dist.ext
  intro a
  simp [branchPosterior, Channel.posterior,
    outcomeMarginal_binaryCollapse_true, binaryCollapse_true]

/-- Deterministically attach the selected branch label to its continuation
record. -/
noncomputable def tagBranchRecordProcessor
    {O Y : Type u}
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (y : Y) : RecordProcessor O (Rec y) ((y : Y) × Rec y) :=
  fun z => TraceableAgency.Dist.pure (Sigma.mk y z.2)

/-- Put a branch continuation on the common tagged record alphabet. -/
noncomputable def tagBranchContinuation
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (y : Y) (K : Channel A (O × Rec y)) :=
  recordPostprocess K (tagBranchRecordProcessor Rec y)

@[simp]
theorem tagBranchContinuation_same
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (y : Y) (K : Channel A (O × Rec y))
    (a : A) (o : O) (r : Rec y) :
    tagBranchContinuation Rec y K a (o, Sigma.mk y r) = K a (o, r) := by
  classical
  simp [tagBranchContinuation, tagBranchRecordProcessor, recordPostprocess,
    payoffPreservingRecordKernel, Channel.postprocess,
    Fintype.sum_prod_type, TraceableAgency.Dist.pure_apply]

theorem tagBranchContinuation_ne
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (y y' : Y) (hy : y' ≠ y) (K : Channel A (O × Rec y))
    (a : A) (o : O) (r : Rec y') :
    tagBranchContinuation Rec y K a (o, Sigma.mk y' r) = 0 := by
  classical
  simp [tagBranchContinuation, tagBranchRecordProcessor, recordPostprocess,
    payoffPreservingRecordKernel, Channel.postprocess,
    Fintype.sum_prod_type, TraceableAgency.Dist.pure_apply, hy]

/-- Remove the constant branch tag.  Values away from `target` only complete
rows that the tagged continuation never reaches. -/
noncomputable def eraseBranchTagProcessor
    {O Y : Type u}
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u) [∀ y, Fintype (Rec y)]
    [∀ y, DecidableEq (Rec y)] (target : Y) [Nonempty (Rec target)] :
    RecordProcessor O ((y : Y) × Rec y) (Rec target) :=
  fun z =>
    match z.2 with
    | Sigma.mk y r =>
        if h : y = target then
          TraceableAgency.Dist.pure (h ▸ r)
        else
          TraceableAgency.Dist.pure (Classical.arbitrary (Rec target))

theorem recordPostprocess_eraseBranchTag
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (target : Y) [Nonempty (Rec target)]
    (K : Channel A (O × Rec target)) :
    recordPostprocess (tagBranchContinuation Rec target K)
        (eraseBranchTagProcessor Rec target) = K := by
  classical
  ext a z
  rcases z with ⟨o, r⟩
  change (∑ x : O × ((y : Y) × Rec y),
      tagBranchContinuation Rec target K a x *
        (if o = x.1 then
          (eraseBranchTagProcessor Rec target x) r else 0)) = K a (o, r)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single o]
  · simp only [if_true, Fintype.sum_sigma]
    rw [Finset.sum_eq_single target]
    · rw [Finset.sum_eq_single r]
      · simp [eraseBranchTagProcessor]
      · intro r' _ hr'
        simp [eraseBranchTagProcessor,
          TraceableAgency.Dist.pure_apply, hr']
        intro heq
        exact (hr' heq.symm).elim
      · exact absurd (Finset.mem_univ r)
    · intro y _ hy
      apply Finset.sum_eq_zero
      intro r' _
      rw [tagBranchContinuation_ne Rec target y hy K]
      ring
    · exact absurd (Finset.mem_univ target)
  · intro o' _ ho'
    simp
    intro heq
    exact (ho' heq.symm).elim
  · exact absurd (Finset.mem_univ o)

/-- Continuation on the complementary binary record.  It first draws the
original branch conditional on not being `target`, then runs that branch's
unchanged continuation.  Null rows receive the canonical posterior
completion and are immaterial in the compound. -/
noncomputable def complementContinuation
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) :=
  fun a => Channel.outcomeMarginal
    (fun y => tagBranchContinuation Rec y (Q y) a)
    (Channel.posterior (branchIndicator target) (P a)
      (ULift.up.{u, 0} false))

theorem complementContinuation_apply
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target y : Y) (a : A) (o : O) (r : Rec y) :
    complementContinuation Rec P Q target a (o, Sigma.mk y r) =
      Channel.posterior (branchIndicator target) (P a)
          (ULift.up false) y * Q y a (o, r) := by
  classical
  unfold complementContinuation
  rw [Channel.outcomeMarginal_apply]
  rw [Finset.sum_eq_single y]
  · rw [tagBranchContinuation_same]
  · intro y' _ hy'
    rw [tagBranchContinuation_ne Rec y' y (Ne.symm hy') (Q y')]
    ring
  · exact absurd (Finset.mem_univ y)

/-- The binary continuation profile representing a finite profile with one
branch separated from its complement. -/
noncomputable def splitContinuation
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) (b : RelevanceBit) :=
  if b.down then tagBranchContinuation Rec target (Q target)
  else complementContinuation Rec P Q target

/-- The corresponding nested binary compound. -/
noncomputable def splitCompound
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) :=
  commonPayoffCompound
    (fun _ : RelevanceBit => (y : Y) × Rec y)
    (binaryCollapse P target) (splitContinuation Rec P Q target)

/-- Add the redundant binary tag to a flat compound record. -/
noncomputable def addSplitTagProcessor
    {O Y : Type u}
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u) [∀ y, Fintype (Rec y)]
    (target : Y) :
    RecordProcessor O ((y : Y) × Rec y)
      ((b : RelevanceBit) × ((y : Y) × Rec y)) :=
  fun z =>
    @TraceableAgency.Dist.pure
      ((b : RelevanceBit) × ((y : Y) × Rec y)) _
      (Classical.decEq ((b : RelevanceBit) × ((y : Y) × Rec y)))
      (show (b : RelevanceBit) × ((y : Y) × Rec y) from
        ⟨ULift.up (decide (z.2.1 = target)), z.2⟩)

/-- Delete the redundant binary tag from a split compound record. -/
noncomputable def eraseSplitTagProcessor
    {O Y : Type u}
    [Fintype Y]
    (Rec : Y → Type u) [∀ y, Fintype (Rec y)] :
    RecordProcessor O ((b : RelevanceBit) × ((y : Y) × Rec y))
      ((y : Y) × Rec y) :=
  fun z =>
    @TraceableAgency.Dist.pure ((y : Y) × Rec y) _
      (Classical.decEq ((y : Y) × Rec y)) z.2.2

@[simp]
theorem commonPayoffCompound_apply
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (a : A) (o : O) (y : Y) (r : Rec y) :
    commonPayoffCompound Rec P Q a (o, Sigma.mk y r) =
      P a y * Q y a (o, r) := by
  rfl

theorem recordPostprocess_addSplitTag_apply
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) (a : A) (o : O) (b : RelevanceBit)
    (y : Y) (r : Rec y) :
    recordPostprocess (commonPayoffCompound Rec P Q)
        (addSplitTagProcessor Rec target) a
        (o, Sigma.mk b (Sigma.mk y r)) =
      if b.down = decide (y = target)
      then P a y * Q y a (o, r) else 0 := by
  classical
  unfold recordPostprocess payoffPreservingRecordKernel Channel.postprocess
  change (∑ x : O × ((y : Y) × Rec y),
      commonPayoffCompound Rec P Q a x *
        (if o = x.1 then
          (addSplitTagProcessor Rec target x)
            (Sigma.mk b (Sigma.mk y r)) else 0)) = _
  rw [Finset.sum_eq_single (o, Sigma.mk y r)]
  · simp only [commonPayoffCompound_apply]
    by_cases hb : b.down = decide (y = target)
    · have hb' : b = ULift.up (decide (y = target)) := by
        apply ULift.ext
        exact hb
      simp [addSplitTagProcessor, TraceableAgency.Dist.pure_apply, hb, hb']
    · have hb' : b ≠ ULift.up (decide (y = target)) := by
        intro heq
        apply hb
        exact congrArg ULift.down heq
      simp [addSplitTagProcessor, TraceableAgency.Dist.pure_apply, hb, hb']
  · intro x _ hx
    rcases x with ⟨o', y', r'⟩
    by_cases ho : o = o'
    · subst o'
      by_cases hyr : (Sigma.mk y r : (y : Y) × Rec y) = Sigma.mk y' r'
      · exact False.elim (hx (Prod.ext rfl hyr.symm))
      · simp [addSplitTagProcessor, TraceableAgency.Dist.pure_apply, hyr]
    · simp [ho]
  · exact absurd (Finset.mem_univ _)

@[simp]
theorem splitCompound_apply
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) (a : A) (o : O) (b : RelevanceBit)
    (y : Y) (r : Rec y) :
    splitCompound Rec P Q target a
        (o, Sigma.mk b (Sigma.mk y r)) =
      binaryCollapse P target a b *
        splitContinuation Rec P Q target b a (o, Sigma.mk y r) := by
  rfl

/-- Adding the deterministic target/complement tag turns the flat finite
compound into the split binary compound exactly. -/
theorem recordPostprocess_addSplitTag
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) :
    recordPostprocess (commonPayoffCompound Rec P Q)
        (addSplitTagProcessor Rec target) =
      splitCompound Rec P Q target := by
  classical
  ext a z
  rcases z with ⟨o, b, y, r⟩
  rw [recordPostprocess_addSplitTag_apply, splitCompound_apply]
  cases b with
  | up b =>
    cases b
    · rw [show splitContinuation Rec P Q target (ULift.up false) =
          complementContinuation Rec P Q target by rfl,
        complementContinuation_apply]
      have hbayes := posterior_mul_marginal (P a)
        (branchIndicator target) (ULift.up false) y
      by_cases hyt : y = target
      · subst y
        rw [if_neg (by simp)]
        change 0 = binaryCollapse P target a (ULift.up false) *
          (Channel.posterior (branchIndicator target) (P a)
            (ULift.up false) target * Q target a (o, r))
        symm
        calc
          binaryCollapse P target a (ULift.up false) *
              (Channel.posterior (branchIndicator target) (P a)
                (ULift.up false) target * Q target a (o, r)) =
              (Channel.outcomeMarginal (branchIndicator target) (P a)
                (ULift.up false) *
                Channel.posterior (branchIndicator target) (P a)
                  (ULift.up false) target) * Q target a (o, r) := by
                    simp [binaryCollapse]
                    ring
          _ = 0 := by rw [hbayes]; simp
      · rw [if_pos (by simp [hyt])]
        change P a y * Q y a (o, r) =
          binaryCollapse P target a (ULift.up false) *
            (Channel.posterior (branchIndicator target) (P a)
              (ULift.up false) y * Q y a (o, r))
        calc
          P a y * Q y a (o, r) =
              (Channel.outcomeMarginal (branchIndicator target) (P a)
                (ULift.up false) *
                Channel.posterior (branchIndicator target) (P a)
                  (ULift.up false) y) * Q y a (o, r) := by
                    rw [hbayes]
                    simp [hyt]
          _ = binaryCollapse P target a (ULift.up false) *
              (Channel.posterior (branchIndicator target) (P a)
                (ULift.up false) y * Q y a (o, r)) := by
                  simp [binaryCollapse]
                  ring
    · by_cases hyt : y = target
      · subst y
        simp [splitContinuation, binaryCollapse_true]
      · simp [splitContinuation, hyt,
          tagBranchContinuation_ne Rec target y hyt]

/-- Erasing the redundant binary tag recovers the flat finite compound. -/
theorem recordPostprocess_eraseSplitTag
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) :
    recordPostprocess (splitCompound Rec P Q target)
        (eraseSplitTagProcessor Rec) =
      commonPayoffCompound Rec P Q := by
  classical
  rw [← recordPostprocess_addSplitTag Rec P Q target]
  ext a z
  rcases z with ⟨o, y, r⟩
  change (∑ x : O × ((b : RelevanceBit) × ((y : Y) × Rec y)),
      recordPostprocess (commonPayoffCompound Rec P Q)
          (addSplitTagProcessor Rec target) a x *
        (if o = x.1 then
          (eraseSplitTagProcessor Rec x) (Sigma.mk y r) else 0)) =
    commonPayoffCompound Rec P Q a (o, Sigma.mk y r)
  rw [Fintype.sum_prod_type, Finset.sum_eq_single o]
  · simp only [if_true]
    rw [Fintype.sum_sigma]
    have hinner (b : RelevanceBit) :
        (∑ yr : (y : Y) × Rec y,
          recordPostprocess (commonPayoffCompound Rec P Q)
              (addSplitTagProcessor Rec target) a (o, Sigma.mk b yr) *
            (eraseSplitTagProcessor Rec (o, Sigma.mk b yr))
              (Sigma.mk y r)) =
          recordPostprocess (commonPayoffCompound Rec P Q)
            (addSplitTagProcessor Rec target) a
              (o, Sigma.mk b (Sigma.mk y r)) := by
      rw [Finset.sum_eq_single (Sigma.mk y r)]
      · simp [eraseSplitTagProcessor, TraceableAgency.Dist.pure_apply]
      · intro yr _ hyr
        simp [eraseSplitTagProcessor, TraceableAgency.Dist.pure_apply]
        intro heq
        exact (hyr heq.symm).elim
      · exact absurd (Finset.mem_univ _)
    simp_rw [hinner]
    rw [Finset.sum_eq_single
      (ULift.up (decide (y = target)) : RelevanceBit)]
    · simp [recordPostprocess_addSplitTag_apply]
    · intro b _ hb
      have hdown : b.down ≠ decide (y = target) := by
        intro heq
        apply hb
        apply ULift.ext
        exact heq
      simp [recordPostprocess_addSplitTag_apply, hdown]
    · exact absurd (Finset.mem_univ _)
  · intro o' _ ho'
    simp
    intro heq
    exact (ho' heq.symm).elim
  · exact absurd (Finset.mem_univ o)

/-! ## Prior-law equivalence and binary split formulas -/

noncomputable def identityActionProcessor
    {A : Type u} [Fintype A] [DecidableEq A] :
    Channel.ActionKernel A A :=
  fun a => TraceableAgency.Dist.pure a

@[simp]
theorem actionPushforward_identityActionProcessor
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : TraceableAgency.Dist A) :
    Channel.actionPushforward q identityActionProcessor = q := by
  ext a
  simp [Channel.actionPushforward, identityActionProcessor,
    TraceableAgency.Dist.pure_apply]

/-- A7 makes channels with the same prior-weighted rows weakly equivalent.
The completion on zero-probability action rows is therefore immaterial. -/
theorem pairWeak_of_samePriorJointLaw
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h7 : A7_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (K L : Channel A (O × R))
    (hlaw : ∀ a z, q a * K a z = q a * L a z) :
    pairWeak F q K q L := by
  have hcompletion : IsActionProcessorCompletion K q
      identityActionProcessor L := by
    intro a z
    rw [actionPushforward_identityActionProcessor]
    rw [Finset.sum_eq_single a]
    · simpa [identityActionProcessor,
        TraceableAgency.Dist.pure_apply] using (hlaw a z).symm
    · intro a' _ ha'
      simp [identityActionProcessor,
        TraceableAgency.Dist.pure_apply, ha']
      intro heq
      exact (ha' heq.symm).elim
    · exact absurd (Finset.mem_univ a)
  simpa using h7 K q identityActionProcessor L hcompletion

theorem pairWeak_refl_of_structural
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    pairWeak F q K q K := by
  have hself : F.rel K q q := by
    rcases (h1 K).1 q q with h | h <;> exact h
  exact (h5.duplication K q q).mp hself

@[simp]
theorem binaryPayoffCompound_apply
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype R] [DecidableEq R]
    (P : Channel A RelevanceBit) (K M : Channel A (O × R))
    (a : A) (o : O) (b : RelevanceBit) (r : R) :
    binaryPayoffCompound P K M a (o, Sigma.mk b r) =
      P a b * binaryContinuationProfile K M b a (o, r) := by
  rfl

theorem splitCompound_eq_binaryPayoffCompound
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q : ∀ y, Channel A (O × Rec y))
    (target : Y) :
    splitCompound Rec P Q target =
      binaryPayoffCompound (binaryCollapse P target)
        (tagBranchContinuation Rec target (Q target))
        (complementContinuation Rec P Q target) := by
  rfl

theorem weighted_complementContinuation_eq_of_offTarget
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q L : ∀ y, Channel A (O × Rec y))
    (target : Y) (hoff : ∀ y, y ≠ target → Q y = L y)
    (q : TraceableAgency.Dist A) (a : A) (o : O) (y : Y) (r : Rec y) :
    q a * binaryCollapse P target a (ULift.up false) *
        complementContinuation Rec P Q target a (o, Sigma.mk y r) =
      q a * binaryCollapse P target a (ULift.up false) *
        complementContinuation Rec P L target a (o, Sigma.mk y r) := by
  rw [complementContinuation_apply, complementContinuation_apply]
  by_cases hyt : y = target
  · subst y
    have hbayes := posterior_mul_marginal (P a)
      (branchIndicator target) (ULift.up false) target
    have hz : binaryCollapse P target a (ULift.up false) *
        Channel.posterior (branchIndicator target) (P a)
          (ULift.up false) target = 0 := by
      simpa [binaryCollapse] using hbayes
    rw [show q a * binaryCollapse P target a (ULift.up false) *
          (Channel.posterior (branchIndicator target) (P a)
            (ULift.up false) target * Q target a (o, r)) =
        q a * (binaryCollapse P target a (ULift.up false) *
          Channel.posterior (branchIndicator target) (P a)
            (ULift.up false) target) * Q target a (o, r) by ring,
      hz, mul_zero, zero_mul]
    rw [show q a * binaryCollapse P target a (ULift.up false) *
          (Channel.posterior (branchIndicator target) (P a)
            (ULift.up false) target * L target a (o, r)) =
        q a * (binaryCollapse P target a (ULift.up false) *
          Channel.posterior (branchIndicator target) (P a)
            (ULift.up false) target) * L target a (o, r) by ring,
      hz, mul_zero, zero_mul]
  · rw [hoff y hyt]

theorem binarySplit_samePriorJointLaw_of_offTarget
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q L : ∀ y, Channel A (O × Rec y))
    (target : Y) (hoff : ∀ y, y ≠ target → Q y = L y)
    (q : TraceableAgency.Dist A) :
    ∀ a z,
      q a * binaryPayoffCompound (binaryCollapse P target)
          (tagBranchContinuation Rec target (L target))
          (complementContinuation Rec P Q target) a z =
        q a * splitCompound Rec P L target a z := by
  intro a z
  rcases z with ⟨o, b, y, r⟩
  rw [splitCompound_eq_binaryPayoffCompound]
  cases b with
  | up b =>
    cases b
    · simp only [binaryPayoffCompound_apply, binaryContinuationProfile,
        Bool.false_eq_true, if_false]
      simpa [mul_assoc] using
        (weighted_complementContinuation_eq_of_offTarget
          Rec P Q L target hoff q a o y r)
    · simp [binaryPayoffCompound_apply, binaryContinuationProfile]

/-! ## One reached branch -/

theorem pairWeak_tagBranchContinuation_of_pairWeak
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F)
    (r : TraceableAgency.Dist A) (target : Y)
    (K L : Channel A (O × Rec target))
    (hKL : pairWeak F r K r L) :
    pairWeak F r (tagBranchContinuation Rec target K)
      r (tagBranchContinuation Rec target L) := by
  have htagK_K := h6 (tagBranchContinuation Rec target K)
    (eraseBranchTagProcessor Rec target) r
  rw [recordPostprocess_eraseBranchTag] at htagK_K
  have hL_tagL := h6 L (tagBranchRecordProcessor Rec target) r
  change pairWeak F r L r (tagBranchContinuation Rec target L) at hL_tagL
  have htagK_L := pairWeak_transitive_of_structural F h1 h5
    r (tagBranchContinuation Rec target K) r K r L htagK_K hKL
  exact pairWeak_transitive_of_structural F h1 h5
    r (tagBranchContinuation Rec target K) r L
      r (tagBranchContinuation Rec target L) htagK_L hL_tagL

/-- Binary A8 is an exact one-branch insertion principle for an arbitrary
finite first-stage record. -/
theorem pairWeak_oneBranchCompound_of_recordwiseSureThing
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h8 : A8_RecordwiseSureThing F)
    (P : Channel A Y) (Q L : ∀ y, Channel A (O × Rec y))
    (q : TraceableAgency.Dist A) (target : Y)
    (htarget : BranchPositive P q target)
    (hoff : ∀ y, y ≠ target → Q y = L y)
    (hbranch : pairWeak F (branchPosterior P q target) (Q target)
      (branchPosterior P q target) (L target)) :
    pairWeak F q (commonPayoffCompound Rec P Q)
      q (commonPayoffCompound Rec P L) := by
  let BP := binaryCollapse P target
  let TK := tagBranchContinuation Rec target (Q target)
  let TL := tagBranchContinuation Rec target (L target)
  let M := complementContinuation Rec P Q target
  let BK := binaryPayoffCompound BP TK M
  let BL := binaryPayoffCompound BP TL M
  have hpositive : BranchPositive BP q (ULift.up true) := by
    simpa [BP, BranchPositive, outcomeMarginal_binaryCollapse_true] using htarget
  have hposterior : branchPosterior BP q (ULift.up true) =
      branchPosterior P q target := by
    simpa [BP] using branchPosterior_binaryCollapse_true P q target
  have htag : pairWeak F (branchPosterior BP q (ULift.up true)) TK
      (branchPosterior BP q (ULift.up true)) TL := by
    rw [hposterior]
    exact pairWeak_tagBranchContinuation_of_pairWeak
      Rec F h1 h5 h6 (branchPosterior P q target) target
        (Q target) (L target) hbranch
  have hbinary : pairWeak F q BK q BL := by
    exact (h8 q BP TK TL M hpositive).mp htag
  have hflat_splitQ : pairWeak F q (commonPayoffCompound Rec P Q)
      q (splitCompound Rec P Q target) := by
    have hh := h6 (commonPayoffCompound Rec P Q)
      (addSplitTagProcessor Rec target) q
    simpa [recordPostprocess_addSplitTag] using hh
  have hBL_splitL : pairWeak F q BL q (splitCompound Rec P L target) := by
    apply pairWeak_of_samePriorJointLaw F h7 q
    exact binarySplit_samePriorJointLaw_of_offTarget
      Rec P Q L target hoff q
  have hsplitL_flat : pairWeak F q (splitCompound Rec P L target)
      q (commonPayoffCompound Rec P L) := by
    have hh := h6 (splitCompound Rec P L target)
      (eraseSplitTagProcessor Rec) q
    simpa [recordPostprocess_eraseSplitTag] using hh
  have hsplitQ_BL : pairWeak F q (splitCompound Rec P Q target) q BL := by
    simpa [BK, splitCompound_eq_binaryPayoffCompound] using hbinary
  have hflat_BL := pairWeak_transitive_of_structural F h1 h5
    q (commonPayoffCompound Rec P Q) q (splitCompound Rec P Q target)
      q BL hflat_splitQ hsplitQ_BL
  have hflat_splitL := pairWeak_transitive_of_structural F h1 h5
    q (commonPayoffCompound Rec P Q) q BL
      q (splitCompound Rec P L target) hflat_BL hBL_splitL
  exact pairWeak_transitive_of_structural F h1 h5
    q (commonPayoffCompound Rec P Q) q (splitCompound Rec P L target)
      q (commonPayoffCompound Rec P L) hflat_splitL hsplitL_flat

theorem compound_samePriorJointLaw_of_nullBranch
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (P : Channel A Y) (Q L : ∀ y, Channel A (O × Rec y))
    (q : TraceableAgency.Dist A) (target : Y)
    (hnull : ¬ BranchPositive P q target)
    (hoff : ∀ y, y ≠ target → Q y = L y) :
    ∀ a z,
      q a * commonPayoffCompound Rec P Q a z =
        q a * commonPayoffCompound Rec P L a z := by
  intro a z
  rcases z with ⟨o, y, r⟩
  by_cases hyt : y = target
  · subst y
    have hmnonneg : 0 ≤ Channel.outcomeMarginal P q target :=
      (Channel.outcomeMarginal P q).nonneg target
    have hmzero : Channel.outcomeMarginal P q target = 0 := by
      apply le_antisymm
      · exact le_of_not_gt hnull
      · exact hmnonneg
    have hterm_le : q a * P a target ≤
        Channel.outcomeMarginal P q target := by
      exact Finset.single_le_sum
        (fun a' _ => mul_nonneg (q.nonneg a') ((P a').nonneg target))
        (Finset.mem_univ a)
    have hterm : q a * P a target = 0 := by
      have hterm_nonneg := mul_nonneg (q.nonneg a) ((P a).nonneg target)
      linarith
    simp only [commonPayoffCompound_apply]
    rw [show q a * (P a target * Q target a (o, r)) =
        (q a * P a target) * Q target a (o, r) by ring,
      hterm, zero_mul]
    rw [show q a * (P a target * L target a (o, r)) =
        (q a * P a target) * L target a (o, r) by ring,
      hterm, zero_mul]
  · rw [commonPayoffCompound_apply, commonPayoffCompound_apply, hoff y hyt]

theorem pairStrict_tagBranchContinuation_of_pairStrict
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (r : TraceableAgency.Dist A) (target : Y)
    (K L : Channel A (O × Rec target))
    (hKL : pairStrict F r K r L) :
    pairStrict F r (tagBranchContinuation Rec target K)
      r (tagBranchContinuation Rec target L) := by
  have htagK_K := h6 (tagBranchContinuation Rec target K)
    (eraseBranchTagProcessor Rec target) r
  rw [recordPostprocess_eraseBranchTag] at htagK_K
  have hL_tagL := h6 L (tagBranchRecordProcessor Rec target) r
  change pairWeak F r L r (tagBranchContinuation Rec target L) at hL_tagL
  exact pairStrict_transport_of_structural F h1 h5 h6 h7
    r K r L r (tagBranchContinuation Rec target K)
      r (tagBranchContinuation Rec target L) hKL htagK_K hL_tagL

theorem pairStrict_oneBranchCompound_of_recordwiseSureThing
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h8 : A8_RecordwiseSureThing F)
    (P : Channel A Y) (Q L : ∀ y, Channel A (O × Rec y))
    (q : TraceableAgency.Dist A) (target : Y)
    (htarget : BranchPositive P q target)
    (hoff : ∀ y, y ≠ target → Q y = L y)
    (hbranch : pairStrict F (branchPosterior P q target) (Q target)
      (branchPosterior P q target) (L target)) :
    pairStrict F q (commonPayoffCompound Rec P Q)
      q (commonPayoffCompound Rec P L) := by
  let BP := binaryCollapse P target
  let TK := tagBranchContinuation Rec target (Q target)
  let TL := tagBranchContinuation Rec target (L target)
  let M := complementContinuation Rec P Q target
  let BK := binaryPayoffCompound BP TK M
  let BL := binaryPayoffCompound BP TL M
  have hpositive : BranchPositive BP q (ULift.up true) := by
    simpa [BP, BranchPositive, outcomeMarginal_binaryCollapse_true] using htarget
  have hposterior : branchPosterior BP q (ULift.up true) =
      branchPosterior P q target := by
    simpa [BP] using branchPosterior_binaryCollapse_true P q target
  have htagStrict : pairStrict F
      (branchPosterior BP q (ULift.up true)) TK
      (branchPosterior BP q (ULift.up true)) TL := by
    rw [hposterior]
    exact pairStrict_tagBranchContinuation_of_pairStrict
      Rec F h1 h5 h6 h7 (branchPosterior P q target) target
        (Q target) (L target) hbranch
  have htagParts := (pairStrict_iff_pairWeak_not_swap
    F h1 h5 h6 h7 (branchPosterior BP q (ULift.up true)) TK
      (branchPosterior BP q (ULift.up true)) TL).mp htagStrict
  have hbinaryStrict : pairStrict F q BK q BL := by
    apply (pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7 q BK q BL).mpr
    constructor
    · exact (h8 q BP TK TL M hpositive).mp htagParts.1
    · intro hreverse
      exact htagParts.2 ((h8 q BP TL TK M hpositive).mpr hreverse)
  have hflat_BK : pairWeak F q (commonPayoffCompound Rec P Q) q BK := by
    have hh := h6 (commonPayoffCompound Rec P Q)
      (addSplitTagProcessor Rec target) q
    rw [recordPostprocess_addSplitTag] at hh
    simpa [BK, splitCompound_eq_binaryPayoffCompound] using hh
  have hBL_splitL : pairWeak F q BL q (splitCompound Rec P L target) := by
    apply pairWeak_of_samePriorJointLaw F h7 q
    exact binarySplit_samePriorJointLaw_of_offTarget
      Rec P Q L target hoff q
  have hsplitL_flat : pairWeak F q (splitCompound Rec P L target)
      q (commonPayoffCompound Rec P L) := by
    have hh := h6 (splitCompound Rec P L target)
      (eraseSplitTagProcessor Rec) q
    simpa [recordPostprocess_eraseSplitTag] using hh
  have hBL_flat := pairWeak_transitive_of_structural F h1 h5
    q BL q (splitCompound Rec P L target)
      q (commonPayoffCompound Rec P L) hBL_splitL hsplitL_flat
  exact pairStrict_transport_of_structural F h1 h5 h6 h7
    q BK q BL q (commonPayoffCompound Rec P Q)
      q (commonPayoffCompound Rec P L) hbinaryStrict hflat_BK hBL_flat

/-! ## Finite replacement -/

def finiteBranchHybrid
    {O A Y : Type u}
    [Fintype O] [Fintype A] [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u) [∀ y, Fintype (Rec y)]
    (K L : ∀ y, Channel A (O × Rec y))
    (s : Finset Y) (y : Y) : Channel A (O × Rec y) :=
  if y ∈ s then L y else K y

theorem finiteBranchConsistency_weak_of_recordwiseSureThing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h8 : A8_RecordwiseSureThing F) :
    FiniteBranchContinuationConsistency_Weak F := by
  intro A Y _ _ _ _ _ _ Rec _ _ _ P K L q hbranch
  classical
  have hind : ∀ s : Finset Y,
      pairWeak F q (commonPayoffCompound Rec P K)
        q (commonPayoffCompound Rec P (finiteBranchHybrid Rec K L s)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have hprofile : finiteBranchHybrid Rec K L ∅ = K := by
          funext y
          simp [finiteBranchHybrid]
        rw [hprofile]
        have hrefl := pairWeak_refl_of_structural F h1 h5 q
          (commonPayoffCompound Rec P K)
        exact hrefl
    | @insert target s hnotmem ih =>
        let Q := finiteBranchHybrid Rec K L s
        let Q' := finiteBranchHybrid Rec K L (insert target s)
        have hoff : ∀ y, y ≠ target → Q y = Q' y := by
          intro y hyt
          simp [Q, Q', finiteBranchHybrid, hyt]
        have hstep : pairWeak F q (commonPayoffCompound Rec P Q)
            q (commonPayoffCompound Rec P Q') := by
          by_cases htarget : BranchPositive P q target
          · apply pairWeak_oneBranchCompound_of_recordwiseSureThing
              Rec F h1 h5 h6 h7 h8 P Q Q' q target htarget hoff
            simpa [Q, Q', finiteBranchHybrid, hnotmem] using
              hbranch target htarget
          · apply pairWeak_of_samePriorJointLaw F h7 q
            exact compound_samePriorJointLaw_of_nullBranch
              Rec P Q Q' q target htarget hoff
        exact pairWeak_transitive_of_structural F h1 h5
          q (commonPayoffCompound Rec P K)
          q (commonPayoffCompound Rec P Q)
          q (commonPayoffCompound Rec P Q') ih hstep
  have hprofile : finiteBranchHybrid Rec K L Finset.univ = L := by
    funext y
    simp [finiteBranchHybrid]
  have hfinal := hind Finset.univ
  rw [hprofile] at hfinal
  exact hfinal

theorem finiteBranchConsistency_strict_of_recordwiseSureThing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h8 : A8_RecordwiseSureThing F) :
    FiniteBranchContinuationConsistency_Strict F := by
  intro A Y _ _ _ _ _ _ Rec _ _ _ P K L q hweak hsome
  classical
  obtain ⟨target, htarget, hstrict⟩ := hsome
  let Q := finiteBranchHybrid Rec K L {target}
  have hoff : ∀ y, y ≠ target → K y = Q y := by
    intro y hyt
    simp [Q, finiteBranchHybrid, hyt]
  have hfirst : pairStrict F q (commonPayoffCompound Rec P K)
      q (commonPayoffCompound Rec P Q) := by
    apply pairStrict_oneBranchCompound_of_recordwiseSureThing
      Rec F h1 h5 h6 h7 h8 P K Q q target htarget hoff
    simpa [Q, finiteBranchHybrid] using hstrict
  have htailBranch : ∀ y, BranchPositive P q y →
      pairWeak F (branchPosterior P q y) (Q y)
        (branchPosterior P q y) (L y) := by
    intro y hy
    by_cases hyt : y = target
    · subst y
      simpa [Q, finiteBranchHybrid] using
        pairWeak_refl_of_structural F h1 h5
          (branchPosterior P q target) (L target)
    · simpa [Q, finiteBranchHybrid, hyt] using hweak y hy
  have htail : pairWeak F q (commonPayoffCompound Rec P Q)
      q (commonPayoffCompound Rec P L) :=
    finiteBranchConsistency_weak_of_recordwiseSureThing
      F h1 h5 h6 h7 h8 Rec P Q L q htailBranch
  have hrefl := pairWeak_refl_of_structural F h1 h5 q
    (commonPayoffCompound Rec P K)
  exact pairStrict_transport_of_structural F h1 h5 h6 h7
    q (commonPayoffCompound Rec P K) q (commonPayoffCompound Rec P Q)
    q (commonPayoffCompound Rec P K) q (commonPayoffCompound Rec P L)
      hfirst hrefl htail

/-- Forward half of the v5 finite-branch extension lemma. -/
theorem finiteBranchContinuationConsistency_of_recordwiseSureThing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h8 : A8_RecordwiseSureThing F) :
    FiniteBranchContinuationConsistency F :=
  ⟨finiteBranchConsistency_weak_of_recordwiseSureThing
      F h1 h5 h6 h7 h8,
    finiteBranchConsistency_strict_of_recordwiseSureThing
      F h1 h5 h6 h7 h8⟩

theorem pairWeak_complete_of_structural
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ∨ pairWeak F p L q K := by
  let C := commonPayoffBlockChannel K L
  rcases (h1 C).1 (leftBlockDist q) (rightBlockDist p) with hqp | hpq
  · exact Or.inl hqp
  · exact Or.inr
      ((sameBlock_reverse_iff_pairWeak_swap F h1 h5 h6 h7 q K p L).mp hpq)

/-- Reverse half of the finite-branch extension lemma. -/
theorem recordwiseSureThing_of_finiteBranchContinuationConsistency
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (hfinite : FiniteBranchContinuationConsistency F) :
    A8_RecordwiseSureThing F := by
  intro A R _ _ _ _ _ _ q P K L M hpositive
  let Q := binaryContinuationProfile K M
  let Q' := binaryContinuationProfile L M
  have hfalse : Q (ULift.up false) = Q' (ULift.up false) := rfl
  constructor
  · intro hKL
    have hbranches : ∀ b, BranchPositive P q b →
        pairWeak F (branchPosterior P q b) (Q b)
          (branchPosterior P q b) (Q' b) := by
      intro b _hb
      cases b with
      | up b =>
        cases b
        · simpa [Q, Q', binaryContinuationProfile] using
            pairWeak_refl_of_structural F h1 h5
              (branchPosterior P q (ULift.up false)) M
        · simpa [Q, Q', binaryContinuationProfile] using hKL
    simpa [Q, Q', binaryPayoffCompound] using
      hfinite.1 (fun _ : RelevanceBit => R) P Q Q' q hbranches
  · intro haggregate
    by_contra hnot
    have hLK : pairWeak F (branchPosterior P q (ULift.up true)) L
        (branchPosterior P q (ULift.up true)) K := by
      rcases pairWeak_complete_of_structural F h1 h5 h6 h7
          (branchPosterior P q (ULift.up true)) K
          (branchPosterior P q (ULift.up true)) L with h | h
      · exact False.elim (hnot h)
      · exact h
    have hstrict : pairStrict F (branchPosterior P q (ULift.up true)) L
        (branchPosterior P q (ULift.up true)) K :=
      (pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7
        (branchPosterior P q (ULift.up true)) L
        (branchPosterior P q (ULift.up true)) K).mpr ⟨hLK, hnot⟩
    have hbranches : ∀ b, BranchPositive P q b →
        pairWeak F (branchPosterior P q b) (Q' b)
          (branchPosterior P q b) (Q b) := by
      intro b _hb
      cases b with
      | up b =>
        cases b
        · simpa [Q, Q', binaryContinuationProfile] using
            pairWeak_refl_of_structural F h1 h5
              (branchPosterior P q (ULift.up false)) M
        · simpa [Q, Q', binaryContinuationProfile] using hLK
    have hsome : ∃ b, BranchPositive P q b ∧
        pairStrict F (branchPosterior P q b) (Q' b)
          (branchPosterior P q b) (Q b) := by
      refine ⟨ULift.up true, hpositive, ?_⟩
      simpa [Q, Q', binaryContinuationProfile] using hstrict
    have hreverse := hfinite.2 (fun _ : RelevanceBit => R)
      P Q' Q q hbranches hsome
    have hparts := (pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7
      q (binaryPayoffCompound P L M)
      q (binaryPayoffCompound P K M)).mp
        (by simpa [Q, Q', binaryPayoffCompound] using hreverse)
    exact hparts.2 haggregate

/-- V5 Lemma (finite-branch extension): under A1 and A5--A7, binary A8 is
equivalent to the weak-and-strict finite-branch property used by the proof. -/
theorem recordwiseSureThing_iff_finiteBranchContinuationConsistency
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F) :
    A8_RecordwiseSureThing F ↔ FiniteBranchContinuationConsistency F := by
  constructor
  · exact finiteBranchContinuationConsistency_of_recordwiseSureThing
      F h1 h5 h6 h7
  · exact recordwiseSureThing_of_finiteBranchContinuationConsistency
      F h1 h5 h6 h7

end TraceableAgency.Theorem1
