/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.Statements

/-!
# The constant-payoff pure-trace bridge

Fixing one material payoff turns every ordinary finite channel into a joint
payoff-record channel.  This file records that construction and transfers the
paper axioms to the already kernel-checked pure-trace theorem.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open Filter Topology
open TraceableAgency

universe u

/-! ## Constant-payoff lift -/

/-- Attach the sure payoff `o` to every visible record of a pure channel. -/
noncomputable def constantPayoffLift
    {O A R : Type u}
    [Fintype O] [DecidableEq O] [Fintype R]
    (o : O) (P : Channel A R) : Channel A (O × R) :=
  fun a =>
    { prob := fun z => if z.1 = o then P a z.2 else 0
      nonneg := fun z => by
        split_ifs
        · exact (P a).nonneg z.2
        · exact le_rfl
      sum_eq_one := by
        rw [Fintype.sum_prod_type]
        simp [← Finset.mul_sum, (P a).sum_eq_one] }

@[simp]
theorem constantPayoffLift_apply
    {O A R : Type u}
    [Fintype O] [DecidableEq O] [Fintype R]
    (o : O) (P : Channel A R) (a : A) (o' : O) (r : R) :
    constantPayoffLift o P a (o', r) = if o' = o then P a r else 0 :=
  rfl

@[simp]
theorem constantPayoffLift_apply_same
    {O A R : Type u}
    [Fintype O] [DecidableEq O] [Fintype R]
    (o : O) (P : Channel A R) (a : A) (r : R) :
    constantPayoffLift o P a (o, r) = P a r := by
  simp

/-- The pure preference family induced by one sure payoff.  A distribution
argument supplies nonemptiness of the action alphabet, and one channel row
then supplies nonemptiness of the record alphabet, so this is total on the
older `PrefFamily` domain without adding a domain axiom. -/
noncomputable def inducedPureTraceFamily
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O) : PrefFamily.{u} where
  rel := by
    intro A R _ _ _ _ P q p
    letI : Nonempty A := Relabeling.nonempty_of_dist q
    letI : Nonempty R :=
      Relabeling.nonempty_of_dist (P (Classical.choice (inferInstance : Nonempty A)))
    exact F.rel (constantPayoffLift o P) q p

@[simp]
theorem inducedPureTraceFamily_rel
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (o : O)
    (P : Channel A R) (q p : TraceableAgency.Dist A) :
    (inducedPureTraceFamily F o).rel P q p =
      F.rel (constantPayoffLift o P) q p := by
  rfl

/-! ## Constructor compatibility -/

theorem constantPayoffLift_blockChannel
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (o : O) (P : Channel A R) (Q : Channel B S) :
    constantPayoffLift o (blockChannel P Q) =
      commonPayoffBlockChannel (constantPayoffLift o P)
        (constantPayoffLift o Q) := by
  classical
  ext ab z
  cases ab with
  | inl a =>
      rcases z with ⟨o', rs⟩
      cases rs <;> simp [constantPayoffLift, commonPayoffBlockChannel,
        Relabeling.relabelChannel, Relabeling.relabelDist,
        sumPayoffRecordEquiv, blockChannel]
  | inr b =>
      rcases z with ⟨o', rs⟩
      cases rs <;> simp [constantPayoffLift, commonPayoffBlockChannel,
        Relabeling.relabelChannel, Relabeling.relabelDist,
        sumPayoffRecordEquiv, blockChannel]

theorem constantPayoffLift_blockFamilyChannel
    {I O : Type u} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    (o : O) (P : ∀ i, Channel (Act i) (Rec i)) :
    constantPayoffLift o (blockFamilyChannel Act Rec P) =
      commonPayoffBlockFamilyChannel Act Rec
        (fun i => constantPayoffLift o (P i)) := by
  classical
  ext ia z
  rcases ia with ⟨i, a⟩
  rcases z with ⟨o', j, r⟩
  by_cases hij : i = j
  · subst j
    simp [constantPayoffLift, commonPayoffBlockFamilyChannel,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      sigmaPayoffRecordEquiv, blockFamilyChannel, blockFamilyProb]
  · simp [constantPayoffLift, commonPayoffBlockFamilyChannel,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      sigmaPayoffRecordEquiv, blockFamilyChannel, blockFamilyProb, hij]

theorem constantPayoffLift_idChannel
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (o : O) :
    constantPayoffLift o (Channel.idChannel : Channel A A) =
      fullRevealAtPayoff o := by
  ext a z
  rcases z with ⟨o', a'⟩
  by_cases ho : o' = o <;> by_cases ha : a' = a <;>
    simp [constantPayoffLift, Channel.idChannel, fullRevealAtPayoff,
      TraceableAgency.Dist.pure_apply, ho, ha]

theorem constantPayoffLift_uninformative
    {O A : Type u}
    [Fintype O] [DecidableEq O] [Fintype A]
    (o : O) :
    constantPayoffLift o (Channel.uninformativeChannelU A) =
      uninformativeAtPayoff o := by
  ext a z
  rcases z with ⟨o', u⟩
  cases u
  simp [constantPayoffLift, Channel.uninformativeChannelU,
    uninformativeAtPayoff, TraceableAgency.Dist.pure_apply]

/-- A pure record processor viewed as a payoff-preserving processor. -/
def liftRecordProcessor
    {O R S : Type u} [Fintype S]
    (T : Channel R S) : RecordProcessor O R S :=
  fun z => T z.2

theorem constantPayoffLift_postprocess
    {O A R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (o : O) (P : Channel A R) (T : Channel R S) :
    constantPayoffLift o (Channel.postprocess P T) =
      recordPostprocess (constantPayoffLift o P)
        (liftRecordProcessor T) := by
  classical
  ext a z
  rcases z with ⟨o', s⟩
  by_cases h : o' = o
  · subst o'
    simp [constantPayoffLift, Channel.postprocess, recordPostprocess,
      payoffPreservingRecordKernel, liftRecordProcessor,
      Fintype.sum_prod_type]
  · simp [constantPayoffLift, Channel.postprocess, recordPostprocess,
      payoffPreservingRecordKernel, liftRecordProcessor,
      Fintype.sum_prod_type, h]

theorem constantPayoffLift_seqComposeDep
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (o : O) (P : Channel A Y) (K : ∀ y, Channel A (Rec y)) :
    constantPayoffLift o (seqComposeDep P Rec K) =
      commonPayoffCompound Rec P (fun y => constantPayoffLift o (K y)) := by
  classical
  ext a z
  rcases z with ⟨o', y, r⟩
  simp [constantPayoffLift, commonPayoffCompound,
    Relabeling.relabelChannel, Relabeling.relabelDist,
    compoundPayoffRecordEquiv, sigmaPayoffRecordEquiv,
    seqComposeDep, seqComposeDepProb]

theorem constantPayoffLift_converges
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R] [DecidableEq R]
    (o : O) (Pseq : ℕ → Channel A R) (P : Channel A R)
    (h : ChannelConverges Pseq P) :
    ChannelConverges (fun n => constantPayoffLift o (Pseq n))
      (constantPayoffLift o P) := by
  intro a z
  rcases z with ⟨o', r⟩
  by_cases ho : o' = o
  · subst o'
    simpa using h a r
  · simpa [constantPayoffLift, ho] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝒩 0))

theorem constantPayoffLift_actionRelabel
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype B]
    [Fintype R] [DecidableEq R]
    (o : O) (e : A ≃ B) (P : Channel A R) :
    Relabeling.relabelChannel e (Equiv.refl (O × R))
        (constantPayoffLift o P) =
      constantPayoffLift o
        (Relabeling.relabelChannel e (Equiv.refl R) P) := by
  ext b z
  rfl

/-! ## Exact action-report completion -/

theorem bayesCompletion_jointEquation
    {A B R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    [Fintype R]
    (P : Channel A R) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Phat : Channel B R)
    (hcompl : Channel.IsBayesPushforwardCompletion P q S Phat) :
    ∀ b r,
      Channel.actionPushforward q S b * Phat b r =
        ∑ a, q a * S a b * P a r := by
  intro b r
  by_cases hb : 0 < Channel.actionPushforward q S b
  · rw [hcompl b hb r]
    field_simp [ne_of_gt hb]
  · have hbzero : Channel.actionPushforward q S b = 0 :=
      le_antisymm (le_of_not_gt hb)
        ((Channel.actionPushforward q S).nonneg b)
    have hcoeff : ∀ a : A, q a * S a b = 0 := by
      intro a
      have hle : q a * S a b ≤ ∑ x : A, q x * S x b :=
        Finset.single_le_sum
          (fun x _ => mul_nonneg (q.nonneg x) ((S x).nonneg b))
          (Finset.mem_univ a)
      change q a * S a b ≤ Channel.actionPushforward q S b at hle
      exact le_antisymm (by simpa [hbzero] using hle)
        (mul_nonneg (q.nonneg a) ((S a).nonneg b))
    simp [hbzero, hcoeff]

theorem constantPayoffLift_actionCompletion
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    [Fintype R]
    (o : O) (P : Channel A R) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Phat : Channel B R)
    (hcompl : Channel.IsBayesPushforwardCompletion P q S Phat) :
    IsActionReportCompletion (constantPayoffLift o P) q S
      (constantPayoffLift o Phat) := by
  intro b z
  rcases z with ⟨o', r⟩
  by_cases ho : o' = o
  · subst o'
    simpa [constantPayoffLift] using
      (bayesCompletion_jointEquation P q S Phat hcompl b r)
  · simp [constantPayoffLift, ho]

/-! ## Replacement inside a common-payoff four-block environment -/

/-- Record alphabets for the common four-block replacement environment. -/
abbrev fixedReplacementRec
    (R S : Type u) : Relabeling.RelabelReplacementBlock → Type u :=
  Relabeling.relabelReplacementOut R S

/-- Joint channels for the common four-block replacement environment. -/
noncomputable def fixedReplacementChannel
    {O A B R S : Type u} [Fintype O] [Fintype R] [Fintype S]
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    ∀ k : Relabeling.RelabelReplacementBlock,
      Channel (Relabeling.relabelReplacementAct A B k)
        (O × fixedReplacementRec R S k)
  | .oldLeft => K
  | .newLeft => L
  | .oldRight => K
  | .newRight => L

/-- If both lotteries are weakly equivalent before and after replacing one
joint channel by another, every comparison between them is preserved.  The
proof is exactly the common four-block transitivity argument used by Appendix
D, now with the material payoff coordinate kept untagged. -/
theorem fixed_pairwiseReplacement_from_weakEquiv
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (K : Channel A (O × R)) (L : Channel B (O × S))
    (q r : TraceableAgency.Dist A) (q' r' : TraceableAgency.Dist B)
    (hq_to_new : pairWeak F q K q' L)
    (hq_to_old : pairWeak F q' L q K)
    (hr_to_new : pairWeak F r K r' L)
    (hr_to_old : pairWeak F r' L r K) :
    F.rel K q r ↔ F.rel L q' r' := by
  classical
  let k0 : Relabeling.RelabelReplacementBlock.{u} := .oldLeft
  let k1 : Relabeling.RelabelReplacementBlock.{u} := .newLeft
  let k2 : Relabeling.RelabelReplacementBlock.{u} := .oldRight
  let k3 : Relabeling.RelabelReplacementBlock.{u} := .newRight
  let Act := Relabeling.relabelReplacementAct A B
  let Rec := fixedReplacementRec R S
  let C := fixedReplacementChannel K L
  letI : Nonempty Relabeling.RelabelReplacementBlock := ⟨.oldLeft⟩
  letI : ∀ k, Nonempty (Act k) := fun k => by
    cases k <;>
      simp [Act, Relabeling.relabelReplacementAct] <;>
      infer_instance
  letI : ∀ k, Nonempty (Rec k) := fun k => by
    cases k <;>
      simp [Rec, fixedReplacementRec, Relabeling.relabelReplacementOut] <;>
      infer_instance
  let commonK := commonPayoffBlockFamilyChannel Act Rec C
  let x := commonPayoffBlockEmbed Act k0 q
  let x' := commonPayoffBlockEmbed Act k1 q'
  let y := commonPayoffBlockEmbed Act k2 r
  let y' := commonPayoffBlockEmbed Act k3 r'
  have htrans :
      ∀ a b c : TraceableAgency.Dist
          ((k : Relabeling.RelabelReplacementBlock) × Act k),
        F.rel commonK a b → F.rel commonK b c → F.rel commonK a c :=
    (h1 commonK).2
  have h02 : k0 ≠ k2 := by decide
  have h01 : k0 ≠ k1 := by decide
  have h10 : k1 ≠ k0 := by decide
  have h23 : k2 ≠ k3 := by decide
  have h32 : k3 ≠ k2 := by decide
  have h13 : k1 ≠ k3 := by decide
  have hleft :
      F.rel K q r ↔ pairWeak F q K r K := h3.duplication K q r
  have hright :
      F.rel L q' r' ↔ pairWeak F q' L r' L := h3.duplication L q' r'
  have hcommon02 :
      F.rel commonK x y ↔ pairWeak F q K r K := by
    have hh := h3.irrelevant_blocks Act Rec C k0 k2 h02 q r
    change F.rel commonK x y ↔ pairWeak F q (C k0) r (C k2) at hh
    have hc0 : C k0 = K := by rfl
    have hc2 : C k2 = K := by rfl
    rw [hc0, hc2] at hh
    exact hh
  have hcommon01 : F.rel commonK x x' := by
    have hh := (h3.irrelevant_blocks Act Rec C k0 k1 h01 q q').mpr hq_to_new
    change F.rel commonK x x' at hh
    exact hh
  have hcommon10 : F.rel commonK x' x := by
    have hh := (h3.irrelevant_blocks Act Rec C k1 k0 h10 q' q).mpr hq_to_old
    change F.rel commonK x' x at hh
    exact hh
  have hcommon23 : F.rel commonK y y' := by
    have hh := (h3.irrelevant_blocks Act Rec C k2 k3 h23 r r').mpr hr_to_new
    change F.rel commonK y y' at hh
    exact hh
  have hcommon32 : F.rel commonK y' y := by
    have hh := (h3.irrelevant_blocks Act Rec C k3 k2 h32 r' r).mpr hr_to_old
    change F.rel commonK y' y at hh
    exact hh
  have hreplace : F.rel commonK x y ↔ F.rel commonK x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonK a b) htrans
      hcommon01 hcommon10 hcommon23 hcommon32
  have hcommon13 :
      F.rel commonK x' y' ↔ pairWeak F q' L r' L := by
    have hh := h3.irrelevant_blocks Act Rec C k1 k3 h13 q' r'
    change F.rel commonK x' y' ↔ pairWeak F q' (C k1) r' (C k3) at hh
    have hc1 : C k1 = L := by rfl
    have hc3 : C k3 = L := by rfl
    rw [hc1, hc3] at hh
    exact hh
  exact hleft.trans
    (hcommon02.symm.trans (hreplace.trans (hcommon13.trans hright.symm)))

/-- Mutual payoff-preserving simulations make two joint channels ordinally
interchangeable. -/
theorem fixed_rel_iff_of_mutualRecordProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    {A R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (K : Channel A (O × R)) (L : Channel A (O × S))
    (T : RecordProcessor O R S) (U : RecordProcessor O S R)
    (hKL : recordPostprocess K T = L)
    (hLK : recordPostprocess L U = K)
    (q r : TraceableAgency.Dist A) :
    F.rel K q r ↔ F.rel L q r := by
  apply fixed_pairwiseReplacement_from_weakEquiv F h1 h3 K L q r q r
  · simpa [hKL] using h4 K T q
  · simpa [hLK] using h4 L U q
  · simpa [hKL] using h4 K T r
  · simpa [hLK] using h4 L U r

/-- The positive-row Bayesian completion equation is equivalent to the exact
joint-law equation once zero reported rows are handled by nonnegativity. -/
theorem actionCompletion_isExact
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R))
    (hcompl : Channel.IsBayesPushforwardCompletion K q S Khat) :
    IsActionReportCompletion K q S Khat := by
  exact bayesCompletion_jointEquation K q S Khat hcompl

/-- A deterministic relabeling of actions preserves every within-channel
comparison.  This is derived from exact A5 in both directions and the
four-block replacement lemma, rather than assumed as a convention. -/
theorem fixed_rel_iff_actionEquiv
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (h5 : A5_ActionDataProcessing F)
    {A B R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (e : A ≃ B) (K : Channel A (O × R))
    (q r : TraceableAgency.Dist A) :
    F.rel K q r ↔
      F.rel (Relabeling.relabelChannel e (Equiv.refl (O × R)) K)
        (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) := by
  let K' := Relabeling.relabelChannel e (Equiv.refl (O × R)) K
  let q' := Relabeling.relabelDist e q
  let r' := Relabeling.relabelDist e r
  have qforward : pairWeak F q K q' K' := by
    have hh := h5 K q (Relabeling.actionEquivKernel e) K'
      (actionCompletion_isExact K q (Relabeling.actionEquivKernel e) K'
        (Relabeling.relabelChannel_isBayesPushforwardCompletion e K q))
    simpa [q', K', Relabeling.actionPushforward_equiv] using hh
  have qback : pairWeak F q' K' q K := by
    have hh := h5 K' q' (Relabeling.actionEquivKernel e.symm) K
      (actionCompletion_isExact K' q' (Relabeling.actionEquivKernel e.symm) K
        (by
          simpa [K', q'] using
            (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion e K q)))
    simpa [q', K', Relabeling.actionPushforward_equiv,
      Relabeling.relabelDist_symm] using hh
  have rforward : pairWeak F r K r' K' := by
    have hh := h5 K r (Relabeling.actionEquivKernel e) K'
      (actionCompletion_isExact K r (Relabeling.actionEquivKernel e) K'
        (Relabeling.relabelChannel_isBayesPushforwardCompletion e K r))
    simpa [r', K', Relabeling.actionPushforward_equiv] using hh
  have rback : pairWeak F r' K' r K := by
    have hh := h5 K' r' (Relabeling.actionEquivKernel e.symm) K
      (actionCompletion_isExact K' r' (Relabeling.actionEquivKernel e.symm) K
        (by
          simpa [K', r'] using
            (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion e K r)))
    simpa [r', K', Relabeling.actionPushforward_equiv,
      Relabeling.relabelDist_symm] using hh
  exact fixed_pairwiseReplacement_from_weakEquiv F h1 h3
    K K' q r q' r' qforward qback rforward rback

/-! ## Removing unused empty blocks -/

/-- Indices whose action fibre is inhabited. -/
abbrev ActiveBlock
    {I : Type u} (Act : I → Type u) [∀ i, Fintype (Act i)] :=
  {i : I // 0 < Fintype.card (Act i)}

/-- Action fibres of the active restriction. -/
abbrev activeAct
    {I : Type u} (Act : I → Type u) [∀ i, Fintype (Act i)]
    (j : ActiveBlock Act) : Type u :=
  Act j.1

/-- Record fibres of the active restriction. -/
abbrev activeRec
    {I : Type u} (Act Rec : I → Type u) [∀ i, Fintype (Act i)]
    (j : ActiveBlock Act) : Type u :=
  Rec j.1

/-- Removing empty action fibres does not change the aggregate action type. -/
def activeBlockActionEquiv
    {I : Type u} (Act : I → Type u) [∀ i, Fintype (Act i)] :
    ((i : I) × Act i) ≃ ((j : ActiveBlock Act) × activeAct Act j) where
  toFun x := ⟨⟨x.1, Fintype.card_pos_iff.mpr ⟨x.2⟩⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv := by
    intro x
    rcases x with ⟨i, a⟩
    rfl
  right_inv := by
    intro x
    rcases x with ⟨⟨i, hi⟩, a⟩
    rfl

/-- Include an active record label into the original aggregate alphabet. -/
def activeRecordInclusion
    {I : Type u} (Act Rec : I → Type u) [∀ i, Fintype (Act i)] :
    ((j : ActiveBlock Act) × activeRec Act Rec j) → ((i : I) × Rec i)
  | ⟨j, r⟩ => ⟨j.1, r⟩

/-- Project an original record label to the active restriction.  Labels of
inactive blocks are unreachable and may all be sent to one fixed fallback. -/
noncomputable def activeRecordProjection
    {I : Type u} (Act Rec : I → Type u) [∀ i, Fintype (Act i)]
    (fallback : (j : ActiveBlock Act) × activeRec Act Rec j) :
    ((i : I) × Rec i) → ((j : ActiveBlock Act) × activeRec Act Rec j)
  | ⟨i, r⟩ =>
      if hi : 0 < Fintype.card (Act i) then ⟨⟨i, hi⟩, r⟩ else fallback

/-- Finite deterministic channel induced by a function. -/
noncomputable def deterministicFiniteChannel
    {X Y : Type u} [Fintype Y] [DecidableEq Y]
    (f : X → Y) : Channel X Y :=
  fun x => TraceableAgency.Dist.pure (f x)

theorem relabel_blockEmbed_active
    {I : Type u} [Fintype I] [DecidableEq I]
    (Act : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    (i : I) (q : TraceableAgency.Dist (Act i)) :
    let ji : ActiveBlock Act :=
      ⟨i, Fintype.card_pos_iff.mpr (Relabeling.nonempty_of_dist q)⟩
    Relabeling.relabelDist (activeBlockActionEquiv Act)
        (blockEmbedDist Act i q) =
      blockEmbedDist (activeAct Act) ji q := by
  classical
  dsimp
  ext x
  rcases x with ⟨⟨k, hk⟩, a⟩
  by_cases hki : k = i
  · subst k
    simp [Relabeling.relabelDist, activeBlockActionEquiv,
      blockEmbedDist, blockEmbedProb]
  · have hsub : (⟨k, hk⟩ : ActiveBlock Act) ≠
        ⟨i, Fintype.card_pos_iff.mpr (Relabeling.nonempty_of_dist q)⟩ := by
      intro h
      exact hki (congrArg Subtype.val h)
    simp [Relabeling.relabelDist, activeBlockActionEquiv,
      blockEmbedDist, blockEmbedProb, hki, hsub]

/-- Projecting unreachable inactive-block record labels recovers the active
block channel after the canonical action relabeling. -/
theorem postprocess_activeProjection
    {I : Type u} [Fintype I] [DecidableEq I]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    (P : ∀ i, Channel (Act i) (Rec i))
    (fallback : (j : ActiveBlock Act) × activeRec Act Rec j) :
    Channel.postprocess
        (Relabeling.relabelChannel (activeBlockActionEquiv Act)
          (Equiv.refl ((i : I) × Rec i))
          (blockFamilyChannel Act Rec P))
        (deterministicFiniteChannel (activeRecordProjection Act Rec fallback)) =
      blockFamilyChannel (activeAct Act) (activeRec Act Rec)
        (fun j => P j.1) := by
  classical
  ext ja lr
  rcases ja with ⟨⟨j, hj⟩, a⟩
  rcases lr with ⟨⟨l, hl⟩, r⟩
  by_cases hjl : j = l
  · subst l
    simp [Channel.postprocess, deterministicFiniteChannel,
      activeRecordProjection, activeBlockActionEquiv,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      blockFamilyChannel, blockFamilyProb, Fintype.sum_sigma, hj]
    rw [Finset.sum_eq_single r]
    · simp
    · intro x _ hx
      have hne :
          (⟨⟨j, Fintype.card_pos_iff.mpr ⟨a⟩⟩, x⟩ :
            (j : ActiveBlock Act) × activeRec Act Rec j) ≠ ⟨⟨j, hl⟩, r⟩ := by
        intro heq
        apply hx
        cases heq
        rfl
      rw [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm, mul_zero]
    · simp
  · simp [Channel.postprocess, deterministicFiniteChannel,
      activeRecordProjection, activeBlockActionEquiv,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      blockFamilyChannel, blockFamilyProb, Fintype.sum_sigma, hj, hjl]
    apply Finset.sum_eq_zero
    intro x _
    have hne :
        (⟨⟨j, Fintype.card_pos_iff.mpr ⟨a⟩⟩, x⟩ :
          (j : ActiveBlock Act) × activeRec Act Rec j) ≠ ⟨⟨l, hl⟩, r⟩ := by
      intro heq
      exact hjl (congrArg (fun z => z.1.1) heq)
    rw [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm, mul_zero]

/-- Re-including the active record labels recovers the relabeled original
block channel, because inactive labels have zero probability at every action. -/
theorem postprocess_activeInclusion
    {I : Type u} [Fintype I] [DecidableEq I]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    (P : ∀ i, Channel (Act i) (Rec i)) :
    Channel.postprocess
        (blockFamilyChannel (activeAct Act) (activeRec Act Rec)
          (fun j => P j.1))
        (deterministicFiniteChannel (activeRecordInclusion Act Rec)) =
      Relabeling.relabelChannel (activeBlockActionEquiv Act)
        (Equiv.refl ((i : I) × Rec i))
        (blockFamilyChannel Act Rec P) := by
  classical
  ext ja kr
  rcases ja with ⟨⟨j, hj⟩, a⟩
  rcases kr with ⟨k, r⟩
  by_cases hjk : j = k
  · subst k
    simp [Channel.postprocess, deterministicFiniteChannel,
      activeRecordInclusion, activeBlockActionEquiv,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      blockFamilyChannel, blockFamilyProb, Fintype.sum_sigma, hj]
    rw [Finset.sum_eq_single r]
    · simp
    · intro x _ hx
      have hne :
          (⟨j, x⟩ : (i : I) × Rec i) ≠ ⟨j, r⟩ := by
        intro heq
        apply hx
        cases heq
        rfl
      rw [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm, mul_zero]
    · simp
  · simp [Channel.postprocess, deterministicFiniteChannel,
      activeRecordInclusion, activeBlockActionEquiv,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      blockFamilyChannel, blockFamilyProb, Fintype.sum_sigma, hj, hjk]
    apply Finset.sum_eq_zero
    intro x _
    have hne : (⟨j, x⟩ : (i : I) × Rec i) ≠ ⟨k, r⟩ := by
      intro heq
      exact hjk (congrArg Sigma.fst heq)
    rw [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm, mul_zero]

/-! ## Direct transfers of A1, A2, A4, A5, A6, and A3 duplication -/

theorem inducedPure_a1_weakOrder
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h1 : A1_WeakOrder F) :
    ∀ {A R : Type u}
      [Fintype A] [DecidableEq A]
      [Fintype R] [DecidableEq R]
      (P : Channel A R),
      (inducedPureTraceFamily F o).IsWeakOrder P := by
  intro A R _ _ _ _ P
  constructor
  · intro q p
    letI : Nonempty A := Relabeling.nonempty_of_dist q
    letI : Nonempty R :=
      Relabeling.nonempty_of_dist (P (Classical.choice (inferInstance : Nonempty A)))
    change F.rel (constantPayoffLift o P) q p ∨
      F.rel (constantPayoffLift o P) p q
    exact (h1 (constantPayoffLift o P)).1 q p
  · intro q p r hqp hpr
    letI : Nonempty A := Relabeling.nonempty_of_dist q
    letI : Nonempty R :=
      Relabeling.nonempty_of_dist (P (Classical.choice (inferInstance : Nonempty A)))
    change F.rel (constantPayoffLift o P) q r
    apply (h1 (constantPayoffLift o P)).2 q p r
    · exact hqp
    · exact hpr

theorem inducedPure_a1_localNontriviality
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h1 : A1_WeakOrder F)
    (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    (h8 : A8_PositiveTraceOrientation F) :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nontrivial A]
      (q : TraceableAgency.Dist A), q.FullSupport →
      let P_id : Channel A A := Channel.idChannel
      let P_uninf : Channel A Unit := Channel.uninformativeChannel A
      let blockP := blockChannel P_id P_uninf
      (inducedPureTraceFamily F o).strictRel blockP (inlDist q) (inrDist q) := by
  intro A _ _ _ q hq
  have h := h8 q hq o
  let e := Relabeling.blockUnitPUnitOutcomeEquiv A
  let P0 : Channel (A ⊕ A) (A ⊕ Unit) :=
    blockChannel (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannel A)
  let P1 : Channel (A ⊕ A) (A ⊕ PUnit.{u + 1}) :=
    blockChannel (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU A)
  have hP1 :
      Relabeling.relabelChannel (Equiv.refl (A ⊕ A)) e P0 = P1 := by
    simpa [e, P0, P1] using
      (Relabeling.relabel_block_id_uninformativeChannel_eq (A := A))
  have hP0 :
      Channel.postprocess P1 (Relabeling.outcomeEquivKernel e.symm) = P0 := by
    rw [← hP1]
    exact Relabeling.postprocess_outcomeEquiv_symm_eq_original e P0
  have hforward :
      recordPostprocess (constantPayoffLift o P0)
          (liftRecordProcessor (Relabeling.outcomeEquivKernel e)) =
        constantPayoffLift o P1 := by
    rw [← constantPayoffLift_postprocess]
    rw [Relabeling.postprocess_outcomeEquiv_eq_relabel, hP1]
  have hback :
      recordPostprocess (constantPayoffLift o P1)
          (liftRecordProcessor (Relabeling.outcomeEquivKernel e.symm)) =
        constantPayoffLift o P0 := by
    rw [← constantPayoffLift_postprocess, hP0]
  have hm :
      F.strictRel (constantPayoffLift o P1) (inlDist q) (inrDist q) := by
    unfold FixedPayoffPrefFamily.strictRel
    unfold pairStrict at h
    simpa [P1, constantPayoffLift_blockChannel,
      constantPayoffLift_idChannel, constantPayoffLift_uninformative,
      leftBlockDist, rightBlockDist] using h
  have hqr := fixed_rel_iff_of_mutualRecordProcessing F h1 h3 h4
    (constantPayoffLift o P0) (constantPayoffLift o P1)
    (liftRecordProcessor (Relabeling.outcomeEquivKernel e))
    (liftRecordProcessor (Relabeling.outcomeEquivKernel e.symm))
    hforward hback (inlDist q) (inrDist q)
  have hrq := fixed_rel_iff_of_mutualRecordProcessing F h1 h3 h4
    (constantPayoffLift o P0) (constantPayoffLift o P1)
    (liftRecordProcessor (Relabeling.outcomeEquivKernel e))
    (liftRecordProcessor (Relabeling.outcomeEquivKernel e.symm))
    hforward hback (inrDist q) (inlDist q)
  unfold PrefFamily.strictRel
  change F.rel (constantPayoffLift o P0) (inlDist q) (inrDist q) ∧
    ¬ F.rel (constantPayoffLift o P0) (inrDist q) (inlDist q)
  exact ⟨hqr.mpr hm.1, fun hrev => hm.2 (hrq.mp hrev)⟩

theorem inducedPure_a2
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h2 : A2_Continuity F) :
    TraceableAgency.A2_Continuity (inducedPureTraceFamily F o) := by
  intro A R _ _ _ _ Pseq P qseq pseq q p hP hq hp hrel
  letI : Nonempty A := Relabeling.nonempty_of_dist q
  letI : Nonempty R :=
    Relabeling.nonempty_of_dist (P (Classical.choice (inferInstance : Nonempty A)))
  apply h2 (fun n => constantPayoffLift o (Pseq n))
    (constantPayoffLift o P) qseq pseq q p
  · exact constantPayoffLift_converges o Pseq P hP
  · exact hq
  · exact hp
  · intro n
    exact hrel n

theorem inducedPure_a3_duplication
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h3 : A3_BlockComparisonCoherence F) :
    ∀ {A R : Type u}
      [Fintype A] [DecidableEq A]
      [Fintype R] [DecidableEq R]
      (P : Channel A R) (q p : TraceableAgency.Dist A),
      (inducedPureTraceFamily F o).rel P q p ↔
        (inducedPureTraceFamily F o).rel (blockChannel P P)
          (inlDist q) (inrDist p) := by
  intro A R _ _ _ _ P q p
  letI : Nonempty A := Relabeling.nonempty_of_dist q
  letI : Nonempty R :=
    Relabeling.nonempty_of_dist (P (Classical.choice (inferInstance : Nonempty A)))
  simpa [inducedPureTraceFamily, pairWeak, leftBlockDist, rightBlockDist,
    constantPayoffLift_blockChannel] using h3.duplication (constantPayoffLift o P) q p

/-- The finite-block transfer on its paper-relevant nonempty core.  The older
pure theorem quantifies over additional unused empty blocks; deleting those
blocks is handled separately below. -/
theorem inducedPure_a3_finiteBlock_nonempty
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h3 : A3_BlockComparisonCoherence F) :
    ∀ {I : Type u} [Fintype I] [DecidableEq I]
      (Act Rec : I → Type u)
      [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
      [∀ i, Nonempty (Act i)]
      [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
      (P : ∀ i, Channel (Act i) (Rec i))
      (i j : I) (hij : i ≠ j)
      (qi : TraceableAgency.Dist (Act i))
      (qj : TraceableAgency.Dist (Act j)),
      (inducedPureTraceFamily F o).rel (blockFamilyChannel Act Rec P)
          (blockEmbedDist Act i qi) (blockEmbedDist Act j qj) ↔
        (inducedPureTraceFamily F o).rel (blockChannel (P i) (P j))
          (inlDist qi) (inrDist qj) := by
  intro I _ _ Act Rec _ _ _ _ _ P i j hij qi qj
  letI : Nonempty I := ⟨i⟩
  letI : ∀ k, Nonempty (Rec k) := fun k =>
    Relabeling.nonempty_of_dist
      (P k (Classical.choice (inferInstance : Nonempty (Act k))))
  simpa [inducedPureTraceFamily, pairWeak, leftBlockDist, rightBlockDist,
    commonPayoffBlockEmbed, constantPayoffLift_blockChannel,
    constantPayoffLift_blockFamilyChannel] using
    h3.irrelevant_blocks Act Rec (fun k => constantPayoffLift o (P k))
      i j hij qi qj

/-- Full finite-block transfer, including the old pure interface's vacuous
unused blocks with empty action fibres.  Such blocks are deleted; their record
labels are unreachable and are removed/reinserted by mutually simulating
deterministic record processors. -/
theorem inducedPure_a3_finiteBlock
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h1 : A1_WeakOrder F)
    (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    (h5 : A5_ActionDataProcessing F) :
    ∀ {I : Type u} [Fintype I] [DecidableEq I]
      (Act Rec : I → Type u)
      [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
      [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
      (P : ∀ i, Channel (Act i) (Rec i))
      (i j : I) (hij : i ≠ j)
      (qi : TraceableAgency.Dist (Act i))
      (qj : TraceableAgency.Dist (Act j)),
      (inducedPureTraceFamily F o).rel (blockFamilyChannel Act Rec P)
          (blockEmbedDist Act i qi) (blockEmbedDist Act j qj) ↔
        (inducedPureTraceFamily F o).rel (blockChannel (P i) (P j))
          (inlDist qi) (inrDist qj) := by
  intro I _ _ Act Rec _ _ _ _ P i j hij qi qj
  classical
  letI : Nonempty (Act i) := Relabeling.nonempty_of_dist qi
  letI : Nonempty (Act j) := Relabeling.nonempty_of_dist qj
  letI : Nonempty (Rec i) :=
    Relabeling.nonempty_of_dist
      (P i (Classical.choice (inferInstance : Nonempty (Act i))))
  let ji : ActiveBlock Act :=
    ⟨i, Fintype.card_pos_iff.mpr (Relabeling.nonempty_of_dist qi)⟩
  let jj : ActiveBlock Act :=
    ⟨j, Fintype.card_pos_iff.mpr (Relabeling.nonempty_of_dist qj)⟩
  have hjij : ji ≠ jj := by
    intro heq
    exact hij (congrArg Subtype.val heq)
  letI : Nonempty (ActiveBlock Act) := ⟨ji⟩
  letI : ∀ k : ActiveBlock Act, Nonempty (activeAct Act k) := fun k =>
    Fintype.card_pos_iff.mp k.2
  letI : ∀ k : ActiveBlock Act, Nonempty (activeRec Act Rec k) := fun k =>
    Relabeling.nonempty_of_dist
      (P k.1 (Classical.choice (inferInstance : Nonempty (activeAct Act k))))
  letI : Nonempty ((k : I) × Act k) :=
    ⟨i, Classical.choice (Relabeling.nonempty_of_dist qi)⟩
  letI : Nonempty ((k : I) × Rec k) :=
    ⟨i, Classical.choice (inferInstance : Nonempty (Rec i))⟩
  let eA := activeBlockActionEquiv Act
  let Pfull := blockFamilyChannel Act Rec P
  let Pact := Relabeling.relabelChannel eA
    (Equiv.refl ((k : I) × Rec k)) Pfull
  let Pred := blockFamilyChannel (activeAct Act) (activeRec Act Rec)
    (fun k : ActiveBlock Act => P k.1)
  let fallback : (k : ActiveBlock Act) × activeRec Act Rec k :=
    ⟨ji, Classical.choice (inferInstance : Nonempty (activeRec Act Rec ji))⟩
  let Tproj := deterministicFiniteChannel
    (activeRecordProjection Act Rec fallback)
  let Tincl := deterministicFiniteChannel (activeRecordInclusion Act Rec)
  have hpureForward : Channel.postprocess Pact Tproj = Pred := by
    simpa [eA, Pfull, Pact, Pred, fallback, Tproj] using
      (postprocess_activeProjection Act Rec P fallback)
  have hpureBack : Channel.postprocess Pred Tincl = Pact := by
    simpa [eA, Pfull, Pact, Pred, Tincl] using
      (postprocess_activeInclusion Act Rec P)
  have hforward :
      recordPostprocess (constantPayoffLift o Pact)
          (liftRecordProcessor Tproj) = constantPayoffLift o Pred := by
    rw [← constantPayoffLift_postprocess, hpureForward]
  have hback :
      recordPostprocess (constantPayoffLift o Pred)
          (liftRecordProcessor Tincl) = constantPayoffLift o Pact := by
    rw [← constantPayoffLift_postprocess, hpureBack]
  have haction :
      F.rel (constantPayoffLift o Pfull)
          (blockEmbedDist Act i qi) (blockEmbedDist Act j qj) ↔
        F.rel (constantPayoffLift o Pact)
          (blockEmbedDist (activeAct Act) ji qi)
          (blockEmbedDist (activeAct Act) jj qj) := by
    have hh := fixed_rel_iff_actionEquiv F h1 h3 h5 eA
      (constantPayoffLift o Pfull)
      (blockEmbedDist Act i qi) (blockEmbedDist Act j qj)
    rw [constantPayoffLift_actionRelabel] at hh
    have hqi : Relabeling.relabelDist eA (blockEmbedDist Act i qi) =
        blockEmbedDist (activeAct Act) ji qi := by
      simpa [ji, eA] using relabel_blockEmbed_active Act i qi
    have hqj : Relabeling.relabelDist eA (blockEmbedDist Act j qj) =
        blockEmbedDist (activeAct Act) jj qj := by
      simpa [jj, eA] using relabel_blockEmbed_active Act j qj
    rw [hqi, hqj] at hh
    simpa [ji, jj, eA, Pact] using hh
  have hrecord :
      F.rel (constantPayoffLift o Pact)
          (blockEmbedDist (activeAct Act) ji qi)
          (blockEmbedDist (activeAct Act) jj qj) ↔
        F.rel (constantPayoffLift o Pred)
          (blockEmbedDist (activeAct Act) ji qi)
          (blockEmbedDist (activeAct Act) jj qj) :=
    fixed_rel_iff_of_mutualRecordProcessing F h1 h3 h4
      (constantPayoffLift o Pact) (constantPayoffLift o Pred)
      (liftRecordProcessor Tproj) (liftRecordProcessor Tincl)
      hforward hback _ _
  have hcore := inducedPure_a3_finiteBlock_nonempty F o h3
    (activeAct Act) (activeRec Act Rec) (fun k : ActiveBlock Act => P k.1)
    ji jj hjij qi qj
  change F.rel (constantPayoffLift o Pred)
      (blockEmbedDist (activeAct Act) ji qi)
      (blockEmbedDist (activeAct Act) jj qj) ↔
    F.rel (constantPayoffLift o (blockChannel (P i) (P j)))
      (inlDist qi) (inrDist qj) at hcore
  change F.rel (constantPayoffLift o Pfull)
      (blockEmbedDist Act i qi) (blockEmbedDist Act j qj) ↔
    F.rel (constantPayoffLift o (blockChannel (P i) (P j)))
      (inlDist qi) (inrDist qj)
  exact haction.trans (hrecord.trans hcore)

theorem inducedPure_a4
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h4 : A4_RecordDataProcessing F) :
    TraceableAgency.A4_OutcomePostprocessingAversion
      (inducedPureTraceFamily F o) := by
  intro A R S _ _ _ _ _ _ P T q
  letI : Nonempty A := Relabeling.nonempty_of_dist q
  letI : Nonempty R :=
    Relabeling.nonempty_of_dist (P (Classical.choice (inferInstance : Nonempty A)))
  letI : Nonempty S :=
    Relabeling.nonempty_of_dist (T (Classical.choice (inferInstance : Nonempty R)))
  simpa [inducedPureTraceFamily, pairWeak, leftBlockDist, rightBlockDist,
    constantPayoffLift_blockChannel, constantPayoffLift_postprocess] using
    h4 (constantPayoffLift o P) (liftRecordProcessor T) q

theorem inducedPure_a5
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h5 : A5_ActionDataProcessing F) :
    TraceableAgency.A5_ActionCoarseningAversion
      (inducedPureTraceFamily F o) := by
  intro A B R _ _ _ _ _ _ _ P q S Phat hcompl
  letI : Nonempty A := Relabeling.nonempty_of_dist q
  letI : Nonempty B :=
    Relabeling.nonempty_of_dist
      (S (Classical.choice (inferInstance : Nonempty A)))
  letI : Nonempty R :=
    Relabeling.nonempty_of_dist (P (Classical.choice (inferInstance : Nonempty A)))
  simpa [inducedPureTraceFamily, pairWeak, leftBlockDist, rightBlockDist,
    constantPayoffLift_blockChannel] using
    h5 (constantPayoffLift o P) q S (constantPayoffLift o Phat)
      (constantPayoffLift_actionCompletion o P q S Phat hcompl)

theorem inducedPure_a6
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h6 : A6_BranchwiseContinuationConsistency F) :
    TraceableAgency.A6_BranchwiseContinuationMonotonicity
      (inducedPureTraceFamily F o) := by
  constructor
  · intro A Y _ _ _ _ _ Rec _ _ q P K L hbranch
    letI : Nonempty Y :=
      Relabeling.nonempty_of_dist
        (P (Classical.choice (inferInstance : Nonempty A)))
    letI : ∀ y, Nonempty (Rec y) := fun y =>
      Relabeling.nonempty_of_dist
        (K y (Classical.choice (inferInstance : Nonempty A)))
    have h := h6.1 Rec P
      (fun y => constantPayoffLift o (K y))
      (fun y => constantPayoffLift o (L y)) q
    have hw : pairWeak F q
        (commonPayoffCompound Rec P (fun y => constantPayoffLift o (K y)))
        q (commonPayoffCompound Rec P (fun y => constantPayoffLift o (L y))) :=
      h (by
        intro y hy
        simpa [inducedPureTraceFamily, pairWeak, leftBlockDist, rightBlockDist,
          constantPayoffLift_blockChannel] using hbranch y hy)
    simpa [inducedPureTraceFamily, pairWeak, leftBlockDist, rightBlockDist,
      constantPayoffLift_blockChannel, constantPayoffLift_seqComposeDep] using hw
  · intro A Y _ _ _ _ _ Rec _ _ q P K L hbranch hstrict
    letI : Nonempty Y :=
      Relabeling.nonempty_of_dist
        (P (Classical.choice (inferInstance : Nonempty A)))
    letI : ∀ y, Nonempty (Rec y) := fun y =>
      Relabeling.nonempty_of_dist
        (K y (Classical.choice (inferInstance : Nonempty A)))
    have h := h6.2 Rec P
      (fun y => constantPayoffLift o (K y))
      (fun y => constantPayoffLift o (L y)) q
    have hs : pairStrict F q
        (commonPayoffCompound Rec P (fun y => constantPayoffLift o (K y)))
        q (commonPayoffCompound Rec P (fun y => constantPayoffLift o (L y))) :=
      h (by
        intro y hy
        simpa [inducedPureTraceFamily, pairWeak, leftBlockDist, rightBlockDist,
          constantPayoffLift_blockChannel] using hbranch y hy) (by
        rcases hstrict with ⟨y, hy, hs⟩
        refine ⟨y, hy, ?_⟩
        simpa [PrefFamily.strictRel, FixedPayoffPrefFamily.strictRel,
          inducedPureTraceFamily, pairStrict, leftBlockDist, rightBlockDist,
          constantPayoffLift_blockChannel] using hs)
    simpa [PrefFamily.strictRel, FixedPayoffPrefFamily.strictRel,
      inducedPureTraceFamily, pairStrict, leftBlockDist, rightBlockDist,
      constantPayoffLift_blockChannel, constantPayoffLift_seqComposeDep] using hs

/-! ## Closed pure-trace proposition -/

/-- A1--A6 and A8 induce the exact pure axiom bundle consumed by the already
formalized pure-trace proposition in Appendix A. -/
theorem inducedPure_traceAxioms_of_components
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h1 : A1_WeakOrder F)
    (h2 : A2_Continuity F)
    (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    (h5 : A5_ActionDataProcessing F)
    (h6 : A6_BranchwiseContinuationConsistency F)
    (h8 : A8_PositiveTraceOrientation F) :
    TraceAxioms (inducedPureTraceFamily F o) where
  a1 := ⟨inducedPure_a1_weakOrder F o h1,
    inducedPure_a1_localNontriviality F o h1 h3 h4 h8⟩
  a2 := inducedPure_a2 F o h2
  a3 := ⟨inducedPure_a3_duplication F o h3,
    inducedPure_a3_finiteBlock F o h1 h3 h4 h5⟩
  a4 := inducedPure_a4 F o h4
  a5 := inducedPure_a5 F o h5
  a6 := inducedPure_a6 F o h6

/-- Compatibility wrapper for callers that already carry the full main-text
axiom bundle.  Material relevance A7 is not used by the pure-trace result. -/
theorem inducedPure_traceAxioms
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h : TraceTemperedAxioms F) :
    TraceAxioms (inducedPureTraceFamily F o) :=
  inducedPure_traceAxioms_of_components F o
    h.a1 h.a2 h.a3 h.a4 h.a5 h.a6 h.a8

/-- Kernel-checked invocation of the pure-trace proposition at a constant payoff. -/
theorem inducedPure_MIRep_of_components
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h1 : A1_WeakOrder F)
    (h2 : A2_Continuity F)
    (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    (h5 : A5_ActionDataProcessing F)
    (h6 : A6_BranchwiseContinuationConsistency F)
    (h8 : A8_PositiveTraceOrientation F) :
    MIRep (inducedPureTraceFamily F o) :=
  (provedMainCharacterizationWithMoreover (inducedPureTraceFamily F o)).1.1
    (inducedPure_traceAxioms_of_components F o h1 h2 h3 h4 h5 h6 h8)

/-- Compatibility wrapper for the complete main-text axiom bundle. -/
theorem inducedPure_MIRep
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h : TraceTemperedAxioms F) :
    MIRep (inducedPureTraceFamily F o) :=
  inducedPure_MIRep_of_components F o
    h.a1 h.a2 h.a3 h.a4 h.a5 h.a6 h.a8

/-- Same-scale general-block conclusion supplied by the same closed theorem. -/
theorem inducedPure_blockSameScale_of_components
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h1 : A1_WeakOrder F)
    (h2 : A2_Continuity F)
    (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    (h5 : A5_ActionDataProcessing F)
    (h6 : A6_BranchwiseContinuationConsistency F)
    (h8 : A8_PositiveTraceOrientation F) :
    BlockSameScaleRep (inducedPureTraceFamily F o) :=
  (provedMainCharacterizationWithMoreover (inducedPureTraceFamily F o)).2
    (inducedPure_traceAxioms_of_components F o h1 h2 h3 h4 h5 h6 h8)

/-- Compatibility wrapper for the complete main-text axiom bundle. -/
theorem inducedPure_blockSameScale
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (o : O)
    (h : TraceTemperedAxioms F) :
    BlockSameScaleRep (inducedPureTraceFamily F o) :=
  inducedPure_blockSameScale_of_components F o
    h.a1 h.a2 h.a3 h.a4 h.a5 h.a6 h.a8

/-- Constant-payoff within-channel comparisons are exactly ranked by mutual
information. -/
theorem constantPayoff_rel_iff_mutualInfo
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (o : O) (P : Channel A R)
    (q p : TraceableAgency.Dist A) :
    F.rel (constantPayoffLift o P) q p ↔
      mutualInfo q P ≥ mutualInfo p P := by
  simpa [inducedPureTraceFamily] using
    (inducedPure_MIRep F o h P q p)

/-- The same pure-trace scale ranks every constant-payoff, block-supported
cross-channel comparison. -/
theorem constantPayoff_blockSameScale
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (o : O)
    {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Nonempty (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    [∀ i, Nonempty (Rec i)]
    (P : ∀ i, Channel (Act i) (Rec i))
    (i j : I) (hij : i ≠ j)
    (qi : TraceableAgency.Dist (Act i))
    (qj : TraceableAgency.Dist (Act j)) :
    F.rel (commonPayoffBlockFamilyChannel Act Rec
          (fun k => constantPayoffLift o (P k)))
        (commonPayoffBlockEmbed Act i qi)
        (commonPayoffBlockEmbed Act j qj) ↔
      mutualInfo qi (P i) ≥ mutualInfo qj (P j) := by
  have hh := inducedPure_blockSameScale F o h
    Act Rec P i j hij qi qj
  simpa [inducedPureTraceFamily, commonPayoffBlockEmbed,
    constantPayoffLift_blockFamilyChannel] using hh

end TraceTemperedChoiceVerification
