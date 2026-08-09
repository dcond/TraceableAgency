/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.Statements

/-!
# Benchmark direction for trace-tempered choice

This file proves the necessity/benchmark half of Theorem 1: every preference
family represented by expected payoff utility plus a positive multiple of
mutual information satisfies A1--A8.  It also proves that the same witnesses
represent block-supported cross-channel comparisons.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open Filter Topology
open TraceableAgency

universe u

/-! ## Finite-expectation and relabeling identities -/

/-- Expected utility with an arbitrary payoff-reading map on the visible
alphabet.  This auxiliary lets us pass through the tagged alphabets used by
the already formalized block and sequential channel constructors. -/
noncomputable def expectedUtilityAlong
    {O A X : Type u} [Fintype A] [Fintype X]
    (u : O → ℝ) (payoff : X → O) (q : TraceableAgency.Dist A) (K : Channel A X) : ℝ :=
  ∑ a, q a * ∑ x, K a x * u (payoff x)

theorem expectedUtilityAlong_eq_marginal
    {O A X : Type u} [Fintype A] [Fintype X]
    (u : O → ℝ) (payoff : X → O) (q : TraceableAgency.Dist A) (K : Channel A X) :
    expectedUtilityAlong u payoff q K =
      ∑ x, (Channel.outcomeMarginal K q) x * u (payoff x) := by
  classical
  unfold expectedUtilityAlong
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Channel.outcomeMarginal_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem expectedPayoffUtility_eq_marginal
    {O A R : Type u} [Fintype O] [Fintype A] [Fintype R]
    (u : O → ℝ) (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    expectedPayoffUtility u q K =
      ∑ z, (Channel.outcomeMarginal K q) z * u z.1 := by
  exact expectedUtilityAlong_eq_marginal u Prod.fst q K

theorem outcomeMarginal_relabelOutcome
    {A X Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (q : TraceableAgency.Dist A) (K : Channel A X) :
    Channel.outcomeMarginal
        (Relabeling.relabelChannel (Equiv.refl A) e K) q =
      Relabeling.relabelDist e (Channel.outcomeMarginal K q) := by
  ext y
  simpa using
    (TraceableAgency.outcomeMarginal_relabelChannel
      (Equiv.refl A) e q K y)

theorem mutualInfo_relabelOutcome
    {A X Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (e : X ≃ Y) (q : TraceableAgency.Dist A) (K : Channel A X) :
    mutualInfo q (Relabeling.relabelChannel (Equiv.refl A) e K) =
      mutualInfo q K := by
  classical
  unfold mutualInfo
  rw [outcomeMarginal_relabelOutcome e q K]
  rw [GenericFaddeev.entropy_relabel]
  apply congrArg (fun t : ℝ => H(Channel.outcomeMarginal K q) - t)
  apply Finset.sum_congr rfl
  intro a _
  change q a * H(Relabeling.relabelDist e (K a)) = q a * H(K a)
  rw [GenericFaddeev.entropy_relabel]

theorem expectedUtilityAlong_relabelOutcome
    {O A X Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (u : O → ℝ) (payoff : Y → O)
    (e : X ≃ Y) (q : TraceableAgency.Dist A) (K : Channel A X) :
    expectedUtilityAlong u payoff q
        (Relabeling.relabelChannel (Equiv.refl A) e K) =
      expectedUtilityAlong u (fun x => payoff (e x)) q K := by
  classical
  rw [expectedUtilityAlong_eq_marginal,
    expectedUtilityAlong_eq_marginal,
    outcomeMarginal_relabelOutcome e q K]
  unfold Relabeling.relabelDist
  simpa using e.symm.sum_comp
    (fun x : X => (Channel.outcomeMarginal K q) x * u (payoff (e x)))

/-! ## Block-supported values -/

def sumVisiblePayoff {O R S : Type u} : ((O × R) ⊕ (O × S)) → O
  | Sum.inl z => z.1
  | Sum.inr z => z.1

def sigmaVisiblePayoff {I O : Type u} {Rec : I → Type u} :
    ((i : I) × (O × Rec i)) → O :=
  fun z => z.2.1

theorem expectedUtilityAlong_block_left
    {O A B R S : Type u}
    [Fintype O] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype R] [Fintype S]
    (u : O → ℝ) (q : TraceableAgency.Dist A)
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    expectedUtilityAlong u sumVisiblePayoff (inlDist q)
        (blockChannel K L) = expectedPayoffUtility u q K := by
  classical
  rw [expectedUtilityAlong_eq_marginal,
    expectedPayoffUtility_eq_marginal]
  rw [Fintype.sum_sum_type]
  simp [sumVisiblePayoff]

theorem expectedUtilityAlong_block_right
    {O A B R S : Type u}
    [Fintype O] [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype R] [Fintype S]
    (u : O → ℝ) (p : TraceableAgency.Dist B)
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    expectedUtilityAlong u sumVisiblePayoff (inrDist p)
        (blockChannel K L) = expectedPayoffUtility u p L := by
  classical
  rw [expectedUtilityAlong_eq_marginal,
    expectedPayoffUtility_eq_marginal]
  rw [Fintype.sum_sum_type]
  simp [sumVisiblePayoff]

theorem expectedPayoffUtility_commonBlock_left
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (u : O → ℝ) (q : TraceableAgency.Dist A)
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    expectedPayoffUtility u (leftBlockDist q)
        (commonPayoffBlockChannel K L) = expectedPayoffUtility u q K := by
  rw [show expectedPayoffUtility u (leftBlockDist q)
      (commonPayoffBlockChannel K L) =
      expectedUtilityAlong u
        (fun z : O × (R ⊕ S) => z.1) (inlDist q)
        (Relabeling.relabelChannel (Equiv.refl (A ⊕ B))
          (sumPayoffRecordEquiv O R S) (blockChannel K L)) by rfl]
  rw [expectedUtilityAlong_relabelOutcome]
  have hpay :
      (fun x : (O × R) ⊕ (O × S) ↦
        ((sumPayoffRecordEquiv O R S) x).1) = sumVisiblePayoff := by
    funext x
    cases x <;> rfl
  rw [hpay]
  exact expectedUtilityAlong_block_left u q K L

theorem expectedPayoffUtility_commonBlock_right
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (u : O → ℝ) (p : TraceableAgency.Dist B)
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    expectedPayoffUtility u (rightBlockDist p)
        (commonPayoffBlockChannel K L) = expectedPayoffUtility u p L := by
  rw [show expectedPayoffUtility u (rightBlockDist p)
      (commonPayoffBlockChannel K L) =
      expectedUtilityAlong u
        (fun z : O × (R ⊕ S) => z.1) (inrDist p)
        (Relabeling.relabelChannel (Equiv.refl (A ⊕ B))
          (sumPayoffRecordEquiv O R S) (blockChannel K L)) by rfl]
  rw [expectedUtilityAlong_relabelOutcome]
  have hpay :
      (fun x : (O × R) ⊕ (O × S) ↦
        ((sumPayoffRecordEquiv O R S) x).1) = sumVisiblePayoff := by
    funext x
    cases x <;> rfl
  rw [hpay]
  exact expectedUtilityAlong_block_right u p K L

theorem mutualInfo_commonBlock_left
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) (L : Channel B (O × S)) :
    mutualInfo (leftBlockDist q) (commonPayoffBlockChannel K L) =
      mutualInfo q K := by
  rw [commonPayoffBlockChannel,
    mutualInfo_relabelOutcome, leftBlockDist, mutualInfo_block_inl]

theorem mutualInfo_commonBlock_right
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (p : TraceableAgency.Dist B) (K : Channel A (O × R)) (L : Channel B (O × S)) :
    mutualInfo (rightBlockDist p) (commonPayoffBlockChannel K L) =
      mutualInfo p L := by
  rw [commonPayoffBlockChannel,
    mutualInfo_relabelOutcome, rightBlockDist, mutualInfo_block_inr]

theorem traceTemperedValue_commonBlock_left
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (u : O → ℝ) (lambda : ℝ) (q : TraceableAgency.Dist A)
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    traceTemperedValue u lambda (leftBlockDist q)
        (commonPayoffBlockChannel K L) = traceTemperedValue u lambda q K := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_commonBlock_left,
    mutualInfo_commonBlock_left]

theorem traceTemperedValue_commonBlock_right
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (u : O → ℝ) (lambda : ℝ) (p : TraceableAgency.Dist B)
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    traceTemperedValue u lambda (rightBlockDist p)
        (commonPayoffBlockChannel K L) = traceTemperedValue u lambda p L := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_commonBlock_right,
    mutualInfo_commonBlock_right]

theorem pairWeak_iff_value_ge
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      traceTemperedValue u lambda q K ≥ traceTemperedValue u lambda p L := by
  unfold pairWeak
  rw [hrep]
  rw [traceTemperedValue_commonBlock_left,
    traceTemperedValue_commonBlock_right]

theorem pairStrict_iff_value_gt
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairStrict F q K p L ↔
      traceTemperedValue u lambda q K > traceTemperedValue u lambda p L := by
  unfold pairStrict
  dsimp
  rw [hrep, hrep]
  rw [traceTemperedValue_commonBlock_left,
    traceTemperedValue_commonBlock_right]
  constructor
  · rintro ⟨_, hnot⟩
    exact lt_of_not_ge hnot
  · intro hlt
    exact ⟨hlt.le, not_le.mpr hlt⟩

/-! ## Arbitrary finite block families and the moreover clause -/

theorem expectedUtilityAlong_blockFamily_embed
    {O I : Type u}
    [Fintype I] [DecidableEq I]
    (Act Out : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Fintype (Out i)] [∀ i, DecidableEq (Out i)]
    (u : O → ℝ) (payoff : ∀ i, Out i → O)
    (K : ∀ i, Channel (Act i) (Out i))
    (i : I) (q : TraceableAgency.Dist (Act i)) :
    expectedUtilityAlong u (fun z ↦ payoff z.1 z.2)
        (blockEmbedDist Act i q) (blockFamilyChannel Act Out K) =
      expectedUtilityAlong u (payoff i) q (K i) := by
  classical
  rw [expectedUtilityAlong_eq_marginal,
    expectedUtilityAlong_eq_marginal, Fintype.sum_sigma]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro x _
    rw [outcomeMarginal_blockFamily_embed_same]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro x _
    rw [outcomeMarginal_blockFamily_embed_ne Act Out K hji]
    simp
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem expectedPayoffUtility_commonBlockFamily_embed
    {O I : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Nonempty (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    [∀ i, Nonempty (Rec i)]
    (u : O → ℝ) (K : ∀ i, Channel (Act i) (O × Rec i))
    (i : I) (q : TraceableAgency.Dist (Act i)) :
    expectedPayoffUtility u (commonPayoffBlockEmbed Act i q)
        (commonPayoffBlockFamilyChannel Act Rec K) =
      expectedPayoffUtility u q (K i) := by
  rw [show expectedPayoffUtility u (commonPayoffBlockEmbed Act i q)
      (commonPayoffBlockFamilyChannel Act Rec K) =
      expectedUtilityAlong u
        (fun z : O × ((i : I) × Rec i) ↦ z.1)
        (blockEmbedDist Act i q)
        (Relabeling.relabelChannel (Equiv.refl ((i : I) × Act i))
          (sigmaPayoffRecordEquiv I O Rec)
          (blockFamilyChannel Act (fun i ↦ O × Rec i) K)) by rfl]
  rw [expectedUtilityAlong_relabelOutcome]
  have hpay :
      (fun z : (i : I) × (O × Rec i) ↦
        ((sigmaPayoffRecordEquiv I O Rec) z).1) = sigmaVisiblePayoff := by
    funext z
    rfl
  rw [hpay]
  exact expectedUtilityAlong_blockFamily_embed
    Act (fun i ↦ O × Rec i) u (fun _ z ↦ z.1) K i q

theorem mutualInfo_commonBlockFamily_embed
    {O I : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Nonempty (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    [∀ i, Nonempty (Rec i)]
    (K : ∀ i, Channel (Act i) (O × Rec i))
    (i : I) (q : TraceableAgency.Dist (Act i)) :
    mutualInfo (commonPayoffBlockEmbed Act i q)
        (commonPayoffBlockFamilyChannel Act Rec K) =
      mutualInfo q (K i) := by
  rw [commonPayoffBlockFamilyChannel, mutualInfo_relabelOutcome,
    commonPayoffBlockEmbed, mutualInfo_blockFamily_embed]

theorem traceTemperedValue_commonBlockFamily_embed
    {O I : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (Act Rec : I → Type u)
    [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)]
    [∀ i, Nonempty (Act i)]
    [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)]
    [∀ i, Nonempty (Rec i)]
    (u : O → ℝ) (lambda : ℝ)
    (K : ∀ i, Channel (Act i) (O × Rec i))
    (i : I) (q : TraceableAgency.Dist (Act i)) :
    traceTemperedValue u lambda (commonPayoffBlockEmbed Act i q)
        (commonPayoffBlockFamilyChannel Act Rec K) =
      traceTemperedValue u lambda q (K i) := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_commonBlockFamily_embed,
    mutualInfo_commonBlockFamily_embed]

theorem sameWitnessBlockRepresentation_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda) :
    SameWitnessBlockRepresentation F u lambda := by
  intro I _ _ _ Act Rec _ _ _ _ _ _ K i j _hij qi qj
  rw [hrep]
  rw [traceTemperedValue_commonBlockFamily_embed,
    traceTemperedValue_commonBlockFamily_embed]

/-! ## Weak order, continuity, and block coherence -/

theorem tendsto_expectedPayoffUtility_of_converges
    {O A R : Type u}
    [Fintype O] [Fintype A] [Fintype R]
    (u : O → ℝ)
    (Kseq : ℕ → Channel A (O × R)) (K : Channel A (O × R))
    (qseq : ℕ → TraceableAgency.Dist A) (q : TraceableAgency.Dist A)
    (hK : ChannelConverges Kseq K) (hq : DistConverges qseq q) :
    Tendsto (fun n ↦ expectedPayoffUtility u (qseq n) (Kseq n)) atTop
      (𝓝 (expectedPayoffUtility u q K)) := by
  unfold expectedPayoffUtility
  apply tendsto_finset_sum
  intro a _
  apply Tendsto.mul (hq a)
  apply tendsto_finset_sum
  intro z _
  exact Tendsto.mul (hK a z) tendsto_const_nhds

theorem tendsto_traceTemperedValue_of_converges
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    [Fintype R] [DecidableEq R]
    (u : O → ℝ) (lambda : ℝ)
    (Kseq : ℕ → Channel A (O × R)) (K : Channel A (O × R))
    (qseq : ℕ → TraceableAgency.Dist A) (q : TraceableAgency.Dist A)
    (hK : ChannelConverges Kseq K) (hq : DistConverges qseq q) :
    Tendsto (fun n ↦ traceTemperedValue u lambda (qseq n) (Kseq n)) atTop
      (𝓝 (traceTemperedValue u lambda q K)) := by
  unfold traceTemperedValue
  apply Tendsto.add
  · exact tendsto_expectedPayoffUtility_of_converges u Kseq K qseq q hK hq
  · exact Tendsto.const_mul lambda
      (tendsto_mutualInfo_of_converges' Kseq K qseq q hK hq)

theorem a1_weakOrder_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda) :
    A1_WeakOrder F := by
  intro A R _ _ _ _ _ _ K
  constructor
  · intro q p
    rw [hrep, hrep]
    exact le_total _ _
  · intro q p s hqp hps
    rw [hrep] at hqp hps ⊢
    exact hps.trans hqp

theorem a2_continuity_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda) :
    A2_Continuity F := by
  intro A R _ _ _ _ _ _ Kseq K qseq pseq q p hK hq hp hrel
  rw [hrep]
  have hleft :=
    tendsto_traceTemperedValue_of_converges u lambda Kseq K qseq q hK hq
  have hright :=
    tendsto_traceTemperedValue_of_converges u lambda Kseq K pseq p hK hp
  apply le_of_tendsto_of_tendsto hright hleft
  apply Filter.Eventually.of_forall
  intro n
  exact (hrep (Kseq n) (qseq n) (pseq n)).mp (hrel n)

theorem a3_blockCoherence_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda) :
    A3_BlockComparisonCoherence F := by
  constructor
  · intro A R _ _ _ _ _ _ K q p
    rw [hrep, pairWeak_iff_value_ge hrep]
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j _hij qi qj
    rw [hrep, pairWeak_iff_value_ge hrep]
    rw [traceTemperedValue_commonBlockFamily_embed,
      traceTemperedValue_commonBlockFamily_embed]

/-! ## Payoff-preserving and action-report data processing -/

theorem expectedUtilityAlong_postprocess
    {O A X Y : Type u}
    [Fintype A] [Fintype X] [Fintype Y]
    (u : O → ℝ) (payoff : Y → O)
    (q : TraceableAgency.Dist A) (K : Channel A X) (T : Channel X Y) :
    expectedUtilityAlong u payoff q (Channel.postprocess K T) =
      ∑ a, q a * ∑ x, K a x * (∑ y, T x y * u (payoff y)) := by
  classical
  unfold expectedUtilityAlong
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp only [Channel.postprocess]
  calc
    (∑ y, (∑ x, K a x * T x y) * u (payoff y)) =
        ∑ y, ∑ x, (K a x * T x y) * u (payoff y) := by
          apply Finset.sum_congr rfl
          intro y _
          rw [Finset.sum_mul]
    _ = ∑ x, ∑ y, (K a x * T x y) * u (payoff y) :=
      Finset.sum_comm
    _ = ∑ x, K a x * ∑ y, T x y * u (payoff y) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

theorem payoffPreservingRecordKernel_expected
    {O R S : Type u}
    [Fintype O] [DecidableEq O] [Fintype R]
    [Fintype S] [DecidableEq S]
    (u : O → ℝ) (T : RecordProcessor O R S) (z : O × R) :
    ∑ z', payoffPreservingRecordKernel T z z' * u z'.1 = u z.1 := by
  classical
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single z.1]
  · simp only [payoffPreservingRecordKernel, ite_true]
    rw [← Finset.sum_mul, (T z).sum_eq_one, one_mul]
  · intro o _ hone
    simp [payoffPreservingRecordKernel, hone]
  · exact absurd (Finset.mem_univ z.1)

theorem expectedPayoffUtility_recordPostprocess
    {O A R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R]
    [Fintype S] [DecidableEq S]
    (u : O → ℝ) (q : TraceableAgency.Dist A)
    (K : Channel A (O × R)) (T : RecordProcessor O R S) :
    expectedPayoffUtility u q (recordPostprocess K T) =
      expectedPayoffUtility u q K := by
  change expectedUtilityAlong u Prod.fst q
      (Channel.postprocess K (payoffPreservingRecordKernel T)) =
    expectedUtilityAlong u Prod.fst q K
  rw [expectedUtilityAlong_postprocess]
  unfold expectedUtilityAlong
  simp_rw [payoffPreservingRecordKernel_expected u T]

theorem a4_recordDataProcessing_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda) :
    A4_RecordDataProcessing F := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [pairWeak_iff_value_ge hrep]
  unfold traceTemperedValue
  rw [expectedPayoffUtility_recordPostprocess]
  have hmi := mutualInfo_outcome_postprocess_le q K
    (payoffPreservingRecordKernel T)
  have hscaled := mul_le_mul_of_nonneg_left hmi hlambda.le
  simpa [add_comm, recordPostprocess] using
    (add_le_add_left hscaled (expectedPayoffUtility u q K))

theorem bayesCompletion_of_actionReportCompletion
    {O A B R : Type u}
    [Fintype O]
    [Fintype A]
    [Fintype B] [DecidableEq B]
    [Fintype R]
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R))
    (hcompletion : IsActionReportCompletion K q S Khat) :
    Channel.IsBayesPushforwardCompletion K q S Khat := by
  intro b hb z
  apply (eq_div_iff (ne_of_gt hb)).2
  simpa [mul_comm] using hcompletion b z

theorem expectedPayoffUtility_actionReport
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
    (u : O → ℝ)
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R))
    (hcompletion : IsActionReportCompletion K q S Khat) :
    expectedPayoffUtility u (Channel.actionPushforward q S) Khat =
      expectedPayoffUtility u q K := by
  rw [expectedPayoffUtility_eq_marginal,
    expectedPayoffUtility_eq_marginal]
  rw [outcomeMarginal_bayesPushforwardCompletion K q S Khat
    (bayesCompletion_of_actionReportCompletion K q S Khat hcompletion)]

theorem a5_actionDataProcessing_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda) :
    A5_ActionDataProcessing F := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Khat hcompletion
  rw [pairWeak_iff_value_ge hrep]
  unfold traceTemperedValue
  rw [expectedPayoffUtility_actionReport u K q S Khat hcompletion]
  have hbayes :=
    bayesCompletion_of_actionReportCompletion K q S Khat hcompletion
  have hmi := mutualInfo_action_bayes_pushforward_le K q S Khat hbayes
  have hscaled := mul_le_mul_of_nonneg_left hmi hlambda.le
  simpa [add_comm] using
    (add_le_add_left hscaled (expectedPayoffUtility u q K))

/-! ## Branchwise compounding -/

theorem expectedUtilityAlong_seqComposeDep
    {O A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    (u : O → ℝ) (payoff : ∀ y, Rec y → O)
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (Rec y)) :
    expectedUtilityAlong u (fun z ↦ payoff z.1 z.2) q
        (seqComposeDep P Rec K) =
      ∑ y, (Channel.outcomeMarginal P q) y *
        expectedUtilityAlong u (payoff y)
          (Channel.posterior P q y) (K y) := by
  classical
  rw [expectedUtilityAlong_eq_marginal, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro y _
  rw [expectedUtilityAlong_eq_marginal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [outcomeMarginal_seqComposeDep_apply]
  ring

theorem expectedPayoffUtility_commonCompound
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (u : O → ℝ) (q : TraceableAgency.Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × Rec y)) :
    expectedPayoffUtility u q (commonPayoffCompound Rec P K) =
      ∑ y, (Channel.outcomeMarginal P q) y *
        expectedPayoffUtility u (branchPosterior P q y) (K y) := by
  rw [show expectedPayoffUtility u q (commonPayoffCompound Rec P K) =
      expectedUtilityAlong u
        (fun z : O × ((y : Y) × Rec y) ↦ z.1) q
        (Relabeling.relabelChannel (Equiv.refl A)
          (compoundPayoffRecordEquiv Y O Rec)
          (seqComposeDep P (fun y ↦ O × Rec y) K)) by rfl]
  rw [expectedUtilityAlong_relabelOutcome]
  change expectedUtilityAlong u
      (fun z : (y : Y) × (O × Rec y) ↦ z.2.1) q
        (seqComposeDep P (fun y ↦ O × Rec y) K) =
    ∑ y, (Channel.outcomeMarginal P q) y *
      expectedUtilityAlong u (fun z : O × Rec y ↦ z.1)
        (Channel.posterior P q y) (K y)
  exact expectedUtilityAlong_seqComposeDep
    (fun y ↦ O × Rec y) u (fun _ z ↦ z.1) q P K

theorem mutualInfo_commonCompound
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × Rec y)) :
    mutualInfo q (commonPayoffCompound Rec P K) =
      mutualInfo q P +
      ∑ y, (Channel.outcomeMarginal P q) y *
        mutualInfo (branchPosterior P q y) (K y) := by
  rw [commonPayoffCompound, mutualInfo_relabelOutcome,
    mutualInfo_seqComposeDep]
  rfl

theorem traceTemperedValue_commonCompound
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (u : O → ℝ) (lambda : ℝ)
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × Rec y)) :
    traceTemperedValue u lambda q (commonPayoffCompound Rec P K) =
      lambda * mutualInfo q P +
      ∑ y, (Channel.outcomeMarginal P q) y *
        traceTemperedValue u lambda (branchPosterior P q y) (K y) := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_commonCompound,
    mutualInfo_commonCompound]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  ring

theorem a6_branchwiseConsistency_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda) :
    A6_BranchwiseContinuationConsistency F := by
  constructor
  · intro A Y _ _ _ _ _ _ Rec _ _ _ P K L q hbranch
    rw [pairWeak_iff_value_ge hrep]
    rw [traceTemperedValue_commonCompound,
      traceTemperedValue_commonCompound]
    have hsum := sum_mul_ge_sum_mul_of_nonneg_of_pos_imp
      (fun y ↦ (Channel.outcomeMarginal P q) y)
      (fun y ↦ traceTemperedValue u lambda
        (branchPosterior P q y) (K y))
      (fun y ↦ traceTemperedValue u lambda
        (branchPosterior P q y) (L y))
      (fun y ↦ (Channel.outcomeMarginal P q).nonneg y)
      (fun y hy ↦ (pairWeak_iff_value_ge hrep _ _ _ _).mp
        (hbranch y hy))
    simpa [add_comm] using
      (add_le_add_left hsum (lambda * mutualInfo q P))
  · intro A Y _ _ _ _ _ _ Rec _ _ _ P K L q hweak hstrict
    rw [pairStrict_iff_value_gt hrep]
    rw [traceTemperedValue_commonCompound,
      traceTemperedValue_commonCompound]
    have hpoint : ∀ y,
        (Channel.outcomeMarginal P q) y > 0 →
        traceTemperedValue u lambda (branchPosterior P q y) (K y) ≥
          traceTemperedValue u lambda (branchPosterior P q y) (L y) := by
      intro y hy
      exact (pairWeak_iff_value_ge hrep _ _ _ _).mp (hweak y hy)
    obtain ⟨y, hy, hystrict⟩ := hstrict
    have hyvalue := (pairStrict_iff_value_gt hrep _ _ _ _).mp hystrict
    have hsum := sum_mul_gt_sum_mul_of_nonneg_of_exists_strict
      (fun y ↦ (Channel.outcomeMarginal P q) y)
      (fun y ↦ traceTemperedValue u lambda
        (branchPosterior P q y) (K y))
      (fun y ↦ traceTemperedValue u lambda
        (branchPosterior P q y) (L y))
      (fun y ↦ (Channel.outcomeMarginal P q).nonneg y)
      hpoint ⟨y, hy, hyvalue⟩
    simpa [add_comm] using
      (add_lt_add_left hsum (lambda * mutualInfo q P))

/-! ## Material relevance and positive trace orientation -/

theorem outcomeMarginal_fullRevealAtPayoff_apply
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (q : TraceableAgency.Dist A) (o o' : O) (a' : A) :
    Channel.outcomeMarginal (fullRevealAtPayoff (A := A) o) q (o', a') =
      if o' = o then q a' else 0 := by
  classical
  by_cases ho : o' = o
  · subst o'
    simp [Channel.outcomeMarginal_apply, fullRevealAtPayoff,
      TraceableAgency.Dist.pure_apply]
  · simp [Channel.outcomeMarginal_apply, fullRevealAtPayoff,
      TraceableAgency.Dist.pure_apply, ho]

theorem entropy_outcomeMarginal_fullRevealAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (q : TraceableAgency.Dist A) (o : O) :
    H(Channel.outcomeMarginal (fullRevealAtPayoff (A := A) o) q) = H(q) := by
  classical
  unfold entropy
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single o]
  · apply Finset.sum_congr rfl
    intro a _
    rw [outcomeMarginal_fullRevealAtPayoff_apply]
    simp
  · intro o' _ hone
    apply Finset.sum_eq_zero
    intro a _
    rw [outcomeMarginal_fullRevealAtPayoff_apply]
    simp [hone, entropyTerm_zero]
  · exact absurd (Finset.mem_univ o)

theorem mutualInfo_fullRevealAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (q : TraceableAgency.Dist A) (o : O) :
    mutualInfo q (fullRevealAtPayoff (A := A) o) = H(q) := by
  unfold mutualInfo
  rw [entropy_outcomeMarginal_fullRevealAtPayoff]
  have hrow : ∀ a : A,
      H(fullRevealAtPayoff (A := A) o a) = 0 := by
    intro a
    exact entropy_pure' (o, a)
  simp_rw [hrow, mul_zero, Finset.sum_const_zero, sub_zero]

theorem outcomeMarginal_uninformativeAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    (q : TraceableAgency.Dist A) (o : O) :
    Channel.outcomeMarginal (uninformativeAtPayoff (A := A) o) q =
      TraceableAgency.Dist.pure (o, PUnit.unit) := by
  classical
  ext z
  rcases z with ⟨o', r⟩
  cases r
  simp [Channel.outcomeMarginal_apply, uninformativeAtPayoff,
    TraceableAgency.Dist.pure_apply, q.sum_eq_one]

theorem mutualInfo_uninformativeAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    (q : TraceableAgency.Dist A) (o : O) :
    mutualInfo q (uninformativeAtPayoff (A := A) o) = 0 := by
  classical
  unfold mutualInfo
  rw [outcomeMarginal_uninformativeAtPayoff, entropy_pure']
  simp [uninformativeAtPayoff, entropy_pure']

theorem expectedPayoffUtility_fullRevealAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (u : O → ℝ) (q : TraceableAgency.Dist A) (o : O) :
    expectedPayoffUtility u q (fullRevealAtPayoff (A := A) o) = u o := by
  rw [expectedPayoffUtility_eq_marginal, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single o]
  · simp_rw [outcomeMarginal_fullRevealAtPayoff_apply]
    simp only [if_pos]
    rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  · intro o' _ hone
    apply Finset.sum_eq_zero
    intro a _
    rw [outcomeMarginal_fullRevealAtPayoff_apply]
    simp [hone]
  · exact absurd (Finset.mem_univ o)

theorem expectedPayoffUtility_uninformativeAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    (u : O → ℝ) (q : TraceableAgency.Dist A) (o : O) :
    expectedPayoffUtility u q (uninformativeAtPayoff (A := A) o) = u o := by
  rw [expectedPayoffUtility_eq_marginal,
    outcomeMarginal_uninformativeAtPayoff]
  simp [TraceableAgency.Dist.pure_apply]

theorem traceTemperedValue_fullRevealAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (u : O → ℝ) (lambda : ℝ)
    (q : TraceableAgency.Dist A) (o : O) :
    traceTemperedValue u lambda q (fullRevealAtPayoff (A := A) o) =
      u o + lambda * H(q) := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_fullRevealAtPayoff,
    mutualInfo_fullRevealAtPayoff]

theorem traceTemperedValue_uninformativeAtPayoff
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    (u : O → ℝ) (lambda : ℝ)
    (q : TraceableAgency.Dist A) (o : O) :
    traceTemperedValue u lambda q (uninformativeAtPayoff (A := A) o) = u o := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_uninformativeAtPayoff,
    mutualInfo_uninformativeAtPayoff]
  ring

theorem traceTemperedValue_deterministicPayoffChannel
    {O : Type u} [Fintype O] [DecidableEq O]
    (u : O → ℝ) (lambda : ℝ) (o : O) :
    traceTemperedValue u lambda
        (TraceableAgency.Dist.pure PUnit.unit)
        (deterministicPayoffChannel o) = u o := by
  exact traceTemperedValue_uninformativeAtPayoff u lambda
    (TraceableAgency.Dist.pure PUnit.unit) o

theorem a7_materialRelevance_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hnonconstant : ¬ IsConstantPayoffIndex u)
    (hrep : WithinChannelRepresentation F u lambda) :
    A7_MaterialRelevance F := by
  classical
  have hpair : ∃ x y : O, u x ≠ u y := by
    by_contra hpairs
    apply hnonconstant
    by_cases hO : Nonempty O
    · let o0 : O := Classical.choice hO
      refine ⟨u o0, ?_⟩
      intro o
      apply not_ne_iff.mp
      intro hne
      exact hpairs ⟨o, o0, hne⟩
    · refine ⟨0, ?_⟩
      intro o
      exact (hO ⟨o⟩).elim
  obtain ⟨x, y, hxy⟩ := hpair
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · refine ⟨y, x, ?_⟩
    rw [pairStrict_iff_value_gt hrep,
      traceTemperedValue_deterministicPayoffChannel,
      traceTemperedValue_deterministicPayoffChannel]
    exact hlt
  · refine ⟨x, y, ?_⟩
    rw [pairStrict_iff_value_gt hrep,
      traceTemperedValue_deterministicPayoffChannel,
      traceTemperedValue_deterministicPayoffChannel]
    exact hgt

theorem a8_positiveTraceOrientation_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda) :
    A8_PositiveTraceOrientation F := by
  intro A _ _ _ q hq o
  rw [pairStrict_iff_value_gt hrep,
    traceTemperedValue_fullRevealAtPayoff,
    traceTemperedValue_uninformativeAtPayoff]
  have hentropy := entropy_pos_of_fullSupport_nontrivial q hq
  nlinarith

/-! ## Complete benchmark package -/

theorem traceTemperedAxioms_of_representation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hnonconstant : ¬ IsConstantPayoffIndex u)
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda) :
    TraceTemperedAxioms F where
  a1 := a1_weakOrder_of_representation hrep
  a2 := a2_continuity_of_representation hrep
  a3 := a3_blockCoherence_of_representation hrep
  a4 := a4_recordDataProcessing_of_representation hlambda hrep
  a5 := a5_actionDataProcessing_of_representation hlambda hrep
  a6 := a6_branchwiseConsistency_of_representation hrep
  a7 := a7_materialRelevance_of_representation hnonconstant hrep
  a8 := a8_positiveTraceOrientation_of_representation hlambda hrep

theorem representation_implies_axioms_and_sameWitnessBlockRepresentation
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hnonconstant : ¬ IsConstantPayoffIndex u)
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda) :
    TraceTemperedAxioms F ∧ SameWitnessBlockRepresentation F u lambda :=
  ⟨traceTemperedAxioms_of_representation hnonconstant hlambda hrep,
    sameWitnessBlockRepresentation_of_representation hrep⟩

end TraceTemperedChoiceVerification
