/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PureTrace

/-!
# Orientation of cross-environment block comparisons

The paper defines the reverse comparison inside the same oriented block
environment.  This file proves, from A6/A7 rather than from an informal
relabeling convention, that it agrees with swapping the two pair arguments.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-- Swap the two tagged record summands while retaining the payoff. -/
def payoffRecordSumComm (O R S : Type u) :
    (O × (R ⊕ S)) ≃ (O × (S ⊕ R)) :=
  Equiv.prodCongr (Equiv.refl O) (Equiv.sumComm R S)

/-- The record processor implementing the sum swap. -/
noncomputable def swapRecordProcessor
    {O R S : Type u} [Fintype (S ⊕ R)] [DecidableEq (S ⊕ R)] :
    RecordProcessor O (R ⊕ S) (S ⊕ R) :=
  fun z => TraceableAgency.Dist.pure (Equiv.sumComm R S z.2)

theorem recordPostprocess_swapRecord
    {O A R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (K : Channel A (O × (R ⊕ S))) :
    recordPostprocess K (swapRecordProcessor (O := O) (R := R) (S := S)) =
      Relabeling.relabelChannel (Equiv.refl A)
        (payoffRecordSumComm O R S) K := by
  classical
  ext a z
  rcases z with ⟨o, sr⟩
  cases sr with
  | inl s =>
      simp [recordPostprocess, payoffPreservingRecordKernel,
        swapRecordProcessor, payoffRecordSumComm,
        Channel.postprocess, Relabeling.relabelChannel,
        Relabeling.relabelDist, Fintype.sum_prod_type,
        TraceableAgency.Dist.pure_apply]
  | inr r =>
      simp [recordPostprocess, payoffPreservingRecordKernel,
        swapRecordProcessor, payoffRecordSumComm,
        Channel.postprocess, Relabeling.relabelChannel,
        Relabeling.relabelDist, Fintype.sum_prod_type,
        TraceableAgency.Dist.pure_apply]

/-- Swapping both tagged actions and tagged records turns `K ⊔ L` into
`L ⊔ K`, with the common payoff coordinate unchanged. -/
theorem commonPayoffBlockChannel_swap
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype R] [DecidableEq R]
    [Fintype S] [DecidableEq S]
    (K : Channel A (O × R)) (L : Channel B (O × S)) :
    Relabeling.relabelChannel (Equiv.sumComm A B)
        (payoffRecordSumComm O R S)
        (commonPayoffBlockChannel K L) =
      commonPayoffBlockChannel L K := by
  classical
  ext x z
  cases x with
  | inl b =>
      rcases z with ⟨o, sr⟩
      cases sr <;>
        simp [commonPayoffBlockChannel, payoffRecordSumComm,
          sumPayoffRecordEquiv, Relabeling.relabelChannel,
          Relabeling.relabelDist, blockChannel]
  | inr a =>
      rcases z with ⟨o, sr⟩
      cases sr <;>
        simp [commonPayoffBlockChannel, payoffRecordSumComm,
          sumPayoffRecordEquiv, Relabeling.relabelChannel,
          Relabeling.relabelDist, blockChannel]

/-- The primitive reverse comparison in one oriented block is the same as the
forward comparison after swapping the two pair arguments. -/
theorem sameBlock_reverse_iff_pairWeak_swap
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F) (h5 : A5_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    F.rel (commonPayoffBlockChannel K L)
        (rightBlockDist p) (leftBlockDist q) ↔
      pairWeak F p L q K := by
  classical
  let C := commonPayoffBlockChannel K L
  let Cact := Relabeling.relabelChannel (Equiv.sumComm A B)
    (Equiv.refl (O × (R ⊕ S))) C
  let Cswap := commonPayoffBlockChannel L K
  let p' := Relabeling.relabelDist (Equiv.sumComm A B) (rightBlockDist p)
  let q' := Relabeling.relabelDist (Equiv.sumComm A B) (leftBlockDist q)
  have haction := fixed_rel_iff_actionEquiv F h1 h3 h5
    (Equiv.sumComm A B) C (rightBlockDist p) (leftBlockDist q)
  have hp : p' = leftBlockDist p := by
    simp [p', rightBlockDist, leftBlockDist]
  have hq : q' = rightBlockDist q := by
    simp [q', rightBlockDist, leftBlockDist]
  have hforward :
      recordPostprocess Cact
          (swapRecordProcessor (O := O) (R := R) (S := S)) = Cswap := by
    rw [recordPostprocess_swapRecord]
    dsimp [Cact, Cswap, C]
    ext x z
    cases x with
    | inl a =>
        rcases z with ⟨o, sr⟩
        cases sr <;>
          simp [commonPayoffBlockChannel, payoffRecordSumComm,
            sumPayoffRecordEquiv, Relabeling.relabelChannel,
            Relabeling.relabelDist, blockChannel]
    | inr b =>
        rcases z with ⟨o, sr⟩
        cases sr <;>
          simp [commonPayoffBlockChannel, payoffRecordSumComm,
            sumPayoffRecordEquiv, Relabeling.relabelChannel,
            Relabeling.relabelDist, blockChannel]
  have hback :
      recordPostprocess Cswap
          (swapRecordProcessor (O := O) (R := S) (S := R)) = Cact := by
    rw [recordPostprocess_swapRecord]
    dsimp [Cact, Cswap, C]
    ext x z
    cases x with
    | inl a =>
        rcases z with ⟨o, rs⟩
        cases rs <;>
          simp [commonPayoffBlockChannel, payoffRecordSumComm,
            sumPayoffRecordEquiv, Relabeling.relabelChannel,
            Relabeling.relabelDist, blockChannel]
    | inr b =>
        rcases z with ⟨o, rs⟩
        cases rs <;>
          simp [commonPayoffBlockChannel, payoffRecordSumComm,
            sumPayoffRecordEquiv, Relabeling.relabelChannel,
            Relabeling.relabelDist, blockChannel]
  have hrecord := fixed_rel_iff_of_mutualRecordProcessing F h1 h3 h4
    Cact Cswap
    (swapRecordProcessor (O := O) (R := R) (S := S))
    (swapRecordProcessor (O := O) (R := S) (S := R))
    hforward hback p' q'
  change F.rel C (rightBlockDist p) (leftBlockDist q) ↔
    F.rel Cact p' q' at haction
  rw [hp, hq] at haction hrecord
  change F.rel C (rightBlockDist p) (leftBlockDist q) ↔
    F.rel Cswap (leftBlockDist p) (rightBlockDist q)
  exact haction.trans hrecord

/-- `pairStrict` is exactly the asymmetric part of the global `pairWeak`
comparison once block-swap neutrality has been derived. -/
theorem pairStrict_iff_pairWeak_not_swap
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F) (h5 : A5_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairStrict F q K p L ↔
      pairWeak F q K p L ∧ ¬ pairWeak F p L q K := by
  unfold pairStrict
  dsimp
  have hswap :=
    sameBlock_reverse_iff_pairWeak_swap F h1 h3 h4 h5 q K p L
  constructor
  · rintro ⟨hforward, hnotReverse⟩
    exact ⟨hforward, fun hpair => hnotReverse (hswap.mpr hpair)⟩
  · rintro ⟨hforward, hnotPair⟩
    exact ⟨hforward, fun hreverse => hnotPair (hswap.mp hreverse)⟩

/-- Cross-environment pair comparison is complete. -/
theorem pairWeak_complete
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ∨ pairWeak F p L q K := by
  let C := commonPayoffBlockChannel K L
  rcases (h.a1 C).1 (leftBlockDist q) (rightBlockDist p) with hqp | hpq
  · exact Or.inl hqp
  · exact Or.inr
      ((sameBlock_reverse_iff_pairWeak_swap F h.a1 h.a3 h.a4 h.a5
        q K p L).1 hpq)

/-- Three labels used to assemble transitivity of cross-environment pairs in
one primitive block environment. -/
inductive PairTripleBlock : Type u
  | left
  | middle
  | right
  deriving DecidableEq, Fintype, Nonempty

open PairTripleBlock

/-- Cross-environment pair comparison is transitive.  The proof puts all
three alternatives in one explicit three-block environment, so no relabelling
or cross-environment convention is used. -/
theorem pairWeak_transitive_of_structural
    {O A B C R S T : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S))
    (s : TraceableAgency.Dist C) (M : Channel C (O × T)) :
    pairWeak F q K p L → pairWeak F p L s M → pairWeak F q K s M := by
  intro hqp hps
  classical
  let Act : PairTripleBlock → Type u
    | left => A
    | middle => B
    | right => C
  let Rec : PairTripleBlock → Type u
    | left => R
    | middle => S
    | right => T
  let actFintype : ∀ k, Fintype (Act k)
    | left => inferInstance
    | middle => inferInstance
    | right => inferInstance
  let actDecEq : ∀ k, DecidableEq (Act k)
    | left => inferInstance
    | middle => inferInstance
    | right => inferInstance
  let actNonempty : ∀ k, Nonempty (Act k)
    | left => inferInstance
    | middle => inferInstance
    | right => inferInstance
  letI : ∀ k, Fintype (Act k) := actFintype
  letI : ∀ k, DecidableEq (Act k) := actDecEq
  letI : ∀ k, Nonempty (Act k) := actNonempty
  let recFintype : ∀ k, Fintype (Rec k)
    | left => inferInstance
    | middle => inferInstance
    | right => inferInstance
  let recDecEq : ∀ k, DecidableEq (Rec k)
    | left => inferInstance
    | middle => inferInstance
    | right => inferInstance
  let recNonempty : ∀ k, Nonempty (Rec k)
    | left => inferInstance
    | middle => inferInstance
    | right => inferInstance
  letI : ∀ k, Fintype (Rec k) := recFintype
  letI : ∀ k, DecidableEq (Rec k) := recDecEq
  letI : ∀ k, Nonempty (Rec k) := recNonempty
  let Ch : ∀ k, Channel (Act k) (O × Rec k)
    | left => K
    | middle => L
    | right => M
  let Big := commonPayoffBlockFamilyChannel Act Rec Ch
  let x := commonPayoffBlockEmbed Act left q
  let y := commonPayoffBlockEmbed Act middle p
  let z := commonPayoffBlockEmbed Act right s
  have hlm : (left : PairTripleBlock.{u}) ≠ middle := by decide
  have hmr : (middle : PairTripleBlock.{u}) ≠ right := by decide
  have hlr : (left : PairTripleBlock.{u}) ≠ right := by decide
  have hxy : F.rel Big x y := by
    have hc := (h3.irrelevant_blocks Act Rec Ch left middle hlm q p).2
      (by simpa [Act, Rec, Ch] using hqp)
    simpa [Big, x, y] using hc
  have hyz : F.rel Big y z := by
    have hc := (h3.irrelevant_blocks Act Rec Ch middle right hmr p s).2
      (by simpa [Act, Rec, Ch] using hps)
    simpa [Big, y, z] using hc
  have hxz : F.rel Big x z := (h1 Big).2 x y z hxy hyz
  have hc := (h3.irrelevant_blocks Act Rec Ch left right hlr q s).1
    (by simpa [Big, x, z] using hxz)
  simpa [Act, Rec, Ch] using hc

/-- Cross-environment transitivity packaged for the representation proof. -/
theorem pairWeak_transitive
    {O A B C R S T : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S))
    (s : TraceableAgency.Dist C) (M : Channel C (O × T)) :
    pairWeak F q K p L → pairWeak F p L s M → pairWeak F q K s M :=
  pairWeak_transitive_of_structural F h.a1 h.a3 q K p L s M

/-- Fixed-action specialization used by each marked-terminal fibre. -/
theorem pairWeak_transitive_sameAction
    {O A R S T : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist A) (L : Channel A (O × S))
    (s : TraceableAgency.Dist A) (M : Channel A (O × T)) :
    pairWeak F q K p L → pairWeak F p L s M → pairWeak F q K s M :=
  pairWeak_transitive F h q K p L s M

/-- Every pair is weakly comparable to itself. -/
theorem pairWeak_refl
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    pairWeak F q K q K := by
  have hself : F.rel K q q := by
    rcases (h.a1 K).1 q q with hq | hq <;> exact hq
  exact (h.a3.duplication K q q).1 hself

end TraceableAgency.Theorem1
