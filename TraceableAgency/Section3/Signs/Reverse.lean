import TraceableAgency.Theorem1.MaterialCalibration.Proof

/-! Literal negative processing orientations and reversal of the primitive family.
The block-swap argument is derived using reversible processors; it is not
assumed as an identification of action or record labels. -/

namespace TraceableAgency.Theorem1.Section3
open TraceableAgency
universe u

def NegativeRecordProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (K : Channel A (O × R)) (T : RecordProcessor O R S) (q : TraceableAgency.Dist A),
    pairWeak F q (recordPostprocess K T) q K

def NegativeActionProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A B R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R)),
    IsActionProcessorCompletion K q S Khat →
    pairWeak F (Channel.actionPushforward q S) Khat q K

theorem negative_rel_iff_actionEquiv
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A5_BlockComparisonCoherence F)
    (h5 : NegativeActionProcessing F)
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
  have qforward : pairWeak F q' K' q K := by
    have hh := h5 K q (Relabeling.actionEquivKernel e) K'
      (actionCompletion_isExact K q (Relabeling.actionEquivKernel e) K'
        (Relabeling.relabelChannel_isBayesPushforwardCompletion e K q))
    simpa [q', K', Relabeling.actionPushforward_equiv] using hh
  have qback : pairWeak F q K q' K' := by
    have hh := h5 K' q' (Relabeling.actionEquivKernel e.symm) K
      (actionCompletion_isExact K' q' (Relabeling.actionEquivKernel e.symm) K
        (by
          simpa [K', q'] using
            (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion e K q)))
    simpa [q', K', Relabeling.actionPushforward_equiv,
      Relabeling.relabelDist_symm] using hh
  have rforward : pairWeak F r' K' r K := by
    have hh := h5 K r (Relabeling.actionEquivKernel e) K'
      (actionCompletion_isExact K r (Relabeling.actionEquivKernel e) K'
        (Relabeling.relabelChannel_isBayesPushforwardCompletion e K r))
    simpa [r', K', Relabeling.actionPushforward_equiv] using hh
  have rback : pairWeak F r K r' K' := by
    have hh := h5 K' r' (Relabeling.actionEquivKernel e.symm) K
      (actionCompletion_isExact K' r' (Relabeling.actionEquivKernel e.symm) K
        (by
          simpa [K', r'] using
            (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion e K r)))
    simpa [r', K', Relabeling.actionPushforward_equiv,
      Relabeling.relabelDist_symm] using hh
  exact fixed_pairwiseReplacement_from_weakEquiv F h1 h3
    K K' q r q' r' qback qforward rback rforward

theorem negative_rel_iff_of_mutualRecordProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A5_BlockComparisonCoherence F)
    (h4 : NegativeRecordProcessing F)
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
  · simpa [hLK] using h4 L U q
  · simpa [hKL] using h4 K T q
  · simpa [hLK] using h4 L U r
  · simpa [hKL] using h4 K T r

theorem negative_sameBlock_reverse_iff_pairWeak_swap
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A5_BlockComparisonCoherence F)
    (h4 : NegativeRecordProcessing F) (h5 : NegativeActionProcessing F)
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
  have haction := negative_rel_iff_actionEquiv F h1 h3 h5
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
  have hrecord := negative_rel_iff_of_mutualRecordProcessing F h1 h3 h4
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


variable {O : Type u} [Fintype O] [DecidableEq O]

/-- Reverse each primitive within-environment weak order. -/
def reverseFamily (F : FixedPayoffPrefFamily O) : FixedPayoffPrefFamily O where
  rel K q p := F.rel K p q

@[simp] theorem reverseFamily_rel (F : FixedPayoffPrefFamily O)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q p : Dist A) :
    (reverseFamily F).rel K q p ↔ F.rel K p q := Iff.rfl

def NegativeTraceRelevance (F : FixedPayoffPrefFamily O) : Prop :=
  ∃ o : O, F.strictRel (traceRelevanceBenchmarkChannel o)
    traceRelevanceUnrevealingPrior traceRelevanceRevealingPrior

structure SignBackground (F : FixedPayoffPrefFamily O) : Prop where
  a1 : A1_WeakOrder F
  a2 : A2_Continuity F
  a3 : A3_MaterialRelevance F
  a5 : A5_BlockComparisonCoherence F
  a8 : A8_RecordwiseSureThing F

theorem reverse_a1 (F : FixedPayoffPrefFamily O) (h : A1_WeakOrder F) :
    A1_WeakOrder (reverseFamily F) := by
  intro A R _ _ _ _ _ _ K
  exact ⟨fun q p => (h K).1 p q,
    fun q p r hqp hpr => (h K).2 r p q hpr hqp⟩

theorem reverse_a2 (F : FixedPayoffPrefFamily O) (h : A2_Continuity F) :
    A2_Continuity (reverseFamily F) := by
  intro A R _ _ _ _ _ _ Ks K qs ps q p hK hq hp hh
  exact h Ks K ps qs p q hK hp hq hh

theorem reverse_pairWeak_iff (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : NegativeRecordProcessing F) (h7 : NegativeActionProcessing F)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R))
    (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (reverseFamily F) q K p L ↔ pairWeak F p L q K :=
  negative_sameBlock_reverse_iff_pairWeak_swap F h1 h5 h6 h7 q K p L

theorem reverse_a5 (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : NegativeRecordProcessing F) (h7 : NegativeActionProcessing F) :
    A5_BlockComparisonCoherence (reverseFamily F) := by
  constructor
  · intro A R _ _ _ _ _ _ K q p
    exact (h5.duplication K p q).trans
      (reverse_pairWeak_iff F h1 h5 h6 h7 q K p K).symm
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    exact (h5.irrelevant_blocks Act Rec K j i (Ne.symm hij) qj qi).trans
      (reverse_pairWeak_iff F h1 h5 h6 h7 qi (K i) qj (K j)).symm

theorem reverse_a6 (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : NegativeRecordProcessing F) (h7 : NegativeActionProcessing F) :
    A6_RecordDataProcessing (reverseFamily F) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  exact (reverse_pairWeak_iff F h1 h5 h6 h7 q K q (recordPostprocess K T)).mpr
    (h6 K T q)

theorem reverse_a7 (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : NegativeRecordProcessing F) (h7 : NegativeActionProcessing F) :
    A7_ActionDataProcessing (reverseFamily F) := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
  exact (reverse_pairWeak_iff F h1 h5 h6 h7 q K
    (Channel.actionPushforward q S) Kh).mpr (h7 K q S Kh hc)

theorem reverse_a8 (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : NegativeRecordProcessing F) (h7 : NegativeActionProcessing F)
    (h8 : A8_RecordwiseSureThing F) :
    A8_RecordwiseSureThing (reverseFamily F) := by
  intro A R _ _ _ _ _ _ q P K L M hp
  rw [reverse_pairWeak_iff F h1 h5 h6 h7,
    reverse_pairWeak_iff F h1 h5 h6 h7]
  exact h8 q P L K M hp

/-- Swapping the two benchmark action labels exchanges its material payoffs. -/
def flipRelevanceBit : RelevanceBit.{u} ≃ RelevanceBit.{u} where
  toFun b := ⟨!b.down⟩
  invFun b := ⟨!b.down⟩
  left_inv b := by cases b with | up b => cases b <;> rfl
  right_inv b := by cases b with | up b => cases b <;> rfl

theorem reverse_a3 (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : NegativeRecordProcessing F) (h7 : NegativeActionProcessing F)
    (h3 : A3_MaterialRelevance F) : A3_MaterialRelevance (reverseFamily F) := by
  obtain ⟨op, om, hne, hstrict⟩ := h3
  refine ⟨om, op, Ne.symm hne, ?_⟩
  let G := reverseFamily F
  let e := flipRelevanceBit.{u}
  have hK : Relabeling.relabelChannel e (Equiv.refl (O × PUnit))
      (materialRelevanceBenchmarkChannel op om) =
      materialRelevanceBenchmarkChannel om op := by
    ext a z
    rcases a with ⟨a⟩
    cases a <;> simp [e, flipRelevanceBit, Relabeling.relabelChannel,
      Relabeling.relabelDist, materialRelevanceBenchmarkChannel]
  have hq : Relabeling.relabelDist e materialRelevanceWorsePrior =
      materialRelevanceBetterPrior := by
    ext a
    rcases a with ⟨a⟩
    cases a <;> simp [e, flipRelevanceBit, Relabeling.relabelDist,
      materialRelevanceWorsePrior, materialRelevanceBetterPrior, Dist.pure_apply]
  have hp : Relabeling.relabelDist e materialRelevanceBetterPrior =
      materialRelevanceWorsePrior := by
    ext a
    rcases a with ⟨a⟩
    cases a <;> simp [e, flipRelevanceBit, Relabeling.relabelDist,
      materialRelevanceWorsePrior, materialRelevanceBetterPrior, Dist.pure_apply]
  have hf := fixed_rel_iff_actionEquiv G (reverse_a1 F h1)
    (reverse_a5 F h1 h5 h6 h7) (reverse_a7 F h1 h5 h6 h7) e
    (materialRelevanceBenchmarkChannel op om)
    materialRelevanceWorsePrior materialRelevanceBetterPrior
  have hb := fixed_rel_iff_actionEquiv G (reverse_a1 F h1)
    (reverse_a5 F h1 h5 h6 h7) (reverse_a7 F h1 h5 h6 h7) e
    (materialRelevanceBenchmarkChannel op om)
    materialRelevanceBetterPrior materialRelevanceWorsePrior
  rw [hK, hq, hp] at hf hb
  exact ⟨hf.mp hstrict.1, fun hn => hstrict.2 (hb.mpr hn)⟩

theorem reverse_axioms (F : FixedPayoffPrefFamily O) (h : SignBackground F)
    (h4 : NegativeTraceRelevance F) (h6 : NegativeRecordProcessing F)
    (h7 : NegativeActionProcessing F) : TraceTemperedAxiomsV10 (reverseFamily F) := by
  exact ⟨reverse_a1 F h.a1, reverse_a2 F h.a2,
    reverse_a3 F h.a1 h.a5 h6 h7 h.a3, h4,
    reverse_a5 F h.a1 h.a5 h6 h7, reverse_a6 F h.a1 h.a5 h6 h7,
    reverse_a7 F h.a1 h.a5 h6 h7, reverse_a8 F h.a1 h.a5 h6 h7 h.a8⟩

end TraceableAgency.Theorem1.Section3
