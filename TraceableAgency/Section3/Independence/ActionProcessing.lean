import TraceableAgency.Section3.Independence.Basic

/-!
# Independence of action processing

Adding the entropy of the chosen action lottery preserves the other seven
axioms. A7 alone rules out a taste for action randomisation that leaves no
evidence in the visible consequence. This is a shorter witness than the
Gini example, for the same independence proposition.
-/

namespace TraceableAgency.Section3.Independence

open TraceableAgency Theorem1 Filter Topology

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

noncomputable def actionEntropyFamily (v : O → ℝ) : FixedPayoffPrefFamily O :=
  scoreFamily (fun q K => traceTemperedValue v 1 q K + entropy q)

theorem actionEntropy_pairWeak (v : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (actionEntropyFamily v) q K p L ↔
      traceTemperedValue v 1 q K + entropy q ≥ traceTemperedValue v 1 p L + entropy p := by
  unfold pairWeak actionEntropyFamily scoreFamily
  change traceTemperedValue v 1 (leftBlockDist q) (commonPayoffBlockChannel K L) +
    entropy (leftBlockDist q) ≥
    traceTemperedValue v 1 (rightBlockDist p) (commonPayoffBlockChannel K L) +
    entropy (rightBlockDist p) ↔ _
  rw [traceTemperedValue_commonBlock_left, traceTemperedValue_commonBlock_right]
  simp only [leftBlockDist, rightBlockDist, entropy_inlDist, entropy_inrDist]

theorem actionEntropy_a2 (v : O → ℝ) : A2_Continuity (actionEntropyFamily v) := by
  apply scoreFamily_a2
  intro A R _ _ _ _ _ _ Kn K qn q hK hq
  apply (tendsto_traceTemperedValue_of_converges v 1 Kn K qn q hK hq).add
  exact tendsto_finsetSum _ fun a _ => continuous_entropyTerm.continuousAt.tendsto.comp (hq a)

theorem actionEntropy_a3 (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) :
    A3_MaterialRelevance (actionEntropyFamily v) := by
  obtain ⟨op, om, hne, hstrict⟩ :=
    (traceTemperedAxiomsV10_of_representation hv (by norm_num : (0:ℝ)<1)
      (traceScoreFamily_rep v 1)).a3
  refine ⟨op, om, hne, ?_⟩
  simpa only [FixedPayoffPrefFamily.strictRel, actionEntropyFamily, traceScoreFamily,
    scoreFamily, materialRelevanceBetterPrior, materialRelevanceWorsePrior,
    entropy_pure', add_zero] using hstrict

theorem actionEntropy_a4 (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) :
    A4_TraceRelevance (actionEntropyFamily v) := by
  obtain ⟨o, hstrict⟩ :=
    (traceTemperedAxiomsV10_of_representation hv (by norm_num : (0:ℝ)<1)
      (traceScoreFamily_rep v 1)).a4
  refine ⟨o, ?_⟩
  simpa only [FixedPayoffPrefFamily.strictRel, actionEntropyFamily, traceScoreFamily,
    scoreFamily, traceRelevanceRevealingPrior, traceRelevanceUnrevealingPrior,
    entropy_inlDist, entropy_inrDist, ge_iff_le, add_le_add_iff_right] using hstrict

theorem actionEntropy_a5 (v : O → ℝ) : A5_BlockComparisonCoherence (actionEntropyFamily v) := by
  constructor
  · intro A R _ _ _ _ _ _ K q p
    rw [actionEntropy_pairWeak]
    rfl
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    rw [actionEntropy_pairWeak]
    change _ + _ ≥ _ + _ ↔ _
    rw [traceTemperedValue_commonBlockFamily_embed, traceTemperedValue_commonBlockFamily_embed]
    simp only [commonPayoffBlockEmbed, entropy_blockEmbedDist]

theorem actionEntropy_a6 (v : O → ℝ) : A6_RecordDataProcessing (actionEntropyFamily v) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [actionEntropy_pairWeak]
  have hh := (pairWeak_iff_value_ge (traceScoreFamily_rep v 1) _ _ _ _).mp
    (traceScoreFamily_a6 v 1 (by norm_num) K T q)
  linarith

theorem actionEntropy_a8 (v : O → ℝ) : A8_RecordwiseSureThing (actionEntropyFamily v) := by
  intro A R _ _ _ _ _ _ q P K L M hy
  simp only [actionEntropy_pairWeak, ge_iff_le, add_le_add_iff_right]
  have h := traceScoreFamily_a8 v 1 (by norm_num) q P K L M hy
  simpa only [pairWeak_iff_value_ge (traceScoreFamily_rep v 1), ge_iff_le] using h

theorem actionEntropy_not_a7 [Nonempty O] (v : O → ℝ) :
    ¬ A7_ActionDataProcessing (actionEntropyFamily v) := by
  intro h
  let o : O := Classical.arbitrary O
  let q : Dist PUnit.{u+1} := Dist.pure PUnit.unit
  let K := uninformativeAtPayoff (A := PUnit.{u+1}) o
  let Kh := uninformativeAtPayoff (A := RelevanceBit.{u}) o
  let S : Channel.ActionKernel PUnit.{u+1} RelevanceBit.{u} := fun _ => Dist.uniform
  have hpush : Channel.actionPushforward q S = Dist.uniform := by
    ext b
    simp [Channel.actionPushforward, q, S, Dist.pure_apply]
  have hc : IsActionProcessorCompletion K q S Kh := by
    intro b z
    rw [hpush]
    simp [K, Kh, S, q, uninformativeAtPayoff, Dist.pure_apply]
  have hh := h K q S Kh hc
  rw [actionEntropy_pairWeak, hpush, show K = uninformativeAtPayoff o from rfl,
    show Kh = uninformativeAtPayoff o from rfl,
    traceTemperedValue_uninformativeAtPayoff, traceTemperedValue_uninformativeAtPayoff] at hh
  have hz : entropy q = 0 := entropy_pure' _
  have hpos : 0 < entropy (Dist.uniform (A := RelevanceBit.{u})) :=
    entropy_uniform_ulift_bool_pos
  linarith

theorem actionEntropy_counterexample [Nonempty O] (v : O → ℝ)
    (hv : ¬ IsConstantPayoffIndex v) :
    let F := actionEntropyFamily v
    A1_WeakOrder F ∧ A2_Continuity F ∧ A3_MaterialRelevance F ∧ A4_TraceRelevance F ∧
    A5_BlockComparisonCoherence F ∧ A6_RecordDataProcessing F ∧
    ¬ A7_ActionDataProcessing F ∧ A8_RecordwiseSureThing F := by
  exact ⟨scoreFamily_a1 _, actionEntropy_a2 v, actionEntropy_a3 v hv,
    actionEntropy_a4 v hv, actionEntropy_a5 v, actionEntropy_a6 v,
    actionEntropy_not_a7 v, actionEntropy_a8 v⟩

end TraceableAgency.Section3.Independence
