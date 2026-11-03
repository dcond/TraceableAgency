import TraceableAgency.Section3.Independence.Relevance

/-! The paper's conditional-noise witness, with noise coefficient one. -/

namespace TraceableAgency.Section3.Independence

open TraceableAgency TraceableAgency.Theorem1 Filter Topology

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

noncomputable def noiseScore (u : O → ℝ)
    {A R : Type u} [Fintype A] [Fintype R]
    (q : Dist A) (K : Channel A (O × R)) : ℝ :=
  traceTemperedValue u 2 q K - entropy (Channel.outcomeMarginal K q)

/-- Equivalently, `U + I - H(O,R | A)`. -/
theorem noiseScore_eq (u : O → ℝ)
    {A R : Type u} [Fintype A] [Fintype R]
    (q : Dist A) (K : Channel A (O × R)) :
    noiseScore u q K = expectedPayoffUtility u q K + mutualInfo q K -
      ∑ a, q a * entropy (K a) := by
  unfold noiseScore traceTemperedValue mutualInfo
  ring

noncomputable def noiseFamily (u : O → ℝ) : FixedPayoffPrefFamily O :=
  scoreFamily (fun q K => noiseScore u q K)

theorem noiseScore_block_left (u : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (L : Channel B (O × S)) :
    noiseScore u (leftBlockDist q) (commonPayoffBlockChannel K L) = noiseScore u q K := by
  unfold noiseScore
  rw [traceTemperedValue_commonBlock_left]
  congr 1
  rw [commonPayoffBlockChannel, outcomeMarginal_relabelOutcome,
    GenericFaddeev.entropy_relabel]
  exact entropy_outcomeMarginal_block_inl K L q

theorem noiseScore_block_right (u : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (p : Dist B) (K : Channel A (O × R)) (L : Channel B (O × S)) :
    noiseScore u (rightBlockDist p) (commonPayoffBlockChannel K L) = noiseScore u p L := by
  unfold noiseScore
  rw [traceTemperedValue_commonBlock_right]
  congr 1
  rw [commonPayoffBlockChannel, outcomeMarginal_relabelOutcome,
    GenericFaddeev.entropy_relabel]
  exact entropy_outcomeMarginal_block_inr K L p

theorem noise_pairWeak (u : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (noiseFamily u) q K p L ↔ noiseScore u p L ≤ noiseScore u q K := by
  unfold pairWeak noiseFamily scoreFamily
  change noiseScore u (leftBlockDist q) (commonPayoffBlockChannel K L) ≥
    noiseScore u (rightBlockDist p) (commonPayoffBlockChannel K L) ↔ _
  rw [noiseScore_block_left, noiseScore_block_right]

theorem noise_a2 (u : O → ℝ) : A2_Continuity (noiseFamily u) := by
  apply scoreFamily_a2
  intro A R _ _ _ _ _ _ Kn K qn q hK hq
  exact (tendsto_traceTemperedValue_of_converges u 2 Kn K qn q hK hq).sub
    (tendsto_entropy_outcomeMarginal_of_converges' Kn K qn q hK hq)

theorem noise_a3 (u : O → ℝ) (op om : O) (hu : u om < u op) :
    A3_MaterialRelevance (noiseFamily u) := by
  have hp : noiseScore u materialRelevanceBetterPrior
      (materialRelevanceBenchmarkChannel op om) = u op := by
    rw [noiseScore_eq, expectedPayoffUtility_material_better]
    simp [materialRelevanceBetterPrior, Dist.pure_apply,
      materialRelevanceBenchmarkChannel, entropy_pure']
  have hm : noiseScore u materialRelevanceWorsePrior
      (materialRelevanceBenchmarkChannel op om) = u om := by
    rw [noiseScore_eq, expectedPayoffUtility_material_worse]
    simp [materialRelevanceWorsePrior, Dist.pure_apply,
      materialRelevanceBenchmarkChannel, entropy_pure']
  refine ⟨op, om, fun h => (ne_of_lt hu) (congrArg u h.symm), ?_⟩
  change noiseScore u _ _ ≥ noiseScore u _ _ ∧ ¬ noiseScore u _ _ ≥ noiseScore u _ _
  rw [hp, hm]
  exact ⟨hu.le, not_le.mpr hu⟩

theorem traceBenchmark_same_output (o : O) :
    Channel.outcomeMarginal (traceRelevanceBenchmarkChannel o) traceRelevanceRevealingPrior =
      Channel.outcomeMarginal (traceRelevanceBenchmarkChannel o) traceRelevanceUnrevealingPrior := by
  ext z
  rcases z with ⟨o', b⟩
  simp only [Channel.outcomeMarginal_apply, traceRelevanceRevealingPrior,
    traceRelevanceUnrevealingPrior, Fintype.sum_sum_type, inlDist_apply_inl,
    inlDist_apply_inr, inrDist_apply_inl, inrDist_apply_inr,
    zero_mul, Finset.sum_const_zero, zero_add, add_zero, traceRelevanceBenchmarkChannel]
  by_cases ho : o' = o
  · subst o'
    simp [Dist.pure_apply, ← Finset.sum_mul, traceRelevanceFairPrior.sum_eq_one]
  · simp [Dist.pure_apply, ho]

theorem noise_a4 (u : O → ℝ) (hu : ¬ IsConstantPayoffIndex u) :
    A4_TraceRelevance (noiseFamily u) := by
  obtain ⟨o, hs⟩ :=
    (traceTemperedAxiomsV10_of_representation hu (by norm_num : (0 : ℝ) < 2)
      (traceScoreFamily_rep u 2)).a4
  refine ⟨o, ?_⟩
  change noiseScore u _ _ ≥ noiseScore u _ _ ∧ ¬ noiseScore u _ _ ≥ noiseScore u _ _
  unfold noiseScore
  rw [traceBenchmark_same_output]
  change traceTemperedValue u 2 _ _ ≥ traceTemperedValue u 2 _ _ ∧
    ¬ traceTemperedValue u 2 _ _ ≥ traceTemperedValue u 2 _ _ at hs
  constructor
  · linarith [hs.1]
  · intro hh
    apply hs.2
    linarith

theorem noise_a5 (u : O → ℝ) : A5_BlockComparisonCoherence (noiseFamily u) := by
  constructor
  · intro A R _ _ _ _ _ _ K q p
    rw [noise_pairWeak]
    rfl
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    rw [noise_pairWeak]
    change noiseScore u _ _ ≥ noiseScore u _ _ ↔ _
    unfold noiseScore
    rw [traceTemperedValue_commonBlockFamily_embed,
      traceTemperedValue_commonBlockFamily_embed]
    simp only [commonPayoffBlockFamilyChannel, outcomeMarginal_relabelOutcome,
      GenericFaddeev.entropy_relabel, commonPayoffBlockEmbed,
      entropy_outcomeMarginal_blockFamily_embed]

theorem noise_a7 (u : O → ℝ) : A7_ActionDataProcessing (noiseFamily u) := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
  rw [noise_pairWeak]
  unfold noiseScore
  rw [outcomeMarginal_bayesPushforwardCompletion K q S Kh
    (bayesCompletion_of_actionProcessorCompletion K q S Kh hc)]
  exact sub_le_sub_right ((pairWeak_iff_value_ge (traceScoreFamily_rep u 2) _ _ _ _).mp
    (traceScoreFamily_a7 u 2 (by norm_num) K q S Kh hc)) _

theorem noiseScore_compound (u : O → ℝ)
    {A Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u) [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)] (q : Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × Rec y)) :
    noiseScore u q (commonPayoffCompound Rec P K) =
      2 * mutualInfo q P - entropy (Channel.outcomeMarginal P q) +
      ∑ y, (Channel.outcomeMarginal P q) y * noiseScore u (branchPosterior P q y) (K y) := by
  unfold noiseScore
  rw [traceTemperedValue_commonCompound]
  rw [commonPayoffCompound, outcomeMarginal_relabelOutcome,
    GenericFaddeev.entropy_relabel, entropy_outcomeMarginal_seqComposeDep]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  unfold branchPosterior
  ring

theorem sum_relevanceBit (f : RelevanceBit.{u} → ℝ) :
    (∑ b, f b) = f (ULift.up false) + f (ULift.up true) := by
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp f]
  simp [Fintype.sum_bool, Equiv.ulift]
  ring

theorem noiseScore_binary_difference (u : O → ℝ)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (P : Channel A RelevanceBit) (K L M : Channel A (O × R)) :
    noiseScore u q (binaryPayoffCompound P K M) -
      noiseScore u q (binaryPayoffCompound P L M) =
      (Channel.outcomeMarginal P q) (ULift.up true) *
        (noiseScore u (branchPosterior P q (ULift.up true)) K -
          noiseScore u (branchPosterior P q (ULift.up true)) L) := by
  rw [binaryPayoffCompound, binaryPayoffCompound, noiseScore_compound, noiseScore_compound,
    sum_relevanceBit, sum_relevanceBit]
  simp only [binaryContinuationProfile, Bool.false_eq_true, if_false, if_true]
  ring

theorem noise_a8 (u : O → ℝ) : A8_RecordwiseSureThing (noiseFamily u) := by
  intro A R _ _ _ _ _ _ q P K L M hpos
  rw [noise_pairWeak, noise_pairWeak]
  constructor
  · intro hl
    apply sub_nonneg.mp
    rw [noiseScore_binary_difference]
    exact mul_nonneg hpos.le (sub_nonneg.mpr hl)
  · intro hl
    apply sub_nonneg.mp
    apply (mul_nonneg_iff_of_pos_left hpos).mp
    rw [← noiseScore_binary_difference]
    exact sub_nonneg.mpr hl

theorem noise_not_a6 [Nonempty O] (u : O → ℝ) : ¬ A6_RecordDataProcessing (noiseFamily u) := by
  intro h6
  let o : O := Classical.choice ‹Nonempty O›
  let q : Dist PUnit.{u+1} := Dist.pure PUnit.unit
  let K := fairIndependentAtPayoff (A := PUnit.{u+1}) o
  let L := uninformativeAtPayoff (A := PUnit.{u+1}) o
  have he : recordPostprocess K eraseAllRecordsProcessor = L := by
    ext a z
    rcases z with ⟨o', r⟩
    cases r
    simp only [K, L, recordPostprocess, payoffPreservingRecordKernel,
      eraseAllRecordsProcessor, Channel.postprocess, Fintype.sum_prod_type,
      fairIndependentAtPayoff, uninformativeAtPayoff, Dist.pure_apply]
    by_cases ho : o' = o
    · subst o'
      simp [traceRelevanceFairPrior.sum_eq_one]
    · simp [ho, Ne.symm ho]
  have hH : entropy (Channel.outcomeMarginal K q) = entropy traceRelevanceFairPrior := by
    have hm : Channel.outcomeMarginal K q =
        Channel.outcomeMarginal (fullRevealAtPayoff o) traceRelevanceFairPrior := by
      ext z
      rcases z with ⟨o', b⟩
      rw [outcomeMarginal_fullRevealAtPayoff_apply]
      simp [Channel.outcomeMarginal_apply, K, q, fairIndependentAtPayoff, Dist.pure_apply]
    rw [hm, entropy_outcomeMarginal_fullRevealAtPayoff]
  have hzero : entropy (Channel.outcomeMarginal L q) = 0 := by
    rw [outcomeMarginal_uninformativeAtPayoff]
    exact entropy_pure' _
  have hI : 0 < entropy traceRelevanceFairPrior :=
    entropy_pos_of_fullSupport_nontrivial _ Dist.uniform_fullSupport
  have hh := h6 K eraseAllRecordsProcessor q
  rw [he, noise_pairWeak] at hh
  unfold noiseScore traceTemperedValue at hh
  have hpay := expectedPayoffUtility_recordPostprocess u q K eraseAllRecordsProcessor
  rw [he] at hpay
  have hmK : mutualInfo q K = 0 := mutualInfo_pure _ _
  have hmL : mutualInfo q L = 0 := mutualInfo_pure _ _
  rw [hpay, hmK, hmL, hzero, hH] at hh
  linarith

theorem noise_counterexample [Nonempty O] (u : O → ℝ) (op om : O) (hu : u om < u op) :
    A1_WeakOrder (noiseFamily u) ∧ A2_Continuity (noiseFamily u) ∧
    A3_MaterialRelevance (noiseFamily u) ∧ A4_TraceRelevance (noiseFamily u) ∧
    A5_BlockComparisonCoherence (noiseFamily u) ∧ ¬ A6_RecordDataProcessing (noiseFamily u) ∧
    A7_ActionDataProcessing (noiseFamily u) ∧ A8_RecordwiseSureThing (noiseFamily u) := by
  have hnc : ¬ IsConstantPayoffIndex u := by
    rintro ⟨c, hc⟩
    simpa [hc op, hc om] using hu
  exact ⟨scoreFamily_a1 _, noise_a2 u, noise_a3 u op om hu, noise_a4 u hnc,
    noise_a5 u, noise_not_a6 u, noise_a7 u, noise_a8 u⟩

end TraceableAgency.Section3.Independence
