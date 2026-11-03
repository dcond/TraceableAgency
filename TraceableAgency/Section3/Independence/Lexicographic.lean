import TraceableAgency.Section3.Independence.Pareto

namespace TraceableAgency.Section3.Independence

open TraceableAgency TraceableAgency.Theorem1 Filter Topology

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

def lexFamily (u : O → ℝ) : FixedPayoffPrefFamily O :=
  coordinateFamily u (fun x y => y.1 < x.1 ∨ (x.1 = y.1 ∧ y.2 ≤ x.2))

theorem lex_a1 (u : O → ℝ) : A1_WeakOrder (lexFamily u) := by
  intro A R _ _ _ _ _ _ K
  constructor
  · intro q p
    change (_ < _ ∨ (_ = _ ∧ _ ≤ _)) ∨ (_ < _ ∨ (_ = _ ∧ _ ≤ _))
    rcases lt_trichotomy (expectedPayoffUtility u p K) (expectedPayoffUtility u q K)
      with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total (mutualInfo p K) (mutualInfo q K) with hi | hi
      · exact Or.inl (Or.inr ⟨h.symm, hi⟩)
      · exact Or.inr (Or.inr ⟨h, hi⟩)
    · exact Or.inr (Or.inl h)
  · intro q p r hqp hpr
    rcases hqp with hqp | ⟨heq, hqp⟩ <;>
      rcases hpr with hpr | ⟨heq', hpr⟩
    · exact Or.inl (hpr.trans hqp)
    · exact Or.inl (by linarith)
    · exact Or.inl (by linarith)
    · exact Or.inr ⟨heq.trans heq', hpr.trans hqp⟩

theorem lex_pairWeak_iff (u : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (lexFamily u) q K p L ↔
      (pairWeak (traceScoreFamily u 0) q K p L ∧
        ¬ pairWeak (traceScoreFamily u 0) p L q K) ∨
      (pairWeak (traceScoreFamily u 0) q K p L ∧
        pairWeak (traceScoreFamily u 0) p L q K ∧
        pairWeak (traceScoreFamily (fun _ : O => 0) 1) q K p L) := by
  rw [show lexFamily u = coordinateFamily u
    (fun x y => y.1 < x.1 ∨ (x.1 = y.1 ∧ y.2 ≤ x.2)) by rfl,
    coordinateFamily_pairWeak]
  simp only [pairWeak_iff_value_ge (traceScoreFamily_rep u 0),
    pairWeak_iff_value_ge (traceScoreFamily_rep (fun _ : O => 0) 1),
    traceTemperedValue, zero_mul, add_zero, expectedPayoffUtility_zero, one_mul, zero_add]
  constructor
  · rintro (hlt | ⟨heq, hi⟩)
    · exact Or.inl ⟨hlt.le, not_le.mpr hlt⟩
    · exact Or.inr ⟨heq.ge, heq.le, hi⟩
  · rintro (⟨_, hnot⟩ | ⟨h1, h2, hi⟩)
    · exact Or.inl (lt_of_not_ge hnot)
    · exact Or.inr ⟨le_antisymm h2 h1, hi⟩

theorem lex_a3 (u : O → ℝ) (op om : O) (hu : u om < u op) :
    A3_MaterialRelevance (lexFamily u) := by
  refine ⟨op, om, ?_, ?_, ?_⟩
  · exact fun h => (ne_of_lt hu) (congrArg u h.symm)
  · change _ < _ ∨ (_ = _ ∧ _ ≤ _)
    left
    simpa using hu
  · intro hr
    change _ < _ ∨ (_ = _ ∧ _ ≤ _) at hr
    simp only [expectedPayoffUtility_material_better, expectedPayoffUtility_material_worse] at hr
    rcases hr with hr | ⟨hr, _⟩ <;> linarith

theorem lex_a4 [Nonempty O] (u : O → ℝ) : A4_TraceRelevance (lexFamily u) := by
  obtain ⟨o, hs⟩ := (informationOnly_counterexample (O := O)).2.2.2.1
  have hi : mutualInfo traceRelevanceUnrevealingPrior (traceRelevanceBenchmarkChannel o) <
      mutualInfo traceRelevanceRevealingPrior (traceRelevanceBenchmarkChannel o) := by
    apply lt_of_not_ge
    simpa [traceScoreFamily, scoreFamily, traceTemperedValue] using hs.2
  refine ⟨o, ?_, ?_⟩
  · change _ < _ ∨ (_ = _ ∧ _ ≤ _)
    right
    exact ⟨by rw [expectedPayoffUtility_traceBenchmark, expectedPayoffUtility_traceBenchmark], hi.le⟩
  · change ¬ (_ < _ ∨ (_ = _ ∧ _ ≤ _))
    rw [expectedPayoffUtility_traceBenchmark, expectedPayoffUtility_traceBenchmark]
    simp [not_le.mpr hi]

theorem lex_a6 (u : O → ℝ) : A6_RecordDataProcessing (lexFamily u) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  unfold lexFamily
  rw [coordinateFamily_pairWeak]
  right
  exact ⟨(expectedPayoffUtility_recordPostprocess u q K T).symm,
    mutualInfo_outcome_postprocess_le q K (payoffPreservingRecordKernel T)⟩

theorem lex_a7 (u : O → ℝ) : A7_ActionDataProcessing (lexFamily u) := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
  unfold lexFamily
  rw [coordinateFamily_pairWeak]
  right
  exact ⟨(expectedPayoffUtility_actionProcessor u K q S Kh hc).symm,
    mutualInfo_action_bayes_pushforward_le K q S Kh
      (bayesCompletion_of_actionProcessorCompletion K q S Kh hc)⟩

theorem lex_a8 (u : O → ℝ) : A8_RecordwiseSureThing (lexFamily u) := by
  intro A R _ _ _ _ _ _ q P K L M hpos
  rw [lex_pairWeak_iff, lex_pairWeak_iff,
    traceScoreFamily_a8 u 0 (by norm_num) q P K L M hpos,
    traceScoreFamily_a8 u 0 (by norm_num) q P L K M hpos,
    traceScoreFamily_a8 (fun _ : O => 0) 1 (by norm_num) q P K L M hpos]

/-- A fixed channel witnesses the failure of sequential closedness. -/
theorem lex_not_a2 (u : O → ℝ) (op om : O) (hu : u om < u op) :
    ¬ A2_Continuity (lexFamily u) := by
  intro h2
  let t : ℕ → ℝ := fun n => (1 / 2) ^ n
  have ht0 : ∀ n, 0 < t n := fun n => pow_pos (by norm_num) n
  have ht1 : ∀ n, t n ≤ 1 := fun n => pow_le_one₀ (by norm_num) (by norm_num)
  have ht : Tendsto t atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  let K := materialRelevanceBenchmarkChannel op om
  let L := fullRevealAtPayoff (A := RelevanceBit.{u}) om
  let C := commonPayoffBlockChannel K L
  let p : Dist RelevanceBit.{u} := Dist.uniform
  let qn : ℕ → Dist RelevanceBit.{u} := fun n =>
    Dist.mix (t n) (ht0 n).le (ht1 n) materialRelevanceBetterPrior materialRelevanceWorsePrior
  have hqn : DistConverges qn materialRelevanceWorsePrior := by
    intro a
    have hh := (ht.mul_const (materialRelevanceBetterPrior a)).add
      (((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul_const (materialRelevanceWorsePrior a))
    simpa [qn, Dist.mix_apply] using hh
  have hleft : DistConverges (fun n => (leftBlockDist (B := RelevanceBit.{u}) (qn n)))
      (leftBlockDist materialRelevanceWorsePrior) := by
    intro a
    cases a with
    | inl a => exact hqn a
    | inr b => exact tendsto_const_nhds
  have hn : ∀ n, (lexFamily u).rel C (leftBlockDist (qn n)) (rightBlockDist p) := by
    intro n
    apply (coordinateFamily_pairWeak u _ (qn n) K p L).mpr
    left
    rw [expectedPayoffUtility_fullRevealAtPayoff]
    change u om < expectedPayoffUtility u
      (Dist.mix (t n) (ht0 n).le (ht1 n) materialRelevanceBetterPrior materialRelevanceWorsePrior) K
    rw [expectedPayoffUtility_mix, expectedPayoffUtility_material_better,
      expectedPayoffUtility_material_worse]
    nlinarith [mul_pos (ht0 n) (sub_pos.mpr hu)]
  have hlim := h2 (fun _ => C) C
    (fun n => leftBlockDist (qn n)) (fun _ => rightBlockDist p)
    (leftBlockDist materialRelevanceWorsePrior) (rightBlockDist p)
    (fun _ _ => tendsto_const_nhds) hleft (fun _ => tendsto_const_nhds) hn
  have hh := (coordinateFamily_pairWeak u _ materialRelevanceWorsePrior K p L).mp hlim
  have hI : 0 < mutualInfo p L := by
    rw [mutualInfo_fullRevealAtPayoff]
    exact entropy_pos_of_fullSupport_nontrivial p Dist.uniform_fullSupport
  change _ < _ ∨ (_ = _ ∧ _ ≤ _) at hh
  rw [expectedPayoffUtility_material_worse, expectedPayoffUtility_fullRevealAtPayoff] at hh
  have hz : mutualInfo materialRelevanceWorsePrior K = 0 := mutualInfo_pure _ _
  rcases hh with hh | ⟨_, hh⟩
  · exact (lt_irrefl _ hh)
  · exact (not_le_of_gt hI) (hz ▸ hh)

theorem lex_counterexample [Nonempty O] (u : O → ℝ) (op om : O) (hu : u om < u op) :
    A1_WeakOrder (lexFamily u) ∧ ¬ A2_Continuity (lexFamily u) ∧
    A3_MaterialRelevance (lexFamily u) ∧ A4_TraceRelevance (lexFamily u) ∧
    A5_BlockComparisonCoherence (lexFamily u) ∧ A6_RecordDataProcessing (lexFamily u) ∧
    A7_ActionDataProcessing (lexFamily u) ∧ A8_RecordwiseSureThing (lexFamily u) := by
  exact ⟨lex_a1 u, lex_not_a2 u op om hu, lex_a3 u op om hu, lex_a4 u,
    coordinateFamily_a5 u _, lex_a6 u, lex_a7 u, lex_a8 u⟩

end TraceableAgency.Section3.Independence
