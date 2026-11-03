import TraceableAgency.Section3.Independence.Basic

namespace TraceableAgency.Section3.Independence

open TraceableAgency TraceableAgency.Theorem1

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

theorem informationOnly_not_a3 :
    ¬ A3_MaterialRelevance (traceScoreFamily (fun _ : O => 0) 1) := by
  rintro ⟨op, om, _, hstrict⟩
  apply hstrict.2
  change traceTemperedValue (fun _ : O => 0) 1 _ _ ≥
    traceTemperedValue (fun _ : O => 0) 1 _ _
  simp [traceTemperedValue, materialRelevanceBetterPrior, materialRelevanceWorsePrior]

/-- Dropping material relevance permits pure mutual information. -/
theorem informationOnly_counterexample [Nonempty O] :
    let F := traceScoreFamily (fun _ : O => 0) 1
    A1_WeakOrder F ∧ A2_Continuity F ∧ ¬ A3_MaterialRelevance F ∧
    A4_TraceRelevance F ∧ A5_BlockComparisonCoherence F ∧
    A6_RecordDataProcessing F ∧ A7_ActionDataProcessing F ∧ A8_RecordwiseSureThing F := by
  dsimp only
  let F := traceScoreFamily (fun _ : O => 0) 1
  have hr : WithinChannelRepresentation F (fun _ : O => 0) 1 := traceScoreFamily_rep (fun _ : O => 0) 1
  have h1 : A1_WeakOrder _ := a1_weakOrder_of_representation hr
  have h5 := a5_blockCoherence_of_representation hr
  have h6 : A6_RecordDataProcessing _ := traceScoreFamily_a6 (fun _ : O => 0) 1 (by norm_num)
  have h7 : A7_ActionDataProcessing _ := traceScoreFamily_a7 (fun _ : O => 0) 1 (by norm_num)
  refine ⟨h1, a2_continuity_of_representation hr, informationOnly_not_a3, ?_, h5,
    h6, h7, traceScoreFamily_a8 (fun _ : O => 0) 1 (by norm_num)⟩
  let o : O := Classical.choice ‹Nonempty O›
  exact positiveOrientationAt_implies_traceRelevance_fixed F h1 h5 h6 h7 o
    (positiveTraceOrientationAt_of_representation o (by norm_num) hr)

theorem expectedPayoffUtility_traceBenchmark
    (u : O → ℝ) (o : O) (q : Dist (RelevanceBit ⊕ RelevanceBit)) :
    expectedPayoffUtility u q (traceRelevanceBenchmarkChannel o) = u o := by
  classical
  have hrow : ∀ a : RelevanceBit ⊕ RelevanceBit,
      (∑ z, traceRelevanceBenchmarkChannel o a z * u z.1) = u o := by
    intro a
    cases a with
    | inl b => simp [traceRelevanceBenchmarkChannel, Dist.pure_apply]
    | inr b =>
        rw [Fintype.sum_prod_type]
        simp only [traceRelevanceBenchmarkChannel]
        rw [Finset.sum_eq_single o]
        · simp only [ite_true]
          rw [← Finset.sum_mul, traceRelevanceFairPrior.sum_eq_one, one_mul]
        · intro x _ hx
          simp [hx]
        · simp
  calc
    expectedPayoffUtility u q (traceRelevanceBenchmarkChannel o) = ∑ a, q a * u o := by
      apply Finset.sum_congr rfl
      intro a _
      rw [hrow]
    _ = u o := by rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

theorem materialOnly_not_a4 (u : O → ℝ) :
    ¬ A4_TraceRelevance (traceScoreFamily u 0) := by
  rintro ⟨o, hs⟩
  apply hs.2
  change traceTemperedValue u 0 _ _ ≥ traceTemperedValue u 0 _ _
  simp [traceTemperedValue, expectedPayoffUtility_traceBenchmark]

/-- Dropping trace relevance permits ordinary expected payoff utility. -/
theorem materialOnly_counterexample (u : O → ℝ) (hu : ¬ IsConstantPayoffIndex u) :
    let F := traceScoreFamily u 0
    A1_WeakOrder F ∧ A2_Continuity F ∧ A3_MaterialRelevance F ∧
    ¬ A4_TraceRelevance F ∧ A5_BlockComparisonCoherence F ∧
    A6_RecordDataProcessing F ∧ A7_ActionDataProcessing F ∧ A8_RecordwiseSureThing F := by
  dsimp only
  have hr : WithinChannelRepresentation (traceScoreFamily u 0) u 0 := traceScoreFamily_rep u 0
  have h1 : A1_WeakOrder _ := a1_weakOrder_of_representation hr
  have h5 := a5_blockCoherence_of_representation hr
  have h6 : A6_RecordDataProcessing _ := traceScoreFamily_a6 u 0 (by norm_num)
  have h7 : A7_ActionDataProcessing _ := traceScoreFamily_a7 u 0 (by norm_num)
  refine ⟨h1, a2_continuity_of_representation hr, ?_, materialOnly_not_a4 u,
    h5, h6, h7, traceScoreFamily_a8 u 0 (by norm_num)⟩
  exact (materialRelevance_bridge _ h1 h5 h6 h7).mpr
    (materialRelevanceEnvironment_of_representation hu hr)

end TraceableAgency.Section3.Independence
