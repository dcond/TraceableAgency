import TraceableAgency.Section3.Signs.Reverse

/-! The negative branch of the sign trichotomy, including the same-witness
finite-block conclusion, follows by reversing primitive preferences. -/
namespace TraceableAgency.Theorem1.Section3
open TraceableAgency
universe u
variable {O : Type u} [Fintype O] [DecidableEq O]

theorem traceTemperedValue_neg
    {A R : Type u} [Fintype A] [Fintype R]
    (v : O → ℝ) (c : ℝ) (q : Dist A) (K : Channel A (O × R)) :
    traceTemperedValue (fun o => -v o) (-c) q K =
      -traceTemperedValue v c q K := by
  simp [traceTemperedValue, expectedPayoffUtility, Finset.sum_neg_distrib, add_comm]

theorem negative_representation (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h4 : NegativeTraceRelevance F)
    (h6 : NegativeRecordProcessing F) (h7 : NegativeActionProcessing F) :
    ∃ (v : O → ℝ) (c : ℝ), ¬ IsConstantPayoffIndex v ∧ c < 0 ∧
      WithinChannelRepresentation F v c ∧ SameWitnessBlockRepresentation F v c := by
  obtain ⟨v, c, hv, hc, hw, hb⟩ :=
    (MaterialCalibration.theorem1V10Clauses_material (reverseFamily F)).2
      (reverse_axioms F h h4 h6 h7)
  refine ⟨fun o => -v o, -c, ?_, neg_neg_of_pos hc, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    apply hv
    refine ⟨-k, fun o => ?_⟩
    have hh := hk o
    linarith
  · intro A R _ _ _ _ _ _ K q p
    have hh := hw K p q
    simpa only [reverseFamily_rel, traceTemperedValue_neg, neg_le_neg_iff] using hh
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    have hh := hb Act Rec K j i (Ne.symm hij) qj qi
    simpa only [reverseFamily_rel, traceTemperedValue_neg, neg_le_neg_iff] using hh

end TraceableAgency.Theorem1.Section3
