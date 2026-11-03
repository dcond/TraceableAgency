import TraceableAgency.Section3.Independence.Relevance

namespace TraceableAgency.Section3.Independence

open TraceableAgency TraceableAgency.Theorem1

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

def paretoFamily (u : O → ℝ) : FixedPayoffPrefFamily O :=
  coordinateFamily u (fun x y => y.1 ≤ x.1 ∧ y.2 ≤ x.2)

theorem pareto_rel_iff (u : O → ℝ)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q p : Dist A) :
    (paretoFamily u).rel K q p ↔
      (traceScoreFamily u 0).rel K q p ∧
      (traceScoreFamily (fun _ : O => 0) 1).rel K q p := by
  simp [paretoFamily, coordinateFamily, traceScoreFamily, scoreFamily, traceTemperedValue]

theorem pareto_pairWeak_iff (u : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (paretoFamily u) q K p L ↔
      pairWeak (traceScoreFamily u 0) q K p L ∧
      pairWeak (traceScoreFamily (fun _ : O => 0) 1) q K p L := by
  exact pareto_rel_iff u _ _ _

theorem pareto_a2 (u : O → ℝ) : A2_Continuity (paretoFamily u) := by
  intro A R _ _ _ _ _ _ Kn K qn pn q p hK hq hp hn
  rw [pareto_rel_iff]
  constructor
  · exact a2_continuity_of_representation (traceScoreFamily_rep u 0)
      Kn K qn pn q p hK hq hp (fun n => (pareto_rel_iff u _ _ _).mp (hn n) |>.1)
  · exact a2_continuity_of_representation (traceScoreFamily_rep (fun _ : O => 0) 1)
      Kn K qn pn q p hK hq hp (fun n => (pareto_rel_iff u _ _ _).mp (hn n) |>.2)

theorem pareto_a3 (u : O → ℝ) (hu : ¬ IsConstantPayoffIndex u) :
    A3_MaterialRelevance (paretoFamily u) := by
  obtain ⟨op, om, hne, hs⟩ := (materialOnly_counterexample u hu).2.2.1
  refine ⟨op, om, hne, ?_, ?_⟩
  · rw [pareto_rel_iff]
    refine ⟨hs.1, ?_⟩
    change traceTemperedValue (fun _ : O => 0) 1 _ _ ≥
      traceTemperedValue (fun _ : O => 0) 1 _ _
    simp [traceTemperedValue, materialRelevanceBetterPrior, materialRelevanceWorsePrior]
  · intro hr
    exact hs.2 ((pareto_rel_iff u _ _ _).mp hr).1

theorem pareto_a4 [Nonempty O] (u : O → ℝ) : A4_TraceRelevance (paretoFamily u) := by
  obtain ⟨o, hs⟩ := (informationOnly_counterexample (O := O)).2.2.2.1
  refine ⟨o, ?_, ?_⟩
  · rw [pareto_rel_iff]
    refine ⟨?_, hs.1⟩
    change traceTemperedValue u 0 _ _ ≥ traceTemperedValue u 0 _ _
    simp [traceTemperedValue, expectedPayoffUtility_traceBenchmark]
  · intro hr
    exact hs.2 ((pareto_rel_iff u _ _ _).mp hr).2

theorem pareto_a6 (u : O → ℝ) : A6_RecordDataProcessing (paretoFamily u) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [pareto_pairWeak_iff]
  exact ⟨traceScoreFamily_a6 u 0 (by norm_num) K T q,
    traceScoreFamily_a6 (fun _ : O => 0) 1 (by norm_num) K T q⟩

theorem pareto_a7 (u : O → ℝ) : A7_ActionDataProcessing (paretoFamily u) := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
  rw [pareto_pairWeak_iff]
  exact ⟨traceScoreFamily_a7 u 0 (by norm_num) K q S Kh hc,
    traceScoreFamily_a7 (fun _ : O => 0) 1 (by norm_num) K q S Kh hc⟩

theorem pareto_a8 (u : O → ℝ) : A8_RecordwiseSureThing (paretoFamily u) := by
  intro A R _ _ _ _ _ _ q P K L M hpos
  rw [pareto_pairWeak_iff, pareto_pairWeak_iff,
    traceScoreFamily_a8 u 0 (by norm_num) q P K L M hpos,
    traceScoreFamily_a8 (fun _ : O => 0) 1 (by norm_num) q P K L M hpos]

theorem pareto_not_a1 (u : O → ℝ) (op om : O) (hu : u om < u op) :
    ¬ A1_WeakOrder (paretoFamily u) := by
  intro h1
  let q : Dist PUnit := Dist.pure PUnit.unit
  let p : Dist RelevanceBit.{u} := Dist.uniform
  let K := deterministicPayoffChannel op
  let L := fullRevealAtPayoff (A := RelevanceBit.{u}) om
  have hI : 0 < mutualInfo p L := by
    rw [mutualInfo_fullRevealAtPayoff]
    exact entropy_pos_of_fullSupport_nontrivial p Dist.uniform_fullSupport
  rcases (h1 (commonPayoffBlockChannel K L)).1
      (leftBlockDist q) (rightBlockDist p) with h | h
  · have hh := (coordinateFamily_pairWeak u _ q K p L).mp h
    have hz : mutualInfo q K = 0 := mutualInfo_pure _ _
    exact (not_le_of_gt hI) (hz ▸ hh.2)
  · have hh := h.1
    change expectedPayoffUtility u (leftBlockDist q) (commonPayoffBlockChannel K L) ≤
      expectedPayoffUtility u (rightBlockDist p) (commonPayoffBlockChannel K L) at hh
    rw [expectedPayoffUtility_commonBlock_left,
      expectedPayoffUtility_commonBlock_right] at hh
    have hK : expectedPayoffUtility u q K = u op :=
      expectedPayoffUtility_uninformativeAtPayoff u q op
    have hL : expectedPayoffUtility u p L = u om :=
      expectedPayoffUtility_fullRevealAtPayoff u p om
    exact (not_le_of_gt hu) (by simpa [hK, hL] using hh)

/-- Completeness is independent even though every other exact axiom holds. -/
theorem pareto_counterexample [Nonempty O] (u : O → ℝ)
    (op om : O) (hu : u om < u op) :
    ¬ A1_WeakOrder (paretoFamily u) ∧ A2_Continuity (paretoFamily u) ∧
    A3_MaterialRelevance (paretoFamily u) ∧ A4_TraceRelevance (paretoFamily u) ∧
    A5_BlockComparisonCoherence (paretoFamily u) ∧
    A6_RecordDataProcessing (paretoFamily u) ∧ A7_ActionDataProcessing (paretoFamily u) ∧
    A8_RecordwiseSureThing (paretoFamily u) := by
  have hnc : ¬ IsConstantPayoffIndex u := by
    rintro ⟨c, hc⟩
    simpa [hc op, hc om] using hu
  exact ⟨pareto_not_a1 u op om hu, pareto_a2 u, pareto_a3 u hnc, pareto_a4 u,
    coordinateFamily_a5 u _, pareto_a6 u, pareto_a7 u, pareto_a8 u⟩

end TraceableAgency.Section3.Independence
