import TraceableAgency.Section3.Independence.Basic
import TraceableAgency.Section3.UniquenessMixture

/-! # Independence of A8: a satiating value of information -/

namespace TraceableAgency.Section3.Independence

open TraceableAgency Theorem1 Section3 Filter Topology

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

noncomputable def satiationFamily (v : O → ℝ) (c : ℝ) : FixedPayoffPrefFamily O :=
  scoreFamily (fun q K => expectedPayoffUtility v q K + min (mutualInfo q K) c)

 theorem satiation_pairWeak (v : O → ℝ) (c : ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (satiationFamily v c) q K p L ↔
      expectedPayoffUtility v q K + min (mutualInfo q K) c ≥
        expectedPayoffUtility v p L + min (mutualInfo p L) c :=
  coordinateFamily_pairWeak v (fun x y => x.1 + min x.2 c ≥ y.1 + min y.2 c) q K p L

 theorem satiation_pairStrict (v : O → ℝ) (c : ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairStrict (satiationFamily v c) q K p L ↔
      expectedPayoffUtility v q K + min (mutualInfo q K) c >
        expectedPayoffUtility v p L + min (mutualInfo p L) c := by
  unfold pairStrict satiationFamily scoreFamily
  simp only [expectedPayoffUtility_commonBlock_left, expectedPayoffUtility_commonBlock_right,
    mutualInfo_commonBlock_left, mutualInfo_commonBlock_right, not_le]
  exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

 theorem satiation_a1 (v : O → ℝ) (c : ℝ) : A1_WeakOrder (satiationFamily v c) :=
  scoreFamily_a1 _

 theorem satiation_a2 (v : O → ℝ) (c : ℝ) : A2_Continuity (satiationFamily v c) := by
  apply scoreFamily_a2
  intro A R _ _ _ _ _ _ Kn K qn q hK hq
  exact (tendsto_expectedPayoffUtility_of_converges v Kn K qn q hK hq).add
    ((tendsto_mutualInfo_of_converges' Kn K qn q hK hq).min tendsto_const_nhds)

 theorem satiation_a3 (v : O → ℝ) (c : ℝ) (hv : ¬ IsConstantPayoffIndex v) :
    A3_MaterialRelevance (satiationFamily v c) := by
  obtain ⟨op, om, hne, hstrict⟩ :=
    (traceTemperedAxiomsV10_of_representation hv (by norm_num : (0:ℝ)<1)
      (traceScoreFamily_rep v 1)).a3
  refine ⟨op, om, hne, ?_⟩
  simp only [FixedPayoffPrefFamily.strictRel, traceScoreFamily, scoreFamily,
    traceTemperedValue, materialRelevanceBetterPrior, materialRelevanceWorsePrior,
    mutualInfo_pure, mul_zero, add_zero] at hstrict
  simpa only [FixedPayoffPrefFamily.strictRel, satiationFamily, scoreFamily,
    materialRelevanceBetterPrior, materialRelevanceWorsePrior, mutualInfo_pure,
    ge_iff_le, add_le_add_iff_right] using hstrict

 theorem satiation_a5 (v : O → ℝ) (c : ℝ) :
    A5_BlockComparisonCoherence (satiationFamily v c) :=
  coordinateFamily_a5 v (fun x y => x.1 + min x.2 c ≥ y.1 + min y.2 c)

 theorem satiation_a6 (v : O → ℝ) (c : ℝ) :
    A6_RecordDataProcessing (satiationFamily v c) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [satiation_pairWeak, expectedPayoffUtility_recordPostprocess]
  have h := min_le_min_right c (mutualInfo_outcome_postprocess_le q K (payoffPreservingRecordKernel T))
  change min (mutualInfo q (recordPostprocess K T)) c ≤ min (mutualInfo q K) c at h
  linarith

 theorem satiation_a7 (v : O → ℝ) (c : ℝ) :
    A7_ActionDataProcessing (satiationFamily v c) := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Khat hc
  rw [satiation_pairWeak, expectedPayoffUtility_actionProcessor v K q S Khat hc]
  have h := min_le_min_right c (mutualInfo_action_bayes_pushforward_le K q S Khat
    (bayesCompletion_of_actionProcessorCompletion K q S Khat hc))
  linarith

 theorem satiation_a4 [Nonempty O] (v : O → ℝ) {c : ℝ} (hc : 0 < c) :
    A4_TraceRelevance (satiationFamily v c) := by
  let o : O := Classical.choice ‹Nonempty O›
  apply positiveOrientationAt_implies_traceRelevance_fixed (satiationFamily v c)
    (satiation_a1 v c) (satiation_a5 v c) (satiation_a6 v c) (satiation_a7 v c) o
  intro A _ _ _ q hq
  rw [satiation_pairStrict, expectedPayoffUtility_fullRevealAtPayoff,
    expectedPayoffUtility_uninformativeAtPayoff, mutualInfo_fullRevealAtPayoff,
    mutualInfo_uninformativeAtPayoff, min_eq_left hc.le]
  have h := lt_min (entropy_pos_of_fullSupport_nontrivial q hq) hc
  linarith

/-- A public fair coin changes no posterior on actions. -/
 theorem fair_binary_compound_values
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (v : O → ℝ) (q : Dist A) (K M : Channel A (O × R)) :
    let P : Channel A RelevanceBit := fun _ => publicCoin (1/2) (by norm_num) (by norm_num)
    expectedPayoffUtility v q (binaryPayoffCompound P K M) =
      (1/2) * expectedPayoffUtility v q K + (1/2) * expectedPayoffUtility v q M ∧
    mutualInfo q (binaryPayoffCompound P K M) =
      (1/2) * mutualInfo q K + (1/2) * mutualInfo q M := by
  dsimp only
  let P : Channel A RelevanceBit := fun _ => publicCoin (1/2) (by norm_num) (by norm_num)
  have hm : Channel.outcomeMarginal P q = publicCoin (1/2) (by norm_num) (by norm_num) :=
    outcomeMarginal_constant q _
  have ht : branchPosterior P q (ULift.up true) = q :=
    posterior_constant_of_pos q _ _ (by norm_num)
  have hf : branchPosterior P q (ULift.up false) = q :=
    posterior_constant_of_pos q _ _ (by norm_num)
  constructor
  · change expectedPayoffUtility v q (binaryPayoffCompound P K M) = _
    rw [binaryPayoffCompound, expectedPayoffUtility_commonCompound, hm, sum_relevanceBit]
    norm_num [binaryContinuationProfile, ht, hf]
  · change mutualInfo q (binaryPayoffCompound P K M) = _
    rw [binaryPayoffCompound, mutualInfo_commonCompound, mutualInfo_constant, hm, sum_relevanceBit]
    norm_num [binaryContinuationProfile, ht, hf]

/-- Every positive cap violates A8. A sufficiently large uniform action
lottery has information greater than twice the cap. Adding revelation on the
other coin branch then makes silence and revelation tie ex ante. -/
 theorem satiation_not_a8 [Nonempty O] (v : O → ℝ) {c : ℝ} (hc : 0 < c) :
    ¬ A8_RecordwiseSureThing (satiationFamily v c) := by
  intro h8
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (2*c))
  have hnpos : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hnexp : Real.exp (2*c) < (n+1 : ℕ) := by
    exact_mod_cast lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
  have hlog : 2*c < Real.log (n+1 : ℕ) := (Real.lt_log_iff_exp_lt hnpos).2 hnexp
  let A := ULift.{u} (Fin (n+1))
  let q : Dist A := Dist.uniform
  have hH : 2*c < entropy q := by
    simpa [q, A, entropy_uniform_eq_log_card] using hlog
  let o : O := Classical.choice ‹Nonempty O›
  let r : A := Classical.choice (inferInstance : Nonempty A)
  let S : Channel A (O × A) := silentChannel o r
  let R : Channel A (O × A) := fullRevealAtPayoff o
  let P : Channel A RelevanceBit := fun _ => publicCoin (1/2) (by norm_num) (by norm_num)
  have hp : branchPosterior P q (ULift.up true) = q :=
    posterior_constant_of_pos q _ _ (by norm_num)
  have hy : BranchPositive P q (ULift.up true) := by
    change 0 < Channel.outcomeMarginal P q (ULift.up true)
    rw [outcomeMarginal_constant]
    norm_num
  have hSmat : expectedPayoffUtility v q S = v o := by
    have h := value_silentChannel v 0 q o r
    simpa only [traceTemperedValue, zero_mul, add_zero] using h
  have hSmi : mutualInfo q S = 0 := mutualInfo_constant q _
  have hRmat : expectedPayoffUtility v q R = v o := expectedPayoffUtility_fullRevealAtPayoff v q o
  have hRmi : mutualInfo q R = entropy q := mutualInfo_fullRevealAtPayoff q o
  have hSR := fair_binary_compound_values v q S R
  have hRR := fair_binary_compound_values v q R R
  change expectedPayoffUtility v q (binaryPayoffCompound P S R) = _ ∧
    mutualInfo q (binaryPayoffCompound P S R) = _ at hSR
  change expectedPayoffUtility v q (binaryPayoffCompound P R R) = _ ∧
    mutualInfo q (binaryPayoffCompound P R R) = _ at hRR
  rw [hSmat, hRmat, hSmi, hRmi] at hSR
  rw [hRmat, hRmi] at hRR
  have hcH : c ≤ entropy q := by linarith
  have hcHalf : c ≤ (1/2:ℝ) * 0 + (1/2:ℝ) * entropy q := by linarith
  have hcFull : c ≤ (1/2:ℝ) * entropy q + (1/2:ℝ) * entropy q := by linarith
  have hexante : pairWeak (satiationFamily v c) q (binaryPayoffCompound P S R)
      q (binaryPayoffCompound P R R) := by
    rw [satiation_pairWeak, hSR.1, hRR.1, hSR.2, hRR.2,
      min_eq_right hcHalf, min_eq_right hcFull]
  have hlocal := (h8 q P S R R hy).mpr hexante
  rw [satiation_pairWeak, hp, hSmat, hRmat, hSmi, hRmi,
    min_eq_left hc.le, min_eq_right hcH] at hlocal
  linarith

 theorem satiation_counterexample [Nonempty O] (v : O → ℝ)
    (hv : ¬ IsConstantPayoffIndex v) {c : ℝ} (hc : 0 < c) :
    let F := satiationFamily v c
    A1_WeakOrder F ∧ A2_Continuity F ∧ A3_MaterialRelevance F ∧ A4_TraceRelevance F ∧
    A5_BlockComparisonCoherence F ∧ A6_RecordDataProcessing F ∧
    A7_ActionDataProcessing F ∧ ¬ A8_RecordwiseSureThing F :=
  ⟨satiation_a1 v c, satiation_a2 v c, satiation_a3 v c hv, satiation_a4 v hc,
    satiation_a5 v c, satiation_a6 v c, satiation_a7 v c, satiation_not_a8 v hc⟩

end TraceableAgency.Section3.Independence
