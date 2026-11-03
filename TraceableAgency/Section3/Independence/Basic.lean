import TraceableAgency.Theorem1.Benchmark

/-! Shared numerical infrastructure for exact axiom-independence witnesses. -/

namespace TraceableAgency.Section3.Independence

set_option linter.unusedSectionVars false

open TraceableAgency TraceableAgency.Theorem1 Filter Topology

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

/-- A numerical index on the same finite experiments as the primitive family. -/
abbrev ExperimentScore (O : Type u) [Fintype O] :=
  ∀ {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R],
    Dist A → Channel A (O × R) → ℝ

/-- The preference family induced by a scalar score. -/
def scoreFamily (v : ExperimentScore O) : FixedPayoffPrefFamily O where
  rel K q p := v q K ≥ v p K

theorem scoreFamily_a1 (v : ExperimentScore O) : A1_WeakOrder (scoreFamily v) := by
  intro A R _ _ _ _ _ _ K
  constructor
  · intro q p
    exact le_total _ _
  · intro q p r hqp hpr
    exact hpr.trans hqp

def ScoreContinuous (v : ExperimentScore O) : Prop :=
  ∀ {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (Kn : ℕ → Channel A (O × R)) (K : Channel A (O × R))
    (qn : ℕ → Dist A) (q : Dist A),
    ChannelConverges Kn K → DistConverges qn q →
    Tendsto (fun n => v (qn n) (Kn n)) atTop (𝓝 (v q K))

theorem scoreFamily_a2 (v : ExperimentScore O) (hv : ScoreContinuous v) :
    A2_Continuity (scoreFamily v) := by
  intro A R _ _ _ _ _ _ Kn K qn pn q p hK hq hp hn
  exact le_of_tendsto_of_tendsto (hv Kn K pn p hK hp)
    (hv Kn K qn q hK hq) (Filter.Eventually.of_forall hn)

/-- A family induced by any comparison of expected payoff and information. -/
def coordinateFamily (u : O → ℝ) (r : ℝ × ℝ → ℝ × ℝ → Prop) :
    FixedPayoffPrefFamily O where
  rel K q p := r (expectedPayoffUtility u q K, mutualInfo q K)
    (expectedPayoffUtility u p K, mutualInfo p K)

theorem coordinateFamily_pairWeak (u : O → ℝ) (r : ℝ × ℝ → ℝ × ℝ → Prop)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (coordinateFamily u r) q K p L ↔
      r (expectedPayoffUtility u q K, mutualInfo q K)
        (expectedPayoffUtility u p L, mutualInfo p L) := by
  unfold pairWeak coordinateFamily
  simp only [expectedPayoffUtility_commonBlock_left,
    expectedPayoffUtility_commonBlock_right,
    mutualInfo_commonBlock_left, mutualInfo_commonBlock_right]

theorem coordinateFamily_a5 (u : O → ℝ) (r : ℝ × ℝ → ℝ × ℝ → Prop) :
    A5_BlockComparisonCoherence (coordinateFamily u r) := by
  constructor
  · intro A R _ _ _ _ _ _ K q p
    rw [coordinateFamily_pairWeak]
    rfl
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    rw [coordinateFamily_pairWeak]
    change r _ _ ↔ r _ _
    simp only [expectedPayoffUtility_commonBlockFamily_embed,
      mutualInfo_commonBlockFamily_embed]

noncomputable def traceScoreFamily (u : O → ℝ) (lambda : ℝ) : FixedPayoffPrefFamily O :=
  scoreFamily (fun q K => traceTemperedValue u lambda q K)

theorem traceScoreFamily_rep (u : O → ℝ) (lambda : ℝ) :
    WithinChannelRepresentation (traceScoreFamily u lambda) u lambda := by
  intro A R _ _ _ _ _ _ K q p
  rfl

theorem traceScoreFamily_a6 (u : O → ℝ) (lambda : ℝ) (hl : 0 ≤ lambda) :
    A6_RecordDataProcessing (traceScoreFamily u lambda) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [pairWeak_iff_value_ge (traceScoreFamily_rep u lambda)]
  unfold traceTemperedValue
  rw [expectedPayoffUtility_recordPostprocess]
  simpa [recordPostprocess, add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_left
      (mutualInfo_outcome_postprocess_le q K (payoffPreservingRecordKernel T)) hl)
    (expectedPayoffUtility u q K)

theorem traceScoreFamily_a7 (u : O → ℝ) (lambda : ℝ) (hl : 0 ≤ lambda) :
    A7_ActionDataProcessing (traceScoreFamily u lambda) := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Khat hc
  rw [pairWeak_iff_value_ge (traceScoreFamily_rep u lambda)]
  unfold traceTemperedValue
  rw [expectedPayoffUtility_actionProcessor u K q S Khat hc]
  simpa [add_comm] using add_le_add_left
    (mul_le_mul_of_nonneg_left (mutualInfo_action_bayes_pushforward_le K q S Khat
      (bayesCompletion_of_actionProcessorCompletion K q S Khat hc)) hl)
    (expectedPayoffUtility u q K)

theorem traceScoreFamily_a8 (u : O → ℝ) (lambda : ℝ) (hl : 0 ≤ lambda) :
    A8_RecordwiseSureThing (traceScoreFamily u lambda) := by
  exact recordwiseSureThing_of_finiteBranchContinuationConsistency _
    (a1_weakOrder_of_representation (traceScoreFamily_rep u lambda))
    (a5_blockCoherence_of_representation (traceScoreFamily_rep u lambda))
    (traceScoreFamily_a6 u lambda hl)
    (traceScoreFamily_a7 u lambda hl)
    (finiteBranchContinuationConsistency_of_representation (traceScoreFamily_rep u lambda))

@[simp] theorem expectedPayoffUtility_zero
    {A R : Type u} [Fintype A] [Fintype R]
    (q : Dist A) (K : Channel A (O × R)) :
    expectedPayoffUtility (fun _ : O => 0) q K = 0 := by
  simp [expectedPayoffUtility]

@[simp] theorem expectedPayoffUtility_pure
    {A R : Type u} [Fintype A] [DecidableEq A] [Fintype R]
    (u : O → ℝ) (a : A) (K : Channel A (O × R)) :
    expectedPayoffUtility u (Dist.pure a) K = ∑ z, K a z * u z.1 := by
  simp [expectedPayoffUtility, Dist.pure_apply]

@[simp] theorem mutualInfo_pure
    {A X : Type u} [Fintype A] [DecidableEq A] [Fintype X]
    (a : A) (K : Channel A X) : mutualInfo (Dist.pure a) K = 0 := by
  have hm : Channel.outcomeMarginal K (Dist.pure a) = K a := by
    ext x
    simp [Channel.outcomeMarginal_apply, Dist.pure_apply]
  simp [mutualInfo, hm, Dist.pure_apply]

theorem expectedPayoffUtility_mix
    {A R : Type u} [Fintype A] [Fintype R]
    (u : O → ℝ) (q p : Dist A) (K : Channel A (O × R))
    (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    expectedPayoffUtility u (Dist.mix t ht ht' q p) K =
      t * expectedPayoffUtility u q K + (1 - t) * expectedPayoffUtility u p K := by
  simp only [expectedPayoffUtility, Dist.mix_apply, add_mul,
    Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]

@[simp] theorem expectedPayoffUtility_material_better (u : O → ℝ) (op om : O) :
    expectedPayoffUtility u materialRelevanceBetterPrior
      (materialRelevanceBenchmarkChannel op om) = u op := by
  simp [materialRelevanceBetterPrior, expectedPayoffUtility_pure,
    materialRelevanceBenchmarkChannel, Dist.pure_apply]

@[simp] theorem expectedPayoffUtility_material_worse (u : O → ℝ) (op om : O) :
    expectedPayoffUtility u materialRelevanceWorsePrior
      (materialRelevanceBenchmarkChannel op om) = u om := by
  simp [materialRelevanceWorsePrior, expectedPayoffUtility_pure,
    materialRelevanceBenchmarkChannel, Dist.pure_apply]

end TraceableAgency.Section3.Independence
