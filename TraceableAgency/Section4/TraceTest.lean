import TraceableAgency.Section3.Range
import TraceableAgency.Section3.UniquenessMixture
import TraceableAgency.Section3.Independence.RecordProcessing

/-! The two treatments of Proposition 5, including all signs and the two
channel-blind impossibility statements. All logarithms are natural. -/

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

abbrev TraceActions : Type u := RelevanceBit.{u} ⊕ RelevanceBit.{u}

noncomputable abbrev traceSecondTreatment (o : O) : Channel TraceActions.{u} (O × RelevanceBit.{u}) :=
  fairIndependentAtPayoff o

theorem trace_revealing_information (o : O) :
    mutualInfo traceRelevanceRevealingPrior.{u,u} (traceRelevanceBenchmarkChannel.{u,u,u} o) =
      Real.log 2 := by
  have hle := mutualInfo_action_bayes_pushforward_le
    (fullRevealAtPayoff o) traceRelevanceFairPrior.{u} traceLeftInclusionProcessor
    (traceRelevanceBenchmarkChannel.{u,u,u} o)
    (bayesCompletion_of_actionProcessorCompletion _ _ _ _
      (traceLeftInclusion_isActionProcessorCompletion o))
  have hge := mutualInfo_action_bayes_pushforward_le
    (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceRevealingPrior.{u,u} traceSideProjectionProcessor
    (fullRevealAtPayoff o)
    (bayesCompletion_of_actionProcessorCompletion _ _ _ _
      (traceSideProjectionLeft_isActionProcessorCompletion o))
  rw [actionPushforward_traceLeftInclusion, mutualInfo_fullRevealAtPayoff] at hle
  rw [actionPushforward_traceSideProjection_left, mutualInfo_fullRevealAtPayoff] at hge
  have he := le_antisymm hle hge
  simpa [traceRelevanceFairPrior, entropy_uniform_eq_log_card] using he

theorem trace_unrevealing_information (o : O) :
    mutualInfo traceRelevanceUnrevealingPrior.{u,u} (traceRelevanceBenchmarkChannel.{u,u,u} o) = 0 := by
  have hle := mutualInfo_action_bayes_pushforward_le
    (fairIndependentAtPayoff (A := RelevanceBit.{u}) o) traceRelevanceFairPrior.{u}
    traceRightInclusionProcessor (traceRelevanceBenchmarkChannel.{u,u,u} o)
    (bayesCompletion_of_actionProcessorCompletion _ _ _ _
      (traceRightInclusion_isActionProcessorCompletion o))
  rw [actionPushforward_traceRightInclusion] at hle
  have hz : mutualInfo traceRelevanceFairPrior.{u} (fairIndependentAtPayoff (A := RelevanceBit.{u}) o) = 0 :=
    mutualInfo_constant _ _
  rw [hz] at hle
  exact le_antisymm hle (sub_nonneg.mpr
    (sum_weighted_entropy_le_entropy_actionPushforward _ _))

theorem traceSecond_information (o : O) (q : Dist TraceActions.{u}) :
    mutualInfo q (traceSecondTreatment o) = 0 := mutualInfo_constant _ _

theorem expectedPayoff_fairIndependent
    {A : Type u} [Fintype A] (v : O → ℝ) (o : O) (q : Dist A) :
    expectedPayoffUtility v q (fairIndependentAtPayoff o) = v o := by
  rw [← recordPostprocess_uninformative_generateFair,
    expectedPayoffUtility_recordPostprocess, expectedPayoffUtility_uninformativeAtPayoff]

theorem trace_test_gap (v : O → ℝ) (lambda : ℝ) (o : O) :
    traceTemperedValue v lambda traceRelevanceRevealingPrior.{u,u} (traceRelevanceBenchmarkChannel.{u,u,u} o) -
      traceTemperedValue v lambda traceRelevanceUnrevealingPrior.{u,u} (traceRelevanceBenchmarkChannel.{u,u,u} o) =
      lambda * Real.log 2 := by
  unfold traceTemperedValue
  rw [Independence.expectedPayoffUtility_traceBenchmark,
    Independence.expectedPayoffUtility_traceBenchmark,
    trace_revealing_information, trace_unrevealing_information]
  ring

theorem traceSecond_value (v : O → ℝ) (lambda : ℝ) (o : O) (q : Dist TraceActions.{u}) :
    traceTemperedValue v lambda q (traceSecondTreatment o) = v o := by
  unfold traceTemperedValue
  rw [traceSecond_information, expectedPayoff_fairIndependent]
  ring

theorem trace_all_marginals (o : O) :
    Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceRevealingPrior.{u,u} =
        Channel.outcomeMarginal (traceSecondTreatment o) traceRelevanceRevealingPrior.{u,u} ∧
    Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceUnrevealingPrior.{u,u} =
        Channel.outcomeMarginal (traceSecondTreatment o) traceRelevanceUnrevealingPrior.{u,u} ∧
    Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceRevealingPrior.{u,u} =
        Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceUnrevealingPrior.{u,u} := by
  have hU : Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceUnrevealingPrior.{u,u} =
      Channel.outcomeMarginal (traceSecondTreatment o) traceRelevanceUnrevealingPrior.{u,u} := by
    ext z
    simp only [Channel.outcomeMarginal_apply, traceRelevanceUnrevealingPrior,
      Fintype.sum_sum_type, inrDist_apply_inl, inrDist_apply_inr,
      zero_mul, Finset.sum_const_zero, zero_add]
    rfl
  have hsecond : Channel.outcomeMarginal (traceSecondTreatment o) traceRelevanceRevealingPrior.{u,u} =
      Channel.outcomeMarginal (traceSecondTreatment o) traceRelevanceUnrevealingPrior.{u,u} := by
    unfold traceSecondTreatment fairIndependentAtPayoff
    rw [outcomeMarginal_constant, outcomeMarginal_constant]
  have hsame := Independence.traceBenchmark_same_output o
  exact ⟨hsame.trans (hU.trans hsecond.symm), hU, hsame⟩

theorem trace_test_orientation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F v lambda) (o : O) :
    (F.strictRel (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceRevealingPrior.{u,u} traceRelevanceUnrevealingPrior.{u,u} ↔ 0 < lambda) ∧
    (F.strictRel (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceUnrevealingPrior.{u,u} traceRelevanceRevealingPrior.{u,u} ↔ lambda < 0) ∧
    (F.indiffRel (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceRevealingPrior.{u,u} traceRelevanceUnrevealingPrior.{u,u} ↔ lambda = 0) ∧
    F.indiffRel (traceSecondTreatment o) traceRelevanceRevealingPrior.{u,u} traceRelevanceUnrevealingPrior.{u,u} := by
  have hgap := trace_test_gap v lambda o
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  simp only [FixedPayoffPrefFamily.strictRel, FixedPayoffPrefFamily.indiffRel]
  repeat' rw [hrep]
  rw [traceSecond_value, traceSecond_value]
  constructor
  · constructor
    · rintro ⟨_, hn⟩
      have : 0 < lambda * Real.log 2 := by linarith [lt_of_not_ge hn]
      exact (mul_pos_iff_of_pos_right hlog).mp this
    · intro hl
      have := mul_pos hl hlog
      exact ⟨by linarith, by linarith⟩
  constructor
  · constructor
    · rintro ⟨_, hn⟩
      have : lambda * Real.log 2 < 0 := by linarith [lt_of_not_ge hn]
      by_contra hn
      have hn0 : 0 ≤ lambda := le_of_not_gt hn
      linarith [mul_nonneg hn0 hlog.le]
    · intro hl
      have := mul_neg_of_neg_of_pos hl hlog
      exact ⟨by linarith, by linarith⟩
  constructor
  · constructor
    · rintro ⟨h1,h2⟩
      have hz : lambda * Real.log 2 = 0 := by linarith
      exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hlog)
    · rintro rfl
      constructor <;> linarith
  · exact ⟨le_rfl,le_rfl⟩

/-- A channel-blind numerical criterion cannot show the two-treatment pattern. -/
theorem channelBlind_cannot_pass_trace_test (o : O)
    (f : Dist (O × RelevanceBit.{u}) → Dist TraceActions.{u} → ℝ) :
    ¬ (f (Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceRevealingPrior.{u,u})
          traceRelevanceRevealingPrior.{u,u} >
        f (Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceUnrevealingPrior.{u,u})
          traceRelevanceUnrevealingPrior.{u,u} ∧
      f (Channel.outcomeMarginal (traceSecondTreatment o) traceRelevanceRevealingPrior.{u,u})
          traceRelevanceRevealingPrior.{u,u} =
        f (Channel.outcomeMarginal (traceSecondTreatment o) traceRelevanceUnrevealingPrior.{u,u})
          traceRelevanceUnrevealingPrior.{u,u}) := by
  rw [(trace_all_marginals o).1, (trace_all_marginals o).2.1]
  rintro ⟨hgt, heq⟩
  linarith

theorem trace_priors_permuted :
    Relabeling.relabelDist (Equiv.sumComm RelevanceBit.{u} RelevanceBit.{u})
      traceRelevanceRevealingPrior.{u,u} = traceRelevanceUnrevealingPrior.{u,u} := by
  ext a
  cases a <;> rfl

/-- Action-permutation invariance makes the first treatment alone decisive. -/
theorem permutationSymmetric_channelBlind_trace_tie (o : O)
    (f : Dist (O × RelevanceBit.{u}) → Dist TraceActions.{u} → ℝ)
    (hinv : ∀ m q (e : TraceActions.{u} ≃ TraceActions.{u}),
      f m (Relabeling.relabelDist e q) = f m q) :
    f (Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceRevealingPrior.{u,u})
        traceRelevanceRevealingPrior.{u,u} =
      f (Channel.outcomeMarginal (traceRelevanceBenchmarkChannel.{u,u,u} o) traceRelevanceUnrevealingPrior.{u,u})
        traceRelevanceUnrevealingPrior.{u,u} := by
  rw [(trace_all_marginals o).2.2, ← trace_priors_permuted]
  exact (hinv _ _ _).symm

end TraceableAgency.Section4
