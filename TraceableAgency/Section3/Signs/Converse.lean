import TraceableAgency.Section3.Signs
import TraceableAgency.Section3.Independence.Relevance

/-! Numerical converses for all signs.  The A8 difference is a positive
branch mass times the local difference, independently of the sign of λ. -/
namespace TraceableAgency.Theorem1.Section3
open TraceableAgency TraceableAgency.Section3.Independence
universe u
variable {O : Type u} [Fintype O] [DecidableEq O]

theorem signed_a3_of_representation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {c : ℝ}
    (hv : ¬ IsConstantPayoffIndex v) (hr : WithinChannelRepresentation F v c) :
    A3_MaterialRelevance F := by
  obtain ⟨op, om, hs⟩ := materialRelevanceEnvironment_of_representation hv hr
  have hvlt : v om < v op := by
    simpa only [traceTemperedValue_deterministicPayoffChannel] using
      (pairStrict_iff_value_gt hr _ _ _ _).mp hs
  refine ⟨op, om, ?_, ?_, ?_⟩
  · intro he
    subst om
    exact (lt_irrefl _ hvlt)
  · apply (hr _ _ _).mpr
    simpa [traceTemperedValue, materialRelevanceBetterPrior,
      materialRelevanceWorsePrior, materialRelevanceBenchmarkChannel, Dist.pure_apply] using hvlt.le
  · intro hn
    have hh := (hr _ _ _).mp hn
    have hh' : v op ≤ v om := by
      simpa [traceTemperedValue, materialRelevanceBetterPrior,
        materialRelevanceWorsePrior, materialRelevanceBenchmarkChannel, Dist.pure_apply] using hh
    exact (not_le_of_gt hvlt) hh'

theorem signed_a8_of_representation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {c : ℝ}
    (hr : WithinChannelRepresentation F v c) : A8_RecordwiseSureThing F := by
  intro A R _ _ _ _ _ _ q P K L M hp
  rw [pairWeak_iff_value_ge hr, pairWeak_iff_value_ge hr]
  simp only [binaryPayoffCompound, traceTemperedValue_commonCompound]
  have hsum (f : RelevanceBit.{u} → ℝ) :
      (∑ b, f b) = f (ULift.up false) + f (ULift.up true) := by
    rw [← (Equiv.ulift (α := Bool)).symm.sum_comp f]
    simp [Fintype.sum_bool, Equiv.ulift, add_comm]
  simp only [hsum, binaryContinuationProfile, ULift.down_up, Bool.false_eq_true,
    Bool.true_eq, if_false, if_true]
  change 0 < (Channel.outcomeMarginal P q) (ULift.up true) at hp
  constructor <;> intro hh <;> nlinarith

theorem signed_background_of_representation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {c : ℝ}
    (hv : ¬ IsConstantPayoffIndex v) (hr : WithinChannelRepresentation F v c) :
    SignBackground F :=
  ⟨a1_weakOrder_of_representation hr, a2_continuity_of_representation hr,
    signed_a3_of_representation hv hr, a5_blockCoherence_of_representation hr,
    signed_a8_of_representation hr⟩

theorem nonpositive_recordProcessing_of_representation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {c : ℝ}
    (hc : c ≤ 0) (hr : WithinChannelRepresentation F v c) :
    NegativeRecordProcessing F := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [pairWeak_iff_value_ge hr]
  unfold traceTemperedValue
  rw [expectedPayoffUtility_recordPostprocess]
  have hh := mul_le_mul_of_nonpos_left
    (mutualInfo_outcome_postprocess_le q K (payoffPreservingRecordKernel T)) hc
  simpa only [add_comm, recordPostprocess] using
    (add_le_add_left hh (expectedPayoffUtility v q K))

theorem nonpositive_actionProcessing_of_representation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {c : ℝ}
    (hc : c ≤ 0) (hr : WithinChannelRepresentation F v c) :
    NegativeActionProcessing F := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hcompletion
  rw [pairWeak_iff_value_ge hr]
  unfold traceTemperedValue
  rw [expectedPayoffUtility_actionProcessor v K q S Kh hcompletion]
  have hh := mul_le_mul_of_nonpos_left
    (mutualInfo_action_bayes_pushforward_le K q S Kh
      (bayesCompletion_of_actionProcessorCompletion K q S Kh hcompletion)) hc
  simpa only [add_comm, recordPostprocess] using
    (add_le_add_left hh (expectedPayoffUtility v q K))

theorem negative_axioms_of_representation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {c : ℝ}
    (hv : ¬ IsConstantPayoffIndex v) (hc : c < 0)
    (hr : WithinChannelRepresentation F v c) :
    SignBackground F ∧ NegativeTraceRelevance F ∧
      NegativeRecordProcessing F ∧ NegativeActionProcessing F := by
  have hneg : ¬ IsConstantPayoffIndex (fun o => -v o) := by
    rintro ⟨k, hk⟩
    apply hv
    refine ⟨-k, fun o => ?_⟩
    have hh := hk o
    linarith
  have hrev : WithinChannelRepresentation (reverseFamily F) (fun o => -v o) (-c) := by
    intro A R _ _ _ _ _ _ K q p
    simpa only [reverseFamily_rel, traceTemperedValue_neg, neg_le_neg_iff] using hr K p q
  have ha := traceTemperedAxiomsV10_of_representation hneg (neg_pos.mpr hc) hrev
  exact ⟨signed_background_of_representation hv hr, ha.a4,
    nonpositive_recordProcessing_of_representation hc.le hr,
    nonpositive_actionProcessing_of_representation hc.le hr⟩

theorem neutral_axioms_of_representation
    {F : FixedPayoffPrefFamily O} {v : O → ℝ}
    (hv : ¬ IsConstantPayoffIndex v) (hr : WithinChannelRepresentation F v 0) :
    SignBackground F ∧ NeutralTraceRelevance F ∧
      IndifferentRecordProcessing F ∧ IndifferentActionProcessing F := by
  have hbg := signed_background_of_representation hv hr
  have h6 : NeutralRecordProcessing F := by
    refine ⟨?_, nonpositive_recordProcessing_of_representation le_rfl hr⟩
    intro A R S _ _ _ _ _ _ _ _ _ K T q
    rw [pairWeak_iff_value_ge hr]
    simp [traceTemperedValue, expectedPayoffUtility_recordPostprocess]
  have h7 : NeutralActionProcessing F := by
    refine ⟨?_, nonpositive_actionProcessing_of_representation le_rfl hr⟩
    intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
    rw [pairWeak_iff_value_ge hr]
    simp [traceTemperedValue, expectedPayoffUtility_actionProcessor v K q S Kh hc]
  obtain ⟨o, _, _⟩ := materialRelevanceEnvironment_of_representation hv hr
  have h4 : NeutralTraceRelevance F := by
    refine ⟨o, ?_, ?_⟩ <;> apply (hr _ _ _).mpr <;>
      simp [traceTemperedValue, expectedPayoffUtility_traceBenchmark]
  have hh := indifferent_processing_of_neutral F hbg.a1 hbg.a5 h6 h7
  exact ⟨hbg, h4, hh.1, hh.2⟩

end TraceableAgency.Theorem1.Section3
