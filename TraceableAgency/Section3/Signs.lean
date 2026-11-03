import TraceableAgency.Section3.Signs.Negative
import TraceableAgency.Section3.Signs.Neutral
import TraceableAgency.Section3.Signs.Incompatibility

/-! Section 3 sign trichotomy in the paper's primitive comparison language. -/
namespace TraceableAgency.Theorem1.Section3
open TraceableAgency
universe u
variable {O : Type u} [Fintype O] [DecidableEq O]

def IndifferentRecordProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (K : Channel A (O × R)) (T : RecordProcessor O R S) (q : TraceableAgency.Dist A),
    pairIndiff F q K q (recordPostprocess K T)

def IndifferentActionProcessing
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop :=
  ∀ {A B R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R)),
    IsActionProcessorCompletion K q S Khat →
    pairIndiff F q K (Channel.actionPushforward q S) Khat

theorem neutral_processing_of_indifferent (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : IndifferentRecordProcessing F) (h7 : IndifferentActionProcessing F) :
    NeutralRecordProcessing F ∧ NeutralActionProcessing F := by
  have hf6 : A6_RecordDataProcessing F := by
    intro A R S _ _ _ _ _ _ _ _ _ K T q
    exact (h6 K T q).1
  have hf7 : A7_ActionDataProcessing F := by
    intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
    exact (h7 K q S Kh hc).1
  refine ⟨⟨hf6, ?_⟩, ⟨hf7, ?_⟩⟩
  · intro A R S _ _ _ _ _ _ _ _ _ K T q
    exact (sameBlock_reverse_iff_pairWeak_swap F h1 h5 hf6 hf7
      q K q (recordPostprocess K T)).mp (h6 K T q).2
  · intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
    exact (sameBlock_reverse_iff_pairWeak_swap F h1 h5 hf6 hf7
      q K (Channel.actionPushforward q S) Kh).mp (h7 K q S Kh hc).2

theorem indifferent_processing_of_neutral (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : NeutralRecordProcessing F) (h7 : NeutralActionProcessing F) :
    IndifferentRecordProcessing F ∧ IndifferentActionProcessing F := by
  constructor
  · intro A R S _ _ _ _ _ _ _ _ _ K T q
    exact ⟨h6.1 K T q,
      (sameBlock_reverse_iff_pairWeak_swap F h1 h5 h6.1 h7.1
        q K q (recordPostprocess K T)).mpr (h6.2 K T q)⟩
  · intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
    exact ⟨h7.1 K q S Kh hc,
      (sameBlock_reverse_iff_pairWeak_swap F h1 h5 h6.1 h7.1
        q K (Channel.actionPushforward q S) Kh).mpr (h7.2 K q S Kh hc)⟩

theorem positive_representation (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h4 : A4_TraceRelevance F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F) :
    ∃ (v : O → ℝ) (c : ℝ), ¬ IsConstantPayoffIndex v ∧ 0 < c ∧
      WithinChannelRepresentation F v c ∧ SameWitnessBlockRepresentation F v c :=
  (MaterialCalibration.theorem1V10Clauses_material F).2
    ⟨h.a1, h.a2, h.a3, h4, h.a5, h6, h7, h.a8⟩

/-- The three clauses of v11 Corollary 3 share exactly A1--A3, A5, A8.
Every clause includes one common pair of witnesses for finite-block orders. -/
theorem sign_trichotomy (F : FixedPayoffPrefFamily O) (h : SignBackground F) :
    (A4_TraceRelevance F → A6_RecordDataProcessing F → A7_ActionDataProcessing F →
      ∃ (v : O → ℝ) (c : ℝ), ¬ IsConstantPayoffIndex v ∧ 0 < c ∧
        WithinChannelRepresentation F v c ∧ SameWitnessBlockRepresentation F v c) ∧
    (NegativeTraceRelevance F → NegativeRecordProcessing F → NegativeActionProcessing F →
      ∃ (v : O → ℝ) (c : ℝ), ¬ IsConstantPayoffIndex v ∧ c < 0 ∧
        WithinChannelRepresentation F v c ∧ SameWitnessBlockRepresentation F v c) ∧
    (NeutralTraceRelevance F → IndifferentRecordProcessing F → IndifferentActionProcessing F →
      ∃ v : O → ℝ, ¬ IsConstantPayoffIndex v ∧
        WithinChannelRepresentation F v 0 ∧ SameWitnessBlockRepresentation F v 0) := by
  refine ⟨positive_representation F h, negative_representation F h, ?_⟩
  intro _h4 h6 h7
  obtain ⟨h6', h7'⟩ := neutral_processing_of_indifferent F h.a1 h.a5 h6 h7
  exact neutral_representation F h h6' h7'

end TraceableAgency.Theorem1.Section3
