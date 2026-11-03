import TraceableAgency.Section3.Independence.GiniExamples
import TraceableAgency.Section3.Independence.GiniRegularity

/-! # The paper's Gini counterexample, with all seven retained axioms -/

namespace TraceableAgency.Section3.Independence

open TraceableAgency Theorem1

universe u

variable {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]

theorem gini_counterexample (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) :
    A1_WeakOrder (giniFamily v) ∧ A2_Continuity (giniFamily v) ∧
    A3_MaterialRelevance (giniFamily v) ∧ A4_TraceRelevance (giniFamily v) ∧
    A5_BlockComparisonCoherence (giniFamily v) ∧
    A6_RecordDataProcessing (giniFamily v) ∧ ¬ A7_ActionDataProcessing (giniFamily v) ∧
    A8_RecordwiseSureThing (giniFamily v) := by
  exact ⟨scoreFamily_a1 _, giniFamily_a2 v, giniFamily_a3 v hv,
    giniFamily_a4 v, giniFamily_a5 v, giniFamily_a6 v,
    giniFamily_not_a7 v, giniFamily_a8 v⟩

end TraceableAgency.Section3.Independence
