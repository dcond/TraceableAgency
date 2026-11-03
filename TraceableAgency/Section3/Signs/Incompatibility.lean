import TraceableAgency.Section3.Signs.Reverse

/-! Positive trace relevance is inconsistent with the negative record
orientation, for either weak action orientation (hence also neutrality).
Only A1 and A5 from the background are needed. -/
namespace TraceableAgency.Theorem1.Section3
open TraceableAgency
universe u
variable {O : Type u} [Fintype O] [DecidableEq O]

theorem fullReveal_redraw_fair (o : O) :
    recordPostprocess (fullRevealAtPayoff (A := RelevanceBit.{u}) o)
      (redrawRecordProcessor traceRelevanceFairPrior) =
      fairIndependentAtPayoff (A := RelevanceBit.{u}) o := by
  rw [recordPostprocess_fullReveal_redraw]
  rfl

theorem positive_trace_incompatible_negative_record
    (F : FixedPayoffPrefFamily O) (h1 : A1_WeakOrder F)
    (h5 : A5_BlockComparisonCoherence F) (h4 : A4_TraceRelevance F)
    (h6 : NegativeRecordProcessing F)
    (h7 : A7_ActionDataProcessing F ∨ NegativeActionProcessing F) : False := by
  obtain ⟨o, hs⟩ := h4
  let K := traceRelevanceBenchmarkChannel o
  have hmid := h6 (fullRevealAtPayoff (A := RelevanceBit) o)
    (redrawRecordProcessor traceRelevanceFairPrior) traceRelevanceFairPrior
  rw [fullReveal_redraw_fair] at hmid
  have hleft : pairWeak F traceRelevanceUnrevealingPrior K traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) o) := by
    rcases h7 with hp | hn
    · have hh := hp K traceRelevanceUnrevealingPrior traceSideProjectionProcessor
        (fairIndependentAtPayoff (A := RelevanceBit) o)
        (traceSideProjectionRight_isActionProcessorCompletion o)
      simpa only [actionPushforward_traceSideProjection_right] using hh
    · have hh := hn (fairIndependentAtPayoff (A := RelevanceBit) o)
        traceRelevanceFairPrior traceRightInclusionProcessor K
        (traceRightInclusion_isActionProcessorCompletion o)
      simpa only [actionPushforward_traceRightInclusion] using hh
  have hright : pairWeak F traceRelevanceFairPrior
      (fullRevealAtPayoff (A := RelevanceBit) o) traceRelevanceRevealingPrior K := by
    rcases h7 with hp | hn
    · have hh := hp (fullRevealAtPayoff o) traceRelevanceFairPrior
        traceLeftInclusionProcessor K (traceLeftInclusion_isActionProcessorCompletion o)
      simpa only [actionPushforward_traceLeftInclusion] using hh
    · have hh := hn K traceRelevanceRevealingPrior traceSideProjectionProcessor
        (fullRevealAtPayoff o) (traceSideProjectionLeft_isActionProcessorCompletion o)
      simpa only [actionPushforward_traceSideProjection_left] using hh
  have hreverse := pairWeak_transitive_of_structural F h1 h5 _ _ _ _ _ _
    (pairWeak_transitive_of_structural F h1 h5 _ _ _ _ _ _ hleft hmid) hright
  exact hs.2 ((h5.duplication K traceRelevanceUnrevealingPrior
    traceRelevanceRevealingPrior).mpr hreverse)

end TraceableAgency.Theorem1.Section3
