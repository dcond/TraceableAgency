import TraceableAgency.Theorem1.SupportDummy
import TraceableAgency.Theorem1.FiniteBranchExtension

/-! # Appendix A structural statements with their stated hypotheses

These proofs use no relevance or continuity assumption. The bundle in the
older interfaces was only packaging; each axiom is explicit here.
-/
namespace TraceableAgency.Theorem1
open TraceableAgency
universe u

theorem pairWeak_ambient_to_support_v11
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h7 : A7_ActionDataProcessing F)
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A) :
    pairWeak F q K q.restrictToSupport (Channel.restrictToSupport K q) := by
  have hh := h7 K q (supportProjectKernel q)
    (Channel.restrictToSupport K q)
    (actionCompletion_isExact K q (supportProjectKernel q)
      (Channel.restrictToSupport K q)
      (restrictToSupport_isBayesPushforwardCompletion K q))
  simpa [actionPushforward_project] using hh

theorem pairWeak_support_to_ambient_v11
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h7 : A7_ActionDataProcessing F)
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A) :
    pairWeak F q.restrictToSupport (Channel.restrictToSupport K q) q K := by
  have hh := h7 (Channel.restrictToSupport K q) q.restrictToSupport
    (supportIncludeKernel q) K
    (actionCompletion_isExact (Channel.restrictToSupport K q) q.restrictToSupport
      (supportIncludeKernel q) K
      (ambient_isBayesPushforwardCompletion_of_restrict K q))
  simpa [actionPushforward_restrict_include] using hh


theorem pairWeak_iff_supportRestriction_v11
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h7 : A7_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      pairWeak F q.restrictToSupport (Channel.restrictToSupport K q)
        p.restrictToSupport (Channel.restrictToSupport L p) :=
  pairWeak_iff_of_pairwiseWeakEquiv F h1 h5
    K (Channel.restrictToSupport K q)
    L (Channel.restrictToSupport L p)
    q q.restrictToSupport p p.restrictToSupport
    (pairWeak_ambient_to_support_v11 F h7 K q)
    (pairWeak_support_to_ambient_v11 F h7 K q)
    (pairWeak_ambient_to_support_v11 F h7 L p)
    (pairWeak_support_to_ambient_v11 F h7 L p)


theorem independentDummy_pairWeak_neutrality_v11
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h7 : A7_ActionDataProcessing F)
    (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    pairWeak F q K (independentDummyPrior q r)
        (independentDummyChannel (B := B) K) ∧
      pairWeak F (independentDummyPrior q r)
        (independentDummyChannel (B := B) K) q K := by
  constructor
  · have hh := h7 K q (dummyRedrawKernel r)
      (independentDummyChannel (B := B) K)
      (dummyRedraw_isActionProcessorCompletion K q r)
    simpa [actionPushforward_dummyRedraw] using hh
  · have hh := h7 (independentDummyChannel (B := B) K)
      (independentDummyPrior q r)
      (dummyProjectionKernel (A := A) (B := B)) K
      (dummyProjection_isActionProcessorCompletion K q r)
    simpa [actionPushforward_dummyProjection] using hh


theorem pairWeak_iff_independentDummy_v11
    {O A B C D R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h7 : A7_ActionDataProcessing F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (r : TraceableAgency.Dist B)
    (p : TraceableAgency.Dist C) (L : Channel C (O × S))
    (s : TraceableAgency.Dist D) :
    pairWeak F q K p L ↔
      pairWeak F (independentDummyPrior q r)
          (independentDummyChannel (B := B) K)
        (independentDummyPrior p s)
          (independentDummyChannel (B := D) L) := by
  have hq := independentDummy_pairWeak_neutrality_v11 F h7 K q r
  have hp := independentDummy_pairWeak_neutrality_v11 F h7 L p s
  exact pairWeak_iff_of_pairwiseWeakEquiv F h1 h5
    K (independentDummyChannel (B := B) K)
    L (independentDummyChannel (B := D) L)
    q (independentDummyPrior q r) p (independentDummyPrior p s)
    hq.1 hq.2 hp.1 hp.2


theorem rel_iff_independentDummy_v11
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h7 : A7_ActionDataProcessing F)
    (K : Channel A (O × R))
    (q p : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    F.rel K q p ↔
      F.rel (independentDummyChannel (B := B) K)
        (independentDummyPrior q r) (independentDummyPrior p r) := by
  exact (h5.duplication K q p).trans
    ((pairWeak_iff_independentDummy_v11 F h1 h5 h7 q K r p K r).trans
      (h5.duplication (independentDummyChannel (B := B) K)
        (independentDummyPrior q r) (independentDummyPrior p r)).symm)


/-- The support restriction in Lemma 9 is indifference in the paper's exact
same-block convention, not merely two comparisons with reversed block tags. -/
theorem supportRestriction_pairIndiff_v11
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (q : Dist A) (K : Channel A (O × R)) :
    pairIndiff F q K q.restrictToSupport (Channel.restrictToSupport K q) := by
  constructor
  · exact pairWeak_ambient_to_support_v11 F h7 K q
  · exact (sameBlock_reverse_iff_pairWeak_swap F h1 h5 h6 h7
      q K q.restrictToSupport (Channel.restrictToSupport K q)).mpr
      (pairWeak_support_to_ambient_v11 F h7 K q)

/-- Independent dummy neutrality in the paper's exact same-block convention. -/
theorem independentDummy_pairIndiff_v11
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (q : Dist A) (K : Channel A (O × R)) (r : Dist B) :
    pairIndiff F q K (independentDummyPrior q r)
      (independentDummyChannel (B := B) K) := by
  have hn := independentDummy_pairWeak_neutrality_v11 F h7 K q r
  exact ⟨hn.1, (sameBlock_reverse_iff_pairWeak_swap F h1 h5 h6 h7
    q K (independentDummyPrior q r) (independentDummyChannel (B := B) K)).mpr hn.2⟩

end TraceableAgency.Theorem1
