import TraceableAgency.Theorem1.V11Affine
import TraceableAgency.Theorem1.CommonMarkedScale
import TraceableAgency.Theorem1.RelevanceBridge

/-! # Common material normalization without trace relevance

Only material relevance is added to the relevance-free affine-fibre theorem.
Proof provenance: the relevant declarations from `SupportDummy.lean`,
`RightDummy.lean`, `MaterialUtility.lean`, `NormalizedMarked.lean`,
`MarkedDummyMaps.lean`, and `CommonMarkedScale.lean` are retained below.
Only their axiom-bundle interfaces and structural-wrapper calls are narrowed.
The proofs below are the same normalization and dummy-embedding arguments,
with the unused trace-orientation field removed from their interfaces.
-/
namespace TraceableAgency.Theorem1.V11
open TraceableAgency Filter Set Topology
universe u

structure MaterialAxioms {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop extends AffineAxioms F where
  a7 : MaterialRelevanceEnvironment F

instance {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} : Coe (MaterialAxioms F) (AffineAxioms F) :=
  ⟨MaterialAxioms.toAffineAxioms⟩

theorem materialAxioms_of_paper
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h2 : A2_Continuity F) (h3 : A3_MaterialRelevance F)
    (h5 : A5_BlockComparisonCoherence F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F) (h8 : A8_RecordwiseSureThing F) :
    MaterialAxioms F :=
  ⟨affineAxioms_of_paper F h1 h2 h5 h6 h7 h8,
    (materialRelevance_bridge F h1 h5 h6 h7).mp h3⟩

/-! ## Narrowed SupportDummy interfaces -/

theorem pairWeak_ambient_to_support
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A) :
    pairWeak F q K q.restrictToSupport (Channel.restrictToSupport K q) := by
  have hh := h.a5 K q (supportProjectKernel q)
    (Channel.restrictToSupport K q)
    (actionCompletion_isExact K q (supportProjectKernel q)
      (Channel.restrictToSupport K q)
      (restrictToSupport_isBayesPushforwardCompletion K q))
  simpa [actionPushforward_project] using hh

theorem pairWeak_support_to_ambient
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A) :
    pairWeak F q.restrictToSupport (Channel.restrictToSupport K q) q K := by
  have hh := h.a5 (Channel.restrictToSupport K q) q.restrictToSupport
    (supportIncludeKernel q) K
    (actionCompletion_isExact (Channel.restrictToSupport K q) q.restrictToSupport
      (supportIncludeKernel q) K
      (ambient_isBayesPushforwardCompletion_of_restrict K q))
  simpa [actionPushforward_restrict_include] using hh

theorem pairWeak_iff_supportRestriction
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      pairWeak F q.restrictToSupport (Channel.restrictToSupport K q)
        p.restrictToSupport (Channel.restrictToSupport L p) :=
  pairWeak_iff_of_pairwiseWeakEquiv F h.a1 h.a3
    K (Channel.restrictToSupport K q)
    L (Channel.restrictToSupport L p)
    q q.restrictToSupport p p.restrictToSupport
    (pairWeak_ambient_to_support F h K q)
    (pairWeak_support_to_ambient F h K q)
    (pairWeak_ambient_to_support F h L p)
    (pairWeak_support_to_ambient F h L p)

theorem rel_iff_supportRestriction
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (K : Channel A (O × R))
    (q p : TraceableAgency.Dist A) :
    F.rel K q p ↔
      pairWeak F q.restrictToSupport (Channel.restrictToSupport K q)
        p.restrictToSupport (Channel.restrictToSupport K p) :=
  (h.a3.duplication K q p).trans
    (pairWeak_iff_supportRestriction F h q K p K)

theorem independentDummy_pairWeak_neutrality
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    pairWeak F q K (independentDummyPrior q r)
        (independentDummyChannel (B := B) K) ∧
      pairWeak F (independentDummyPrior q r)
        (independentDummyChannel (B := B) K) q K := by
  constructor
  · have hh := h.a5 K q (dummyRedrawKernel r)
      (independentDummyChannel (B := B) K)
      (dummyRedraw_isActionProcessorCompletion K q r)
    simpa [actionPushforward_dummyRedraw] using hh
  · have hh := h.a5 (independentDummyChannel (B := B) K)
      (independentDummyPrior q r)
      (dummyProjectionKernel (A := A) (B := B)) K
      (dummyProjection_isActionProcessorCompletion K q r)
    simpa [actionPushforward_dummyProjection] using hh

theorem pairWeak_iff_independentDummy
    {O A B C D R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (r : TraceableAgency.Dist B)
    (p : TraceableAgency.Dist C) (L : Channel C (O × S))
    (s : TraceableAgency.Dist D) :
    pairWeak F q K p L ↔
      pairWeak F (independentDummyPrior q r)
          (independentDummyChannel (B := B) K)
        (independentDummyPrior p s)
          (independentDummyChannel (B := D) L) := by
  have hq := independentDummy_pairWeak_neutrality F h K q r
  have hp := independentDummy_pairWeak_neutrality F h L p s
  exact pairWeak_iff_of_pairwiseWeakEquiv F h.a1 h.a3
    K (independentDummyChannel (B := B) K)
    L (independentDummyChannel (B := D) L)
    q (independentDummyPrior q r) p (independentDummyPrior p s)
    hq.1 hq.2 hp.1 hp.2

theorem rel_iff_independentDummy
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (K : Channel A (O × R))
    (q p : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    F.rel K q p ↔
      F.rel (independentDummyChannel (B := B) K)
        (independentDummyPrior q r) (independentDummyPrior p r) := by
  exact (h.a3.duplication K q p).trans
    ((pairWeak_iff_independentDummy F h q K r p K r).trans
      (h.a3.duplication (independentDummyChannel (B := B) K)
        (independentDummyPrior q r) (independentDummyPrior p r)).symm)

/-! ## Narrowed RightDummy interfaces -/

theorem rightIndependentDummy_pairWeak_neutrality
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (L : Channel B (O × R))
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairWeak F p L (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) ∧
      pairWeak F (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) p L := by
  let Lleft := independentDummyChannel (B := A) L
  let pleft := prodDist p q
  let Lright := rightIndependentDummyChannel (A := A) L
  let pright := prodDist q p
  have hleft := independentDummy_pairWeak_neutrality F h L p q
  have hswap := actionRelabel_pairWeak_neutrality F h.a5
    (Equiv.prodComm B A) Lleft pleft
  have hL : Relabeling.relabelChannel (Equiv.prodComm B A)
      (Equiv.refl (O × R)) Lleft = Lright := by
    exact relabel_independentDummyChannel_prodComm L
  have hp : Relabeling.relabelDist (Equiv.prodComm B A) pleft = pright := by
    exact relabel_prodDist_prodComm q p
  rw [hL, hp] at hswap
  exact
    ⟨pairWeak_transitive F h p L pleft Lleft pright Lright
        hleft.1 hswap.1,
      pairWeak_transitive F h pright Lright pleft Lleft p L
        hswap.2 hleft.2⟩

theorem pairWeak_iff_commonProductLifts
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      pairWeak F (prodDist q p)
          (independentDummyChannel (B := B) K)
        (prodDist q p)
          (rightIndependentDummyChannel (A := A) L) := by
  have hK := independentDummy_pairWeak_neutrality F h K q p
  have hL := rightIndependentDummy_pairWeak_neutrality F h L q p
  constructor
  · intro hKL
    exact pairWeak_transitive F h (prodDist q p)
      (independentDummyChannel (B := B) K) q K (prodDist q p)
      (rightIndependentDummyChannel (A := A) L)
      hK.2 (pairWeak_transitive F h q K p L (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) hKL hL.1)
  · intro hlift
    exact pairWeak_transitive F h q K (prodDist q p)
      (independentDummyChannel (B := B) K) p L
      hK.1 (pairWeak_transitive F h (prodDist q p)
        (independentDummyChannel (B := B) K) (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) p L hlift hL.2)

/-! ## Narrowed MaterialUtility interfaces -/

variable {O : Type u} [Fintype O] [DecidableEq O]

theorem payoffLotteryRel_complete
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (ell m : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m ∨ payoffLotteryRel F m ell :=
  pairWeak_complete F h
    singletonActionPrior (singletonPayoffLotteryChannel ell)
    singletonActionPrior (singletonPayoffLotteryChannel m)

theorem payoffLotteryRel_transitive
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (ell m n : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m → payoffLotteryRel F m n →
      payoffLotteryRel F ell n :=
  pairWeak_transitive_sameAction F h
    singletonActionPrior (singletonPayoffLotteryChannel ell)
    singletonActionPrior (singletonPayoffLotteryChannel m)
    singletonActionPrior (singletonPayoffLotteryChannel n)

theorem payoffCompoundMix_mutualPairWeak_ordinary
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell n : TraceableAgency.Dist O) :
    pairWeak F singletonActionPrior
        (payoffCompoundMixChannel t ht0 ht1 ell n)
        singletonActionPrior
        (mixedPayoffLotteryChannel t ht0 ht1 ell n) ∧
      pairWeak F singletonActionPrior
        (mixedPayoffLotteryChannel t ht0 ht1 ell n)
        singletonActionPrior
        (payoffCompoundMixChannel t ht0 ht1 ell n) := by
  rcases payoffCompoundMix_mutualPairWeak_marked F h.a4
      t ht0 ht1 ell n with ⟨hcm, hmc⟩
  rcases markedPayoffMix_mutualPairWeak F h.a4
      t ht0 ht1 ell n singletonActionPrior with ⟨hmo, hom⟩
  constructor
  · exact pairWeak_transitive F h
      singletonActionPrior (payoffCompoundMixChannel t ht0 ht1 ell n)
      singletonActionPrior (markedPayoffMixChannel t ht0 ht1 ell n)
      singletonActionPrior (mixedPayoffLotteryChannel t ht0 ht1 ell n)
      hcm hmo
  · exact pairWeak_transitive F h
      singletonActionPrior (mixedPayoffLotteryChannel t ht0 ht1 ell n)
      singletonActionPrior (markedPayoffMixChannel t ht0 ht1 ell n)
      singletonActionPrior (payoffCompoundMixChannel t ht0 ht1 ell n)
      hom hmc

theorem payoffCompoundMix_pairWeak_of_base
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (ell m n : TraceableAgency.Dist O)
    (hbase : payoffLotteryRel F ell m) :
    pairWeak F singletonActionPrior
        (payoffCompoundMixChannel t (le_of_lt ht0) (le_of_lt ht1) ell n)
      singletonActionPrior
        (payoffCompoundMixChannel t (le_of_lt ht0) (le_of_lt ht1) m n) := by
  apply h.a6.1 (fun _ : PayoffMixTag => PUnit.{u + 1})
    (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
    (payoffMixContinuation ell n) (payoffMixContinuation m n)
    singletonActionPrior
  intro b _hb
  have hp :
      branchPosterior
          (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
          singletonActionPrior b = singletonActionPrior :=
    dist_punit_eq_singleton _
  rcases b with ⟨b⟩
  cases b with
  | false =>
      simpa [payoffMixContinuation, hp] using
        pairWeak_refl F h singletonActionPrior
          (singletonPayoffLotteryChannel n)
  | true =>
      simpa [payoffLotteryRel, payoffMixContinuation, hp] using hbase

theorem payoffCompoundMix_pairStrict_of_base
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (ell m n : TraceableAgency.Dist O)
    (hbase : HMStrict (payoffLotteryRel F) ell m) :
    pairStrict F singletonActionPrior
        (payoffCompoundMixChannel t (le_of_lt ht0) (le_of_lt ht1) ell n)
      singletonActionPrior
        (payoffCompoundMixChannel t (le_of_lt ht0) (le_of_lt ht1) m n) := by
  have hweak :
      ∀ b, BranchPositive
          (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
          singletonActionPrior b →
        pairWeak F
          (branchPosterior
            (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
            singletonActionPrior b)
          (payoffMixContinuation ell n b)
          (branchPosterior
            (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
            singletonActionPrior b)
          (payoffMixContinuation m n b) := by
    intro b _hb
    have hp :
        branchPosterior
            (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
            singletonActionPrior b = singletonActionPrior :=
      dist_punit_eq_singleton _
    rcases b with ⟨b⟩
    cases b with
    | false =>
        simpa [payoffMixContinuation, hp] using
          pairWeak_refl F h singletonActionPrior
            (singletonPayoffLotteryChannel n)
    | true =>
        simpa [payoffLotteryRel, payoffMixContinuation, hp] using hbase.1
  apply h.a6.2 (fun _ : PayoffMixTag => PUnit.{u + 1})
    (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
    (payoffMixContinuation ell n) (payoffMixContinuation m n)
    singletonActionPrior hweak
  refine ⟨payoffMixLeft,
    payoffMixFirstStage_left_positive t ht0 ht1, ?_⟩
  have hp :
      branchPosterior
          (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
          singletonActionPrior payoffMixLeft = singletonActionPrior :=
    dist_punit_eq_singleton _
  have hstrict :
      pairStrict F singletonActionPrior
          (singletonPayoffLotteryChannel ell)
        singletonActionPrior
          (singletonPayoffLotteryChannel m) :=
    (pairStrict_iff_pairWeak_not_swap F h.a1 h.a3 h.a4 h.a5
      singletonActionPrior (singletonPayoffLotteryChannel ell)
      singletonActionPrior (singletonPayoffLotteryChannel m)).2
      (by simpa [HMStrict, payoffLotteryRel] using hbase)
  rw [hp]
  simpa [payoffMixContinuation, payoffMixLeft] using hstrict

theorem payoffLotteryRel_independence
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (ell m n : TraceableAgency.Dist O) (t : Set.Ioo (0 : ℝ) 1) :
    payoffLotteryRel F ell m ↔
      payoffLotteryRel F
        (payoffLotteryMixtureSpace.mix t ell n)
        (payoffLotteryMixtureSpace.mix t m n) := by
  let ht0 : 0 ≤ t.1 := le_of_lt t.2.1
  let ht1 : t.1 ≤ 1 := le_of_lt t.2.2
  have hell := payoffCompoundMix_mutualPairWeak_ordinary F h
    t.1 ht0 ht1 ell n
  have hm := payoffCompoundMix_mutualPairWeak_ordinary F h
    t.1 ht0 ht1 m n
  constructor
  · intro hbase
    have hcomp := payoffCompoundMix_pairWeak_of_base F h
      t.1 t.2.1 t.2.2 ell m n hbase
    have hleft := pairWeak_transitive F h
      singletonActionPrior (mixedPayoffLotteryChannel t.1 ht0 ht1 ell n)
      singletonActionPrior (payoffCompoundMixChannel t.1 ht0 ht1 ell n)
      singletonActionPrior (payoffCompoundMixChannel t.1 ht0 ht1 m n)
      hell.2 hcomp
    have hord := pairWeak_transitive F h
      singletonActionPrior (mixedPayoffLotteryChannel t.1 ht0 ht1 ell n)
      singletonActionPrior (payoffCompoundMixChannel t.1 ht0 ht1 m n)
      singletonActionPrior (mixedPayoffLotteryChannel t.1 ht0 ht1 m n)
      hleft hm.1
    simpa [payoffLotteryRel, payoffLotteryMixtureSpace,
      mixedPayoffLotteryChannel] using hord
  · intro hmixed
    by_contra hnbase
    have hswap : payoffLotteryRel F m ell :=
      (payoffLotteryRel_complete F h ell m).resolve_left hnbase
    have hstrictBase : HMStrict (payoffLotteryRel F) m ell :=
      ⟨hswap, hnbase⟩
    have hcompStrict := payoffCompoundMix_pairStrict_of_base F h
      t.1 t.2.1 t.2.2 m ell n hstrictBase
    have hordStrict :
        pairStrict F singletonActionPrior
            (mixedPayoffLotteryChannel t.1 ht0 ht1 m n)
          singletonActionPrior
            (mixedPayoffLotteryChannel t.1 ht0 ht1 ell n) := by
      exact pairStrict_transport_of_structural F h.a1 h.a3 h.a4 h.a5
        singletonActionPrior (payoffCompoundMixChannel t.1 ht0 ht1 m n)
        singletonActionPrior (payoffCompoundMixChannel t.1 ht0 ht1 ell n)
        singletonActionPrior (mixedPayoffLotteryChannel t.1 ht0 ht1 m n)
        singletonActionPrior (mixedPayoffLotteryChannel t.1 ht0 ht1 ell n)
        hcompStrict hm.2 hell.1
    have hnotReverse :=
      (pairStrict_iff_pairWeak_not_swap F h.a1 h.a3 h.a4 h.a5
        singletonActionPrior
          (mixedPayoffLotteryChannel t.1 ht0 ht1 m n)
        singletonActionPrior
          (mixedPayoffLotteryChannel t.1 ht0 ht1 ell n)).1
        hordStrict |>.2
    apply hnotReverse
    simpa [payoffLotteryRel, payoffLotteryMixtureSpace,
      mixedPayoffLotteryChannel] using hmixed

theorem payoffLotteryRel_sequentiallyClosed
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (ellseq : ℕ → TraceableAgency.Dist O) (ell : TraceableAgency.Dist O)
    (mseq : ℕ → TraceableAgency.Dist O) (m : TraceableAgency.Dist O)
    (hell : payoffLotteryMixtureSpace.Converges ellseq ell)
    (hm : payoffLotteryMixtureSpace.Converges mseq m)
    (hrel : ∀ k, payoffLotteryRel F (ellseq k) (mseq k)) :
    payoffLotteryRel F ell m := by
  apply h.a2
    (fun k => commonPayoffBlockChannel
      (singletonPayoffLotteryChannel (ellseq k))
      (singletonPayoffLotteryChannel (mseq k)))
    (commonPayoffBlockChannel
      (singletonPayoffLotteryChannel ell)
      (singletonPayoffLotteryChannel m))
    (fun _ => leftBlockDist singletonActionPrior)
    (fun _ => rightBlockDist singletonActionPrior)
    (leftBlockDist singletonActionPrior)
    (rightBlockDist singletonActionPrior)
  · exact payoffLotteryBlockChannel_converges ellseq mseq ell m hell hm
  · intro a
    exact tendsto_const_nhds
  · intro a
    exact tendsto_const_nhds
  · intro k
    simpa [payoffLotteryRel, pairWeak] using hrel k

theorem payoffLotteryContinuousIndependentWeakOrder
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    ContinuousIndependentWeakOrder payoffLotteryMixtureSpace
      (payoffLotteryRel F) where
  complete := payoffLotteryRel_complete F h
  transitive := payoffLotteryRel_transitive F h
  independence := payoffLotteryRel_independence F h
  sequentially_closed := payoffLotteryRel_sequentiallyClosed F h

theorem payoffLotteryRel_segmentCalibration
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (high target low : TraceableAgency.Dist O)
    (hhigh : payoffLotteryRel F high target)
    (hlow : payoffLotteryRel F target low) :
    ∃ t : HMUnitInterval,
      HMIndiff (payoffLotteryRel F) target
        (hmSegment payoffLotteryMixtureSpace t high low) :=
  hm_exists_indifferent_segment payoffLotteryMixtureSpace
    (payoffLotteryRel F)
    (payoffLotteryContinuousIndependentWeakOrder F h)
    high target low hhigh hlow

theorem payoffLotteryCalibratableWeakOrder
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    HMCalibratableWeakOrder payoffLotteryMixtureSpace
      (payoffLotteryRel F) where
  complete := payoffLotteryRel_complete F h
  transitive := payoffLotteryRel_transitive F h
  independence := payoffLotteryRel_independence F h
  segment_calibration := payoffLotteryRel_segmentCalibration F h

theorem payoffLotteryAffineUtility_exists
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    Nonempty
      (AffineUtilityRepresentation payoffLotteryMixtureSpace
        (payoffLotteryRel F)) :=
  genericHersteinMilnorAffineUtility_of_calibratable
    payoffLotteryMixtureSpace (payoffLotteryRel F)
    (payoffLotteryCalibratableWeakOrder F h)

noncomputable def materialHighOutcome
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) : O :=
  Classical.choose h.a7

noncomputable def materialLowOutcome
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) : O :=
  Classical.choose (Classical.choose_spec h.a7)

theorem materialChosenAnchors_pairStrict
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    pairStrict F singletonActionPrior
        (deterministicPayoffChannel (materialHighOutcome F h))
      singletonActionPrior
        (deterministicPayoffChannel (materialLowOutcome F h)) :=
  Classical.choose_spec (Classical.choose_spec h.a7)

theorem materialChosenAnchors_HMStrict
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    HMStrict (payoffLotteryRel F)
      (TraceableAgency.Dist.pure (materialHighOutcome F h))
      (TraceableAgency.Dist.pure (materialLowOutcome F h)) := by
  have hs :
      pairStrict F singletonActionPrior
          (singletonPayoffLotteryChannel
            (TraceableAgency.Dist.pure (materialHighOutcome F h)))
        singletonActionPrior
          (singletonPayoffLotteryChannel
            (TraceableAgency.Dist.pure (materialLowOutcome F h))) := by
    rw [singletonPayoffLottery_pure_eq_deterministic,
      singletonPayoffLottery_pure_eq_deterministic]
    exact materialChosenAnchors_pairStrict F h
  have hp :=
    (pairStrict_iff_pairWeak_not_swap F h.a1 h.a3 h.a4 h.a5
      singletonActionPrior
        (singletonPayoffLotteryChannel
          (TraceableAgency.Dist.pure (materialHighOutcome F h)))
      singletonActionPrior
        (singletonPayoffLotteryChannel
          (TraceableAgency.Dist.pure (materialLowOutcome F h)))).1 hs
  simpa only [HMStrict, payoffLotteryRel] using hp

noncomputable def materialRawAffineUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    AffineUtilityRepresentation payoffLotteryMixtureSpace
      (payoffLotteryRel F) :=
  Classical.choice (payoffLotteryAffineUtility_exists F h)

noncomputable def materialAffineUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    AffineUtilityRepresentation payoffLotteryMixtureSpace
      (payoffLotteryRel F) :=
  normalizeAffineUtility (materialRawAffineUtility F h)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)

noncomputable def materialPayoffUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) : O → ℝ :=
  fun o => (materialAffineUtility F h).utility
    (TraceableAgency.Dist.pure o)


theorem materialPayoffUtility_high
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    materialPayoffUtility F h (materialHighOutcome F h) = 1 := by
  exact normalizeAffineUtility_high
    (materialRawAffineUtility F h)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)


theorem materialAffineUtility_high
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    (materialAffineUtility F h).utility
        (TraceableAgency.Dist.pure (materialHighOutcome F h)) = 1 :=
  materialPayoffUtility_high F h


theorem materialPayoffUtility_low
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    materialPayoffUtility F h (materialLowOutcome F h) = 0 := by
  exact normalizeAffineUtility_low
    (materialRawAffineUtility F h)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)


theorem materialAffineUtility_low
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    (materialAffineUtility F h).utility
        (TraceableAgency.Dist.pure (materialLowOutcome F h)) = 0 :=
  materialPayoffUtility_low F h

theorem materialPayoffUtility_high_ne_low
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    materialPayoffUtility F h (materialHighOutcome F h) ≠
      materialPayoffUtility F h (materialLowOutcome F h) := by
  rw [materialPayoffUtility_high, materialPayoffUtility_low]
  norm_num

theorem materialHighOutcome_ne_low
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    materialHighOutcome F h ≠ materialLowOutcome F h := by
  intro heq
  have hu := materialPayoffUtility_high_ne_low F h
  exact hu (congrArg (materialPayoffUtility F h) heq)

theorem materialPayoffUtility_nonconstant
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    ¬ IsConstantPayoffIndex (materialPayoffUtility F h) := by
  rintro ⟨c, hc⟩
  have hhigh := hc (materialHighOutcome F h)
  have hlow := hc (materialLowOutcome F h)
  rw [materialPayoffUtility_high] at hhigh
  rw [materialPayoffUtility_low] at hlow
  linarith

theorem materialChosenAnchors_strict_everyPrior
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairStrict F q
        (payoffLotteryChannel
          (TraceableAgency.Dist.pure (materialHighOutcome F h)))
      p
        (payoffLotteryChannel
          (TraceableAgency.Dist.pure (materialLowOutcome F h))) := by
  have hs :
      pairStrict F singletonActionPrior
          (singletonPayoffLotteryChannel
            (TraceableAgency.Dist.pure (materialHighOutcome F h)))
        singletonActionPrior
          (singletonPayoffLotteryChannel
            (TraceableAgency.Dist.pure (materialLowOutcome F h))) := by
    rw [singletonPayoffLottery_pure_eq_deterministic,
      singletonPayoffLottery_pure_eq_deterministic]
    exact materialChosenAnchors_pairStrict F h
  exact pairStrict_transport_of_structural F h.a1 h.a3 h.a4 h.a5
    singletonActionPrior
      (singletonPayoffLotteryChannel
        (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    singletonActionPrior
      (singletonPayoffLotteryChannel
        (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    q (payoffLotteryChannel
      (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    p (payoffLotteryChannel
      (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    hs
    (payoffLottery_pairWeak F h.a5
      (TraceableAgency.Dist.pure (materialHighOutcome F h))
      q singletonActionPrior)
    (payoffLottery_pairWeak F h.a5
      (TraceableAgency.Dist.pure (materialLowOutcome F h))
      singletonActionPrior p)

theorem materialAffineUtility_eq_expected
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (ell : TraceableAgency.Dist O) :
    (materialAffineUtility F h).utility ell =
      payoffLotteryExpected (materialPayoffUtility F h) ell := by
  simpa [payoffLotteryExpected, materialPayoffUtility] using
    affineUtility_payoffLotteryExpected (payoffLotteryRel F)
      (materialAffineUtility F h) ell

theorem pairWeak_payoffLottery_iff_singletonRel
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ell m : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairWeak F q (payoffLotteryChannel ell)
        p (payoffLotteryChannel m) ↔
      payoffLotteryRel F ell m := by
  rcases payoffLottery_mutualPairWeak_singleton F h.a5 ell q with
    ⟨hqSingle, hsingleQ⟩
  rcases payoffLottery_mutualPairWeak_singleton F h.a5 m p with
    ⟨hpSingle, hsingleP⟩
  constructor
  · intro hqp
    have hleft := pairWeak_transitive F h
      singletonActionPrior (singletonPayoffLotteryChannel ell)
      q (payoffLotteryChannel ell)
      p (payoffLotteryChannel m)
      hsingleQ hqp
    exact pairWeak_transitive F h
      singletonActionPrior (singletonPayoffLotteryChannel ell)
      p (payoffLotteryChannel m)
      singletonActionPrior (singletonPayoffLotteryChannel m)
      hleft hpSingle
  · intro hsingle
    have hleft := pairWeak_transitive F h
      q (payoffLotteryChannel ell)
      singletonActionPrior (singletonPayoffLotteryChannel ell)
      singletonActionPrior (singletonPayoffLotteryChannel m)
      hqSingle hsingle
    exact pairWeak_transitive F h
      q (payoffLotteryChannel ell)
      singletonActionPrior (singletonPayoffLotteryChannel m)
      p (payoffLotteryChannel m)
      hleft hsingleP

theorem payoffLotteryRel_iff_expectedMaterialUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (ell m : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m ↔
      payoffLotteryExpected (materialPayoffUtility F h) ell ≥
        payoffLotteryExpected (materialPayoffUtility F h) m := by
  rw [(materialAffineUtility F h).represents]
  rw [materialAffineUtility_eq_expected,
    materialAffineUtility_eq_expected]

theorem pairWeak_payoffLottery_iff_expectedMaterialUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ell m : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairWeak F q (payoffLotteryChannel ell)
        p (payoffLotteryChannel m) ↔
      payoffLotteryExpected (materialPayoffUtility F h) ell ≥
        payoffLotteryExpected (materialPayoffUtility F h) m := by
  rw [pairWeak_payoffLottery_iff_singletonRel F h ell m q p,
    payoffLotteryRel_iff_expectedMaterialUtility F h ell m]

theorem pairWeak_payoffLottery_iff_expectedPayoffUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (ell m : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairWeak F q (payoffLotteryChannel ell)
        p (payoffLotteryChannel m) ↔
      expectedPayoffUtility (materialPayoffUtility F h) q
          (payoffLotteryChannel ell) ≥
        expectedPayoffUtility (materialPayoffUtility F h) p
          (payoffLotteryChannel m) := by
  rw [expectedPayoffUtility_payoffLotteryChannel,
    expectedPayoffUtility_payoffLotteryChannel]
  exact pairWeak_payoffLottery_iff_expectedMaterialUtility
    F h ell m q p

/-! ## Narrowed NormalizedMarked interfaces -/

variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

theorem markedPayoffLotteryEmbedding_order
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (ell m : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m ↔
      markedTerminalMixtureRel F h q hq
        (markedPayoffLotteryEmbedding q ell)
        (markedPayoffLotteryEmbedding q m) := by
  change payoffLotteryRel F ell m ↔
    markedTerminalMixtureRel F h q hq
      (⟦markedPayoffLotteryExperiment ell⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) q)
      ⟦markedPayoffLotteryExperiment m⟧
  rw [markedTerminalMixtureRel_mk]
  change payoffLotteryRel F ell m ↔
    pairWeak F q (payoffLotteryChannel ell) q (payoffLotteryChannel m)
  rw [payoffLotteryRel_iff_expectedMaterialUtility F h,
    pairWeak_payoffLottery_iff_expectedMaterialUtility F h ell m q q]

noncomputable abbrev markedMaterialHighExperiment
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    MarkedTerminalExperiment O A :=
  markedPayoffLotteryExperiment
    (TraceableAgency.Dist.pure (materialHighOutcome F h))

noncomputable abbrev markedMaterialLowExperiment
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F) :
    MarkedTerminalExperiment O A :=
  markedPayoffLotteryExperiment
    (TraceableAgency.Dist.pure (materialLowOutcome F h))

theorem markedMaterialAnchors_HMStrict
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    HMStrict (markedTerminalMixtureRel F h q hq)
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialHighOutcome F h)))
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialLowOutcome F h))) := by
  have hs := materialChosenAnchors_strict_everyPrior F h q q
  have hp := (pairStrict_iff_pairWeak_not_swap
    F h.a1 h.a3 h.a4 h.a5 q
      (payoffLotteryChannel
        (TraceableAgency.Dist.pure (materialHighOutcome F h))) q
      (payoffLotteryChannel
        (TraceableAgency.Dist.pure (materialLowOutcome F h)))).1 hs
  constructor
  · apply (markedTerminalMixtureRel_mk F h q hq
      (markedMaterialHighExperiment F h)
      (markedMaterialLowExperiment F h)).2
    simpa [MarkedPairWeak] using hp.1
  · intro hreverse
    apply hp.2
    have hr := (markedTerminalMixtureRel_mk F h q hq
      (markedMaterialLowExperiment F h)
      (markedMaterialHighExperiment F h)).1 hreverse
    simpa [MarkedPairWeak] using hr

noncomputable def normalizedMarkedAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq) :=
  normalizeAffineUtility
    (markedTerminalAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    (markedMaterialAnchors_HMStrict F h q hq)


theorem normalizedMarkedAffineUtility_high
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    (normalizedMarkedAffineUtilityRepresentation F h q hq).utility
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialHighOutcome F h))) = 1 := by
  exact normalizeAffineUtility_high
    (markedTerminalAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    (markedMaterialAnchors_HMStrict F h q hq)


theorem normalizedMarkedAffineUtility_low
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    (normalizedMarkedAffineUtilityRepresentation F h q hq).utility
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialLowOutcome F h))) = 0 := by
  exact normalizeAffineUtility_low
    (markedTerminalAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    (markedMaterialAnchors_HMStrict F h q hq)

noncomputable def normalizedMarkedUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E : MarkedTerminalExperiment O A) : ℝ :=
  (normalizedMarkedAffineUtilityRepresentation F h q hq).utility
    (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q)

theorem normalizedMarkedUtility_represents
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    MarkedPairWeak F q E q G ↔
      normalizedMarkedUtility F h q hq E ≥
        normalizedMarkedUtility F h q hq G := by
  rw [← markedTerminalMixtureRel_mk F h q hq E G]
  exact (normalizedMarkedAffineUtilityRepresentation F h q hq).represents _ _

theorem normalizedMarkedUtility_publicMix
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A) :
    normalizedMarkedUtility F h q hq
        (markedPublicMixExperiment t ht0 ht1 E R) =
      t * normalizedMarkedUtility F h q hq E +
        (1 - t) * normalizedMarkedUtility F h q hq R := by
  let ti : Set.Ioo (0 : ℝ) 1 := ⟨t, ht0, ht1⟩
  simpa [normalizedMarkedUtility,
    markedTerminalAbstractConvexMixtureSpace] using
      (normalizedMarkedAffineUtilityRepresentation F h q hq).affine ti
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦R⟧

theorem normalizedMarkedUtility_respects_sameMarkedTerminalLaw
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E') :
    normalizedMarkedUtility F h q hq E =
      normalizedMarkedUtility F h q hq E' := by
  unfold normalizedMarkedUtility
  congr 1
  exact Quotient.sound hsame


theorem normalizedMarkedUtility_high
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    normalizedMarkedUtility F h q hq
      (markedMaterialHighExperiment F h) = 1 :=
  normalizedMarkedAffineUtility_high F h q hq


theorem normalizedMarkedUtility_low
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    normalizedMarkedUtility F h q hq
      (markedMaterialLowExperiment F h) = 0 :=
  normalizedMarkedAffineUtility_low F h q hq

theorem normalizedMarkedUtility_payoffLottery
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (ell : TraceableAgency.Dist O) :
    normalizedMarkedUtility F h q hq
        (markedPayoffLotteryExperiment ell) =
      expectedPayoffUtility (materialPayoffUtility F h) q
        (payoffLotteryChannel ell) := by
  have hunique := normalizedAffineUtility_eq_along_embedding
    payoffLotteryMixtureSpace
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
    (payoffLotteryRel F)
    (markedTerminalMixtureRel (O := O) (A := A) F h q hq)
    (materialAffineUtility F h)
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q)
    (markedPayoffLotteryEmbedding_order F h q hq)
    (markedPayoffLotteryEmbedding_mix q)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)
    (materialAffineUtility_low F h)
    (materialAffineUtility_high F h)
    (normalizedMarkedAffineUtility_low F h q hq)
    (normalizedMarkedAffineUtility_high F h q hq)
    ell
  calc
    normalizedMarkedUtility F h q hq
        (markedPayoffLotteryExperiment ell) =
        (materialAffineUtility F h).utility ell := hunique
    _ = payoffLotteryExpected (materialPayoffUtility F h) ell :=
      materialAffineUtility_eq_expected F h ell
    _ = expectedPayoffUtility (materialPayoffUtility F h) q
        (payoffLotteryChannel ell) :=
      (expectedPayoffUtility_payoffLotteryChannel
        (materialPayoffUtility F h) ell q).symm

/-! ## Narrowed MarkedDummyMaps interfaces -/

variable {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B]

theorem independentDummyMarkedMixtureMap_rel_iff
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y ↔
      markedTerminalMixtureRel F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (independentDummyMarkedMixtureMap q r x)
        (independentDummyMarkedMixtureMap q r y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      letI : Fintype E.RecordType := E.recordFintype
      letI : DecidableEq E.RecordType := E.recordDecEq
      letI : Nonempty E.RecordType := E.recordNonempty
      letI : Fintype G.RecordType := G.recordFintype
      letI : DecidableEq G.RecordType := G.recordDecEq
      letI : Nonempty G.RecordType := G.recordNonempty
      simpa [markedTerminalMixtureRel_mk, MarkedPairWeak,
        independentDummyMarkedExperiment, independentDummyPrior] using
          (pairWeak_iff_independentDummy F h q E.K r q G.K r)

theorem rightIndependentDummyMarkedMixtureMap_rel_iff
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := B) r) :
    markedTerminalMixtureRel F h r hr x y ↔
      markedTerminalMixtureRel F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (rightIndependentDummyMarkedMixtureMap q r x)
        (rightIndependentDummyMarkedMixtureMap q r y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      letI : Fintype E.RecordType := E.recordFintype
      letI : DecidableEq E.RecordType := E.recordDecEq
      letI : Nonempty E.RecordType := E.recordNonempty
      letI : Fintype G.RecordType := G.recordFintype
      letI : DecidableEq G.RecordType := G.recordDecEq
      letI : Nonempty G.RecordType := G.recordNonempty
      have hE := rightIndependentDummy_pairWeak_neutrality
        F h E.K q r
      have hG := rightIndependentDummy_pairWeak_neutrality
        F h G.K q r
      simpa [markedTerminalMixtureRel_mk, MarkedPairWeak,
        rightIndependentDummyMarkedExperiment] using
          (pairWeak_iff_of_pairwiseWeakEquiv F h.a1 h.a3
            E.K (rightIndependentDummyChannel (A := A) E.K)
            G.K (rightIndependentDummyChannel (A := A) G.K)
            r (prodDist q r) r (prodDist q r)
            hE.1 hE.2 hG.1 hG.2)

/-! ## Narrowed CommonMarkedScale interfaces -/

theorem normalizedMarkedAffineUtility_independentDummy
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)).utility
        (independentDummyMarkedMixtureMap q r x) =
      (normalizedMarkedAffineUtilityRepresentation F h q hq).utility x := by
  let high := TraceableAgency.Dist.pure (materialHighOutcome F h)
  let low := TraceableAgency.Dist.pure (materialLowOutcome F h)
  have htargetLow :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (independentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding q low)) = 0 := by
    rw [independentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_low F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  have htargetHigh :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (independentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding q high)) = 1 := by
    rw [independentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_high F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  exact normalizedAffineUtility_eq_along_embedding
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
    (markedTerminalAbstractConvexMixtureSpace
      (O := O) (A := A × B) (prodDist q r))
    (markedTerminalMixtureRel (O := O) (A := A) F h q hq)
    (markedTerminalMixtureRel (O := O) (A := A × B) F h
      (prodDist q r) (markedDummy_prodDist_fullSupport q r hq hr))
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr))
    (independentDummyMarkedMixtureMap q r)
    (independentDummyMarkedMixtureMap_rel_iff F h q r hq hr)
    (independentDummyMarkedMixtureMap_affine q r)
    (markedPayoffLotteryEmbedding q high)
    (markedPayoffLotteryEmbedding q low)
    (markedMaterialAnchors_HMStrict F h q hq)
    (normalizedMarkedAffineUtility_low F h q hq)
    (normalizedMarkedAffineUtility_high F h q hq)
    htargetLow htargetHigh x

theorem normalizedMarkedAffineUtility_rightIndependentDummy
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (x : MarkedTerminalMixtureSpace (O := O) (A := B) r) :
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)).utility
        (rightIndependentDummyMarkedMixtureMap q r x) =
      (normalizedMarkedAffineUtilityRepresentation F h r hr).utility x := by
  let high := TraceableAgency.Dist.pure (materialHighOutcome F h)
  let low := TraceableAgency.Dist.pure (materialLowOutcome F h)
  have htargetLow :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (rightIndependentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding r low)) = 0 := by
    rw [rightIndependentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_low F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  have htargetHigh :
      (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
          (markedDummy_prodDist_fullSupport q r hq hr)).utility
          (rightIndependentDummyMarkedMixtureMap q r
            (markedPayoffLotteryEmbedding r high)) = 1 := by
    rw [rightIndependentDummyMarkedMixtureMap_payoffLottery]
    exact normalizedMarkedAffineUtility_high F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr)
  exact normalizedAffineUtility_eq_along_embedding
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := B) r)
    (markedTerminalAbstractConvexMixtureSpace
      (O := O) (A := A × B) (prodDist q r))
    (markedTerminalMixtureRel (O := O) (A := B) F h r hr)
    (markedTerminalMixtureRel (O := O) (A := A × B) F h
      (prodDist q r) (markedDummy_prodDist_fullSupport q r hq hr))
    (normalizedMarkedAffineUtilityRepresentation F h r hr)
    (normalizedMarkedAffineUtilityRepresentation F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr))
    (rightIndependentDummyMarkedMixtureMap q r)
    (rightIndependentDummyMarkedMixtureMap_rel_iff F h q r hq hr)
    (rightIndependentDummyMarkedMixtureMap_affine q r)
    (markedPayoffLotteryEmbedding r high)
    (markedPayoffLotteryEmbedding r low)
    (markedMaterialAnchors_HMStrict F h r hr)
    (normalizedMarkedAffineUtility_low F h r hr)
    (normalizedMarkedAffineUtility_high F h r hr)
    htargetLow htargetHigh x

theorem normalizedMarkedUtility_independentDummy
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (E : MarkedTerminalExperiment O A) :
    normalizedMarkedUtility F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (independentDummyMarkedExperiment (B := B) E) =
      normalizedMarkedUtility F h q hq E := by
  simpa [normalizedMarkedUtility] using
    normalizedMarkedAffineUtility_independentDummy F h q r hq hr
      (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q)

theorem normalizedMarkedUtility_rightIndependentDummy
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (E : MarkedTerminalExperiment O B) :
    normalizedMarkedUtility F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr)
        (rightIndependentDummyMarkedExperiment (A := A) E) =
      normalizedMarkedUtility F h r hr E := by
  simpa [normalizedMarkedUtility] using
    normalizedMarkedAffineUtility_rightIndependentDummy F h q r hq hr
      (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := B) r)

theorem pairWeak_markedExperiments_iff_normalizedMarkedUtility
    (F : FixedPayoffPrefFamily O) (h : MaterialAxioms F)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hp : p.FullSupport)
    (E : MarkedTerminalExperiment O A)
    (G : MarkedTerminalExperiment O B) :
    @pairWeak O A B E.RecordType G.RecordType
        inferInstance inferInstance
        inferInstance inferInstance inferInstance
        inferInstance inferInstance inferInstance
        E.recordFintype E.recordDecEq E.recordNonempty
        G.recordFintype G.recordDecEq G.recordNonempty
        F q E.channel p G.channel ↔
      normalizedMarkedUtility F h q hq E ≥
        normalizedMarkedUtility F h p hp G := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  rw [pairWeak_iff_commonProductLifts F h q E.K p G.K]
  change MarkedPairWeak F (prodDist q p)
      (independentDummyMarkedExperiment (B := B) E) (prodDist q p)
      (rightIndependentDummyMarkedExperiment (A := A) G) ↔ _
  rw [normalizedMarkedUtility_represents F h (prodDist q p)
      (markedDummy_prodDist_fullSupport q p hq hp),
    normalizedMarkedUtility_independentDummy F h q p hq hp E,
    normalizedMarkedUtility_rightIndependentDummy F h q p hq hp G]

/-- The complete conclusion of Appendix A Lemma 13. Values are defined on all
finite full-support fibres with one material utility and a common cardinal
scale; no trace-orientation condition occurs in this structure. -/
structure CommonMaterialScale
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) where
  utility : O → ℝ
  high : O
  low : O
  nonconstant : ¬ IsConstantPayoffIndex utility
  high_value : utility high = 1
  low_value : utility low = 0
  value : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
    (q : Dist A) → q.FullSupport → MarkedTerminalExperiment O A → ℝ
  affine : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E G : MarkedTerminalExperiment O A),
    value q hq (markedPublicMixExperiment t ht0 ht1 E G) =
      t * value q hq E + (1 - t) * value q hq G
  law_invariant : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (E G : MarkedTerminalExperiment O A),
    SameMarkedTerminalLaw q E G → value q hq E = value q hq G
  payoff_lottery : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (ell : Dist O),
    value q hq (markedPayoffLotteryExperiment ell) = payoffLotteryExpected utility ell
  dummy_invariant : ∀ {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (E : MarkedTerminalExperiment O A),
    value (prodDist q r) (markedDummy_prodDist_fullSupport q r hq hr)
      (independentDummyMarkedExperiment (B := B) E) = value q hq E
  represents : ∀ {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (p : Dist B) (hq : q.FullSupport) (hp : p.FullSupport)
    (K : Channel A (O × R)) (L : Channel B (O × S)),
    pairWeak F q K p L ↔
      value q hq (markedExperimentOfChannel K) ≥ value p hp (markedExperimentOfChannel L)

/-- Lemma 13 with precisely its seven numbered axioms, omitting A4. The
constructed witnesses verify every clause of the paper's common-scale claim. -/
theorem common_material_scale_exists_v11
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h2 : A2_Continuity F) (h3 : A3_MaterialRelevance F)
    (h5 : A5_BlockComparisonCoherence F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F) (h8 : A8_RecordwiseSureThing F) :
    Nonempty (CommonMaterialScale F) := by
  let h := materialAxioms_of_paper F h1 h2 h3 h5 h6 h7 h8
  refine ⟨{
    utility := materialPayoffUtility F h
    high := materialHighOutcome F h
    low := materialLowOutcome F h
    nonconstant := materialPayoffUtility_nonconstant F h
    high_value := materialPayoffUtility_high F h
    low_value := materialPayoffUtility_low F h
    value := fun q hq E ↦ normalizedMarkedUtility F h q hq E
    affine := ?_
    law_invariant := ?_
    payoff_lottery := ?_
    dummy_invariant := ?_
    represents := ?_
  }⟩
  · intro A _ _ _ q hq t ht0 ht1 E G
    exact normalizedMarkedUtility_publicMix F h q hq t ht0 ht1 E G
  · intro A _ _ _ q hq E G hlaw
    exact normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq E G hlaw
  · intro A _ _ _ q hq ell
    rw [normalizedMarkedUtility_payoffLottery, expectedPayoffUtility_payoffLotteryChannel]
  · intro A B _ _ _ _ _ _ q r hq hr E
    exact normalizedMarkedUtility_independentDummy F h q r hq hr E
  · intro A B R S _ _ _ _ _ _ _ _ _ _ _ _ q p hq hp K L
    exact pairWeak_markedExperiments_iff_normalizedMarkedUtility F h q p hq hp
      (markedExperimentOfChannel K) (markedExperimentOfChannel L)

end TraceableAgency.Theorem1.V11
