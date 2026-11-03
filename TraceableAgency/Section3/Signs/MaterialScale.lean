import TraceableAgency.Section3.Signs.Reverse

/-! Material lottery cardinalization requires no orientation of trace relevance.
This version exposes precisely the background, forward weak processing, and A8
hypotheses used by the payoff-simplex argument. -/
namespace TraceableAgency.Theorem1.Section3
open TraceableAgency Filter Set Topology
universe u
variable {O : Type u} [Fintype O] [DecidableEq O]

 theorem weak_pair_complete (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R))
    (p : Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ∨ pairWeak F p L q K := by
  rcases (h.a1 (commonPayoffBlockChannel K L)).1
    (leftBlockDist q) (rightBlockDist p) with hh | hh
  · exact Or.inl hh
  · exact Or.inr ((sameBlock_reverse_iff_pairWeak_swap F h.a1 h.a5 h6 h7
      q K p L).mp hh)

theorem weak_payoffCompoundMix_mutual
    (F : FixedPayoffPrefFamily O) (h : SignBackground F) (h6 : A6_RecordDataProcessing F)
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
  rcases payoffCompoundMix_mutualPairWeak_marked F h6
      t ht0 ht1 ell n with ⟨hcm, hmc⟩
  rcases markedPayoffMix_mutualPairWeak F h6
      t ht0 ht1 ell n singletonActionPrior with ⟨hmo, hom⟩
  constructor
  · exact pairWeak_transitive_of_structural F h.a1 h.a5
      singletonActionPrior (payoffCompoundMixChannel t ht0 ht1 ell n)
      singletonActionPrior (markedPayoffMixChannel t ht0 ht1 ell n)
      singletonActionPrior (mixedPayoffLotteryChannel t ht0 ht1 ell n)
      hcm hmo
  · exact pairWeak_transitive_of_structural F h.a1 h.a5
      singletonActionPrior (mixedPayoffLotteryChannel t ht0 ht1 ell n)
      singletonActionPrior (markedPayoffMixChannel t ht0 ht1 ell n)
      singletonActionPrior (payoffCompoundMixChannel t ht0 ht1 ell n)
      hom hmc

theorem weak_payoffLottery_independence (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h6 : A6_RecordDataProcessing F)
    (ell m n : Dist O) (t : Set.Ioo (0 : ℝ) 1) :
    payoffLotteryRel F ell m ↔ payoffLotteryRel F
      (payoffLotteryMixtureSpace.mix t ell n)
      (payoffLotteryMixtureSpace.mix t m n) := by
  let ht0 := le_of_lt t.2.1
  let ht1 := le_of_lt t.2.2
  have he := weak_payoffCompoundMix_mutual F h h6 t.1 ht0 ht1 ell n
  have hm := weak_payoffCompoundMix_mutual F h h6 t.1 ht0 ht1 m n
  have hc := h.a8 singletonActionPrior (payoffMixFirstStage t.1 ht0 ht1)
    (singletonPayoffLotteryChannel ell) (singletonPayoffLotteryChannel m)
    (singletonPayoffLotteryChannel n)
    (payoffMixFirstStage_left_positive t.1 t.2.1 t.2.2)
  rw [dist_punit_eq_singleton (branchPosterior (payoffMixFirstStage t.1 ht0 ht1)
    singletonActionPrior (ULift.up true))] at hc
  change payoffLotteryRel F ell m ↔
    pairWeak F singletonActionPrior (payoffCompoundMixChannel t.1 ht0 ht1 ell n)
      singletonActionPrior (payoffCompoundMixChannel t.1 ht0 ht1 m n) at hc
  constructor
  · intro hh
    have hx := pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ he.2 (hc.mp hh)
    have hy := pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ hx hm.1
    simpa [payoffLotteryRel, payoffLotteryMixtureSpace, mixedPayoffLotteryChannel] using hy
  · intro hh
    apply hc.mpr
    have hh' : pairWeak F singletonActionPrior
        (mixedPayoffLotteryChannel t.1 ht0 ht1 ell n) singletonActionPrior
        (mixedPayoffLotteryChannel t.1 ht0 ht1 m n) := hh
    have hx := pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ he.1 hh'
    exact pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ hx hm.2

theorem weak_payoffLottery_closed
    (F : FixedPayoffPrefFamily O) (h : SignBackground F)
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

noncomputable def weak_payoffLottery_order (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F) :
    ContinuousIndependentWeakOrder payoffLotteryMixtureSpace (payoffLotteryRel F) where
  complete := fun ell m => weak_pair_complete F h h6 h7
    singletonActionPrior (singletonPayoffLotteryChannel ell)
    singletonActionPrior (singletonPayoffLotteryChannel m)
  transitive := fun ell m n => pairWeak_transitive_of_structural F h.a1 h.a5
    singletonActionPrior (singletonPayoffLotteryChannel ell)
    singletonActionPrior (singletonPayoffLotteryChannel m)
    singletonActionPrior (singletonPayoffLotteryChannel n)
  independence := weak_payoffLottery_independence F h h6
  sequentially_closed := weak_payoffLottery_closed F h

theorem weak_payoffLottery_affine_exists (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F) :
    Nonempty (AffineUtilityRepresentation payoffLotteryMixtureSpace (payoffLotteryRel F)) := by
  let hc := weak_payoffLottery_order F h h6 h7
  apply genericHersteinMilnorAffineUtility_of_calibratable
  exact {
    complete := hc.complete
    transitive := hc.transitive
    independence := hc.independence
    segment_calibration := hm_exists_indifferent_segment payoffLotteryMixtureSpace
      (payoffLotteryRel F) hc }

end TraceableAgency.Theorem1.Section3
