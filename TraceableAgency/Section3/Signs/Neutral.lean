import TraceableAgency.Section3.Signs.MaterialScale

/-! Neutral processing reduces every experiment to its payoff lottery.
The payoff-simplex utility is cardinalized without trace relevance. -/
namespace TraceableAgency.Theorem1.Section3
open TraceableAgency
universe u
variable {O : Type u} [Fintype O] [DecidableEq O]

/-- Indifference under record processing, expressed in both canonical orders. -/
def NeutralRecordProcessing (F : FixedPayoffPrefFamily O) : Prop :=
  A6_RecordDataProcessing F ∧ NegativeRecordProcessing F

/-- Indifference under exact action processing. -/
def NeutralActionProcessing (F : FixedPayoffPrefFamily O) : Prop :=
  A7_ActionDataProcessing F ∧ NegativeActionProcessing F

def NeutralTraceRelevance (F : FixedPayoffPrefFamily O) : Prop :=
  ∃ o : O, F.indiffRel (traceRelevanceBenchmarkChannel o)
    traceRelevanceRevealingPrior traceRelevanceUnrevealingPrior

/-- The payoff marginal, for arbitrary action alphabets. -/
noncomputable def neutralPayoffMarginal
    {A R : Type u} [Fintype A] [Fintype R]
    (q : Dist A) (K : Channel A (O × R)) : Dist O where
  prob o := ∑ r : R, Channel.outcomeMarginal K q (o, r)
  nonneg o := Finset.sum_nonneg fun r _ => (Channel.outcomeMarginal K q).nonneg (o, r)
  sum_eq_one := by
    rw [← Fintype.sum_prod_type]
    exact (Channel.outcomeMarginal K q).sum_eq_one

noncomputable def collapseOutputChannel
    {A R : Type u} [Fintype A] [Fintype R]
    (q : Dist A) (K : Channel A (O × R)) : Channel PUnit (O × R) :=
  fun _ => Channel.outcomeMarginal K q

noncomputable def eraseAllRecords {R : Type u} : RecordProcessor O R PUnit :=
  fun _ => Dist.pure PUnit.unit

theorem collapseOutput_completion
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (K : Channel A (O × R)) :
    IsActionProcessorCompletion K q collapseToUnitProcessor (collapseOutputChannel q K) := by
  intro b z
  cases b
  rw [actionPushforward_collapseToUnitProcessor]
  simp [collapseOutputChannel, collapseToUnitProcessor, pureActionProcessor,
    Channel.outcomeMarginal_apply]

theorem collapseOutput_erase
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (K : Channel A (O × R)) :
    recordPostprocess (collapseOutputChannel q K) eraseAllRecords =
      singletonPayoffLotteryChannel (neutralPayoffMarginal q K) := by
  classical
  ext a z
  rcases z with ⟨o, r⟩
  cases a
  cases r
  simp [recordPostprocess, payoffPreservingRecordKernel, Channel.postprocess,
    collapseOutputChannel, eraseAllRecords, Fintype.sum_prod_type,
    singletonPayoffLotteryChannel, payoffLotteryChannel, payoffLotteryRecordDist,
    neutralPayoffMarginal]
  rw [Finset.sum_eq_single o]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

theorem neutral_payoff_equivalence (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h6 : NeutralRecordProcessing F)
    (h7 : NeutralActionProcessing F)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (K : Channel A (O × R)) :
    pairWeak F q K singletonActionPrior
        (singletonPayoffLotteryChannel (neutralPayoffMarginal q K)) ∧
      pairWeak F singletonActionPrior
        (singletonPayoffLotteryChannel (neutralPayoffMarginal q K)) q K := by
  have hc := h7.1 K q collapseToUnitProcessor (collapseOutputChannel q K)
    (collapseOutput_completion q K)
  have hcr := h7.2 K q collapseToUnitProcessor (collapseOutputChannel q K)
    (collapseOutput_completion q K)
  rw [actionPushforward_collapseToUnitProcessor] at hc hcr
  have he := h6.1 (collapseOutputChannel q K) eraseAllRecords singletonActionPrior
  have her := h6.2 (collapseOutputChannel q K) eraseAllRecords singletonActionPrior
  rw [collapseOutput_erase] at he her
  exact ⟨pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ hc he,
    pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ her hcr⟩

theorem neutral_pair_iff_payoffLottery (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h6 : NeutralRecordProcessing F)
    (h7 : NeutralActionProcessing F)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R))
    (p : Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔ payoffLotteryRel F
      (neutralPayoffMarginal q K) (neutralPayoffMarginal p L) := by
  have hq := neutral_payoff_equivalence F h h6 h7 q K
  have hp := neutral_payoff_equivalence F h h6 h7 p L
  constructor
  · intro hh
    exact pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _
      (pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ hq.2 hh) hp.1
  · intro hh
    exact pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _
      (pairWeak_transitive_of_structural F h.a1 h.a5 _ _ _ _ _ _ hq.1 hh) hp.2

theorem payoffLotteryExpected_induced
    {A R : Type u} [Fintype A] [Fintype R]
    (v : O → ℝ) (q : Dist A) (K : Channel A (O × R)) :
    payoffLotteryExpected v (neutralPayoffMarginal q K) = expectedPayoffUtility v q K := by
  rw [expectedPayoffUtility_eq_marginal, Fintype.sum_prod_type]
  simp [payoffLotteryExpected, neutralPayoffMarginal, Finset.sum_mul]

/-- Neutral action and record processing suffice; neutral benchmark relevance
is then a consequence rather than an additional cardinalization assumption. -/
theorem neutral_representation (F : FixedPayoffPrefFamily O)
    (h : SignBackground F) (h6 : NeutralRecordProcessing F)
    (h7 : NeutralActionProcessing F) :
    ∃ v : O → ℝ, ¬ IsConstantPayoffIndex v ∧
      WithinChannelRepresentation F v 0 ∧ SameWitnessBlockRepresentation F v 0 := by
  obtain ⟨rep⟩ := weak_payoffLottery_affine_exists F h h6.1 h7.1
  let v : O → ℝ := fun o => rep.utility (Dist.pure o)
  have hlot (ell : Dist O) : rep.utility ell = payoffLotteryExpected v ell :=
    affineUtility_payoffLotteryExpected (payoffLotteryRel F) rep ell
  have hpair {A B R S : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype R] [DecidableEq R] [Nonempty R]
      [Fintype S] [DecidableEq S] [Nonempty S]
      (q : Dist A) (K : Channel A (O × R))
      (p : Dist B) (L : Channel B (O × S)) :
      pairWeak F q K p L ↔ traceTemperedValue v 0 q K ≥ traceTemperedValue v 0 p L := by
    rw [neutral_pair_iff_payoffLottery F h h6 h7, rep.represents, hlot, hlot,
      payoffLotteryExpected_induced, payoffLotteryExpected_induced]
    simp [traceTemperedValue]
  have hw : WithinChannelRepresentation F v 0 := by
    intro A R _ _ _ _ _ _ K q p
    exact (h.a5.duplication K q p).trans (hpair q K p K)
  refine ⟨v, ?_, hw, ?_⟩
  · rintro ⟨c, hc⟩
    obtain ⟨op, om, _, hs⟩ := h.a3
    apply hs.2
    apply (hw (materialRelevanceBenchmarkChannel op om)
      materialRelevanceWorsePrior materialRelevanceBetterPrior).mpr
    have hconst {A R : Type u} [Fintype A] [Fintype R]
        (q : Dist A) (K : Channel A (O × R)) : traceTemperedValue v 0 q K = c := by
      simp only [traceTemperedValue, zero_mul, add_zero, expectedPayoffUtility, hc]
      simp_rw [← Finset.sum_mul, Dist.sum_eq_one, one_mul]
      rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
    rw [hconst, hconst]
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    exact (h.a5.irrelevant_blocks Act Rec K i j hij qi qj).trans (hpair qi (K i) qj (K j))

end TraceableAgency.Theorem1.Section3
