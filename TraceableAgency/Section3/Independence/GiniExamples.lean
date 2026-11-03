import TraceableAgency.Section3.Independence.GiniStructure
import TraceableAgency.Section3.Independence.Relevance
import TraceableAgency.Theorem1.PureTrace

namespace TraceableAgency.Section3.Independence

open TraceableAgency Theorem1

universe u

@[simp] theorem squareMass_pure {A : Type u} [Fintype A] [DecidableEq A] (a : A) :
    squareMass (Dist.pure a) = 1 := by
  simp [squareMass, Dist.pure_apply]

@[simp] theorem gini_pure {A : Type u} [Fintype A] [DecidableEq A] (a : A) :
    gini (Dist.pure a) = 0 := by simp [gini]

@[simp] theorem giniInformation_pure
    {A Z : Type u} [Fintype A] [DecidableEq A] [Fintype Z]
    (a : A) (K : Channel A Z) : giniInformation (Dist.pure a) K = 0 := by
  have hm : Channel.outcomeMarginal K (Dist.pure a) = K a := by
    ext z
    simp [Channel.outcomeMarginal_apply, Dist.pure_apply]
  simp [giniInformation, hm, Dist.pure_apply, sq, mul_self_div_self, (K a).sum_eq_one]

theorem giniInformation_constantPayoffLift
    {O A R : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R]
    (o : O) (q : Dist A) (P : Channel A R) :
    giniInformation q (constantPayoffLift o P) = giniInformation q P := by
  unfold giniInformation
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_eq_single o]
  · simp only [constantPayoffLift_apply_same, Channel.outcomeMarginal_apply,
      constantPayoffLift_apply, ite_true]
  · intro o' _ ho
    simp [constantPayoffLift_apply, ho]
  · simp

theorem expectedPayoffUtility_constantPayoffLift_gini
    {O A R : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R]
    (v : O → ℝ) (o : O) (q : Dist A) (P : Channel A R) :
    expectedPayoffUtility v q (constantPayoffLift o P) = v o := by
  unfold expectedPayoffUtility
  have hrow : ∀ a, ∑ z, constantPayoffLift o P a z * v z.1 = v o := by
    intro a
    rw [Fintype.sum_prod_type, Finset.sum_eq_single o]
    · simp only [constantPayoffLift_apply_same]
      rw [← Finset.sum_mul, (P a).sum_eq_one, one_mul]
    · intro o' _ ho
      simp [constantPayoffLift_apply, ho]
    · simp
  simp_rw [hrow]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

private theorem sum_giniBit (f : RelevanceBit.{u} → ℝ) :
    (∑ b, f b) = f (ULift.up false) + f (ULift.up true) := by
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp f]
  simp [Fintype.sum_bool, Equiv.ulift]
  ring

noncomputable def giniTraceRecordBenchmark :
    Channel (RelevanceBit.{u} ⊕ RelevanceBit.{u}) RelevanceBit.{u}
  | Sum.inl b => Dist.pure b
  | Sum.inr _ => traceRelevanceFairPrior

theorem traceBenchmark_eq_giniLift
    {O : Type u} [Fintype O] [DecidableEq O] (o : O) :
    traceRelevanceBenchmarkChannel o = constantPayoffLift o giniTraceRecordBenchmark := by
  ext a z
  rcases z with ⟨o', b⟩
  cases a with
  | inl a =>
      by_cases ho : o' = o <;> by_cases hb : b = a <;>
        simp [traceRelevanceBenchmarkChannel, constantPayoffLift_apply,
          giniTraceRecordBenchmark, Dist.pure_apply, ho, hb]
  | inr a => rfl

theorem gini_traceBenchmark_revealing
    {O : Type u} [Fintype O] [DecidableEq O] (o : O) :
    giniInformation traceRelevanceRevealingPrior.{u,u} (traceRelevanceBenchmarkChannel.{u,u,u} o) = 1 / 2 := by
  rw [traceBenchmark_eq_giniLift o, giniInformation_constantPayoffLift]
  norm_num [giniInformation, squareMass, Channel.outcomeMarginal_apply,
    Fintype.sum_sum_type, sum_giniBit, traceRelevanceRevealingPrior,
    giniTraceRecordBenchmark, traceRelevanceFairPrior, Dist.uniform_apply, Dist.pure_apply]

theorem gini_traceBenchmark_unrevealing
    {O : Type u} [Fintype O] [DecidableEq O] (o : O) :
    giniInformation traceRelevanceUnrevealingPrior.{u,u} (traceRelevanceBenchmarkChannel.{u,u,u} o) = 0 := by
  rw [traceBenchmark_eq_giniLift o, giniInformation_constantPayoffLift]
  norm_num [giniInformation, squareMass, Channel.outcomeMarginal_apply,
    Fintype.sum_sum_type, sum_giniBit, traceRelevanceUnrevealingPrior,
    giniTraceRecordBenchmark, traceRelevanceFairPrior, Dist.uniform_apply, Dist.pure_apply]

theorem giniFamily_a3
    {O : Type u} [Fintype O] [DecidableEq O]
    (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) : A3_MaterialRelevance (giniFamily v) := by
  obtain ⟨op, om, hne, hs⟩ := (materialOnly_counterexample v hv).2.2.1
  refine ⟨op, om, hne, ?_⟩
  simpa only [FixedPayoffPrefFamily.strictRel, giniFamily, scoreFamily,
    traceScoreFamily, traceTemperedValue, zero_mul, add_zero,
    materialRelevanceBetterPrior, materialRelevanceWorsePrior,
    giniInformation_pure] using hs

theorem giniFamily_a4
    {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
    (v : O → ℝ) : A4_TraceRelevance (giniFamily v) := by
  let o : O := Classical.choice ‹Nonempty O›
  refine ⟨o, ?_⟩
  change expectedPayoffUtility v _ _ + giniInformation _ _ ≥
    expectedPayoffUtility v _ _ + giniInformation _ _ ∧ ¬
    expectedPayoffUtility v _ _ + giniInformation _ _ ≥
      expectedPayoffUtility v _ _ + giniInformation _ _
  rw [expectedPayoffUtility_traceBenchmark, expectedPayoffUtility_traceBenchmark,
    gini_traceBenchmark_revealing, gini_traceBenchmark_unrevealing]
  constructor <;> linarith

abbrev GiniThree : Type u := ULift.{u,0} (Fin 3)

noncomputable def giniThreePrior : Dist GiniThree.{u} where
  prob a := if a.down = 2 then 1 / 2 else 1 / 4
  nonneg a := by split_ifs <;> norm_num
  sum_eq_one := by
    rw [← (Equiv.ulift (α := Fin 3)).symm.sum_comp]
    norm_num [Equiv.ulift, Fin.sum_univ_succ, Fin.ext_iff]

def giniMerge (a : GiniThree.{u}) : RelevanceBit.{u} :=
  ULift.up (decide (a.down = 2))

noncomputable def giniMergeChannel : Channel GiniThree.{u} RelevanceBit.{u} :=
  fun a => Dist.pure (giniMerge a)

theorem giniMerge_pushforward :
    Channel.actionPushforward giniThreePrior (pureActionProcessor giniMerge) =
      traceRelevanceFairPrior := by
  ext b
  cases b with
  | up b =>
    cases b <;>
      simp only [Channel.actionPushforward, pureActionProcessor, Dist.pure_apply]
    all_goals
      rw [← (Equiv.ulift (α := Fin 3)).symm.sum_comp]
      norm_num [Equiv.ulift, Fin.sum_univ_succ, Fin.ext_iff, giniThreePrior, giniMerge,
        traceRelevanceFairPrior, Dist.uniform_apply]

theorem giniMerge_information : giniInformation giniThreePrior giniMergeChannel = 3 / 8 := by
  unfold giniInformation squareMass
  rw [sum_giniBit]
  simp only [Channel.outcomeMarginal_apply]
  simp_rw [← (Equiv.ulift (α := Fin 3)).symm.sum_comp]
  norm_num [Equiv.ulift, Fin.sum_univ_succ, Fin.ext_iff, giniThreePrior, giniMergeChannel,
    giniMerge, Dist.pure_apply]

theorem giniFair_reveal_information :
    giniInformation traceRelevanceFairPrior (Channel.idChannel : Channel RelevanceBit.{u} RelevanceBit.{u}) =
      1 / 2 := by
  norm_num [giniInformation, squareMass, Channel.outcomeMarginal_apply,
    sum_giniBit, traceRelevanceFairPrior, Dist.uniform_apply, Channel.idChannel, Dist.pure_apply]

theorem deterministicMerge_completion
    {O A B R : Type u} [Fintype O] [Fintype A] [Fintype B] [DecidableEq B]
    [Fintype R] (q : Dist A) (f : A → B) (L : Channel B (O × R)) :
    IsActionProcessorCompletion (fun a => L (f a)) q (pureActionProcessor f) L := by
  intro b z
  simp only [Channel.actionPushforward]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : b = f a
  · simp [pureActionProcessor, Dist.pure_apply, ha]
  · simp [pureActionProcessor, Dist.pure_apply, ha]

/-- Merging identical rows raises the Gini score from `3/8` to `1/2`. -/
theorem giniFamily_not_a7
    {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
    (v : O → ℝ) : ¬ A7_ActionDataProcessing (giniFamily v) := by
  intro h7
  let o : O := Classical.choice ‹Nonempty O›
  let K := constantPayoffLift o giniMergeChannel
  let L := fullRevealAtPayoff (A := RelevanceBit.{u}) o
  have hK : K = fun a => L (giniMerge a) := by
    ext a z
    rcases z with ⟨o', b⟩
    by_cases ho : o' = o <;> by_cases hb : b = giniMerge a <;>
      simp [K, L, constantPayoffLift_apply, giniMergeChannel,
        fullRevealAtPayoff, Dist.pure_apply, ho, hb]
  have hc : IsActionProcessorCompletion K giniThreePrior (pureActionProcessor giniMerge) L := by
    rw [hK]
    exact deterministicMerge_completion giniThreePrior giniMerge L
  have hh := h7 K giniThreePrior (pureActionProcessor giniMerge) L hc
  rw [giniFamily_pairWeak, giniMerge_pushforward] at hh
  change expectedPayoffUtility v _ (constantPayoffLift o giniMergeChannel) +
    giniInformation _ (constantPayoffLift o giniMergeChannel) ≥
      expectedPayoffUtility v _ (fullRevealAtPayoff o) + giniInformation _ (fullRevealAtPayoff o) at hh
  rw [expectedPayoffUtility_constantPayoffLift_gini,
    expectedPayoffUtility_fullRevealAtPayoff,
    giniInformation_constantPayoffLift, giniMerge_information,
    ← constantPayoffLift_idChannel, giniInformation_constantPayoffLift,
    giniFair_reveal_information] at hh
  linarith

end TraceableAgency.Section3.Independence
