/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PairOrder

/-!
# Action-independent payoff lotteries

This file isolates the material-payoff slice used in the converse direction.
It defines action-independent payoff lotteries, their singleton versions, and
binary public mixtures.  It proves their finite marginal and expectation
identities, their exact action-report equivalence across action alphabets, and
the payoff-preserving record equivalence between marked and ordinary mixtures.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-! ## Ordinary payoff lotteries -/

/-- The visible payoff-record law associated with a payoff lottery.  Its
record is the unique uninformative record. -/
noncomputable def payoffLotteryRecordDist
    {O : Type u} [Fintype O]
    (ell : TraceableAgency.Dist O) :
    TraceableAgency.Dist (O × PUnit) where
  prob := fun z => ell z.1
  nonneg := fun z => ell.nonneg z.1
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simpa using ell.sum_eq_one

@[simp]
theorem payoffLotteryRecordDist_apply
    {O : Type u} [Fintype O]
    (ell : TraceableAgency.Dist O) (o : O) (r : PUnit) :
    payoffLotteryRecordDist ell (o, r) = ell o :=
  rfl

/-- An action-independent payoff lottery with an uninformative record. -/
noncomputable def payoffLotteryChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (ell : TraceableAgency.Dist O) : Channel A (O × PUnit) :=
  fun _ => payoffLotteryRecordDist ell

@[simp]
theorem payoffLotteryChannel_apply
    {O A : Type u} [Fintype O] [Fintype A]
    (ell : TraceableAgency.Dist O) (a : A) (o : O) (r : PUnit) :
    payoffLotteryChannel (A := A) ell a (o, r) = ell o :=
  rfl

/-- The canonical singleton-action version of a payoff lottery. -/
noncomputable abbrev singletonPayoffLotteryChannel
    {O : Type u} [Fintype O]
    (ell : TraceableAgency.Dist O) : Channel PUnit (O × PUnit) :=
  payoffLotteryChannel ell

/-- The unique singleton-action prior. -/
noncomputable abbrev singletonActionPrior : TraceableAgency.Dist PUnit :=
  TraceableAgency.Dist.pure PUnit.unit

theorem outcomeMarginal_payoffLotteryChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (ell : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) :
    Channel.outcomeMarginal (payoffLotteryChannel (A := A) ell) q =
      payoffLotteryRecordDist ell := by
  ext z
  simp only [Channel.outcomeMarginal_apply, payoffLotteryChannel]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

theorem payoffMarginal_payoffLotteryChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (ell : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) (o : O) :
    ∑ r : PUnit,
      Channel.outcomeMarginal (payoffLotteryChannel (A := A) ell) q (o, r) =
      ell o := by
  rw [outcomeMarginal_payoffLotteryChannel]
  simp

/-- Ordinary expectation of a payoff index under a payoff lottery. -/
noncomputable def payoffLotteryExpected
    {O : Type u} [Fintype O]
    (v : O → ℝ) (ell : TraceableAgency.Dist O) : ℝ :=
  ∑ o, ell o * v o

theorem expectedPayoffUtility_payoffLotteryChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (v : O → ℝ) (ell : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) :
    expectedPayoffUtility v q (payoffLotteryChannel (A := A) ell) =
      payoffLotteryExpected v ell := by
  unfold expectedPayoffUtility payoffLotteryExpected payoffLotteryChannel
  simp only [Fintype.sum_prod_type, payoffLotteryRecordDist_apply]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  simp

/-! ## Binary public mixtures -/

/-- A universe-polymorphic two-point public record. -/
abbrev PayoffMixTag : Type u := ULift.{u, 0} Bool

def payoffMixLeft : PayoffMixTag.{u} := ULift.up true
def payoffMixRight : PayoffMixTag.{u} := ULift.up false

/-- The public-coin weights `(t,1-t)`. -/
noncomputable def payoffMixWeights
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TraceableAgency.Dist PayoffMixTag :=
  faddeevBinaryDist ⟨t, ht0, ht1⟩

@[simp]
theorem payoffMixWeights_left
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    payoffMixWeights t ht0 ht1 payoffMixLeft = t := by
  simp [payoffMixWeights, payoffMixLeft, faddeevBinaryDist]

@[simp]
theorem payoffMixWeights_right
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    payoffMixWeights t ht0 ht1 payoffMixRight = 1 - t := by
  simp [payoffMixWeights, payoffMixRight, faddeevBinaryDist]

/-- Conditional payoff law in each public branch. -/
def payoffMixBranchChannel
    {O : Type u} [Fintype O]
    (ell m : TraceableAgency.Dist O) : Channel PayoffMixTag O :=
  fun b => if b.down then ell else m

@[simp]
theorem payoffMixBranchChannel_left
    {O : Type u} [Fintype O]
    (ell m : TraceableAgency.Dist O) :
    payoffMixBranchChannel ell m payoffMixLeft = ell := by
  simp [payoffMixBranchChannel, payoffMixLeft]

@[simp]
theorem payoffMixBranchChannel_right
    {O : Type u} [Fintype O]
    (ell m : TraceableAgency.Dist O) :
    payoffMixBranchChannel ell m payoffMixRight = m := by
  simp [payoffMixBranchChannel, payoffMixRight]

theorem outcomeMarginal_payoffMixBranchChannel
    {O : Type u} [Fintype O]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) :
    Channel.outcomeMarginal (payoffMixBranchChannel ell m)
        (payoffMixWeights t ht0 ht1) =
      TraceableAgency.Dist.mix t ht0 ht1 ell m := by
  ext o
  simp only [Channel.outcomeMarginal_apply]
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp
    (fun b : PayoffMixTag =>
      payoffMixWeights t ht0 ht1 b * payoffMixBranchChannel ell m b o)]
  simp [Fintype.sum_bool, payoffMixLeft, payoffMixRight,
    payoffMixWeights, faddeevBinaryDist, payoffMixBranchChannel]

/-- Joint payoff/public-record law before the public record is erased. -/
noncomputable def markedPayoffMixDist
    {O : Type u} [Fintype O]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) :
    TraceableAgency.Dist (O × PayoffMixTag) where
  prob := fun z => payoffMixWeights t ht0 ht1 z.2 *
    payoffMixBranchChannel ell m z.2 z.1
  nonneg := fun z => mul_nonneg
    ((payoffMixWeights t ht0 ht1).nonneg z.2)
    ((payoffMixBranchChannel ell m z.2).nonneg z.1)
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [← Finset.mul_sum,
      (payoffMixBranchChannel ell m _).sum_eq_one, mul_one]
    exact (payoffMixWeights t ht0 ht1).sum_eq_one

@[simp]
theorem markedPayoffMixDist_apply
    {O : Type u} [Fintype O]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) (o : O) (b : PayoffMixTag) :
    markedPayoffMixDist t ht0 ht1 ell m (o, b) =
      payoffMixWeights t ht0 ht1 b * payoffMixBranchChannel ell m b o :=
  rfl

/-- Action-independent payoff lottery whose visible record marks the public
branch used to generate the payoff. -/
noncomputable def markedPayoffMixChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) :
    Channel A (O × PayoffMixTag) :=
  fun _ => markedPayoffMixDist t ht0 ht1 ell m

/-- The ordinary, unmarked convex mixture of two payoff lotteries. -/
noncomputable def mixedPayoffLotteryChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) : Channel A (O × PUnit) :=
  payoffLotteryChannel (TraceableAgency.Dist.mix t ht0 ht1 ell m)

theorem outcomeMarginal_markedPayoffMixChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) :
    Channel.outcomeMarginal
        (markedPayoffMixChannel (A := A) t ht0 ht1 ell m) q =
      markedPayoffMixDist t ht0 ht1 ell m := by
  ext z
  simp only [Channel.outcomeMarginal_apply, markedPayoffMixChannel]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

theorem payoffMarginal_markedPayoffMixChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) (o : O) :
    ∑ b : PayoffMixTag,
      Channel.outcomeMarginal
        (markedPayoffMixChannel (A := A) t ht0 ht1 ell m) q (o, b) =
      TraceableAgency.Dist.mix t ht0 ht1 ell m o := by
  rw [outcomeMarginal_markedPayoffMixChannel]
  change ∑ b, payoffMixWeights t ht0 ht1 b *
      payoffMixBranchChannel ell m b o = _
  have hmarg := congrArg
    (fun d : TraceableAgency.Dist O => d o)
    (outcomeMarginal_payoffMixBranchChannel t ht0 ht1 ell m)
  exact hmarg

theorem expectedPayoffUtility_markedPayoffMixChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (v : O → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) :
    expectedPayoffUtility v q
        (markedPayoffMixChannel (A := A) t ht0 ht1 ell m) =
      t * payoffLotteryExpected v ell +
        (1 - t) * payoffLotteryExpected v m := by
  unfold expectedPayoffUtility payoffLotteryExpected markedPayoffMixChannel
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [markedPayoffMixDist_apply]
  rw [Finset.sum_comm]
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp
    (fun b : PayoffMixTag =>
      ∑ o, payoffMixWeights t ht0 ht1 b *
        payoffMixBranchChannel ell m b o * v o)]
  simp [Fintype.sum_bool, payoffMixLeft, payoffMixRight,
    payoffMixWeights, faddeevBinaryDist, payoffMixBranchChannel,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro o _ <;> ring

theorem expectedPayoffUtility_mixedPayoffLotteryChannel
    {O A : Type u} [Fintype O] [Fintype A]
    (v : O → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) :
    expectedPayoffUtility v q
        (mixedPayoffLotteryChannel (A := A) t ht0 ht1 ell m) =
      t * payoffLotteryExpected v ell +
        (1 - t) * payoffLotteryExpected v m := by
  rw [mixedPayoffLotteryChannel,
    expectedPayoffUtility_payoffLotteryChannel]
  unfold payoffLotteryExpected
  simp_rw [TraceableAgency.Dist.mix_apply, add_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro o _ <;> ring

/-! ## Exact action-report equivalence -/

/-- Ignore the reported action and draw the target action from `p`. -/
noncomputable def payoffLotteryActionReport
    {A B : Type u} [Fintype B]
    (p : TraceableAgency.Dist B) : Channel.ActionKernel A B :=
  fun _ => p

theorem actionPushforward_payoffLotteryActionReport
    {A B : Type u} [Fintype A] [Fintype B]
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    Channel.actionPushforward q (payoffLotteryActionReport p) = p := by
  ext b
  change (∑ a, q a * p b) = p b
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

theorem payoffLotteryActionReport_isBayesCompletion
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    (ell : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    Channel.IsBayesPushforwardCompletion
      (payoffLotteryChannel (A := A) ell) q
      (payoffLotteryActionReport p)
      (payoffLotteryChannel (A := B) ell) := by
  intro b hb z
  rw [actionPushforward_payoffLotteryActionReport] at hb ⊢
  change ell z.1 = (∑ a, q a * p b * ell z.1) / p b
  simp_rw [mul_assoc]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  field_simp [ne_of_gt hb]

theorem payoffLotteryActionReport_isExact
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    (ell : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    IsActionReportCompletion
      (payoffLotteryChannel (A := A) ell) q
      (payoffLotteryActionReport p)
      (payoffLotteryChannel (A := B) ell) :=
  actionCompletion_isExact
    (payoffLotteryChannel (A := A) ell) q
    (payoffLotteryActionReport p)
    (payoffLotteryChannel (A := B) ell)
    (payoffLotteryActionReport_isBayesCompletion ell q p)

/-- Any two uses of the same payoff lottery are weakly equivalent, regardless
of their action alphabets or priors. -/
theorem payoffLottery_pairWeak
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (F : FixedPayoffPrefFamily O) (h5 : A5_ActionDataProcessing F)
    (ell : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairWeak F q (payoffLotteryChannel ell)
      p (payoffLotteryChannel ell) := by
  have hh := h5 (payoffLotteryChannel (A := A) ell) q
    (payoffLotteryActionReport p)
    (payoffLotteryChannel (A := B) ell)
    (payoffLotteryActionReport_isExact ell q p)
  simpa [actionPushforward_payoffLotteryActionReport] using hh

theorem payoffLottery_mutualPairWeak
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (F : FixedPayoffPrefFamily O) (h5 : A5_ActionDataProcessing F)
    (ell : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairWeak F q (payoffLotteryChannel ell)
        p (payoffLotteryChannel ell) ∧
      pairWeak F p (payoffLotteryChannel ell)
        q (payoffLotteryChannel ell) :=
  ⟨payoffLottery_pairWeak F h5 ell q p,
    payoffLottery_pairWeak F h5 ell p q⟩

theorem payoffLottery_mutualPairWeak_singleton
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : FixedPayoffPrefFamily O) (h5 : A5_ActionDataProcessing F)
    (ell : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) :
    pairWeak F q (payoffLotteryChannel ell)
        singletonActionPrior (singletonPayoffLotteryChannel ell) ∧
      pairWeak F singletonActionPrior (singletonPayoffLotteryChannel ell)
        q (payoffLotteryChannel ell) :=
  payoffLottery_mutualPairWeak F h5 ell q singletonActionPrior

theorem payoffLottery_pairIndiff
    {O A B : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (ell : TraceableAgency.Dist O)
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairIndiff F q (payoffLotteryChannel ell)
      p (payoffLotteryChannel ell) := by
  rcases payoffLottery_mutualPairWeak F h.a5 ell q p with ⟨hforward, hback⟩
  unfold pairIndiff
  dsimp
  exact ⟨hforward,
    (sameBlock_reverse_iff_pairWeak_swap F h.a1 h.a3 h.a4 h.a5
      q (payoffLotteryChannel ell) p (payoffLotteryChannel ell)).2 hback⟩

/-! ## Erasing and reconstructing the public mark -/

theorem payoffMarginal_markedPayoffMixDist
    {O : Type u} [Fintype O]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) (o : O) :
    ∑ b : PayoffMixTag, markedPayoffMixDist t ht0 ht1 ell m (o, b) =
      TraceableAgency.Dist.mix t ht0 ht1 ell m o := by
  change ∑ b, payoffMixWeights t ht0 ht1 b *
      payoffMixBranchChannel ell m b o = _
  have hmarg := congrArg
    (fun d : TraceableAgency.Dist O => d o)
    (outcomeMarginal_payoffMixBranchChannel t ht0 ht1 ell m)
  exact hmarg

/-- Forget the public branch mark. -/
noncomputable def erasePayoffMixTag
    {O : Type u} : RecordProcessor O PayoffMixTag PUnit :=
  fun _ => TraceableAgency.Dist.pure PUnit.unit

/-- Reconstruct the public branch from its conditional distribution given the
realized payoff.  Dependence on the payoff is permitted by A4. -/
noncomputable def reconstructPayoffMixTag
    {O : Type u} [Fintype O]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) :
    RecordProcessor O PUnit PayoffMixTag :=
  fun z => Channel.posterior (payoffMixBranchChannel ell m)
    (payoffMixWeights t ht0 ht1) z.1

theorem recordPostprocess_markedPayoffMix_erase
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) :
    recordPostprocess
        (markedPayoffMixChannel (A := A) t ht0 ht1 ell m)
        (erasePayoffMixTag (O := O)) =
      mixedPayoffLotteryChannel (A := A) t ht0 ht1 ell m := by
  classical
  ext a z
  rcases z with ⟨o, r⟩
  cases r
  simp only [recordPostprocess, Channel.postprocess,
    payoffPreservingRecordKernel, markedPayoffMixChannel,
    mixedPayoffLotteryChannel, payoffLotteryChannel,
    erasePayoffMixTag, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single o]
  · simp only [ite_true, TraceableAgency.Dist.pure_apply_self, mul_one]
    exact payoffMarginal_markedPayoffMixDist t ht0 ht1 ell m o
  · intro o' _ hone
    simp [hone.symm]
  · exact absurd (Finset.mem_univ o)

theorem recordPostprocess_mixedPayoffLottery_reconstruct
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) :
    recordPostprocess
        (mixedPayoffLotteryChannel (A := A) t ht0 ht1 ell m)
        (reconstructPayoffMixTag t ht0 ht1 ell m) =
      markedPayoffMixChannel (A := A) t ht0 ht1 ell m := by
  classical
  ext a z
  rcases z with ⟨o, b⟩
  simp only [recordPostprocess, Channel.postprocess,
    payoffPreservingRecordKernel, mixedPayoffLotteryChannel,
    payoffLotteryChannel, payoffLotteryRecordDist,
    reconstructPayoffMixTag, markedPayoffMixChannel,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single o]
  · simp only [ite_true, mul_one]
    have hbayes := posterior_mul_marginal
      (payoffMixWeights t ht0 ht1)
      (payoffMixBranchChannel ell m) o b
    rw [outcomeMarginal_payoffMixBranchChannel] at hbayes
    simpa using hbayes
  · intro o' _ hone
    simp [hone.symm]
  · exact absurd (Finset.mem_univ o)

theorem markedPayoffMix_mutualPairWeak
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : FixedPayoffPrefFamily O) (h4 : A4_RecordDataProcessing F)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O) (q : TraceableAgency.Dist A) :
    pairWeak F q (markedPayoffMixChannel t ht0 ht1 ell m)
        q (mixedPayoffLotteryChannel t ht0 ht1 ell m) ∧
      pairWeak F q (mixedPayoffLotteryChannel t ht0 ht1 ell m)
        q (markedPayoffMixChannel t ht0 ht1 ell m) := by
  constructor
  · simpa [recordPostprocess_markedPayoffMix_erase] using
      h4 (markedPayoffMixChannel (A := A) t ht0 ht1 ell m)
        (erasePayoffMixTag (O := O)) q
  · simpa [recordPostprocess_mixedPayoffLottery_reconstruct] using
      h4 (mixedPayoffLotteryChannel (A := A) t ht0 ht1 ell m)
        (reconstructPayoffMixTag t ht0 ht1 ell m) q

theorem rel_markedPayoffMix_iff_mixedPayoffLottery
    {O A : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell m : TraceableAgency.Dist O)
    (q r : TraceableAgency.Dist A) :
    F.rel (markedPayoffMixChannel t ht0 ht1 ell m) q r ↔
      F.rel (mixedPayoffLotteryChannel t ht0 ht1 ell m) q r := by
  exact fixed_rel_iff_of_mutualRecordProcessing F h1 h3 h4
    (markedPayoffMixChannel (A := A) t ht0 ht1 ell m)
    (mixedPayoffLotteryChannel (A := A) t ht0 ht1 ell m)
    (erasePayoffMixTag (O := O))
    (reconstructPayoffMixTag t ht0 ht1 ell m)
    (recordPostprocess_markedPayoffMix_erase t ht0 ht1 ell m)
    (recordPostprocess_mixedPayoffLottery_reconstruct t ht0 ht1 ell m)
    q r

/-! ## Transporting strict material anchors -/

/-- Strict comparison is preserved when its preferred endpoint is replaced by
a weakly better equivalent and its dispreferred endpoint by a weakly worse
equivalent.  Cross-environment transitivity and reverse orientation are the
derived results in `PairOrder.lean`. -/
theorem pairStrict_transport
    {O A B C D R S T U : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    [Fintype U] [DecidableEq U] [Nonempty U]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S))
    (q' : TraceableAgency.Dist C) (K' : Channel C (O × T))
    (p' : TraceableAgency.Dist D) (L' : Channel D (O × U))
    (hstrict : pairStrict F q K p L)
    (hq'_to_q : pairWeak F q' K' q K)
    (hp_to_p' : pairWeak F p L p' L') :
    pairStrict F q' K' p' L' := by
  rw [pairStrict_iff_pairWeak_not_swap F h.a1 h.a3 h.a4 h.a5] at hstrict ⊢
  rcases hstrict with ⟨hqp, hnotpq⟩
  constructor
  · have hq'p := pairWeak_transitive F h q' K' q K p L
      hq'_to_q hqp
    exact pairWeak_transitive F h q' K' p L p' L' hq'p hp_to_p'
  · intro hp'q'
    apply hnotpq
    have hpq' := pairWeak_transitive F h p L p' L' q' K'
      hp_to_p' hp'q'
    exact pairWeak_transitive F h p L q' K' q K hpq' hq'_to_q

theorem singletonPayoffLottery_pure_eq_deterministic
    {O : Type u} [Fintype O] [DecidableEq O]
    (o : O) :
    singletonPayoffLotteryChannel (TraceableAgency.Dist.pure o) =
      deterministicPayoffChannel o := by
  ext a z
  rcases z with ⟨o', r⟩
  cases a
  cases r
  simp [singletonPayoffLotteryChannel, payoffLotteryChannel,
    payoffLotteryRecordDist, deterministicPayoffChannel,
    TraceableAgency.Dist.pure_apply]

/-- The two A7 anchors strictly rank the corresponding action-independent
payoff lotteries for every pair of finite action alphabets and every pair of
priors. -/
theorem materialAnchors_strict_everyPrior
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    ∃ oplus ominus : O,
      ∀ {A B : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B),
        pairStrict F q
          (payoffLotteryChannel (TraceableAgency.Dist.pure oplus))
          p (payoffLotteryChannel (TraceableAgency.Dist.pure ominus)) := by
  obtain ⟨oplus, ominus, hanchor⟩ := h.a7
  refine ⟨oplus, ominus, ?_⟩
  intro A B _ _ _ _ _ _ q p
  have hsingleton :
      pairStrict F singletonActionPrior
          (singletonPayoffLotteryChannel (TraceableAgency.Dist.pure oplus))
        singletonActionPrior
          (singletonPayoffLotteryChannel (TraceableAgency.Dist.pure ominus)) := by
    rw [singletonPayoffLottery_pure_eq_deterministic,
      singletonPayoffLottery_pure_eq_deterministic]
    exact hanchor
  apply pairStrict_transport F h
    singletonActionPrior
      (singletonPayoffLotteryChannel (TraceableAgency.Dist.pure oplus))
    singletonActionPrior
      (singletonPayoffLotteryChannel (TraceableAgency.Dist.pure ominus))
    q (payoffLotteryChannel (TraceableAgency.Dist.pure oplus))
    p (payoffLotteryChannel (TraceableAgency.Dist.pure ominus))
    hsingleton
  · exact payoffLottery_pairWeak F h.a5
      (TraceableAgency.Dist.pure oplus) q singletonActionPrior
  · exact payoffLottery_pairWeak F h.a5
      (TraceableAgency.Dist.pure ominus) singletonActionPrior p

end TraceableAgency.Theorem1
