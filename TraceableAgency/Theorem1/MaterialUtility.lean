/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PayoffLotteries
import TraceableAgency.Theorem1.NormalizeAffine
import TraceableAgency.PureTrace.Support.GenericHersteinMilnor

/-!
# The common material utility scale

This file cardinalizes the singleton-action order on ordinary payoff
lotteries.  The public-mixture independence used by Herstein--Milnor is
derived from A6; A2 supplies the closed-segment calibration.  The normalized
affine representative is then expanded over the finite payoff simplex and
transported to arbitrary action alphabets by the exact A5 reports.
-/

namespace TraceableAgency.Theorem1

open Filter Set Topology
open TraceableAgency

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

/-! ## The payoff-lottery mixture order -/

/-- The global pair comparison, restricted to singleton-action ordinary
payoff lotteries. -/
def payoffLotteryRel (F : FixedPayoffPrefFamily O) :
    TraceableAgency.Dist O → TraceableAgency.Dist O → Prop :=
  fun ell m =>
    pairWeak F singletonActionPrior (singletonPayoffLotteryChannel ell)
      singletonActionPrior (singletonPayoffLotteryChannel m)

/-- Probability coordinates give the finite payoff simplex its abstract
convex mixture-space structure. -/
noncomputable def payoffLotteryMixtureSpace :
    AbstractConvexMixtureSpace (TraceableAgency.Dist O) where
  Coordinate := O
  coordinate := fun ell o => ell o
  coordinate_ext := by
    intro ell m h
    exact TraceableAgency.Dist.ext h
  mix := fun t ell m =>
    TraceableAgency.Dist.mix t.1 (le_of_lt t.2.1) (le_of_lt t.2.2) ell m
  coordinate_mix := by
    intro t ell m o
    rfl

@[simp]
theorem payoffLotteryMixtureSpace_mix
    (t : Set.Ioo (0 : ℝ) 1)
    (ell m : TraceableAgency.Dist O) :
    payoffLotteryMixtureSpace.mix t ell m =
      TraceableAgency.Dist.mix t.1 (le_of_lt t.2.1)
        (le_of_lt t.2.2) ell m :=
  rfl

theorem payoffLotteryRel_complete
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (ell m : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m ∨ payoffLotteryRel F m ell :=
  pairWeak_complete F h
    singletonActionPrior (singletonPayoffLotteryChannel ell)
    singletonActionPrior (singletonPayoffLotteryChannel m)

theorem payoffLotteryRel_transitive
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (ell m n : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m → payoffLotteryRel F m n →
      payoffLotteryRel F ell n :=
  pairWeak_transitive_sameAction F h
    singletonActionPrior (singletonPayoffLotteryChannel ell)
    singletonActionPrior (singletonPayoffLotteryChannel m)
    singletonActionPrior (singletonPayoffLotteryChannel n)

/-! ## A6 and the visible public coin -/

/-- The public coin, viewed as a first-stage singleton-action channel. -/
noncomputable def payoffMixFirstStage
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Channel PUnit.{u + 1} PayoffMixTag :=
  fun _ => payoffMixWeights t ht0 ht1

/-- Branch continuations: the left branch pays `ell`, and the right branch
pays the common background lottery `n`. -/
noncomputable def payoffMixContinuation
    (ell n : TraceableAgency.Dist O) (b : PayoffMixTag) :
    Channel PUnit.{u + 1} (O × PUnit.{u + 1}) :=
  if b.down then singletonPayoffLotteryChannel ell
  else singletonPayoffLotteryChannel n

/-- The A6 compound implementing a visible mixture of payoff lotteries. -/
noncomputable def payoffCompoundMixChannel
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell n : TraceableAgency.Dist O) :
    Channel PUnit.{u + 1} (O × ((b : PayoffMixTag) × PUnit.{u + 1})) :=
  commonPayoffCompound (fun _ : PayoffMixTag => PUnit.{u + 1})
    (payoffMixFirstStage t ht0 ht1) (payoffMixContinuation ell n)

@[simp]
theorem payoffCompoundMixChannel_apply
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell n : TraceableAgency.Dist O)
    (a : PUnit.{u + 1}) (o : O) (b : PayoffMixTag)
    (r : PUnit.{u + 1}) :
    payoffCompoundMixChannel t ht0 ht1 ell n a (o, ⟨b, r⟩) =
      payoffMixWeights t ht0 ht1 b *
        payoffMixBranchChannel ell n b o := by
  cases a
  cases r
  rcases b with ⟨b⟩
  cases b <;>
    simp [payoffCompoundMixChannel, commonPayoffCompound,
      payoffMixFirstStage, payoffMixContinuation,
      payoffMixBranchChannel, compoundPayoffRecordEquiv,
      Relabeling.relabelChannel, Relabeling.relabelDist,
      seqComposeDep, seqComposeDepProb, sigmaPayoffRecordEquiv]

/-- Delete the redundant unit record retained by the A6 compound. -/
noncomputable def erasePayoffCompoundUnit :
    RecordProcessor O ((b : PayoffMixTag) × PUnit.{u + 1}) PayoffMixTag :=
  fun z => TraceableAgency.Dist.pure z.2.1

/-- Reinsert the redundant unit record. -/
noncomputable def insertPayoffCompoundUnit :
    RecordProcessor O PayoffMixTag ((b : PayoffMixTag) × PUnit.{u + 1}) :=
  fun z => TraceableAgency.Dist.pure ⟨z.2, PUnit.unit⟩

theorem recordPostprocess_payoffCompoundMix_erase
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell n : TraceableAgency.Dist O) :
    recordPostprocess (payoffCompoundMixChannel t ht0 ht1 ell n)
        erasePayoffCompoundUnit =
      markedPayoffMixChannel t ht0 ht1 ell n := by
  classical
  ext a z
  rcases z with ⟨o, b⟩
  simp only [recordPostprocess, Channel.postprocess,
    payoffPreservingRecordKernel, erasePayoffCompoundUnit,
    markedPayoffMixChannel, TraceableAgency.Dist.pure_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single o]
  · rw [Fintype.sum_sigma]
    rw [Finset.sum_eq_single b]
    · simp [payoffCompoundMixChannel_apply]
    · intro b' _ hb'
      simp [hb'.symm]
    · exact absurd (Finset.mem_univ b)
  · intro o' _ ho'
    simp [ho'.symm]
  · exact absurd (Finset.mem_univ o)

theorem recordPostprocess_markedPayoffMix_insert
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell n : TraceableAgency.Dist O) :
    recordPostprocess (markedPayoffMixChannel t ht0 ht1 ell n)
        insertPayoffCompoundUnit =
      payoffCompoundMixChannel t ht0 ht1 ell n := by
  classical
  ext a z
  rcases z with ⟨o, br⟩
  rcases br with ⟨b, r⟩
  cases r
  simp [recordPostprocess, Channel.postprocess,
    payoffPreservingRecordKernel, insertPayoffCompoundUnit,
    markedPayoffMixChannel, Fintype.sum_prod_type,
    payoffCompoundMixChannel_apply,
    TraceableAgency.Dist.pure_apply]

theorem payoffCompoundMix_mutualPairWeak_marked
    (F : FixedPayoffPrefFamily O) (h4 : A4_RecordDataProcessing F)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ell n : TraceableAgency.Dist O) :
    pairWeak F singletonActionPrior
        (payoffCompoundMixChannel t ht0 ht1 ell n)
        singletonActionPrior
        (markedPayoffMixChannel t ht0 ht1 ell n) ∧
      pairWeak F singletonActionPrior
        (markedPayoffMixChannel t ht0 ht1 ell n)
        singletonActionPrior
        (payoffCompoundMixChannel t ht0 ht1 ell n) := by
  constructor
  · simpa [recordPostprocess_payoffCompoundMix_erase] using
      h4 (payoffCompoundMixChannel t ht0 ht1 ell n)
        erasePayoffCompoundUnit singletonActionPrior
  · simpa [recordPostprocess_markedPayoffMix_insert] using
      h4 (markedPayoffMixChannel (A := PUnit) t ht0 ht1 ell n)
        insertPayoffCompoundUnit singletonActionPrior

/-- The A6 compound and the ordinary, unmarked mixed payoff lottery are
mutually weakly equivalent. -/
theorem payoffCompoundMix_mutualPairWeak_ordinary
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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

theorem dist_punit_eq_singleton
    (q : TraceableAgency.Dist PUnit.{u + 1}) :
    q = singletonActionPrior := by
  ext a
  cases a
  simpa using q.sum_eq_one

theorem payoffMixFirstStage_left_positive
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    BranchPositive
      (payoffMixFirstStage t (le_of_lt ht0) (le_of_lt ht1))
      singletonActionPrior payoffMixLeft := by
  simp [BranchPositive, Channel.outcomeMarginal_apply,
    payoffMixFirstStage, singletonActionPrior]
  exact ht0

/-- The weak clause of A6 lifts a payoff-lottery comparison through the
visible public coin. -/
theorem payoffCompoundMix_pairWeak_of_base
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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

/-- The strict clause of A6 lifts a strict payoff-lottery comparison through
the positive left branch of the visible public coin. -/
theorem payoffCompoundMix_pairStrict_of_base
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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

/-- A6, including its strict clause, gives the two-way public-mixture
independence required by Herstein--Milnor. -/
theorem payoffLotteryRel_independence
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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
      exact pairStrict_transport F h
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

/-! ## A2 closedness and segment calibration -/

theorem payoffLotteryBlockChannel_converges
    (ellseq mseq : ℕ → TraceableAgency.Dist O)
    (ell m : TraceableAgency.Dist O)
    (hell : payoffLotteryMixtureSpace.Converges ellseq ell)
    (hm : payoffLotteryMixtureSpace.Converges mseq m) :
    ChannelConverges
      (fun k => commonPayoffBlockChannel
        (singletonPayoffLotteryChannel (ellseq k))
        (singletonPayoffLotteryChannel (mseq k)))
      (commonPayoffBlockChannel
        (singletonPayoffLotteryChannel ell)
        (singletonPayoffLotteryChannel m)) := by
  intro a z
  rcases z with ⟨o, rs⟩
  cases a with
  | inl a =>
      cases a
      cases rs with
      | inl r =>
          cases r
          simpa [commonPayoffBlockChannel, sumPayoffRecordEquiv,
            Relabeling.relabelChannel, Relabeling.relabelDist,
            blockChannel, singletonPayoffLotteryChannel,
            payoffLotteryChannel, payoffLotteryRecordDist,
            payoffLotteryMixtureSpace] using hell o
      | inr r =>
          cases r
          simp [commonPayoffBlockChannel, sumPayoffRecordEquiv,
            Relabeling.relabelChannel, Relabeling.relabelDist,
            blockChannel, singletonPayoffLotteryChannel,
            payoffLotteryChannel, payoffLotteryRecordDist]
  | inr a =>
      cases a
      cases rs with
      | inl r =>
          cases r
          simp [commonPayoffBlockChannel, sumPayoffRecordEquiv,
            Relabeling.relabelChannel, Relabeling.relabelDist,
            blockChannel, singletonPayoffLotteryChannel,
            payoffLotteryChannel, payoffLotteryRecordDist]
      | inr r =>
          cases r
          simpa [commonPayoffBlockChannel, sumPayoffRecordEquiv,
            Relabeling.relabelChannel, Relabeling.relabelDist,
            blockChannel, singletonPayoffLotteryChannel,
            payoffLotteryChannel, payoffLotteryRecordDist,
            payoffLotteryMixtureSpace] using hm o

/-- A2 closes the payoff-lottery order for pointwise probability-coordinate
convergence. -/
theorem payoffLotteryRel_sequentiallyClosed
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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

noncomputable def payoffLotteryContinuousIndependentWeakOrder
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    ContinuousIndependentWeakOrder payoffLotteryMixtureSpace
      (payoffLotteryRel F) where
  complete := payoffLotteryRel_complete F h
  transitive := payoffLotteryRel_transitive F h
  independence := payoffLotteryRel_independence F h
  sequentially_closed := payoffLotteryRel_sequentiallyClosed F h

/-- This is the exact A2 closed-segment calibration consumed by the generic
Herstein--Milnor construction. -/
theorem payoffLotteryRel_segmentCalibration
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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

noncomputable def payoffLotteryCalibratableWeakOrder
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    HMCalibratableWeakOrder payoffLotteryMixtureSpace
      (payoffLotteryRel F) where
  complete := payoffLotteryRel_complete F h
  transitive := payoffLotteryRel_transitive F h
  independence := payoffLotteryRel_independence F h
  segment_calibration := payoffLotteryRel_segmentCalibration F h

/-! ## Affine cardinalization and A7 normalization -/

theorem payoffLotteryAffineUtility_exists
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    Nonempty
      (AffineUtilityRepresentation payoffLotteryMixtureSpace
        (payoffLotteryRel F)) :=
  genericHersteinMilnorAffineUtility_of_calibratable
    payoffLotteryMixtureSpace (payoffLotteryRel F)
    (payoffLotteryCalibratableWeakOrder F h)

/-- The high material outcome selected from the A7 witness. -/
noncomputable def materialHighOutcome
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) : O :=
  Classical.choose h.a7

/-- The low material outcome paired with `materialHighOutcome` by A7. -/
noncomputable def materialLowOutcome
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) : O :=
  Classical.choose (Classical.choose_spec h.a7)

theorem materialChosenAnchors_pairStrict
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    pairStrict F singletonActionPrior
        (deterministicPayoffChannel (materialHighOutcome F h))
      singletonActionPrior
        (deterministicPayoffChannel (materialLowOutcome F h)) :=
  Classical.choose_spec (Classical.choose_spec h.a7)

theorem materialChosenAnchors_HMStrict
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
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

/-- An arbitrary affine representative supplied by the kernel-checked generic
Herstein--Milnor theorem. -/
noncomputable def materialRawAffineUtility
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    AffineUtilityRepresentation payoffLotteryMixtureSpace
      (payoffLotteryRel F) :=
  Classical.choice (payoffLotteryAffineUtility_exists F h)

/-- The canonical material representative, normalized to assign the chosen
A7 low/high outcomes values zero and one. -/
noncomputable def materialAffineUtility
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    AffineUtilityRepresentation payoffLotteryMixtureSpace
      (payoffLotteryRel F) :=
  normalizeAffineUtility (materialRawAffineUtility F h)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)

/-- The common material payoff index, obtained by evaluating the normalized
lottery representative at degenerate lotteries. -/
noncomputable def materialPayoffUtility
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) : O → ℝ :=
  fun o => (materialAffineUtility F h).utility
    (TraceableAgency.Dist.pure o)

@[simp]
theorem materialPayoffUtility_high
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    materialPayoffUtility F h (materialHighOutcome F h) = 1 := by
  exact normalizeAffineUtility_high
    (materialRawAffineUtility F h)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)

@[simp]
theorem materialAffineUtility_high
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    (materialAffineUtility F h).utility
        (TraceableAgency.Dist.pure (materialHighOutcome F h)) = 1 :=
  materialPayoffUtility_high F h

@[simp]
theorem materialPayoffUtility_low
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    materialPayoffUtility F h (materialLowOutcome F h) = 0 := by
  exact normalizeAffineUtility_low
    (materialRawAffineUtility F h)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)

@[simp]
theorem materialAffineUtility_low
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    (materialAffineUtility F h).utility
        (TraceableAgency.Dist.pure (materialLowOutcome F h)) = 0 :=
  materialPayoffUtility_low F h

theorem materialPayoffUtility_high_ne_low
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    materialPayoffUtility F h (materialHighOutcome F h) ≠
      materialPayoffUtility F h (materialLowOutcome F h) := by
  simp

theorem materialHighOutcome_ne_low
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    materialHighOutcome F h ≠ materialLowOutcome F h := by
  intro heq
  have hu := materialPayoffUtility_high_ne_low F h
  exact hu (congrArg (materialPayoffUtility F h) heq)

theorem materialPayoffUtility_nonconstant
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    ¬ IsConstantPayoffIndex (materialPayoffUtility F h) := by
  rintro ⟨c, hc⟩
  have hhigh := hc (materialHighOutcome F h)
  have hlow := hc (materialLowOutcome F h)
  rw [materialPayoffUtility_high] at hhigh
  rw [materialPayoffUtility_low] at hlow
  linarith

/-- The very same chosen A7 anchors are strict at every pair of priors and
finite nonempty action alphabets. -/
theorem materialChosenAnchors_strict_everyPrior
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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
  exact pairStrict_transport F h
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

/-! ## Finite affine expansion -/

/-- Delete one non-certain payoff and renormalize the remaining lottery. -/
noncomputable def payoffEraseNormalizeDist
    (ell : TraceableAgency.Dist O) (i : O) (hi : ell i < 1) :
    TraceableAgency.Dist O where
  prob := fun j => if j = i then 0 else ell j / (1 - ell i)
  nonneg := by
    intro j
    split_ifs
    · exact le_rfl
    · exact div_nonneg (ell.nonneg j) (by linarith)
  sum_eq_one := by
    have hden : 1 - ell i ≠ 0 := ne_of_gt (by linarith)
    have hsumErase :
        ∑ j ∈ (Finset.univ.erase i), ell j = 1 - ell i := by
      have hs := Finset.sum_erase_add
        (Finset.univ : Finset O) (fun j => ell j)
        (Finset.mem_univ i)
      rw [ell.sum_eq_one] at hs
      linarith
    calc
      (∑ j : O, if j = i then 0 else ell j / (1 - ell i)) =
          ∑ j ∈ (Finset.univ.erase i), ell j / (1 - ell i) := by
            rw [← Finset.sum_erase (Finset.univ : Finset O)
              (by simp : (if i = i then 0 else ell i / (1 - ell i)) = 0)]
            apply Finset.sum_congr rfl
            intro j hj
            simp [(Finset.mem_erase.mp hj).1]
      _ = (∑ j ∈ (Finset.univ.erase i), ell j) / (1 - ell i) := by
            rw [Finset.sum_div]
      _ = 1 := by
            rw [hsumErase, div_self hden]

@[simp]
theorem payoffEraseNormalizeDist_self
    (ell : TraceableAgency.Dist O) (i : O) (hi : ell i < 1) :
    payoffEraseNormalizeDist ell i hi i = 0 := by
  simp [payoffEraseNormalizeDist]

theorem payoffEraseNormalizeDist_apply_ne
    (ell : TraceableAgency.Dist O) (i j : O) (hi : ell i < 1)
    (hji : j ≠ i) :
    payoffEraseNormalizeDist ell i hi j = ell j / (1 - ell i) := by
  simp [payoffEraseNormalizeDist, hji]

private noncomputable def payoffLotterySupport
    (ell : TraceableAgency.Dist O) : Finset O :=
  Finset.univ.filter (fun i => ell i ≠ 0)

/-- Binary affinity on the payoff simplex evaluates every finite lottery as
the probability-weighted sum of its values on degenerate lotteries. -/
theorem affineUtility_payoffLotteryExpected
    (R : TraceableAgency.Dist O → TraceableAgency.Dist O → Prop)
    (rep : AffineUtilityRepresentation payoffLotteryMixtureSpace R)
    (ell : TraceableAgency.Dist O) :
    rep.utility ell =
      ∑ o : O, ell o * rep.utility (TraceableAgency.Dist.pure o) := by
  classical
  have hex : ∃ i : O, 0 < ell i := by
    by_contra hn
    push Not at hn
    have hz : ∀ i : O, ell i = 0 := fun i =>
      le_antisymm (hn i) (ell.nonneg i)
    have hs := ell.sum_eq_one
    simp [hz] at hs
  obtain ⟨i, hi⟩ := hex
  by_cases hiOne : ell i = 1
  · have hell : ell = TraceableAgency.Dist.pure i := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [hiOne]
      · have hsumErase :
            ∑ k ∈ (Finset.univ.erase i), ell k = 0 := by
          have hs := Finset.sum_erase_add
            (Finset.univ : Finset O) (fun k => ell k)
            (Finset.mem_univ i)
          rw [ell.sum_eq_one, hiOne] at hs
          linarith
        have hjle : ell j ≤ ∑ k ∈ (Finset.univ.erase i), ell k :=
          Finset.single_le_sum (fun k _ => ell.nonneg k)
            (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
        have hz : ell j = 0 :=
          le_antisymm (by linarith) (ell.nonneg j)
        simp [TraceableAgency.Dist.pure_apply_ne i j hji, hz]
    rw [hell, Fintype.sum_eq_single i]
    · simp
    · intro j hji
      simp [TraceableAgency.Dist.pure_apply_ne i j hji]
  · have hiLt : ell i < 1 :=
      lt_of_le_of_ne (TraceableAgency.Dist.prob_le_one ell i) hiOne
    let ell' := payoffEraseNormalizeDist ell i hiLt
    let ti : Set.Ioo (0 : ℝ) 1 := ⟨ell i, hi, hiLt⟩
    have hdecomp :
        payoffLotteryMixtureSpace.mix ti
            (TraceableAgency.Dist.pure i) ell' = ell := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [payoffLotteryMixtureSpace, ti, ell', hiLt]
      · rw [payoffLotteryMixtureSpace_mix,
          TraceableAgency.Dist.mix_apply,
          TraceableAgency.Dist.pure_apply_ne i j hji,
          payoffEraseNormalizeDist_apply_ne ell i j hiLt hji]
        have hden : 1 - ell i ≠ 0 := ne_of_gt (by linarith)
        dsimp [ti]
        field_simp [hden]
        ring
    have haff := rep.affine ti (TraceableAgency.Dist.pure i) ell'
    rw [hdecomp] at haff
    have hiMem : i ∈ payoffLotterySupport ell := by
      simp [payoffLotterySupport, ne_of_gt hi]
    have hsub :
        payoffLotterySupport ell' ⊆ (payoffLotterySupport ell).erase i := by
      intro j hj
      have hell'jne : ell' j ≠ 0 := by
        simpa [payoffLotterySupport] using hj
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hell'jne (payoffEraseNormalizeDist_self ell i hiLt)
      have helljne : ell j ≠ 0 := by
        intro hz
        apply hell'jne
        rw [payoffEraseNormalizeDist_apply_ne ell i j hiLt hji,
          hz, zero_div]
      exact Finset.mem_erase.mpr
        ⟨hji, by simpa [payoffLotterySupport] using helljne⟩
    have hcard :
        (payoffLotterySupport ell').card <
          (payoffLotterySupport ell).card :=
      lt_of_le_of_lt (Finset.card_le_card hsub)
        (Finset.card_erase_lt_of_mem hiMem)
    have hrec := affineUtility_payoffLotteryExpected R rep ell'
    rw [hrec] at haff
    have hsum :
        (∑ j : O,
          ell j * rep.utility (TraceableAgency.Dist.pure j)) =
          ell i * rep.utility (TraceableAgency.Dist.pure i) +
            (1 - ell i) *
              ∑ j : O,
                ell' j * rep.utility (TraceableAgency.Dist.pure j) := by
      let x : O → ℝ := fun j =>
        rep.utility (TraceableAgency.Dist.pure j)
      have hden : 1 - ell i ≠ 0 := ne_of_gt (by linarith)
      rw [← Finset.sum_erase_add (Finset.univ : Finset O)
        (fun j => ell j * x j) (Finset.mem_univ i)]
      rw [← Finset.sum_erase_add (Finset.univ : Finset O)
        (fun j => ell' j * x j) (Finset.mem_univ i)]
      have hself : ell' i = 0 :=
        payoffEraseNormalizeDist_self ell i hiLt
      rw [hself, zero_mul, add_zero]
      have hrest :
          ∑ j ∈ (Finset.univ.erase i), ell' j * x j =
            (∑ j ∈ (Finset.univ.erase i), ell j * x j) /
              (1 - ell i) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [payoffEraseNormalizeDist_apply_ne ell i j hiLt hji]
        ring
      rw [hrest]
      field_simp [hden]
      ring
    rw [hsum]
    exact haff
termination_by (payoffLotterySupport ell).card
decreasing_by exact hcard

theorem materialAffineUtility_eq_expected
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (ell : TraceableAgency.Dist O) :
    (materialAffineUtility F h).utility ell =
      payoffLotteryExpected (materialPayoffUtility F h) ell := by
  simpa [payoffLotteryExpected, materialPayoffUtility] using
    affineUtility_payoffLotteryExpected (payoffLotteryRel F)
      (materialAffineUtility F h) ell

/-! ## Common-scale representation at arbitrary priors -/

/-- Exact A5 reports identify the cross-environment payoff-lottery order with
the canonical singleton order. -/
theorem pairWeak_payoffLottery_iff_singletonRel
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (ell m : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m ↔
      payoffLotteryExpected (materialPayoffUtility F h) ell ≥
        payoffLotteryExpected (materialPayoffUtility F h) m := by
  rw [(materialAffineUtility F h).represents]
  rw [materialAffineUtility_eq_expected,
    materialAffineUtility_eq_expected]

/-- Every action-independent, uninformative-record payoff lottery is ordered
on the same normalized material scale, for arbitrary priors and finite
nonempty action alphabets. -/
theorem pairWeak_payoffLottery_iff_expectedMaterialUtility
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
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

end TraceableAgency.Theorem1
