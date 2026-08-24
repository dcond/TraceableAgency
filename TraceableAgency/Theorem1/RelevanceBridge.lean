/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PayoffLotteries
import TraceableAgency.Theorem1.FiniteBranchExtension
import TraceableAgency.PureTrace.Support.BranchAggregation.Reachability

/-!
# Fixed-channel relevance bridge

This file proves the v10 Appendix A relevance bridge.  Only A1 and A5--A8 are
used: the two fixed within-channel relevance comparisons are equivalent to
the environment forms consumed by the representation proof.  In the trace
part the payoff `ostar` is never changed; branch continuation transports the
fair binary comparison across priors, and exact action processors transport
it across nontrivial finite action alphabets.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u v

/-! ## Small exact action processors -/

noncomputable def pureActionProcessor
    {A : Type u} {B : Type v} [Fintype B] [DecidableEq B]
    (f : A → B) : Channel.ActionKernel A B :=
  fun a => TraceableAgency.Dist.pure (f a)

noncomputable def materialSelectProcessor
    (b : RelevanceBit) : Channel.ActionKernel PUnit RelevanceBit :=
  pureActionProcessor (fun _ => b)

noncomputable def collapseToUnitProcessor
    {A : Type u} : Channel.ActionKernel A PUnit :=
  pureActionProcessor (fun _ => PUnit.unit)

theorem actionPushforward_materialSelectProcessor
    (b : RelevanceBit) :
    Channel.actionPushforward (TraceableAgency.Dist.pure PUnit.unit)
        (materialSelectProcessor b) = TraceableAgency.Dist.pure b := by
  ext b'
  simp [Channel.actionPushforward, materialSelectProcessor,
    pureActionProcessor, TraceableAgency.Dist.pure_apply]

theorem actionPushforward_collapseToUnitProcessor
    {A : Type u} [Fintype A]
    (q : TraceableAgency.Dist A) :
    Channel.actionPushforward q (collapseToUnitProcessor (A := A)) =
      TraceableAgency.Dist.pure PUnit.unit := by
  ext a
  cases a
  simp [Channel.actionPushforward, collapseToUnitProcessor,
    pureActionProcessor, q.sum_eq_one]

theorem actionPushforward_pureActionProcessor_const
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (q : TraceableAgency.Dist A) (b : B) :
    Channel.actionPushforward q (pureActionProcessor (fun _ : A => b)) =
      TraceableAgency.Dist.pure b := by
  ext b'
  by_cases hb : b' = b
  · subst b'
    simp [Channel.actionPushforward, pureActionProcessor, q.sum_eq_one]
  · simp [Channel.actionPushforward, pureActionProcessor, hb]

theorem materialSelect_isActionProcessorCompletion
    {O : Type u} [Fintype O] [DecidableEq O]
    (oplus ominus : O) (b : RelevanceBit) :
    IsActionProcessorCompletion (deterministicPayoffChannel
        (if b.down then oplus else ominus))
      (TraceableAgency.Dist.pure PUnit.unit)
      (materialSelectProcessor b)
      (materialRelevanceBenchmarkChannel oplus ominus) := by
  intro b' z
  rw [show Channel.actionPushforward
      (TraceableAgency.Dist.pure PUnit.unit) (materialSelectProcessor b) b' =
      TraceableAgency.Dist.pure b b' by
    rw [actionPushforward_materialSelectProcessor]]
  by_cases hbb : b' = b
  · subst b'
    simp [materialSelectProcessor, pureActionProcessor,
      materialRelevanceBenchmarkChannel, deterministicPayoffChannel,
      TraceableAgency.Dist.pure_apply]
  · simp [materialSelectProcessor, pureActionProcessor,
      materialRelevanceBenchmarkChannel, deterministicPayoffChannel,
      TraceableAgency.Dist.pure_apply, hbb]

theorem materialCollapse_isActionProcessorCompletion
    {O : Type u} [Fintype O] [DecidableEq O]
    (oplus ominus : O) (b : RelevanceBit) :
    IsActionProcessorCompletion (materialRelevanceBenchmarkChannel oplus ominus)
      (TraceableAgency.Dist.pure b)
      collapseToUnitProcessor
      (deterministicPayoffChannel (if b.down then oplus else ominus)) := by
  intro a z
  cases a
  rw [show Channel.actionPushforward (TraceableAgency.Dist.pure b)
      collapseToUnitProcessor PUnit.unit =
      (TraceableAgency.Dist.pure PUnit.unit) PUnit.unit by
    rw [actionPushforward_collapseToUnitProcessor]]
  rw [Finset.sum_eq_single b]
  · simp [collapseToUnitProcessor, pureActionProcessor,
      materialRelevanceBenchmarkChannel, deterministicPayoffChannel,
      TraceableAgency.Dist.pure_apply]
  · intro b' _ hne
    simp [collapseToUnitProcessor, pureActionProcessor,
      TraceableAgency.Dist.pure_apply_ne _ _ hne]
  · exact absurd (Finset.mem_univ b)

/-! ## Material relevance -/

theorem materialRelevance_fixed_implies_environment
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h3 : A3_MaterialRelevance F) :
    MaterialRelevanceEnvironment F := by
  obtain ⟨oplus, ominus, _hne, hstrict⟩ := h3
  let K := materialRelevanceBenchmarkChannel oplus ominus
  let qplus := materialRelevanceBetterPrior
  let qminus := materialRelevanceWorsePrior
  have hpair : pairStrict F qplus K qminus K := by
    rw [pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7]
    exact ⟨(h5.duplication K qplus qminus).mp hstrict.1,
      fun hrev => hstrict.2 ((h5.duplication K qminus qplus).mpr hrev)⟩
  have hplus : pairWeak F
      (TraceableAgency.Dist.pure PUnit.unit)
        (deterministicPayoffChannel oplus) qplus K := by
    have hh := h7 (deterministicPayoffChannel oplus)
      (TraceableAgency.Dist.pure PUnit.unit)
      (materialSelectProcessor (ULift.up true)) K
      (materialSelect_isActionProcessorCompletion oplus ominus (ULift.up true))
    rw [actionPushforward_materialSelectProcessor] at hh
    exact hh
  have hminus : pairWeak F qminus K
      (TraceableAgency.Dist.pure PUnit.unit)
        (deterministicPayoffChannel ominus) := by
    have hh := h7 K qminus collapseToUnitProcessor
      (deterministicPayoffChannel ominus)
      (materialCollapse_isActionProcessorCompletion oplus ominus (ULift.up false))
    rw [actionPushforward_collapseToUnitProcessor] at hh
    exact hh
  exact ⟨oplus, ominus,
    pairStrict_transport_of_structural F h1 h5 h6 h7
      qplus K qminus K
      (TraceableAgency.Dist.pure PUnit.unit)
        (deterministicPayoffChannel oplus)
      (TraceableAgency.Dist.pure PUnit.unit)
        (deterministicPayoffChannel ominus)
      hpair hplus hminus⟩

theorem materialRelevance_environment_implies_fixed
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (henv : MaterialRelevanceEnvironment F) :
    A3_MaterialRelevance F := by
  obtain ⟨oplus, ominus, hstrict⟩ := henv
  let K := materialRelevanceBenchmarkChannel oplus ominus
  let qplus := materialRelevanceBetterPrior
  let qminus := materialRelevanceWorsePrior
  have hplus : pairWeak F qplus K
      (TraceableAgency.Dist.pure PUnit.unit)
        (deterministicPayoffChannel oplus) := by
    have hh := h7 K qplus collapseToUnitProcessor
      (deterministicPayoffChannel oplus)
      (materialCollapse_isActionProcessorCompletion oplus ominus (ULift.up true))
    rw [actionPushforward_collapseToUnitProcessor] at hh
    exact hh
  have hminus : pairWeak F
      (TraceableAgency.Dist.pure PUnit.unit)
        (deterministicPayoffChannel ominus) qminus K := by
    have hh := h7 (deterministicPayoffChannel ominus)
      (TraceableAgency.Dist.pure PUnit.unit)
      (materialSelectProcessor (ULift.up false)) K
      (materialSelect_isActionProcessorCompletion oplus ominus (ULift.up false))
    rw [actionPushforward_materialSelectProcessor] at hh
    exact hh
  have hpair := pairStrict_transport_of_structural F h1 h5 h6 h7
    (TraceableAgency.Dist.pure PUnit.unit)
      (deterministicPayoffChannel oplus)
    (TraceableAgency.Dist.pure PUnit.unit)
      (deterministicPayoffChannel ominus)
      qplus K qminus K hstrict hplus hminus
  rw [pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7] at hpair
  have hfixed : F.strictRel K qplus qminus := by
    constructor
    · exact (h5.duplication K qplus qminus).mpr hpair.1
    · intro hrev
      exact hpair.2 ((h5.duplication K qminus qplus).mp hrev)
  have hne : oplus ≠ ominus := by
    intro hoeq
    subst ominus
    have hbackPair : pairWeak F qminus K qplus K := by
      have hpush : Channel.actionPushforward qminus
          (pureActionProcessor (fun _ : RelevanceBit => ULift.up true)) = qplus := by
        simpa [qplus, materialRelevanceBetterPrior] using
          (actionPushforward_pureActionProcessor_const qminus (ULift.up true))
      rw [← hpush]
      apply h7 K qminus
        (pureActionProcessor (fun _ : RelevanceBit => ULift.up true)) K
      intro b z
      rw [hpush]
      by_cases hb : b = ULift.up true
      · subst b
        change qplus (ULift.up true) * K (ULift.up true) z =
          ∑ x, qminus x * 1 * K x z
        simp only [qplus, materialRelevanceBetterPrior,
          TraceableAgency.Dist.pure_apply_self, one_mul]
        have hrow : ∀ x : RelevanceBit, K x z = K (ULift.up true) z := by
          intro x
          simp [K, materialRelevanceBenchmarkChannel]
        simp_rw [hrow]
        rw [← Finset.sum_mul]
        simp_rw [mul_one]
        rw [qminus.sum_eq_one, one_mul]
      · have hqb : qplus b = 0 := by
          dsimp [qplus, materialRelevanceBetterPrior]
          exact TraceableAgency.Dist.pure_apply_ne _ _ hb
        rw [hqb, zero_mul]
        symm
        apply Finset.sum_eq_zero
        intro a _
        simp [pureActionProcessor, hb]
    exact hfixed.2 ((h5.duplication K qminus qplus).mpr hbackPair)
  exact ⟨oplus, ominus, hne, by simpa [K] using hfixed⟩

theorem materialRelevance_bridge
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F) :
    A3_MaterialRelevance F ↔ MaterialRelevanceEnvironment F :=
  ⟨materialRelevance_fixed_implies_environment F h1 h5 h6 h7,
    materialRelevance_environment_implies_fixed F h1 h5 h6 h7⟩

/-! ## The fair binary trace comparison inside the fixed A4 channel -/

/-- A constant-payoff channel whose explicit record is an independent fair
bit.  Unlike the one-point uninformative channel, it has the same record type
as full revelation and is therefore convenient under A8. -/
noncomputable def fairIndependentAtPayoff
    {O A : Type u} [Fintype O] [DecidableEq O] [Fintype A]
    (ostar : O) : Channel A (O × RelevanceBit) :=
  fun _ =>
    { prob := fun z => if z.1 = ostar then traceRelevanceFairPrior z.2 else 0
      nonneg := fun z => by
        split_ifs
        · exact traceRelevanceFairPrior.nonneg z.2
        · exact le_rfl
      sum_eq_one := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single ostar]
        · simpa using traceRelevanceFairPrior.sum_eq_one
        · intro o _ ho
          simp [ho]
        · simp }

noncomputable def traceSideProjectionProcessor :
    Channel.ActionKernel (RelevanceBit ⊕ RelevanceBit) RelevanceBit :=
  pureActionProcessor (Sum.elim id id)

noncomputable def traceLeftInclusionProcessor :
    Channel.ActionKernel RelevanceBit (RelevanceBit ⊕ RelevanceBit) :=
  pureActionProcessor Sum.inl

theorem actionPushforward_traceLeftInclusion :
    Channel.actionPushforward traceRelevanceFairPrior
        traceLeftInclusionProcessor = traceRelevanceRevealingPrior := by
  ext a
  cases a with
  | inl b =>
      simp [Channel.actionPushforward, traceLeftInclusionProcessor,
        pureActionProcessor, traceRelevanceRevealingPrior,
        TraceableAgency.Dist.pure_apply]
  | inr b =>
      simp [Channel.actionPushforward, traceLeftInclusionProcessor,
        pureActionProcessor, traceRelevanceRevealingPrior,
        TraceableAgency.Dist.pure_apply]

theorem actionPushforward_traceSideProjection_right :
    Channel.actionPushforward traceRelevanceUnrevealingPrior
        traceSideProjectionProcessor = traceRelevanceFairPrior := by
  ext b
  simp only [Channel.actionPushforward, traceRelevanceUnrevealingPrior,
    Fintype.sum_sum_type, inrDist_apply_inl, zero_mul, Finset.sum_const_zero,
    zero_add, inrDist_apply_inr, traceSideProjectionProcessor,
    pureActionProcessor, Sum.elim_inr]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne
    simp [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm]
  · exact absurd (Finset.mem_univ b)

theorem traceLeftInclusion_isActionProcessorCompletion
    {O : Type u} [Fintype O] [DecidableEq O] (ostar : O) :
    IsActionProcessorCompletion (fullRevealAtPayoff ostar)
      traceRelevanceFairPrior traceLeftInclusionProcessor
      (traceRelevanceBenchmarkChannel ostar) := by
  intro a z
  rw [show Channel.actionPushforward traceRelevanceFairPrior
      traceLeftInclusionProcessor a = traceRelevanceRevealingPrior a by
    rw [actionPushforward_traceLeftInclusion]]
  cases a with
  | inl b =>
      rw [Finset.sum_eq_single b]
      · simp [traceRelevanceRevealingPrior, traceLeftInclusionProcessor,
          pureActionProcessor, traceRelevanceBenchmarkChannel,
          fullRevealAtPayoff]
      · intro b' _ hne
        have hinj : Sum.inl b' ≠ (Sum.inl b : RelevanceBit ⊕ RelevanceBit) := by
          intro hh
          exact hne (Sum.inl.inj hh)
        change traceRelevanceFairPrior b' *
          (TraceableAgency.Dist.pure (Sum.inl b')) (Sum.inl b) *
          (fullRevealAtPayoff ostar b') z = 0
        rw [TraceableAgency.Dist.pure_apply_ne _ _ hinj.symm]
        ring
      · exact absurd (Finset.mem_univ b)
  | inr b =>
      simp [traceRelevanceRevealingPrior, traceLeftInclusionProcessor,
        pureActionProcessor]

theorem traceSideProjectionRight_isActionProcessorCompletion
    {O : Type u} [Fintype O] [DecidableEq O] (ostar : O) :
    IsActionProcessorCompletion
      (traceRelevanceBenchmarkChannel (O := O) ostar)
      (traceRelevanceUnrevealingPrior :
        TraceableAgency.Dist (RelevanceBit.{u} ⊕ RelevanceBit.{u}))
      (traceSideProjectionProcessor : Channel.ActionKernel
        (RelevanceBit.{u} ⊕ RelevanceBit.{u}) RelevanceBit.{u})
      (fairIndependentAtPayoff (O := O) (A := RelevanceBit.{u}) ostar) := by
  intro b z
  rw [show Channel.actionPushforward traceRelevanceUnrevealingPrior
      traceSideProjectionProcessor b = traceRelevanceFairPrior b by
    rw [actionPushforward_traceSideProjection_right]]
  simp only [traceRelevanceUnrevealingPrior, Fintype.sum_sum_type,
    inrDist_apply_inl, zero_mul, traceSideProjectionProcessor,
    pureActionProcessor, Sum.elim_inl, Sum.elim_inr, inrDist_apply_inr]
  have hsum :
      (∑ x : RelevanceBit,
          traceRelevanceFairPrior x * (TraceableAgency.Dist.pure x) b) =
        traceRelevanceFairPrior b := by
    rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hne
      simp [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm]
    · exact absurd (Finset.mem_univ b)
  by_cases hz : z.1 = ostar
  · simp only [traceRelevanceBenchmarkChannel, fairIndependentAtPayoff,
      hz, if_true]
    simp only [Finset.sum_const_zero, zero_add, id_eq]
    rw [← Finset.sum_mul, hsum]
  · simp [traceRelevanceBenchmarkChannel, fairIndependentAtPayoff, hz]

theorem traceRelevance_fixed_implies_fairBinary
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h4 : A4_TraceRelevance F) :
    ∃ ostar : O,
      pairStrict F traceRelevanceFairPrior (fullRevealAtPayoff ostar)
        traceRelevanceFairPrior
          (fairIndependentAtPayoff (A := RelevanceBit) ostar) := by
  obtain ⟨ostar, hstrict⟩ := h4
  let K := traceRelevanceBenchmarkChannel ostar
  let qR := traceRelevanceRevealingPrior
  let qU := traceRelevanceUnrevealingPrior
  have hpair : pairStrict F qR K qU K := by
    rw [pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7]
    exact ⟨(h5.duplication K qR qU).mp hstrict.1,
      fun hrev => hstrict.2 ((h5.duplication K qU qR).mpr hrev)⟩
  have hleft : pairWeak F traceRelevanceFairPrior
      (fullRevealAtPayoff ostar) qR K := by
    have hh := h7 (fullRevealAtPayoff ostar) traceRelevanceFairPrior
      traceLeftInclusionProcessor K
      (traceLeftInclusion_isActionProcessorCompletion ostar)
    rw [actionPushforward_traceLeftInclusion] at hh
    exact hh
  have hright : pairWeak F qU K traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar) := by
    have hh := h7 K qU traceSideProjectionProcessor
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)
      (traceSideProjectionRight_isActionProcessorCompletion ostar)
    rw [actionPushforward_traceSideProjection_right] at hh
    exact hh
  exact ⟨ostar, pairStrict_transport_of_structural F h1 h5 h6 h7
    qR K qU K
    traceRelevanceFairPrior (fullRevealAtPayoff ostar)
    traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)
    hpair hleft hright⟩

/-! ## Transport from the binary alphabet to an arbitrary nontrivial alphabet -/

def relevanceBitEmbed {A : Type u} (a0 a1 : A) : RelevanceBit.{u} → A :=
  fun b => if b.down then a1 else a0

def relevanceBitRetract {A : Type u} [DecidableEq A] (_a0 a1 : A) :
    A → RelevanceBit.{u} :=
  fun a => ULift.up (a = a1)

theorem relevanceBitRetract_embed {A : Type u} [DecidableEq A]
    (a0 a1 : A) (hne : a0 ≠ a1) (b : RelevanceBit.{u}) :
    relevanceBitRetract a0 a1 (relevanceBitEmbed a0 a1 b) = b := by
  cases b with
  | up b =>
      cases b <;> simp [relevanceBitRetract, relevanceBitEmbed, hne]

noncomputable def embeddedFairPrior {A : Type u}
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) : TraceableAgency.Dist A :=
  Channel.actionPushforward traceRelevanceFairPrior
    (pureActionProcessor (relevanceBitEmbed a0 a1) :
      Channel.ActionKernel RelevanceBit.{u} A)

noncomputable def traceRetractionProcessor {A : Type u}
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) : Channel.ActionKernel A RelevanceBit.{u} :=
  pureActionProcessor (relevanceBitRetract a0 a1)

noncomputable def traceEmbeddingProcessor {A : Type u}
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) : Channel.ActionKernel RelevanceBit.{u} A :=
  pureActionProcessor (relevanceBitEmbed a0 a1)

theorem actionPushforward_embeddedFair_retract {A : Type u}
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) (hne : a0 ≠ a1) :
    Channel.actionPushforward (embeddedFairPrior a0 a1)
        (traceRetractionProcessor a0 a1) = traceRelevanceFairPrior := by
  rw [show Channel.actionPushforward (embeddedFairPrior a0 a1)
      (traceRetractionProcessor a0 a1) =
      Channel.actionPushforward traceRelevanceFairPrior
        (pureActionProcessor (fun b : RelevanceBit.{u} =>
          relevanceBitRetract a0 a1 (relevanceBitEmbed a0 a1 b))) by
    change Channel.actionPushforward
        (Channel.actionPushforward traceRelevanceFairPrior
          (fun b => TraceableAgency.Dist.pure (relevanceBitEmbed a0 a1 b)))
        (fun a => TraceableAgency.Dist.pure (relevanceBitRetract a0 a1 a)) =
      Channel.actionPushforward traceRelevanceFairPrior
        (fun b => TraceableAgency.Dist.pure
          (relevanceBitRetract a0 a1 (relevanceBitEmbed a0 a1 b)))
    exact actionPushforward_pure_comp
      (traceRelevanceFairPrior : TraceableAgency.Dist RelevanceBit.{u})
      (relevanceBitEmbed a0 a1) (relevanceBitRetract a0 a1)]
  have hfun : (fun b : RelevanceBit.{u} =>
      relevanceBitRetract a0 a1 (relevanceBitEmbed a0 a1 b)) = id := by
    funext b
    exact relevanceBitRetract_embed a0 a1 hne b
  rw [hfun]
  ext b
  change (∑ b' : RelevanceBit.{u},
      traceRelevanceFairPrior b' * (TraceableAgency.Dist.pure b') b) =
    traceRelevanceFairPrior b
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne'
    simp [TraceableAgency.Dist.pure_apply_ne _ _ hne'.symm]
  · exact absurd (Finset.mem_univ b)

theorem actionPushforward_fair_embed {A : Type u}
    [Fintype A] [DecidableEq A] (a0 a1 : A) :
    Channel.actionPushforward traceRelevanceFairPrior
        (traceEmbeddingProcessor a0 a1) = embeddedFairPrior a0 a1 := rfl

noncomputable def embeddedFullAtPayoff
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) (ostar : O) : Channel RelevanceBit (O × A) :=
  fun b => TraceableAgency.Dist.pure (ostar, relevanceBitEmbed a0 a1 b)

theorem traceRetraction_isActionProcessorCompletion
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) (hne : a0 ≠ a1) (ostar : O) :
    IsActionProcessorCompletion (fullRevealAtPayoff ostar)
      (embeddedFairPrior a0 a1) (traceRetractionProcessor a0 a1)
      (embeddedFullAtPayoff a0 a1 ostar) := by
  intro b z
  rw [show Channel.actionPushforward (embeddedFairPrior a0 a1)
      (traceRetractionProcessor a0 a1) b = traceRelevanceFairPrior b by
    rw [actionPushforward_embeddedFair_retract a0 a1 hne]]
  change traceRelevanceFairPrior b *
      (TraceableAgency.Dist.pure
        (ostar, relevanceBitEmbed a0 a1 b)) z =
    ∑ a : A,
      (∑ c : RelevanceBit,
        traceRelevanceFairPrior c *
          (TraceableAgency.Dist.pure (relevanceBitEmbed a0 a1 c)) a) *
      (TraceableAgency.Dist.pure (relevanceBitRetract a0 a1 a)) b *
      (TraceableAgency.Dist.pure (ostar, a)) z
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinner : ∀ c : RelevanceBit,
      (∑ a : A,
        traceRelevanceFairPrior c *
          (TraceableAgency.Dist.pure (relevanceBitEmbed a0 a1 c)) a *
          (TraceableAgency.Dist.pure (relevanceBitRetract a0 a1 a)) b *
          (TraceableAgency.Dist.pure (ostar, a)) z) =
        traceRelevanceFairPrior c *
          (TraceableAgency.Dist.pure c) b *
          (TraceableAgency.Dist.pure
            (ostar, relevanceBitEmbed a0 a1 c)) z := by
    intro c
    rw [Finset.sum_eq_single (relevanceBitEmbed a0 a1 c)]
    · rw [TraceableAgency.Dist.pure_apply_self,
        relevanceBitRetract_embed a0 a1 hne]
      ring
    · intro a _ haneq
      rw [TraceableAgency.Dist.pure_apply_ne _ _ haneq]
      ring
    · exact absurd (Finset.mem_univ _)
  simp_rw [hinner]
  rw [Finset.sum_eq_single b]
  · rw [TraceableAgency.Dist.pure_apply_self]
    ring
  · intro c _ hcne
    rw [TraceableAgency.Dist.pure_apply_ne _ _ hcne.symm]
    ring
  · exact absurd (Finset.mem_univ b)

theorem traceEmbedding_isActionProcessorCompletion
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) (ostar : O) :
    IsActionProcessorCompletion
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)
      traceRelevanceFairPrior (traceEmbeddingProcessor a0 a1)
      (fairIndependentAtPayoff (A := A) ostar) := by
  intro a z
  simp only [traceEmbeddingProcessor, pureActionProcessor]
  change embeddedFairPrior a0 a1 a *
      (if z.1 = ostar then traceRelevanceFairPrior z.2 else 0) =
    ∑ b : RelevanceBit,
      traceRelevanceFairPrior b *
        (TraceableAgency.Dist.pure (relevanceBitEmbed a0 a1 b)) a *
        (if z.1 = ostar then traceRelevanceFairPrior z.2 else 0)
  unfold embeddedFairPrior Channel.actionPushforward
  simp only [pureActionProcessor]
  rw [Finset.sum_mul]

noncomputable def embeddedRecordRetractProcessor
    {O A : Type u} [Fintype A] [DecidableEq A]
    (a0 a1 : A) : RecordProcessor O A RelevanceBit :=
  fun z => TraceableAgency.Dist.pure (relevanceBitRetract a0 a1 z.2)

theorem recordPostprocess_embeddedFull_retract
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (a0 a1 : A) (hne : a0 ≠ a1) (ostar : O) :
    recordPostprocess (embeddedFullAtPayoff a0 a1 ostar)
        (embeddedRecordRetractProcessor a0 a1) =
      fullRevealAtPayoff ostar := by
  ext b z
  rcases z with ⟨o, r⟩
  simp only [recordPostprocess, payoffPreservingRecordKernel,
    embeddedFullAtPayoff, embeddedRecordRetractProcessor,
    fullRevealAtPayoff, Channel.postprocess, Fintype.sum_prod_type,
    TraceableAgency.Dist.pure_apply]
  rw [Finset.sum_eq_single ostar]
  · rw [Finset.sum_eq_single (relevanceBitEmbed a0 a1 b)]
    · rw [relevanceBitRetract_embed a0 a1 hne]
      by_cases ho : o = ostar <;> by_cases hr : r = b <;> simp [ho, hr]
    · intro a _ haneq
      simp [haneq]
    · exact absurd (Finset.mem_univ _)
  · intro o' _ hone
    simp [hone]
  · exact absurd (Finset.mem_univ _)

theorem fairBinaryTrace_implies_embeddedTrace
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (ostar : O)
    (hfair : pairStrict F traceRelevanceFairPrior
      (fullRevealAtPayoff ostar) traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar))
    (a0 a1 : A) (hne : a0 ≠ a1) :
    pairStrict F (embeddedFairPrior a0 a1) (fullRevealAtPayoff ostar)
      (embeddedFairPrior a0 a1)
        (fairIndependentAtPayoff (A := A) ostar) := by
  let r := embeddedFairPrior a0 a1
  have hleftProcess : pairWeak F r (fullRevealAtPayoff ostar)
      traceRelevanceFairPrior (embeddedFullAtPayoff a0 a1 ostar) := by
    have hh := h7 (fullRevealAtPayoff ostar) r
      (traceRetractionProcessor a0 a1)
      (embeddedFullAtPayoff a0 a1 ostar)
      (traceRetraction_isActionProcessorCompletion a0 a1 hne ostar)
    rw [actionPushforward_embeddedFair_retract a0 a1 hne] at hh
    exact hh
  have hleftRecord : pairWeak F traceRelevanceFairPrior
      (embeddedFullAtPayoff a0 a1 ostar)
      traceRelevanceFairPrior (fullRevealAtPayoff ostar) := by
    have hh := h6 (embeddedFullAtPayoff a0 a1 ostar)
      (embeddedRecordRetractProcessor a0 a1) traceRelevanceFairPrior
    rw [recordPostprocess_embeddedFull_retract a0 a1 hne ostar] at hh
    exact hh
  have hleft : pairWeak F r (fullRevealAtPayoff ostar)
      traceRelevanceFairPrior (fullRevealAtPayoff ostar) :=
    pairWeak_transitive_of_structural F h1 h5
      r (fullRevealAtPayoff ostar)
      traceRelevanceFairPrior (embeddedFullAtPayoff a0 a1 ostar)
      traceRelevanceFairPrior (fullRevealAtPayoff ostar)
      hleftProcess hleftRecord
  have hright : pairWeak F traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)
      r (fairIndependentAtPayoff (A := A) ostar) := by
    have hh := h7 (fairIndependentAtPayoff (A := RelevanceBit) ostar)
      traceRelevanceFairPrior (traceEmbeddingProcessor a0 a1)
      (fairIndependentAtPayoff (A := A) ostar)
      (traceEmbedding_isActionProcessorCompletion a0 a1 ostar)
    rw [actionPushforward_fair_embed] at hh
    exact hh
  exact pairStrict_transport_of_structural F h1 h5 h6 h7
    traceRelevanceFairPrior (fullRevealAtPayoff ostar)
    traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)
    r (fullRevealAtPayoff ostar) r
      (fairIndependentAtPayoff (A := A) ostar)
    hfair hleft hright

noncomputable def embeddedIndependentAtPayoff
    {O A B : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype B]
    (d : TraceableAgency.Dist B) (ostar : O) : Channel A (O × B) :=
  fun _ =>
    { prob := fun z => if z.1 = ostar then d z.2 else 0
      nonneg := fun z => by
        split_ifs
        · exact d.nonneg z.2
        · exact le_rfl
      sum_eq_one := by
        rw [Fintype.sum_prod_type, Finset.sum_eq_single ostar]
        · simpa using d.sum_eq_one
        · intro o _ ho
          simp [ho]
        · simp }

noncomputable def embeddedFairRecordProcessor
    {O A : Type u} [Fintype A] [DecidableEq A]
    (a0 a1 : A) : RecordProcessor O RelevanceBit A :=
  fun z => TraceableAgency.Dist.pure (relevanceBitEmbed a0 a1 z.2)

theorem recordPostprocess_fairIndependent_embed
    {O A B : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype B] [DecidableEq B]
    (a0 a1 : B) (ostar : O) :
    recordPostprocess (fairIndependentAtPayoff (A := A) ostar)
        (embeddedFairRecordProcessor a0 a1) =
      embeddedIndependentAtPayoff (A := A) (embeddedFairPrior a0 a1) ostar := by
  ext a z
  rcases z with ⟨o, b⟩
  simp only [recordPostprocess, payoffPreservingRecordKernel,
    fairIndependentAtPayoff, embeddedFairRecordProcessor,
    embeddedIndependentAtPayoff, Channel.postprocess,
    Fintype.sum_prod_type]
  by_cases ho : o = ostar
  · subst o
    rw [Finset.sum_eq_single ostar]
    · unfold embeddedFairPrior Channel.actionPushforward
      simp only [pureActionProcessor, if_true]
    · intro o' _ hone
      simp [hone]
    · exact absurd (Finset.mem_univ _)
  · simp [ho]

theorem embeddedTrace_with_commonRecord
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (ostar : O) (a0 a1 : A)
    (hstrict : pairStrict F (embeddedFairPrior a0 a1)
      (fullRevealAtPayoff ostar) (embeddedFairPrior a0 a1)
      (fairIndependentAtPayoff (A := A) ostar)) :
    pairStrict F (embeddedFairPrior a0 a1) (fullRevealAtPayoff ostar)
      (embeddedFairPrior a0 a1)
        (embeddedIndependentAtPayoff (A := A)
          (embeddedFairPrior a0 a1) ostar) := by
  let r := embeddedFairPrior a0 a1
  have hself : pairWeak F r (fullRevealAtPayoff ostar)
      r (fullRevealAtPayoff ostar) := by
    have hrel : F.rel (fullRevealAtPayoff ostar) r r := by
      rcases (h1 (fullRevealAtPayoff ostar)).1 r r with hh | hh <;> exact hh
    exact (h5.duplication (fullRevealAtPayoff ostar) r r).mp hrel
  have hright : pairWeak F r (fairIndependentAtPayoff (A := A) ostar)
      r (embeddedIndependentAtPayoff (A := A) r ostar) := by
    have hh := h6 (fairIndependentAtPayoff (A := A) ostar)
      (embeddedFairRecordProcessor a0 a1) r
    rw [recordPostprocess_fairIndependent_embed] at hh
    exact hh
  exact pairStrict_transport_of_structural F h1 h5 h6 h7
    r (fullRevealAtPayoff ostar)
    r (fairIndependentAtPayoff (A := A) ostar)
    r (fullRevealAtPayoff ostar)
    r (embeddedIndependentAtPayoff (A := A) r ostar)
    hstrict hself hright

/-! ## Branch transport from the embedded comparison to every full-support prior -/

noncomputable def redrawRecordProcessor
    {O R S : Type u} [Fintype S]
    (d : TraceableAgency.Dist S) : RecordProcessor O R S :=
  fun _ => d

theorem recordPostprocess_fullReveal_redraw
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    (d : TraceableAgency.Dist A) (ostar : O) :
    recordPostprocess (fullRevealAtPayoff (A := A) ostar)
        (redrawRecordProcessor d) =
      embeddedIndependentAtPayoff (A := A) d ostar := by
  ext a z
  rcases z with ⟨o, r⟩
  simp only [recordPostprocess, payoffPreservingRecordKernel,
    fullRevealAtPayoff, redrawRecordProcessor,
    embeddedIndependentAtPayoff, Channel.postprocess,
    Fintype.sum_prod_type, TraceableAgency.Dist.pure_apply]
  rw [Finset.sum_eq_single ostar]
  · rw [Finset.sum_eq_single a]
    · by_cases ho : o = ostar <;> simp [ho]
    · intro a' _ hne
      simp [hne]
    · exact absurd (Finset.mem_univ _)
  · intro o' _ hne
    simp [hne]
  · exact absurd (Finset.mem_univ _)

noncomputable def branchTaggedRevealProcessor
    {O A Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A Y) : RecordProcessor O A ((_y : Y) × A) :=
  fun z =>
    { prob := fun ya => if ya.2 = z.2 then P z.2 ya.1 else 0
      nonneg := fun ya => by
        split_ifs
        · exact (P z.2).nonneg ya.1
        · exact le_rfl
      sum_eq_one := by
        rw [Fintype.sum_sigma]
        have hrow : ∀ y : Y,
            (∑ a' : A, if a' = z.2 then P z.2 y else 0) = P z.2 y := by
          intro y
          rw [Finset.sum_eq_single z.2]
          · simp
          · intro a' _ hne
            simp [hne]
          · exact absurd (Finset.mem_univ _)
        simp_rw [hrow]
        exact (P z.2).sum_eq_one }

theorem recordPostprocess_fullReveal_branchTagged
    {O A Y : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A Y) (ostar : O) :
    recordPostprocess (fullRevealAtPayoff (A := A) ostar)
        (branchTaggedRevealProcessor P) =
      commonPayoffCompound (fun _ : Y => A) P
        (fun _ => fullRevealAtPayoff ostar) := by
  ext a z
  rcases z with ⟨o, y, r⟩
  simp [recordPostprocess, payoffPreservingRecordKernel,
    fullRevealAtPayoff, branchTaggedRevealProcessor,
    commonPayoffCompound, compoundPayoffRecordEquiv,
    sigmaPayoffRecordEquiv, Channel.postprocess, seqComposeDep,
    seqComposeDepProb,
    Relabeling.relabelChannel, Relabeling.relabelDist,
    Fintype.sum_prod_type, TraceableAgency.Dist.pure_apply]
  by_cases h : o = ostar ∧ r = a
  · rcases h with ⟨rfl, rfl⟩
    simp
  · simp [h]

noncomputable def eraseAllRecordsProcessor
    {O R : Type u} : RecordProcessor O R PUnit :=
  fun _ => TraceableAgency.Dist.pure PUnit.unit

theorem recordPostprocess_compoundIndependent_erase
    {O A Y R : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype Y] [DecidableEq Y]
    [Fintype R] [DecidableEq R]
    (P : Channel A Y) (d : TraceableAgency.Dist R) (ostar : O) :
    recordPostprocess
        (commonPayoffCompound (fun _ : Y => R) P
          (fun _ => embeddedIndependentAtPayoff (A := A) d ostar))
        eraseAllRecordsProcessor =
      uninformativeAtPayoff (A := A) ostar := by
  ext a z
  rcases z with ⟨o, r⟩
  cases r
  simp only [recordPostprocess, payoffPreservingRecordKernel,
    eraseAllRecordsProcessor, uninformativeAtPayoff,
    Channel.postprocess, Fintype.sum_prod_type,
    TraceableAgency.Dist.pure_apply]
  rw [Finset.sum_eq_single o]
  · simp only [if_true, TraceableAgency.Dist.pure_apply_self, mul_one]
    change (∑ yr : (y : Y) × R,
        P a yr.1 * (if o = ostar then d yr.2 else 0)) =
      (if (o, PUnit.unit) = (ostar, PUnit.unit) then 1 else 0)
    rw [Fintype.sum_sigma]
    by_cases ho : o = ostar
    · subst o
      simp only [if_true, TraceableAgency.Dist.pure_apply_self, mul_one]
      simp_rw [← Finset.mul_sum, d.sum_eq_one, mul_one]
      exact (P a).sum_eq_one
    · simp [ho]
  · intro o' _ hne
    simp [hne.symm]
  · exact absurd (Finset.mem_univ _)

theorem fairBinaryTrace_implies_positiveOrientationAt
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h8 : FiniteBranchContinuationConsistency F)
    (ostar : O)
    (hfair : pairStrict F traceRelevanceFairPrior
      (fullRevealAtPayoff ostar) traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)) :
    PositiveTraceOrientationAt F ostar := by
  intro A _ _ _ q hq
  obtain ⟨a0, a1, hne⟩ := exists_pair_ne A
  let r : TraceableAgency.Dist A := embeddedFairPrior a0 a1
  have hembedded : pairStrict F r (fullRevealAtPayoff ostar)
      r (fairIndependentAtPayoff (A := A) ostar) := by
    exact fairBinaryTrace_implies_embeddedTrace F h1 h5 h6 h7
      ostar hfair a0 a1 hne
  have htarget : pairStrict F r (fullRevealAtPayoff ostar)
      r (embeddedIndependentAtPayoff (A := A) r ostar) := by
    exact embeddedTrace_with_commonRecord F h1 h5 h6 h7
      ostar a0 a1 hembedded
  obtain ⟨ε, hε, hdom⟩ :=
    exists_positive_branch_mass_dominated_target q r hq
  let P : Channel A RelevanceBit :=
    binaryReachChannel q r ε (le_of_lt hε) hdom
  let K : RelevanceBit → Channel A (O × A) :=
    fun _ => fullRevealAtPayoff ostar
  let L : RelevanceBit → Channel A (O × A) :=
    fun _ => embeddedIndependentAtPayoff r ostar
  have hpositive : BranchPositive P q (ULift.up true) := by
    change (Channel.outcomeMarginal P q) (ULift.up true) > 0
    rw [show (Channel.outcomeMarginal P q) (ULift.up true) = ε by
      dsimp [P]
      exact outcomeMarginal_binaryReachChannel_true q r ε
        (le_of_lt hε) hdom]
    exact hε
  have hposterior : branchPosterior P q (ULift.up true) = r := by
    dsimp [P]
    exact branchPosterior_binaryReachChannel_true q r ε hε hdom
  have hall : ∀ y, BranchPositive P q y →
      pairWeak F (branchPosterior P q y) (K y)
        (branchPosterior P q y) (L y) := by
    intro y _hy
    have hh := h6 (fullRevealAtPayoff (A := A) ostar)
      (redrawRecordProcessor r) (branchPosterior P q y)
    rw [recordPostprocess_fullReveal_redraw] at hh
    simpa [K, L] using hh
  have hsome : ∃ y, BranchPositive P q y ∧
      pairStrict F (branchPosterior P q y) (K y)
        (branchPosterior P q y) (L y) := by
    refine ⟨ULift.up true, hpositive, ?_⟩
    rw [hposterior]
    simpa [K, L] using htarget
  have hcompound : pairStrict F q (commonPayoffCompound (fun _ : RelevanceBit => A) P K)
      q (commonPayoffCompound (fun _ : RelevanceBit => A) P L) :=
    h8.2 (fun _ : RelevanceBit => A) P K L q hall hsome
  have hleft : pairWeak F q (fullRevealAtPayoff ostar)
      q (commonPayoffCompound (fun _ : RelevanceBit => A) P K) := by
    have hh := h6 (fullRevealAtPayoff (A := A) ostar)
      (branchTaggedRevealProcessor P) q
    rw [recordPostprocess_fullReveal_branchTagged] at hh
    simpa [K] using hh
  have hright : pairWeak F q
      (commonPayoffCompound (fun _ : RelevanceBit => A) P L)
      q (uninformativeAtPayoff ostar) := by
    have hh := h6 (commonPayoffCompound (fun _ : RelevanceBit => A) P L)
      eraseAllRecordsProcessor q
    rw [show recordPostprocess
        (commonPayoffCompound (fun _ : RelevanceBit => A) P L)
          eraseAllRecordsProcessor = uninformativeAtPayoff ostar by
      simpa [L] using
        (recordPostprocess_compoundIndependent_erase P r ostar)] at hh
    exact hh
  exact pairStrict_transport_of_structural F h1 h5 h6 h7
    q (commonPayoffCompound (fun _ : RelevanceBit => A) P K)
    q (commonPayoffCompound (fun _ : RelevanceBit => A) P L)
    q (fullRevealAtPayoff ostar) q (uninformativeAtPayoff ostar)
    hcompound hleft hright

/-! ## Converse trace bridge back to the fixed four-action channel -/

noncomputable def traceRightInclusionProcessor :
    Channel.ActionKernel RelevanceBit (RelevanceBit ⊕ RelevanceBit) :=
  pureActionProcessor Sum.inr

theorem actionPushforward_traceRightInclusion :
    Channel.actionPushforward traceRelevanceFairPrior
        traceRightInclusionProcessor = traceRelevanceUnrevealingPrior := by
  ext a
  cases a with
  | inl b =>
      simp [Channel.actionPushforward, traceRightInclusionProcessor,
        pureActionProcessor, traceRelevanceUnrevealingPrior,
        TraceableAgency.Dist.pure_apply]
  | inr b =>
      simp [Channel.actionPushforward, traceRightInclusionProcessor,
        pureActionProcessor, traceRelevanceUnrevealingPrior,
        TraceableAgency.Dist.pure_apply]

theorem actionPushforward_traceSideProjection_left :
    Channel.actionPushforward traceRelevanceRevealingPrior
        traceSideProjectionProcessor = traceRelevanceFairPrior := by
  ext b
  simp only [Channel.actionPushforward, traceRelevanceRevealingPrior,
    Fintype.sum_sum_type, inlDist_apply_inl, inlDist_apply_inr,
    zero_mul, Finset.sum_const_zero, add_zero,
    traceSideProjectionProcessor, pureActionProcessor,
    Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_eq_single b]
  · simp
  · intro b' _ hne
    simp [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm]
  · exact absurd (Finset.mem_univ b)

theorem traceSideProjectionLeft_isActionProcessorCompletion
    {O : Type u} [Fintype O] [DecidableEq O] (ostar : O) :
    IsActionProcessorCompletion
      (traceRelevanceBenchmarkChannel (O := O) ostar)
      (traceRelevanceRevealingPrior :
        TraceableAgency.Dist (RelevanceBit.{u} ⊕ RelevanceBit.{u}))
      (traceSideProjectionProcessor : Channel.ActionKernel
        (RelevanceBit.{u} ⊕ RelevanceBit.{u}) RelevanceBit.{u})
      (fullRevealAtPayoff ostar) := by
  intro b z
  rw [show Channel.actionPushforward traceRelevanceRevealingPrior
      traceSideProjectionProcessor b = traceRelevanceFairPrior b by
    rw [actionPushforward_traceSideProjection_left]]
  simp only [traceRelevanceRevealingPrior, Fintype.sum_sum_type,
    inlDist_apply_inl, inlDist_apply_inr, zero_mul,
    traceSideProjectionProcessor, pureActionProcessor,
    Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_eq_single b]
  · simp [traceRelevanceBenchmarkChannel, fullRevealAtPayoff]
  · intro b' _ hne
    simp only [id_eq]
    rw [TraceableAgency.Dist.pure_apply_ne _ _ hne.symm]
    ring
  · exact absurd (Finset.mem_univ b)

theorem traceRightInclusion_isActionProcessorCompletion
    {O : Type u} [Fintype O] [DecidableEq O] (ostar : O) :
    IsActionProcessorCompletion
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)
      traceRelevanceFairPrior traceRightInclusionProcessor
      (traceRelevanceBenchmarkChannel ostar) := by
  intro a z
  rw [show Channel.actionPushforward traceRelevanceFairPrior
      traceRightInclusionProcessor a = traceRelevanceUnrevealingPrior a by
    rw [actionPushforward_traceRightInclusion]]
  cases a with
  | inl b =>
      simp [traceRelevanceUnrevealingPrior, traceRightInclusionProcessor,
        pureActionProcessor]
  | inr b =>
      rw [Finset.sum_eq_single b]
      · simp [traceRelevanceUnrevealingPrior, traceRightInclusionProcessor,
          pureActionProcessor, traceRelevanceBenchmarkChannel,
          fairIndependentAtPayoff]
      · intro b' _ hne
        have hinj : Sum.inr b' ≠
            (Sum.inr b : RelevanceBit ⊕ RelevanceBit) := by
          intro hh
          exact hne (Sum.inr.inj hh)
        change traceRelevanceFairPrior b' *
          (TraceableAgency.Dist.pure (Sum.inr b')) (Sum.inr b) *
          (fairIndependentAtPayoff (A := RelevanceBit) ostar b') z = 0
        rw [TraceableAgency.Dist.pure_apply_ne _ _ hinj.symm]
        ring
      · exact absurd (Finset.mem_univ b)

theorem recordPostprocess_uninformative_generateFair
    {O A : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] (ostar : O) :
    recordPostprocess (uninformativeAtPayoff (A := A) ostar)
        (redrawRecordProcessor traceRelevanceFairPrior) =
      fairIndependentAtPayoff (A := A) ostar := by
  ext a z
  rcases z with ⟨o, r⟩
  simp [recordPostprocess, payoffPreservingRecordKernel,
    uninformativeAtPayoff, redrawRecordProcessor,
    fairIndependentAtPayoff, Channel.postprocess,
    Fintype.sum_prod_type, TraceableAgency.Dist.pure_apply]

theorem positiveOrientationAt_implies_traceRelevance_fixed
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (ostar : O) (hpos : PositiveTraceOrientationAt F ostar) :
    A4_TraceRelevance F := by
  have hfullSilence := hpos traceRelevanceFairPrior (by
    exact TraceableAgency.Dist.uniform_fullSupport)
  have hself : pairWeak F traceRelevanceFairPrior
      (fullRevealAtPayoff ostar) traceRelevanceFairPrior
      (fullRevealAtPayoff ostar) := by
    have hrel : F.rel (fullRevealAtPayoff ostar)
        traceRelevanceFairPrior traceRelevanceFairPrior := by
      rcases (h1 (fullRevealAtPayoff ostar)).1
        traceRelevanceFairPrior traceRelevanceFairPrior with hh | hh <;> exact hh
    exact (h5.duplication (fullRevealAtPayoff ostar)
      traceRelevanceFairPrior traceRelevanceFairPrior).mp hrel
  have hsilenceFair : pairWeak F traceRelevanceFairPrior
      (uninformativeAtPayoff ostar) traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar) := by
    have hh := h6 (uninformativeAtPayoff (A := RelevanceBit) ostar)
      (redrawRecordProcessor traceRelevanceFairPrior)
      traceRelevanceFairPrior
    rw [recordPostprocess_uninformative_generateFair] at hh
    exact hh
  have hfair : pairStrict F traceRelevanceFairPrior
      (fullRevealAtPayoff ostar) traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar) :=
    pairStrict_transport_of_structural F h1 h5 h6 h7
      traceRelevanceFairPrior (fullRevealAtPayoff ostar)
      traceRelevanceFairPrior (uninformativeAtPayoff ostar)
      traceRelevanceFairPrior (fullRevealAtPayoff ostar)
      traceRelevanceFairPrior
        (fairIndependentAtPayoff (A := RelevanceBit) ostar)
      hfullSilence hself hsilenceFair
  let K := traceRelevanceBenchmarkChannel ostar
  let qR := traceRelevanceRevealingPrior
  let qU := traceRelevanceUnrevealingPrior
  have hleft : pairWeak F qR K traceRelevanceFairPrior
      (fullRevealAtPayoff ostar) := by
    have hh := h7 K qR traceSideProjectionProcessor
      (fullRevealAtPayoff ostar)
      (traceSideProjectionLeft_isActionProcessorCompletion ostar)
    rw [actionPushforward_traceSideProjection_left] at hh
    exact hh
  have hright : pairWeak F traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar) qU K := by
    have hh := h7 (fairIndependentAtPayoff (A := RelevanceBit) ostar)
      traceRelevanceFairPrior traceRightInclusionProcessor K
      (traceRightInclusion_isActionProcessorCompletion ostar)
    rw [actionPushforward_traceRightInclusion] at hh
    exact hh
  have hpair := pairStrict_transport_of_structural F h1 h5 h6 h7
    traceRelevanceFairPrior (fullRevealAtPayoff ostar)
    traceRelevanceFairPrior
      (fairIndependentAtPayoff (A := RelevanceBit) ostar)
    qR K qU K hfair hleft hright
  rw [pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7] at hpair
  refine ⟨ostar, ?_⟩
  constructor
  · exact (h5.duplication K qR qU).mpr hpair.1
  · intro hrev
    exact hpair.2 ((h5.duplication K qU qR).mp hrev)

theorem traceRelevance_bridge
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
    (h8 : FiniteBranchContinuationConsistency F) :
    A4_TraceRelevance F ↔ ∃ ostar : O, PositiveTraceOrientationAt F ostar := by
  constructor
  · intro h4
    obtain ⟨ostar, hfair⟩ :=
      traceRelevance_fixed_implies_fairBinary F h1 h5 h6 h7 h4
    exact ⟨ostar,
      fairBinaryTrace_implies_positiveOrientationAt F h1 h5 h6 h7 h8
        ostar hfair⟩
  · rintro ⟨ostar, hpos⟩
    exact positiveOrientationAt_implies_traceRelevance_fixed
      F h1 h5 h6 h7 ostar hpos

/-- The exact paper bundle supplies precisely the semantic bridge bundle used by
the long representation proof. -/
theorem traceTemperedBridgeAxioms_of_v10
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxiomsV10 F) :
    ∃ traceAnchor : O, TraceTemperedBridgeAxioms F traceAnchor := by
  have hfinite : FiniteBranchContinuationConsistency F :=
    finiteBranchContinuationConsistency_of_recordwiseSureThing
      F h.a1 h.a5 h.a6 h.a7 h.a8
  obtain ⟨ostar, hpos⟩ :=
    (traceRelevance_bridge F h.a1 h.a5 h.a6 h.a7 hfinite).mp h.a4
  exact ⟨ostar,
    { a1 := h.a1
      a2 := h.a2
      a3 := h.a5
      a4 := h.a6
      a5 := h.a7
      a6 := hfinite
      a7 := (materialRelevance_bridge F h.a1 h.a5 h.a6 h.a7).mp h.a3
      a8 := hpos }⟩

/-- Conversely, the proof-facing relevance environments imply the two fixed
paper benchmarks under the same structural axioms. -/
theorem traceTemperedAxiomsV10_of_bridge
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor) :
    TraceTemperedAxiomsV10 F :=
  { a1 := h.a1
    a2 := h.a2
    a3 := (materialRelevance_bridge F h.a1 h.a3 h.a4 h.a5).mpr h.a7
    a4 := positiveOrientationAt_implies_traceRelevance_fixed
      F h.a1 h.a3 h.a4 h.a5 h.traceAnchor h.a8
    a5 := h.a3
    a6 := h.a4
    a7 := h.a5
    a8 := recordwiseSureThing_of_finiteBranchContinuationConsistency
      F h.a1 h.a3 h.a4 h.a5 h.a6 }

end TraceableAgency.Theorem1
