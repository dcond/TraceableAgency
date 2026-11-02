import TraceableAgency.Theorem1.CommonMarkedScale

/-!
# Payoff-dependent two-cell action merging

A cell record and a payoff depending only on that cell cannot distinguish
within-cell actions.  Two exact A7 processors therefore identify the
experiment with full revelation of the cell prior.  No information-value
representation is used.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype O] [DecidableEq O]

theorem sum_partitionCell (f : RelevanceBit.{u} → ℝ) :
    (∑ b, f b) = f (ULift.up false) + f (ULift.up true) := by
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp f]
  simp [Fintype.sum_bool, Equiv.ulift]
  ring

/-- The non-singleton cell is `true`; the adjoined singleton is `false`. -/
def partitionCell : A ⊕ PUnit.{u+1} → RelevanceBit.{u}
  | Sum.inl _ => ULift.up true
  | Sum.inr _ => ULift.up false

noncomputable def partitionPrior (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TraceableAgency.Dist (A ⊕ PUnit.{u+1}) :=
  TraceableAgency.Dist.mix t ht0 ht1 (inlDist r)
    (inrDist (TraceableAgency.Dist.pure PUnit.unit))

noncomputable def partitionCellPrior
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    TraceableAgency.Dist RelevanceBit.{u} :=
  TraceableAgency.Dist.mix t ht0 ht1
    (TraceableAgency.Dist.pure (ULift.up true))
    (TraceableAgency.Dist.pure (ULift.up false))

@[simp]theorem partitionPrior_inl (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : A) :
    partitionPrior r t ht0 ht1 (Sum.inl a) = t * r a := by
  simp [partitionPrior]

@[simp]theorem partitionPrior_inr (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (a : PUnit.{u+1}) :
    partitionPrior r t ht0 ht1 (Sum.inr a) = 1 - t := by
  cases a
  simp [partitionPrior]

@[simp]theorem partitionCellPrior_true
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    partitionCellPrior t ht0 ht1 (ULift.up true) = t := by
  simp [partitionCellPrior, TraceableAgency.Dist.pure_apply]

@[simp]theorem partitionCellPrior_false
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    partitionCellPrior t ht0 ht1 (ULift.up false) = 1 - t := by
  simp [partitionCellPrior, TraceableAgency.Dist.pure_apply]

theorem partitionPrior_fullSupport (r : TraceableAgency.Dist A)
    (hr : r.FullSupport) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (partitionPrior r t (le_of_lt ht0) (le_of_lt ht1)).FullSupport := by
  intro a
  cases a with
  | inl a => simpa using mul_pos ht0 (hr a)
  | inr a => simpa using sub_pos.mpr ht1

theorem partitionCellPrior_fullSupport
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    (partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1)).FullSupport := by
  intro a
  rcases a with ⟨a⟩
  cases a <;> simp [ht0, sub_pos.mpr ht1]

noncomputable def partitionCollapse : Channel.ActionKernel (A ⊕ PUnit.{u+1}) RelevanceBit.{u} :=
  fun a => TraceableAgency.Dist.pure (partitionCell a)

/-- The same deterministic map used as a first-stage record channel. -/
noncomputable abbrev partitionRecordChannel : Channel (A ⊕ PUnit.{u+1}) RelevanceBit.{u} :=
  partitionCollapse

noncomputable def partitionRefine (r : TraceableAgency.Dist A) :
    Channel.ActionKernel RelevanceBit.{u} (A ⊕ PUnit.{u+1}) :=
  fun b => if b.down then inlDist r
    else inrDist (TraceableAgency.Dist.pure PUnit.unit)

/-- Full revelation of the cell, allowing a different payoff in each cell. -/
noncomputable def partitionCellPayoffChannel (g : RelevanceBit.{u} → O) :
    Channel RelevanceBit.{u} (O × RelevanceBit.{u}) :=
  fun b => TraceableAgency.Dist.pure (g b, b)

/-- The corresponding payoff and record on the unmerged action alphabet. -/
noncomputable def partitionPayoffChannel (g : RelevanceBit.{u} → O) :
    Channel (A ⊕ PUnit.{u+1}) (O × RelevanceBit.{u}) :=
  fun a => partitionCellPayoffChannel g (partitionCell a)

theorem partitionCollapse_pushforward (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Channel.actionPushforward (partitionPrior r t ht0 ht1) partitionCollapse =
      partitionCellPrior t ht0 ht1 := by
  ext b
  rcases b with ⟨b⟩
  cases b <;>
    simp [Channel.actionPushforward, Fintype.sum_sum_type,
      partitionCollapse, partitionCell, TraceableAgency.Dist.pure_apply,
      ← Finset.mul_sum, r.sum_eq_one]

theorem partitionRefine_pushforward (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Channel.actionPushforward (partitionCellPrior t ht0 ht1) (partitionRefine r) =
      partitionPrior r t ht0 ht1 := by
  ext a
  cases a with
  | inl a =>
      simp [Channel.actionPushforward, partitionRefine,
        sum_partitionCell]
  | inr a =>
      cases a
      simp [Channel.actionPushforward, partitionRefine,
        sum_partitionCell]

/-- The recorded cell has the binary prior `(t,1-t)`. -/
theorem partitionRecord_marginal (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Channel.outcomeMarginal (partitionCollapse (A := A))
        (partitionPrior r t ht0 ht1) = partitionCellPrior t ht0 ht1 :=
  partitionCollapse_pushforward r t ht0 ht1

/-- On the non-singleton cell, the posterior is the original prior, embedded
in the larger action set. -/
theorem partitionRecord_posterior_true (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    branchPosterior (partitionCollapse (A := A))
        (partitionPrior r t (le_of_lt ht0) ht1) (ULift.up true) = inlDist r := by
  have hm : Channel.outcomeMarginal (partitionCollapse (A := A))
      (partitionPrior r t (le_of_lt ht0) ht1) (ULift.up true) = t := by
    rw [partitionRecord_marginal, partitionCellPrior_true]
  have hp : 0 < Channel.outcomeMarginal (partitionCollapse (A := A))
      (partitionPrior r t (le_of_lt ht0) ht1) (ULift.up true) := by
    rw [hm]
    exact ht0
  unfold branchPosterior Channel.posterior
  rw [dif_pos hp]
  ext a
  change partitionPrior r t (le_of_lt ht0) ht1 a *
      partitionCollapse a (ULift.up true) /
      Channel.outcomeMarginal (partitionCollapse (A := A))
        (partitionPrior r t (le_of_lt ht0) ht1) (ULift.up true) = inlDist r a
  rw [hm]
  cases a with
  | inl a =>
      simp [partitionCollapse, partitionCell, mul_div_cancel_left₀, ne_of_gt ht0]
  | inr a =>
      simp [partitionCollapse, partitionCell, TraceableAgency.Dist.pure_apply]

/-- On the singleton cell, the posterior puts all mass on its one action. -/
theorem partitionRecord_posterior_false (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    branchPosterior (partitionCollapse (A := A))
        (partitionPrior r t ht0 (le_of_lt ht1)) (ULift.up false) =
      TraceableAgency.Dist.pure (Sum.inr PUnit.unit) := by
  have hm : Channel.outcomeMarginal (partitionCollapse (A := A))
      (partitionPrior r t ht0 (le_of_lt ht1)) (ULift.up false) = 1 - t := by
    rw [partitionRecord_marginal, partitionCellPrior_false]
  have hp : 0 < Channel.outcomeMarginal (partitionCollapse (A := A))
      (partitionPrior r t ht0 (le_of_lt ht1)) (ULift.up false) := by
    rw [hm]
    exact sub_pos.mpr ht1
  unfold branchPosterior Channel.posterior
  rw [dif_pos hp]
  ext a
  change partitionPrior r t ht0 (le_of_lt ht1) a *
      partitionCollapse a (ULift.up false) /
      Channel.outcomeMarginal (partitionCollapse (A := A))
        (partitionPrior r t ht0 (le_of_lt ht1)) (ULift.up false) =
      TraceableAgency.Dist.pure (Sum.inr PUnit.unit) a
  rw [hm]
  cases a with
  | inl a =>
      simp [partitionCollapse, partitionCell, TraceableAgency.Dist.pure_apply]
  | inr a =>
      cases a
      simp [partitionCollapse, partitionCell, ne_of_gt (sub_pos.mpr ht1)]

theorem partitionRecord_positive_true (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    BranchPositive (partitionCollapse (A := A))
      (partitionPrior r t (le_of_lt ht0) ht1) (ULift.up true) := by
  change Channel.outcomeMarginal _ _ _ > 0
  rw [partitionRecord_marginal, partitionCellPrior_true]
  exact ht0

theorem partitionRecord_positive_false (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    BranchPositive (partitionCollapse (A := A))
      (partitionPrior r t ht0 (le_of_lt ht1)) (ULift.up false) := by
  change Channel.outcomeMarginal _ _ _ > 0
  rw [partitionRecord_marginal, partitionCellPrior_false]
  exact sub_pos.mpr ht1

theorem partitionCollapse_completion (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (g : RelevanceBit.{u} → O) :
    IsActionProcessorCompletion (partitionPayoffChannel g)
      (partitionPrior r t ht0 ht1) partitionCollapse
      (partitionCellPayoffChannel g) := by
  intro b z
  rw [partitionCollapse_pushforward]
  rcases b with ⟨b⟩
  cases b <;>
    simp [Fintype.sum_sum_type, partitionCollapse, partitionCell,
      partitionPayoffChannel, TraceableAgency.Dist.pure_apply,
      ← Finset.sum_mul, ← Finset.mul_sum, r.sum_eq_one]

theorem partitionRefine_completion (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (g : RelevanceBit.{u} → O) :
    IsActionProcessorCompletion (partitionCellPayoffChannel g)
      (partitionCellPrior t ht0 ht1) (partitionRefine r)
      (partitionPayoffChannel g) := by
  intro a z
  rw [partitionRefine_pushforward]
  cases a with
  | inl a =>
      simp [partitionRefine, partitionPayoffChannel, partitionCell,
        sum_partitionCell]
  | inr a =>
      cases a
      simp [partitionRefine, partitionPayoffChannel, partitionCell,
        sum_partitionCell]

/-- A7 in both directions merges all within-cell actions even when the
terminal payoff depends on the cell. -/
theorem partitionPayoff_pairWeak_both
    (F : FixedPayoffPrefFamily O) (h7 : A7_ActionDataProcessing F)
    (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (g : RelevanceBit.{u} → O) :
    pairWeak F (partitionPrior r t ht0 ht1) (partitionPayoffChannel g)
      (partitionCellPrior t ht0 ht1) (partitionCellPayoffChannel g) ∧
    pairWeak F (partitionCellPrior t ht0 ht1) (partitionCellPayoffChannel g)
      (partitionPrior r t ht0 ht1) (partitionPayoffChannel g) := by
  constructor
  · have hh := h7 (partitionPayoffChannel g) (partitionPrior r t ht0 ht1)
      partitionCollapse (partitionCellPayoffChannel g)
      (partitionCollapse_completion r t ht0 ht1 g)
    simpa [partitionCollapse_pushforward] using hh
  · have hh := h7 (partitionCellPayoffChannel g) (partitionCellPrior t ht0 ht1)
      (partitionRefine r) (partitionPayoffChannel g)
      (partitionRefine_completion r t ht0 ht1 g)
    simpa [partitionRefine_pushforward] using hh

/-- Indifference in the paper's single oriented comparison environment. -/
theorem partitionPayoff_pairIndiff
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (g : RelevanceBit.{u} → O) :
    pairIndiff F (partitionPrior r t ht0 ht1) (partitionPayoffChannel g)
      (partitionCellPrior t ht0 ht1) (partitionCellPayoffChannel g) := by
  obtain ⟨hf, hb⟩ := partitionPayoff_pairWeak_both F h.a5 r t ht0 ht1 g
  exact ⟨hf, (sameBlock_reverse_iff_pairWeak_swap F h.a1 h.a3 h.a4 h.a5
    (partitionPrior r t ht0 ht1) (partitionPayoffChannel g)
    (partitionCellPrior t ht0 ht1) (partitionCellPayoffChannel g)).mpr hb⟩

/-- The material-normalized common values agree exactly under the merge. -/
theorem partitionPayoff_normalizedValue_eq
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : TraceableAgency.Dist A) (hr : r.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (g : RelevanceBit.{u} → O) :
    normalizedMarkedUtility F h
        (partitionPrior r t (le_of_lt ht0) (le_of_lt ht1))
        (partitionPrior_fullSupport r hr t ht0 ht1)
        (markedExperimentOfChannel (partitionPayoffChannel g)) =
      normalizedMarkedUtility F h
        (partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1))
        (partitionCellPrior_fullSupport t ht0 ht1)
        (markedExperimentOfChannel (partitionCellPayoffChannel g)) := by
  have hi := partitionPayoff_pairWeak_both F h.a5 r t
    (le_of_lt ht0) (le_of_lt ht1) g
  apply le_antisymm
  · exact (pairWeak_markedExperiments_iff_normalizedMarkedUtility F h
      (partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1))
      (partitionPrior r t (le_of_lt ht0) (le_of_lt ht1))
      (partitionCellPrior_fullSupport t ht0 ht1)
      (partitionPrior_fullSupport r hr t ht0 ht1)
      (markedExperimentOfChannel (partitionCellPayoffChannel g))
      (markedExperimentOfChannel (partitionPayoffChannel g))).mp hi.2
  · exact (pairWeak_markedExperiments_iff_normalizedMarkedUtility F h
      (partitionPrior r t (le_of_lt ht0) (le_of_lt ht1))
      (partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1))
      (partitionPrior_fullSupport r hr t ht0 ht1)
      (partitionCellPrior_fullSupport t ht0 ht1)
      (markedExperimentOfChannel (partitionPayoffChannel g))
      (markedExperimentOfChannel (partitionCellPayoffChannel g))).mp hi.1

end TraceableAgency.Theorem1.MaterialCalibration
