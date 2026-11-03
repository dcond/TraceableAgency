import TraceableAgency.Theorem1.MaterialCalibration.TraceEntropy
import TraceableAgency.Theorem1.MaterialCalibration.SupportedValue
import TraceableAgency.Theorem1.MaterialCalibration.EntropyProperties

/-! Entropy reduction on arbitrary prior supports. -/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

def materialCompoundRecordEquiv : ((y : Y) × payoffBranchRecord y) ≃ Y where
  toFun z := z.1
  invFun y := ⟨y, PUnit.unit⟩
  left_inv z := by rcases z with ⟨y, z⟩; cases z; rfl
  right_inv _ := rfl

theorem payoffBranchCompound_relabel_constant (P : Channel A Y) (o : O) :
    Relabeling.relabelChannel (Equiv.refl A)
        (Equiv.prodCongr (Equiv.refl O) materialCompoundRecordEquiv)
        (payoffBranchCompound P (fun _ ↦ o)) = constantPayoffLift o P := by
  ext a z
  rcases z with ⟨o', y⟩
  change payoffBranchCompound P (fun _ ↦ o) a (o', ⟨y, PUnit.unit⟩) = _
  rw [payoffBranchCompound, commonPayoffCompound_apply]
  by_cases ho : o' = o
  · subst o'
    simp [payoffBranchContinuation, uninformativeAtPayoff, constantPayoffLift]
  · simp [payoffBranchContinuation, uninformativeAtPayoff, constantPayoffLift, ho]

theorem materialTraceValue_eq_constantPayoffLift
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y) :
    materialTraceValue F h q hq P =
      normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (constantPayoffLift (materialLowOutcome F h) P)) := by
  have hv := normalizedMarkedUtility_recordEquiv F h
    (materialCompoundRecordEquiv (Y := Y)) q hq
    (payoffBranchCompound P (fun _ ↦ materialLowOutcome F h))
  rw [payoffBranchCompound_relabel_constant] at hv
  exact hv.symm

theorem supportedMarkedValue_constantPayoffLift_eq_supportTraceValue
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (P : Channel A Y) :
    supportedMarkedValue F h q (constantPayoffLift (materialLowOutcome F h) P) =
      materialTraceValue F h q.restrictToSupport
        (Dist.restrictToSupport_fullSupport q) (Channel.restrictToSupport P q) := by
  rw [materialTraceValue_eq_constantPayoffLift]
  rfl

/-- Entropy reduction for arbitrary priors, after deleting null action rows.
Reached posteriors are transported back by support inclusion; null records
contribute zero independently of their fallback posterior. -/
theorem supportedMarkedValue_constantPayoffLift_eq_entropy_sub_expected
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (P : Channel A Y) :
    supportedMarkedValue F h q (constantPayoffLift (materialLowOutcome F h) P) =
      materialEntropy F h q -
        ∑ y, Channel.outcomeMarginal P q y *
          materialEntropy F h (branchPosterior P q y) := by
  rw [supportedMarkedValue_constantPayoffLift_eq_supportTraceValue,
    materialTraceValue_eq_entropy_sub_expected,
    ← materialEntropy_support_restriction]
  congr 1
  apply Finset.sum_congr rfl
  intro y _hy
  have hmarg := congrArg (fun d : Dist Y ↦ d y)
    (Channel.outcomeMarginal_restrictToSupport P q)
  rw [hmarg]
  by_cases hpos : 0 < Channel.outcomeMarginal P q y
  · have hpost := posterior_restrictToSupport_include_of_pos P q y hpos
    have hentropy := materialEntropy_supportPushforward F h q
      (branchPosterior (Channel.restrictToSupport P q) q.restrictToSupport y)
    change materialEntropy F h (Channel.actionPushforward
      (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport y)
      (supportIncludeKernel q)) = _ at hentropy
    rw [hpost] at hentropy
    rw [← hentropy]
    rfl
  · have hz : Channel.outcomeMarginal P q y = 0 :=
      le_antisymm (le_of_not_gt hpos) ((Channel.outcomeMarginal P q).nonneg y)
    rw [hz, zero_mul, zero_mul]

end TraceableAgency.Theorem1.MaterialCalibration
