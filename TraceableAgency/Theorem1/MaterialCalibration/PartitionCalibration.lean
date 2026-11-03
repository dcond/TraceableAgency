import TraceableAgency.Theorem1.MaterialCalibration.PartitionUnits
import TraceableAgency.Theorem1.MaterialCalibration.FullRevelationValue

/-!
# Two-cell calibration equations

A deterministic payoff following a recorded partition is the same experiment
as the direct cell-payoff channel. Merging actions by A7 therefore identifies
its one-cell payoff upgrades with the corresponding fully revealed binary
upgrades. These equations are established before identifying information.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {A O : Type u}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype O] [DecidableEq O]

/-- Drop the final singleton record from the deterministic-payoff compound. -/
def partitionCompoundRecordEquiv :
    ((y : RelevanceBit.{u}) × payoffBranchRecord y) ≃ RelevanceBit.{u} where
  toFun z := z.1
  invFun y := ⟨y, PUnit.unit⟩
  left_inv z := by
    rcases z with ⟨y, z⟩
    cases z
    rfl
  right_inv y := rfl

/-- The compound and direct cell experiment differ only by a record bijection. -/
theorem partitionPayoffCompound_relabel (g : RelevanceBit.{u} → O) :
    Relabeling.relabelChannel (Equiv.refl (A ⊕ PUnit.{u+1}))
      (Equiv.prodCongr (Equiv.refl O) partitionCompoundRecordEquiv)
      (payoffBranchCompound (partitionRecordChannel (A := A)) g) =
      partitionPayoffChannel g := by
  ext a z
  rcases z with ⟨o, b⟩
  change payoffBranchCompound (partitionRecordChannel (A := A)) g a
      (o, ⟨b, PUnit.unit⟩) = partitionPayoffChannel g a (o, b)
  rw [payoffBranchCompound, commonPayoffCompound_apply]
  by_cases hb : b = partitionCell a
  · subst b
    simp [partitionRecordChannel, partitionCollapse, partitionPayoffChannel,
      partitionCellPayoffChannel, payoffBranchContinuation,
      uninformativeAtPayoff, Dist.pure_apply]
  · simp [partitionRecordChannel, partitionCollapse, partitionPayoffChannel,
      partitionCellPayoffChannel, payoffBranchContinuation,
      uninformativeAtPayoff, Dist.pure_apply, hb]

/-- Deterministic branch construction and the direct cell channel have the
same material-normalized value at every full-support prior. -/
theorem normalizedMarkedUtility_partitionPayoffBranch_eq_direct
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist (A ⊕ PUnit.{u+1})) (hq : q.FullSupport)
    (g : RelevanceBit.{u} → O) :
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment (partitionRecordChannel (A := A)) g) =
      normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (partitionPayoffChannel g)) := by
  have hv := normalizedMarkedUtility_recordEquiv F h
    partitionCompoundRecordEquiv q hq
    (payoffBranchCompound (partitionRecordChannel (A := A)) g)
  simpa only [partitionPayoffCompound_relabel, payoffBranchExperiment] using hv.symm

/-- After the two-way A7 merge, the branch experiment is valued exactly as
full revelation of the binary cell prior with the same payoff profile. -/
theorem normalizedMarkedUtility_partitionPayoffBranch_eq_binary
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (g : RelevanceBit.{u} → O) :
    normalizedMarkedUtility F h
        (partitionPrior r t (le_of_lt ht0) (le_of_lt ht1))
        (partitionPrior_fullSupport r hr t ht0 ht1)
        (payoffBranchExperiment (partitionRecordChannel (A := A)) g) =
      normalizedMarkedUtility F h
        (partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1))
        (partitionCellPrior_fullSupport t ht0 ht1)
        (fullRevealWithPayoffExperiment g) := by
  rw [normalizedMarkedUtility_partitionPayoffBranch_eq_direct]
  exact partitionPayoff_normalizedValue_eq F h r hr t ht0 ht1 g

/-- Upgrading one partition cell has the cell probability times the common
unit of the fully revealed binary experiment. -/
theorem partitionPayoff_upgrade_value
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (cell : RelevanceBit.{u}) :
    normalizedMarkedUtility F h
        (partitionPrior r t (le_of_lt ht0) (le_of_lt ht1))
        (partitionPrior_fullSupport r hr t ht0 ht1)
        (payoffBranchExperiment (partitionRecordChannel (A := A))
          (updateBranchPayoff (fun _ => materialLowOutcome F h) cell
            (materialHighOutcome F h))) -
      normalizedMarkedUtility F h
        (partitionPrior r t (le_of_lt ht0) (le_of_lt ht1))
        (partitionPrior_fullSupport r hr t ht0 ht1)
        (payoffBranchExperiment (partitionRecordChannel (A := A))
          (fun _ => materialLowOutcome F h)) =
      partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1) cell *
        revealMaterialUnit F h
          (partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1))
          (partitionCellPrior_fullSupport t ht0 ht1) := by
  rw [normalizedMarkedUtility_partitionPayoffBranch_eq_binary F h r hr t ht0 ht1,
    normalizedMarkedUtility_partitionPayoffBranch_eq_binary F h r hr t ht0 ht1,
    updateBranchPayoff_eq_update]
  exact revealUpgrade_eq_probability_mul_unit F h
    (partitionCellPrior t (le_of_lt ht0) (le_of_lt ht1))
    (partitionCellPrior_fullSupport t ht0 ht1) cell

end TraceableAgency.Theorem1.MaterialCalibration
