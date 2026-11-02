import TraceableAgency.Theorem1.MaterialCalibration.Calibration

/-!
# Exact branch comparisons with arbitrary continuation backgrounds

The marked-law difference from replacing one continuation is independent of
all other branches. Affinity transfers that difference to the material-
calibrated insertion with a constant background, giving the probability weight
for arbitrary continuation profiles and arbitrary reached posterior supports.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A Y R : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]
variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- Restricting an experiment to the positive support preserves its marked
law after the local action posteriors are included in the original alphabet. -/
theorem markedChannelIntegral_restrictToSupport_material
    (r : Dist A) (K : Channel A (O × R))
    (phi : O × Dist A → ℝ) :
    markedChannelIntegral r K phi =
      markedChannelIntegral r.restrictToSupport (Channel.restrictToSupport K r)
        (fun op => phi (op.1, supportPushforwardPosterior r op.2)) := by
  classical
  unfold markedChannelIntegral
  apply Finset.sum_congr rfl
  intro z _hz
  have hmarg := congrArg (fun d : Dist (O × R) => d z)
    (Channel.outcomeMarginal_restrictToSupport K r)
  by_cases hpos : 0 < Channel.outcomeMarginal K r z
  · have hpost := posterior_restrictToSupport_include_of_pos K r z hpos
    rw [hmarg]
    change Channel.outcomeMarginal K r z * phi (z.1, Channel.posterior K r z) =
      Channel.outcomeMarginal K r z * phi (z.1,
        Channel.actionPushforward
          (Channel.posterior (Channel.restrictToSupport K r) r.restrictToSupport z)
          (supportIncludeKernel r))
    rw [hpost]
  · have hz : Channel.outcomeMarginal K r z = 0 :=
      le_antisymm (le_of_not_gt hpos) ((Channel.outcomeMarginal K r).nonneg z)
    rw [hmarg, hz, zero_mul, zero_mul]

/-- All unchanged branches cancel from the difference of the joint laws of
payoff and posterior, even when their continuations are arbitrary channels. -/
theorem markedChannelIntegral_compound_oneBranch_difference
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : Dist A) (P : Channel A Y)
    (K L : ∀ y, Channel A (O × Rec y)) (target : Y)
    (hoff : ∀ y, y ≠ target → K y = L y)
    (phi : O × Dist A → ℝ) :
    markedChannelIntegral q (commonPayoffCompound Rec P K) phi -
        markedChannelIntegral q (commonPayoffCompound Rec P L) phi =
      Channel.outcomeMarginal P q target *
        (markedChannelIntegral (branchPosterior P q target) (K target) phi -
          markedChannelIntegral (branchPosterior P q target) (L target) phi) := by
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound, ← Finset.sum_sub_distrib,
    Finset.sum_eq_single target]
  · simp only [branchPosterior]
    ring
  · intro y _hy hyt
    rw [hoff y hyt]
    ring
  · simp

/-- Exact cardinal A8 with an arbitrary background: two continuation
profiles agreeing off a reached branch differ in value by the branch mass
multiplied by their local value difference. Restricting the local prior to its
positive support includes boundary and singleton posterior cases. -/
theorem normalizedMarkedUtility_compound_oneBranch_difference_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y)
    (K L : ∀ y, Channel A (O × Rec y)) (target : Y)
    (htarget : BranchPositive P q target)
    (hoff : ∀ y, y ≠ target → K y = L y) :
    normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (commonPayoffCompound Rec P K)) -
      normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (commonPayoffCompound Rec P L)) =
      Channel.outcomeMarginal P q target *
        (normalizedMarkedUtility F h
            (branchPosterior P q target).restrictToSupport
            (Dist.restrictToSupport_fullSupport _)
            (markedExperimentOfChannel
              (Channel.restrictToSupport (K target) (branchPosterior P q target))) -
          normalizedMarkedUtility F h
            (branchPosterior P q target).restrictToSupport
            (Dist.restrictToSupport_fullSupport _)
            (markedExperimentOfChannel
              (Channel.restrictToSupport (L target) (branchPosterior P q target)))) := by
  let r := branchPosterior P q target
  let E := markedExperimentOfChannel (Channel.restrictToSupport (K target) r)
  let G := markedExperimentOfChannel (Channel.restrictToSupport (L target) r)
  let background := materialLowOutcome F h
  have hdir (phi : O × Dist A → ℝ) :
      markedTerminalIntegral q
          (markedExperimentOfChannel (commonPayoffCompound Rec P K)) phi -
        markedTerminalIntegral q
          (markedExperimentOfChannel (commonPayoffCompound Rec P L)) phi =
      markedTerminalIntegral q
          (supportBranchInsertionExperiment q P target background E) phi -
        markedTerminalIntegral q
          (supportBranchInsertionExperiment q P target background G) phi := by
    change markedChannelIntegral q (commonPayoffCompound Rec P K) phi -
        markedChannelIntegral q (commonPayoffCompound Rec P L) phi = _
    rw [markedChannelIntegral_compound_oneBranch_difference Rec q P K L target hoff,
      markedTerminalIntegral_supportBranchInsertion_difference,
      markedChannelIntegral_restrictToSupport_material
        (branchPosterior P q target) (K target) phi,
      markedChannelIntegral_restrictToSupport_material
        (branchPosterior P q target) (L target) phi]
    rfl
  have hvalue := normalizedMarkedUtility_difference_of_integral_difference
    F h q hq
    (markedExperimentOfChannel (commonPayoffCompound Rec P K))
    (markedExperimentOfChannel (commonPayoffCompound Rec P L))
    (supportBranchInsertionExperiment q P target background E)
    (supportBranchInsertionExperiment q P target background G) hdir
  exact hvalue.trans
    (normalizedMarkedUtility_supportInsertion_difference_material
      F h q hq P target htarget background E G)

end TraceableAgency.Theorem1.MaterialCalibration
