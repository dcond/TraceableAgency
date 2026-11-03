import TraceableAgency.Theorem1.MaterialCalibration.TraceValue

/-!
# Exact cardinal aggregation of arbitrary continuation changes

The one-branch formula is extended to null branches and then telescoped over
all branches. No information-value representation is used.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- The exact branch difference also holds at null branches, where both
sides vanish. -/
theorem normalizedMarkedUtility_compound_oneBranch_difference_material_all
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y)
    (K L : ∀ y, Channel A (O × Rec y)) (target : Y)
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
  by_cases hp : BranchPositive P q target
  · exact normalizedMarkedUtility_compound_oneBranch_difference_material
      F h Rec q hq P K L target hp hoff
  · have hz : Channel.outcomeMarginal P q target = 0 :=
      le_antisymm (le_of_not_gt hp) ((Channel.outcomeMarginal P q).nonneg target)
    have hlaw : SameMarkedTerminalLaw q
        (markedExperimentOfChannel (commonPayoffCompound Rec P K))
        (markedExperimentOfChannel (commonPayoffCompound Rec P L)) := by
      intro phi
      have hd := markedChannelIntegral_compound_oneBranch_difference
        Rec q P K L target hoff phi
      rw [hz, zero_mul] at hd
      exact sub_eq_zero.mp hd
    rw [normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _ hlaw,
      sub_self, hz, zero_mul]

/-- Change exactly the branches in a finite set from `L` to `K`. -/
def partialContinuationProfile
    (Rec : Y → Type u) [∀ y, Fintype (Rec y)]
    (K L : ∀ y, Channel A (O × Rec y)) (s : Finset Y) :
    ∀ y, Channel A (O × Rec y) :=
  fun y ↦ if y ∈ s then K y else L y

/-- The difference between any two compound continuation profiles is the
sum of their conditional differences weighted by branch probabilities. -/
theorem normalizedMarkedUtility_compound_difference_material
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y)
    (K L : ∀ y, Channel A (O × Rec y)) :
    normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (commonPayoffCompound Rec P K)) -
      normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (commonPayoffCompound Rec P L)) =
      ∑ y, Channel.outcomeMarginal P q y *
        (normalizedMarkedUtility F h
            (branchPosterior P q y).restrictToSupport
            (Dist.restrictToSupport_fullSupport _)
            (markedExperimentOfChannel
              (Channel.restrictToSupport (K y) (branchPosterior P q y))) -
          normalizedMarkedUtility F h
            (branchPosterior P q y).restrictToSupport
            (Dist.restrictToSupport_fullSupport _)
            (markedExperimentOfChannel
              (Channel.restrictToSupport (L y) (branchPosterior P q y)))) := by
  classical
  let V := fun (M : ∀ y, Channel A (O × Rec y)) ↦
    normalizedMarkedUtility F h q hq
      (markedExperimentOfChannel (commonPayoffCompound Rec P M))
  let d := fun y ↦ Channel.outcomeMarginal P q y *
    (normalizedMarkedUtility F h (branchPosterior P q y).restrictToSupport
        (Dist.restrictToSupport_fullSupport _)
        (markedExperimentOfChannel
          (Channel.restrictToSupport (K y) (branchPosterior P q y))) -
      normalizedMarkedUtility F h (branchPosterior P q y).restrictToSupport
        (Dist.restrictToSupport_fullSupport _)
        (markedExperimentOfChannel
          (Channel.restrictToSupport (L y) (branchPosterior P q y))))
  have hempty : partialContinuationProfile Rec K L ∅ = L := by
    funext y
    simp [partialContinuationProfile]
  have huniv : partialContinuationProfile Rec K L Finset.univ = K := by
    funext y
    simp [partialContinuationProfile]
  have hs : ∀ s : Finset Y,
      V (partialContinuationProfile Rec K L s) - V L = ∑ y ∈ s, d y := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [hempty, sub_self, Finset.sum_empty]
    | @insert target s htarget ih =>
      have hoff : ∀ y, y ≠ target →
          partialContinuationProfile Rec K L (insert target s) y =
            partialContinuationProfile Rec K L s y := by
        intro y hy
        simp [partialContinuationProfile, hy]
      have hd := normalizedMarkedUtility_compound_oneBranch_difference_material_all
        F h Rec q hq P (partialContinuationProfile Rec K L (insert target s))
          (partialContinuationProfile Rec K L s) target hoff
      simp only [partialContinuationProfile, Finset.mem_insert_self, if_true,
        htarget, if_false] at hd
      change V (partialContinuationProfile Rec K L (insert target s)) -
        V (partialContinuationProfile Rec K L s) = d target at hd
      rw [Finset.sum_insert htarget]
      linarith
  simpa only [huniv, V, d] using hs Finset.univ

end TraceableAgency.Theorem1.MaterialCalibration
