import TraceableAgency.Theorem1.MaterialCalibration.V11Cardinal

/-! # Complete affine-insertion and material-unit statements

These statements collect the Appendix A conclusions, including different
continuation record alphabets and boundary outer priors. The universal
insertion coefficient is the already calibrated branch probability; these
exports are downstream corollaries and are not used to prove calibration.
-/
namespace TraceableAgency.Theorem1.MaterialCalibration
open TraceableAgency
universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

/-- Extending an arbitrary support continuation to null ambient rows leaves
its supported value exactly unchanged. -/
theorem supportedMarkedValue_supportExtend_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (r : Dist A) (K : Channel (supportSubtype r) (O × R)) :
    supportedMarkedValue F h r (supportExtendChannel r K) =
      supportedMarkedValue F h r.restrictToSupport K := by
  rw [supportedMarkedValue_eq_normalized_of_fullSupport F h
    r.restrictToSupport r.restrictToSupport_fullSupport K]
  unfold supportedMarkedValue
  rw [restrictToSupport_supportExtendChannel]

/-- Lemma 15: a single positive coefficient works for every continuation pair
and every background, with independent record alphabets on the two sides.
The local supported value is, by definition, the value on its posterior
support; `supportedMarkedValue_supportExtend_v11` also permits continuations
specified only on that support. -/
theorem affine_insertion_exists_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (q : Dist A) (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (RecK RecL : Y → Type u)
      [∀ y, Fintype (RecK y)] [∀ y, DecidableEq (RecK y)]
      [∀ y, Nonempty (RecK y)]
      [∀ y, Fintype (RecL y)] [∀ y, DecidableEq (RecL y)]
      [∀ y, Nonempty (RecL y)]
      (K : ∀ y, Channel A (O × RecK y))
      (L : ∀ y, Channel A (O × RecL y)),
      (∀ y, y ≠ target →
        supportedMarkedValue F h (branchPosterior P q y) (K y) =
        supportedMarkedValue F h (branchPosterior P q y) (L y)) →
      supportedMarkedValue F h q (commonPayoffCompound RecK P K) -
        supportedMarkedValue F h q (commonPayoffCompound RecL P L) =
        c * (supportedMarkedValue F h (branchPosterior P q target) (K target) -
          supportedMarkedValue F h (branchPosterior P q target) (L target)) := by
  refine ⟨Channel.outcomeMarginal P q target, htarget, ?_⟩
  intro RecK RecL _ _ _ _ _ _ K L hoff
  exact supportedMarkedValue_oneBranch_difference_v11 F h RecK RecL q P K L target hoff

/-- Relabelling invariance of the actual material units. This is the omitted
explicit invariance clause of Lemma 16, now a corollary of calibration. -/
theorem revealMaterialUnit_relabel_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    revealMaterialUnit F h (Relabeling.relabelDist e q)
      (Relabeling.relabelDist_fullSupport e q hq) = revealMaterialUnit F h q hq := by
  rw [revealMaterialUnit_eq_one, revealMaterialUnit_eq_one]

/-- Lemma 16's positive material unit and all reached-support ratios, including
singleton supports. The stronger calibrated normalization also implies the
paper's singleton normalization. -/
theorem material_unit_exists_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    ∃ gamma : ℝ, 0 < gamma ∧
      (∀ a, revealUpgrade F h q hq a = q a * gamma) ∧
      gamma = 1 ∧
      (∀ {B : Type u} [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B),
        revealMaterialUnit F h (Relabeling.relabelDist e q)
          (Relabeling.relabelDist_fullSupport e q hq) = gamma) ∧
      (∀ {Y : Type u} [Fintype Y] [DecidableEq Y] [Nonempty Y]
        (P : Channel A Y) (target : Y)
        (htarget : BranchPositive P q target) (background : O),
        supportBranchInsertionScale F h q hq P target htarget background *
          revealMaterialUnit F h (branchPosterior P q target).restrictToSupport
            (Dist.restrictToSupport_fullSupport _) =
          Channel.outcomeMarginal P q target * gamma) := by
  refine ⟨revealMaterialUnit F h q hq, revealMaterialUnit_pos F h q hq,
    revealUpgrade_eq_probability_mul_unit F h q hq,
    revealMaterialUnit_eq_one F h q hq, ?_, ?_⟩
  · intro B _ _ _ e
    exact revealMaterialUnit_relabel_v11 F h e q hq
  · intro Y _ _ _ P target htarget background
    exact supportBranchInsertionScale_mul_revealMaterialUnit F h q hq P target htarget background

end TraceableAgency.Theorem1.MaterialCalibration
