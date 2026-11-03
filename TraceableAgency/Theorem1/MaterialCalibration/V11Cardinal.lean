import TraceableAgency.Theorem1.MaterialCalibration.Proof
import TraceableAgency.Theorem1.MaterialCalibration.SupportedValue

/-! # Appendix A identities at arbitrary priors and record alphabets

These endpoints extend the already checked material-normalized numerical
values. They are corollaries of the completed representation, not premises of
its material-first derivation. In particular, neither outer nor posterior
priors need full support, and the two continuation profiles may have different
record types on every branch.
-/
namespace TraceableAgency.Theorem1.MaterialCalibration
open TraceableAgency
universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

theorem supportedMarkedValue_formula_of_fullSupportFormula_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ)
    (hvalue : MaterialNormalizedValueFormula F h lambda)
    {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (K : Channel A (O × R)) :
    supportedMarkedValue F h q K =
      traceTemperedValue (materialPayoffUtility F h) lambda q K := by
  unfold supportedMarkedValue
  rw [hvalue q.restrictToSupport q.restrictToSupport_fullSupport
    (Channel.restrictToSupport K q), traceTemperedValue_restrictToSupport]

/-- One positive coefficient works for the actual supported numerical values,
not merely for an ordinally equivalent representation. -/
theorem exists_pos_supportedMarkedValue_formula_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ {A R : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype R] [DecidableEq R] [Nonempty R]
      (q : Dist A) (K : Channel A (O × R)),
      supportedMarkedValue F h q K =
        traceTemperedValue (materialPayoffUtility F h) lambda q K := by
  obtain ⟨lambda, hpos, hentropy⟩ := exists_pos_materialEntropy_eq_entropy F h
  refine ⟨lambda, hpos, ?_⟩
  intro A R _ _ _ _ _ _ q K
  exact supportedMarkedValue_formula_of_fullSupportFormula_v11 F h lambda
    (materialNormalizedValueFormula_of_constantRecordValueFormula F h lambda
      (constantRecordValueFormula_of_materialEntropy_eq F h lambda hentropy)) q K

/-- The complete continuation difference formula, with arbitrary priors and
separate record alphabets for the two profiles. Null branches contribute zero. -/
theorem supportedMarkedValue_compound_difference_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (RecK RecL : Y → Type u)
    [∀ y, Fintype (RecK y)] [∀ y, DecidableEq (RecK y)]
    [∀ y, Nonempty (RecK y)]
    [∀ y, Fintype (RecL y)] [∀ y, DecidableEq (RecL y)]
    [∀ y, Nonempty (RecL y)]
    (q : Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × RecK y))
    (L : ∀ y, Channel A (O × RecL y)) :
    supportedMarkedValue F h q (commonPayoffCompound RecK P K) -
      supportedMarkedValue F h q (commonPayoffCompound RecL P L) =
      ∑ y, Channel.outcomeMarginal P q y *
        (supportedMarkedValue F h (branchPosterior P q y) (K y) -
          supportedMarkedValue F h (branchPosterior P q y) (L y)) := by
  obtain ⟨lambda, _hpos, hv⟩ := exists_pos_supportedMarkedValue_formula_v11 F h
  simp_rw [hv, traceTemperedValue_commonCompound, mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

/-- Exact one-branch weight, including boundary outer priors, singleton
posterior supports, different record alphabets, and even a null target branch.
Other branches need only have equal numerical values. -/
theorem supportedMarkedValue_oneBranch_difference_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (RecK RecL : Y → Type u)
    [∀ y, Fintype (RecK y)] [∀ y, DecidableEq (RecK y)]
    [∀ y, Nonempty (RecK y)]
    [∀ y, Fintype (RecL y)] [∀ y, DecidableEq (RecL y)]
    [∀ y, Nonempty (RecL y)]
    (q : Dist A) (P : Channel A Y)
    (K : ∀ y, Channel A (O × RecK y))
    (L : ∀ y, Channel A (O × RecL y)) (target : Y)
    (hoff : ∀ y, y ≠ target →
      supportedMarkedValue F h (branchPosterior P q y) (K y) =
      supportedMarkedValue F h (branchPosterior P q y) (L y)) :
    supportedMarkedValue F h q (commonPayoffCompound RecK P K) -
      supportedMarkedValue F h q (commonPayoffCompound RecL P L) =
      Channel.outcomeMarginal P q target *
        (supportedMarkedValue F h (branchPosterior P q target) (K target) -
          supportedMarkedValue F h (branchPosterior P q target) (L target)) := by
  rw [supportedMarkedValue_compound_difference_v11]
  apply Finset.sum_eq_single target
  · intro y _hy hne
    rw [hoff y hne, sub_self, mul_zero]
  · intro hnot
    exact (hnot (Finset.mem_univ target)).elim

/-- Deterministic payoff separation at every prior. -/
theorem supportedMarkedValue_payoffBranch_separation_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (q : Dist A) (P : Channel A Y) (g : Y → O) :
    supportedMarkedValue F h q (payoffBranchCompound P g) =
      supportedMarkedValue F h q
        (payoffBranchCompound P (fun _ ↦ materialLowOutcome F h)) +
      ∑ y, Channel.outcomeMarginal P q y * materialPayoffUtility F h (g y) := by
  obtain ⟨lambda, _hpos, hv⟩ := exists_pos_supportedMarkedValue_formula_v11 F h
  simp only [hv, traceTemperedValue_payoffBranchCompound, materialPayoffUtility_low,
    mul_zero, Finset.sum_const_zero, add_zero]

/-- Corollary 21, with the same globally identified coefficient and no
full-support restriction. -/
theorem exists_pos_payoffBranch_formula_v11
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    ∃ lambda : ℝ, 0 < lambda ∧
      ∀ {A Y : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype Y] [DecidableEq Y] [Nonempty Y]
      (q : Dist A) (P : Channel A Y) (g : Y → O),
      supportedMarkedValue F h q (payoffBranchCompound P g) =
        lambda * mutualInfo q P +
          ∑ y, Channel.outcomeMarginal P q y * materialPayoffUtility F h (g y) := by
  obtain ⟨lambda, hpos, hv⟩ := exists_pos_supportedMarkedValue_formula_v11 F h
  refine ⟨lambda, hpos, ?_⟩
  intro A Y _ _ _ _ _ _ q P g
  rw [hv, traceTemperedValue_payoffBranchCompound]

end TraceableAgency.Theorem1.MaterialCalibration
