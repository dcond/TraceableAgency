/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.FullSupportValueAssembly
import Theorem1Verification.RepresentationAssembly
import Theorem1Verification.Benchmark

/-!
# Final closure of Trace-Tempered Choice, Theorem 1

This module packages the last logical step of the proof.  Once the reached-
branch payoff increment formula is available, the full-support value assembly
gives the canonical numerical formula.  The representation assembly then gives
both the within-channel representation and the finite-block moreover clause
with exactly the same material utility and trace coefficient.  The converse
direction is the already kernel-checked benchmark implication.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

/-- The one remaining premise, quantified at exactly the scope needed to close
`Theorem1Statement`. -/
def Theorem1PositiveBranchPayoffIncrementPremise : Prop :=
  ∀ (O : Type u) [Fintype O] [DecidableEq O],
    2 ≤ Fintype.card O →
    ∀ (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F),
      PositiveBranchPayoffIncrementFormula F h

/-- For a fixed preference family satisfying the axioms, the positive reached-
branch payoff increment formula supplies the complete representation witnesses,
including the same-witness block comparison clause. -/
theorem traceTemperedAxioms_imply_representation_and_block_of_positiveBranchPayoffIncrement
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (hpositive : PositiveBranchPayoffIncrementFormula F h) :
    ∃ (u : O → ℝ) (lambda : ℝ),
      ¬ IsConstantPayoffIndex u ∧
      0 < lambda ∧
      WithinChannelRepresentation F u lambda ∧
      SameWitnessBlockRepresentation F u lambda := by
  have hvalue : FullSupportNormalizedValueFormula F h :=
    fullSupportNormalizedValueFormula_of_positiveBranchPayoffIncrement
      F h hpositive
  obtain ⟨hwithin, hblock⟩ :=
    representationClauses_of_fullSupportNormalizedValueFormula F h hvalue
  exact ⟨materialPayoffUtility F h, globalTraceLambda F h,
    materialPayoffUtility_nonconstant F h, globalTraceLambda_pos F h,
    hwithin, hblock⟩

/-- Fixed-family closure: a branch-increment proof for every axioms witness
gives both clauses appearing under the payoff-alphabet quantifier in
`Theorem1Statement`.  The reverse implication uses the benchmark construction
for all eight axioms. -/
theorem theorem1Clauses_of_positiveBranchPayoffIncrement
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (hpositive : ∀ h : TraceTemperedAxioms F,
      PositiveBranchPayoffIncrementFormula F h) :
    (TraceTemperedAxioms F ↔
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧
        0 < lambda ∧
        WithinChannelRepresentation F u lambda) ∧
    (TraceTemperedAxioms F →
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧
        0 < lambda ∧
        WithinChannelRepresentation F u lambda ∧
        SameWitnessBlockRepresentation F u lambda) := by
  constructor
  · constructor
    · intro h
      obtain ⟨u, lambda, hnonconstant, hlambda, hwithin, _hblock⟩ :=
        traceTemperedAxioms_imply_representation_and_block_of_positiveBranchPayoffIncrement
          F h (hpositive h)
      exact ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
    · rintro ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
      exact traceTemperedAxioms_of_representation
        hnonconstant hlambda hwithin
  · intro h
    exact
      traceTemperedAxioms_imply_representation_and_block_of_positiveBranchPayoffIncrement
        F h (hpositive h)

/-- The complete formal theorem follows from a proof of the single remaining
positive-branch increment premise for every payoff alphabet and preference
family in its stated scope. -/
theorem theorem1Statement_of_positiveBranchPayoffIncrement
    (hpositive : Theorem1PositiveBranchPayoffIncrementPremise.{u}) :
    Theorem1Statement.{u} := by
  intro O _instFintype _instDecidableEq _hcard F
  exact theorem1Clauses_of_positiveBranchPayoffIncrement F
    (fun h ↦ hpositive O _hcard F h)

end TraceTemperedChoiceVerification
