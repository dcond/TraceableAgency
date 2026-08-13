/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.FullSupportValueAssembly
import TraceableAgency.Theorem1.RepresentationAssembly
import TraceableAgency.Theorem1.PositiveBranchIncrement
import TraceableAgency.Theorem1.Benchmark
import TraceableAgency.Theorem1.RelevanceBridge

/-!
# Final closure of Trace-Tempered Choice, Theorem 1

The fixed-channel relevance bridge chooses the single trace anchor from v4
inside the proposition being proved.  The anchor-indexed proof bundle then
feeds the branch increment, full-support value assembly, and representation
assembly.  The converse returns to the exact fixed A3/A4 benchmark channels.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-- An anchor-indexed semantic axiom bundle yields one set of representation
witnesses, including the same-witness finite-block clause. -/
theorem traceTemperedBridgeAxioms_imply_representation_and_block
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    ∃ (u : O → ℝ) (lambda : ℝ),
      ¬ IsConstantPayoffIndex u ∧
      0 < lambda ∧
      WithinChannelRepresentation F u lambda ∧
      SameWitnessBlockRepresentation F u lambda := by
  have hpositive : PositiveBranchPayoffIncrementFormula F h :=
    positiveBranchPayoffIncrementFormula F h
  have hvalue : FullSupportNormalizedValueFormula F h :=
    fullSupportNormalizedValueFormula_of_positiveBranchPayoffIncrement
      F h hpositive
  obtain ⟨hwithin, hblock⟩ :=
    representationClauses_of_fullSupportNormalizedValueFormula F h hvalue
  exact ⟨materialPayoffUtility F h, globalTraceLambda F h,
    materialPayoffUtility_nonconstant F h, globalTraceLambda_pos F h,
    hwithin, hblock⟩

/-- Fixed-family closure for the exact v4 axioms. -/
theorem theorem1V4Clauses
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) :
    (TraceTemperedAxiomsV4 F ↔
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧
        0 < lambda ∧
        WithinChannelRepresentation F u lambda) ∧
    (TraceTemperedAxiomsV4 F →
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧
        0 < lambda ∧
        WithinChannelRepresentation F u lambda ∧
        SameWitnessBlockRepresentation F u lambda) := by
  constructor
  · constructor
    · intro hv4
      obtain ⟨_traceAnchor, hbridge⟩ :=
        traceTemperedBridgeAxioms_of_v4 F hv4
      obtain ⟨u, lambda, hnonconstant, hlambda, hwithin, _hblock⟩ :=
        traceTemperedBridgeAxioms_imply_representation_and_block F hbridge
      exact ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
    · rintro ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
      exact traceTemperedAxiomsV4_of_representation
        hnonconstant hlambda hwithin
  · intro hv4
    obtain ⟨_traceAnchor, hbridge⟩ :=
      traceTemperedBridgeAxioms_of_v4 F hv4
    exact traceTemperedBridgeAxioms_imply_representation_and_block F hbridge

/-- Complete exact v4 statement, including the same-witness clause. -/
theorem theorem1StatementV4 : Theorem1StatementV4.{u} := by
  intro O _instFintype _instDecidableEq _hcard F
  exact theorem1V4Clauses F

/-- Compatibility closure for the historical v3 bundle. -/
theorem theorem1V3Clauses
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) :
    (TraceTemperedAxiomsV3 F ↔
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧
        0 < lambda ∧
        WithinChannelRepresentation F u lambda) ∧
    (TraceTemperedAxiomsV3 F →
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧
        0 < lambda ∧
        WithinChannelRepresentation F u lambda ∧
        SameWitnessBlockRepresentation F u lambda) := by
  constructor
  · constructor
    · intro hv3
      obtain ⟨_traceAnchor, hbridge⟩ :=
        traceTemperedBridgeAxioms_of_v3 F hv3
      obtain ⟨u, lambda, hnonconstant, hlambda, hwithin, _hblock⟩ :=
        traceTemperedBridgeAxioms_imply_representation_and_block F hbridge
      exact ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
    · rintro ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
      exact traceTemperedAxioms_of_representation
        hnonconstant hlambda hwithin
  · intro hv3
    obtain ⟨_traceAnchor, hbridge⟩ :=
      traceTemperedBridgeAxioms_of_v3 F hv3
    exact traceTemperedBridgeAxioms_imply_representation_and_block F hbridge

/-- Historical statement retained as a proved compatibility theorem. -/
theorem theorem1StatementV3 : Theorem1StatementV3.{u} := by
  intro O _instFintype _instDecidableEq _hcard F
  exact theorem1V3Clauses F

end TraceableAgency.Theorem1
