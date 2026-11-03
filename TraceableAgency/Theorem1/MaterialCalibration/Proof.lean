import TraceableAgency.Theorem1.MaterialCalibration.ShannonIdentification
import TraceableAgency.Theorem1.MaterialCalibration.ShannonAssembly
import TraceableAgency.Theorem1.RelevanceBridge

/-!
# Theorem 1 by the material-first route

Material relevance first calibrates all continuation coefficients. The
resulting entropy functional satisfies grouping and continuity, so the generic
finite Faddeev theorem identifies one positive information coefficient.
Payoff separation and support restriction supply the complete representation.
The original proof and its public entry point are unchanged.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

theorem traceTemperedBridgeAxioms_imply_representation_and_block_material
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    ∃ (u : O → ℝ) (lambda : ℝ),
      ¬ IsConstantPayoffIndex u ∧ 0 < lambda ∧
      WithinChannelRepresentation F u lambda ∧
      SameWitnessBlockRepresentation F u lambda := by
  obtain ⟨lambda, hlambda, hentropy⟩ := exists_pos_materialEntropy_eq_entropy F h
  obtain ⟨hwithin, hblock⟩ := representation_and_block_of_materialEntropy_eq
    F h lambda hentropy
  exact ⟨materialPayoffUtility F h, lambda, materialPayoffUtility_nonconstant F h,
    hlambda, hwithin, hblock⟩

/-- The exact paper axioms characterize the same representation, with one set
of witnesses also representing every finite-block comparison. -/
theorem theorem1V10Clauses_material
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) :
    (TraceTemperedAxiomsV10 F ↔
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧ 0 < lambda ∧
        WithinChannelRepresentation F u lambda) ∧
    (TraceTemperedAxiomsV10 F →
      ∃ (u : O → ℝ) (lambda : ℝ),
        ¬ IsConstantPayoffIndex u ∧ 0 < lambda ∧
        WithinChannelRepresentation F u lambda ∧
        SameWitnessBlockRepresentation F u lambda) := by
  constructor
  · constructor
    · intro hv10
      obtain ⟨traceAnchor, hbridge⟩ := traceTemperedBridgeAxioms_of_v10 F hv10
      obtain ⟨u, lambda, hnonconstant, hlambda, hwithin, _hblock⟩ :=
        traceTemperedBridgeAxioms_imply_representation_and_block_material F hbridge
      exact ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
    · rintro ⟨u, lambda, hnonconstant, hlambda, hwithin⟩
      exact traceTemperedAxiomsV10_of_representation hnonconstant hlambda hwithin
  · intro hv10
    obtain ⟨traceAnchor, hbridge⟩ := traceTemperedBridgeAxioms_of_v10 F hv10
    exact traceTemperedBridgeAxioms_imply_representation_and_block_material F hbridge

/-- A second proof of the unchanged complete public Theorem 1 statement. -/
theorem theorem1StatementV10_material : Theorem1StatementV10.{u} := by
  intro O _ _ _ F
  exact theorem1V10Clauses_material F

end TraceableAgency.Theorem1.MaterialCalibration

namespace TraceTemperedChoiceVerification

universe u

/-- Material-first proof of Theorem 1, including the same-witness block clause. -/
theorem trace_tempered_choice_v10_theorem1_material :
    TraceableAgency.Theorem1.Theorem1StatementV10.{u} :=
  TraceableAgency.Theorem1.MaterialCalibration.theorem1StatementV10_material

end TraceTemperedChoiceVerification
