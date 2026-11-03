import TraceableAgency.Section3.UniquenessParameters
import TraceableAgency.Theorem1.MaterialCalibration.Proof

/-!
# Section 3: the complete uniqueness proposition

The ordinal statement uses exactly the finite-domain common-scale definition.
The cardinal statement adds precisely numerical branch additivity, rather
than strengthening the ordinal axioms. The final theorem obtains its
representation witnesses from the material-first proof of A1--A8.
-/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1

universe u

variable {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]

/-- The two parts of Proposition `Uniqueness`, for any fixed representing
parameters. The hypotheses are the representation itself and its positive
information weight, so no additional regularity is imposed on `W`. -/
theorem uniqueness_for_representation
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hrep : WithinChannelRepresentation F u lambda) :
    (∀ W : CommonIndex O,
      CommonScaleRepresentation F W ↔
        ∃ phi : Set.Ici (minPayoff u) → ℝ, StrictMono phi ∧
          ∀ E, W E = phi ⟨valueIndex u lambda E,
            minPayoff_le_valueIndex u hlambda.le E⟩) ∧
    (∀ W : CommonIndex O, CommonScaleRepresentation F W →
      (BranchAdditiveIndex W ↔ ∃ alpha beta : ℝ, 0 < alpha ∧
        ∀ E, W E = alpha * valueIndex u lambda E + beta)) :=
  ⟨commonScale_iff_strictMono_transform hlambda hrep,
    fun _ hW => branchAdditive_iff_positiveAffine hlambda hrep hW⟩

/-- A1--A8 provide witnesses with both complete uniqueness clauses. All
alphabets in the clauses remain arbitrary finite nonempty alphabets, and
all priors (not just full-support priors) are included. -/
theorem uniqueness_of_axioms
    (F : FixedPayoffPrefFamily O) (haxioms : TraceTemperedAxiomsV10 F) :
    ∃ (u : O → ℝ) (lambda : ℝ) (hlambda : 0 < lambda),
      ¬ IsConstantPayoffIndex u ∧ WithinChannelRepresentation F u lambda ∧
      SameWitnessBlockRepresentation F u lambda ∧
      (∀ W : CommonIndex O,
        CommonScaleRepresentation F W ↔
          ∃ phi : Set.Ici (minPayoff u) → ℝ, StrictMono phi ∧
            ∀ E, W E = phi ⟨valueIndex u lambda E,
              minPayoff_le_valueIndex u hlambda.le E⟩) ∧
      (∀ W : CommonIndex O, CommonScaleRepresentation F W →
        (BranchAdditiveIndex W ↔ ∃ alpha beta : ℝ, 0 < alpha ∧
          ∀ E, W E = alpha * valueIndex u lambda E + beta)) ∧
      (∀ (v : O → ℝ) (mu : ℝ), WithinChannelRepresentation F v mu →
        ∃ alpha beta : ℝ, 0 < alpha ∧
          (∀ o, v o = alpha * u o + beta) ∧ mu = alpha * lambda) := by
  obtain ⟨u, lambda, hnonconstant, hlambda, hrep, hblock⟩ :=
    (MaterialCalibration.theorem1V10Clauses_material F).2 haxioms
  obtain ⟨hordinal, hcardinal⟩ := uniqueness_for_representation hlambda hrep
  exact ⟨u, lambda, hlambda, hnonconstant, hrep, hblock, hordinal, hcardinal,
    fun _ _ hrep' => traceTempered_parameters_unique hlambda hrep hrep'⟩

end TraceableAgency.Section3
