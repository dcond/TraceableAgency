import TraceableAgency.Theorem1.MaterialCalibration.TraceEntropy
import TraceableAgency.Theorem1.MaterialCalibration.Representation

/-!
# From the new entropy coefficient to the full representation

This assembly is parameterized by a Shannon formula for the material-normalized
full-revelation functional. The entropy-reduction identity then identifies
record value, and the material separation and support arguments finish the
representation with that same coefficient.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

theorem constantRecordValueFormula_of_materialEntropy_eq
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ)
    (hentropy : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A), materialEntropy F h q = lambda * entropy q) :
    ConstantRecordValueFormula F h lambda := by
  intro A Y _ _ _ _ _ _ q hq P
  change materialTraceValue F h q hq P = _
  rw [materialTraceValue_eq_entropy_sub_expected, hentropy,
    mutualInfo_entropyReduction, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _hy
  rw [hentropy]
  unfold branchPosterior
  ring

theorem representation_and_block_of_materialEntropy_eq
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ)
    (hentropy : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A), materialEntropy F h q = lambda * entropy q) :
    WithinChannelRepresentation F (materialPayoffUtility F h) lambda ∧
      SameWitnessBlockRepresentation F (materialPayoffUtility F h) lambda := by
  apply representationClauses_of_materialNormalizedValueFormula F h lambda
  apply materialNormalizedValueFormula_of_constantRecordValueFormula F h lambda
  exact constantRecordValueFormula_of_materialEntropy_eq F h lambda hentropy

end TraceableAgency.Theorem1.MaterialCalibration
