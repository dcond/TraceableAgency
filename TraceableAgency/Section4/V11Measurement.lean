import TraceableAgency.Section4.MeasurementDilution

/-! Proposition 32(iii), including the zero-dilution endpoint. -/
namespace TraceableAgency.Section4
open Theorem1 Section3
universe u

theorem dilution_compensation_feasible_iff_all_rates
    {O A B : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (v : O → ℝ) (lambda : ℝ) (q : Dist A) (p : Dist B)
    (eps : DilutionRate) (op om : O) (hu : v om < v op)
    (E : MarkedTerminalExperiment O A) (D : MarkedTerminalExperiment O B) :
    (∃ b b' : CompensationProbability,
      markedValue v lambda q (dilutionExperiment eps op om E b) =
        markedValue v lambda p (dilutionExperiment eps op om D b')) ↔
      |markedValue v lambda p D - markedValue v lambda q E| ≤
        eps.1 / (1-eps.1) * (v op-v om) := by
  by_cases he : 0 < eps.1
  · exact dilution_compensation_feasible_iff v lambda q p eps he op om hu E D
  · have hz : eps.1 = 0 := le_antisymm (le_of_not_gt he) eps.2.1
    simp only [dilutionExperiment, hz, ↓reduceDIte, sub_zero, zero_div, zero_mul,
      abs_nonpos_iff, sub_eq_zero]
    constructor
    · rintro ⟨_, _, h⟩
      exact h.symm
    · intro h
      exact ⟨compensationZero, compensationZero, h.symm⟩

end TraceableAgency.Section4
