import TraceableAgency.Section3.Independence.Pareto
import TraceableAgency.Section3.Independence.Lexicographic
import TraceableAgency.Section3.Independence.Relevance
import TraceableAgency.Section3.Independence.BlockCoherence
import TraceableAgency.Section3.Independence.RecordProcessing
import TraceableAgency.Section3.Independence.ActionProcessing
import TraceableAgency.Section3.Independence.Satiation

/-! # Independence of the eight exact paper axioms -/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1 Independence

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

/-- Index `0` is A1, ..., index `7` is A8. These are the original
behavioral predicates, not numerical surrogates for them. -/
def PaperAxiom (F : FixedPayoffPrefFamily O) (i : Fin 8) : Prop :=
  match i.val with
  | 0 => A1_WeakOrder F
  | 1 => A2_Continuity F
  | 2 => A3_MaterialRelevance F
  | 3 => A4_TraceRelevance F
  | 4 => A5_BlockComparisonCoherence F
  | 5 => A6_RecordDataProcessing F
  | 6 => A7_ActionDataProcessing F
  | _ => A8_RecordwiseSureThing F

/-- Every axiom can fail while all seven others hold, on any fixed finite
payoff alphabet with at least two elements. -/
theorem axioms_independent [Nontrivial O] (i : Fin 8) :
    ∃ F : FixedPayoffPrefFamily O,
      (∀ j : Fin 8, j ≠ i → PaperAxiom F j) ∧ ¬ PaperAxiom F i := by
  classical
  obtain ⟨om, op, hne⟩ := exists_pair_ne O
  let v : O → ℝ := fun o => if o = op then 1 else 0
  have hlt : v om < v op := by simp [v, hne]
  have hv : ¬ IsConstantPayoffIndex v := by
    rintro ⟨c, hc⟩
    simpa [hc om, hc op] using hlt
  fin_cases i
  · have h := pareto_counterexample v op om hlt
    refine ⟨paretoFamily v, ?_, h.1⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]
  · have h := lex_counterexample v op om hlt
    refine ⟨lexFamily v, ?_, h.2.1⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]
  · have h := informationOnly_counterexample (O := O)
    refine ⟨traceScoreFamily (fun _ : O => 0) 1, ?_, h.2.2.1⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]
  · have h := materialOnly_counterexample v hv
    refine ⟨traceScoreFamily v 0, ?_, h.2.2.2.1⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]
  · have h := supportBonus_counterexample v hv
    refine ⟨supportBonusFamily v, ?_, h.2.2.2.2.1⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]
  · have h := noise_counterexample v op om hlt
    refine ⟨noiseFamily v, ?_, h.2.2.2.2.2.1⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]
  · have h := actionEntropy_counterexample v hv
    refine ⟨actionEntropyFamily v, ?_, h.2.2.2.2.2.2.1⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]
  · have h := satiation_counterexample v hv (by norm_num : (0:ℝ)<1)
    refine ⟨satiationFamily v 1, ?_, h.2.2.2.2.2.2.2⟩
    intro j hj
    fin_cases j <;> simp_all [PaperAxiom]

/-- Logical non-derivability formulation of the same independence result. -/
theorem no_axiom_implied_by_other_seven [Nontrivial O] (i : Fin 8) :
    ¬ (∀ F : FixedPayoffPrefFamily O,
      (∀ j : Fin 8, j ≠ i → PaperAxiom F j) → PaperAxiom F i) := by
  intro himplied
  obtain ⟨F, hothers, hfail⟩ := axioms_independent (O := O) i
  exact hfail (himplied F hothers)

end TraceableAgency.Section3
