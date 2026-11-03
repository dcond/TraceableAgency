import TraceableAgency.Theorem1.MaterialCalibration.PayoffSeparation
import TraceableAgency.Theorem1.MaterialCalibration.TraceValue

/-!
# Strict positivity before Shannon identification

Trace relevance holds at the designated payoff. Material payoff separation
moves that comparison to the low payoff without changing its strictness.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Changing the constant payoff under full revelation adds exactly its
normalized material utility. -/
theorem normalizedMarkedUtility_fullReveal_const_material_shift
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (o : O) :
    normalizedMarkedUtility F h q hq
        (fullRevealWithPayoffExperiment (fun _ : A ↦ o)) -
      materialEntropy F h q = materialPayoffUtility F h o := by
  rw [materialEntropy_eq_fullReveal F h q hq,
    normalizedMarkedUtility_fullRevealWithPayoff_eq_payoffBranch,
    normalizedMarkedUtility_fullRevealWithPayoff_eq_payoffBranch,
    normalizedMarkedUtility_payoffBranch_difference_from_low_material]
  simp only [identityChannel_outcomeMarginal, ← Finset.sum_mul, q.sum_eq_one,
    one_mul]

/-- Full revelation has strictly positive material-normalized information
value at every interior prior on a nontrivial action alphabet. -/
theorem materialEntropy_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    [Nontrivial A] (q : Dist A) (hq : q.FullSupport) :
    0 < materialEntropy F h q := by
  have hstrict := h.a8 q hq
  have hparts := (pairStrict_iff_pairWeak_not_swap F h.a1 h.a3 h.a4 h.a5
    q (fullRevealAtPayoff traceAnchor) q (uninformativeAtPayoff traceAnchor)).mp
      hstrict
  have hv : materialPayoffUtility F h traceAnchor <
      normalizedMarkedUtility F h q hq
        (fullRevealWithPayoffExperiment (fun _ : A ↦ traceAnchor)) := by
    apply lt_of_not_ge
    intro hle
    apply hparts.2
    rw [← payoffLotteryChannel_pure_eq_uninformative]
    exact (normalizedMarkedUtility_represents F h q hq
      (markedPayoffLotteryExperiment (Dist.pure traceAnchor))
      (fullRevealWithPayoffExperiment (fun _ : A ↦ traceAnchor))).mpr (by
        rwa [normalizedMarkedUtility_purePayoff_material])
  have hshift := normalizedMarkedUtility_fullReveal_const_material_shift
    F h q hq traceAnchor
  linarith

end TraceableAgency.Theorem1.MaterialCalibration
