/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.BranchScaleIdentification
import TraceableAgency.Theorem1.DummyBranchBridge
import TraceableAgency.Theorem1.FullSupportValueAssembly

/-!
# The unconditional positive-branch payoff increment

Adjoin the fixed full-support two-action reference dummy to the first-stage
action.  The reached posterior in the enlarged problem has nontrivial support,
so the calibrated nontrivial-support increment theorem applies.  Exact dummy
invariance of normalized marked utility and exact preservation of branch mass
then transport the formula back to the original problem, including the case
where the original reached posterior has singleton support.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-- Every positive branch has the probability-weighted material-payoff
increment, without any nontriviality assumption on its posterior support. -/
theorem positiveBranchPayoffIncrementFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    PositiveBranchPayoffIncrementFormula F h := by
  classical
  intro A Y _ _ _ _ _ _ _ q hq P target htarget o
  let s : TraceableAgency.Dist TraceReferenceAction.{u} :=
    traceReferencePrior.{u}
  have hs : s.FullSupport := traceReferencePrior_fullSupport.{u}
  have hqs : (prodDist q s).FullSupport :=
    markedDummy_prodDist_fullSupport q s hq hs
  have hliftPositive :
      BranchPositive
        (independentDummyFirstStage
          (B := TraceReferenceAction.{u}) P)
        (prodDist q s) target :=
    branchPositive_independentDummyFirstStage P q s target htarget
  letI : Nontrivial
      (supportSubtype
        (branchPosterior
          (independentDummyFirstStage
            (B := TraceReferenceAction.{u}) P)
          (prodDist q s) target)) :=
    supportSubtype_branchPosterior_independentDummyFirstStage_nontrivial
      P q s hs target htarget
  have hlift :=
    positiveBranchPayoffIncrement_of_nontrivialSupport
      F h (prodDist q s) hqs
        (independentDummyFirstStage
          (B := TraceReferenceAction.{u}) P)
        target hliftPositive o
  rw [
    normalizedMarkedUtility_payoffBranch_independentDummy
      F h q s hq hs P
        (updateBranchPayoff
          (fun _ : Y ↦ materialLowOutcome F h) target o),
    normalizedMarkedUtility_payoffBranch_independentDummy
      F h q s hq hs P
        (fun _ : Y ↦ materialLowOutcome F h),
    branchMass_independentDummyFirstStage P q s target] at hlift
  exact hlift

end TraceableAgency.Theorem1
