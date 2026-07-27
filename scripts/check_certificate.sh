#!/usr/bin/env bash
set -euo pipefail

echo "== Lean/Lake versions =="
lake --version
lake env lean --version

echo
echo "== Building project =="
lake build

cat > /tmp/final_certificate_check.lean <<'LEAN'
import TraceableAgency.MainTheorem

open TraceableAgency

#print MainCharacterizationWithMoreover_of_FinalHM
#check MainCharacterizationWithMoreover_of_FinalHM
#print axioms MainCharacterizationWithMoreover_of_FinalHM
#print MainCharacterizationWithMoreover
#print MainCharacterization
#print MIRep
#print BlockSameScaleRep
#print TraceAxioms
#print ClassicalFaddeevTheoremAssumptions
#print FiniteFaddeevStandardHypotheses
#print FinalHMInterface
#print FiniteSamePosteriorLawBlackwellEquivalenceAssumptions
#print FiniteAdaptedSimplexBarycentricGrid
#print ClassicalHersteinMilnorMixtureTheoremAssumptions
#print AbstractConvexMixtureSpace
#print ContinuousIndependentWeakOrder
#print AffineUtilityRepresentation
#check AbstractConvexMixtureSpace.mix_self
#check AbstractConvexMixtureSpace.mix_swap
#print FinitePosteriorIntegralRepresentationAssumptions
#check FiniteAdaptedSimplexBarycentricGrid.exists_adaptedGrid
#check samePosteriorLawExp_all_test_functions
#check finitePosteriorLawFixedSandwich
#check finitePosteriorIntegralRepresentation_of_finite
#check continuousIndependentWeakOrder_posteriorLaw
#check posteriorLawAbstractConvexMixtureSpace
#check finiteHersteinMilnorConclusion_of_generic
#print axioms finiteHersteinMilnorConclusion_of_generic
#check posteriorValue_eq_integral_finite
#check sum_weighted_entropy_le_entropy_actionPushforward
#check mutualInfo_action_bayes_pushforward_le
#check mutualInfo_outcome_postprocess_le
#check posteriorLawContinuity_of_axioms
#check posteriorLawContinuity_of_FinalHMInterface
#check faddeevBinaryEntropy_continuous_of_axioms
#check finiteFaddeevStandardHypotheses_of_axioms
#print axioms finiteFaddeevStandardHypotheses_of_axioms
#check canonicalPosteriorValue_supportFace
#check canonicalPosteriorValue_relabel
#check finalConstructedCardinalGaugeSelectedRelabeling
#check finalConstructedBoundaryValueSupportRead_of_FinalHM_TraceAxioms
#check cardinalScaleBranchResultFor
#print BenchmarkStatement
#print BenchmarkStatement_of_MIRep
#print blockSameScaleRep_of_MIRep
#check MIRep_of_TraceAxioms_FinalHM_Faddeev
#print axioms MIRep_of_TraceAxioms_FinalHM_Faddeev
LEAN

echo
echo "== Checking public theorem boundary =="
lake env lean /tmp/final_certificate_check.lean

echo
echo "== Hygiene checks =="
if rg "\bsorry\b" TraceableAgency; then
  echo "ERROR: found 'sorry' in Lean source."
  exit 1
fi
if rg "\badmit\b" TraceableAgency; then
  echo "ERROR: found 'admit' in Lean source."
  exit 1
fi
if rg "^\s*axiom\s" TraceableAgency; then
  echo "ERROR: found declaration-level axiom in Lean source."
  exit 1
fi
if rg "reverse_binary|of_recursion|ClassicalFiniteHersteinMilnorTheoremAssumptions" TraceableAgency; then
  echo "ERROR: found a removed convention or project-shaped theorem boundary."
  exit 1
fi

echo "Verification passed."
