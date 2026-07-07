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

#print MainCharacterizationWithMoreover_clean
#check MainCharacterizationWithMoreover_clean
#print axioms MainCharacterizationWithMoreover_clean
#print MainCharacterizationWithMoreover
#print MainCharacterization
#print MIRep
#print BlockSameScaleRep
#print TraceAxioms
#print ClassicalFaddeevTheoremAssumptions
#print FinalHMInterface
#print FiniteDPIAssumptions
#print FiniteSamePosteriorLawBlackwellEquivalenceAssumptions
#print FiniteHersteinMilnorAssumptions
#print ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions
#print FinitePosteriorLawValueAffineAssumptions
#print FinitePosteriorIntegralRepresentationAssumptions
#print BenchmarkStatement
#print BenchmarkStatement_of_DPI
#print blockSameScaleRep_of_MIRep
#check MIRep_of_TraceAxioms_FinalHM_Faddeev_clean
#print axioms MIRep_of_TraceAxioms_FinalHM_Faddeev_clean
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

echo "Verification passed."
