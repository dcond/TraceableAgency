/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Main
import TraceableAgency.External.Faddeev

/-!
# Main Theorem Assembly from External Assumptions

This file assembles the full main characterization theorem from explicit
external assumption bundles.

## Main results

* `MainCharacterization_of_external_assumptions` - TraceAxioms F ↔ MIRep F
* `MainCharacterizationWithMoreover_of_external_assumptions` - full theorem with
  block-scale moreover clause

## Dependencies

The proof combines:
1. `SufficiencyStatement_of_external_assumptions` (from External/Faddeev.lean)
2. `BenchmarkStatement_of_DPI` (from Main.lean)
3. `blockScaleStatement_from_sufficiency` + `blockScaleFromMIRepStatement`
4. `main_characterization_from_spine`

## External Assumptions

- **Sufficiency**: `SufficiencyExternalAssumptions` bundles the remaining
  sufficiency assumptions; support-restriction boundary assembly is now internal
- **Benchmark**: `FiniteDPIAssumptions` bundles finite data processing inequalities
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
## Full Main Theorem Modulo External Assumptions
-/

/--
**Main Characterization from External Assumptions**

The main theorem TraceAxioms F ↔ MIRep F, proved modulo explicit external
assumption bundles for sufficiency and benchmark.

This theorem states: given the sufficiency external assumptions and the
finite DPI assumptions, the full main characterization holds.
-/
theorem MainCharacterization_of_external_assumptions
    (hsuff : SufficiencyExternalAssumptions.{u})
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterization.{u} := by
  intro F
  constructor
  · intro hax
    exact (SufficiencyStatement_of_external_assumptions hsuff) F hax
  · intro hrep
    exact (BenchmarkStatement_of_DPI hdpi) F hrep

/--
**Main Characterization With Moreover from External Assumptions**

The full main theorem including the "moreover" clause about block-supported
cross-channel comparisons being on the same MI scale.

Paper: Theorem 1 (lines 770-787 of empowerment_v5.tex)

This combines:
1. `SufficiencyStatement_of_external_assumptions`
2. `BenchmarkStatement_of_DPI`
3. `blockScaleStatement_from_sufficiency` + `blockScaleFromMIRepStatement`
4. `main_characterization_from_spine`
-/
theorem MainCharacterizationWithMoreover_of_external_assumptions
    (hsuff : SufficiencyExternalAssumptions.{u})
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  apply main_characterization_from_spine
  · exact SufficiencyStatement_of_external_assumptions hsuff
  · exact BenchmarkStatement_of_DPI hdpi
  · exact blockScaleStatement_from_sufficiency
      (SufficiencyStatement_of_external_assumptions hsuff)
      blockScaleFromMIRepStatement

/-!
## Combined Assumption Bundle
-/

/--
**All External Assumptions Bundle**

Combines both sufficiency and benchmark external assumptions into a single bundle.
This provides a complete specification of what is assumed to prove the main theorem.
-/
structure AllExternalAssumptions.{v} where
  /-- Sufficiency external assumptions; support assembly is internal. -/
  sufficiency : SufficiencyExternalAssumptions.{v}
  /-- Finite DPI assumptions for benchmark direction -/
  dpi : FiniteDPIAssumptions.{v}

/--
**Main Characterization With Moreover from All External Assumptions**

The full main theorem from a single combined assumption bundle.
-/
theorem MainCharacterizationWithMoreover_of_all_assumptions
    (h : AllExternalAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} :=
  MainCharacterizationWithMoreover_of_external_assumptions h.sufficiency h.dpi

/--
**Main Characterization from All External Assumptions**

The basic characterization (without moreover) from a single combined assumption bundle.
-/
theorem MainCharacterization_of_all_assumptions
    (h : AllExternalAssumptions.{u}) :
    MainCharacterization.{u} :=
  MainCharacterization_of_external_assumptions h.sufficiency h.dpi

/-!
## Summary of External Assumptions

The full main theorem depends on:

### Sufficiency Direction (SufficiencyExternalAssumptions)
1. `FiniteSamePosteriorLawBlackwellEquivalenceAssumptions` - classical finite
   same-posterior-law mutual garbling; `FiniteBlackwellPosteriorAssumptions`
   is reconstructed internally from this plus A4/A3/A1 block replacement
2. `FiniteHersteinMilnorAssumptions` - posterior value representation
   (classical Herstein-Milnor plus paper-specific quotient interface)
3. `FiniteBranchAggregationAssumptions` - branch aggregation compatibility
   monolith.  The faithful branch route is exposed separately through
   `SufficiencyFaithfulBranchAssumptions`, which produces
   `BranchAggregationStructure`, `BranchChainStructure`, and the normalized
   chain rule without using the old hax-free/global branch packages.
4. `FiniteScaleCoherenceAssumptions` - universal scale
5. `FiniteCrossPriorBlockAssumptions` - law-level posterior value affinity,
   first-slice affine uniqueness, second-coordinate intercept affine
   uniqueness, second-coordinate slope affine uniqueness, posterior value
   relabeling coherence, singleton coefficient gauge convention,
   singleton swap/rho gauge convention, reference-gauge transform and
   current-representative gauge convention, and singleton interaction gauge
   convention; Lean proves singleton slice affinity internally (Stage 10N),
   public-mix posterior-law mixture structurally, derives channel-level value
   public-mix affinity, A1 experiment-pair strictness, value nonconstancy,
   product-slice public-mix affinity, the intercept, slope, nondegenerate
   C1-C3 coefficient extraction, triple-product value associativity from
   value relabeling, product-swap value equality and nondegenerate rho
   reciprocity, derives the positive gauge-choice package from the reference
   gauge convention, Step 3 gauge normalization, proves K1-K4 interaction
   associativity from normalized triple-product expansions, proves interaction
   swap symmetry from product-swap value equality and normalized coefficients,
   proves singleton interaction-term degeneracy, derives the common-κ
   interaction package from the remaining singleton convention,
   and derives gauge coherence packages,
   affine-slice uniqueness,
   left-slice affinity, pairwise product bilinear form, coherent product
   quasi-additivity via `coherentnorm_of_decomposed_components`, the
   product-lift value identities, and
   product-block transfer from A3/A4/A5, then assembles the unscaled
   cross-prior blockbridge and converts it to the normalized bridge by
   universal scale
6. `FiniteEntropyRegularityFromAxiomsAssumptions` - entropy regularity
7. `FiniteHfunBlockEmbeddingInvarianceAssumptions` - fibre embedding invariance
8. `FiniteCoarseRevealEntropyReductionAssumptions` - coarse-reveal entropy reduction
9. `FiniteCardinalSupportBoundaryAssumptions` - cardinal support boundary extension
10. `ClassicalFaddeevTheoremAssumptions` - classical Faddeev theorem/application
Support-restriction boundary assembly is now proved internally from A5, A1, and
A3 in `External.SupportRestriction`.
Finite action/outcome relabeling invariance is now proved internally from A4,
A5, A3, and A1 transitivity in `External.Relabeling`.

### Benchmark Direction (FiniteDPIAssumptions)
1. Outcome post-processing DPI: I(q, P∘T) ≤ I(q, P)
2. Action Bayes-pushforward DPI: I(qS, P̂) ≤ I(q, P)

### Pure Lean Proofs
The following are proved in pure Lean without external assumptions:
- `FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm` (final sufficiency bridge)
- `FullSupportBlockMI_of_FaddeevEntropyForm` (full-support block/cross-support MI)
- `MIRep_of_SufficiencyMIPackage` (collapse from α·MI to MI)
- `blockSameScaleRep_of_MIRep` (block scale from MI representation)
- `main_characterization_from_spine` (logical assembly)
-/

end TraceableAgency
