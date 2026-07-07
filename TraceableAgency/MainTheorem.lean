/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Main
import TraceableAgency.External.Faddeev
import TraceableAgency.External.EntropyReductionClosure

/-!
# Main Theorem Assembly from Known Results

This file assembles the full main characterization theorem.  The canonical
paper-facing route is the cardinal-gauge route from named known results:
classical Faddeev, the final HM interface, the constructed-representative
known-result package, and finite DPI for the benchmark direction.  Product
normalisation, support-scale, cardinal-boundary, branch/scale/cross-prior
monoliths, and posterior-law-continuity assumptions are kept off the public
theorem boundary.

## Main results

* `MainCharacterization_of_final_known_results` - TraceAxioms F ↔ MIRep F
* `MainCharacterizationWithMoreover_of_final_known_results` - canonical theorem
  with the block-scale moreover clause

## Dependencies

The proof combines:
1. `SufficiencyStatement_of_final_known_results`
2. `BenchmarkStatement_of_DPI` (from Main.lean)
3. `blockScaleStatement_from_sufficiency` + `blockScaleFromMIRepStatement`
4. `main_characterization_from_spine`

## Known-Result Inputs

- **Sufficiency**: classical Faddeev, final HM, and the per-axiom
  cardinal-gauge constructed-representative known result
- **Benchmark**: `FiniteDPIAssumptions` bundles finite data processing inequalities
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
## Final Main Route: Known Results plus Internalized Normalizations
-/

/--
**Sufficiency from Final Known Results**

This is the cleaned sufficiency route after the pre-entropy/cardinal/product
graft.  The obsolete sufficiency wrapper is deliberately absent: the theorem takes
exactly the named classical results and the per-axiom cardinal-gauge
known-result constructor used by the proof.
-/
theorem SufficiencyStatement_of_final_known_results
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (hknown :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FinalConstructedRepresentativeKnownResultsCardinalGaugeProductTransform
          hhm hax) :
    SufficiencyStatement.{u} := by
  intro F hax
  exact MIRep_of_TraceAxioms_FinalHM_Faddeev_withCardinalGaugeKnownResults
    hfad hhm hax (hknown hax)

/--
**Main Characterization from Final Known Results**

This theorem is the paper-facing route: the sufficiency direction uses the
cardinal-gauge construction directly from named known results, and the benchmark
direction uses finite DPI.  No sufficiency assumption bundle and no
posterior-law-continuity assumption appears at this boundary.
-/
theorem MainCharacterization_of_final_known_results
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (hknown :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FinalConstructedRepresentativeKnownResultsCardinalGaugeProductTransform
          hhm hax)
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterization.{u} := by
  intro F
  constructor
  · intro hax
    exact (SufficiencyStatement_of_final_known_results hfad hhm hknown) F hax
  · intro hrep
    exact (BenchmarkStatement_of_DPI hdpi) F hrep

/--
**Main Characterization With Moreover from Final Known Results**

The full theorem, including the block-scale moreover clause, using the final
known-result cardinal-gauge sufficiency route.
-/
theorem MainCharacterizationWithMoreover_of_final_known_results
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (hknown :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FinalConstructedRepresentativeKnownResultsCardinalGaugeProductTransform
          hhm hax)
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  apply main_characterization_from_spine
  · exact SufficiencyStatement_of_final_known_results hfad hhm hknown
  · exact BenchmarkStatement_of_DPI hdpi
  · exact blockScaleStatement_from_sufficiency
      (SufficiencyStatement_of_final_known_results hfad hhm hknown)
      blockScaleFromMIRepStatement

/--
**Main Characterization With Moreover, Exposing Only Pre-Entropy Inputs**

This is the audit-facing theorem boundary.  The branch/cardinal/product-gauge
representative is constructed internally from `FinalHMInterface` and
`TraceAxioms`; the only remaining sufficiency-side inputs are the six
pre-entropy transport/normalization facts for that constructed representative.
-/
theorem MainCharacterizationWithMoreover_onlyPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (coordinate_value :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteCoordinateSupportFaceValueTransportAssumptionsFor
          (finalConstructedCardinalGaugeFaceScales hhm hax))
    (coordinate_scale :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteCoordinateSupportFaceScaleTransportAssumptionsFor
          (finalConstructedCardinalGaugeFaceScales hhm hax))
    (block_value :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteBlockSupportFaceValueTransportFor
          (finalConstructedCardinalGaugeFaceScales hhm hax))
    (block_scale :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteBlockSupportFaceScaleTransportFor
          (finalConstructedCardinalGaugeFaceScales hhm hax))
    (reference_z :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteProductReferenceZNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax)
          (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    (universal_singleton :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteUniversalScaleSingletonNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax))
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  refine MainCharacterizationWithMoreover_of_final_known_results
    hfad hhm ?_ hdpi
  intro F hax
  exact
    finalConstructedRepresentativeKnownResultsCardinalGaugeProductTransform_of_preEntropy
      hhm hax
      (coordinate_value hax)
      (coordinate_scale hax)
      (block_value hax)
      (block_scale hax)
      (reference_z hax)
      (universal_singleton hax)

/--
**Sufficiency with Support-Read Pre-Entropy Internalized**

The coordinate value/scale facts are proved internally as support-read theorems
for the final constructed representative, and the block value/scale facts are
proved internally on the support face of the embedded block posterior.  The
remaining visible pre-entropy inputs are the two product/singleton
normalizations.
-/
theorem SufficiencyStatement_of_coordinateSupportReadPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (reference_z :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteProductReferenceZNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax)
          (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    (universal_singleton :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteUniversalScaleSingletonNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax)) :
    SufficiencyStatement.{u} := by
  intro F hax
  exact
    MIRep_of_TraceAxioms_FinalHM_Faddeev_withCoordinateSupportReadPreEntropy
      hfad hhm hax
      (reference_z hax)
      (universal_singleton hax)

/--
**Main Characterization With Moreover, Support-Read Route**

Audit-facing theorem after internalizing the coordinate and block support-face
value/scale facts.  No ambient coordinate or block transport hypothesis appears.
-/
theorem MainCharacterizationWithMoreover_coordinateSupportReadPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (reference_z :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteProductReferenceZNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax)
          (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    (universal_singleton :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteUniversalScaleSingletonNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax))
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  apply main_characterization_from_spine
  · exact SufficiencyStatement_of_coordinateSupportReadPreEntropy
      hfad hhm reference_z universal_singleton
  · exact BenchmarkStatement_of_DPI hdpi
  · exact blockScaleStatement_from_sufficiency
      (SufficiencyStatement_of_coordinateSupportReadPreEntropy
        hfad hhm reference_z universal_singleton)
      blockScaleFromMIRepStatement

/--
**Sufficiency with Only Reference-Z Pre-Entropy Remaining**

The universal singleton scale normalization is constructed internally from the
remaining product-reference `Z` normalization and the final cardinal-gauge
representative.  Thus `reference_z` is the only visible pre-entropy
normalization at this boundary.
-/
theorem SufficiencyStatement_of_onlyReferenceZ
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (reference_z :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteProductReferenceZNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax)
          (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax)) :
    SufficiencyStatement.{u} := by
  intro F hax
  exact
    MIRep_of_TraceAxioms_FinalHM_Faddeev_onlyReferenceZPreEntropy
      hfad hhm hax (reference_z hax)

/--
**Main Characterization With Moreover, Only Reference-Z Remaining**

Audit-facing theorem after internalizing the universal singleton scale
normalization.  The only visible sufficiency-side pre-entropy obligation is the
product-reference `Z` normalization for the internally constructed
cardinal-gauge representative.
-/
theorem MainCharacterizationWithMoreover_onlyReferenceZ
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (reference_z :
      ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F),
        FiniteProductReferenceZNormalizationFor
          (finalConstructedCardinalGaugeFaceScales hhm hax)
          (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  apply main_characterization_from_spine
  · exact SufficiencyStatement_of_onlyReferenceZ hfad hhm reference_z
  · exact BenchmarkStatement_of_DPI hdpi
  · exact blockScaleStatement_from_sufficiency
      (SufficiencyStatement_of_onlyReferenceZ hfad hhm reference_z)
      blockScaleFromMIRepStatement

/--
**Clean Sufficiency Statement**

All sufficiency-side pre-entropy normalization obligations are now constructed
internally for the final cardinal-gauge representative.  The only remaining
inputs are the paper axioms, supplied per `F`, and the accepted classical
Faddeev/HM interfaces.
-/
theorem SufficiencyStatement_clean
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u}) :
    SufficiencyStatement.{u} := by
  intro F hax
  exact MIRep_of_TraceAxioms_FinalHM_Faddeev_clean hfad hhm hax

/--
**Clean Main Characterization With Moreover**

Audit-facing theorem with no extra sufficiency-side conventions: reference-Z
normalization, universal singleton normalization, coordinate/block
support-face transport, branch data, product gauge, support scale, and
value-relabeling facts are all internalized before this boundary.
-/
theorem MainCharacterizationWithMoreover_clean
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u})
    (hdpi : FiniteDPIAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  apply main_characterization_from_spine
  · exact SufficiencyStatement_clean hfad hhm
  · exact BenchmarkStatement_of_DPI hdpi
  · exact blockScaleStatement_from_sufficiency
      (SufficiencyStatement_clean hfad hhm)
      blockScaleFromMIRepStatement

/-!
## Summary of Known-Result Inputs

The full main theorem depends on:

### Sufficiency Direction
1. `ClassicalFaddeevTheoremAssumptions` - classical Faddeev theorem/application
2. `FinalHMInterface` - final HM interface used by the constructed
   representative
3. `FinalConstructedRepresentativeKnownResultsCardinalGaugeProductTransform` -
   per-axiom known-result package for the cardinal-gauge product transform
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
