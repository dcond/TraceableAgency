/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.CrossPrior
import TraceableAgency.PureTrace.Support.BranchAggregation.Compatibility
import TraceableAgency.PureTrace.Support.ScaleCoherence.Compatibility

namespace TraceableAgency

universe u

/-!
## Bridge Theorems

These theorems show how to use entropy reduction in the sufficiency spine.
-/

/--
**Entropy Reduction from Scale Coherence**

Given a scale coherence structure, derive an entropy reduction representation.
-/
noncomputable def entropyReduction_of_assumption
    (F : PrefFamily.{u})
    (hscale : ScaleCoherenceStructure F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_scale F hscale

/--
**Cross-Prior Block Representation from Unscaled Blockbridge**

Given the external unscaled paper blockbridge and an entropy-reduction
representation, derive the scaled cross-prior block representation by dividing
by the universal positive scale.
-/
noncomputable def crossPriorBlockRepresentation_of_unscaled
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hentropy : EntropyReductionRepresentation F) :
    CrossPriorBlockRepresentation F where
  entropy_reduction := hentropy
  cross_prior_block_rep := by
    intro A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P Q
    have hraw :=
      hcross.unscaled_cross_prior_block_rep F hax hentropy.scale_coherence
        q r hq hr P Q
    rw [hraw]
    have hscale :
        hentropy.scale_coherence.scale q = hentropy.scale_coherence.scale r :=
      hentropy.scale_coherence.scale_universal q r hq hr
    have hpos : 0 < hentropy.scale_coherence.scale q :=
      hentropy.scale_coherence.scale_pos q hq
    rw [← hscale]
    exact (div_le_div_iff_of_pos_right hpos).symm

/--
**Cross-Prior Block Representation from Assumption**

Compatibility name for the scaled representation derived from the unscaled
paper blockbridge.
-/
noncomputable def crossPriorBlock_of_assumption
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hentropy : EntropyReductionRepresentation F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_unscaled hcross F hax hentropy

/-- Named Stage 12B scaled reassembly of paper Lemma `blockbridge`.

The unscaled full-support bridge is `blockbridge_fullSupport_of_decomposed_components`;
this wrapper applies the universal positive scale carried by
`EntropyReductionRepresentation`. -/
noncomputable def crossPriorBlockRepresentation_of_decomposed_components
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hentropy : EntropyReductionRepresentation F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_unscaled hcross F hax hentropy

/--
**Entropy Reduction from All External Assumptions**

Given the first external assumptions through scale coherence, derive an entropy
reduction representation.

This composes the first five sufficiency bridges:
1. PureTraceConditions → PosteriorLawSufficiency (via Blackwell)
2. PosteriorLawSufficiency → PosteriorValueRepresentation (via Herstein-Milnor)
3. PosteriorValueRepresentation → BranchAggregationStructure (via Branch Aggregation)
4. BranchAggregationStructure → ScaleCoherenceStructure (via Scale Coherence)
5. ScaleCoherenceStructure → EntropyReductionRepresentation
   (via internal normalized chain rule)

Paper: Lemmas blockcoh--blackwell + postsep + branchagg + chain + scalecoherence +
faddeevsketch.
-/
noncomputable def entropyReduction_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hax : PureTraceConditions F) :
    EntropyReductionRepresentation F :=
  let hscaleStruct := scaleCoherence_of_axioms F hblackwell hhm hbranch hscale hax
  EntropyReductionRepresentation_of_scale F hscaleStruct

/--
**Cross-Prior Block Representation from All External Assumptions**

Given the external assumptions through entropy reduction plus the separate
unscaled cross-prior block assumption, derive a scaled cross-prior block
representation.
-/
noncomputable def crossPriorBlock_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (hax : PureTraceConditions F) :
    CrossPriorBlockRepresentation F :=
  let hentropyStruct :=
    entropyReduction_of_axioms F hblackwell hhm hbranch hscale hax
  crossPriorBlockRepresentation_of_unscaled hcross F hax hentropyStruct

end TraceableAgency
