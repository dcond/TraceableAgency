/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.Bridges

namespace TraceableAgency

universe u

/-!
## Spine Integration Helper

Shows how to fill the `scale_to_entropy_reduction` field of `SufficiencySpineAssumptions`.
-/

/--
**Scale to Entropy Reduction Bridge**

Provides the bridge from ScaleCoherenceStructure to EntropyReductionRepresentation.

This can be used to fill the `scale_to_entropy_reduction` field when constructing
`SufficiencySpineAssumptions`.
-/
noncomputable def scale_to_entropy_reduction_of_scale :
    ∀ F : PrefFamily.{u}, ScaleCoherenceStructure F → EntropyReductionRepresentation F :=
  fun F hscale => EntropyReductionRepresentation_of_scale F hscale

/--
**Entropy Reduction to Cross-Prior Bridge**

Given the cross-prior block external assumption, provides the bridge from
`EntropyReductionRepresentation` to `CrossPriorBlockRepresentation` by way of
the unscaled paper blockbridge and universal scale.
-/
noncomputable def entropy_reduction_to_cross_prior_of_assumption
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    ∀ F : PrefFamily.{u}, PureTraceConditions F →
      EntropyReductionRepresentation F → CrossPriorBlockRepresentation F :=
  fun F hax hentropy => crossPriorBlockRepresentation_of_unscaled hcross F hax hentropy

end TraceableAgency
