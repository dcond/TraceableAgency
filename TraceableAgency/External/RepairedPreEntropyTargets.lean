/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.CardinalPermutationInvariance
import TraceableAgency.External.PreUniversalBlockBridge

/-!
# Repaired Pre-Entropy Targets

The strict countermodel pass showed that two tempting theorem statements are
too broad:

* selected cardinal relabeling is not a theorem of an arbitrary
  `CoherentRelabelingFaceScalesStructure`;
* block-reveal value is not a theorem of `hfaces + hprod` without the
  pre-universal cross-prior block bridge.

This file records the repaired dependency shape.  It does not add a new
economic premise and it does not prove closure from renamed obligations.  It only
names the earlier proof targets that match the TeX proof order.
-/

namespace TraceableAgency

universe u

/--
Product-normalized selected representatives.

This package is the corrected target for the paper's cardinal relabeling step:
the selected representative first has an actionbase scalar, and the product
normalization argument pins that scalar to one.  It is intentionally not stated
as a theorem for every arbitrary `hfaces`.
-/
structure FiniteProductNormalizedSelectedRepresentativesFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  actionbase_scalar :
    FiniteSelectedActionbaseScalarFor hfaces
  product_normalization_pinning :
    FiniteSelectedPermutationInvariancePinningFor hfaces

/--
The corrected selected-relabeling assembly from the two TeX cardinal steps.
-/
theorem finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hnorm : FiniteProductNormalizedSelectedRepresentativesFor hfaces) :
    FiniteSelectedPosteriorValueRelabelingFor hfaces :=
  finiteSelectedPosteriorValueRelabeling_of_actionbase_permutationinvariance
    hnorm.actionbase_scalar hnorm.product_normalization_pinning

/--
Pre-universal cross-prior block bridge for the selected face-scale
representative.

This is the dependency missing from the over-weak target
`hfaces + hprod => blockReveal = H(p)`.  It is the selected, unscaled analogue
of the paper's blockbridge before entropy reduction/Faddeev: cross-prior block
comparisons are represented by the selected cardinal values themselves.
-/
structure FinitePreUniversalCrossPriorBlockBridgeFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  unscaled_cross_prior_block_rep :
    ∀ (_hax : TraceAxioms F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B)
      (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (Q : Channel B Y),
      F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) ≥
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel Q)

/-
The next Lean theorem should prove `FinitePreUniversalBlockRevealValueFor`
from `FinitePreUniversalCrossPriorBlockBridgeFor` plus the already formalized
coarse-reveal/undetectable-distinctions neutrality and sigma-support algebra.
This file deliberately does not bundle `FinitePreUniversalBlockRevealValueFor`
as a field, because that would merely rename the previous over-strong target.
-/

end TraceableAgency
