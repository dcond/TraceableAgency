/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence.GroupingEvaluation
import TraceableAgency.PureTrace.Support.BranchAggregation.Compatibility

namespace TraceableAgency

universe u

/-!
## Scale Coherence External Assumption

The scale coherence theorem states that given branch aggregation coefficients β(q,r):

1. **Cocycle**: β(q,s) = β(q,r) β(r,s) for nested supports
2. **Factorization**: β(q,r) = a_q/a_r where a_q := 1/β(q₀, q) for fixed basepoint q₀
3. **Universal scale**: The two-grouping argument (using derived background
   inertness) shows a_q = a is independent of q across all full-support priors
   on all finite action sets

Paper proof sketch (Lemma scalecoherence):
1. Define H(q) := F_q(χ_q) (full revelation value) and Z(q) := 1 + κH(q)
2. Product revelation: reveal A first, then B in each branch
3. Compare with quasi-additivity to get a_{q⊗r}/a_r = Z(q)
4. Symmetry gives a_q = C·Z(q) for universal C > 0
5. Two-grouping argument via derived background inertness forces κ = 0, hence
   Z ≡ 1
6. Therefore a_q = C is universal
-/

/--
**Finite Scale Coherence Assumptions**

External assumption that branch aggregation coefficients satisfy cocycle/factorization
properties and that the scale is universal across all full-support priors.

Paper: Lemmas chain, facescales, scalecoherence.

**Key mathematical content:**
- Cocycle: β(q,s) = β(q,r) β(r,s)
- Factorization: β(q,r) = a_q/a_r
- Universal scale: a_q = a for all full-support q (via two-grouping and
  derived background inertness)

This is a data-carrying structure because it provides the scale function.
-/
structure FiniteScaleCoherenceAssumptions.{v} where
  /-- Given branch aggregation structure, construct scale coherence structure.
      This packages Lemmas chain + facescales + scalecoherence. -/
  of_branch_aggregation :
    ∀ (F : PrefFamily.{v}),
      BranchAggregationStructure F →
      ScaleCoherenceStructure F

/-!
## Bridge Theorems

These theorems show how to use the scale coherence assumption in the
sufficiency spine.
-/

/--
**Scale Coherence from Assumption**

Given the external scale coherence assumption and a branch aggregation structure,
derive a scale coherence structure.
-/
noncomputable def scaleCoherence_of_assumption
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (F : PrefFamily.{u})
    (hbranch : BranchAggregationStructure F) :
    ScaleCoherenceStructure F :=
  hscale.of_branch_aggregation F hbranch

/--
**Legacy packaged scale-coherence constructor**

Given the older packaged Blackwell, Herstein--Milnor, branch-aggregation, and
scale-coherence interfaces plus `PureTraceConditions`, derive a scale coherence
structure. This constructor is retained for compatibility and is not the
final theorem route.

This composes the first four sufficiency bridges:
1. PureTraceConditions → PosteriorLawSufficiency (via Blackwell)
2. PosteriorLawSufficiency → PosteriorValueRepresentation (via Herstein-Milnor)
3. PosteriorValueRepresentation → BranchAggregationStructure (via Branch Aggregation)
4. BranchAggregationStructure → ScaleCoherenceStructure (via Scale Coherence)

Paper: Lemmas blockcoh--blackwell + postsep + branchagg + chain + scalecoherence.
-/
noncomputable def scaleCoherence_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hax : PureTraceConditions F) :
    ScaleCoherenceStructure F :=
  let hbranchStruct := branchAggregation_of_axioms F hblackwell hhm hbranch hax
  hscale.of_branch_aggregation F hbranchStruct

/-!
## Spine Integration Helper

Shows how to fill the `branch_to_scale` field of `SufficiencySpineAssumptions`.
-/

/--
**Branch to Scale Bridge**

Given the scale coherence external assumption, provides the bridge
from BranchAggregationStructure to ScaleCoherenceStructure.

This can be used to fill the `branch_to_scale` field when constructing
`SufficiencySpineAssumptions`.
-/
noncomputable def branch_to_scale_of_assumption
    (hscale : FiniteScaleCoherenceAssumptions.{u}) :
    ∀ F : PrefFamily.{u}, BranchAggregationStructure F → ScaleCoherenceStructure F :=
  fun F hbranch => hscale.of_branch_aggregation F hbranch

end TraceableAgency
