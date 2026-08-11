/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.CoefficientAssembly

namespace TraceableAgency

universe u v

/-!
## Branch Aggregation External Assumption

The branch aggregation theorem states that given:
1. Axiom A6 (branchwise continuation monotonicity)
2. A posterior value representation V from Herstein-Milnor

There exist positive branch coefficients β(q, r) such that the value of a
sequential experiment decomposes into first-stage value plus expected scaled
continuation values.

Paper proof sketch:
1. Fix first-stage channel P₁ with branch structure (m(o), r_o)
2. For a positive-probability branch o̅, define g(ν) = F_q(T_H(ν)) where T_H
   embeds branch law ν into the full posterior law
3. A6 implies g and F_r represent the same weak order on M_r
4. Herstein-Milnor uniqueness gives g = αF_r + γ with α > 0
5. Path-independence argument shows α/m depends only on (q, r), not on P₁
6. Define β(q, r) := α/m to get the aggregation formula
-/

/--
**Finite Branch Aggregation Assumptions**

External assumption that Axiom A6 (branchwise continuation monotonicity)
combined with a posterior value representation yields a branch aggregation
structure with positive coefficients.

Paper: Lemma branchagg.

**Key mathematical content:**
- From A6 + posterior value representation, derive positive β(q, r)
- β(q, r) depends only on prior q and reached posterior r, not on the
  specific first-stage channel
- The value decomposes as: V_q(P₁▷{Q}) = V_q(P₁) + Σ m(o) β(q,r_o) V_{r_o}(Q^o)

We state this as an external assumption because the proof involves:
- Tangent-space arguments on the space of posterior laws
- Path-independence via affine-hull decomposition
- Case analysis for boundary/degenerate posteriors
-/
structure FiniteBranchAggregationAssumptions where
  /-- Given A6 and a posterior value representation, construct a branch
      aggregation structure. This is the main theorem of Lemma branchagg.

      Note: This returns a data-carrying structure (BranchAggregationStructure),
      so FiniteBranchAggregationAssumptions is Type, not Prop. -/
  of_A6 :
    ∀ (F : PrefFamily.{v}),
      PureTraceBranchContinuationMonotonicity F →
      PosteriorValueRepresentation F →
      BranchAggregationStructure F

/-!
## Bridge Theorems

These theorems show how to use the branch aggregation assumption in the
sufficiency spine.
-/

/--
**Branch Aggregation from A6 Assumption**

Given the external branch aggregation assumption, A6, and a posterior value
representation, derive a branch aggregation structure.
-/
noncomputable def branchAggregation_of_assumption
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u})
    (hA6 : PureTraceBranchContinuationMonotonicity F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationStructure F :=
  hbranch.of_A6 F hA6 hV

/--
**Branch Aggregation from PureTraceConditions**

Given the external branch aggregation assumption and full PureTraceConditions,
derive a branch aggregation structure.
-/
noncomputable def branchAggregation_of_traceAxioms
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationStructure F :=
  hbranch.of_A6 F hax.branchContinuation hV

/--
**Legacy packaged branch-aggregation constructor**

Given the older packaged Blackwell, Herstein--Milnor, and branch-aggregation
interfaces plus `PureTraceConditions`, derive a branch aggregation structure. This
constructor is retained for compatibility and is not the final theorem route.

This composes the first three sufficiency bridges:
1. PureTraceConditions → PosteriorLawSufficiency (via Blackwell)
2. PosteriorLawSufficiency → PosteriorValueRepresentation (via Herstein-Milnor)
3. PosteriorValueRepresentation → BranchAggregationStructure (via Branch Aggregation)

Paper: Lemmas blockcoh--blackwell + postsep + branchagg.
-/
noncomputable def branchAggregation_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hax : PureTraceConditions F) :
    BranchAggregationStructure F :=
  let hpls : PosteriorLawSufficiency F := from_axioms_to_posterior_of_blackwell F hblackwell hax
  let hV : PosteriorValueRepresentation F :=
    posteriorValueRep_of_HersteinMilnor F hhm hax hpls
  hbranch.of_A6 F hax.branchContinuation hV

/-!
## Spine Integration Helper

Shows how to fill the `value_rep_to_branch` field of `SufficiencySpineAssumptions`.
-/

/--
**Value Rep to Branch Bridge**

Given A6 and the branch aggregation external assumption, provides the bridge
from PosteriorValueRepresentation to BranchAggregationStructure.

This can be used to fill the `value_rep_to_branch` field when constructing
`SufficiencySpineAssumptions`.
-/
noncomputable def value_rep_to_branch_of_assumption
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u})
    (hA6 : PureTraceBranchContinuationMonotonicity F) :
    PosteriorValueRepresentation F → BranchAggregationStructure F :=
  fun hV => hbranch.of_A6 F hA6 hV

end TraceableAgency
