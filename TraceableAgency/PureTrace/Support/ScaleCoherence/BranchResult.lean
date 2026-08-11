/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence.BranchAPI

namespace TraceableAgency

universe u

/-!
## Faithful named result

The following package is the faithful Lean statement of the paper's named
result "Branch aggregation, cocycle, and normalised chain rule".  It exposes
the branch aggregation structure, the public full-support cocycle, the
full-support scale factorization, the boundary/singleton-extended scale
factorization, and the induced normalised chain rule.  It deliberately does not
use the old hax-free `FiniteBranchAggregationAssumptions` compatibility
monolith.
-/

/-- Faithful output package for branch aggregation, public cocycle,
scale factorization, and the normalised chain rule. -/
structure BranchAggregationCocycleNormalizedChainRuleStructure
    (F : PrefFamily.{u}) where
  branch_agg : BranchAggregationStructure F
  coeff_cocycle : FiniteBranchCoeffCocycleAssumptionsFor branch_agg
  full_support_scale :
    FiniteBranchScaleFactorizationFullSupportAssumptions branch_agg
  scale_factorization :
    FiniteBranchScaleFactorizationAssumptions branch_agg

namespace BranchAggregationCocycleNormalizedChainRuleStructure

/-- The branch-chain structure induced by the faithful named-result package. -/
noncomputable def chain
    {F : PrefFamily.{u}}
    (h : BranchAggregationCocycleNormalizedChainRuleStructure F) :
    BranchChainStructure F :=
  branchChainStructure_of_scaleFactorization h.branch_agg h.scale_factorization

/-- The normalised chain rule induced by the faithful named-result package. -/
theorem normalizedChainRule
    {F : PrefFamily.{u}}
    (h : BranchAggregationCocycleNormalizedChainRuleStructure F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : O → Channel A Y) :
    branchNormalizedValue h.chain q (P ▷ Q)
    =
    branchNormalizedValue h.chain q P
      + ∑ o : O,
          (Channel.outcomeMarginal P q) o *
          branchNormalizedValue h.chain
            (Channel.posterior P q o) (Q o) :=
  branchNormalizedValue_seqCompose_of_chain h.chain q hq P Q

end BranchAggregationCocycleNormalizedChainRuleStructure

/-- Faithful theorem statement for the named result "Branch aggregation,
cocycle, and normalised chain rule".

All residual inputs are explicit in `FiniteFaithfulBranchAggregationAssumptions`:
finite tangent geometry, same-sign scalar linear algebra, support-face
representative normalization, boundary coefficient/scale transport, and
singleton normalizations. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_faithful
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hpath :=
    branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV
  let hboundary :=
    branchBoundaryFaceScale_of_faithfulAssumptions hfaith
  let hvalue :=
    branchBoundaryValueTransport_of_faithfulAssumptions hfaith
  let hcoeff :=
    branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransport
      F hax hV hfaith.linear_part hpath hboundary hfaith.singleton_scale
      hvalue hcoeff
  let hbranch :=
    branchAggregationStructure_of_tangentFormulaFor
      F hax hV hfaith.linear_part hpath hboundary hfaith.singleton_scale
      hformula
  let hcocycle :=
    branchCoeffCocycleFor_of_tangentScalar
      F hax hV hfaith.linear_part hpath hboundary hfaith.singleton_scale
      hformula
  let hfull :=
    branchScaleFactorizationFullSupport_of_cocycle hbranch hcocycle
  {
    branch_agg := hbranch
    coeff_cocycle := hcocycle
    full_support_scale := hfull
    scale_factorization :=
      branchScaleFactorization_of_fullSupport_boundary_singleton
        hbranch hfull
        (hfaith.boundary_scale_factorization F hax hV)
        (hfaith.singleton_scale_factorization F hax hV)
  }

/-- Selected faithful theorem statement for branch aggregation, cocycle, and
normalised chain rule.

This is the same construction as `BranchAggregationCocycleNormalizedChainRule_of_faithful`,
but it consumes boundary value transport only for the representative `hV` being
assembled. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_componentsFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary)
    (hboundaryScale :
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff))
    (hsingleScale :
      FiniteBranchScaleFactorizationSingletonNormalization
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransportFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  let hbranch :=
    branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula
  let hcocycle :=
    branchCoeffCocycleFor_of_tangentScalar
      F hax hV hlin hpath hboundary hsingle hformula
  let hfull :=
    branchScaleFactorizationFullSupport_of_cocycle hbranch hcocycle
  {
    branch_agg := hbranch
    coeff_cocycle := hcocycle
    full_support_scale := hfull
    scale_factorization :=
      branchScaleFactorization_of_fullSupport_boundary_singleton
        hbranch hfull hboundaryScale hsingleScale
  }

end TraceableAgency
