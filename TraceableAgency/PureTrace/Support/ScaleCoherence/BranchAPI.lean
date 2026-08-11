/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence.BranchChain

namespace TraceableAgency

universe u

/-!
## Faithful Branch API

The old `FiniteBranchAggregationAssumptions` package returns a branch
aggregation structure from only A6 and a value representation.  The faithful
route developed in Stages 13--22 carries the extra classical finite-geometry
interfaces and the explicit boundary/singleton normalizations.  The following
bundle exposes that route without pretending to reconstruct the old hax-free
monolith.
-/

/-- Public faithful branch component bundle.

Later fields are dependent: boundary and singleton scale factorization are
typed for the branch structure and full-support scale constructed from the
earlier faithful components. -/
structure FiniteFaithfulBranchAggregationAssumptions.{v} where
  linear_part : FiniteAffineLinearPartAssumptions.{v}
  tangent_spanning : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{v}
  same_sign_scalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{v}
  support_face_rep : FiniteSupportFaceRepresentativeTransportAssumptions.{v}
  boundary_coeff_scale : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{v}
  singleton_scale : FiniteBranchSingletonScaleNormalizationAssumptions.{v}
  boundary_linear_transport :
    FiniteBoundaryLinearPartTransportAssumptions.{v}
      linear_part
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff_scale)
  boundary_scale_factorization :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F),
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          linear_part same_sign_scalar tangent_spanning F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff_scale
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport support_face_rep
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport
          linear_part hboundary boundary_linear_transport
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)
  singleton_scale_factorization :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F),
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          linear_part same_sign_scalar tangent_spanning F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff_scale
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport support_face_rep
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport
          linear_part hboundary boundary_linear_transport
      FiniteBranchScaleFactorizationSingletonNormalization
        (faithfulBranchAggregationStructure_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)

/-- Tangent scalar structure produced from a faithful branch bundle. -/
noncomputable def branchPathTangentScalarStructure_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchPathTangentScalarStructure F hV hfaith.linear_part :=
  branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
    hfaith.linear_part hfaith.same_sign_scalar hfaith.tangent_spanning F hax hV

/-- Boundary face-scale structure produced from a faithful branch bundle. -/
def branchBoundaryFaceScale_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u}) :
    FiniteBranchBoundaryFaceScaleAssumptions.{u} :=
  boundaryFaceScale_of_coefficientScaleNormalization hfaith.boundary_coeff_scale

/-- Boundary value transport produced from a faithful branch bundle. -/
theorem branchBoundaryValueTransport_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u}) :
    FiniteBranchBoundaryValueTransportAssumptions.{u} :=
  boundaryValueTransport_of_supportFaceRepresentativeTransport
    hfaith.support_face_rep

/-- Boundary coefficient transport produced from a faithful branch bundle. -/
theorem branchBoundaryCoefficientTransport_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u}) :
    FiniteBranchBoundaryCoefficientTransportAssumptions.{u}
      hfaith.linear_part
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith) :=
  boundaryCoefficientTransport_of_linearPartTransport
    hfaith.linear_part
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.boundary_linear_transport

/-- Public branch aggregation structure produced from faithful branch
components. -/
noncomputable def branchAggregationStructure_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationStructure F :=
  faithfulBranchAggregationStructure_of_components
    F hax hV hfaith.linear_part
    (branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV)
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.singleton_scale
    (branchBoundaryValueTransport_of_faithfulAssumptions hfaith)
    (branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith)

/-- Full-support scale factorization produced from faithful branch
components. -/
noncomputable def branchFullSupportScale_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (branchAggregationStructure_of_faithfulAssumptions hfaith F hax hV) :=
  faithfulBranchFullSupportScale_of_components
    F hax hV hfaith.linear_part
    (branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV)
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.singleton_scale
    (branchBoundaryValueTransport_of_faithfulAssumptions hfaith)
    (branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith)

/-- Public branch-chain structure produced from faithful branch components. -/
noncomputable def branchChainStructure_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    BranchChainStructure F :=
  BranchAggregationChainRule_of_faithful_components
    F hax hV hfaith.linear_part
    (branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV)
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.singleton_scale
    (branchBoundaryValueTransport_of_faithfulAssumptions hfaith)
    (branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith)
    (hfaith.boundary_scale_factorization F hax hV)
    (hfaith.singleton_scale_factorization F hax hV)

/-- Normalized chain rule exposed directly from faithful branch assumptions. -/
theorem normalizedChainRule_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : O → Channel A Y) :
    branchNormalizedValue
      (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
      q (P ▷ Q)
    =
    branchNormalizedValue
      (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
      q P
      + ∑ o : O,
          (Channel.outcomeMarginal P q) o *
          branchNormalizedValue
            (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
            (Channel.posterior P q o) (Q o) :=
  branchNormalizedValue_seqCompose_of_chain
    (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
    q hq P Q

end TraceableAgency
