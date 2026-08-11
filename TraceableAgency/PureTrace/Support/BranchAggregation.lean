/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.SignedLaws
import TraceableAgency.PureTrace.Support.BranchAggregation.AffineLinear
import TraceableAgency.PureTrace.Support.BranchAggregation.OneBranch
import TraceableAgency.PureTrace.Support.BranchAggregation.SignPreservation
import TraceableAgency.PureTrace.Support.BranchAggregation.PositiveAffine
import TraceableAgency.PureTrace.Support.BranchAggregation.BackgroundIndependence
import TraceableAgency.PureTrace.Support.BranchAggregation.TangentInterfaces
import TraceableAgency.PureTrace.Support.BranchAggregation.AtomicSpanning
import TraceableAgency.PureTrace.Support.BranchAggregation.Reachability
import TraceableAgency.PureTrace.Support.BranchAggregation.PathScalars
import TraceableAgency.PureTrace.Support.BranchAggregation.BoundaryFaces
import TraceableAgency.PureTrace.Support.BranchAggregation.CoefficientAssembly

/-!
# Pure-trace branch aggregation

Finite signed-law, affine, branch, face, and coefficient constructions used by the pure-trace reduction.
-/
