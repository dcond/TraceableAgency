/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.HMInterface
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.EntropyRegularity
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.RecursionInputs
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.BoundaryTransport
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.EmbeddingDefect
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.DefectCocycle
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.Alignment
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.SingletonInteraction
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.ProductGauge
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.BoundaryCompletion
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.Grouping
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.FinalReduction

/-!
# Closed pure-trace entropy reduction

The closed Herstein--Milnor, branch, face, product, grouping, and Shannon-reduction route used by the pure-trace theorem.
-/
