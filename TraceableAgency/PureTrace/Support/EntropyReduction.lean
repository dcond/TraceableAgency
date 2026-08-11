/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.NormalizedValue
import TraceableAgency.PureTrace.Support.EntropyReduction.Compatibility
import TraceableAgency.PureTrace.Support.EntropyReduction.ProductLifts
import TraceableAgency.PureTrace.Support.EntropyReduction.ProductKernels
import TraceableAgency.PureTrace.Support.EntropyReduction.ProductReplacement
import TraceableAgency.PureTrace.Support.EntropyReduction.BackgroundInertness
import TraceableAgency.PureTrace.Support.EntropyReduction.PosteriorCompatibility
import TraceableAgency.PureTrace.Support.EntropyReduction.SingletonCollapse
import TraceableAgency.PureTrace.Support.EntropyReduction.SliceAffine
import TraceableAgency.PureTrace.Support.EntropyReduction.GaugeCoherence
import TraceableAgency.PureTrace.Support.EntropyReduction.CrossPrior
import TraceableAgency.PureTrace.Support.EntropyReduction.SliceIdentification

/-!
# Pure-trace entropy reduction

Normalized-value, product, gauge, and cross-prior constructions used by the pure-trace reduction.
-/
