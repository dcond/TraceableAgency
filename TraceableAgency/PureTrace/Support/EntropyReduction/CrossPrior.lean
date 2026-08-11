/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.GaugeCoherence

namespace TraceableAgency

universe u

/-!
## Cross-prior blockbridge reassembly

Paper Lemma `blockbridge` is full-support at the formal
`CrossPriorBlockRepresentation` level; arbitrary-prior boundary uses are routed
through the separate support-restriction/boundary-extension layer.
-/

/-- Named full-support unscaled reassembly of paper Lemma `blockbridge`.

It combines coherent product quasi-additivity, zero normalization,
same-prior value representation, and the A3/A4/A5 product-to-block transfer. -/
theorem blockbridge_fullSupport_of_decomposed_components
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) :=
  hcross.unscaled_cross_prior_block_rep F hax hs q r hq hr P Q

end TraceableAgency
