/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PairOrder

/-!
# Two-alternative surface of the pure-trace scale

`PureTrace` exposes the pure-trace conclusion (Appendix A of the current
paper) for arbitrary finite block
families.  The theorem below specializes it to the material model's primitive
two-alternative `pairWeak` notation without assuming a block convention.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

inductive TracePairIndex : Type u
  | left
  | right
  deriving DecidableEq, Fintype, Nonempty

open TracePairIndex

/-- At the v4 trace anchor, the pure-trace proposition ranks every
cross-channel, cross-prior comparison by the same mutual-information scale. -/
theorem constantPayoff_pairWeak_iff_mutualInfo
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (P : Channel A R)
    (p : TraceableAgency.Dist B) (Q : Channel B S) :
    pairWeak F q (constantPayoffLift h.traceAnchor P)
        p (constantPayoffLift h.traceAnchor Q) ↔
      mutualInfo q P ≥ mutualInfo p Q := by
  classical
  let Act : TracePairIndex → Type u
    | left => A
    | right => B
  let Rec : TracePairIndex → Type u
    | left => R
    | right => S
  let actFintype : ∀ k, Fintype (Act k)
    | left => inferInstance
    | right => inferInstance
  let actDecEq : ∀ k, DecidableEq (Act k)
    | left => inferInstance
    | right => inferInstance
  let actNonempty : ∀ k, Nonempty (Act k)
    | left => inferInstance
    | right => inferInstance
  let recFintype : ∀ k, Fintype (Rec k)
    | left => inferInstance
    | right => inferInstance
  let recDecEq : ∀ k, DecidableEq (Rec k)
    | left => inferInstance
    | right => inferInstance
  let recNonempty : ∀ k, Nonempty (Rec k)
    | left => inferInstance
    | right => inferInstance
  letI : ∀ k, Fintype (Act k) := actFintype
  letI : ∀ k, DecidableEq (Act k) := actDecEq
  letI : ∀ k, Nonempty (Act k) := actNonempty
  letI : ∀ k, Fintype (Rec k) := recFintype
  letI : ∀ k, DecidableEq (Rec k) := recDecEq
  letI : ∀ k, Nonempty (Rec k) := recNonempty
  let C : ∀ k, Channel (Act k) (Rec k)
    | left => P
    | right => Q
  have hlr : (left : TracePairIndex.{u}) ≠ right := by decide
  have hblock := constantPayoff_blockRepresentation
    F h Act Rec C left right hlr q p
  have hcoherence := h.a3.irrelevant_blocks Act Rec
    (fun k ↦ constantPayoffLift h.traceAnchor (C k))
    left right hlr q p
  exact hcoherence.symm.trans hblock

end TraceableAgency.Theorem1
