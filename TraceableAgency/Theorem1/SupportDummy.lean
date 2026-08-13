/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.PureTrace
import TraceableAgency.Basic.SupportRestriction

/-!
# Support restriction and independent dummy actions

This module derives two structural invariances from the stated behavioral
axioms.  Both are proved through exact A5 joint-law completions and the same
common-payoff four-block replacement argument used in the pure-trace bridge.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-! ## A four-object comparison replacement lemma -/

inductive CrossReplacementBlock : Type u
  | oldLeft
  | newLeft
  | oldRight
  | newRight
  deriving DecidableEq, Fintype

open CrossReplacementBlock

def crossReplacementAct
    (A A' B B' : Type u) : CrossReplacementBlock → Type u
  | oldLeft => A
  | newLeft => A'
  | oldRight => B
  | newRight => B'

noncomputable instance crossReplacementActFintype
    {A A' B B' : Type u}
    [Fintype A] [Fintype A'] [Fintype B] [Fintype B'] :
  ∀ k, Fintype (crossReplacementAct A A' B B' k)
  | oldLeft => show Fintype A from inferInstance
  | newLeft => show Fintype A' from inferInstance
  | oldRight => show Fintype B from inferInstance
  | newRight => show Fintype B' from inferInstance

instance crossReplacementActDecidableEq
    {A A' B B' : Type u}
    [DecidableEq A] [DecidableEq A'] [DecidableEq B] [DecidableEq B'] :
  ∀ k, DecidableEq (crossReplacementAct A A' B B' k)
  | oldLeft => show DecidableEq A from inferInstance
  | newLeft => show DecidableEq A' from inferInstance
  | oldRight => show DecidableEq B from inferInstance
  | newRight => show DecidableEq B' from inferInstance

def crossReplacementRec
    (R R' S S' : Type u) : CrossReplacementBlock → Type u
  | oldLeft => R
  | newLeft => R'
  | oldRight => S
  | newRight => S'

noncomputable instance crossReplacementRecFintype
    {R R' S S' : Type u}
    [Fintype R] [Fintype R'] [Fintype S] [Fintype S'] :
  ∀ k, Fintype (crossReplacementRec R R' S S' k)
  | oldLeft => show Fintype R from inferInstance
  | newLeft => show Fintype R' from inferInstance
  | oldRight => show Fintype S from inferInstance
  | newRight => show Fintype S' from inferInstance

instance crossReplacementRecDecidableEq
    {R R' S S' : Type u}
    [DecidableEq R] [DecidableEq R'] [DecidableEq S] [DecidableEq S'] :
  ∀ k, DecidableEq (crossReplacementRec R R' S S' k)
  | oldLeft => show DecidableEq R from inferInstance
  | newLeft => show DecidableEq R' from inferInstance
  | oldRight => show DecidableEq S from inferInstance
  | newRight => show DecidableEq S' from inferInstance

noncomputable def crossReplacementChannel
    {O A A' B B' R R' S S' : Type u}
    [Fintype O] [Fintype R] [Fintype R'] [Fintype S] [Fintype S']
    (K : Channel A (O × R)) (K' : Channel A' (O × R'))
    (L : Channel B (O × S)) (L' : Channel B' (O × S')) :
    ∀ k : CrossReplacementBlock,
      Channel (crossReplacementAct A A' B B' k)
        (O × crossReplacementRec R R' S S' k)
  | oldLeft => show Channel A (O × R) from K
  | newLeft => show Channel A' (O × R') from K'
  | oldRight => show Channel B (O × S) from L
  | newRight => show Channel B' (O × S') from L'

/-- Replacing the left and right alternatives by weakly equivalent objects
preserves their cross-channel comparison. -/
theorem pairWeak_iff_of_pairwiseWeakEquiv
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    {A A' B B' R R' S S' : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype A'] [DecidableEq A'] [Nonempty A']
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype B'] [DecidableEq B'] [Nonempty B']
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype R'] [DecidableEq R'] [Nonempty R']
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype S'] [DecidableEq S'] [Nonempty S']
    (K : Channel A (O × R)) (K' : Channel A' (O × R'))
    (L : Channel B (O × S)) (L' : Channel B' (O × S'))
    (q : TraceableAgency.Dist A) (q' : TraceableAgency.Dist A')
    (p : TraceableAgency.Dist B) (p' : TraceableAgency.Dist B')
    (hq_forward : pairWeak F q K q' K')
    (hq_back : pairWeak F q' K' q K)
    (hp_forward : pairWeak F p L p' L')
    (hp_back : pairWeak F p' L' p L) :
    pairWeak F q K p L ↔ pairWeak F q' K' p' L' := by
  classical
  let k0 : CrossReplacementBlock.{u} := oldLeft
  let k1 : CrossReplacementBlock.{u} := newLeft
  let k2 : CrossReplacementBlock.{u} := oldRight
  let k3 : CrossReplacementBlock.{u} := newRight
  let Act := crossReplacementAct A A' B B'
  let Rec := crossReplacementRec R R' S S'
  let C := crossReplacementChannel K K' L L'
  letI : Nonempty CrossReplacementBlock := ⟨oldLeft⟩
  letI : ∀ k, Nonempty (Act k) := fun k => by
    cases k <;> simp [Act, crossReplacementAct] <;> infer_instance
  letI : ∀ k, Nonempty (Rec k) := fun k => by
    cases k <;> simp [Rec, crossReplacementRec] <;> infer_instance
  let commonK := commonPayoffBlockFamilyChannel Act Rec C
  let x := commonPayoffBlockEmbed Act k0 q
  let x' := commonPayoffBlockEmbed Act k1 q'
  let y := commonPayoffBlockEmbed Act k2 p
  let y' := commonPayoffBlockEmbed Act k3 p'
  have htrans :
      ∀ a b c : TraceableAgency.Dist ((k : CrossReplacementBlock) × Act k),
        F.rel commonK a b → F.rel commonK b c → F.rel commonK a c :=
    (h1 commonK).2
  have h02 : k0 ≠ k2 := by decide
  have h01 : k0 ≠ k1 := by decide
  have h10 : k1 ≠ k0 := by decide
  have h23 : k2 ≠ k3 := by decide
  have h32 : k3 ≠ k2 := by decide
  have h13 : k1 ≠ k3 := by decide
  have hcommon02 : F.rel commonK x y ↔ pairWeak F q K p L := by
    have hh := h3.irrelevant_blocks Act Rec C k0 k2 h02 q p
    change F.rel commonK x y ↔ pairWeak F q (C k0) p (C k2) at hh
    have hc0 : C k0 = K := by rfl
    have hc2 : C k2 = L := by rfl
    rw [hc0, hc2] at hh
    exact hh
  have hcommon01 : F.rel commonK x x' := by
    have hh := (h3.irrelevant_blocks Act Rec C k0 k1 h01 q q').mpr hq_forward
    change F.rel commonK x x' at hh
    exact hh
  have hcommon10 : F.rel commonK x' x := by
    have hh := (h3.irrelevant_blocks Act Rec C k1 k0 h10 q' q).mpr hq_back
    change F.rel commonK x' x at hh
    exact hh
  have hcommon23 : F.rel commonK y y' := by
    have hh := (h3.irrelevant_blocks Act Rec C k2 k3 h23 p p').mpr hp_forward
    change F.rel commonK y y' at hh
    exact hh
  have hcommon32 : F.rel commonK y' y := by
    have hh := (h3.irrelevant_blocks Act Rec C k3 k2 h32 p' p).mpr hp_back
    change F.rel commonK y' y at hh
    exact hh
  have hreplace : F.rel commonK x y ↔ F.rel commonK x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonK a b) htrans
      hcommon01 hcommon10 hcommon23 hcommon32
  have hcommon13 : F.rel commonK x' y' ↔ pairWeak F q' K' p' L' := by
    have hh := h3.irrelevant_blocks Act Rec C k1 k3 h13 q' p'
    change F.rel commonK x' y' ↔ pairWeak F q' (C k1) p' (C k3) at hh
    have hc1 : C k1 = K' := by rfl
    have hc3 : C k3 = L' := by rfl
    rw [hc1, hc3] at hh
    exact hh
  exact hcommon02.symm.trans (hreplace.trans hcommon13)

/-! ## Support restriction -/

theorem pairWeak_ambient_to_support
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A) :
    pairWeak F q K q.restrictToSupport (Channel.restrictToSupport K q) := by
  have hh := h.a5 K q (supportProjectKernel q)
    (Channel.restrictToSupport K q)
    (actionCompletion_isExact K q (supportProjectKernel q)
      (Channel.restrictToSupport K q)
      (restrictToSupport_isBayesPushforwardCompletion K q))
  simpa [actionPushforward_project] using hh

theorem pairWeak_support_to_ambient
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (K : Channel A (O × R)) (q : TraceableAgency.Dist A) :
    pairWeak F q.restrictToSupport (Channel.restrictToSupport K q) q K := by
  have hh := h.a5 (Channel.restrictToSupport K q) q.restrictToSupport
    (supportIncludeKernel q) K
    (actionCompletion_isExact (Channel.restrictToSupport K q) q.restrictToSupport
      (supportIncludeKernel q) K
      (ambient_isBayesPushforwardCompletion_of_restrict K q))
  simpa [actionPushforward_restrict_include] using hh

/-- Cross-channel comparisons are unchanged after deleting every zero-prior
action row on both sides. -/
theorem pairWeak_iff_supportRestriction
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      pairWeak F q.restrictToSupport (Channel.restrictToSupport K q)
        p.restrictToSupport (Channel.restrictToSupport L p) :=
  pairWeak_iff_of_pairwiseWeakEquiv F h.a1 h.a3
    K (Channel.restrictToSupport K q)
    L (Channel.restrictToSupport L p)
    q q.restrictToSupport p p.restrictToSupport
    (pairWeak_ambient_to_support F h K q)
    (pairWeak_support_to_ambient F h K q)
    (pairWeak_ambient_to_support F h L p)
    (pairWeak_support_to_ambient F h L p)

/-- Within one joint channel, arbitrary boundary priors reduce to their two
possibly different full-support faces. -/
theorem rel_iff_supportRestriction
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (K : Channel A (O × R))
    (q p : TraceableAgency.Dist A) :
    F.rel K q p ↔
      pairWeak F q.restrictToSupport (Channel.restrictToSupport K q)
        p.restrictToSupport (Channel.restrictToSupport K p) :=
  (h.a3.duplication K q p).trans
    (pairWeak_iff_supportRestriction F h q K p K)

/-! ## Independent dummy actions -/

/-- Add an independent action coordinate to a prior. -/
noncomputable def independentDummyPrior
    {A B : Type u} [Fintype A] [Fintype B]
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    TraceableAgency.Dist (A × B) :=
  prodDist q r

/-- Add a dummy action coordinate which the joint payoff-record channel ignores. -/
noncomputable def independentDummyChannel
    {O A B R : Type u} [Fintype O] [Fintype R]
    (K : Channel A (O × R)) : Channel (A × B) (O × R) :=
  fun ab => K ab.1

/-- Forget the independent dummy coordinate. -/
noncomputable def dummyProjectionKernel
    {A B : Type u} [Fintype A] [DecidableEq A] :
    Channel.ActionKernel (A × B) A :=
  fun ab => TraceableAgency.Dist.pure ab.1

/-- Independently redraw the dummy coordinate with law `r`. -/
noncomputable def dummyRedrawKernel
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Fintype B]
    (r : TraceableAgency.Dist B) : Channel.ActionKernel A (A × B) :=
  fun a => prodDist (TraceableAgency.Dist.pure a) r

theorem actionPushforward_dummyProjection
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Fintype B]
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    Channel.actionPushforward (independentDummyPrior q r)
        (dummyProjectionKernel (A := A) (B := B)) = q := by
  ext a
  change (∑ ab : A × B,
      prodDist q r ab * TraceableAgency.Dist.pure ab.1 a) = q a
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single a]
  · simp [prodDist_apply_pair, ← Finset.mul_sum, r.sum_eq_one]
  · intro a' ha'
    apply Finset.sum_eq_zero
    intro b _
    have hne : a ≠ a' := fun h => ha' h.symm
    simp [prodDist_apply_pair,
      TraceableAgency.Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_dummyRedraw
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Fintype B]
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    Channel.actionPushforward q (dummyRedrawKernel r) =
      independentDummyPrior q r := by
  ext ab
  rcases ab with ⟨a, b⟩
  change (∑ a' : A,
      q a' * prodDist (TraceableAgency.Dist.pure a') r (a, b)) =
    prodDist q r (a, b)
  rw [Fintype.sum_eq_single a]
  · simp [prodDist_apply_pair]
  · intro a' ha'
    have hne : a ≠ a' := fun h => ha' h.symm
    simp [prodDist_apply_pair,
      TraceableAgency.Dist.pure_apply_ne _ _ hne]

/-- Forgetting the dummy coordinate has `K` as its exact A5 completion. -/
theorem dummyProjection_isActionProcessorCompletion
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    IsActionProcessorCompletion (independentDummyChannel (B := B) K)
      (independentDummyPrior q r)
      (dummyProjectionKernel (A := A) (B := B)) K := by
  intro a z
  rw [show Channel.actionPushforward (independentDummyPrior q r)
      (dummyProjectionKernel (A := A) (B := B)) a = q a by
    rw [actionPushforward_dummyProjection]]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single a]
  · simp only [independentDummyPrior, independentDummyChannel,
      dummyProjectionKernel, prodDist_apply_pair,
      TraceableAgency.Dist.pure_apply_self, mul_one]
    calc
      q a * K a z = (q a * K a z) * ∑ b : B, r b := by
        rw [r.sum_eq_one, mul_one]
      _ = ∑ b : B, q a * r b * K a z := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
  · intro a' ha'
    apply Finset.sum_eq_zero
    intro b _
    have hne : a ≠ a' := fun h => ha' h.symm
    simp [independentDummyPrior, independentDummyChannel,
      dummyProjectionKernel, prodDist_apply_pair,
      TraceableAgency.Dist.pure_apply_ne _ _ hne]

/-- Independently redrawing the dummy coordinate has the dummy lift as its
exact A5 completion. -/
theorem dummyRedraw_isActionProcessorCompletion
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    IsActionProcessorCompletion K q (dummyRedrawKernel r)
      (independentDummyChannel (B := B) K) := by
  intro ab z
  rcases ab with ⟨a, b⟩
  rw [show Channel.actionPushforward q (dummyRedrawKernel r) (a, b) =
      independentDummyPrior q r (a, b) by
    rw [actionPushforward_dummyRedraw]]
  rw [Fintype.sum_eq_single a]
  · simp [independentDummyPrior, independentDummyChannel,
      dummyRedrawKernel, prodDist_apply_pair]
  · intro a' ha'
    have hne : a ≠ a' := fun h => ha' h.symm
    simp [dummyRedrawKernel, prodDist_apply_pair,
      TraceableAgency.Dist.pure_apply_ne _ _ hne]

/-- A pair is weakly equivalent to its independent-dummy lift, in both
directions. -/
theorem independentDummy_pairWeak_neutrality
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    pairWeak F q K (independentDummyPrior q r)
        (independentDummyChannel (B := B) K) ∧
      pairWeak F (independentDummyPrior q r)
        (independentDummyChannel (B := B) K) q K := by
  constructor
  · have hh := h.a5 K q (dummyRedrawKernel r)
      (independentDummyChannel (B := B) K)
      (dummyRedraw_isActionProcessorCompletion K q r)
    simpa [actionPushforward_dummyRedraw] using hh
  · have hh := h.a5 (independentDummyChannel (B := B) K)
      (independentDummyPrior q r)
      (dummyProjectionKernel (A := A) (B := B)) K
      (dummyProjection_isActionProcessorCompletion K q r)
    simpa [actionPushforward_dummyProjection] using hh

/-- Replacing both compared objects by arbitrary independent dummy lifts does
not change their comparison. -/
theorem pairWeak_iff_independentDummy
    {O A B C D R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype D] [DecidableEq D] [Nonempty D]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (r : TraceableAgency.Dist B)
    (p : TraceableAgency.Dist C) (L : Channel C (O × S))
    (s : TraceableAgency.Dist D) :
    pairWeak F q K p L ↔
      pairWeak F (independentDummyPrior q r)
          (independentDummyChannel (B := B) K)
        (independentDummyPrior p s)
          (independentDummyChannel (B := D) L) := by
  have hq := independentDummy_pairWeak_neutrality F h K q r
  have hp := independentDummy_pairWeak_neutrality F h L p s
  exact pairWeak_iff_of_pairwiseWeakEquiv F h.a1 h.a3
    K (independentDummyChannel (B := B) K)
    L (independentDummyChannel (B := D) L)
    q (independentDummyPrior q r) p (independentDummyPrior p s)
    hq.1 hq.2 hp.1 hp.2

/-- Within one environment, adjoining the same independently distributed
dummy coordinate to both priors preserves the primitive comparison. -/
theorem rel_iff_independentDummy
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (K : Channel A (O × R))
    (q p : TraceableAgency.Dist A) (r : TraceableAgency.Dist B) :
    F.rel K q p ↔
      F.rel (independentDummyChannel (B := B) K)
        (independentDummyPrior q r) (independentDummyPrior p r) := by
  exact (h.a3.duplication K q p).trans
    ((pairWeak_iff_independentDummy F h q K r p K r).trans
      (h.a3.duplication (independentDummyChannel (B := B) K)
        (independentDummyPrior q r) (independentDummyPrior p r)).symm)

end TraceableAgency.Theorem1
