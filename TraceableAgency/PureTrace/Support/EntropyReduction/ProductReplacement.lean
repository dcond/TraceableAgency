/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.ProductKernels

namespace TraceableAgency

universe u

/-!
## Product-block transfer from A3/A4/A5
-/

/-- Four labels for a common finite-block replacement environment. -/
inductive ProductBlockReplacementBlock : Type u
  | originalLeft
  | replacementLeft
  | originalRight
  | replacementRight
  deriving DecidableEq, Fintype

open ProductBlockReplacementBlock

/-- Action alphabets for the common product-block replacement environment. -/
def productBlockReplacementAct
    (A A' B B' : Type u) : ProductBlockReplacementBlock → Type u
  | originalLeft => A
  | replacementLeft => A'
  | originalRight => B
  | replacementRight => B'

noncomputable instance productBlockReplacementActFintype
    {A A' B B' : Type u} [Fintype A] [Fintype A'] [Fintype B] [Fintype B'] :
    ∀ k : ProductBlockReplacementBlock, Fintype (productBlockReplacementAct A A' B B' k)
  | originalLeft => show Fintype A from inferInstance
  | replacementLeft => show Fintype A' from inferInstance
  | originalRight => show Fintype B from inferInstance
  | replacementRight => show Fintype B' from inferInstance

instance productBlockReplacementActDecidableEq
    {A A' B B' : Type u} [DecidableEq A] [DecidableEq A'] [DecidableEq B]
    [DecidableEq B'] :
    ∀ k : ProductBlockReplacementBlock,
      DecidableEq (productBlockReplacementAct A A' B B' k)
  | originalLeft => show DecidableEq A from inferInstance
  | replacementLeft => show DecidableEq A' from inferInstance
  | originalRight => show DecidableEq B from inferInstance
  | replacementRight => show DecidableEq B' from inferInstance

/-- Outcome alphabets for the common product-block replacement environment. -/
def productBlockReplacementOut
    (O O' Y Y' : Type u) : ProductBlockReplacementBlock → Type u
  | originalLeft => O
  | replacementLeft => O'
  | originalRight => Y
  | replacementRight => Y'

noncomputable instance productBlockReplacementOutFintype
    {O O' Y Y' : Type u} [Fintype O] [Fintype O'] [Fintype Y] [Fintype Y'] :
    ∀ k : ProductBlockReplacementBlock, Fintype (productBlockReplacementOut O O' Y Y' k)
  | originalLeft => show Fintype O from inferInstance
  | replacementLeft => show Fintype O' from inferInstance
  | originalRight => show Fintype Y from inferInstance
  | replacementRight => show Fintype Y' from inferInstance

instance productBlockReplacementOutDecidableEq
    {O O' Y Y' : Type u} [DecidableEq O] [DecidableEq O'] [DecidableEq Y]
    [DecidableEq Y'] :
    ∀ k : ProductBlockReplacementBlock,
      DecidableEq (productBlockReplacementOut O O' Y Y' k)
  | originalLeft => show DecidableEq O from inferInstance
  | replacementLeft => show DecidableEq O' from inferInstance
  | originalRight => show DecidableEq Y from inferInstance
  | replacementRight => show DecidableEq Y' from inferInstance

/-- Channels for the common product-block replacement environment. -/
noncomputable def productBlockReplacementChannel
    {A A' B B' O O' Y Y' : Type u}
    [Fintype O] [Fintype O'] [Fintype Y] [Fintype Y']
    (P : Channel A O) (P' : Channel A' O')
    (Q : Channel B Y) (Q' : Channel B' Y') :
    ∀ k : ProductBlockReplacementBlock,
      Channel (productBlockReplacementAct A A' B B' k)
        (productBlockReplacementOut O O' Y Y' k)
  | originalLeft => show Channel A O from P
  | replacementLeft => show Channel A' O' from P'
  | originalRight => show Channel B Y from Q
  | replacementRight => show Channel B' Y' from Q'

/--
Common-block transfer: if each side of a two-block comparison is weakly
equivalent to a replacement side, then A3 and transitivity preserve the
pairwise comparison.
-/
theorem pairwise_product_block_replacement_from_weak_equiv
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A A' B B' O O' Y Y' : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B']
    [Fintype O] [DecidableEq O]
    [Fintype O'] [DecidableEq O']
    [Fintype Y] [DecidableEq Y]
    [Fintype Y'] [DecidableEq Y']
    (P : Channel A O) (P' : Channel A' O')
    (Q : Channel B Y) (Q' : Channel B' Y')
    (q : Dist A) (q' : Dist A') (r : Dist B) (r' : Dist B')
    (hleft_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q'))
    (hleft_to_old :
      F.rel (blockChannel P' P) (inlDist q') (inrDist q))
    (hright_to_new :
      F.rel (blockChannel Q Q') (inlDist r) (inrDist r'))
    (hright_to_old :
      F.rel (blockChannel Q' Q) (inlDist r') (inrDist r)) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      F.rel (blockChannel P' Q') (inlDist q') (inrDist r') := by
  classical
  let k0 : ProductBlockReplacementBlock.{u} := originalLeft
  let k1 : ProductBlockReplacementBlock.{u} := replacementLeft
  let k2 : ProductBlockReplacementBlock.{u} := originalRight
  let k3 : ProductBlockReplacementBlock.{u} := replacementRight
  let Act := productBlockReplacementAct A A' B B'
  let Out := productBlockReplacementOut O O' Y Y'
  let C := productBlockReplacementChannel P P' Q Q'
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act k0 q
  let x' := blockEmbedDist Act k1 q'
  let y := blockEmbedDist Act k2 r
  let y' := blockEmbedDist Act k3 r'
  have htrans :
      ∀ a b c : Dist ((k : ProductBlockReplacementBlock) × Act k),
        F.rel commonP a b → F.rel commonP b c → F.rel commonP a c :=
    (hax.weakOrder.1 commonP).2
  have h02_ne : k0 ≠ k2 := by decide
  have h01_ne : k0 ≠ k1 := by decide
  have h10_ne : k1 ≠ k0 := by decide
  have h23_ne : k2 ≠ k3 := by decide
  have h32_ne : k3 ≠ k2 := by decide
  have h13_ne : k1 ≠ k3 := by decide
  have hcommon_02 :
      F.rel commonP x y ↔
        F.rel (blockChannel P Q) (inlDist q) (inrDist r) := by
    simpa [commonP, x, y, k0, k2, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using
      (hax.blockCoherence.finite_block (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k2) h02_ne
        (qᵢ := q) (qⱼ := r))
  have hcommon_01 : F.rel commonP x x' := by
    have h :=
      (hax.blockCoherence.finite_block (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k1) h01_ne
        (qᵢ := q) (qⱼ := q')).mpr hleft_to_new
    simpa [commonP, x, x', k0, k1, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hcommon_10 : F.rel commonP x' x := by
    have h :=
      (hax.blockCoherence.finite_block (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k0) h10_ne
        (qᵢ := q') (qⱼ := q)).mpr hleft_to_old
    simpa [commonP, x, x', k0, k1, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hcommon_23 : F.rel commonP y y' := by
    have h :=
      (hax.blockCoherence.finite_block (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k2) (j := k3) h23_ne
        (qᵢ := r) (qⱼ := r')).mpr hright_to_new
    simpa [commonP, y, y', k2, k3, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hcommon_32 : F.rel commonP y' y := by
    have h :=
      (hax.blockCoherence.finite_block (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k3) (j := k2) h32_ne
        (qᵢ := r') (qⱼ := r)).mpr hright_to_old
    simpa [commonP, y, y', k2, k3, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hreplace : F.rel commonP x y ↔ F.rel commonP x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonP a b) htrans
      hcommon_01 hcommon_10 hcommon_23 hcommon_32
  have hcommon_13 :
      F.rel commonP x' y' ↔
        F.rel (blockChannel P' Q') (inlDist q') (inrDist r') := by
    simpa [commonP, x', y', k1, k3, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using
      (hax.blockCoherence.finite_block (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k3) h13_ne
        (qᵢ := q') (qⱼ := r'))
  exact hcommon_02.symm.trans (hreplace.trans hcommon_13)

theorem original_rel_leftUnitOutcome
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel (blockChannel P (leftUnitOutcomeChannel P)) (inlDist q) (inrDist q) := by
  have h := hax.recordProcessing P outcomeRightUnitKernel q
  simpa [postprocess_outcomeRightUnit_eq_leftUnitOutcome P] using h

theorem leftUnitOutcome_rel_original
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel (blockChannel (leftUnitOutcomeChannel P) P) (inlDist q) (inrDist q) := by
  have h := hax.recordProcessing (leftUnitOutcomeChannel P) outcomeRightUnitProjectKernel q
  simpa [postprocess_leftUnitOutcome_project_eq P] using h

theorem original_rel_rightUnitOutcome
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {B Y : Type u} [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (r : Dist B) :
    F.rel (blockChannel Q (rightUnitOutcomeChannel Q)) (inlDist r) (inrDist r) := by
  have h := hax.recordProcessing Q outcomeLeftUnitKernel r
  simpa [postprocess_outcomeLeftUnit_eq_rightUnitOutcome Q] using h

theorem rightUnitOutcome_rel_original
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {B Y : Type u} [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (r : Dist B) :
    F.rel (blockChannel (rightUnitOutcomeChannel Q) Q) (inlDist r) (inrDist r) := by
  have h := hax.recordProcessing (rightUnitOutcomeChannel Q) outcomeLeftUnitProjectKernel r
  simpa [postprocess_rightUnitOutcome_project_eq Q] using h

theorem leftProductLift_rel_leftUnitOutcome
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (leftProductLiftChannel (B := B) P) (leftUnitOutcomeChannel P))
      (inlDist (prodDist q r)) (inrDist q) := by
  have h :=
    hax.actionProcessing (leftProductLiftChannel (B := B) P) (prodDist q r)
      (fstProjectionKernel (A := A) (B := B)) (leftUnitOutcomeChannel P)
      (leftProductLift_isBayesPushforwardCompletion_fst P q r)
  simpa [actionPushforward_prod_fst q r] using h

theorem leftUnitOutcome_rel_leftProductLift
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (leftUnitOutcomeChannel P) (leftProductLiftChannel (B := B) P))
      (inlDist q) (inrDist (prodDist q r)) := by
  have h :=
    hax.actionProcessing (leftUnitOutcomeChannel P) q (leftEmbedKernel (A := A) r)
      (leftProductLiftChannel (B := B) P)
      (leftUnitOutcome_isBayesPushforwardCompletion_leftEmbed P q r)
  simpa [actionPushforward_leftEmbed q r] using h

theorem rightProductLift_rel_rightUnitOutcome
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (rightProductLiftChannel (A := A) Q) (rightUnitOutcomeChannel Q))
      (inlDist (prodDist q r)) (inrDist r) := by
  have h :=
    hax.actionProcessing (rightProductLiftChannel (A := A) Q) (prodDist q r)
      (sndProjectionKernel (A := A) (B := B)) (rightUnitOutcomeChannel Q)
      (rightProductLift_isBayesPushforwardCompletion_snd Q q r)
  simpa [actionPushforward_prod_snd q r] using h

theorem rightUnitOutcome_rel_rightProductLift
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (rightUnitOutcomeChannel Q) (rightProductLiftChannel (A := A) Q))
      (inlDist r) (inrDist (prodDist q r)) := by
  have h :=
    hax.actionProcessing (rightUnitOutcomeChannel Q) r (rightEmbedKernel (B := B) q)
      (rightProductLiftChannel (A := A) Q)
      (rightUnitOutcome_isBayesPushforwardCompletion_rightEmbed Q q r)
  simpa [actionPushforward_rightEmbed q r] using h

theorem product_block_transfer_of_A5_A3
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      ProductLiftedComparison F q r P Q := by
  have horig_to_unit :
      F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
        F.rel (blockChannel (leftUnitOutcomeChannel P) (rightUnitOutcomeChannel Q))
          (inlDist q) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax P
      (leftUnitOutcomeChannel P) Q (rightUnitOutcomeChannel Q) q q r r
      (original_rel_leftUnitOutcome F hax P q)
      (leftUnitOutcome_rel_original F hax P q)
      (original_rel_rightUnitOutcome F hax Q r)
      (rightUnitOutcome_rel_original F hax Q r)
  have hunit_to_product :
      F.rel (blockChannel (leftUnitOutcomeChannel P) (rightUnitOutcomeChannel Q))
          (inlDist q) (inrDist r) ↔
        F.rel (blockChannel (leftProductLiftChannel (B := B) P)
            (rightProductLiftChannel (A := A) Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftUnitOutcomeChannel P) (leftProductLiftChannel (B := B) P)
      (rightUnitOutcomeChannel Q) (rightProductLiftChannel (A := A) Q)
      q (prodDist q r) r (prodDist q r)
      (leftUnitOutcome_rel_leftProductLift F hax P q r)
      (leftProductLift_rel_leftUnitOutcome F hax P q r)
      (rightUnitOutcome_rel_rightProductLift F hax Q q r)
      (rightProductLift_rel_rightUnitOutcome F hax Q q r)
  have hproduct :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (rightProductLiftChannel (A := A) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        ProductLiftedComparison F q r P Q := by
    rfl
  exact horig_to_unit.trans (hunit_to_product.trans hproduct)

end TraceableAgency
