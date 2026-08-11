/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.ProductReplacement

namespace TraceableAgency

universe u

/-!
## Derived background inertness

Paper v7, Lemma `background`.  The old A7 independent-background axiom is
derived here from A1, A3, A4, A5, and the weak/strict clauses of A6.  The proof
is deliberately kept at the primitive preference level, before any product
scale or cardinal product representation is constructed.
-/

/-- A pairwise comparison between first-coordinate product lifts is exactly
the original first-coordinate comparison.  This is the A5 projection/embedding
neutrality step of the v7 background-inertness proof, with reversible outcome
padding supplied by A4 and pairwise replacement by A1/A3.  No support
assumption is needed. -/
theorem product_left_lifted_rel_iff_base
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (P Q : Channel A O) :
    F.rel
        (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) := by
  have hlift_to_unit :
      F.rel
          (blockChannel (leftProductLiftChannel (B := B) P)
            (leftProductLiftChannel (B := B) Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        F.rel
          (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
          (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftProductLiftChannel (B := B) P) (leftUnitOutcomeChannel P)
      (leftProductLiftChannel (B := B) Q) (leftUnitOutcomeChannel Q)
      (prodDist q r) q (prodDist q r) q
      (leftProductLift_rel_leftUnitOutcome F hax P q r)
      (leftUnitOutcome_rel_leftProductLift F hax P q r)
      (leftProductLift_rel_leftUnitOutcome F hax Q q r)
      (leftUnitOutcome_rel_leftProductLift F hax Q q r)
  have hunit_to_base :
      F.rel
          (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
          (inlDist q) (inrDist q) ↔
        F.rel (blockChannel P Q) (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftUnitOutcomeChannel P) P
      (leftUnitOutcomeChannel Q) Q
      q q q q
      (leftUnitOutcome_rel_original F hax P q)
      (original_rel_leftUnitOutcome F hax P q)
      (leftUnitOutcome_rel_original F hax Q q)
      (original_rel_leftUnitOutcome F hax Q q)
  exact hlift_to_unit.trans hunit_to_base

/-- Symmetric second-coordinate version of
`product_left_lifted_rel_iff_base`. -/
theorem product_right_lifted_rel_iff_base
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (P Q : Channel B O) :
    F.rel
        (blockChannel (rightProductLiftChannel (A := A) P)
          (rightProductLiftChannel (A := A) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel P Q) (inlDist r) (inrDist r) := by
  have hlift_to_unit :
      F.rel
          (blockChannel (rightProductLiftChannel (A := A) P)
            (rightProductLiftChannel (A := A) Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        F.rel
          (blockChannel (rightUnitOutcomeChannel P) (rightUnitOutcomeChannel Q))
          (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightProductLiftChannel (A := A) P) (rightUnitOutcomeChannel P)
      (rightProductLiftChannel (A := A) Q) (rightUnitOutcomeChannel Q)
      (prodDist q r) r (prodDist q r) r
      (rightProductLift_rel_rightUnitOutcome F hax P q r)
      (rightUnitOutcome_rel_rightProductLift F hax P q r)
      (rightProductLift_rel_rightUnitOutcome F hax Q q r)
      (rightUnitOutcome_rel_rightProductLift F hax Q q r)
  have hunit_to_base :
      F.rel
          (blockChannel (rightUnitOutcomeChannel P) (rightUnitOutcomeChannel Q))
          (inlDist r) (inrDist r) ↔
        F.rel (blockChannel P Q) (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightUnitOutcomeChannel P) P
      (rightUnitOutcomeChannel Q) Q
      r r r r
      (rightUnitOutcome_rel_original F hax P r)
      (original_rel_rightUnitOutcome F hax P r)
      (rightUnitOutcome_rel_original F hax Q r)
      (original_rel_rightUnitOutcome F hax Q r)
  exact hlift_to_unit.trans hunit_to_base

/-- Outcome relabeling from “background first, foreground second” to the
ordinary product-channel outcome order. -/
def rightBackgroundFirstOutcomeEquiv (O Y : Type u) :
    ((_ : PUnit.{u + 1} × Y) × (O × PUnit.{u + 1})) ≃ (O × Y) where
  toFun x := (x.2.1, x.1.2)
  invFun x := ⟨(PUnit.unit, x.2), (x.1, PUnit.unit)⟩
  left_inv := by
    intro x
    rcases x with ⟨⟨u₁, y⟩, ⟨o, u₂⟩⟩
    cases u₁
    cases u₂
    rfl
  right_inv := by
    intro x
    rfl

/-- The sequential channel that observes the right background first and then
runs a constant left-coordinate continuation is the corresponding product
channel, up to the canonical outcome relabeling. -/
theorem relabel_rightBackgroundFirst_seq_eq_prod
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (R : Channel B Y) :
    Relabeling.relabelChannel (Equiv.refl (A × B))
        (rightBackgroundFirstOutcomeEquiv O Y)
        (seqComposeDep (rightProductLiftChannel (A := A) R)
          (fun _ => O × PUnit.{u + 1})
          (fun _ => leftProductLiftChannel (B := B) P)) =
      prodChannel P R := by
  ext ab oy
  rcases ab with ⟨a, b⟩
  rcases oy with ⟨o, y⟩
  simp only [Relabeling.relabelChannel_apply]
  change
    rightProductLiftChannel (A := A) R (a, b) (PUnit.unit, y) *
        leftProductLiftChannel (B := B) P (a, b) (o, PUnit.unit) =
      prodChannel P R (a, b) (o, y)
  simp [rightProductLiftChannel, leftProductLiftChannel,
    Channel.uninformativeChannelU, prodChannel_apply_pair]
  ring

/-- A reached posterior after observing only the right background remains a
product, with unchanged left marginal. -/
theorem branchPosterior_rightProductLift_eq_prod
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y)
    (uy : PUnit.{u + 1} × Y)
    (hpos : BranchPositive (rightProductLiftChannel (A := A) R)
      (prodDist q r) uy) :
    branchPosterior (rightProductLiftChannel (A := A) R)
        (prodDist q r) uy =
      prodDist q (branchPosterior R r uy.2) := by
  rcases uy with ⟨u₀, y⟩
  cases u₀
  have hmarg :
      Channel.outcomeMarginal (rightProductLiftChannel (A := A) R)
          (prodDist q r) (PUnit.unit, y) =
        Channel.outcomeMarginal R r y := by
    change
      (∑ ab : A × B,
          prodDist q r ab *
            rightProductLiftChannel (A := A) R ab (PUnit.unit, y)) =
        ∑ b : B, r b * R b y
    rw [Fintype.sum_prod_type]
    simp only [prodDist_apply_pair, rightProductLiftChannel,
      prodChannel_apply_pair, Channel.uninformativeChannelU, one_mul]
    calc
      (∑ a : A, ∑ b : B, q a * r b * R b y) =
          ∑ a : A, q a * (∑ b : B, r b * R b y) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            ring
      _ = (∑ a : A, q a) * (∑ b : B, r b * R b y) := by
            rw [Finset.sum_mul]
      _ = ∑ b : B, r b * R b y := by rw [q.sum_eq_one, one_mul]
  have hposR : BranchPositive R r y := by
    change Channel.outcomeMarginal R r y > 0
    rw [← hmarg]
    exact hpos
  have hpos' :
      Channel.outcomeMarginal (rightProductLiftChannel (A := A) R)
          (prodDist q r) (PUnit.unit, y) > 0 :=
    hpos
  have hposR' : Channel.outcomeMarginal R r y > 0 := hposR
  unfold branchPosterior Channel.posterior
  rw [dif_pos hpos', dif_pos hposR']
  ext ab
  rcases ab with ⟨a, b⟩
  change
    prodDist q r (a, b) *
          rightProductLiftChannel (A := A) R (a, b) (PUnit.unit, y) /
        Channel.outcomeMarginal (rightProductLiftChannel (A := A) R)
          (prodDist q r) (PUnit.unit, y) =
      q a * (r b * R b y / Channel.outcomeMarginal R r y)
  rw [hmarg]
  simp only [prodDist_apply_pair, rightProductLiftChannel,
    prodChannel_apply_pair, Channel.uninformativeChannelU, one_mul]
  ring

/-- Every finite first-stage channel has at least one reached branch. -/
theorem exists_branchPositive
    {A O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    ∃ o, BranchPositive P q o := by
  classical
  let m := Channel.outcomeMarginal P q
  have hne : ∃ o : O, m o ≠ 0 := by
    by_contra h
    have hzero : ∀ o : O, m o = 0 := by
      intro o
      simpa using (not_exists.mp h o)
    have hsum : (∑ o : O, m o) = 0 := by
      apply Finset.sum_eq_zero
      intro o _
      exact hzero o
    linarith [m.sum_eq_one]
  obtain ⟨o, ho⟩ := hne
  refine ⟨o, ?_⟩
  change m o > 0
  exact lt_of_le_of_ne (m.nonneg o) (Ne.symm ho)

/-- Reversible outcome relabeling identifies a product-channel comparison with
the comparison of its “right background first” sequential presentations. -/
theorem product_left_background_rel_iff_sequential
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (P Q : Channel A O) (R : Channel B Y) :
    F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel
        (blockChannel
          (seqComposeDep (rightProductLiftChannel (A := A) R)
            (fun _ => O × PUnit.{u + 1})
            (fun _ => leftProductLiftChannel (B := B) P))
          (seqComposeDep (rightProductLiftChannel (A := A) R)
            (fun _ => O × PUnit.{u + 1})
            (fun _ => leftProductLiftChannel (B := B) Q)))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) := by
  let e := rightBackgroundFirstOutcomeEquiv O Y
  let seqP :=
    seqComposeDep (rightProductLiftChannel (A := A) R)
      (fun _ => O × PUnit.{u + 1})
      (fun _ => leftProductLiftChannel (B := B) P)
  let seqQ :=
    seqComposeDep (rightProductLiftChannel (A := A) R)
      (fun _ => O × PUnit.{u + 1})
      (fun _ => leftProductLiftChannel (B := B) Q)
  have heqP :
      Relabeling.relabelChannel (Equiv.refl (A × B)) e seqP =
        prodChannel P R := by
    simpa [e, seqP] using relabel_rightBackgroundFirst_seq_eq_prod P R
  have heqQ :
      Relabeling.relabelChannel (Equiv.refl (A × B)) e seqQ =
        prodChannel Q R := by
    simpa [e, seqQ] using relabel_rightBackgroundFirst_seq_eq_prod Q R
  have hseqP_to_prodP :
      F.rel (blockChannel seqP (prodChannel P R))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) := by
    have h :=
      hax.recordProcessing seqP (Relabeling.outcomeEquivKernel e) (prodDist q r)
    rw [Relabeling.postprocess_outcomeEquiv_eq_relabel, heqP] at h
    exact h
  have hprodP_to_seqP :
      F.rel (blockChannel (prodChannel P R) seqP)
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) := by
    have h :=
      hax.recordProcessing (prodChannel P R) (Relabeling.outcomeEquivKernel e.symm)
        (prodDist q r)
    have heqP' :
        Relabeling.relabelChannel (Equiv.refl (A × B)) e.symm
            (prodChannel P R) =
          seqP := by
      rw [← heqP]
      simpa using
        (Relabeling.relabelChannel_symm (Equiv.refl (A × B)) e seqP)
    rw [Relabeling.postprocess_outcomeEquiv_eq_relabel, heqP'] at h
    exact h
  have hseqQ_to_prodQ :
      F.rel (blockChannel seqQ (prodChannel Q R))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) := by
    have h :=
      hax.recordProcessing seqQ (Relabeling.outcomeEquivKernel e) (prodDist q r)
    rw [Relabeling.postprocess_outcomeEquiv_eq_relabel, heqQ] at h
    exact h
  have hprodQ_to_seqQ :
      F.rel (blockChannel (prodChannel Q R) seqQ)
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) := by
    have h :=
      hax.recordProcessing (prodChannel Q R) (Relabeling.outcomeEquivKernel e.symm)
        (prodDist q r)
    have heqQ' :
        Relabeling.relabelChannel (Equiv.refl (A × B)) e.symm
            (prodChannel Q R) =
          seqQ := by
      rw [← heqQ]
      simpa using
        (Relabeling.relabelChannel_symm (Equiv.refl (A × B)) e seqQ)
    rw [Relabeling.postprocess_outcomeEquiv_eq_relabel, heqQ'] at h
    exact h
  simpa [seqP, seqQ] using
    (pairwise_product_block_replacement_from_weak_equiv F hax
      (prodChannel P R) seqP (prodChannel Q R) seqQ
      (prodDist q r) (prodDist q r) (prodDist q r) (prodDist q r)
      hprodP_to_seqP hseqP_to_prodP hprodQ_to_seqQ hseqQ_to_prodQ)

/-- **Derived background inertness, first coordinate.**

Adding the same statistically independent right background to both foreground
channels preserves and reflects their comparison.  This is the stronger
statement from paper v7; unlike the old A7, it identifies the product
comparison with the background-free comparison itself. -/
theorem derived_background_inertness_left
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (P Q : Channel A O) (R : Channel B Y) :
    F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) := by
  let bg := rightProductLiftChannel (A := A) R
  let O₂ : (PUnit.{u + 1} × Y) → Type u :=
    fun _ => O × PUnit.{u + 1}
  let contP : ∀ _ : PUnit.{u + 1} × Y, Channel (A × B) (O × PUnit.{u + 1}) :=
    fun _ => leftProductLiftChannel (B := B) P
  let contQ : ∀ _ : PUnit.{u + 1} × Y, Channel (A × B) (O × PUnit.{u + 1}) :=
    fun _ => leftProductLiftChannel (B := B) Q
  have htransport :=
    product_left_background_rel_iff_sequential F hax q r P Q R
  constructor
  · intro hprod
    have hseq :
        F.rel (blockChannel (seqComposeDep bg O₂ contP)
            (seqComposeDep bg O₂ contQ))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) := by
      simpa [bg, O₂, contP, contQ] using htransport.mp hprod
    by_contra hbase
    have hcomplete :=
      (hax.weakOrder.1 (blockChannel P Q)).1 (inlDist q) (inrDist q)
    have hreverse_same :
        F.rel (blockChannel P Q) (inrDist q) (inlDist q) :=
      hcomplete.resolve_left hbase
    have hQP :
        F.rel (blockChannel Q P) (inlDist q) (inrDist q) :=
      (Relabeling.block_swap_rel_of_axioms F hax P Q q q).mp
        hreverse_same
    have hbranches :
        ∀ uy, BranchPositive bg (prodDist q r) uy →
          F.rel (blockChannel (contQ uy) (contP uy))
            (inlDist (branchPosterior bg (prodDist q r) uy))
            (inrDist (branchPosterior bg (prodDist q r) uy)) := by
      intro uy huy
      have hpost :=
        branchPosterior_rightProductLift_eq_prod q r R uy (by
          simpa [bg] using huy)
      rw [show branchPosterior bg (prodDist q r) uy =
          prodDist q (branchPosterior R r uy.2) by
            simpa [bg] using hpost]
      exact
        (product_left_lifted_rel_iff_base F hax q
          (branchPosterior R r uy.2) Q P).mpr hQP
    obtain ⟨uy, huy⟩ := exists_branchPositive bg (prodDist q r)
    have hnotPQbranch :
        ¬ F.rel (blockChannel (contP uy) (contQ uy))
            (inlDist (branchPosterior bg (prodDist q r) uy))
            (inrDist (branchPosterior bg (prodDist q r) uy)) := by
      intro hPQ
      have hpost :=
        branchPosterior_rightProductLift_eq_prod q r R uy (by
          simpa [bg] using huy)
      have hPQ' :
          F.rel
              (blockChannel (leftProductLiftChannel (B := B) P)
                (leftProductLiftChannel (B := B) Q))
              (inlDist (prodDist q (branchPosterior R r uy.2)))
              (inrDist (prodDist q (branchPosterior R r uy.2))) := by
        simpa [bg, contP, contQ, hpost] using hPQ
      exact hbase
        ((product_left_lifted_rel_iff_base F hax q
          (branchPosterior R r uy.2) P Q).mp hPQ')
    have hstrictBranch :
        F.strictRel (blockChannel (contQ uy) (contP uy))
          (inlDist (branchPosterior bg (prodDist q r) uy))
          (inrDist (branchPosterior bg (prodDist q r) uy)) := by
      refine ⟨hbranches uy huy, ?_⟩
      intro hreverse
      exact hnotPQbranch
        ((Relabeling.block_swap_rel_of_axioms F hax
          (contQ uy) (contP uy)
          (branchPosterior bg (prodDist q r) uy)
          (branchPosterior bg (prodDist q r) uy)).mp hreverse)
    have hstrictSeq :
        F.strictRel (blockChannel (seqComposeDep bg O₂ contQ)
            (seqComposeDep bg O₂ contP))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) :=
      hax.branchContinuation.2 O₂ (prodDist q r) bg contQ contP hbranches
        ⟨uy, huy, hstrictBranch⟩
    exact hstrictSeq.2
      ((Relabeling.block_swap_rel_of_axioms F hax
        (seqComposeDep bg O₂ contQ) (seqComposeDep bg O₂ contP)
        (prodDist q r) (prodDist q r)).mpr hseq)
  · intro hbase
    have hbranches :
        ∀ uy, BranchPositive bg (prodDist q r) uy →
          F.rel (blockChannel (contP uy) (contQ uy))
            (inlDist (branchPosterior bg (prodDist q r) uy))
            (inrDist (branchPosterior bg (prodDist q r) uy)) := by
      intro uy huy
      have hpost :=
        branchPosterior_rightProductLift_eq_prod q r R uy (by
          simpa [bg] using huy)
      rw [show branchPosterior bg (prodDist q r) uy =
          prodDist q (branchPosterior R r uy.2) by
            simpa [bg] using hpost]
      exact
        (product_left_lifted_rel_iff_base F hax q
          (branchPosterior R r uy.2) P Q).mpr hbase
    have hseq :
        F.rel (blockChannel (seqComposeDep bg O₂ contP)
            (seqComposeDep bg O₂ contQ))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) :=
      hax.branchContinuation.1 O₂ (prodDist q r) bg contP contQ hbranches
    exact htransport.mpr (by
      simpa [bg, O₂, contP, contQ] using hseq)

/-- Swapping product coordinates sends a product prior to the reversed product
prior. -/
@[simp]
theorem relabelDist_prodComm_background
    {A B : Type u} [Fintype A] [Fintype B]
    (q : Dist A) (r : Dist B) :
    Relabeling.relabelDist (Equiv.prodComm A B) (prodDist q r) =
      prodDist r q := by
  ext ab
  rcases ab with ⟨b, a⟩
  simp [Relabeling.relabelDist, prodDist_apply_pair, mul_comm]

/-- Swapping both action and outcome coordinates reverses a product channel. -/
@[simp]
theorem relabelChannel_prodComm_background
    {A B O Y : Type u}
    [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (P : Channel A O) (R : Channel B Y) :
    Relabeling.relabelChannel (Equiv.prodComm A B) (Equiv.prodComm O Y)
        (prodChannel P R) =
      prodChannel R P := by
  ext ba yo
  rcases ba with ⟨b, a⟩
  rcases yo with ⟨y, o⟩
  simp [Relabeling.relabelChannel, prodChannel_apply_pair, mul_comm]

/-- A right-coordinate product comparison is the relabeling of the
corresponding left-coordinate comparison after swapping product coordinates. -/
theorem product_right_comparison_relabel_to_left
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B X O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype X] [DecidableEq X]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B)
    (R : Channel A X) (P Q : Channel B O) :
    F.rel (blockChannel (prodChannel R P) (prodChannel R Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
        (inlDist (prodDist r q)) (inrDist (prodDist r q)) := by
  have h :=
    Relabeling.relabel_rel_of_axioms F hax
      (Equiv.sumCongr (Equiv.prodComm A B) (Equiv.prodComm A B))
      (Equiv.sumCongr (Equiv.prodComm X O) (Equiv.prodComm X O))
      (blockChannel (prodChannel R P) (prodChannel R Q))
      (inlDist (prodDist q r)) (inrDist (prodDist q r))
  simpa only [Relabeling.relabel_blockChannel_sumCongr_eq,
    relabelChannel_prodComm_background,
    Relabeling.relabelDist_sumCongr_inl,
    Relabeling.relabelDist_sumCongr_inr,
    relabelDist_prodComm_background] using h

/-- **Derived background inertness, second coordinate.**  This is the
coordinate-swapped consequence of `derived_background_inertness_left`. -/
theorem derived_background_inertness_right
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A B X O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype X] [DecidableEq X]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B)
    (R : Channel A X) (P Q : Channel B O) :
    F.rel (blockChannel (prodChannel R P) (prodChannel R Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel P Q) (inlDist r) (inrDist r) :=
  (product_right_comparison_relabel_to_left F hax q r R P Q).trans
    (derived_background_inertness_left F hax r q P Q R)

/-- The v6 A7 predicate is a theorem of the v7 axioms.  Full support is not
used: the derivation actually establishes background inertness on boundary
priors as well. -/
theorem independentBackgroundSeparability_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    IndependentBackgroundSeparability F := by
  constructor
  · intro A₁ A₂ O₁ O₂R O₂S _ _ _ _ _ _ _ _ _ _ q₁ q₂ _hq₁ _hq₂ P₁ Q₁ R₂ S₂
    letI : Nonempty A₁ := Relabeling.nonempty_of_dist q₁
    letI : Nonempty A₂ := Relabeling.nonempty_of_dist q₂
    exact
      (derived_background_inertness_left F hax q₁ q₂ P₁ Q₁ R₂).trans
        (derived_background_inertness_left F hax q₁ q₂ P₁ Q₁ S₂).symm
  · intro A₁ A₂ O₁R O₁S O₂ _ _ _ _ _ _ _ _ _ _ q₁ q₂ _hq₁ _hq₂ R₁ S₁ P₂ Q₂
    letI : Nonempty A₁ := Relabeling.nonempty_of_dist q₁
    letI : Nonempty A₂ := Relabeling.nonempty_of_dist q₂
    exact
      (derived_background_inertness_right F hax q₁ q₂ R₁ P₂ Q₂).trans
        (derived_background_inertness_right F hax q₁ q₂ S₁ P₂ Q₂).symm

/-- The same-prior product-lifted comparison is represented by the product-prior
value functional. This is internal: it is exactly
`PosteriorValueRepresentation.represents_block_comparisons` plus
`prodDist_fullSupport`. -/
theorem productLiftedComparison_represents
    (F : PrefFamily.{u})
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    ProductLiftedComparison F q r P Q ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) Q)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r _hq _hr
  exact
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (rightProductLiftChannel (A := A) Q))

/-- Derived background inertness, transported through the same-prior value representation, says that the
value order between first-coordinate product experiments is independent of the
second-coordinate background. This is the ordinal product-coordinate
independence step of paper Lemma `coherentnorm`; the later cardinal bilinear
form is kept separate. -/
theorem product_left_coordinate_value_order_independent
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B O O₂R O₂S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype O₂R] [DecidableEq O₂R]
    [Fintype O₂S] [DecidableEq O₂S]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) (R : Channel B O₂R) (S : Channel B O₂S) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q R)) ↔
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P S)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q S)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel Q R))
  have hS :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P S))
      (experimentOfChannel (prodChannel Q S))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q R)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel P S) (prodChannel Q S))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P S)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q S)) at hS'
  exact hR'.symm.trans
    (((independentBackgroundSeparability_of_axioms F hax).1
      q r hq hr P Q R S).trans hS')

/-- Symmetric derived value-order independence for second-coordinate product
experiments. -/
theorem product_right_coordinate_value_order_independent
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B O₁R O₁S O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O₁R] [DecidableEq O₁R]
    [Fintype O₁S] [DecidableEq O₁S]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel A O₁R) (S : Channel A O₁S) (P Q : Channel B O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R P)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R Q)) ↔
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S P)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S Q)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel R P))
      (experimentOfChannel (prodChannel R Q))
  have hS :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel S P))
      (experimentOfChannel (prodChannel S Q))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel R P) (prodChannel R Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R Q)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel S P) (prodChannel S Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S Q)) at hS'
  exact hR'.symm.trans
    (((independentBackgroundSeparability_of_axioms F hax).2
      q r hq hr R S P Q).trans hS')

/-- Product left-slice value functional:
`P ↦ V_{q⊗r}(P⊗R)` for fixed full-support product prior and fixed
second-coordinate background. -/
noncomputable def productLeftSliceValue
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y)
    (P : Channel A O) : ℝ :=
  hs.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Product left-slice order with no-information background is the original
first-coordinate order. This is the projection/embedding part of Step 1 of
paper Lemma `coherentnorm`, proved from the A3/A4/A5 weak-equivalence
machinery internalized in Stage 10C. -/
theorem product_left_noInfo_value_order_iff_base
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) Q)) ↔
    hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
  have hprod_rel :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) := by
    change
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftProductLiftChannel (B := B) P) (leftUnitOutcomeChannel P)
      (leftProductLiftChannel (B := B) Q) (leftUnitOutcomeChannel Q)
      (prodDist q r) q (prodDist q r) q
      (leftProductLift_rel_leftUnitOutcome F hax P q r)
      (leftUnitOutcome_rel_leftProductLift F hax P q r)
      (leftProductLift_rel_leftUnitOutcome F hax Q q r)
      (leftUnitOutcome_rel_leftProductLift F hax Q q r)
  have hunit_to_base :
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) ↔
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftUnitOutcomeChannel P) P
      (leftUnitOutcomeChannel Q) Q
      q q q q
      (leftUnitOutcome_rel_original F hax P q)
      (original_rel_leftUnitOutcome F hax P q)
      (leftUnitOutcome_rel_original F hax Q q)
      (original_rel_leftUnitOutcome F hax Q q)
  have hbase_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      q hq (experimentOfChannel P) (experimentOfChannel Q)
  have hbase_rel :
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
    change
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- For a fixed second-coordinate background, the product left-slice value and
the original first-coordinate value represent the same weak order. This is the
Lean version of Step 1 of paper Lemma `coherentnorm` for first-coordinate
slices. -/
theorem product_left_slice_same_order
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) (R : Channel B Y) :
    productLeftSliceValue hs q r R P ≥ productLeftSliceValue hs q r R Q ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
  have hbackground :=
    product_left_coordinate_value_order_independent F hax hs
      q r hq hr P Q R (Channel.uninformativeChannelU B)
  have hbase :=
    product_left_noInfo_value_order_iff_base F hax hs q r hq hr P Q
  exact (by
    simpa [productLeftSliceValue, leftProductLiftChannel] using
      hbackground.trans hbase)

/-- Product right-slice value functional:
`R ↦ V_{q⊗r}(P⊗R)` for fixed full-support product prior and fixed
first-coordinate background. -/
noncomputable def productRightSliceValue
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O)
    (R : Channel B Y) : ℝ :=
  hs.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Product right-slice with no-information first-coordinate background recovers
the base second-coordinate order. Proved from A3/A4/A5 projection/embedding
machinery (right-side analogue of `product_left_noInfo_value_order_iff_base`). -/
theorem product_right_noInfo_value_order_iff_base
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R S : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) S)) ↔
    hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (rightProductLiftChannel (A := A) R))
      (experimentOfChannel (rightProductLiftChannel (A := A) S))
  have hprod_rel :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) := by
    change
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightProductLiftChannel (A := A) R) (rightUnitOutcomeChannel R)
      (rightProductLiftChannel (A := A) S) (rightUnitOutcomeChannel S)
      (prodDist q r) r (prodDist q r) r
      (rightProductLift_rel_rightUnitOutcome F hax R q r)
      (rightUnitOutcome_rel_rightProductLift F hax R q r)
      (rightProductLift_rel_rightUnitOutcome F hax S q r)
      (rightUnitOutcome_rel_rightProductLift F hax S q r)
  have hunit_to_base :
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) ↔
      F.rel (blockChannel R S) (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightUnitOutcomeChannel R) R
      (rightUnitOutcomeChannel S) S
      r r r r
      (rightUnitOutcome_rel_original F hax R r)
      (original_rel_rightUnitOutcome F hax R r)
      (rightUnitOutcome_rel_original F hax S r)
      (original_rel_rightUnitOutcome F hax S r)
  have hbase_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      r hr (experimentOfChannel R) (experimentOfChannel S)
  have hbase_rel :
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
    change
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- For a fixed first-coordinate background, the product right-slice value and
the original second-coordinate value represent the same weak order. Right-side
analogue of `product_left_slice_same_order`. -/
theorem product_right_slice_same_order
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R S : Channel B Y) :
    productRightSliceValue hs q r P R ≥ productRightSliceValue hs q r P S ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
  have hbackground :=
    product_right_coordinate_value_order_independent F hax hs
      q r hq hr (Channel.uninformativeChannelU A) P R S
  have hbase :=
    product_right_noInfo_value_order_iff_base F hax hs q r hq hr R S
  exact (by
    simpa [productRightSliceValue, rightProductLiftChannel] using
      hbackground.symm.trans hbase)

/--
**Product Left-Slice Affine Assumptions**

Paper-specific cardinal content from the first half of Step 2 of Lemma
`coherentnorm`. After product-coordinate order independence, affine-utility
uniqueness makes each first-coordinate slice a positive affine transform of the
first-coordinate representative:

`L_{q,r}(P,R) = α_R V_q(P) + γ_R`.
-/
structure FiniteProductLeftSliceAffineAssumptions.{v} where
  leftSliceSlope :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftSliceIntercept :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftSliceSlope_pos :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      0 < leftSliceSlope F hax hs q r R
  left_slice_affine :
    ∀ (F : PrefFamily.{v})
      (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftSliceSlope F hax hs q r R *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        leftSliceIntercept F hax hs q r R

/--
**Affine Slice Uniqueness Assumptions**

Paper-specific affine/HM uniqueness content behind Step 2 of Lemma
`coherentnorm`. The same-order fact for product left-slices is proved above;
what remains external here is the cardinal theorem that two nonconstant affine
representatives of that order differ by a positive affine transform.
-/
structure FiniteAffineSliceUniquenessAssumptions.{v} where
  left_slice_positive_affine_transform :
    ∀ (F : PrefFamily.{v})
      (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          productLeftSliceValue hs q r R P =
            a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b

/-- Left outcome marginal of a public-coin mixture. -/
theorem outcomeMarginal_publicMixChannel_inl
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (o : O) :
    Channel.outcomeMarginal (publicMixChannel t ht0 ht1 P Q) q (Sum.inl o) =
      t * Channel.outcomeMarginal P q o := by
  simp only [Channel.outcomeMarginal_apply, publicMixChannel]
  rw [Finset.mul_sum]
  congr 1
  ext a
  ring

/-- Right outcome marginal of a public-coin mixture. -/
theorem outcomeMarginal_publicMixChannel_inr
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (y : Y) :
    Channel.outcomeMarginal (publicMixChannel t ht0 ht1 P Q) q (Sum.inr y) =
      (1 - t) * Channel.outcomeMarginal Q q y := by
  simp only [Channel.outcomeMarginal_apply, publicMixChannel]
  rw [Finset.mul_sum]
  congr 1
  ext a
  ring

/-- Left branch posterior of a public-coin mixture. -/
theorem posterior_publicMixChannel_inl
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (o : O) :
    Channel.posterior (publicMixChannel t ht0 ht1 P Q) q (Sum.inl o) =
      Channel.posterior P q o := by
  ext a
  unfold Channel.posterior
  simp only [outcomeMarginal_publicMixChannel_inl]
  by_cases hm : Channel.outcomeMarginal P q o > 0
  · have hm_sum : 0 < ∑ x, q x * P x o := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have htm_sum : 0 < t * ∑ x, q x * P x o := mul_pos ht0 hm_sum
    simp [hm_sum, htm_sum, publicMixChannel]
    field_simp [ne_of_gt ht0]
  · have hm0 : Channel.outcomeMarginal P q o = 0 := by
      exact le_antisymm (not_lt.mp hm) ((Channel.outcomeMarginal P q).nonneg o)
    have hm_sum_nonpos : ¬ 0 < ∑ x, q x * P x o := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have hm_sum_eq : (∑ x, q x * P x o) = 0 := by
      simpa [Channel.outcomeMarginal_apply] using hm0
    have htm_sum_nonpos : ¬ 0 < t * ∑ x, q x * P x o := by
      simp [hm_sum_eq]
    simp [hm_sum_nonpos, htm_sum_nonpos]

/-- Right branch posterior of a public-coin mixture. -/
theorem posterior_publicMixChannel_inr
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (y : Y) :
    Channel.posterior (publicMixChannel t ht0 ht1 P Q) q (Sum.inr y) =
      Channel.posterior Q q y := by
  ext a
  unfold Channel.posterior
  simp only [outcomeMarginal_publicMixChannel_inr]
  have h1t_pos : 0 < 1 - t := by linarith
  by_cases hm : Channel.outcomeMarginal Q q y > 0
  · have hm_sum : 0 < ∑ x, q x * Q x y := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have htm_sum : 0 < (1 - t) * ∑ x, q x * Q x y :=
      mul_pos h1t_pos hm_sum
    simp [hm_sum, htm_sum, publicMixChannel]
    field_simp [ne_of_gt h1t_pos]
  · have hm0 : Channel.outcomeMarginal Q q y = 0 := by
      exact le_antisymm (not_lt.mp hm) ((Channel.outcomeMarginal Q q).nonneg y)
    have hm_sum_nonpos : ¬ 0 < ∑ x, q x * Q x y := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have hm_sum_eq : (∑ x, q x * Q x y) = 0 := by
      simpa [Channel.outcomeMarginal_apply] using hm0
    have htm_sum_nonpos : ¬ 0 < (1 - t) * ∑ x, q x * Q x y := by
      simp [hm_sum_eq]
    simp [hm_sum_nonpos, htm_sum_nonpos]

/--
Public-coin mixtures of implementing channels induce convex mixtures of
posterior laws, stated extensionally through posterior-law integrals.
-/
theorem posteriorLawIntegral_publicMixChannel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y)
    (φ : Dist A → ℝ) :
    posteriorLawIntegral q (publicMixChannel t ht0 ht1 P Q) φ =
      t * posteriorLawIntegral q P φ +
        (1 - t) * posteriorLawIntegral q Q φ := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_sum_type]
  simp only [outcomeMarginal_publicMixChannel_inl,
    outcomeMarginal_publicMixChannel_inr,
    posterior_publicMixChannel_inl,
    posterior_publicMixChannel_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring_nf

/--
**Posterior-Law Value Affinity**

Herstein--Milnor/value-representation interface content: the chosen posterior
value representative is affine over convex mixtures of posterior laws.  The
posterior laws are represented extensionally by their posterior-law integrals.
-/
structure FinitePosteriorLawValueAffineAssumptions.{v} where
  V_affine_of_posteriorLawIntegral_mix :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (_ht0 : 0 < t) (_ht1 : t < 1)
      (E_mix E₁ E₂ : FiniteExperimentOn A),
      (∀ φ : Dist A → ℝ, Continuous φ →
        posteriorLawIntegralExp q E_mix φ =
          t * posteriorLawIntegralExp q E₁ φ +
            (1 - t) * posteriorLawIntegralExp q E₂ φ) →
      hV.V q E_mix = t * hV.V q E₁ + (1 - t) * hV.V q E₂

/-- Affinity is intrinsic data of a `PosteriorValueRepresentation`: the latter
is the selected cardinal Herstein--Milnor representative, rather than an
arbitrary ordinal transform. -/
theorem finitePosteriorLawValueAffine_of_representation :
    FinitePosteriorLawValueAffineAssumptions.{u} where
  V_affine_of_posteriorLawIntegral_mix := by
    intro F hax hV A _ _ _ q hq t ht0 ht1 E_mix E₁ E₂ hmix
    exact hV.affine_of_posteriorLawIntegral_mix
      q t ht0 ht1 E_mix E₁ E₂ hmix

/--
**Posterior Value Public-Mix Affinity**

Compatibility package for public-coin mixtures of implementing channels.  Stage
10K derives this from the structural posterior-law mixture identity plus the
law-level Herstein--Milnor value-affinity interface.
-/
structure FinitePosteriorValueAffineAssumptions.{v} where
  V_publicMix_affine :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Y),
      hV.V q (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
        t * hV.V q (experimentOfChannel P) +
          (1 - t) * hV.V q (experimentOfChannel Q)

theorem posteriorValueAffine_of_lawAffine_and_publicMixLaw
    (hlaw : FinitePosteriorLawValueAffineAssumptions.{u}) :
    FinitePosteriorValueAffineAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hV A O Y _ _ _ _ _ _ _ q hq t ht0 ht1 P Q
  exact
    hlaw.V_affine_of_posteriorLawIntegral_mix
      F hax hV q hq t ht0 ht1
      (experimentOfChannel (publicMixChannel t ht0 ht1 P Q))
      (experimentOfChannel P)
      (experimentOfChannel Q)
      (by
        intro φ _hφ
        unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
        exact posteriorLawIntegral_publicMixChannel q t ht0 ht1 P Q φ)

/-- Data supplied by the internally proved finite affine
integral-representation construction.

It selects a test-function representation separately for each affine
posterior-law value.  It contains no support-face, relabelling, or cross-prior
coherence clause. Public-mixture affinity is already intrinsic data of
`PosteriorValueRepresentation`. -/
structure FinitePosteriorIntegralRepresentationData.{v} where
  representation :
    FinitePosteriorIntegralRepresentationAssumptions.{v}

/-- Posterior-law value affinity is intrinsic to the selected
`PosteriorValueRepresentation`; it is not another universally quantified
external HM premise. -/
theorem finitePosteriorLawValueAffine_of_HM
    (_hhm : FinitePosteriorIntegralRepresentationData.{u}) :
    FinitePosteriorLawValueAffineAssumptions.{u} :=
  finitePosteriorLawValueAffine_of_representation

/-- Extract the downstream integral-representation data. -/
noncomputable def finitePosteriorIntegralRepresentation_of_HM
    (hhm : FinitePosteriorIntegralRepresentationData.{u}) :
    FinitePosteriorIntegralRepresentationAssumptions.{u} :=
  hhm.representation

/-- The branch affine-linear-part package follows from the integral part of the
downstream construction package. -/
noncomputable def finiteAffineLinearPartAssumptions_of_HM
    (hhm : FinitePosteriorIntegralRepresentationData.{u}) :
    FiniteAffineLinearPartAssumptions.{u} :=
  finiteAffineLinearPartAssumptions_of_integralRepresentation
    hhm.representation

/-- Canonical outcome equivalence distributing product over a public-mix sum:
`((O ⊕ Z) × Y) ≃ ((O × Y) ⊕ (Z × Y))`. -/
def prodSumDistribEquiv (O Z Y : Type u) :
    ((O ⊕ Z) × Y) ≃ ((O × Y) ⊕ (Z × Y)) where
  toFun oy :=
    match oy.1 with
    | Sum.inl o => Sum.inl (o, oy.2)
    | Sum.inr z => Sum.inr (z, oy.2)
  invFun s :=
    match s with
    | Sum.inl oy => (Sum.inl oy.1, oy.2)
    | Sum.inr zy => (Sum.inr zy.1, zy.2)
  left_inv := by
    intro oy
    cases oy with
    | mk oz y =>
      cases oz <;> rfl
  right_inv := by
    intro s
    cases s with
    | inl oy =>
      cases oy
      rfl
    | inr zy =>
      cases zy
      rfl

@[simp]
theorem prodSumDistribEquiv_inl {O Z Y : Type u} (o : O) (y : Y) :
    prodSumDistribEquiv O Z Y (Sum.inl o, y) = Sum.inl (o, y) := rfl

@[simp]
theorem prodSumDistribEquiv_inr {O Z Y : Type u} (z : Z) (y : Y) :
    prodSumDistribEquiv O Z Y (Sum.inr z, y) = Sum.inr (z, y) := rfl

/-- Deterministic outcome kernel induced by an outcome equivalence.  This local
copy avoids importing the later Faddeev relabeling file into the upstream
entropy/cross-prior layer. -/
noncomputable def posteriorLawEquivKernel
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) : Channel O Y :=
  fun o => Dist.pure (e o)

@[simp]
theorem posteriorLawEquivKernel_apply
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (o : O) (y : Y) :
    posteriorLawEquivKernel e o y = if y = e o then 1 else 0 := rfl

/-- Postprocessing by a deterministic outcome equivalence simply relabels the
row probabilities. -/
theorem postprocess_posteriorLawEquivKernel_apply
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (P : Channel A O) (a : A) (y : Y) :
    Channel.postprocess P (posteriorLawEquivKernel e) a y = P a (e.symm y) := by
  change (∑ o : O, P a o * Dist.pure (e o) y) = P a (e.symm y)
  rw [Fintype.sum_eq_single (e.symm y)]
  · simp
  · intro o hone
    have hne : y ≠ e o := by
      intro hy
      apply hone
      exact e.injective (by simpa using hy.symm)
    simp [Dist.pure_apply_ne _ _ hne]

/-- Outcome marginals relabel under deterministic bijective postprocessing. -/
theorem outcomeMarginal_postprocess_posteriorLawEquivKernel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) (y : Y) :
    Channel.outcomeMarginal (Channel.postprocess P (posteriorLawEquivKernel e)) q y =
      Channel.outcomeMarginal P q (e.symm y) := by
  simp [Channel.outcomeMarginal_apply, postprocess_posteriorLawEquivKernel_apply]

/-- Posteriors relabel under deterministic bijective postprocessing. -/
theorem posterior_postprocess_posteriorLawEquivKernel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) (y : Y) :
    Channel.posterior (Channel.postprocess P (posteriorLawEquivKernel e)) q y =
      Channel.posterior P q (e.symm y) := by
  ext a
  unfold Channel.posterior
  simp [postprocess_posteriorLawEquivKernel_apply]

/-- Posterior-law integrals are invariant under deterministic bijective
postprocessing of outcomes. -/
theorem posteriorLawIntegral_postprocess_posteriorLawEquivKernel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) (φ : Dist A → ℝ) :
    posteriorLawIntegral q P φ =
      posteriorLawIntegral q (Channel.postprocess P (posteriorLawEquivKernel e)) φ := by
  unfold posteriorLawIntegral
  let f : O → ℝ := fun o =>
    Channel.outcomeMarginal P q o * φ (Channel.posterior P q o)
  let g : Y → ℝ := fun y =>
    Channel.outcomeMarginal (Channel.postprocess P (posteriorLawEquivKernel e)) q y *
      φ (Channel.posterior (Channel.postprocess P (posteriorLawEquivKernel e)) q y)
  change (∑ o : O, f o) = ∑ y : Y, g y
  exact Fintype.sum_equiv e f g (by
    intro o
    dsimp [f, g]
    simp [postprocess_posteriorLawEquivKernel_apply,
      posterior_postprocess_posteriorLawEquivKernel])

/-- Experiments have the same posterior law after deterministic bijective
postprocessing of outcomes. -/
theorem samePosteriorLawExp_of_bijective_postprocess
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) :
    SamePosteriorLawExp q
      (experimentOfChannel P)
      (experimentOfChannel (Channel.postprocess P (posteriorLawEquivKernel e))) := by
  intro φ _hφ
  unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
  exact posteriorLawIntegral_postprocess_posteriorLawEquivKernel q P e φ

/-- Deterministic outcome kernel induced by `prodSumDistribEquiv`. -/
noncomputable def prodSumDistribKernel
    {O Z Y : Type u} [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] :
    Channel ((O ⊕ Z) × Y) ((O × Y) ⊕ (Z × Y)) :=
  posteriorLawEquivKernel (prodSumDistribEquiv O Z Y)

theorem prodSumDistribKernel_eq_posteriorLawEquivKernel
    {O Z Y : Type u} [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] :
    prodSumDistribKernel (O := O) (Z := Z) (Y := Y) =
      posteriorLawEquivKernel (prodSumDistribEquiv O Z Y) := rfl

/--
At the channel level, taking a product with a fixed background channel commutes
with public mixing in the first coordinate, up to the canonical outcome
relabeling `prodSumDistribEquiv`.
-/
theorem prodChannel_publicMix_left_postprocess
    {A B O Z Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    [Fintype Y] [DecidableEq Y]
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Z) (R : Channel B Y) :
    Channel.postprocess
        (prodChannel (publicMixChannel t ht0 ht1 P Q) R)
        (prodSumDistribKernel (O := O) (Z := Z) (Y := Y)) =
      publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R) := by
  ext ab s
  rcases ab with ⟨a, b⟩
  cases s with
  | inl oy =>
    rcases oy with ⟨o, y⟩
    change
      (∑ oy' : (O ⊕ Z) × Y,
          (publicMixChannel t ht0 ht1 P Q a oy'.1 * R b oy'.2) *
            Dist.pure (prodSumDistribEquiv O Z Y oy') (Sum.inl (o, y))) =
        t * (P a o * R b y)
    rw [Fintype.sum_eq_single ((Sum.inl o : O ⊕ Z), y)]
    · simp [prodSumDistribEquiv, publicMixChannel]
      ring
    · intro oy' hoy'
      rcases oy' with ⟨oz, y'⟩
      by_cases hmap : prodSumDistribEquiv O Z Y (oz, y') = Sum.inl (o, y)
      · have hsource : (oz, y') = ((Sum.inl o : O ⊕ Z), y) := by
          cases oz with
          | inl o' =>
            simp only [prodSumDistribEquiv_inl, Sum.inl.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨ho, hy⟩
            subst ho
            subst hy
            rfl
          | inr z =>
            simp [prodSumDistribEquiv_inr] at hmap
        exact (hoy' hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquiv O Z Y (oz, y')) (Sum.inl (o, y)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]
  | inr zy =>
    rcases zy with ⟨z, y⟩
    change
      (∑ oy' : (O ⊕ Z) × Y,
          (publicMixChannel t ht0 ht1 P Q a oy'.1 * R b oy'.2) *
            Dist.pure (prodSumDistribEquiv O Z Y oy') (Sum.inr (z, y))) =
        (1 - t) * (Q a z * R b y)
    rw [Fintype.sum_eq_single ((Sum.inr z : O ⊕ Z), y)]
    · simp [prodSumDistribEquiv, publicMixChannel]
      ring
    · intro oy' hoy'
      rcases oy' with ⟨oz, y'⟩
      by_cases hmap : prodSumDistribEquiv O Z Y (oz, y') = Sum.inr (z, y)
      · have hsource : (oz, y') = ((Sum.inr z : O ⊕ Z), y) := by
          cases oz with
          | inl o =>
            simp [prodSumDistribEquiv_inl] at hmap
          | inr z' =>
            simp only [prodSumDistribEquiv_inr, Sum.inr.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨hz, hy⟩
            subst hz
            subst hy
            rfl
        exact (hoy' hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquiv O Z Y (oz, y')) (Sum.inr (z, y)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]

/--
Narrow posterior-law compatibility left after the channel-level equality:
posterior laws are unchanged by the canonical finite outcome relabeling that
identifies `prodChannel (publicMix P Q) R` with the public mixture of product
channels. This is structural channel/posterior-law content, not an economic
axiom.
-/
structure FiniteProductPublicMixPosteriorLawAssumptions.{v} where
  samePosteriorLaw_prod_publicMix_left :
    ∀ {A B O Z Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B)
      (R : Channel B Y)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R)))

theorem samePosteriorLaw_prod_publicMix_left_of_postprocess
    {A B O Z Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (R : Channel B Y)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Z) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) := by
  let PmixProd := prodChannel (publicMixChannel t ht0 ht1 P Q) R
  have hsame :
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel PmixProd)
        (experimentOfChannel
          (Channel.postprocess PmixProd
            (posteriorLawEquivKernel (prodSumDistribEquiv O Z Y)))) :=
    samePosteriorLawExp_of_bijective_postprocess
      (prodDist q r) PmixProd (prodSumDistribEquiv O Z Y)
  have hchan :
      Channel.postprocess PmixProd
          (posteriorLawEquivKernel (prodSumDistribEquiv O Z Y)) =
        publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R) := by
    simpa [PmixProd, prodSumDistribKernel_eq_posteriorLawEquivKernel] using
      (prodChannel_publicMix_left_postprocess
        (t := t) (ht0 := ht0) (ht1 := ht1) (P := P) (Q := Q) (R := R))
  simpa [PmixProd, hchan] using hsame

theorem productPublicMixPosteriorLaw_of_structural :
    FiniteProductPublicMixPosteriorLawAssumptions.{u} where
  samePosteriorLaw_prod_publicMix_left := by
    intro A B O Z Y _ _ _ _ _ _ _ _ _ _ _ _ q r R t ht0 ht1 P Q
    exact samePosteriorLaw_prod_publicMix_left_of_postprocess q r R t ht0 ht1 P Q

end TraceableAgency
