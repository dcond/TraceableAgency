/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.AffineLinear

namespace TraceableAgency

universe u v

/-!
## One-branch A6 plumbing

These lemmas do not prove the branch-slice affine theorem.  They isolate the
pure A6/A3/A1 step: if two continuation profiles differ in one branch only,
then the branch comparison lifts to the aggregate comparison.
-/

/-- A1 gives reflexivity of the preference relation for a fixed channel. -/
theorem rel_refl_of_A1
    (F : PrefFamily.{u}) (hA1 : PureTraceWeakOrderAndNontriviality F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel P q q := by
  exact (hA1.1 P).1 q q |>.elim id id

/-- Identical branches are weakly comparable in the duplicated block
environment, by A3 plus A1 reflexivity. -/
theorem block_duplicate_rel_refl_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel (blockChannel P P) (inlDist q) (inrDist q) := by
  exact (hax.blockCoherence.duplication P q q).mp (rel_refl_of_A1 F hax.weakOrder P q)

/-- Weak one-branch A6 specialization.  All non-target branches are identical,
so their weak comparisons are supplied by `block_duplicate_rel_refl_of_axioms`.
-/
theorem A6_weak_one_branch_of_rel
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q R : ∀ o, Channel A (O₂ o)) (target : O₁)
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (htarget :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target))) :
    F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q) := by
  exact hax.branchContinuation.1 O₂ q P₁ Q R (fun o _hpos => by
    by_cases ho : o = target
    · subst ho
      exact htarget
    · rw [hsame o ho]
      exact block_duplicate_rel_refl_of_axioms F hax (R o) (branchPosterior P₁ q o))

/-- Strict one-branch A6 specialization.  The target branch is strictly better,
and all non-target branches are identical. -/
theorem A6_strict_one_branch_of_strict
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (q : Dist A) (P₁ : Channel A O₁)
    (Q R : ∀ o, Channel A (O₂ o)) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (htarget_weak :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)))
    (htarget_strict :
      F.strictRel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target))) :
    F.strictRel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q) := by
  exact hax.branchContinuation.2 O₂ q P₁ Q R
    (fun o _hpos => by
      by_cases ho : o = target
      · subst ho
        exact htarget_weak
      · rw [hsame o ho]
        exact block_duplicate_rel_refl_of_axioms F hax (R o) (branchPosterior P₁ q o))
    ⟨target, hpos, htarget_strict⟩

end TraceableAgency
