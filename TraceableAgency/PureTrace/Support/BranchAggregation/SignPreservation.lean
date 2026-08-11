/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.OneBranch

namespace TraceableAgency

universe u v

/-!
## Feasible branch-difference sign preservation

The tangent-space sign-preservation theorem needed for path independence is
stronger than A6 directly supplies: it talks about arbitrary signed
posterior-law directions.  A6 directly supplies the following feasible-channel
version, where the signed direction is the difference of two continuation
experiments and the aggregate experiments differ only in one branch.
-/

theorem linearPart_difference_pos_iff_value_gt
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    0 < hlin.linearPart F hV q (posteriorLawDifferenceExp q E E') ↔
      hV.V q E' < hV.V q E := by
  have hdiff := hlin.value_difference F hV q E E'
  constructor
  · intro hpos
    linarith
  · intro hgt
    linarith

theorem linearPart_difference_zero_iff_value_eq
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    hlin.linearPart F hV q (posteriorLawDifferenceExp q E E') = 0 ↔
      hV.V q E = hV.V q E' := by
  have hdiff := hlin.value_difference F hV q E E'
  constructor
  · intro hzero
    linarith
  · intro heq
    linarith

theorem linearPart_difference_swap_eq_neg
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    hlin.linearPart F hV q (posteriorLawDifferenceExp q E' E) =
      - hlin.linearPart F hV q (posteriorLawDifferenceExp q E E') := by
  rw [posteriorLawDifferenceExp_swap, hlin.linearPart_smul]
  ring

/-- A value gap between two experiments gives a nonzero affine-linear-part
witness in the corresponding signed posterior-law direction. -/
theorem branch_linear_part_nonzero_of_value_gap
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (E E' : FiniteExperimentOn A)
    (hgap : hV.V r E ≠ hV.V r E') :
    ∃ η : PosteriorLawSigned A,
      hlin.linearPart F hV r η ≠ 0 := by
  refine ⟨posteriorLawDifferenceExp r E E', ?_⟩
  intro hzero
  have hdiff := hlin.value_difference F hV r E E'
  have hVeq : hV.V r E = hV.V r E' := by
    linarith
  exact hgap hVeq

/-- Strict experiment-pair preference at a full-support prior forces a strict
gap in any posterior value representation. -/
theorem branch_value_ne_of_strict_experiment_pref
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (E₁ E₂ : FiniteExperimentOn A)
    (hpref : ExperimentPairPref F E₁ E₂ q q)
    (hnrev : ¬ ExperimentPairPref F E₂ E₁ q q) :
    hV.V q E₁ ≠ hV.V q E₂ := by
  intro heq
  have hge₂₁ : hV.V q E₂ ≥ hV.V q E₁ := by
    simp [heq]
  exact hnrev ((hV.represents_block_comparisons q hq E₂ E₁).mpr hge₂₁)

/-- A nondegenerate support witness rules out a subsingleton action type. -/
theorem not_subsingleton_of_dist_nondegenerate
    {A : Type u} [Fintype A] (r : Dist A)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ¬ Subsingleton A := by
  intro hsub
  rcases hr_nondegenerate with ⟨a, b, hab, _ha, _hb⟩
  exact hab (Subsingleton.elim a b)

/-- A1's strict full-revelation versus no-information comparison, transported
to the experiment-pair orientation used by posterior value representatives. -/
theorem branch_id_uninformativeU_experiment_strict_of_A1
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hnot_subsingleton : ¬ Subsingleton A) :
    ExperimentPairPref F
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      q q
    ∧
    ¬ ExperimentPairPref F
      (experimentOfChannel (Channel.uninformativeChannelU A))
      (experimentOfChannel (Channel.idChannel : Channel A A))
      q q := by
  classical
  haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
  have hstrict :=
    Relabeling.lifted_uninformative_strict_of_A1 F hax q hq
  constructor
  · change
      F.rel
        (blockChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A))
        (inlDist q) (inrDist q)
    exact hstrict.1
  · intro hrev
    change
      F.rel
        (blockChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel A A))
        (inlDist q) (inrDist q) at hrev
    have hrev_same :
        F.rel
          (blockChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU A))
          (inrDist q) (inlDist q) := by
      exact
        (Relabeling.block_swap_rel_of_axioms F hax
          (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A) q q).mpr hrev
    exact hstrict.2 hrev_same

/-- A1 and the value representation give a concrete value gap at every
full-support nondegenerate prior. -/
theorem branch_value_gap_of_A1
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ E E' : FiniteExperimentOn A,
      hV.V r E ≠ hV.V r E' := by
  have hnot_subsingleton : ¬ Subsingleton A :=
    not_subsingleton_of_dist_nondegenerate r hr_nondegenerate
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax r hr hnot_subsingleton
  refine ⟨experimentOfChannel (Channel.idChannel : Channel A A),
    experimentOfChannel (Channel.uninformativeChannelU A), ?_⟩
  exact branch_value_ne_of_strict_experiment_pref F hV r hr
    (experimentOfChannel (Channel.idChannel : Channel A A))
    (experimentOfChannel (Channel.uninformativeChannelU A))
    hstrict.1 hstrict.2

/-- A1 supplies the nonzero branch-linear-functional witness needed by the
same-sign scalar argument, once the affine linear part is available.

The theorem is deliberately `PureTraceConditions`-aware.  The legacy
`FiniteBranchLinearPartNonzeroAssumptions` below has no `PureTraceConditions` argument,
so it is stronger than what A1 can prove directly. -/
theorem branch_linear_part_nonzero_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ η : PosteriorLawSigned A, hlin.linearPart F hV r η ≠ 0 := by
  rcases branch_value_gap_of_A1 F hax hV r hr hr_nondegenerate with
    ⟨E, E', hgap⟩
  exact branch_linear_part_nonzero_of_value_gap hlin F hV r E E' hgap

/-- A1 supplies a nonzero branch-linear-functional witness inside the tangent
subspace. -/
theorem branch_linear_part_nonzero_tangent_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ η : PosteriorLawSigned A,
      PosteriorLawTangent η ∧ hlin.linearPart F hV r η ≠ 0 := by
  rcases branch_value_gap_of_A1 F hax hV r hr hr_nondegenerate with
    ⟨E, E', hgap⟩
  refine ⟨posteriorLawDifferenceExp r E E',
    posteriorLawDifferenceExp_tangent r E E', ?_⟩
  intro hzero
  have hdiff := hlin.value_difference F hV r E E'
  have hVeq : hV.V r E = hV.V r E' := by
    linarith
  exact hgap hVeq

theorem branch_linear_part_nonzero_atomicLinear_tangent_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (hr : r.FullSupport)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ (η : PosteriorLawSigned A) (_hatomic : PosteriorLawSigned.AtomicLinear η),
      PosteriorLawTangent η ∧ hlin.linearPart F hV r η ≠ 0 := by
  rcases branch_value_gap_of_A1 F hax hV r hr hr_nondegenerate with
    ⟨E, E', hgap⟩
  refine ⟨posteriorLawDifferenceExp r E E',
    posteriorLawDifferenceExp_atomicLinear r E E',
    posteriorLawDifferenceExp_tangent r E E', ?_⟩
  intro hzero
  have hdiff := hlin.value_difference F hV r E E'
  have hVeq : hV.V r E = hV.V r E' := by
    linarith
  exact hgap hVeq

theorem block_rel_of_channel_value_ge
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : Channel A Y)
    (hge :
      hV.V q (experimentOfChannel P) ≥
        hV.V q (experimentOfChannel Q)) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist q) := by
  have hpref :
      ExperimentPairPref F (experimentOfChannel P) (experimentOfChannel Q) q q :=
    (hV.represents_block_comparisons q hq _ _).mpr hge
  change F.rel (blockChannel P Q) (inlDist q) (inrDist q) at hpref
  exact hpref

theorem block_strictRel_of_channel_value_gt
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : Channel A Y)
    (hgt :
      hV.V q (experimentOfChannel Q) <
        hV.V q (experimentOfChannel P)) :
    F.strictRel (blockChannel P Q) (inlDist q) (inrDist q) := by
  constructor
  · exact block_rel_of_channel_value_ge F hV q hq P Q (le_of_lt hgt)
  · intro hrev
    have hswap :
        F.rel (blockChannel Q P) (inlDist q) (inrDist q) :=
      (Relabeling.block_swap_rel_of_axioms F hax P Q q q).mp hrev
    have hpref_rev :
        ExperimentPairPref F (experimentOfChannel Q) (experimentOfChannel P) q q := by
      change F.rel (blockChannel Q P) (inlDist q) (inrDist q)
      exact hswap
    have hge_rev :
        hV.V q (experimentOfChannel Q) ≥
          hV.V q (experimentOfChannel P) :=
      (hV.represents_block_comparisons q hq _ _).mp hpref_rev
    linarith

theorem branch_feasible_difference_pos_of_branch_pos
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o))
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (hr : (branchPosterior P₁ q target).FullSupport)
    (hbranch_pos :
      0 < hlin.linearPart F hV (branchPosterior P₁ q target)
        (posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target)))) :
    0 < hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R))) := by
  have hbranch_gt :
      hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (R target)) <
        hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (Q target)) :=
    (linearPart_difference_pos_iff_value_gt hlin F hV
      (branchPosterior P₁ q target)
      (experimentOfChannel (Q target))
      (experimentOfChannel (R target))).mp hbranch_pos
  have htarget_weak :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_rel_of_channel_value_ge F hV
      (branchPosterior P₁ q target) hr (Q target) (R target)
      (le_of_lt hbranch_gt)
  have htarget_strict :
      F.strictRel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_strictRel_of_channel_value_gt F hax hV
      (branchPosterior P₁ q target) hr (Q target) (R target)
      hbranch_gt
  have hagg_strict :
      F.strictRel
        (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
        (inlDist q) (inrDist q) :=
    A6_strict_one_branch_of_strict F hax O₂ q P₁ Q R target hpos hsame
      htarget_weak htarget_strict
  have hagg_gt :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) <
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) := by
    have hpref :
        ExperimentPairPref F
          (experimentOfChannel (seqComposeDep P₁ O₂ Q))
          (experimentOfChannel (seqComposeDep P₁ O₂ R)) q q := by
      change F.rel
        (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
        (inlDist q) (inrDist q)
      exact hagg_strict.1
    have hge :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) ≥
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) :=
      (hV.represents_block_comparisons q hq _ _).mp hpref
    by_contra hnot_gt
    have hge_rev :
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) ≥
          hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) :=
      le_of_not_gt hnot_gt
    have hpref_rev :
        ExperimentPairPref F
          (experimentOfChannel (seqComposeDep P₁ O₂ R))
          (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q :=
      (hV.represents_block_comparisons q hq _ _).mpr hge_rev
    have hrel_rev :
        F.rel
          (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q))
          (inlDist q) (inrDist q) := by
      exact hpref_rev
    have hrel_rev_same :
        F.rel
          (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
          (inrDist q) (inlDist q) :=
      (Relabeling.block_swap_rel_of_axioms F hax
        (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R) q q).mpr hrel_rev
    exact hagg_strict.2 hrel_rev_same
  exact (linearPart_difference_pos_iff_value_gt hlin F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q))
    (experimentOfChannel (seqComposeDep P₁ O₂ R))).mpr hagg_gt

theorem branch_feasible_difference_zero_of_branch_zero
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o))
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (hr : (branchPosterior P₁ q target).FullSupport)
    (hbranch_zero :
      hlin.linearPart F hV (branchPosterior P₁ q target)
        (posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target))) = 0) :
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R))) = 0 := by
  have hbranch_eq :
      hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (Q target)) =
        hV.V (branchPosterior P₁ q target)
          (experimentOfChannel (R target)) :=
    (linearPart_difference_zero_iff_value_eq hlin F hV
      (branchPosterior P₁ q target)
      (experimentOfChannel (Q target))
      (experimentOfChannel (R target))).mp hbranch_zero
  have htarget_QR :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_rel_of_channel_value_ge F hV
      (branchPosterior P₁ q target) hr (Q target) (R target) (by
        rw [hbranch_eq])
  have htarget_RQ :
      F.rel (blockChannel (R target) (Q target))
        (inlDist (branchPosterior P₁ q target))
        (inrDist (branchPosterior P₁ q target)) :=
    block_rel_of_channel_value_ge F hV
      (branchPosterior P₁ q target) hr (R target) (Q target) (by
        rw [hbranch_eq])
  have hagg_QR :
      F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
        (inlDist q) (inrDist q) :=
    A6_weak_one_branch_of_rel F hax O₂ q P₁ Q R target hsame htarget_QR
  have hagg_RQ :
      F.rel (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q))
        (inlDist q) (inrDist q) :=
    A6_weak_one_branch_of_rel F hax O₂ q P₁ R Q target
      (fun o ho => (hsame o ho).symm) htarget_RQ
  have hpref_QR :
      ExperimentPairPref F
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R)) q q := by
    change F.rel
      (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R))
      (inlDist q) (inrDist q)
    exact hagg_QR
  have hpref_RQ :
      ExperimentPairPref F
        (experimentOfChannel (seqComposeDep P₁ O₂ R))
        (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q := by
    change F.rel
      (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q))
      (inlDist q) (inrDist q)
    exact hagg_RQ
  have hge_QR :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) ≥
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) :=
    (hV.represents_block_comparisons q hq _ _).mp hpref_QR
  have hge_RQ :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) ≥
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) :=
    (hV.represents_block_comparisons q hq _ _).mp hpref_RQ
  have hagg_eq :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) :=
    le_antisymm hge_RQ hge_QR
  exact (linearPart_difference_zero_iff_value_eq hlin F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q))
    (experimentOfChannel (seqComposeDep P₁ O₂ R))).mpr hagg_eq

/-- If two dependent continuation profiles differ only in one branch, then the
signed posterior-law difference of the compound experiments is the branch
probability times the signed posterior-law difference in that branch. -/
theorem posteriorLawDifference_seqComposeDep_one_branch
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o)) (target : O₁)
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp q
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel (seqComposeDep P₁ O₂ R)) φ =
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target)) φ := by
  classical
  unfold posteriorLawDifferenceExp
  change
    posteriorLawIntegral q (seqComposeDep P₁ O₂ Q) φ -
      posteriorLawIntegral q (seqComposeDep P₁ O₂ R) φ =
      (Channel.outcomeMarginal P₁ q) target *
        (posteriorLawIntegral (branchPosterior P₁ q target) (Q target) φ -
          posteriorLawIntegral (branchPosterior P₁ q target) (R target) φ)
  rw [posteriorLawIntegral_seqComposeDep_eq_sum q P₁ O₂ Q φ,
    posteriorLawIntegral_seqComposeDep_eq_sum q P₁ O₂ R φ]
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ x : O₁,
        ((Channel.outcomeMarginal P₁ q) x *
            posteriorLawIntegral (Channel.posterior P₁ q x) (Q x) φ -
          (Channel.outcomeMarginal P₁ q) x *
            posteriorLawIntegral (Channel.posterior P₁ q x) (R x) φ))
        =
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawIntegral (Channel.posterior P₁ q target) (Q target) φ -
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawIntegral (Channel.posterior P₁ q target) (R target) φ := by
        refine Finset.sum_eq_single target ?_ ?_
        · intro o _ho hne
          rw [hsame o hne]
          ring
        · intro hnot
          exact absurd (Finset.mem_univ target) hnot
    _ =
      (Channel.outcomeMarginal P₁ q) target *
        (posteriorLawIntegral (Channel.posterior P₁ q target) (Q target) φ -
          posteriorLawIntegral (Channel.posterior P₁ q target) (R target) φ) := by
        ring
    _ =
      (Channel.outcomeMarginal P₁ q) target *
        posteriorLawDifferenceExp (branchPosterior P₁ q target)
          (experimentOfChannel (Q target))
          (experimentOfChannel (R target)) φ := by
        rfl

/-- The signed posterior-law difference between a dependent sequential
experiment and its first-stage experiment is the sum of the branch
probabilities times the continuation posterior-law differences from the
no-information branch baseline. -/
theorem posteriorLawDifference_seqComposeDep_eq_sum_branch_differences
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q : ∀ o, Channel A (O₂ o)) (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp q
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel P₁) φ =
      posteriorLawSignedSum (fun o : O₁ =>
        posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
          (posteriorLawDifferenceExp (branchPosterior P₁ q o)
            (experimentOfChannel (Q o))
            (experimentOfChannel (Channel.uninformativeChannelU A)))) φ := by
  classical
  unfold posteriorLawDifferenceExp posteriorLawSignedSum
    posteriorLawSignedFinsetSum posteriorLawSignedSMul
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegral_seqComposeDep_eq_sum q P₁ O₂ Q φ]
  unfold posteriorLawIntegral
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro o _ho
  dsimp
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior]
  simp [posteriorLawIntegral, branchPosterior]
  ring_nf

/-- Outcome marginal of the public fixed-output sequential composition. -/
theorem outcomeMarginal_seqCompose_apply
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (o : O₁ × O₂) :
    (Channel.outcomeMarginal (P₁ ▷ Q) q) o =
      (Channel.outcomeMarginal P₁ q) o.1 *
        (Channel.outcomeMarginal (Q o.1) (Channel.posterior P₁ q o.1)) o.2 := by
  classical
  obtain ⟨o₁, o₂⟩ := o
  simp only [Channel.outcomeMarginal_apply]
  have step0 :
      ∑ a, q a * (P₁ ▷ Q) a (o₁, o₂) =
        ∑ a, q a * (P₁ a o₁ * Q o₁ a o₂) := by
    refine Finset.sum_congr rfl ?_
    intro a _ha
    rw [seqCompose_apply]
  rw [step0]
  have step1 :
      ∑ a, q a * (P₁ a o₁ * Q o₁ a o₂) =
        ∑ a, (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.posterior P₁ q o₁) a * Q o₁ a o₂) := by
    congr 1
    ext a
    have h := posterior_mul_marginal q P₁ o₁ a
    calc
      q a * (P₁ a o₁ * Q o₁ a o₂)
          = (q a * P₁ a o₁) * Q o₁ a o₂ := by ring
      _ = ((Channel.outcomeMarginal P₁ q) o₁ *
            (Channel.posterior P₁ q o₁) a) * Q o₁ a o₂ := by
            rw [h]
      _ = (Channel.outcomeMarginal P₁ q) o₁ *
            ((Channel.posterior P₁ q o₁) a * Q o₁ a o₂) := by ring
  rw [step1, ← Finset.mul_sum]
  simp only [Channel.outcomeMarginal_apply]

/-- Positive fixed-output sequential outcomes have the posterior of the
selected continuation branch. -/
theorem posterior_seqCompose_of_pos
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (o₁ : O₁) (o₂ : O₂)
    (hpos : (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) > 0) :
    Channel.posterior (P₁ ▷ Q) q (o₁, o₂) =
      Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂ := by
  classical
  have hmarg := outcomeMarginal_seqCompose_apply q P₁ Q (o₁, o₂)
  have hprod :
      (Channel.outcomeMarginal P₁ q) o₁ *
          (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ > 0 := by
    rw [hmarg] at hpos
    exact hpos
  have hm₁_nonneg : 0 ≤ (Channel.outcomeMarginal P₁ q) o₁ :=
    (Channel.outcomeMarginal P₁ q).nonneg o₁
  have hm₂_nonneg :
      0 ≤ (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ :=
    (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)).nonneg o₂
  have hm₁_pos : (Channel.outcomeMarginal P₁ q) o₁ > 0 := by nlinarith
  have hm₂_pos :
      (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ > 0 := by
    nlinarith
  ext a
  let mC := (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂)
  let m₁ := (Channel.outcomeMarginal P₁ q) o₁
  let m₂ := (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂
  let pC := Channel.posterior (P₁ ▷ Q) q (o₁, o₂)
  let p₁ := Channel.posterior P₁ q o₁
  let p₂ := Channel.posterior (Q o₁) p₁ o₂
  have hleft := posterior_mul_marginal q (P₁ ▷ Q) (o₁, o₂) a
  have hfirst := posterior_mul_marginal q P₁ o₁ a
  have hsecond := posterior_mul_marginal p₁ (Q o₁) o₂ a
  have hmarg' : mC = m₁ * m₂ := by
    simpa [mC, m₁, m₂] using hmarg
  have hcalc : mC * pC a = mC * p₂ a := by
    calc
      mC * pC a
          = q a * (P₁ ▷ Q) a (o₁, o₂) := hleft
      _ = q a * (P₁ a o₁ * Q o₁ a o₂) := by rw [seqCompose_apply]
      _ = (q a * P₁ a o₁) * Q o₁ a o₂ := by ring
      _ = (m₁ * p₁ a) * Q o₁ a o₂ := by rw [← hfirst]
      _ = m₁ * (p₁ a * Q o₁ a o₂) := by ring
      _ = m₁ * (m₂ * p₂ a) := by rw [← hsecond]
      _ = (m₁ * m₂) * p₂ a := by ring
      _ = mC * p₂ a := by rw [hmarg']
  exact mul_left_cancel₀ (ne_of_gt hpos) hcalc

/-- Public fixed-output posterior law of a sequential composition is the
first-stage marginal mixture of the branch posterior laws. -/
theorem posteriorLawIntegral_seqCompose_eq_sum
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (φ : Dist A → ℝ) :
    posteriorLawIntegral q (P₁ ▷ Q) φ =
      ∑ o₁,
        (Channel.outcomeMarginal P₁ q) o₁ *
          posteriorLawIntegral (Channel.posterior P₁ q o₁) (Q o₁) φ := by
  classical
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  congr 1
  ext o₁
  rw [Finset.mul_sum]
  congr 1
  ext o₂
  have hmarg := outcomeMarginal_seqCompose_apply q P₁ Q (o₁, o₂)
  by_cases hpos : (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) > 0
  · have hpost := posterior_seqCompose_of_pos q P₁ Q o₁ o₂ hpos
    calc
      (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) *
          φ (Channel.posterior (P₁ ▷ Q) q (o₁, o₂))
          =
        ((Channel.outcomeMarginal P₁ q) o₁ *
          (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂) *
          φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂) := by
            rw [hpost, hmarg]
      _ =
        (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ *
            φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂)) := by
            ring
  · have hzero :
      (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) = 0 := by
      exact le_antisymm (le_of_not_gt hpos)
        ((Channel.outcomeMarginal (P₁ ▷ Q) q).nonneg (o₁, o₂))
    have hprod :
        (Channel.outcomeMarginal P₁ q) o₁ *
            (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ = 0 := by
      rw [hmarg] at hzero
      exact hzero
    calc
      (Channel.outcomeMarginal (P₁ ▷ Q) q) (o₁, o₂) *
          φ (Channel.posterior (P₁ ▷ Q) q (o₁, o₂))
          = 0 := by rw [hzero, zero_mul]
      _ =
        (Channel.outcomeMarginal P₁ q) o₁ *
          ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ *
            φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂)) := by
            calc
              0 = ((Channel.outcomeMarginal P₁ q) o₁ *
                    (Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂) *
                    φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂) := by
                    rw [hprod, zero_mul]
              _ =
                  (Channel.outcomeMarginal P₁ q) o₁ *
                    ((Channel.outcomeMarginal (Q o₁) (Channel.posterior P₁ q o₁)) o₂ *
                      φ (Channel.posterior (Q o₁) (Channel.posterior P₁ q o₁) o₂)) := by
                    ring

/-- Fixed-output version of the sequential posterior-law difference branch
sum identity. -/
theorem posteriorLawDifference_seqCompose_eq_sum_branch_differences
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp q
      (experimentOfChannel (P₁ ▷ Q))
      (experimentOfChannel P₁) φ =
      posteriorLawSignedSum (fun o : O₁ =>
        posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
          (posteriorLawDifferenceExp (branchPosterior P₁ q o)
            (experimentOfChannel (Q o))
            (experimentOfChannel (Channel.uninformativeChannelU A)))) φ := by
  classical
  unfold posteriorLawDifferenceExp posteriorLawSignedSum
    posteriorLawSignedFinsetSum posteriorLawSignedSMul
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegral_seqCompose_eq_sum q P₁ Q φ]
  unfold posteriorLawIntegral
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro o _ho
  dsimp
  rw [posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior]
  simp [posteriorLawIntegral, branchPosterior]
  ring_nf

/-- Fixed-outcome posterior-law algebra interface for the branch formula.

The dependent sequential algebra is proved internally above.  The public branch
formula is stated for the uniform-outcome `P₁ ▷ Q`, whose outcome type is
`O₁ × O₂`; transporting the dependent sigma-outcome identity to this product
presentation is a pure finite probability/relabeling step, not a behavioral
axiom. -/
structure FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions : Prop where
  posteriorLawDifference_seqCompose_eq_sum_branch_differences :
    ∀ {A O₁ O₂ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂)
      (φ : Dist A → ℝ),
      posteriorLawDifferenceExp q
        (experimentOfChannel (P₁ ▷ Q))
        (experimentOfChannel P₁) φ =
        posteriorLawSignedSum (fun o : O₁ =>
          posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A)))) φ

/-- The fixed-output posterior-law algebra is internal finite channel
algebra. -/
theorem fixedOutcomePosteriorAlgebra_of_finite :
    FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions.{u} where
  posteriorLawDifference_seqCompose_eq_sum_branch_differences := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q P₁ Q φ
    exact posteriorLawDifference_seqCompose_eq_sum_branch_differences q P₁ Q φ

/-- Affine expansion of the dependent sequential value difference. -/
theorem branch_formula_affine_expansion_seqComposeDep
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q : ∀ o, Channel A (O₂ o)) :
    hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) -
      hV.V q (experimentOfChannel P₁) =
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel P₁)) :=
  hlin.value_difference F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q))
    (experimentOfChannel P₁)

/-- Affine expansion of the public fixed-output sequential value difference. -/
theorem branch_formula_affine_expansion_seqCompose
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂) :
    hV.V q (experimentOfChannel (P₁ ▷ Q)) -
      hV.V q (experimentOfChannel P₁) =
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (P₁ ▷ Q))
        (experimentOfChannel P₁)) :=
  hlin.value_difference F hV q
    (experimentOfChannel (P₁ ▷ Q))
    (experimentOfChannel P₁)

/-- Linear-part expansion of the dependent sequential branch difference as a
sum of branch continuation differences from the no-information baseline. -/
theorem branch_formula_linearPart_seqComposeDep_sum
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (P₁ : Channel A O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q : ∀ o, Channel A (O₂ o)) :
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel P₁)) =
      ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
  classical
  let branchTerm : O₁ → PosteriorLawSigned A := fun o =>
    posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
      (posteriorLawDifferenceExp (branchPosterior P₁ q o)
        (experimentOfChannel (Q o))
        (experimentOfChannel (Channel.uninformativeChannelU A)))
  have hdiff :
      ∀ φ : Dist A → ℝ,
        posteriorLawDifferenceExp q
          (experimentOfChannel (seqComposeDep P₁ O₂ Q))
          (experimentOfChannel P₁) φ =
        posteriorLawSignedSum branchTerm φ := by
    intro φ
    exact posteriorLawDifference_seqComposeDep_eq_sum_branch_differences
      q P₁ O₂ Q φ
  calc
    hlin.linearPart F hV q
        (posteriorLawDifferenceExp q
          (experimentOfChannel (seqComposeDep P₁ O₂ Q))
          (experimentOfChannel P₁))
        =
      hlin.linearPart F hV q (posteriorLawSignedSum branchTerm) :=
        hlin.linearPart_ext F hV q _ _ hdiff
    _ = ∑ o : O₁, hlin.linearPart F hV q (branchTerm o) := by
        rw [linearPart_sum hlin F hV q branchTerm]
    _ = ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
        apply Finset.sum_congr rfl
        intro o _ho
        simp [branchTerm, hlin.linearPart_smul]

/-- Linear-part expansion of the public fixed-output branch difference as a
sum of branch continuation differences from the no-information baseline. -/
theorem branch_formula_linearPart_seqCompose_sum
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
    (q : Dist A) (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂) :
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (P₁ ▷ Q))
        (experimentOfChannel P₁)) =
      ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
  classical
  let branchTerm : O₁ → PosteriorLawSigned A := fun o =>
    posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) o)
      (posteriorLawDifferenceExp (branchPosterior P₁ q o)
        (experimentOfChannel (Q o))
        (experimentOfChannel (Channel.uninformativeChannelU A)))
  have hdiff :
      ∀ φ : Dist A → ℝ,
        posteriorLawDifferenceExp q
          (experimentOfChannel (P₁ ▷ Q))
          (experimentOfChannel P₁) φ =
        posteriorLawSignedSum branchTerm φ := by
    intro φ
    exact posteriorLawDifference_seqCompose_eq_sum_branch_differences
      q P₁ Q φ
  calc
    hlin.linearPart F hV q
        (posteriorLawDifferenceExp q
          (experimentOfChannel (P₁ ▷ Q))
          (experimentOfChannel P₁))
        =
      hlin.linearPart F hV q (posteriorLawSignedSum branchTerm) :=
        hlin.linearPart_ext F hV q _ _ hdiff
    _ = ∑ o : O₁, hlin.linearPart F hV q (branchTerm o) := by
        rw [linearPart_sum hlin F hV q branchTerm]
    _ = ∑ o : O₁,
        (Channel.outcomeMarginal P₁ q) o *
          hlin.linearPart F hV q
            (posteriorLawDifferenceExp (branchPosterior P₁ q o)
              (experimentOfChannel (Q o))
              (experimentOfChannel (Channel.uninformativeChannelU A))) := by
        apply Finset.sum_congr rfl
        intro o _ho
        simp [branchTerm, hlin.linearPart_smul]

/-- Forward and zero sign transport for a common-outcome feasible branch
direction.

This is the compiled A6/posterior-law-realization core of tangent sign
agreement: if a signed branch direction `η` is a positive scalar multiple of a
common-outcome feasible difference at a reached posterior `r`, then positive
and zero branch-linear signs transport to the aggregate prior `q`.  The reverse
positive direction is left to the full tangent sign-agreement interface; it
uses the same argument applied to the swapped direction. -/
theorem branch_tangent_forward_zero_of_commonOutcome_realization
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A O O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype O₁] [DecidableEq O₁]
    (q r : Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (η : PosteriorLawSigned A) (t : ℝ) (ht : 0 < t)
    (P R : Channel A O)
    (hη :
      ∀ φ : Dist A → ℝ,
        η φ =
          t * posteriorLawDifferenceExp r
            (experimentOfChannel P) (experimentOfChannel R) φ)
    (P₁ : Channel A O₁) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (hpost : branchPosterior P₁ q target = r) :
    (0 < hlin.linearPart F hV r η →
      0 < hlin.linearPart F hV q η) ∧
    (hlin.linearPart F hV r η = 0 →
      hlin.linearPart F hV q η = 0) := by
  classical
  let O₂ : O₁ → Type u := fun _ => O
  let Q : ∀ o, Channel A (O₂ o) := fun o =>
    if o = target then P else P
  let S : ∀ o, Channel A (O₂ o) := fun o =>
    if o = target then R else P
  let branchDiff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r
      (experimentOfChannel P) (experimentOfChannel R)
  let seqDiff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp q
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel (seqComposeDep P₁ O₂ S))
  have hsame : ∀ o, o ≠ target → Q o = S o := by
    intro o ho
    simp [Q, S, ho]
  have hbranch_full : (branchPosterior P₁ q target).FullSupport := by
    simpa [hpost] using hr
  have hη_eq : η = posteriorLawSignedSMul t branchDiff := by
    funext φ
    exact hη φ
  have hη_lin_r :
      hlin.linearPart F hV r η =
        t * hlin.linearPart F hV r branchDiff := by
    rw [hη_eq, hlin.linearPart_smul]
  have hη_lin_q :
      hlin.linearPart F hV q η =
        t * hlin.linearPart F hV q branchDiff := by
    rw [hη_eq, hlin.linearPart_smul]
  have hseq_eq :
      seqDiff =
        posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
          branchDiff := by
    funext φ
    have h :=
      posteriorLawDifference_seqComposeDep_one_branch
        q P₁ O₂ Q S target hsame φ
    simpa [seqDiff, branchDiff, Q, S, hpost, posteriorLawSignedSMul] using h
  have hseq_lin_q :
      hlin.linearPart F hV q seqDiff =
        (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff := by
    rw [hseq_eq, hlin.linearPart_smul]
  have htargetQ :
      Q target = P := by
    simp [Q]
  have htargetS :
      S target = R := by
    simp [S]
  have hbranch_pos_to_q_pos :
      0 < hlin.linearPart F hV r branchDiff →
        0 < hlin.linearPart F hV q branchDiff := by
    intro hbpos
    have hbpos_target :
        0 < hlin.linearPart F hV (branchPosterior P₁ q target)
          (posteriorLawDifferenceExp (branchPosterior P₁ q target)
            (experimentOfChannel (Q target))
            (experimentOfChannel (S target))) := by
      simpa [branchDiff, hpost, htargetQ, htargetS] using hbpos
    have hseq_pos :
        0 < hlin.linearPart F hV q seqDiff := by
      simpa [seqDiff] using
        (branch_feasible_difference_pos_of_branch_pos
          hlin F hax hV q hq P₁ target hpos O₂ Q S hsame
          hbranch_full hbpos_target)
    have hmpos : 0 < (Channel.outcomeMarginal P₁ q) target := hpos
    have hmul :
        0 < (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff := by
      simpa [hseq_lin_q] using hseq_pos
    nlinarith [hmpos, hmul]
  have hbranch_zero_to_q_zero :
      hlin.linearPart F hV r branchDiff = 0 →
        hlin.linearPart F hV q branchDiff = 0 := by
    intro hbzero
    have hbzero_target :
        hlin.linearPart F hV (branchPosterior P₁ q target)
          (posteriorLawDifferenceExp (branchPosterior P₁ q target)
            (experimentOfChannel (Q target))
            (experimentOfChannel (S target))) = 0 := by
      simpa [branchDiff, hpost, htargetQ, htargetS] using hbzero
    have hseq_zero :
        hlin.linearPart F hV q seqDiff = 0 := by
      simpa [seqDiff] using
        (branch_feasible_difference_zero_of_branch_zero
          hlin F hax hV q hq P₁ target O₂ Q S hsame
          hbranch_full hbzero_target)
    have hmne : (Channel.outcomeMarginal P₁ q) target ≠ 0 := ne_of_gt hpos
    have hmul :
        (Channel.outcomeMarginal P₁ q) target *
          hlin.linearPart F hV q branchDiff = 0 := by
      simpa [hseq_lin_q] using hseq_zero
    exact (mul_eq_zero.mp hmul).resolve_left hmne
  constructor
  · intro hrη_pos
    have hbpos : 0 < hlin.linearPart F hV r branchDiff := by
      nlinarith [hη_lin_r, ht, hrη_pos]
    have hqpos := hbranch_pos_to_q_pos hbpos
    nlinarith [hη_lin_q, ht, hqpos]
  · intro hrη_zero
    have hbzero : hlin.linearPart F hV r branchDiff = 0 := by
      nlinarith [hη_lin_r, ht, hrη_zero]
    have hqzero := hbranch_zero_to_q_zero hbzero
    nlinarith [hη_lin_q, ht, hqzero]

end TraceableAgency
