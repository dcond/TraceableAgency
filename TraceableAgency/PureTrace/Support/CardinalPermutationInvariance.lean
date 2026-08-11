/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.SelectedRelabeling

/-!
# Selected Cardinal Permutation Invariance

This file isolates the selected-representative cardinal relabeling proof into
the two named TeX steps: actionbase scalar and permutation-invariance scalar
pinning.  The composition theorem proves the repaired selected relabeling
target from those two strictly earlier obligations.
-/

namespace TraceableAgency

universe u

/--
Selected actionbase scalar theorem.

For the coherent face-scale representative, action/outcome relabeling is a
positive scalar multiple of the original value.  This is the cardinal content
left by order-level relabeling plus HM/affine uniqueness before product
normalization pins the scalar.
-/
structure FiniteSelectedActionbaseScalarFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  relabel_scalar :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (eA : A ≃ B) (q : Dist A),
      ∃ c : ℝ, 0 < c ∧
        ∀ {O Y : Type v}
          [Fintype O] [DecidableEq O]
          [Fintype Y] [DecidableEq Y]
          (eO : O ≃ Y) (P : Channel A O),
          hfaces.branch_result.branch_agg.value_rep.V
              (Relabeling.relabelDist eA q)
              (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
            c *
              hfaces.branch_result.branch_agg.value_rep.V q
                (experimentOfChannel P)

/--
Selected permutation-invariance scalar pinning.

This is the TeX product-normalization step: any scalar supplied by
`FiniteSelectedActionbaseScalarFor` must equal one.  Its proof obligation is
strictly weaker than old all-representatives value relabeling because it only
talks about scalars already obtained for the selected coherent representative.
-/
structure FiniteSelectedPermutationInvariancePinningFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  scalar_eq_one :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (eA : A ≃ B) (q : Dist A)
      (c : ℝ) (_hc : 0 < c),
      (∀ {O Y : Type v}
          [Fintype O] [DecidableEq O]
          [Fintype Y] [DecidableEq Y]
          (eO : O ≃ Y) (P : Channel A O),
          hfaces.branch_result.branch_agg.value_rep.V
              (Relabeling.relabelDist eA q)
              (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
            c *
              hfaces.branch_result.branch_agg.value_rep.V q
                (experimentOfChannel P)) →
        c = 1

/--
Selected exact value relabeling from the TeX actionbase scalar theorem plus
permutation-invariance scalar pinning.
-/
theorem finiteSelectedPosteriorValueRelabeling_of_actionbase_permutationinvariance
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haction : FiniteSelectedActionbaseScalarFor hfaces)
    (hpin : FiniteSelectedPermutationInvariancePinningFor hfaces) :
    FiniteSelectedPosteriorValueRelabelingFor hfaces where
  V_relabel_eq := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    rcases haction.relabel_scalar hax eA q with ⟨c, hc, hscalar⟩
    have hc1 : c = 1 :=
      hpin.scalar_eq_one hax eA q c hc hscalar
    have h := hscalar eO P
    simpa [hc1] using h

end TraceableAgency
