/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence

/-!
# Selected Representative Relabeling

This file separates the paper-level value-relabeling target for the selected
coherent face-scale representatives from the older, stronger target over every
bare `PosteriorValueRepresentation`.
-/

namespace TraceableAgency

universe u

/--
Exact action/outcome relabeling for the selected posterior-value
representative carried by a `CoherentRelabelingFaceScalesStructure`.

This is strictly weaker than `FinitePosteriorValueRelabelingAssumptions`: it
does not quantify over arbitrary bare representatives.
-/
structure FiniteSelectedPosteriorValueRelabelingFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  V_relabel_eq :
    ∀ (_hax : PureTraceConditions F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (eA : A ≃ B) (eO : O ≃ Y)
      (q : Dist A) (P : Channel A O),
      hfaces.branch_result.branch_agg.value_rep.V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P)

/--
The old all-representatives relabeling input implies the repaired selected
target.  This is only a compatibility bridge; it is not the non-circular paper
proof of selected cardinal relabeling.
-/
theorem selectedPosteriorValueRelabeling_of_valueRelabeling
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u}) :
    FiniteSelectedPosteriorValueRelabelingFor hfaces where
  V_relabel_eq := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    exact hrelV.V_relabel_eq F hax
      hfaces.branch_result.branch_agg.value_rep eA eO q P

/-- Projection form of selected exact relabeling. -/
theorem exactSelectedRelabelingInvariance
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) :
    hfaces.branch_result.branch_agg.value_rep.V
        (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel P) :=
  hsel.V_relabel_eq hax eA eO q P

/--
Full-revelation value `H` is invariant under action relabeling, using only the
selected representative relabeling package.
-/
theorem fullRevelationValueForFaceScales_relabel_eq_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) :
    fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) =
      fullRevelationValueForFaceScales hfaces q := by
  have hrel :=
    hsel.V_relabel_eq hax e e q (Channel.idChannel : Channel A A)
  have hid :
      Relabeling.relabelChannel e e (Channel.idChannel : Channel A A) =
        (Channel.idChannel : Channel B B) := by
    funext b
    ext b'
    rw [Relabeling.relabelChannel_apply]
    simp only [Channel.idChannel]
    by_cases hbb : b' = b
    · subst hbb
      rw [Dist.pure_apply_self, Dist.pure_apply_self]
    · rw [Dist.pure_apply_ne (e.symm b) (e.symm b')
          (fun h => hbb (e.symm.injective h)),
        Dist.pure_apply_ne b b' hbb]
  rw [hid] at hrel
  simpa [fullRevelationValueForFaceScales] using hrel

/--
Triple-product value associativity from the selected representative relabeling
target and the structural product associator facts.
-/
theorem faceScaleTripleProductValueAssociativity_of_selectedRelabeling
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces) :
    FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces where
  triple_value_assoc := by
    intro hax A B C O Y Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q r s _hq _hr _hs
      P R S
    have hrel :=
      hsel.V_relabel_eq hax
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc O Y Z)
        (prodDist (prodDist q r) s) (prodChannel (prodChannel P R) S)
    have hrel' :
        hfaces.branch_result.branch_agg.value_rep.V
            (prodDist q (prodDist r s))
            (experimentOfChannel (prodChannel P (prodChannel R S))) =
          hfaces.branch_result.branch_agg.value_rep.V
            (prodDist (prodDist q r) s)
            (experimentOfChannel (prodChannel (prodChannel P R) S)) := by
      simpa [relabelDist_prodAssoc q r s, relabelChannel_prodAssoc P R S]
        using hrel
    exact hrel'.symm

end TraceableAgency
