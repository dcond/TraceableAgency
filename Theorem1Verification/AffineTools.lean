/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.External.GenericHersteinMilnor

/-!
# Small affine-uniqueness tools

This file proves the standard uniqueness statement for affine utilities on an
abstract convex mixture space.  It is preference-free and introduces no
axiom: two affine utilities representing the same nonconstant weak order are
related by one positive affine transformation.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

private theorem affine_value_on_segment
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R)
    (t : HMUnitInterval) (x y : X) :
    rep.utility (hmSegment M t x y) =
      t.1 * rep.utility x + (1 - t.1) * rep.utility y := by
  by_cases h0 : t.1 = 0
  · have ht : t = hmUnitZero := Subtype.ext h0
    subst t
    calc
      rep.utility (hmSegment M hmUnitZero x y) = rep.utility y := by
        rw [hmSegment_zero]
      _ = (hmUnitZero : ℝ) * rep.utility x +
          (1 - (hmUnitZero : ℝ)) * rep.utility y := by
        norm_num [hmUnitZero]
  by_cases h1 : t.1 = 1
  · have ht : t = hmUnitOne := Subtype.ext h1
    subst t
    calc
      rep.utility (hmSegment M hmUnitOne x y) = rep.utility x := by
        rw [hmSegment_one]
      _ = (hmUnitOne : ℝ) * rep.utility x +
          (1 - (hmUnitOne : ℝ)) * rep.utility y := by
        norm_num [hmUnitOne]
  let ti : Set.Ioo (0 : ℝ) 1 :=
    ⟨t.1, lt_of_le_of_ne t.2.1 (Ne.symm h0),
      lt_of_le_of_ne t.2.2 h1⟩
  rw [show hmSegment M t x y = M.mix ti x y by
    simp [hmSegment, h0, h1, ti]]
  exact rep.affine ti x y

private theorem affine_rep_indiff_iff_value_eq
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R) (x y : X) :
    HMIndiff R x y ↔ rep.utility x = rep.utility y := by
  constructor
  · intro h
    exact le_antisymm
      ((rep.represents y x).1 h.2)
      ((rep.represents x y).1 h.1)
  · intro h
    constructor
    · exact (rep.represents x y).2 (le_of_eq h.symm)
    · exact (rep.represents y x).2 (le_of_eq h)

/-- Affine utility on a nonconstant abstract mixture order is unique up to a
positive affine transformation. -/
theorem affineUtilityRepresentation_positiveAffine_unique
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop)
    (base target : AffineUtilityRepresentation M R)
    (hnonconstant : ∃ x y : X, base.utility x ≠ base.utility y) :
    ∃ a b : ℝ, 0 < a ∧
      ∀ z : X, target.utility z = a * base.utility z + b := by
  classical
  rcases hnonconstant with ⟨x, y, hxy⟩
  obtain ⟨high, low, hbase⟩ :
      ∃ high low : X, base.utility low < base.utility high := by
    rcases lt_or_gt_of_ne hxy with h | h
    · exact ⟨y, x, h⟩
    · exact ⟨x, y, h⟩
  have hstrict : HMStrict R high low := by
    constructor
    · exact (base.represents high low).2 (le_of_lt hbase)
    · intro hrev
      have := (base.represents low high).1 hrev
      linarith
  have htarget : target.utility low < target.utility high := by
    have hge := (target.represents high low).1 hstrict.1
    have hnge : ¬ target.utility low ≥ target.utility high := by
      intro h
      exact hstrict.2 ((target.represents low high).2 h)
    exact lt_of_le_of_ne hge (fun heq => hnge (le_of_eq heq.symm))
  let a : ℝ :=
    (target.utility high - target.utility low) /
      (base.utility high - base.utility low)
  let b : ℝ := target.utility low - a * base.utility low
  have hden : 0 < base.utility high - base.utility low := sub_pos.mpr hbase
  have hnum : 0 < target.utility high - target.utility low := sub_pos.mpr htarget
  have ha : 0 < a := div_pos hnum hden
  refine ⟨a, b, ha, ?_⟩
  intro z
  by_cases hzlo : base.utility z < base.utility low
  · let tval : ℝ :=
      (base.utility low - base.utility z) /
        (base.utility high - base.utility z)
    have ht0 : 0 < tval := div_pos (sub_pos.mpr hzlo)
      (sub_pos.mpr (lt_trans hzlo hbase))
    have ht1 : tval < 1 := by
      rw [div_lt_one (sub_pos.mpr (lt_trans hzlo hbase))]
      linarith
    let t : Set.Ioo (0 : ℝ) 1 := ⟨tval, ht0, ht1⟩
    have hbaseMix :
        base.utility (M.mix t high z) = base.utility low := by
      rw [base.affine]
      dsimp [t, tval]
      field_simp [ne_of_gt (sub_pos.mpr (lt_trans hzlo hbase))]
      ring
    have hind : HMIndiff R (M.mix t high z) low :=
      (affine_rep_indiff_iff_value_eq base _ _).2 hbaseMix
    have htargetMix :
        target.utility (M.mix t high z) = target.utility low :=
      (affine_rep_indiff_iff_value_eq target _ _).1 hind
    rw [target.affine] at htargetMix
    dsimp [t, tval] at htargetMix
    dsimp [a, b, t, tval]
    field_simp [ne_of_gt hden,
      ne_of_gt (sub_pos.mpr (lt_trans hzlo hbase))] at htargetMix ⊢
    ring_nf at htargetMix ⊢
    linarith
  · have hzlo' : base.utility low ≤ base.utility z := le_of_not_gt hzlo
    by_cases hzhi : base.utility high < base.utility z
    · let tval : ℝ :=
        (base.utility high - base.utility low) /
          (base.utility z - base.utility low)
      have ht0 : 0 < tval := div_pos hden (sub_pos.mpr (lt_trans hbase hzhi))
      have ht1 : tval < 1 := by
        rw [div_lt_one (sub_pos.mpr (lt_trans hbase hzhi))]
        linarith
      let t : Set.Ioo (0 : ℝ) 1 := ⟨tval, ht0, ht1⟩
      have hbaseMix :
          base.utility (M.mix t z low) = base.utility high := by
        rw [base.affine]
        dsimp [t, tval]
        field_simp [ne_of_gt (sub_pos.mpr (lt_trans hbase hzhi))]
        ring
      have hind : HMIndiff R (M.mix t z low) high :=
        (affine_rep_indiff_iff_value_eq base _ _).2 hbaseMix
      have htargetMix :
          target.utility (M.mix t z low) = target.utility high :=
        (affine_rep_indiff_iff_value_eq target _ _).1 hind
      rw [target.affine] at htargetMix
      dsimp [t, tval] at htargetMix
      dsimp [a, b, t, tval]
      field_simp [ne_of_gt hden,
        ne_of_gt (sub_pos.mpr (lt_trans hbase hzhi))] at htargetMix ⊢
      ring_nf at htargetMix ⊢
      linarith
    · have hzhi' : base.utility z ≤ base.utility high := le_of_not_gt hzhi
      let tval : ℝ :=
        (base.utility z - base.utility low) /
          (base.utility high - base.utility low)
      have ht0 : 0 ≤ tval := div_nonneg (sub_nonneg.mpr hzlo') (le_of_lt hden)
      have ht1 : tval ≤ 1 := by
        rw [div_le_one hden]
        linarith
      let t : HMUnitInterval := ⟨tval, ht0, ht1⟩
      have hbaseSeg :
          base.utility (hmSegment M t high low) = base.utility z := by
        rw [affine_value_on_segment M base]
        dsimp [t, tval]
        field_simp [ne_of_gt hden]
        ring
      have hind : HMIndiff R (hmSegment M t high low) z :=
        (affine_rep_indiff_iff_value_eq base _ _).2 hbaseSeg
      have htargetSeg :
          target.utility (hmSegment M t high low) = target.utility z :=
        (affine_rep_indiff_iff_value_eq target _ _).1 hind
      rw [affine_value_on_segment M target] at htargetSeg
      dsimp [t, tval] at htargetSeg
      dsimp [a, b, t, tval]
      field_simp [ne_of_gt hden] at htargetSeg ⊢
      ring_nf at htargetSeg ⊢
      linarith

end TraceTemperedChoiceVerification
