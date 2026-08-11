/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.AffineTools

/-!
# Anchor normalization of affine utility

This file contains the preference-free normalization used to put every
marked-terminal Herstein--Milnor representative on the same material scale.
Given a strictly ordered pair of anchors, the lower anchor is assigned zero
and the upper anchor one.  No normalization convention is assumed: all facts
below are consequences of the supplied affine representation.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u v

variable {X : Type u}

/-- A represented strict comparison is a strict numerical inequality. -/
theorem affineUtility_strict_value
    {M : AbstractConvexMixtureSpace X} {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R) {high low : X}
    (hstrict : HMStrict R high low) :
    rep.utility low < rep.utility high := by
  have hle : rep.utility low ≤ rep.utility high :=
    (rep.represents high low).1 hstrict.1
  exact lt_of_le_of_ne hle fun heq ↦
    hstrict.2 ((rep.represents low high).2 (le_of_eq heq.symm))

/-- The positive gap between two strictly ordered anchors. -/
noncomputable def affineAnchorGap
    {M : AbstractConvexMixtureSpace X} {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R) (high low : X) : ℝ :=
  rep.utility high - rep.utility low

theorem affineAnchorGap_pos
    {M : AbstractConvexMixtureSpace X} {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R) {high low : X}
    (hstrict : HMStrict R high low) :
    0 < affineAnchorGap rep high low := by
  exact sub_pos.mpr (affineUtility_strict_value rep hstrict)

/-- Normalize an affine representative at a strict high/low pair. -/
noncomputable def normalizeAffineUtility
    {M : AbstractConvexMixtureSpace X} {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R) (high low : X)
    (hstrict : HMStrict R high low) :
    AffineUtilityRepresentation M R where
  utility := fun x ↦
    (rep.utility x - rep.utility low) / affineAnchorGap rep high low
  represents := by
    intro x y
    rw [rep.represents]
    have hgap := affineAnchorGap_pos rep hstrict
    constructor
    · intro hxy
      exact (div_le_div_iff_of_pos_right hgap).2 (by linarith)
    · intro hxy
      have := (div_le_div_iff_of_pos_right hgap).1 hxy
      linarith
  affine := by
    intro t x y
    rw [rep.affine]
    have hgap_ne : affineAnchorGap rep high low ≠ 0 :=
      ne_of_gt (affineAnchorGap_pos rep hstrict)
    field_simp [hgap_ne]
    ring

@[simp]
theorem normalizeAffineUtility_low
    {M : AbstractConvexMixtureSpace X} {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R) (high low : X)
    (hstrict : HMStrict R high low) :
    (normalizeAffineUtility rep high low hstrict).utility low = 0 := by
  simp [normalizeAffineUtility]

@[simp]
theorem normalizeAffineUtility_high
    {M : AbstractConvexMixtureSpace X} {R : X → X → Prop}
    (rep : AffineUtilityRepresentation M R) (high low : X)
    (hstrict : HMStrict R high low) :
    (normalizeAffineUtility rep high low hstrict).utility high = 1 := by
  change (rep.utility high - rep.utility low) /
      (rep.utility high - rep.utility low) = 1
  exact div_self (ne_of_gt (affineAnchorGap_pos rep hstrict))

/-- Two affine representatives normalized at the same strict anchors agree
pointwise.  This is the cardinal uniqueness fact used for dummy lifts and
cross-prior product bridges. -/
theorem normalizedAffineUtility_unique
    {M : AbstractConvexMixtureSpace X} {R : X → X → Prop}
    (base target : AffineUtilityRepresentation M R)
    (high low : X) (hstrict : HMStrict R high low)
    (hbaseLow : base.utility low = 0)
    (hbaseHigh : base.utility high = 1)
    (htargetLow : target.utility low = 0)
    (htargetHigh : target.utility high = 1) :
    ∀ x, target.utility x = base.utility x := by
  have hnonconstant : ∃ x y : X, base.utility x ≠ base.utility y := by
    exact ⟨high, low, by simp [hbaseHigh, hbaseLow]⟩
  obtain ⟨a, b, ha, hab⟩ :=
    affineUtilityRepresentation_positiveAffine_unique
      M R base target hnonconstant
  have hb : b = 0 := by
    have h := hab low
    rw [hbaseLow, htargetLow] at h
    linarith
  have ha1 : a = 1 := by
    have h := hab high
    rw [hbaseHigh, htargetHigh, hb] at h
    linarith
  intro x
  rw [hab x, ha1, hb]
  ring

/-- Pull an affine utility back along an affine order embedding. -/
noncomputable def pullbackAffineUtility
    {Y : Type v}
    (MX : AbstractConvexMixtureSpace X)
    (MY : AbstractConvexMixtureSpace Y)
    (RX : X → X → Prop) (RY : Y → Y → Prop)
    (target : AffineUtilityRepresentation MY RY)
    (f : X → Y)
    (horder : ∀ x y, RX x y ↔ RY (f x) (f y))
    (hmix : ∀ (t : Set.Ioo (0 : ℝ) 1) x y,
      f (MX.mix t x y) = MY.mix t (f x) (f y)) :
    AffineUtilityRepresentation MX RX where
  utility := fun x ↦ target.utility (f x)
  represents := by
    intro x y
    rw [horder, target.represents]
  affine := by
    intro t x y
    rw [hmix, target.affine]

/-- Anchor normalization makes an affine order embedding cardinally exact. -/
theorem normalizedAffineUtility_eq_along_embedding
    {Y : Type v}
    (MX : AbstractConvexMixtureSpace X)
    (MY : AbstractConvexMixtureSpace Y)
    (RX : X → X → Prop) (RY : Y → Y → Prop)
    (base : AffineUtilityRepresentation MX RX)
    (target : AffineUtilityRepresentation MY RY)
    (f : X → Y)
    (horder : ∀ x y, RX x y ↔ RY (f x) (f y))
    (hmix : ∀ (t : Set.Ioo (0 : ℝ) 1) x y,
      f (MX.mix t x y) = MY.mix t (f x) (f y))
    (high low : X) (hstrict : HMStrict RX high low)
    (hbaseLow : base.utility low = 0)
    (hbaseHigh : base.utility high = 1)
    (htargetLow : target.utility (f low) = 0)
    (htargetHigh : target.utility (f high) = 1) :
    ∀ x, target.utility (f x) = base.utility x := by
  let pulled := pullbackAffineUtility MX MY RX RY target f horder hmix
  exact normalizedAffineUtility_unique base pulled high low hstrict
    hbaseLow hbaseHigh htargetLow htargetHigh

end TraceableAgency.Theorem1
