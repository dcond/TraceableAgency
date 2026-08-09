/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.HersteinMilnor

/-!
# Generic Herstein--Milnor theorem

This file proves the exact preference-free mixture-space theorem stated by
`ClassicalHersteinMilnorMixtureTheoremAssumptions`.  The proof uses only:

* separating affine real coordinates for the interior mixture operation;
* completeness, transitivity, and mixture independence;
* sequential closure for coordinatewise-convergent sequences.

The construction is the classical standard-sequence/calibration argument.
Closed upper and lower contour cuts on the real unit interval intersect by
connectedness.  A nontrivial pair then calibrates every point by a unique real
number, and mixture independence makes that calibration affine.
-/

set_option linter.style.header false

namespace TraceableAgency

open Filter Set Topology

universe u

/-- Closed unit-interval coefficients used to include the two endpoints in
the Herstein--Milnor calibration path. -/
abbrev HMUnitInterval := Set.Icc (0 : ℝ) 1

def hmUnitZero : HMUnitInterval := ⟨0, by simp⟩

def hmUnitOne : HMUnitInterval := ⟨1, by simp⟩

noncomputable def hmUnitHalf : HMUnitInterval := ⟨(1 / 2 : ℝ), by norm_num⟩

/-- Extend the primitive interior mixture operation to the closed unit
interval by using the corresponding endpoint at `0` and `1`. -/
noncomputable def hmSegment
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (t : HMUnitInterval) (x y : X) : X :=
  if h0 : t.1 = 0 then y
  else if h1 : t.1 = 1 then x
  else
    M.mix
      ⟨t.1,
        lt_of_le_of_ne t.2.1 (Ne.symm h0),
        lt_of_le_of_ne t.2.2 h1⟩ x y

@[simp]
theorem hmSegment_zero
    {X : Type u} (M : AbstractConvexMixtureSpace X) (x y : X) :
    hmSegment M hmUnitZero x y = y := by
  simp [hmSegment, hmUnitZero]

@[simp]
theorem hmSegment_one
    {X : Type u} (M : AbstractConvexMixtureSpace X) (x y : X) :
    hmSegment M hmUnitOne x y = x := by
  simp [hmSegment, hmUnitOne]

theorem hmSegment_coordinate
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (t : HMUnitInterval) (x y : X) (k : M.Coordinate) :
    M.coordinate (hmSegment M t x y) k =
      t.1 * M.coordinate x k + (1 - t.1) * M.coordinate y k := by
  by_cases h0 : t.1 = 0
  · simp [hmSegment, h0]
  by_cases h1 : t.1 = 1
  · simp [hmSegment, h1]
  · simp only [hmSegment, dif_neg h0, dif_neg h1]
    exact M.coordinate_mix
      ⟨t.1, lt_of_le_of_ne t.2.1 (Ne.symm h0),
        lt_of_le_of_ne t.2.2 h1⟩ x y k

theorem hmSegment_eq_mix
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (t : Set.Ioo (0 : ℝ) 1) (x y : X) :
    hmSegment M ⟨t.1, le_of_lt t.2.1, le_of_lt t.2.2⟩ x y =
      M.mix t x y := by
  unfold hmSegment
  rw [dif_neg (ne_of_gt t.2.1), dif_neg (ne_of_lt t.2.2)]

/-- The closed segment is coordinatewise continuous in its coefficient. -/
theorem hmSegment_converges
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (𝓝 t)) (x y : X) :
    M.Converges (fun n => hmSegment M (tseq n) x y)
      (hmSegment M t x y) := by
  intro k
  have hval :
      Tendsto (fun n => (tseq n).1) atTop (𝓝 t.1) :=
    (continuous_subtype_val.tendsto t).comp ht
  have hcoord :
      Tendsto
        (fun n =>
          (tseq n).1 * M.coordinate x k +
            (1 - (tseq n).1) * M.coordinate y k)
        atTop
        (𝓝 (t.1 * M.coordinate x k +
          (1 - t.1) * M.coordinate y k)) :=
    (hval.mul tendsto_const_nhds).add
      ((tendsto_const_nhds.sub hval).mul tendsto_const_nhds)
  simpa only [hmSegment_coordinate] using hcoord

/-- Weak indifference associated with a binary relation. -/
def HMIndiff {X : Type u} (R : X → X → Prop) (x y : X) : Prop :=
  R x y ∧ R y x

/-- Strict preference associated with a binary relation. -/
def HMStrict {X : Type u} (R : X → X → Prop) (x y : X) : Prop :=
  R x y ∧ ¬ R y x

/-- The exact order-theoretic input used by the calibration construction.

The generic Herstein--Milnor proof needs continuity only to obtain an
indifferent point on each closed anchor segment.  Once those points are
available, completeness, transitivity, and mixture independence suffice for
the rest of the construction.  Keeping this smaller interface separate lets
applications prove segment calibration directly without manufacturing a
global sequential-closedness statement. -/
structure HMCalibratableWeakOrder
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) : Prop where
  complete : ∀ x y, R x y ∨ R y x
  transitive : ∀ x y z, R x y → R y z → R x z
  independence :
    ∀ (x y z : X) (t : Set.Ioo (0 : ℝ) 1),
      R x y ↔ R (M.mix t x z) (M.mix t y z)
  segment_calibration :
    ∀ (high target low : X),
      R high target → R target low →
        ∃ t : HMUnitInterval,
          HMIndiff R target (hmSegment M t high low)

theorem hm_refl
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    (x : X) :
    R x x := by
  rcases hR.complete x x with h | h
  · exact h
  · exact h

theorem hm_indiff_refl
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    (x : X) :
    HMIndiff R x x :=
  ⟨hm_refl hR x, hm_refl hR x⟩

theorem hm_indiff_symm
    {X : Type u} {R : X → X → Prop} {x y : X}
    (h : HMIndiff R x y) :
    HMIndiff R y x :=
  ⟨h.2, h.1⟩

theorem hm_indiff_trans
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x y z : X} (hxy : HMIndiff R x y) (hyz : HMIndiff R y z) :
    HMIndiff R x z :=
  ⟨hR.transitive x y z hxy.1 hyz.1,
    hR.transitive z y x hyz.2 hxy.2⟩

theorem hm_rel_congr
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x x' y y' : X}
    (hxx' : HMIndiff R x x') (hyy' : HMIndiff R y y') :
    R x y ↔ R x' y' := by
  constructor
  · intro hxy
    exact hR.transitive x' x y' hxx'.2
      (hR.transitive x y y' hxy hyy'.1)
  · intro hx'y'
    exact hR.transitive x x' y hxx'.1
      (hR.transitive x' y' y hx'y' hyy'.2)

theorem hm_strict_of_indiff_left
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x x' y : X} (hxx' : HMIndiff R x x') (hxy : HMStrict R x y) :
    HMStrict R x' y := by
  constructor
  · exact hR.transitive x' x y hxx'.2 hxy.1
  · intro hyx'
    exact hxy.2 (hR.transitive y x' x hyx' hxx'.2)

theorem hm_strict_of_indiff_right
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x y y' : X} (hyy' : HMIndiff R y y') (hxy : HMStrict R x y) :
    HMStrict R x y' := by
  constructor
  · exact hR.transitive x y y' hxy.1 hyy'.1
  · intro hy'x
    exact hxy.2 (hR.transitive y y' x hyy'.1 hy'x)

theorem hm_strict_trans
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x y z : X} (hxy : HMStrict R x y) (hyz : HMStrict R y z) :
    HMStrict R x z := by
  constructor
  · exact hR.transitive x y z hxy.1 hyz.1
  · intro hzx
    exact hyz.2 (hR.transitive z x y hzx hxy.1)

/-- Independence preserves indifference when both alternatives are mixed
with the same background. -/
theorem hm_indiff_mix_iff
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    (x y z : X) (t : Set.Ioo (0 : ℝ) 1) :
    HMIndiff R x y ↔
      HMIndiff R (M.mix t x z) (M.mix t y z) := by
  constructor
  · intro h
    exact ⟨(hR.independence x y z t).mp h.1,
      (hR.independence y x z t).mp h.2⟩
  · intro h
    exact ⟨(hR.independence x y z t).mpr h.1,
      (hR.independence y x z t).mpr h.2⟩

theorem hm_strict_mix
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x y : X} (hxy : HMStrict R x y) (z : X)
    (t : Set.Ioo (0 : ℝ) 1) :
    HMStrict R (M.mix t x z) (M.mix t y z) := by
  constructor
  · exact (hR.independence x y z t).mp hxy.1
  · intro hrev
    exact hxy.2 ((hR.independence y x z t).mpr hrev)

/-- Mixtures respect indifference in both arguments. -/
theorem hm_mix_indiff_congr
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x x' y y' : X} (hxx' : HMIndiff R x x')
    (hyy' : HMIndiff R y y') (t : Set.Ioo (0 : ℝ) 1) :
    HMIndiff R (M.mix t x y) (M.mix t x' y') := by
  have hfirst :
      HMIndiff R (M.mix t x y) (M.mix t x' y) :=
    (hm_indiff_mix_iff hR x x' y t).mp hxx'
  let tswap : Set.Ioo (0 : ℝ) 1 :=
    ⟨1 - t.1, sub_pos.mpr t.2.2, by linarith [t.2.1]⟩
  have hsecondSwap :
      HMIndiff R (M.mix tswap y x') (M.mix tswap y' x') :=
    (hm_indiff_mix_iff hR y y' x' tswap).mp hyy'
  have hsecond :
      HMIndiff R (M.mix t x' y) (M.mix t x' y') := by
    simpa only [M.mix_swap t x' y, M.mix_swap t x' y'] using hsecondSwap
  exact hm_indiff_trans hR hfirst hsecond

/-- The two contour cuts of a point along a closed mixture segment intersect.
This is precisely where sequential closure is used. -/
theorem hm_exists_indifferent_segment
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : ContinuousIndependentWeakOrder M R)
    (high target low : X)
    (hhigh : R high target) (hlow : R target low) :
    ∃ t : HMUnitInterval,
      HMIndiff R target (hmSegment M t high low) := by
  let upper : Set HMUnitInterval :=
    {t | R (hmSegment M t high low) target}
  let lower : Set HMUnitInterval :=
    {t | R target (hmSegment M t high low)}
  have hupperClosed : IsClosed upper := by
    apply IsSeqClosed.isClosed
    intro tseq t htmem htt
    exact hR.sequentially_closed
      (fun n => hmSegment M (tseq n) high low)
      (hmSegment M t high low)
      (fun _ => target) target
      (hmSegment_converges M htt high low)
      (fun k => tendsto_const_nhds)
      (fun n => htmem n)
  have hlowerClosed : IsClosed lower := by
    apply IsSeqClosed.isClosed
    intro tseq t htmem htt
    exact hR.sequentially_closed
      (fun _ => target) target
      (fun n => hmSegment M (tseq n) high low)
      (hmSegment M t high low)
      (fun k => tendsto_const_nhds)
      (hmSegment_converges M htt high low)
      (fun n => htmem n)
  have honeUpper : hmUnitOne ∈ upper := by
    simpa [upper] using hhigh
  have hzeroLower : hmUnitZero ∈ lower := by
    simpa [lower] using hlow
  by_contra hinter
  have hdisjoint : upper ∩ lower = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    exact hinter ⟨t, ht.2, ht.1⟩
  have hcover : (Set.univ : Set HMUnitInterval) ⊆ upperᶜ ∪ lowerᶜ := by
    intro t _ht
    by_cases hu : t ∈ upper
    · right
      intro hl
      have : t ∈ upper ∩ lower := ⟨hu, hl⟩
      rw [hdisjoint] at this
      exact this
    · exact Or.inl hu
  have hleftNonempty : ((Set.univ : Set HMUnitInterval) ∩ upperᶜ).Nonempty := by
    refine ⟨hmUnitZero, Set.mem_univ _, ?_⟩
    intro hzUpper
    have : hmUnitZero ∈ upper ∩ lower := ⟨hzUpper, hzeroLower⟩
    rw [hdisjoint] at this
    exact this
  have hrightNonempty : ((Set.univ : Set HMUnitInterval) ∩ lowerᶜ).Nonempty := by
    refine ⟨hmUnitOne, Set.mem_univ _, ?_⟩
    intro hoLower
    have : hmUnitOne ∈ upper ∩ lower := ⟨honeUpper, hoLower⟩
    rw [hdisjoint] at this
    exact this
  have hboth :=
    isPreconnected_univ upperᶜ lowerᶜ
      hupperClosed.isOpen_compl hlowerClosed.isOpen_compl
      hcover hleftNonempty hrightNonempty
  rcases hboth with ⟨t, _htuniv, hnotUpper, hnotLower⟩
  rcases hR.complete (hmSegment M t high low) target with h | h
  · exact hnotUpper h
  · exact hnotLower h

/-- Sequentially closed independent weak orders are calibratable.  This is
the compatibility bridge from the original generic HM interface to the
smaller interface used by the proof below. -/
theorem HMCalibratableWeakOrder.ofContinuous
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop}
    (hR : ContinuousIndependentWeakOrder M R) :
    HMCalibratableWeakOrder M R where
  complete := hR.complete
  transitive := hR.transitive
  independence := hR.independence
  segment_calibration := by
    intro high target low hhigh hlow
    exact hm_exists_indifferent_segment M R hR high target low hhigh hlow

/-- Convenience coercion for contexts in which the mixture space and relation
are already fixed by the expected `HMCalibratableWeakOrder` type. -/
instance continuousIndependentWeakOrderToHMCalibratableWeakOrder
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} :
    Coe (ContinuousIndependentWeakOrder M R)
      (HMCalibratableWeakOrder M R) :=
  ⟨HMCalibratableWeakOrder.ofContinuous⟩

/-- Every nonzero point on a segment from a strictly better endpoint is
strictly better than the low endpoint. -/
theorem hm_segment_strict_low
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    {high low : X} (hhl : HMStrict R high low)
    (t : HMUnitInterval) (ht0 : 0 < t.1) :
    HMStrict R (hmSegment M t high low) low := by
  by_cases ht1 : t.1 = 1
  · have ht : t = hmUnitOne := Subtype.ext ht1
    simpa [ht] using hhl
  let ti : Set.Ioo (0 : ℝ) 1 :=
    ⟨t.1, ht0, lt_of_le_of_ne t.2.2 ht1⟩
  have hs := hm_strict_mix hR hhl low ti
  rw [M.mix_self] at hs
  have hseg : hmSegment M t high low = M.mix ti high low := by
    unfold hmSegment
    rw [dif_neg (ne_of_gt ht0), dif_neg ht1]
  rwa [hseg]

/-- Every point short of the high endpoint on a strict segment is strictly
below that endpoint. -/
theorem hm_segment_strict_high
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    {high low : X} (hhl : HMStrict R high low)
    (t : HMUnitInterval) (ht1 : t.1 < 1) :
    HMStrict R high (hmSegment M t high low) := by
  by_cases ht0 : t.1 = 0
  · have ht : t = hmUnitZero := Subtype.ext ht0
    simpa [ht] using hhl
  let ti : Set.Ioo (0 : ℝ) 1 :=
    ⟨t.1, lt_of_le_of_ne t.2.1 (Ne.symm ht0), ht1⟩
  let tswap : Set.Ioo (0 : ℝ) 1 :=
    ⟨1 - t.1, sub_pos.mpr ht1, by linarith [ti.2.1]⟩
  have hs := hm_strict_mix hR hhl high tswap
  rw [M.mix_self] at hs
  have hswap : M.mix ti high low = M.mix tswap low high :=
    M.mix_swap ti high low
  rw [← hswap] at hs
  have hseg : hmSegment M t high low = M.mix ti high low := by
    unfold hmSegment
    rw [dif_neg ht0, dif_neg (ne_of_lt ht1)]
  rwa [hseg]

/-- Strict endpoints make the closed calibration segment strictly increasing
in its scalar coefficient. -/
theorem hm_segment_strict_mono
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    {high low : X} (hhl : HMStrict R high low)
    (s t : HMUnitInterval) (hst : s.1 < t.1) :
    HMStrict R (hmSegment M t high low) (hmSegment M s high low) := by
  by_cases ht1 : t.1 = 1
  · have ht : t = hmUnitOne := Subtype.ext ht1
    simpa [ht] using
      hm_segment_strict_high M R hR hhl s (by simpa [ht1] using hst)
  have hs1 : s.1 < 1 := lt_trans hst (lt_of_le_of_ne t.2.2 ht1)
  have hden : 0 < 1 - s.1 := sub_pos.mpr hs1
  let lam : Set.Ioo (0 : ℝ) 1 :=
    ⟨(t.1 - s.1) / (1 - s.1),
      div_pos (sub_pos.mpr hst) hden,
      (div_lt_one hden).mpr (by linarith [lt_of_le_of_ne t.2.2 ht1])⟩
  have hhighs :
      HMStrict R high (hmSegment M s high low) :=
    hm_segment_strict_high M R hR hhl s hs1
  have hmixed :=
    hm_strict_mix hR hhighs (hmSegment M s high low) lam
  rw [M.mix_self] at hmixed
  have heq :
      M.mix lam high (hmSegment M s high low) =
        hmSegment M t high low := by
    apply M.coordinate_ext
    intro k
    rw [M.coordinate_mix, hmSegment_coordinate, hmSegment_coordinate]
    dsimp [lam]
    field_simp [ne_of_gt hden]
    ring
  rwa [heq] at hmixed

/-- Along a strict segment, the weak order is exactly the reverse order of
the right-hand coefficient argument. -/
theorem hm_segment_rel_iff
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    {high low : X} (hhl : HMStrict R high low)
    (s t : HMUnitInterval) :
    R (hmSegment M s high low) (hmSegment M t high low) ↔
      t.1 ≤ s.1 := by
  constructor
  · intro hrel
    by_contra hnot
    have hst : s.1 < t.1 := lt_of_not_ge hnot
    exact (hm_segment_strict_mono M R hR hhl s t hst).2 hrel
  · intro hts
    rcases hts.eq_or_lt with heq | hlt
    · have hsub : t = s := Subtype.ext heq
      simpa [hsub] using hm_refl hR (hmSegment M s high low)
    · exact (hm_segment_strict_mono M R hR hhl t s hlt).1

theorem hm_indifferent_segment_unique
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    {high low target : X} (hhl : HMStrict R high low)
    {s t : HMUnitInterval}
    (hs : HMIndiff R target (hmSegment M s high low))
    (ht : HMIndiff R target (hmSegment M t high low)) :
    s = t := by
  have hst :
      R (hmSegment M s high low) (hmSegment M t high low) :=
    hR.transitive _ target _ hs.2 ht.1
  have hts :
      R (hmSegment M t high low) (hmSegment M s high low) :=
    hR.transitive _ target _ ht.2 hs.1
  apply Subtype.ext
  exact le_antisymm
    ((hm_segment_rel_iff M R hR hhl t s).mp hts)
    ((hm_segment_rel_iff M R hR hhl s t).mp hst)

/-- The canonical coefficient selected by the closed-contour intersection
argument. -/
noncomputable def hmBetweenCoefficient
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (high target low : X)
    (hhigh : R high target) (hlow : R target low) :
    HMUnitInterval :=
  Classical.choose
    (hR.segment_calibration high target low hhigh hlow)

theorem hmBetweenCoefficient_spec
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (high target low : X)
    (hhigh : R high target) (hlow : R target low) :
    HMIndiff R target
      (hmSegment M
        (hmBetweenCoefficient M R hR high target low hhigh hlow)
        high low) :=
  Classical.choose_spec
    (hR.segment_calibration high target low hhigh hlow)

theorem hmBetweenCoefficient_unique
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (high target low : X)
    (hhigh : R high target) (hlow : R target low)
    (hhl : HMStrict R high low)
    (t : HMUnitInterval)
    (ht : HMIndiff R target (hmSegment M t high low)) :
    t = hmBetweenCoefficient M R hR high target low hhigh hlow :=
  hm_indifferent_segment_unique M R hR hhl ht
    (hmBetweenCoefficient_spec M R hR high target low hhigh hlow)

theorem hm_reverse_rel_of_not_strict
    {X : Type u} {M : AbstractConvexMixtureSpace X}
    {R : X → X → Prop} (hR : HMCalibratableWeakOrder M R)
    {x y : X} (hnot : ¬ HMStrict R x y) :
    R y x := by
  rcases hR.complete x y with hxy | hyx
  · by_contra hn
    exact hnot ⟨hxy, hn⟩
  · exact hyx

/-- Weight on an alternative strictly above the high anchor that makes it
indifferent to that anchor after dilution by the low anchor. -/
noncomputable def hmUpperWeight
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hxa : HMStrict R x a) :
    HMUnitInterval :=
  hmBetweenCoefficient M R hR x a b hxa.1 hab.1

theorem hmUpperWeight_spec
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hxa : HMStrict R x a) :
    HMIndiff R a
      (hmSegment M (hmUpperWeight M R hR a b hab x hxa) x b) :=
  hmBetweenCoefficient_spec M R hR x a b hxa.1 hab.1

theorem hmUpperWeight_mem_Ioo
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hxa : HMStrict R x a) :
    (hmUpperWeight M R hR a b hab x hxa).1 ∈ Set.Ioo (0 : ℝ) 1 := by
  let p := hmUpperWeight M R hR a b hab x hxa
  have hp := hmUpperWeight_spec M R hR a b hab x hxa
  change HMIndiff R a (hmSegment M p x b) at hp
  have hp0 : p.1 ≠ 0 := by
    intro hzero
    have hpeq : p = hmUnitZero := Subtype.ext hzero
    rw [hpeq, hmSegment_zero] at hp
    exact hab.2 hp.2
  have hp1 : p.1 ≠ 1 := by
    intro hone
    have hpeq : p = hmUnitOne := Subtype.ext hone
    rw [hpeq, hmSegment_one] at hp
    exact hxa.2 hp.1
  exact
    ⟨lt_of_le_of_ne p.2.1 (Ne.symm hp0),
      lt_of_le_of_ne p.2.2 hp1⟩

/-- Raw coefficient on the high anchor that makes a point strictly below the
low anchor indifferent to that low anchor. -/
noncomputable def hmLowerRawCoefficient
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hbx : HMStrict R b x) :
    HMUnitInterval :=
  hmBetweenCoefficient M R hR a b x hab.1 hbx.1

/-- Weight on the low alternative itself in the lower-anchor calibration. -/
noncomputable def hmLowerWeight
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hbx : HMStrict R b x) :
    HMUnitInterval := by
  let t := hmLowerRawCoefficient M R hR a b hab x hbx
  exact ⟨1 - t.1, by constructor <;> linarith [t.2.1, t.2.2]⟩

theorem hmLowerRawCoefficient_spec
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hbx : HMStrict R b x) :
    HMIndiff R b
      (hmSegment M
        (hmLowerRawCoefficient M R hR a b hab x hbx) a x) :=
  hmBetweenCoefficient_spec M R hR a b x hab.1 hbx.1

theorem hmLowerRawCoefficient_mem_Ioo
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hbx : HMStrict R b x) :
    (hmLowerRawCoefficient M R hR a b hab x hbx).1 ∈
      Set.Ioo (0 : ℝ) 1 := by
  let t := hmLowerRawCoefficient M R hR a b hab x hbx
  have ht := hmLowerRawCoefficient_spec M R hR a b hab x hbx
  change HMIndiff R b (hmSegment M t a x) at ht
  have ht0 : t.1 ≠ 0 := by
    intro hzero
    have hteq : t = hmUnitZero := Subtype.ext hzero
    rw [hteq, hmSegment_zero] at ht
    exact hbx.2 ht.2
  have ht1 : t.1 ≠ 1 := by
    intro hone
    have hteq : t = hmUnitOne := Subtype.ext hone
    rw [hteq, hmSegment_one] at ht
    exact hab.2 ht.1
  exact
    ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0),
      lt_of_le_of_ne t.2.2 ht1⟩

theorem hmLowerWeight_mem_Ioo
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hbx : HMStrict R b x) :
    (hmLowerWeight M R hR a b hab x hbx).1 ∈
      Set.Ioo (0 : ℝ) 1 := by
  have ht :=
    hmLowerRawCoefficient_mem_Ioo M R hR a b hab x hbx
  change 0 < 1 -
      (hmLowerRawCoefficient M R hR a b hab x hbx).1 ∧
    1 - (hmLowerRawCoefficient M R hR a b hab x hbx).1 < 1
  constructor <;> linarith [ht.1, ht.2]

theorem hmLowerWeight_spec
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hbx : HMStrict R b x) :
    let q := hmLowerWeight M R hR a b hab x hbx
    let qi : Set.Ioo (0 : ℝ) 1 :=
      ⟨q.1, (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).1,
        (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).2⟩
    HMIndiff R b (M.mix qi x a) := by
  dsimp
  let t := hmLowerRawCoefficient M R hR a b hab x hbx
  let ti : Set.Ioo (0 : ℝ) 1 :=
    ⟨t.1,
      (hmLowerRawCoefficient_mem_Ioo M R hR a b hab x hbx).1,
      (hmLowerRawCoefficient_mem_Ioo M R hR a b hab x hbx).2⟩
  have hspec := hmLowerRawCoefficient_spec M R hR a b hab x hbx
  have hseg : hmSegment M t a x = M.mix ti a x := by
    exact hmSegment_eq_mix M ti a x
  rw [hseg] at hspec
  have hswap := M.mix_swap ti a x
  rw [hswap] at hspec
  simpa [hmLowerWeight, t, ti] using hspec

/-- Relation comparison for two points above the high anchor, expressed by
their dilution weights. -/
theorem hm_upper_rel_iff_weight_le
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x y : X) (hxa : HMStrict R x a) (hya : HMStrict R y a) :
    R x y ↔
      (hmUpperWeight M R hR a b hab x hxa).1 ≤
        (hmUpperWeight M R hR a b hab y hya).1 := by
  let px := hmUpperWeight M R hR a b hab x hxa
  let py := hmUpperWeight M R hR a b hab y hya
  let pxi : Set.Ioo (0 : ℝ) 1 :=
    ⟨px.1, (hmUpperWeight_mem_Ioo M R hR a b hab x hxa).1,
      (hmUpperWeight_mem_Ioo M R hR a b hab x hxa).2⟩
  have hxspec := hmUpperWeight_spec M R hR a b hab x hxa
  have hyspec := hmUpperWeight_spec M R hR a b hab y hya
  have hsegx : hmSegment M px x b = M.mix pxi x b :=
    hmSegment_eq_mix M pxi x b
  have hsegy : hmSegment M px y b = M.mix pxi y b :=
    hmSegment_eq_mix M pxi y b
  have hyb : HMStrict R y b := hm_strict_trans hR hya hab
  calc
    R x y ↔ R (M.mix pxi x b) (M.mix pxi y b) :=
      hR.independence x y b pxi
    _ ↔ R (hmSegment M px x b) (hmSegment M px y b) := by
      rw [hsegx, hsegy]
    _ ↔ R a (hmSegment M px y b) :=
      hm_rel_congr hR (hm_indiff_symm hxspec)
        (hm_indiff_refl hR _)
    _ ↔ R (hmSegment M py y b) (hmSegment M px y b) :=
      hm_rel_congr hR hyspec (hm_indiff_refl hR _)
    _ ↔ px.1 ≤ py.1 :=
      hm_segment_rel_iff M R hR hyb py px

/-- Relation comparison for two points below the low anchor, expressed by
their self-weights in the lower calibration. -/
theorem hm_lower_rel_iff_weight_ge
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x y : X) (hbx : HMStrict R b x) (hby : HMStrict R b y) :
    R x y ↔
      (hmLowerWeight M R hR a b hab y hby).1 ≤
        (hmLowerWeight M R hR a b hab x hbx).1 := by
  let qx := hmLowerWeight M R hR a b hab x hbx
  let qy := hmLowerWeight M R hR a b hab y hby
  let qxi : Set.Ioo (0 : ℝ) 1 :=
    ⟨qx.1, (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).1,
      (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).2⟩
  let tx : HMUnitInterval := ⟨1 - qx.1, by
    constructor <;> linarith [qx.2.1, qx.2.2]⟩
  let ty : HMUnitInterval := ⟨1 - qy.1, by
    constructor <;> linarith [qy.2.1, qy.2.2]⟩
  have hxspec := hmLowerWeight_spec M R hR a b hab x hbx
  have hyspec := hmLowerWeight_spec M R hR a b hab y hby
  have hsegx : hmSegment M tx a x = M.mix qxi x a := by
    apply M.coordinate_ext
    intro k
    rw [hmSegment_coordinate, M.coordinate_mix]
    dsimp [tx, qxi]
    ring
  have hsegy : hmSegment M tx a y = M.mix qxi y a := by
    apply M.coordinate_ext
    intro k
    rw [hmSegment_coordinate, M.coordinate_mix]
    dsimp [tx, qxi]
    ring
  have hay : HMStrict R a y := hm_strict_trans hR hab hby
  have hxspec' : HMIndiff R b (hmSegment M tx a x) := by
    rw [hsegx]
    exact hxspec
  have hyspec' : HMIndiff R b (hmSegment M ty a y) := by
    let hqyi : Set.Ioo (0 : ℝ) 1 :=
      ⟨qy.1, (hmLowerWeight_mem_Ioo M R hR a b hab y hby).1,
        (hmLowerWeight_mem_Ioo M R hR a b hab y hby).2⟩
    have heq : hmSegment M ty a y = M.mix hqyi y a := by
      apply M.coordinate_ext
      intro k
      rw [hmSegment_coordinate, M.coordinate_mix]
      dsimp [ty, hqyi]
      ring
    rw [heq]
    simpa [hqyi, qy] using hyspec
  calc
    R x y ↔ R (M.mix qxi x a) (M.mix qxi y a) :=
      hR.independence x y a qxi
    _ ↔ R (hmSegment M tx a x) (hmSegment M tx a y) := by
      rw [hsegx, hsegy]
    _ ↔ R b (hmSegment M tx a y) :=
      hm_rel_congr hR (hm_indiff_symm hxspec')
        (hm_indiff_refl hR _)
    _ ↔ R (hmSegment M ty a y) (hmSegment M tx a y) :=
      hm_rel_congr hR hyspec' (hm_indiff_refl hR _)
    _ ↔ tx.1 ≤ ty.1 :=
      hm_segment_rel_iff M R hR hay ty tx
    _ ↔ qy.1 ≤ qx.1 := by
      change (1 - qx.1 ≤ 1 - qy.1) ↔ qy.1 ≤ qx.1
      constructor <;> intro h <;> linarith

/-- Comparison for two points between the normalized anchors. -/
theorem hm_middle_rel_iff_coefficient_ge
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x y : X) (hax : R a x) (hxb : R x b)
    (hay : R a y) (hyb : R y b) :
    R x y ↔
      (hmBetweenCoefficient M R hR a y b hay hyb).1 ≤
        (hmBetweenCoefficient M R hR a x b hax hxb).1 := by
  let tx := hmBetweenCoefficient M R hR a x b hax hxb
  let ty := hmBetweenCoefficient M R hR a y b hay hyb
  have hxspec := hmBetweenCoefficient_spec M R hR a x b hax hxb
  have hyspec := hmBetweenCoefficient_spec M R hR a y b hay hyb
  calc
    R x y ↔ R (hmSegment M tx a b) (hmSegment M ty a b) :=
      hm_rel_congr hR hxspec hyspec
    _ ↔ ty.1 ≤ tx.1 :=
      hm_segment_rel_iff M R hR hab tx ty

/-- Normalized Herstein--Milnor utility associated with a strict anchor pair:
the anchors receive values `1` and `0`. -/
noncomputable def hmUtility
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X) : ℝ := by
  classical
  by_cases hxa : HMStrict R x a
  · exact 1 / (hmUpperWeight M R hR a b hab x hxa).1
  by_cases hbx : HMStrict R b x
  · exact 1 - 1 / (hmLowerWeight M R hR a b hab x hbx).1
  · have hax : R a x := hm_reverse_rel_of_not_strict hR hxa
    have hxb : R x b := hm_reverse_rel_of_not_strict hR hbx
    exact (hmBetweenCoefficient M R hR a x b hax hxb).1

theorem hmUtility_of_upper
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X)
    (hxa : HMStrict R x a) :
    hmUtility M R hR a b hab x =
      1 / (hmUpperWeight M R hR a b hab x hxa).1 := by
  simp [hmUtility, hxa]

theorem hmUtility_of_lower
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X)
    (hbx : HMStrict R b x) :
    hmUtility M R hR a b hab x =
      1 - 1 / (hmLowerWeight M R hR a b hab x hbx).1 := by
  have hnotUpper : ¬ HMStrict R x a := by
    intro hxa
    exact hab.2 (hm_strict_trans hR hbx hxa).1
  simp [hmUtility, hnotUpper, hbx]

theorem hmUtility_of_middle
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X)
    (hnotUpper : ¬ HMStrict R x a)
    (hnotLower : ¬ HMStrict R b x) :
    hmUtility M R hR a b hab x =
      (hmBetweenCoefficient M R hR a x b
        (hm_reverse_rel_of_not_strict hR hnotUpper)
        (hm_reverse_rel_of_not_strict hR hnotLower)).1 := by
  simp [hmUtility, hnotUpper, hnotLower]

theorem hmUtility_gt_one_of_upper
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X)
    (hxa : HMStrict R x a) :
    1 < hmUtility M R hR a b hab x := by
  rw [hmUtility_of_upper M R hR a b hab x hxa]
  have hp := hmUpperWeight_mem_Ioo M R hR a b hab x hxa
  exact one_lt_one_div hp.1 hp.2

theorem hmUtility_le_one_of_not_upper
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X)
    (hnotUpper : ¬ HMStrict R x a) :
    hmUtility M R hR a b hab x ≤ 1 := by
  by_cases hbx : HMStrict R b x
  · rw [hmUtility_of_lower M R hR a b hab x hbx]
    have hq := hmLowerWeight_mem_Ioo M R hR a b hab x hbx
    have : 0 < 1 / (hmLowerWeight M R hR a b hab x hbx).1 :=
      one_div_pos.mpr hq.1
    linarith
  · rw [hmUtility_of_middle M R hR a b hab x hnotUpper hbx]
    exact (hmBetweenCoefficient M R hR a x b
      (hm_reverse_rel_of_not_strict hR hnotUpper)
      (hm_reverse_rel_of_not_strict hR hbx)).2.2

theorem hmUtility_lt_zero_of_lower
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X)
    (hbx : HMStrict R b x) :
    hmUtility M R hR a b hab x < 0 := by
  rw [hmUtility_of_lower M R hR a b hab x hbx]
  have hq := hmLowerWeight_mem_Ioo M R hR a b hab x hbx
  have hone : 1 < 1 / (hmLowerWeight M R hR a b hab x hbx).1 :=
    one_lt_one_div hq.1 hq.2
  linarith

theorem hmUtility_nonneg_of_not_lower
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x : X)
    (hnotLower : ¬ HMStrict R b x) :
    0 ≤ hmUtility M R hR a b hab x := by
  by_cases hxa : HMStrict R x a
  · rw [hmUtility_of_upper M R hR a b hab x hxa]
    exact (one_div_pos.mpr
      (hmUpperWeight_mem_Ioo M R hR a b hab x hxa).1).le
  · rw [hmUtility_of_middle M R hR a b hab x hxa hnotLower]
    exact (hmBetweenCoefficient M R hR a x b
      (hm_reverse_rel_of_not_strict hR hxa)
      (hm_reverse_rel_of_not_strict hR hnotLower)).2.1

/-- The normalized calibration represents the weak order globally. -/
theorem hmUtility_represents
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b) (x y : X) :
    R x y ↔ hmUtility M R hR a b hab x ≥
      hmUtility M R hR a b hab y := by
  classical
  by_cases hxa : HMStrict R x a
  · by_cases hya : HMStrict R y a
    · rw [hmUtility_of_upper M R hR a b hab x hxa,
        hmUtility_of_upper M R hR a b hab y hya,
        hm_upper_rel_iff_weight_le M R hR a b hab x y hxa hya]
      exact (one_div_le_one_div
        (hmUpperWeight_mem_Ioo M R hR a b hab y hya).1
        (hmUpperWeight_mem_Ioo M R hR a b hab x hxa).1).symm
    · have hxy : HMStrict R x y := by
        have hay : R a y := hm_reverse_rel_of_not_strict hR hya
        exact
          ⟨hR.transitive x a y hxa.1 hay,
            fun hyx => hxa.2 (hR.transitive a y x hay hyx)⟩
      constructor
      · intro _h
        exact le_of_lt (lt_of_le_of_lt
          (hmUtility_le_one_of_not_upper M R hR a b hab y hya)
          (hmUtility_gt_one_of_upper M R hR a b hab x hxa))
      · intro _h
        exact hxy.1
  · by_cases hya : HMStrict R y a
    · have hyx : HMStrict R y x := by
        have hax : R a x := hm_reverse_rel_of_not_strict hR hxa
        exact
          ⟨hR.transitive y a x hya.1 hax,
            fun hxy => hya.2 (hR.transitive a x y hax hxy)⟩
      constructor
      · intro hxy
        exact (hyx.2 hxy).elim
      · intro huv
        have hxle :=
          hmUtility_le_one_of_not_upper M R hR a b hab x hxa
        have hygt :=
          hmUtility_gt_one_of_upper M R hR a b hab y hya
        linarith
    · by_cases hbx : HMStrict R b x
      · by_cases hby : HMStrict R b y
        · rw [hmUtility_of_lower M R hR a b hab x hbx,
            hmUtility_of_lower M R hR a b hab y hby,
            hm_lower_rel_iff_weight_ge M R hR a b hab x y hbx hby]
          have hqx :=
            (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).1
          have hqy :=
            (hmLowerWeight_mem_Ioo M R hR a b hab y hby).1
          constructor
          · intro hq
            have := (one_div_le_one_div hqx hqy).mpr hq
            linarith
          · intro hu
            have hdiv :
                1 / (hmLowerWeight M R hR a b hab x hbx).1 ≤
                  1 / (hmLowerWeight M R hR a b hab y hby).1 := by
              linarith
            exact (one_div_le_one_div hqx hqy).mp hdiv
        · have hyx : HMStrict R y x := by
            have hyb : R y b := hm_reverse_rel_of_not_strict hR hby
            exact
              ⟨hR.transitive y b x hyb hbx.1,
                fun hxy => hbx.2 (hR.transitive x y b hxy hyb)⟩
          constructor
          · intro hxy
            exact (hyx.2 hxy).elim
          · intro huv
            have hxlt :=
              hmUtility_lt_zero_of_lower M R hR a b hab x hbx
            have hynonneg :=
              hmUtility_nonneg_of_not_lower M R hR a b hab y hby
            linarith
      · by_cases hby : HMStrict R b y
        · have hxy : HMStrict R x y := by
            have hxb : R x b := hm_reverse_rel_of_not_strict hR hbx
            exact
              ⟨hR.transitive x b y hxb hby.1,
                fun hyx => hby.2 (hR.transitive y x b hyx hxb)⟩
          constructor
          · intro _h
            exact le_of_lt (lt_of_lt_of_le
              (hmUtility_lt_zero_of_lower M R hR a b hab y hby)
              (hmUtility_nonneg_of_not_lower M R hR a b hab x hbx))
          · intro _h
            exact hxy.1
        · rw [hmUtility_of_middle M R hR a b hab x hxa hbx,
            hmUtility_of_middle M R hR a b hab y hya hby]
          exact hm_middle_rel_iff_coefficient_ge M R hR a b hab x y
            (hm_reverse_rel_of_not_strict hR hxa)
            (hm_reverse_rel_of_not_strict hR hbx)
            (hm_reverse_rel_of_not_strict hR hya)
            (hm_reverse_rel_of_not_strict hR hby)

/-!
## Affinity of the calibrated utility

The following coordinate identities supply the algebraic part of the
standard Herstein--Milnor proof.
-/

/-- Mixtures distribute over mixtures with a common second component. -/
theorem hm_mix_distrib
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (p t : Set.Ioo (0 : ℝ) 1) (x y z : X) :
    M.mix p (M.mix t x z) (M.mix t y z) =
      M.mix t (M.mix p x y) z := by
  apply M.coordinate_ext
  intro k
  repeat' rw [M.coordinate_mix]
  ring

/-- Mixing two points on the same standard segment mixes their scalar
coefficients. -/
theorem hm_mix_segments
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (p : Set.Ioo (0 : ℝ) 1) (s t c : HMUnitInterval)
    (a b : X)
    (hc : c.1 = p.1 * s.1 + (1 - p.1) * t.1) :
    M.mix p (hmSegment M s a b) (hmSegment M t a b) =
      hmSegment M c a b := by
  apply M.coordinate_ext
  intro k
  rw [M.coordinate_mix, hmSegment_coordinate, hmSegment_coordinate,
    hmSegment_coordinate, hc]
  ring

/-- Middle-case dilution: a point already calibrated between the anchors
mixes with the midpoint exactly as its scalar value does. -/
theorem hm_middle_dilution
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hnotUpper : ¬ HMStrict R x a)
    (hnotLower : ¬ HMStrict R b x)
    (lam : Set.Ioo (0 : ℝ) 1) (c : HMUnitInterval)
    (hc : c.1 =
      lam.1 * hmUtility M R hR a b hab x +
        (1 - lam.1) * (1 / 2 : ℝ)) :
    HMIndiff R
      (M.mix lam x (hmSegment M hmUnitHalf a b))
      (hmSegment M c a b) := by
  let tx :=
    hmBetweenCoefficient M R hR a x b
      (hm_reverse_rel_of_not_strict hR hnotUpper)
      (hm_reverse_rel_of_not_strict hR hnotLower)
  have hxspec :=
    hmBetweenCoefficient_spec M R hR a x b
      (hm_reverse_rel_of_not_strict hR hnotUpper)
      (hm_reverse_rel_of_not_strict hR hnotLower)
  have hmix :=
    (hm_indiff_mix_iff hR x (hmSegment M tx a b)
      (hmSegment M hmUnitHalf a b) lam).mp hxspec
  have hcoeff : c.1 =
      lam.1 * tx.1 + (1 - lam.1) * hmUnitHalf.1 := by
    rw [hc, hmUtility_of_middle M R hR a b hab x hnotUpper hnotLower]
    rfl
  have heq :=
    hm_mix_segments M lam tx hmUnitHalf c a b hcoeff
  rwa [heq] at hmix

/-- Upper-case dilution, proved by applying independence once at the
calibrating weight. -/
theorem hm_upper_dilution
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hxa : HMStrict R x a)
    (lam : Set.Ioo (0 : ℝ) 1) (c : HMUnitInterval)
    (hc : c.1 =
      lam.1 * hmUtility M R hR a b hab x +
        (1 - lam.1) * (1 / 2 : ℝ)) :
    HMIndiff R
      (M.mix lam x (hmSegment M hmUnitHalf a b))
      (hmSegment M c a b) := by
  let p := hmUpperWeight M R hR a b hab x hxa
  let pi : Set.Ioo (0 : ℝ) 1 :=
    ⟨p.1, (hmUpperWeight_mem_Ioo M R hR a b hab x hxa).1,
      (hmUpperWeight_mem_Ioo M R hR a b hab x hxa).2⟩
  let mid := hmSegment M hmUnitHalf a b
  let dx := M.mix lam x mid
  let db := M.mix lam b mid
  let da := M.mix lam a mid
  have hpspec := hmUpperWeight_spec M R hR a b hab x hxa
  change HMIndiff R a (hmSegment M p x b) at hpspec
  have hpseg : hmSegment M p x b = M.mix pi x b :=
    hmSegment_eq_mix M pi x b
  rw [hpseg] at hpspec
  have hleftEq : M.mix pi dx db = M.mix lam (M.mix pi x b) mid := by
    exact hm_mix_distrib M pi lam x b mid
  have hleftIndiff : HMIndiff R (M.mix pi dx db) da := by
    rw [hleftEq]
    exact
      (hm_indiff_mix_iff hR (M.mix pi x b) a mid lam).mp
        (hm_indiff_symm hpspec)
  have hrightEq : M.mix pi (hmSegment M c a b) db = da := by
    have hpne : p.1 ≠ 0 :=
      ne_of_gt (hmUpperWeight_mem_Ioo M R hR a b hab x hxa).1
    apply M.coordinate_ext
    intro k
    rw [M.coordinate_mix, hmSegment_coordinate, M.coordinate_mix,
      hmSegment_coordinate, M.coordinate_mix, hmSegment_coordinate]
    rw [hc, hmUtility_of_upper M R hR a b hab x hxa]
    change
      p.1 *
          ((lam.1 * (1 / p.1) + (1 - lam.1) * (1 / 2 : ℝ)) *
              M.coordinate a k +
            (1 -
                (lam.1 * (1 / p.1) +
                  (1 - lam.1) * (1 / 2 : ℝ))) *
              M.coordinate b k) +
        (1 - p.1) *
          (lam.1 * M.coordinate b k +
            (1 - lam.1) *
              ((1 / 2 : ℝ) * M.coordinate a k +
                (1 - (1 / 2 : ℝ)) * M.coordinate b k)) =
        lam.1 * M.coordinate a k +
          (1 - lam.1) *
            ((1 / 2 : ℝ) * M.coordinate a k +
              (1 - (1 / 2 : ℝ)) * M.coordinate b k)
    field_simp [hpne]
    ring
  have hmixed :
      HMIndiff R (M.mix pi dx db)
        (M.mix pi (hmSegment M c a b) db) := by
    rw [hrightEq]
    exact hleftIndiff
  exact
    (hm_indiff_mix_iff hR dx (hmSegment M c a b) db pi).mpr hmixed

/-- Lower-case dilution, symmetric to the upper case after swapping the
calibrating anchor. -/
theorem hm_lower_dilution
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (hbx : HMStrict R b x)
    (lam : Set.Ioo (0 : ℝ) 1) (c : HMUnitInterval)
    (hc : c.1 =
      lam.1 * hmUtility M R hR a b hab x +
        (1 - lam.1) * (1 / 2 : ℝ)) :
    HMIndiff R
      (M.mix lam x (hmSegment M hmUnitHalf a b))
      (hmSegment M c a b) := by
  let q := hmLowerWeight M R hR a b hab x hbx
  let qi : Set.Ioo (0 : ℝ) 1 :=
    ⟨q.1, (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).1,
      (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).2⟩
  let mid := hmSegment M hmUnitHalf a b
  let dx := M.mix lam x mid
  let da := M.mix lam a mid
  let db := M.mix lam b mid
  have hqspec := hmLowerWeight_spec M R hR a b hab x hbx
  change HMIndiff R b (M.mix qi x a) at hqspec
  have hleftEq : M.mix qi dx da = M.mix lam (M.mix qi x a) mid := by
    exact hm_mix_distrib M qi lam x a mid
  have hleftIndiff : HMIndiff R (M.mix qi dx da) db := by
    rw [hleftEq]
    exact
      (hm_indiff_mix_iff hR (M.mix qi x a) b mid lam).mp
        (hm_indiff_symm hqspec)
  have hrightEq : M.mix qi (hmSegment M c a b) da = db := by
    have hqne : q.1 ≠ 0 :=
      ne_of_gt (hmLowerWeight_mem_Ioo M R hR a b hab x hbx).1
    apply M.coordinate_ext
    intro k
    rw [M.coordinate_mix, hmSegment_coordinate, M.coordinate_mix,
      hmSegment_coordinate, M.coordinate_mix, hmSegment_coordinate]
    rw [hc, hmUtility_of_lower M R hR a b hab x hbx]
    change
      q.1 *
          ((lam.1 * (1 - 1 / q.1) +
                (1 - lam.1) * (1 / 2 : ℝ)) *
              M.coordinate a k +
            (1 -
                (lam.1 * (1 - 1 / q.1) +
                  (1 - lam.1) * (1 / 2 : ℝ))) *
              M.coordinate b k) +
        (1 - q.1) *
          (lam.1 * M.coordinate a k +
            (1 - lam.1) *
              ((1 / 2 : ℝ) * M.coordinate a k +
                (1 - (1 / 2 : ℝ)) * M.coordinate b k)) =
        lam.1 * M.coordinate b k +
          (1 - lam.1) *
            ((1 / 2 : ℝ) * M.coordinate a k +
              (1 - (1 / 2 : ℝ)) * M.coordinate b k)
    field_simp [hqne]
    ring
  have hmixed :
      HMIndiff R (M.mix qi dx da)
        (M.mix qi (hmSegment M c a b) da) := by
    rw [hrightEq]
    exact hleftIndiff
  exact
    (hm_indiff_mix_iff hR dx (hmSegment M c a b) da qi).mpr hmixed

/-- Every point, whether below, between, or above the anchors, becomes
equivalent after a small common dilution to the standard segment point with
the correspondingly diluted scalar value. -/
theorem hm_dilution
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (x : X) (lam : Set.Ioo (0 : ℝ) 1) (c : HMUnitInterval)
    (hc : c.1 =
      lam.1 * hmUtility M R hR a b hab x +
        (1 - lam.1) * (1 / 2 : ℝ)) :
    HMIndiff R
      (M.mix lam x (hmSegment M hmUnitHalf a b))
      (hmSegment M c a b) := by
  by_cases hxa : HMStrict R x a
  · exact hm_upper_dilution M R hR a b hab x hxa lam c hc
  by_cases hbx : HMStrict R b x
  · exact hm_lower_dilution M R hR a b hab x hbx lam c hc
  · exact hm_middle_dilution M R hR a b hab x hxa hbx lam c hc

/-- A single sufficiently small positive dilution sends any three real
numbers into the open unit interval around the midpoint.  This elementary
lemma is the only boundedness device needed for global affinity. -/
theorem hm_exists_common_dilution_coefficients (ux uy uz : ℝ) :
    ∃ (lam : Set.Ioo (0 : ℝ) 1) (cx cy cz : HMUnitInterval),
      cx.1 = lam.1 * ux + (1 - lam.1) * (1 / 2 : ℝ) ∧
      cy.1 = lam.1 * uy + (1 - lam.1) * (1 / 2 : ℝ) ∧
      cz.1 = lam.1 * uz + (1 - lam.1) * (1 / 2 : ℝ) := by
  let lseq : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hlseq : Tendsto lseq atTop (𝓝 0) := by
    simpa [lseq] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hcoeff (v : ℝ) :
      Tendsto
        (fun n => lseq n * v + (1 - lseq n) * (1 / 2 : ℝ))
        atTop (𝓝 (1 / 2 : ℝ)) := by
    have hv :
        Tendsto (fun _ : ℕ => v) atTop (𝓝 v) :=
      tendsto_const_nhds
    have hone :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have hhalf :
        Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    simpa using (hlseq.mul hv).add ((hone.sub hlseq).mul hhalf)
  have hnhds : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 (1 / 2 : ℝ) :=
    isOpen_Ioo.mem_nhds (by norm_num)
  have hux :
      ∀ᶠ n in atTop,
        lseq n * ux + (1 - lseq n) * (1 / 2 : ℝ) ∈
          Set.Ioo (0 : ℝ) 1 :=
    (hcoeff ux).eventually hnhds
  have huy :
      ∀ᶠ n in atTop,
        lseq n * uy + (1 - lseq n) * (1 / 2 : ℝ) ∈
          Set.Ioo (0 : ℝ) 1 :=
    (hcoeff uy).eventually hnhds
  have huz :
      ∀ᶠ n in atTop,
        lseq n * uz + (1 - lseq n) * (1 / 2 : ℝ) ∈
          Set.Ioo (0 : ℝ) 1 :=
    (hcoeff uz).eventually hnhds
  have hnpos : ∀ᶠ n : ℕ in atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => by omega⟩
  rcases (hux.and (huy.and (huz.and hnpos))).exists with
    ⟨n, hcx, hcy, hcz, hn⟩
  have hden : 1 < (n : ℝ) + 1 := by
    exact_mod_cast (Nat.succ_lt_succ hn)
  have hlamPos : 0 < lseq n := by
    dsimp [lseq]
    positivity
  have hlamLt : lseq n < 1 := by
    have hrecip :
        1 / ((n : ℝ) + 1) < 1 / (1 : ℝ) :=
      (one_div_lt_one_div (by positivity) zero_lt_one).2 hden
    simpa [lseq] using hrecip
  let lam : Set.Ioo (0 : ℝ) 1 := ⟨lseq n, hlamPos, hlamLt⟩
  let cx : HMUnitInterval :=
    ⟨lseq n * ux + (1 - lseq n) * (1 / 2 : ℝ),
      le_of_lt hcx.1, le_of_lt hcx.2⟩
  let cy : HMUnitInterval :=
    ⟨lseq n * uy + (1 - lseq n) * (1 / 2 : ℝ),
      le_of_lt hcy.1, le_of_lt hcy.2⟩
  let cz : HMUnitInterval :=
    ⟨lseq n * uz + (1 - lseq n) * (1 / 2 : ℝ),
      le_of_lt hcz.1, le_of_lt hcz.2⟩
  exact ⟨lam, cx, cy, cz, rfl, rfl, rfl⟩

/-- The globally normalized calibration is affine for the primitive
interior mixture operation.  The proof dilutes both inputs and their mixture
by one common positive weight, then invokes uniqueness on the strict anchor
segment and cancels that weight. -/
theorem hmUtility_affine
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R)
    (a b : X) (hab : HMStrict R a b)
    (t : Set.Ioo (0 : ℝ) 1) (x y : X) :
    hmUtility M R hR a b hab (M.mix t x y) =
      t.1 * hmUtility M R hR a b hab x +
        (1 - t.1) * hmUtility M R hR a b hab y := by
  obtain ⟨lam, cx, cy, cz, hcx, hcy, hcz⟩ :=
    hm_exists_common_dilution_coefficients
      (hmUtility M R hR a b hab x)
      (hmUtility M R hR a b hab y)
      (hmUtility M R hR a b hab (M.mix t x y))
  let mid := hmSegment M hmUnitHalf a b
  have hxcal :
      HMIndiff R (M.mix lam x mid) (hmSegment M cx a b) :=
    hm_dilution M R hR a b hab x lam cx hcx
  have hycal :
      HMIndiff R (M.mix lam y mid) (hmSegment M cy a b) :=
    hm_dilution M R hR a b hab y lam cy hcy
  have hzcal :
      HMIndiff R (M.mix lam (M.mix t x y) mid)
        (hmSegment M cz a b) :=
    hm_dilution M R hR a b hab (M.mix t x y) lam cz hcz
  have htNonneg : 0 ≤ t.1 := le_of_lt t.2.1
  have hOneSubNonneg : 0 ≤ 1 - t.1 := by
    linarith [t.2.2]
  have hcxyNonneg :
      0 ≤ t.1 * cx.1 + (1 - t.1) * cy.1 :=
    add_nonneg
      (mul_nonneg htNonneg cx.2.1)
      (mul_nonneg hOneSubNonneg cy.2.1)
  have hcxyLe :
      t.1 * cx.1 + (1 - t.1) * cy.1 ≤ 1 := by
    calc
      t.1 * cx.1 + (1 - t.1) * cy.1
          ≤ t.1 * 1 + (1 - t.1) * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left cx.2.2 htNonneg)
          (mul_le_mul_of_nonneg_left cy.2.2 hOneSubNonneg)
      _ = 1 := by ring
  let cxy : HMUnitInterval :=
    ⟨t.1 * cx.1 + (1 - t.1) * cy.1, hcxyNonneg, hcxyLe⟩
  have hcalibratedMix :
      HMIndiff R
        (M.mix t (M.mix lam x mid) (M.mix lam y mid))
        (M.mix t (hmSegment M cx a b) (hmSegment M cy a b)) :=
    hm_mix_indiff_congr hR hxcal hycal t
  have hdistrib :
      M.mix t (M.mix lam x mid) (M.mix lam y mid) =
        M.mix lam (M.mix t x y) mid :=
    hm_mix_distrib M t lam x y mid
  have hsegmentMix :
      M.mix t (hmSegment M cx a b) (hmSegment M cy a b) =
        hmSegment M cxy a b :=
    hm_mix_segments M t cx cy cxy a b rfl
  have hzcal' :
      HMIndiff R (M.mix lam (M.mix t x y) mid)
        (hmSegment M cxy a b) := by
    rw [← hdistrib, ← hsegmentMix]
    exact hcalibratedMix
  have hcoeffEq : cz = cxy :=
    hm_indifferent_segment_unique M R hR hab hzcal hzcal'
  have hvals : cz.1 = cxy.1 :=
    congrArg Subtype.val hcoeffEq
  dsimp only [cxy] at hvals
  rw [hcz, hcx, hcy] at hvals
  have hscaled :
      lam.1 * hmUtility M R hR a b hab (M.mix t x y) =
        lam.1 *
          (t.1 * hmUtility M R hR a b hab x +
            (1 - t.1) * hmUtility M R hR a b hab y) := by
    calc
      lam.1 * hmUtility M R hR a b hab (M.mix t x y) =
          (lam.1 * hmUtility M R hR a b hab (M.mix t x y) +
            (1 - lam.1) * (1 / 2 : ℝ)) -
            (1 - lam.1) * (1 / 2 : ℝ) := by ring
      _ =
          (t.1 *
              (lam.1 * hmUtility M R hR a b hab x +
                (1 - lam.1) * (1 / 2 : ℝ)) +
            (1 - t.1) *
              (lam.1 * hmUtility M R hR a b hab y +
                (1 - lam.1) * (1 / 2 : ℝ))) -
            (1 - lam.1) * (1 / 2 : ℝ) := by rw [hvals]
      _ =
          lam.1 *
            (t.1 * hmUtility M R hR a b hab x +
              (1 - t.1) * hmUtility M R hR a b hab y) := by ring
  exact mul_left_cancel₀ (ne_of_gt lam.2.1) hscaled

/-- Exact generic Herstein--Milnor representation theorem from segment
calibration.  This is the smallest hypothesis actually consumed by the
standard-sequence construction. -/
theorem genericHersteinMilnorAffineUtility_of_calibratable
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : HMCalibratableWeakOrder M R) :
    Nonempty (AffineUtilityRepresentation M R) := by
  classical
  by_cases hstrict : ∃ a b : X, HMStrict R a b
  · rcases hstrict with ⟨a, b, hab⟩
    exact
      ⟨{
        utility := hmUtility M R hR a b hab
        represents := hmUtility_represents M R hR a b hab
        affine := hmUtility_affine M R hR a b hab
      }⟩
  · exact
      ⟨{
        utility := fun _ => 0
        represents := by
          intro x y
          constructor
          · intro _hxy
            norm_num
          · intro _hzero
            rcases hR.complete x y with hxy | hyx
            · exact hxy
            · by_contra hnxy
              exact hstrict ⟨y, x, hyx, hnxy⟩
        affine := by
          intro t x y
          simp
      }⟩

/-- Exact generic Herstein--Milnor representation theorem for this
development's original sequentially closed/interior-mixture schema. -/
theorem genericHersteinMilnorAffineUtility
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) (hR : ContinuousIndependentWeakOrder M R) :
    Nonempty (AffineUtilityRepresentation M R) :=
  genericHersteinMilnorAffineUtility_of_calibratable M R
    (HMCalibratableWeakOrder.ofContinuous hR)

/-- A closed Lean term inhabiting the formerly external generic HM theorem
assumption.  In particular, downstream results may use this theorem without
adding any new mathematical axiom or interface field. -/
theorem genericHersteinMilnorMixtureTheorem :
    ClassicalHersteinMilnorMixtureTheoremAssumptions.{u} where
  affine_utility := by
    intro X M R hR
    exact genericHersteinMilnorAffineUtility M R hR

end TraceableAgency
