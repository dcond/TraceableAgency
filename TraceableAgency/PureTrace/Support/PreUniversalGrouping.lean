/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.SelectedRelabeling

/-!
# Pre-Universal Grouping Recursion

This file exposes the face-scale block-reveal identity needed before the
entropy/Faddeev layer and proves the algebraic conversion from the TeX grouping
recursion `(GR)` to the existing pre-universal weight equation `(W)`.
-/

namespace TraceableAgency

universe u

/--
The block-reveal channel for a dependent sum action type, defined here under a
pre-universal name to avoid depending on the downstream Faddeev module.
-/
noncomputable def preUniversalCoarseRevealChannel
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) :
    Channel ((k : K) × Act k) K :=
  fun ka => Dist.pure ka.1

/--
The exact pre-universal block-reveal value identity needed for the TeX `(BG)`
step.  This is intentionally earlier than W: it identifies the selected
face-scale value of the block-reveal experiment with full revelation of the
coarse prior.
-/
structure FinitePreUniversalBlockRevealValueFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_reveal_value_eq_fullRevelationValue :
    ∀ (_hax : PureTraceConditions F)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (f : ∀ k, Dist (Act k))
      (_hp : p.FullSupport)
      (_hf : ∀ k, (f k).FullSupport)
      (_hsigma : (sigmaDist p f).FullSupport),
      hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
          (experimentOfChannel
            (preUniversalCoarseRevealChannel (K := K) Act)) =
        fullRevelationValueForFaceScales hfaces p

/--
The pre-universal grouping recursion `(GR)` from the TeX proof, stated before
the final `w = Z⁻¹` algebraic rearrangement.
-/
structure FinitePreUniversalGroupingGRFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  grouping_GR :
    ∀ (hax : PureTraceConditions F)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (f : ∀ k, Dist (Act k))
      (_hp : p.FullSupport)
      (_hf : ∀ k, (f k).FullSupport)
      (_hsigma : (sigmaDist p f).FullSupport)
      (_hKnd : ¬ Subsingleton K)
      (_hAnd : ∀ k, ¬ Subsingleton (Act k)),
      fullRevelationValueForFaceScales hfaces (sigmaDist p f) =
        fullRevelationValueForFaceScales hfaces p +
          productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k))
  reference_Z_eq_one :
    ∀ (hax : PureTraceConditions F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- Real algebra converting the TeX `(GR)` equation to `(W)`. -/
private theorem weightRecursion_algebra_of_groupingGR
    {K : Type u} [Fintype K]
    (p : Dist K)
    (κ Hsigma Hp : ℝ) (Hf : K → ℝ)
    (hZsigma_pos : 0 < 1 + κ * Hsigma)
    (hZp_pos : 0 < 1 + κ * Hp)
    (hZf_pos : ∀ k, 0 < 1 + κ * Hf k)
    (hGR :
      Hsigma =
        Hp + (1 + κ * Hsigma) *
          ∑ k, p k * (Hf k / (1 + κ * Hf k))) :
    (1 + κ * Hsigma)⁻¹ =
      (1 + κ * Hp)⁻¹ * ∑ k, p k * (1 + κ * Hf k)⁻¹ := by
  classical
  by_cases hκ : κ = 0
  · simp [hκ, p.sum_eq_one]
  · let Zsigma : ℝ := 1 + κ * Hsigma
    let Zp : ℝ := 1 + κ * Hp
    let Zf : K → ℝ := fun k => 1 + κ * Hf k
    let S : ℝ := ∑ k, p k * (Zf k)⁻¹
    let T : ℝ := ∑ k, p k * (Hf k / Zf k)
    have hZsigma_ne : Zsigma ≠ 0 := ne_of_gt (by simpa [Zsigma] using hZsigma_pos)
    have hZp_ne : Zp ≠ 0 := ne_of_gt (by simpa [Zp] using hZp_pos)
    have hZf_ne : ∀ k, Zf k ≠ 0 := fun k =>
      ne_of_gt (by simpa [Zf] using hZf_pos k)
    have hGR' : Hsigma = Hp + Zsigma * T := by
      simpa [Zsigma, Zf, T] using hGR
    have hκT : κ * T = 1 - S := by
      have hsum :
          ∑ k, κ * (p k * (Hf k / Zf k)) =
            ∑ k, p k * (1 - (Zf k)⁻¹) := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        have hz : Zf k = 1 + κ * Hf k := rfl
        have hz_ne : Zf k ≠ 0 := hZf_ne k
        field_simp [hz_ne, hκ, Zf]
        ring
      calc
        κ * T = ∑ k, κ * (p k * (Hf k / Zf k)) := by
          simp [T, Finset.mul_sum]
        _ = ∑ k, p k * (1 - (Zf k)⁻¹) := hsum
        _ = ∑ k, (p k - p k * (Zf k)⁻¹) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          ring
        _ = ∑ k, p k - ∑ k, p k * (Zf k)⁻¹ := by
          rw [Finset.sum_sub_distrib]
        _ = 1 - S := by
          simp [S, p.sum_eq_one]
    have hZeq : Zsigma = Zp + Zsigma * (1 - S) := by
      calc
        Zsigma = 1 + κ * Hsigma := rfl
        _ = 1 + κ * (Hp + Zsigma * T) := by rw [hGR']
        _ = Zp + Zsigma * (κ * T) := by
          ring
        _ = Zp + Zsigma * (1 - S) := by rw [hκT]
    have hZp_eq : Zp = Zsigma * S := by
      nlinarith [hZeq]
    have hS_ne : S ≠ 0 := by
      intro hS
      exact hZp_ne (by rw [hZp_eq, hS, mul_zero])
    have hmain : Zsigma⁻¹ = Zp⁻¹ * S := by
      rw [hZp_eq]
      field_simp [hZsigma_ne, hS_ne]
    simpa [Zsigma, Zp, Zf, S] using hmain

/--
Convert the pre-universal grouping recursion `(GR)` into the existing weight
recursion `(W)`.  This theorem uses only face-scale objects plus POS for `Z`.
-/
theorem finitePreUniversalGroupingWeightRecursion_of_GR
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hGR : FinitePreUniversalGroupingGRFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod where
  weight_recursion := by
    intro hax K _ _ _ Act _ _ _ _ p f hp hf hsigma hKnd hAnd
    have hgr :=
      hGR.grouping_GR hax Act p f hp hf hsigma hKnd hAnd
    have hsigma_pos :=
      hpos.Z_pos hax (sigmaDist p f) hsigma
    have hp_pos :=
      hpos.Z_pos hax p hp
    have hf_pos : ∀ k,
        0 < productScaleZForFaceScales hfaces hprod hax (f k) := fun k =>
      hpos.Z_pos hax (f k) (hf k)
    simpa [productScaleZForFaceScales] using
      weightRecursion_algebra_of_groupingGR
        p (hprod.kappa hax)
        (fullRevelationValueForFaceScales hfaces (sigmaDist p f))
        (fullRevelationValueForFaceScales hfaces p)
        (fun k => fullRevelationValueForFaceScales hfaces (f k))
        (by simpa [productScaleZForFaceScales] using hsigma_pos)
        (by simpa [productScaleZForFaceScales] using hp_pos)
        (fun k => by
          simpa [productScaleZForFaceScales] using hf_pos k)
        (by simpa [productScaleZForFaceScales] using hgr)
  reference_Z_eq_one := hGR.reference_Z_eq_one

end TraceableAgency
