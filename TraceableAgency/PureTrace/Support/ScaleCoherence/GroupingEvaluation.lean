/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence.ProductInteraction

namespace TraceableAgency

universe u

/-!
### Deriving the two-grouping evaluations E1/E2 from the weight recursion (W)

The labelled disjoint union `T = ½(u⊗u)⁰ ⊔ ½(v⊗v)¹` is presented as a
`sigmaDist` in two ways: grouped by the top label, and grouped by the pair
(label, first within-block coordinate).  The weight recursion evaluates both;
exact relabeling identifies the two presentations; multiplicativity of `Z`
turns `w(u⊗u)` into `w(u)²`.  Everything below is the paper's Lemma
scalecoherence Step 3 up to (E1)/(E2), with no entropy or universal scale.
-/

/-- `sigmaDist` of full-support pieces is full-support. -/
theorem sigmaDist_fullSupport
    {K : Type u} [Fintype K] {Act : K → Type u}
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (f : ∀ k, Dist (Act k))
    (hp : p.FullSupport) (hf : ∀ k, (f k).FullSupport) :
    (sigmaDist p f).FullSupport := by
  intro ka
  rcases ka with ⟨k, a⟩
  rw [sigmaDist_apply]
  exact mul_pos (hp k) (hf k a)

/-- Sum over the two-point reference label type. -/
theorem sum_universalScaleReferenceType
    (g : universalScaleReferenceType → ℝ) :
    (∑ k : universalScaleReferenceType, g k) =
      g (ULift.up false) + g (ULift.up true) := by
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp g]
  simp [Fintype.sum_bool, Equiv.ulift]
  ring

/-- The uniform reference prior puts mass `1/2` on each label. -/
theorem universalScaleReferencePrior_apply
    (k : universalScaleReferenceType.{u}) :
    universalScaleReferencePrior k = 1 / 2 := by
  have hcard : Fintype.card universalScaleReferenceType.{u} = 2 := by
    simp [universalScaleReferenceType]
  simp [universalScaleReferencePrior, Dist.uniform_apply, hcard]

/-- A product with a nonsubsingleton factor is nonsubsingleton. -/
theorem not_subsingleton_prod_left
    {α β : Type u} [Nonempty β]
    (hα : ¬ Subsingleton α) : ¬ Subsingleton (α × β) := by
  intro hsub
  apply hα
  obtain ⟨b⟩ : Nonempty β := inferInstance
  constructor
  intro a a'
  have := Subsingleton.elim (α := α × β) (a, b) (a', b)
  exact congrArg Prod.fst this

/-- A sigma with a nonsubsingleton base and nonempty fibers is
nonsubsingleton. -/
theorem not_subsingleton_sigma
    {K : Type u} {Act : K → Type u} [∀ k, Nonempty (Act k)]
    (hK : ¬ Subsingleton K) : ¬ Subsingleton ((k : K) × Act k) := by
  intro hsub
  apply hK
  constructor
  intro k k'
  have := Subsingleton.elim (α := (k : K) × Act k)
    ⟨k, Classical.choice inferInstance⟩ ⟨k', Classical.choice inferInstance⟩
  exact congrArg Sigma.fst this

/-- Two-case fiber family over the two-point reference label type. -/
def twoGroupingFiber (U V : Type u) : universalScaleReferenceType → Type u
  | ⟨false⟩ => U
  | ⟨true⟩ => V

noncomputable instance twoGroupingFiberFintype
    {U V : Type u} [Fintype U] [Fintype V] :
    ∀ k, Fintype (twoGroupingFiber U V k)
  | ⟨false⟩ => show Fintype U from inferInstance
  | ⟨true⟩ => show Fintype V from inferInstance

instance twoGroupingFiberDecidableEq
    {U V : Type u} [DecidableEq U] [DecidableEq V] :
    ∀ k, DecidableEq (twoGroupingFiber U V k)
  | ⟨false⟩ => show DecidableEq U from inferInstance
  | ⟨true⟩ => show DecidableEq V from inferInstance

instance twoGroupingFiberNonempty
    {U V : Type u} [Nonempty U] [Nonempty V] :
    ∀ k, Nonempty (twoGroupingFiber U V k)
  | ⟨false⟩ => show Nonempty U from inferInstance
  | ⟨true⟩ => show Nonempty V from inferInstance

/-- The two block conditionals of the two-grouping disjoint union. -/
noncomputable def twoGroupingConditional
    {U V : Type u} [Fintype U] [Fintype V]
    (u : Dist U) (v : Dist V) :
    ∀ k, Dist (twoGroupingFiber U V k)
  | ⟨false⟩ => u
  | ⟨true⟩ => v

/-- Reassociation of the two sigma presentations of the two-grouping
disjoint union. -/
def twoGroupingReassoc (U V : Type u) :
    ((ka : (k : universalScaleReferenceType) × twoGroupingFiber U V k) ×
        twoGroupingFiber U V ka.1) ≃
      ((k : universalScaleReferenceType) ×
        (twoGroupingFiber U V k × twoGroupingFiber U V k)) where
  toFun := fun x => ⟨x.1.1, (x.1.2, x.2)⟩
  invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun x => rfl
  right_inv := fun x => rfl

/-- The fine sigma presentation relabels onto the coarse one. -/
theorem relabelDist_twoGroupingReassoc
    {U V : Type u}
    [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V]
    (u : Dist U) (v : Dist V) :
    Relabeling.relabelDist (twoGroupingReassoc U V)
        (sigmaDist
          (sigmaDist universalScaleReferencePrior
            (twoGroupingConditional u v))
          (fun ka => twoGroupingConditional u v ka.1)) =
      sigmaDist universalScaleReferencePrior
        (fun k => prodDist (twoGroupingConditional u v k)
          (twoGroupingConditional u v k)) := by
  ext x
  rcases x with ⟨k, a, b⟩
  show (sigmaDist
      (sigmaDist universalScaleReferencePrior (twoGroupingConditional u v))
      (fun ka => twoGroupingConditional u v ka.1))
        ((twoGroupingReassoc U V).symm ⟨k, (a, b)⟩) =
    (sigmaDist universalScaleReferencePrior
      (fun k => prodDist (twoGroupingConditional u v k)
        (twoGroupingConditional u v k))) ⟨k, (a, b)⟩
  show (sigmaDist universalScaleReferencePrior (twoGroupingConditional u v))
        ⟨k, a⟩ * (twoGroupingConditional u v k) b =
    universalScaleReferencePrior k *
      (prodDist (twoGroupingConditional u v k)
        (twoGroupingConditional u v k)) (a, b)
  rw [sigmaDist_apply, prodDist_apply_pair]
  ring

/-- **E1/E2 derived from the pre-universal weight recursion.**

The two evaluations of `w(T)` for the labelled disjoint union
`T = ½(u⊗u)⁰ ⊔ ½(v⊗v)¹` follow from:

* the weight recursion (W) applied to the coarse grouping of `T` (E1),
* the weight recursion applied twice — to the fine grouping of `T` and to its
  coarse marginal `S = ½u⁰ ⊔ ½v¹` (E2),
* exact relabeling between the two sigma presentations of `T`
  (`hrelV` + `relabelDist_twoGroupingReassoc`),
* multiplicativity `Z(x ⊗ x) = Z(x)²`
  (`productScaleZForFaceScales_prod_eq`), and
* `Z`-positivity for the reference weight `wp = w(p₂) > 0`.

This upgrades the two-grouping target: its remaining source is exactly the
weight recursion (W). -/
theorem finiteProductTwoGroupingWeightEquation_of_weightRecursion
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hrec :
      FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod where
  reference_Z_eq_one := hrec.reference_Z_eq_one
  two_grouping_evaluations := by
    intro hax U V _ _ _ _ _ _ u v hu hv hU hV
    classical
    -- Setup: label type, fibers, conditionals.
    set K := universalScaleReferenceType with hK
    set p₂ := universalScaleReferencePrior with hp₂
    have hp₂fs : p₂.FullSupport := universalScaleReferencePrior_fullSupport
    have hKnd : ¬ Subsingleton K := universalScaleReference_not_subsingleton
    set g := twoGroupingConditional u v with hg
    have hgfs : ∀ k, (g k).FullSupport := by
      intro k
      rcases k with ⟨b⟩
      cases b
      · exact hu
      · exact hv
    have hgnd : ∀ k, ¬ Subsingleton (twoGroupingFiber U V k) := by
      intro k
      rcases k with ⟨b⟩
      cases b
      · exact hU
      · exact hV
    -- Coarse presentation T and fine marginal S.
    set f := fun k => prodDist (g k) (g k) with hf
    have hffs : ∀ k, (f k).FullSupport := fun k =>
      prodDist_fullSupport (g k) (g k) (hgfs k) (hgfs k)
    have hfnd : ∀ k, ¬ Subsingleton (twoGroupingFiber U V k ×
        twoGroupingFiber U V k) := fun k =>
      not_subsingleton_prod_left (hgnd k)
    set T := sigmaDist p₂ f with hT
    set S := sigmaDist p₂ g with hS
    have hTfs : T.FullSupport := sigmaDist_fullSupport p₂ f hp₂fs hffs
    have hSfs : S.FullSupport := sigmaDist_fullSupport p₂ g hp₂fs hgfs
    haveI : Nonempty ((k : K) × (twoGroupingFiber U V k ×
        twoGroupingFiber U V k)) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    haveI : Nonempty ((k : K) × twoGroupingFiber U V k) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    -- Fine presentation T' over the coarse marginal S.
    set f' := fun (ka : (k : K) × twoGroupingFiber U V k) => g ka.1 with hf'
    have hf'fs : ∀ ka : (k : K) × twoGroupingFiber U V k,
        (f' ka).FullSupport :=
      fun ka => hgfs ka.1
    have hf'nd : ∀ ka : (k : K) × twoGroupingFiber U V k,
        ¬ Subsingleton (twoGroupingFiber U V ka.1) :=
      fun ka => hgnd ka.1
    set T' := sigmaDist S f' with hT'
    have hT'fs : T'.FullSupport := sigmaDist_fullSupport S f' hSfs hf'fs
    haveI :
        Nonempty ((ka : (k : K) × twoGroupingFiber U V k) ×
          twoGroupingFiber U V ka.1) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    have hSnd : ¬ Subsingleton ((k : K) × twoGroupingFiber U V k) :=
      not_subsingleton_sigma hKnd
    -- Exact relabeling identifies the two presentations: Z(T') = Z(T).
    have hHrel :
        fullRevelationValueForFaceScales hfaces
            (Relabeling.relabelDist (twoGroupingReassoc U V) T') =
          fullRevelationValueForFaceScales hfaces T' :=
      fullRevelationValueForFaceScales_relabel_eq hrelV hax hfaces
        (twoGroupingReassoc U V) T'
    have hTeq : Relabeling.relabelDist (twoGroupingReassoc U V) T' = T :=
      relabelDist_twoGroupingReassoc u v
    have hZTT' : productScaleZForFaceScales hfaces hprod hax T = productScaleZForFaceScales hfaces hprod hax T' := by
      unfold productScaleZForFaceScales
      rw [← hTeq, hHrel]
    -- Weight recursion, coarse grouping: E1 before multiplicativity.
    have hrecT :=
      hrec.weight_recursion hax
        (fun k : K => twoGroupingFiber U V k × twoGroupingFiber U V k)
        p₂ f hp₂fs hffs hTfs hKnd hfnd
    -- Weight recursion, fine grouping and its coarse marginal.
    have hrecT' :=
      hrec.weight_recursion hax
        (fun ka : (k : K) × twoGroupingFiber U V k =>
          twoGroupingFiber U V ka.1)
        S f' hSfs hf'fs hT'fs hSnd hf'nd
    have hrecS :=
      hrec.weight_recursion hax (twoGroupingFiber U V)
        p₂ g hp₂fs hgfs hSfs hKnd hgnd
    -- Abbreviations for the two weights.
    set x := (productScaleZForFaceScales hfaces hprod hax u)⁻¹ with hx
    set y := (productScaleZForFaceScales hfaces hprod hax v)⁻¹ with hy
    -- The coarse sum: Σ p₂ k · w(f k) = (x² + y²)/2, via multiplicativity.
    have hsum_f :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹) = (x ^ 2 + y ^ 2) / 2 := by
      rw [sum_universalScaleReferenceType
        (fun k => p₂ k * (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹)]
      have hZff : productScaleZForFaceScales hfaces hprod hax (f (ULift.up false)) = productScaleZForFaceScales hfaces hprod hax u * productScaleZForFaceScales hfaces hprod hax u := by
        show productScaleZForFaceScales hfaces hprod hax
            (prodDist u u) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax u u hu hu
      have hZft : productScaleZForFaceScales hfaces hprod hax (f (ULift.up true)) = productScaleZForFaceScales hfaces hprod hax v * productScaleZForFaceScales hfaces hprod hax v := by
        show productScaleZForFaceScales hfaces hprod hax
            (prodDist v v) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax v v hv hv
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply,
        hZff, hZft, mul_inv, mul_inv]
      show 1 / 2 * ((productScaleZForFaceScales hfaces hprod hax u)⁻¹ * (productScaleZForFaceScales hfaces hprod hax u)⁻¹) + 1 / 2 * ((productScaleZForFaceScales hfaces hprod hax v)⁻¹ * (productScaleZForFaceScales hfaces hprod hax v)⁻¹) = _
      rw [← hx, ← hy]
      ring
    -- The fine sums: both marginal sums are (x + y)/2.
    have hsum_g :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) = (x + y) / 2 := by
      rw [sum_universalScaleReferenceType (fun k => p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹)]
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply]
      show 1 / 2 * (productScaleZForFaceScales hfaces hprod hax u)⁻¹ + 1 / 2 * (productScaleZForFaceScales hfaces hprod hax v)⁻¹ = _
      rw [← hx, ← hy]
      ring
    have hsum_f' :
        (∑ ka : (k : K) × twoGroupingFiber U V k,
          S ka * (productScaleZForFaceScales hfaces hprod hax (f' ka))⁻¹) = (x + y) / 2 := by
      rw [Fintype.sum_sigma]
      have hterm :
          ∀ k, (∑ a : twoGroupingFiber U V k,
              S ⟨k, a⟩ * (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹) =
            p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
        intro k
        have : ∀ a : twoGroupingFiber U V k,
            S ⟨k, a⟩ * (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹ =
              p₂ k * (g k) a * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
          intro a
          show (sigmaDist p₂ g) ⟨k, a⟩ * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ = _
          rw [sigmaDist_apply]
        rw [Finset.sum_congr rfl (fun a _ => this a)]
        have hfactor :
            (∑ a : twoGroupingFiber U V k,
              p₂ k * (g k) a * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) =
              (p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) * (∑ a, (g k) a) := by
          rw [Finset.mul_sum]
          congr 1
          ext a
          ring
        rw [hfactor, (g k).sum_eq_one, mul_one]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      exact hsum_g
    -- Reference weight is positive.
    have hZp₂pos : 0 < productScaleZForFaceScales hfaces hprod hax p₂ := hpos.Z_pos hax p₂ hp₂fs
    -- Assemble E1 and E2 with wT := w(T), wp := w(p₂).
    refine ⟨(productScaleZForFaceScales hfaces hprod hax T)⁻¹, (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹, inv_pos.mpr hZp₂pos, ?_, ?_⟩
    · -- E1: coarse grouping.
      rw [show (productScaleZForFaceScales hfaces hprod hax T)⁻¹ =
          (productScaleZForFaceScales hfaces hprod hax (sigmaDist p₂ f))⁻¹
        from rfl]
      rw [hrecT, hsum_f]
    · -- E2: fine grouping + coarse marginal, transported by relabeling.
      have hE2' :
          (productScaleZForFaceScales hfaces hprod hax T')⁻¹ = (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹ * (((x + y) / 2) ^ 2) := by
        rw [show (productScaleZForFaceScales hfaces hprod hax T')⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist S f'))⁻¹
          from rfl]
        rw [hrecT', hsum_f']
        rw [show (productScaleZForFaceScales hfaces hprod hax S)⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax S)⁻¹ from rfl]
        rw [show (productScaleZForFaceScales hfaces hprod hax S)⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p₂ g))⁻¹
          from rfl]
        rw [hrecS, hsum_g]
        ring
      rw [hZTT']
      exact hE2'

/-- Sharper source-ready grouping bridge.

The paper's finite partition/disjoint-union grouping argument first makes the
`Z` weight independent of the nondegenerate full-support prior, and then fixes
that common value by a reference normalization.  This structure records those
two pieces separately from the downstream cancellation to `kappa = 0`. -/
structure FiniteProductGroupingReferenceWeightAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  Z_eq_reference_of_grouping :
    ∀ (hax : PureTraceConditions F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hA : ¬ Subsingleton A),
      productScaleZForFaceScales hfaces hprod hax q =
        productScaleZForFaceScales hfaces hprod hax
          universalScaleReferencePrior
  reference_Z_eq_one :
    ∀ (hax : PureTraceConditions F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- Reconstruct the old weight-constant package from the sharper grouping
reference-weight bridge. -/
theorem productGroupingWeightConstant_of_reference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod) :
    FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod where
  Z_eq_one_of_nondegenerate := by
    intro hax A _ _ _ q hq hA
    calc
      productScaleZForFaceScales hfaces hprod hax q =
          productScaleZForFaceScales hfaces hprod hax
            universalScaleReferencePrior :=
        hgroup.Z_eq_reference_of_grouping hax q hq hA
      _ = 1 := hgroup.reference_Z_eq_one hax

/-- **Repaired grouping equation ⟹ reference-weight package.**

The paper's two-grouping evaluations plus `Z`-positivity reconstruct the
reference-weight package that the interaction-collapse constructor consumes.
The `Z`-equal-to-reference field is the two-grouping cancellation
(`productScaleZ_eq_of_twoGrouping`); the reference normalization is supplied
directly.  This is the faithful reduction of the grouping equation: everything
downstream of the paper's two evaluations is now proved in Lean. -/
theorem productGroupingReferenceWeight_of_twoGroupingWeightEquation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod where
  Z_eq_reference_of_grouping := by
    intro hax A _ _ _ q hq hA
    exact productScaleZ_eq_of_twoGrouping hgroup hpos hax q
      universalScaleReferencePrior hq universalScaleReferencePrior_fullSupport
      hA universalScaleReference_not_subsingleton
  reference_Z_eq_one := hgroup.reference_Z_eq_one

/-- The final algebraic cancellation in Step 3: if the grouping argument makes
`Z` identically one on nondegenerate full-support priors, then `kappa = 0`. -/
theorem twoGroupingInteractionCollapse_of_weightConstant
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod) :
    FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod where
  kappa_eq_zero := by
    intro hax
    let q0 : Dist universalScaleReferenceType := universalScaleReferencePrior
    have hq0 : q0.FullSupport := universalScaleReferencePrior_fullSupport
    have hRef : ¬ Subsingleton universalScaleReferenceType :=
      universalScaleReference_not_subsingleton
    have hZ :=
      hweight.Z_eq_one_of_nondegenerate hax q0 hq0 hRef
    have hH_ne :
        fullRevelationValueForFaceScales hfaces q0 ≠ 0 :=
      fullRevelationValueForFaceScales_ne_zero_of_A1
        hfaces hax q0 hq0 hRef
    have hkH :
        hprod.kappa hax * fullRevelationValueForFaceScales hfaces q0 = 0 := by
      unfold productScaleZForFaceScales at hZ
      linarith
    exact (mul_eq_zero.mp hkH).resolve_right hH_ne

/-- Product-revelation scale links plus `kappa = 0` imply universal scale on
nondegenerate full-support priors. -/
theorem scale_eq_of_productRevelation_and_interactionCollapse
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hax : PureTraceConditions F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hfaces.branch_result.scale_factorization.scale q =
      hfaces.branch_result.scale_factorization.scale r := by
  have hleft :=
    hlink.scale_product_left hax q r hq hr hA hB
  have hright :=
    hlink.scale_product_right hax q r hq hr hA hB
  have hleft' :
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        hfaces.branch_result.scale_factorization.scale r := by
    simpa [hcollapse.kappa_eq_zero hax] using hleft
  have hright' :
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        hfaces.branch_result.scale_factorization.scale q := by
    simpa [hcollapse.kappa_eq_zero hax] using hright
  exact hright'.symm.trans hleft'

/-- Universal scale for all full-support priors from the nondegenerate product
argument plus the singleton/degenerate normalization. -/
theorem scale_universal_of_productRevelation_and_interactionCollapse
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hfaces.branch_result.scale_factorization.scale q =
      hfaces.branch_result.scale_factorization.scale r := by
  by_cases hA : Subsingleton A
  · exact hsingle.scale_eq_of_subsingleton q r hq hr (Or.inl hA)
  · by_cases hB : Subsingleton B
    · exact hsingle.scale_eq_of_subsingleton q r hq hr (Or.inr hB)
    · exact scale_eq_of_productRevelation_and_interactionCollapse
        hfaces hprod hlink hcollapse hax q r hq hr hA hB

/-- Reassemble the public `ScaleCoherenceStructure` from faithful face scales
and the sharp interaction-collapse components. -/
noncomputable def scaleCoherence_of_faceScales_interactionCollapse
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    ScaleCoherenceStructure F where
  branch_agg := hfaces.branch_result.branch_agg
  scale := hfaces.branch_result.scale_factorization.scale
  scale_pos := hfaces.branch_result.scale_factorization.scale_pos
  branchCoeff_factorization :=
    hfaces.branch_result.scale_factorization.branchCoeff_factorization
  scale_universal := by
    intro A B _ _ _ _ _ _ q r hq hr
    exact scale_universal_of_productRevelation_and_interactionCollapse
      hfaces hprod hlink hcollapse hsingle hax q r hq hr

/-- Faithful output package for "Interaction collapse and universal chain
scale". -/
structure InteractionCollapseUniversalChainScaleStructure
    (F : PrefFamily.{u}) where
  face_scales : CoherentRelabelingFaceScalesStructure F
  product_quasi_add :
    FiniteProductQuasiAdditivityForFaceScales face_scales
  scale_coherence : ScaleCoherenceStructure F
  interaction_collapse :
    ∀ (hax : PureTraceConditions F), product_quasi_add.kappa hax = 0

namespace InteractionCollapseUniversalChainScaleStructure

/-- The universal chain-scale output. -/
theorem scale_universal
    {F : PrefFamily.{u}}
    (h : InteractionCollapseUniversalChainScaleStructure F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    h.scale_coherence.scale q = h.scale_coherence.scale r :=
  h.scale_coherence.scale_universal q r hq hr

/-- Product additivity after the interaction coefficient collapses. -/
theorem product_additivity
    {F : PrefFamily.{u}}
    (h : InteractionCollapseUniversalChainScaleStructure F)
    (hax : PureTraceConditions F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    h.face_scales.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      h.face_scales.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel P) +
      h.face_scales.branch_result.branch_agg.value_rep.V r
        (experimentOfChannel R) := by
  have hqa :=
    h.product_quasi_add.product_quasi_add hax q r hq hr P R
  simpa [h.interaction_collapse hax] using hqa

end InteractionCollapseUniversalChainScaleStructure

/-- Faithful theorem statement for "Interaction collapse and universal chain
scale". -/
noncomputable def InteractionCollapseUniversalScale_of_faithfulFaceScales
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F where
  face_scales := hfaces
  product_quasi_add := hprod
  scale_coherence :=
    scaleCoherence_of_faceScales_interactionCollapse
      hfaces hprod hlink hcollapse hsingle hax
  interaction_collapse := hcollapse.kappa_eq_zero

/-- Stage 27 reassembler for "Interaction collapse and universal chain
scale" using the sharper product-revelation and two-grouping inputs. -/
noncomputable def InteractionCollapseUniversalScale_of_decomposedProductBridges
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hseq : FiniteProductRevelationSequentialScaleAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_faithfulFaceScales
    hfaces hprod
    (productRevelationScaleLink_of_sequentialScale hfaces hprod hseq)
    (twoGroupingInteractionCollapse_of_weightConstant hfaces hprod hweight)
    hsingle hax

/-- Stage 28 reassembler using the normalized-chain full-revelation form of
the product-revelation Step 1 bridge. -/
noncomputable def InteractionCollapseUniversalScale_of_normalizedSequentialProduct
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hnorm :
      FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_decomposedProductBridges
    hfaces hprod
    (productRevelationSequentialScale_of_normalizedChain hfaces hnorm)
    hweight hsingle hax

/-- Stage 29 reassembler using the coordinate-reveal value and continuation
transport pieces directly. -/
noncomputable def InteractionCollapseUniversalScale_of_coordinateRevealTransports
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hvalue : FiniteCoordinateRevealValueTransportAssumptionsFor hfaces)
    (hcont :
      FiniteCoordinateRevealContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_normalizedSequentialProduct
    hfaces hprod
    (sequentialFullRevelationNormalizedChain_of_coordinateTransports
      hfaces hvalue hcont)
    hweight hsingle hax

/-- Stage 30 reassembler using the sharper coordinate transport pieces. -/
noncomputable def InteractionCollapseUniversalScale_of_coordinateTransportPieces
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hmarg :
      FiniteCoordinateRevealMarginalValueTransportAssumptionsFor hfaces)
    (hswap :
      FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces)
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_coordinateRevealTransports
    hfaces hprod
    (coordinateRevealValueTransport_of_marginal_and_swap hmarg hswap)
    (coordinateRevealContinuationTransport_of_branchTransport hbranch)
    hweight hsingle hax

/-- Stage IC cleanup reassembler: the marginal coordinate-reveal value
transport is derived internally from product quasi-additivity, so this
constructor takes only the swap and coordinate-face continuation transports as
coordinate residuals. -/
noncomputable def InteractionCollapseUniversalScale_of_productQuasiAndCoordinatePieces
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hswap :
      FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces)
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_coordinateTransportPieces
    hfaces hprod
    (coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
      hfaces hprod)
    hswap hbranch hweight hsingle hax

/-- Stage IC all-residual cleanup reassembler: both coordinate-reveal marginal
value transport and swapped full-revelation transport are internal, so the only
coordinate residual left is pointwise coordinate-face continuation transport. -/
noncomputable def InteractionCollapseUniversalScale_of_productQuasiAndBranchContinuation
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_productQuasiAndCoordinatePieces
    hfaces hprod
    (coordinateSwapFullRevelationValueTransport_of_posteriorLaw hfaces)
    hbranch hweight hsingle hax

/-- Minimal current faithful reassembler for the interaction-collapse route
after the coordinate-reveal cleanup.

The swap full-revelation and marginal coordinate-reveal value transports are
internal.  The coordinate continuation residual is reduced to the two exact
support-face transports: value representatives and chain scales. -/
noncomputable def InteractionCollapseUniversalScale_of_minimalResiduals
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hcoordValue :
      FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_productQuasiAndBranchContinuation
    hfaces hprod
    (coordinateRevealBranchContinuationTransport_of_coordinateSupportFaceTransports
      hcoordValue hcoordScale)
    hweight hsingle hax

/-- Interaction-collapse reassembler using the non-circular face-scale product
components instead of the already assembled product quasi-additivity package. -/
noncomputable def InteractionCollapseUniversalScale_of_productComponents
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm :
      FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (huniv :
      FiniteFaceScaleProductInteractionUniversalityAssumptionsFor hpair)
    (hcoordValue :
      FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces)
    (hweight :
      FiniteProductGroupingWeightConstantAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_components
          hpair hnorm huniv))
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_components hpair hnorm huniv)
    hcoordValue hcoordScale hweight hsingle hax

/-- Final current interaction-collapse constructor.

This uses the smallest named product and coordinate components currently
available in this file: explicit product current-gauge normalization,
interaction K-associativity plus singleton normalization, and coordinate
support-face representative/scale normalizations. -/
noncomputable def InteractionCollapseUniversalScale_of_finalComponents
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair)
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hweight :
      FiniteProductGroupingWeightConstantAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_finalProductComponents
          hpair hgauge hassoc hinterSingle))
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_finalProductComponents
      hpair hgauge hassoc hinterSingle)
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    hweight hunivSingle hax

/-- Interaction-collapse constructor using the multi-stage source-ready
components instead of the broader pairwise, interaction-associativity, and
weight-constant packages. -/
noncomputable def InteractionCollapseUniversalScale_of_multiClosedComponents
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        htriple)
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope))
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hweight :
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_multiComponents
          haff hintercept hslope hgauge htriple hextract hinterSingle))
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_multiComponents
      haff hintercept hslope hgauge htriple hextract hinterSingle)
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    (productGroupingWeightConstant_of_reference hweight)
    hunivSingle hax

/-- Closed-local left-slice affine transform constructor.

This removes the old face-scale-specific affine-utility uniqueness package from
the interaction-collapse API: the non-singleton case is supplied by the single
classical finite affine-utility uniqueness theorem, and nonconstancy is internal
from A1. -/
theorem faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces :=
  faceScaleProductLeftSliceAffineTransform_of_parts
    hbaseAff hsliceAff hsameOrder
    (faceScaleBaseValueNonconstancy_of_A1 hfaces)
    hsingle
    (classicalFaceScaleAffineUtilityUniqueness_of_finiteAffineUtility huniq)

/-- Closed-local pairwise bilinearity constructor.

This keeps the second-coordinate intercept uniqueness and slope-affinity theorem
pieces explicit, but no longer requires an intercept-zero interface: zero is
proved internally from subsingleton no-information value normalization. -/
noncomputable def faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hinterceptOrder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptAff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptUniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq))) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces :=
  let haff :=
    faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
      hbaseAff hsliceAff hsameOrder hsingle huniq
  let hlin :=
    faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
      hinterceptOrder hinterceptAff hinterceptUniq
  faceScaleProductPairwiseBilinearity_of_multiPieces haff hlin hslope

/-- Product quasi-additivity from the closed-local IC theorem pieces.

The triple-product value associativity package is no longer an explicit input;
it is reconstructed from exact relabeling of posterior-value representatives. -/
noncomputable def productQuasiAdditivityForFaceScales_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hinterceptOrder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptAff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptUniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        (faceScaleTripleProductValueAssociativity_of_valueRelabeling
          hfaces hrelV))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope)) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  let haff :=
    faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
      hbaseAff hsliceAff hsameOrder hsingle huniq
  let hlin :=
    faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
      hinterceptOrder hinterceptAff hinterceptUniq
  productQuasiAdditivityForFaceScales_of_multiComponents
    haff hlin hslope hgauge
    (faceScaleTripleProductValueAssociativity_of_valueRelabeling hfaces hrelV)
    hextract hinterSingle

/-- Family-level product representation theorem for the pre-universal
face-scale layer.

This is deliberately not another local interface for one residual.  It groups
the remaining HM/product-coordinate content behind coherent product
quasi-additivity: public-mix affinity, product-coordinate order transport,
intercept/slope affine uniqueness, and triple-product coefficient extraction.
It replaces seven local theorem externals plus the coefficient-extraction
external in the public interaction-collapse constructor. -/
structure FiniteFaceScaleProductRepresentationTheoremAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  base_publicMix :
    FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces
  coordinate_publicMix :
    FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces
  left_slice_same_order :
    FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces
  intercept_same_order :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  intercept_publicMix :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  second_coordinate_uniqueness :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  slope_affine :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  triple_coeff_extraction :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v})
      (hgauge :
        FiniteFaceScaleCurrentProductGaugeNormalizationFor
          (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq
            (intercept_same_order hsingle huniq)
            (intercept_publicMix hsingle huniq)
            (second_coordinate_uniqueness hsingle huniq)
            (slope_affine hsingle huniq)))
      (hrelV : FinitePosteriorValueRelabelingAssumptions.{v}),
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          base_publicMix coordinate_publicMix left_slice_same_order
          hsingle huniq
          (intercept_same_order hsingle huniq)
          (intercept_publicMix hsingle huniq)
          (second_coordinate_uniqueness hsingle huniq)
          (slope_affine hsingle huniq))
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        (faceScaleTripleProductValueAssociativity_of_valueRelabeling
          hfaces hrelV)

/-- Product quasi-additivity reconstructed from the family-level product
representation theorem. -/
noncomputable def productQuasiAdditivityForFaceScales_of_productRepresentation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprodRep :
      FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq)))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq))) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  productQuasiAdditivityForFaceScales_of_closedLocalTheorems
    hprodRep.base_publicMix
    hprodRep.coordinate_publicMix
    hprodRep.left_slice_same_order
    hsingle huniq
    (hprodRep.intercept_same_order hsingle huniq)
    (hprodRep.intercept_publicMix hsingle huniq)
    (hprodRep.second_coordinate_uniqueness hsingle huniq)
    (hprodRep.slope_affine hsingle huniq)
    hgauge hrelV
    (hprodRep.triple_coeff_extraction hsingle huniq hgauge hrelV)
    hinterSingle

/-- Family-level grouping equation theorem.

This replaces the local `FiniteProductGroupingReferenceWeightAssumptionsFor`
for each product-quasi-additivity package.  The intended proof is the paper's
finite partition/disjoint-union grouping equation, followed by the already
internal reference-weight algebra. -/
structure FiniteProductGroupingEquationAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  reference_weight :
    ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod

/-- Reference-weight package reconstructed from the family-level grouping
equation theorem. -/
theorem productGroupingReferenceWeight_of_groupingEquation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hgroup :
      FiniteProductGroupingEquationAssumptionsFor hfaces)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) :
    FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod :=
  hgroup.reference_weight hprod

/-- Cleanest current interaction-collapse constructor after local closure.

Compared with `InteractionCollapseUniversalScale_of_multiClosedComponents`, this
does not expose the old intercept-zero, face-scale-specific affine-uniqueness,
or triple-product value-associativity packages.  Remaining theorem inputs are
the public-mix/order/slope/coefficient/grouping statements that have not been
proved locally, plus explicit gauge/support-face/singleton normalizations. -/
noncomputable def InteractionCollapseUniversalScale_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hinterceptOrder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptAff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptUniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        (faceScaleTripleProductValueAssociativity_of_valueRelabeling
          hfaces hrelV))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope))
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hweight :
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope
          hgauge hrelV hextract hinterSingle))
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_closedLocalTheorems
      hbaseAff hsliceAff hsameOrder hsingle huniq
      hinterceptOrder hinterceptAff hinterceptUniq hslope
      hgauge hrelV hextract hinterSingle)
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    (productGroupingWeightConstant_of_reference hweight)
    hunivSingle hax

/-- Total-closure interaction-collapse constructor.

This is the strictest current API: the nine remaining local theorem externals
are not exposed.  They are replaced by two family-level theorem assumptions:
one coherent product-representation theorem and one finite grouping-equation
theorem.  Existing global classical/relabeling inputs remain explicit. -/
noncomputable def InteractionCollapseUniversalScale_of_totalClosure
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprodRep :
      FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq)))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq)))
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hgroup :
      FiniteProductGroupingEquationAssumptionsFor hfaces)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : PureTraceConditions F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  let hprod :=
    productQuasiAdditivityForFaceScales_of_productRepresentation
      hprodRep hsingle huniq hgauge hrelV hinterSingle
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces hprod
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    (productGroupingWeightConstant_of_reference
      (productGroupingReferenceWeight_of_groupingEquation hgroup hprod))
    hunivSingle hax

/-- Family-level grouping equation reconstructed from the repaired two-grouping
weight equation plus `Z`-positivity.

This exposes the honest remaining product-grouping content — the paper's
two-grouping evaluations (E1)/(E2) and the positive-slice-slope condition
(POS) — instead of the opaque reference-weight package.  Everything downstream
(the `(x−y)²=0` cancellation, `Z ≡ 1`, `κ = 0`) is now proved in Lean. -/
theorem finiteProductGroupingEquation_of_twoGroupingWeightEquation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hgroup :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductGroupingEquationAssumptionsFor hfaces where
  reference_weight := fun hprod =>
    productGroupingReferenceWeight_of_twoGroupingWeightEquation
      (hgroup hprod) (hpos hprod)

/-- **Family-level grouping equation from the pre-universal weight recursion.**

POS is discharged internally (`productScaleZpositive_of_sliceTransform`), and
the two-grouping evaluations E1/E2 are derived from the weight recursion (W)
(`finiteProductTwoGroupingWeightEquation_of_weightRecursion`).  The remaining
product-grouping input is exactly the paper's weight equation (W). -/
theorem finiteProductGroupingEquation_of_weightRecursion
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hrec :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod) :
    FiniteProductGroupingEquationAssumptionsFor hfaces :=
  finiteProductGroupingEquation_of_twoGroupingWeightEquation
    (fun hprod =>
      finiteProductTwoGroupingWeightEquation_of_weightRecursion hrelV
        (hrec hprod)
        (productScaleZpositive_of_sliceTransform hprod haff))
    (fun hprod => productScaleZpositive_of_sliceTransform hprod haff)

end TraceableAgency
