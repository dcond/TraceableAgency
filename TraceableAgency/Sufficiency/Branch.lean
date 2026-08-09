/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import Mathlib
import TraceableAgency.External.CanonicalPosteriorValue
import TraceableAgency.External.FiniteIntegralRepresentation
import TraceableAgency.External.ScaleCoherence

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
# A direct affine linear part on posterior-law differences

This file develops the algebraic extension needed by the paper's tangent-space
branch proof.  It deliberately uses only law extensionality and finite-mixture
affinity of a `PosteriorValueRepresentation`.  In particular, no pointwise
posterior integrand is selected.
-/

/-- The free linear combination of posterior laws induced by experiments at
one prior. -/
noncomputable def experimentPosteriorLawMap
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    (FiniteExperimentOn A →₀ ℝ) →ₗ[ℝ] PosteriorLawSigned A :=
  Finsupp.linearCombination ℝ (posteriorLawSignedOfExperiment q)

/-- The corresponding free linear combination of selected posterior values. -/
noncomputable def experimentPosteriorValueMap
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    (FiniteExperimentOn A →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (hV.V q)

@[simp] theorem experimentPosteriorLawMap_single
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (c : ℝ) :
    experimentPosteriorLawMap q (Finsupp.single E c) =
      c • posteriorLawSignedOfExperiment q E := by
  simp [experimentPosteriorLawMap]

@[simp] theorem experimentPosteriorValueMap_single
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (c : ℝ) :
    experimentPosteriorValueMap hV q (Finsupp.single E c) = c * hV.V q E := by
  simp [experimentPosteriorValueMap]

@[simp] theorem experimentPosteriorLawMap_apply
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (c : FiniteExperimentOn A →₀ ℝ) (phi : Dist A → ℝ) :
    experimentPosteriorLawMap q c phi =
      c.sum fun E a => a * posteriorLawIntegralExp q E phi := by
  rw [experimentPosteriorLawMap, Finsupp.linearCombination_apply]
  classical
  simp [Finsupp.sum, posteriorLawSignedOfExperiment]

@[simp] theorem experimentPosteriorValueMap_apply
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (c : FiniteExperimentOn A →₀ ℝ) :
    experimentPosteriorValueMap hV q c =
      c.sum fun E a => a * hV.V q E := by
  rw [experimentPosteriorValueMap, Finsupp.linearCombination_apply]
  rfl

private theorem finsupp_sum_eq_supportSubtype_sum
    {X : Type u} (c : X →₀ ℝ) (f : X → ℝ → ℝ) :
    c.sum f = ∑ i : {x : X // x ∈ c.support}, f i.1 (c i.1) := by
  classical
  rw [Finsupp.sum, ← c.support.sum_attach]
  rfl

/-- Affinity makes every linear relation among implemented posterior laws a
linear relation among their selected values.  This is the key well-definedness
statement; its proof compares the normalized positive and negative parts as
two finite public mixtures. -/
theorem experimentPosteriorLawMap_ker_le_value_ker
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    LinearMap.ker (experimentPosteriorLawMap q) ≤
      LinearMap.ker (experimentPosteriorValueMap hV q) := by
  classical
  intro c hc
  apply LinearMap.mem_ker.mpr
  have hcLaw : experimentPosteriorLawMap q c = 0 :=
    LinearMap.mem_ker.mp hc
  by_cases hc0 : c = 0
  · simp [hc0]
  let J := {E : FiniteExperimentOn A // E ∈ c.support}
  letI : Fintype J := inferInstance
  let I := ULift.{u} (Fin (Fintype.card J))
  let e : I ≃ J :=
    Equiv.ulift.trans (Fintype.equivFin J).symm
  letI : Fintype I := inferInstance
  letI : DecidableEq I := inferInstance
  have hcoeffSum : ∑ i : I, c (e i).1 = 0 := by
    have hmass := congrFun hcLaw (fun _ => (1 : ℝ))
    rw [experimentPosteriorLawMap_apply] at hmass
    rw [finsupp_sum_eq_supportSubtype_sum] at hmass
    simp_rw [posteriorLawIntegralExp_const_one] at hmass
    calc
      ∑ i : I, c (e i).1 = ∑ j : J, c j.1 :=
        e.sum_comp (fun j : J => c j.1)
      _ = 0 := by simpa [J] using hmass
  have hpositive : ∃ i : I, 0 < c (e i).1 := by
    by_contra h
    push_neg at h
    have hallzero_fun : (fun i : I => c (e i).1) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonpos h).mp hcoeffSum
    have hallzero : ∀ i : I, c (e i).1 = 0 := fun i =>
      congrFun hallzero_fun i
    obtain ⟨E, hE⟩ := Finsupp.support_nonempty_iff.mpr hc0
    have hEc : c E ≠ 0 := Finsupp.mem_support_iff.mp hE
    have hz := hallzero (e.symm ⟨E, hE⟩)
    exact hEc (by simpa using hz)
  let T : ℝ := ∑ i : I, max (c (e i).1) 0
  have hTpos : 0 < T := by
    dsimp [T]
    apply Finset.sum_pos'
    · intro i _hi
      exact le_max_right _ _
    · obtain ⟨i, hi⟩ := hpositive
      exact ⟨i, Finset.mem_univ i, by simpa [hi.le] using hi⟩
  have hnegSum : ∑ i : I, max (-c (e i).1) 0 = T := by
    have hdiff :
        (∑ i : I, max (c (e i).1) 0) -
            ∑ i : I, max (-c (e i).1) 0 = 0 := by
      rw [← Finset.sum_sub_distrib]
      simpa [max_zero_sub_max_neg_zero_eq_self] using hcoeffSum
    dsimp [T]
    linarith
  let wpos : Dist I :=
    { prob := fun i => max (c (e i).1) 0 / T
      nonneg := by
        intro i
        exact div_nonneg (le_max_right _ _) hTpos.le
      sum_eq_one := by
        rw [← Finset.sum_div]
        exact div_self (ne_of_gt hTpos) }
  let wneg : Dist I :=
    { prob := fun i => max (-c (e i).1) 0 / T
      nonneg := by
        intro i
        exact div_nonneg (le_max_right _ _) hTpos.le
      sum_eq_one := by
        rw [← Finset.sum_div, hnegSum]
        exact div_self (ne_of_gt hTpos) }
  let Es : I → FiniteExperimentOn A := fun i => (e i).1
  have hsame :
      SamePosteriorLawExp q
        (finitePublicMixExperiment (A := A) (I := I) wpos Es)
        (finitePublicMixExperiment (A := A) (I := I) wneg Es) := by
    intro phi _hphi
    rw [posteriorLawIntegralExp_finitePublicMixExperiment,
      posteriorLawIntegralExp_finitePublicMixExperiment]
    have hzeroPhi := congrFun hcLaw phi
    rw [experimentPosteriorLawMap_apply] at hzeroPhi
    rw [finsupp_sum_eq_supportSubtype_sum] at hzeroPhi
    have hzeroPhiI :
        ∑ i : I, c (e i).1 * posteriorLawIntegralExp q (Es i) phi = 0 := by
      calc
        ∑ i : I, c (e i).1 * posteriorLawIntegralExp q (Es i) phi =
            ∑ j : J, c j.1 * posteriorLawIntegralExp q j.1 phi := by
              simpa [Es] using
                e.sum_comp
                  (fun j : J => c j.1 * posteriorLawIntegralExp q j.1 phi)
        _ = 0 := by simpa [J] using hzeroPhi
    have hsplit :
        (∑ i : I,
            max (c (e i).1) 0 * posteriorLawIntegralExp q (Es i) phi) =
          ∑ i : I,
            max (-c (e i).1) 0 * posteriorLawIntegralExp q (Es i) phi := by
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      calc
        ∑ i : I,
            (max (c (e i).1) 0 * posteriorLawIntegralExp q (Es i) phi -
              max (-c (e i).1) 0 * posteriorLawIntegralExp q (Es i) phi) =
            ∑ i : I, c (e i).1 * posteriorLawIntegralExp q (Es i) phi := by
              apply Finset.sum_congr rfl
              intro i _
              rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
        _ = 0 := hzeroPhiI
    dsimp [wpos, wneg]
    calc
      (∑ i : I,
          max (c (e i).1) 0 / T * posteriorLawIntegralExp q (Es i) phi) =
          (∑ i : I,
            max (c (e i).1) 0 * posteriorLawIntegralExp q (Es i) phi) / T := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i : I,
            max (-c (e i).1) 0 * posteriorLawIntegralExp q (Es i) phi) / T := by
              rw [hsplit]
      _ = ∑ i : I,
          max (-c (e i).1) 0 / T * posteriorLawIntegralExp q (Es i) phi := by
              rw [Finset.sum_div]
              apply Finset.sum_congr rfl
              intro i _
              ring
  have hmixValue :=
    hV.respects_same_posterior_law q
      (finitePublicMixExperiment (A := A) (I := I) wpos Es)
      (finitePublicMixExperiment (A := A) (I := I) wneg Es) hsame
  have hposValue :=
    affineValue_finitePublicMix q (hV.V q)
      (hV.respects_same_posterior_law q)
      (hV.affine_of_posteriorLawIntegral_mix q) wpos Es
  have hnegValue :=
    affineValue_finitePublicMix q (hV.V q)
      (hV.respects_same_posterior_law q)
      (hV.affine_of_posteriorLawIntegral_mix q) wneg Es
  rw [hposValue, hnegValue] at hmixValue
  have hweightedValue :
      (∑ i : I, max (c (e i).1) 0 * hV.V q (Es i)) =
        ∑ i : I, max (-c (e i).1) 0 * hV.V q (Es i) := by
    dsimp [wpos, wneg] at hmixValue
    have hposNorm :
        (∑ i : I, max (c (e i).1) 0 / T * hV.V q (Es i)) =
          (∑ i : I, max (c (e i).1) 0 * hV.V q (Es i)) / T := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hnegNorm :
        (∑ i : I, max (-c (e i).1) 0 / T * hV.V q (Es i)) =
          (∑ i : I, max (-c (e i).1) 0 * hV.V q (Es i)) / T := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hposNorm, hnegNorm] at hmixValue
    exact (div_left_inj' (ne_of_gt hTpos)).mp hmixValue
  have hvalueI : ∑ i : I, c (e i).1 * hV.V q (Es i) = 0 := by
    calc
      ∑ i : I, c (e i).1 * hV.V q (Es i) =
        ∑ i : I,
          (max (c (e i).1) 0 * hV.V q (Es i) -
            max (-c (e i).1) 0 * hV.V q (Es i)) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [← sub_mul, max_zero_sub_max_neg_zero_eq_self]
      _ = (∑ i : I, max (c (e i).1) 0 * hV.V q (Es i)) -
          ∑ i : I, max (-c (e i).1) 0 * hV.V q (Es i) := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hweightedValue
  rw [experimentPosteriorValueMap_apply,
    finsupp_sum_eq_supportSubtype_sum]
  calc
    ∑ j : J, c j.1 * hV.V q j.1 =
        ∑ i : I, c (e i).1 * hV.V q (Es i) := by
          simpa [Es] using
            (e.sum_comp (fun j : J => c j.1 * hV.V q j.1)).symm
    _ = 0 := hvalueI

/-- The value linear map on the span of implemented posterior laws, obtained
by quotienting the free experiment space by the kernel of its law map. -/
noncomputable def posteriorLawRangeValueLinearMap
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    LinearMap.range (experimentPosteriorLawMap q) →ₗ[ℝ] ℝ :=
  (LinearMap.ker (experimentPosteriorLawMap q)).liftQ
      (experimentPosteriorValueMap hV q)
      (experimentPosteriorLawMap_ker_le_value_ker hV q) ∘ₗ
    (experimentPosteriorLawMap q).quotKerEquivRange.symm.toLinearMap

@[simp] theorem posteriorLawRangeValueLinearMap_image
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (c : FiniteExperimentOn A →₀ ℝ) :
    posteriorLawRangeValueLinearMap hV q
        ⟨experimentPosteriorLawMap q c, ⟨c, rfl⟩⟩ =
      experimentPosteriorValueMap hV q c := by
  simp [posteriorLawRangeValueLinearMap]

/-- A classical linear extension from the implemented-law span to the whole
extensional signed-law space.  Values outside the implemented span are
irrelevant; all atomic tangent directions lie in the span by
`finiteAtomicPosteriorTangentSpanning`. -/
noncomputable def directPosteriorLawLinearMap
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : PosteriorLawSigned A →ₗ[ℝ] ℝ :=
  Classical.choose
    (LinearMap.exists_extend (posteriorLawRangeValueLinearMap hV q))

theorem directPosteriorLawLinearMap_comp_rangeSubtype
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    (directPosteriorLawLinearMap hV q).comp
        (LinearMap.range (experimentPosteriorLawMap q)).subtype =
      posteriorLawRangeValueLinearMap hV q :=
  Classical.choose_spec
    (LinearMap.exists_extend (posteriorLawRangeValueLinearMap hV q))

@[simp] theorem directPosteriorLawLinearMap_lawCombination
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (c : FiniteExperimentOn A →₀ ℝ) :
    directPosteriorLawLinearMap hV q (experimentPosteriorLawMap q c) =
      experimentPosteriorValueMap hV q c := by
  have hcomp := LinearMap.congr_fun
    (directPosteriorLawLinearMap_comp_rangeSubtype hV q)
    ⟨experimentPosteriorLawMap q c, ⟨c, rfl⟩⟩
  simpa using hcomp

/-- The free coefficient vector representing the difference of two
experiment laws. -/
noncomputable def experimentDifferenceFinsupp
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (E E' : FiniteExperimentOn A) : FiniteExperimentOn A →₀ ℝ :=
  Finsupp.single E 1 - Finsupp.single E' 1

@[simp] theorem experimentPosteriorLawMap_difference
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    experimentPosteriorLawMap q (experimentDifferenceFinsupp E E') =
      posteriorLawDifferenceExp q E E' := by
  rw [experimentDifferenceFinsupp, map_sub,
    experimentPosteriorLawMap_single, experimentPosteriorLawMap_single]
  ext phi
  simp [posteriorLawDifferenceExp, posteriorLawSignedOfExperiment]

@[simp] theorem experimentPosteriorValueMap_difference
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    experimentPosteriorValueMap hV q (experimentDifferenceFinsupp E E') =
      hV.V q E - hV.V q E' := by
  rw [experimentDifferenceFinsupp, map_sub,
    experimentPosteriorValueMap_single, experimentPosteriorValueMap_single]
  ring

/-- The direct linear part evaluates a feasible posterior-law difference as
the corresponding value difference. -/
theorem directPosteriorLawLinearMap_difference
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    directPosteriorLawLinearMap hV q (posteriorLawDifferenceExp q E E') =
      hV.V q E - hV.V q E' := by
  rw [← experimentPosteriorLawMap_difference q E E',
    directPosteriorLawLinearMap_lawCombination,
    experimentPosteriorValueMap_difference]

/-- Paper-faithful affine-linear-part producer.  It uses a quotient of finite
linear combinations of experiment laws followed by a linear extension.  No
posterior-separable integral representation or marginal value function occurs
in its type or construction. -/
noncomputable def finiteAffineLinearPartAssumptions_of_posteriorValue :
    FiniteAffineLinearPartAssumptions.{u} where
  linearPart := fun _F hV {_A} [_] [_] [_] q =>
    directPosteriorLawLinearMap hV q
  value_difference := by
    intro F hV A _ _ _ q E E'
    exact (directPosteriorLawLinearMap_difference hV q E E').symm
  linearPart_ext := by
    intro F hV A _ _ _ q eta zeta h
    apply congrArg (directPosteriorLawLinearMap hV q)
    funext phi
    exact h phi
  linearPart_add := by
    intro F hV A _ _ _ q eta zeta
    exact (directPosteriorLawLinearMap hV q).map_add eta zeta
  linearPart_smul := by
    intro F hV A _ _ _ q c eta
    exact (directPosteriorLawLinearMap hV q).map_smul c eta

/-- Exact selected-value covariance forces the direct linear part to commute
with finite action relabelling on atomic tangent directions.  The arbitrary
linear extension away from the feasible-law span is therefore immaterial. -/
theorem directPosteriorLawLinearMap_relabel_atomicTangent
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    (hrelab :
      ∀ {A B O Y : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        [Fintype O] [DecidableEq O]
        [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y)
        (q : Dist A) (P : Channel A O),
        hV.V (Relabeling.relabelDist eA q)
            (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hV.V q (experimentOfChannel P))
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (s : Dist A) (hs : s.FullSupport)
    (η : PosteriorLawSigned A)
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    directPosteriorLawLinearMap hV (Relabeling.relabelDist e s)
        (relabelPosteriorLawSigned e η) =
      directPosteriorLawLinearMap hV s η := by
  simpa [finiteAffineLinearPartAssumptions_of_posteriorValue] using
    (affineLinearPart_relabel_atomicTangent
      finiteAffineLinearPartAssumptions_of_posteriorValue hV hrelab
      e s hs η hηatomic hηtan)

/-!
## Direct branch aggregation components

The remainder of this file feeds the direct affine linear part into the
existing A1/A6 tangent argument.  The only representative-level datum retained
as an explicit input is support-face value transport: it compares values at an
ambient boundary prior with values on its intrinsic positive-support simplex.
-/

/-- The corrected atomic-linear tangent spanning package used by the direct
branch construction. -/
noncomputable def directAtomicLinearTangentSpanning :
    FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u} :=
  atomicLinearTangentSpanning_of_atomic
    finiteAtomicPosteriorTangentSpanning

/-- The A1/A6 path coefficient obtained from the direct affine linear part. -/
noncomputable def directBranchPathTangentScalar
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchPathTangentScalarStructure F hV
      finiteAffineLinearPartAssumptions_of_posteriorValue :=
  branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
    finiteAffineLinearPartAssumptions_of_posteriorValue
    finiteLinearFunctionalSameSignScalarOnTangent_of_direct
    directAtomicLinearTangentSpanning F hax hV

/-- The positive ambient-to-face coefficient obtained from the same direct
linear part and atomic tangent spanning. -/
noncomputable def directBoundaryCoefficientScaleNormalization
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u} :=
  boundaryCoefficientScaleNormalization_of_A1_atomicLinearTangentSpanning
    finiteAffineLinearPartAssumptions_of_posteriorValue
    directAtomicLinearTangentSpanning F hax hV

/-- Boundary face-scale view of the direct ambient-to-face coefficient. -/
noncomputable def directBoundaryFaceScale
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBranchBoundaryFaceScaleAssumptions.{u} :=
  boundaryFaceScale_of_coefficientScaleNormalization
    (directBoundaryCoefficientScaleNormalization F hax hV)

/-- Push a signed law on a positive-support face into the ambient simplex. -/
noncomputable def directPushSignedIncl
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (η : PosteriorLawSigned (supportSubtype r)) : PosteriorLawSigned A :=
  fun φ => η (fun d =>
    φ (Channel.actionPushforward d (supportIncludeKernel r)))

/-- Inclusion pushforward preserves finite atomic-linearity. -/
noncomputable def directPushSignedIncl_atomicLinear
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    {η : PosteriorLawSigned (supportSubtype r)}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (directPushSignedIncl r η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact
      { I := hη.witness.I
        instFintypeI := inferInstance
        instDecidableEqI := inferInstance
        weight := hη.witness.weight
        point := fun i => Channel.actionPushforward
          (hη.witness.point i) (supportIncludeKernel r) }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext φ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        φ (Channel.actionPushforward
          (hη.witness.point i) (supportIncludeKernel r))) =
      η (fun d => φ
        (Channel.actionPushforward d (supportIncludeKernel r)))
    have h := congrFun hη.eval_eq
      (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

private theorem direct_actionPushforward_supportIncludeKernel_apply
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (t : Dist (supportSubtype q)) (a : A) :
    Channel.actionPushforward t (supportIncludeKernel q) a =
      if h : q a > 0 then t ⟨a, h⟩ else 0 := by
  unfold Channel.actionPushforward supportIncludeKernel
  change (∑ c : supportSubtype q, t c * (Dist.pure c.1) a) =
    if h : q a > 0 then t ⟨a, h⟩ else 0
  by_cases hqa : q a > 0
  · rw [dif_pos hqa]
    let b : supportSubtype q := ⟨a, hqa⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro c _ hc
      have hne : c.1 ≠ a := by
        intro hca
        apply hc
        exact Subtype.ext hca
      rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · rw [dif_neg hqa]
    apply Finset.sum_eq_zero
    intro c _
    have hne : c.1 ≠ a := by
      intro hca
      exact hqa (hca ▸ c.2)
    rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]

/-- Inclusion pushforward preserves the atomic tangent conditions. -/
theorem directPushSignedIncl_tangent
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    {η : PosteriorLawSigned (supportSubtype r)}
    (hη : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    PosteriorLawTangent (directPushSignedIncl r η) := by
  refine ⟨?_, ?_⟩
  · show η (fun _ => (1 : ℝ)) = 0
    exact hηtan.1
  · intro a
    show η (fun d =>
      (Channel.actionPushforward d (supportIncludeKernel r)) a) = 0
    by_cases ha : r a > 0
    · have heq :
          (fun d : Dist (supportSubtype r) =>
            (Channel.actionPushforward d (supportIncludeKernel r)) a) =
          (fun d : Dist (supportSubtype r) => d ⟨a, ha⟩) := by
        funext d
        rw [direct_actionPushforward_supportIncludeKernel_apply, dif_pos ha]
      rw [heq]
      exact hηtan.2 ⟨a, ha⟩
    · have heq :
          (fun d : Dist (supportSubtype r) =>
            (Channel.actionPushforward d (supportIncludeKernel r)) a) =
          (fun _ => (0 : ℝ)) := by
        funext d
        rw [direct_actionPushforward_supportIncludeKernel_apply, dif_neg ha]
      rw [heq]
      have h := congrFun hη.eval_eq (fun _ => (0 : ℝ))
      rw [AtomicPosteriorSignedLaw.eval_apply] at h
      rw [← h]
      simp

/-- The direct ambient-to-face coefficient is independent of the chosen
full-support ambient prior up to the full-support path coefficient. -/
theorem directBoundaryCoeff_qIndep
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    (directBoundaryFaceScale F hax hV).boundaryCoeff q r *
        (directBranchPathTangentScalar F hax hV).branchPathCoeff q' q =
      (directBoundaryFaceScale F hax hV).boundaryCoeff q' r := by
  classical
  let hlin := finiteAffineLinearPartAssumptions_of_posteriorValue
  let hpath := directBranchPathTangentScalar F hax hV
  change boundaryAtomicLinearTangentCoeffOfA1Spanning
      hlin directAtomicLinearTangentSpanning F hax hV q r *
        hpath.branchPathCoeff q' q =
    boundaryAtomicLinearTangentCoeffOfA1Spanning
      hlin directAtomicLinearTangentSpanning F hax hV q' r
  haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  have hrs_fs : r.restrictToSupport.FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h
      exact hab (congrArg Subtype.val h)
    · rw [Dist.restrictToSupport_apply]
      exact ha
    · rw [Dist.restrictToSupport_apply]
      exact hb
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV r.restrictToSupport r.restrictToSupport
      hrs_fs hrs_fs hrs_nd
  have hTq :=
    boundaryAtomicLinearTangentCoeffOfA1Spanning_relation
      hlin directAtomicLinearTangentSpanning F hax hV
      q r hq hrs_nd η hηatomic hηtan
  have hTq' :=
    boundaryAtomicLinearTangentCoeffOfA1Spanning_relation
      hlin directAtomicLinearTangentSpanning F hax hV
      q' r hq' hrs_nd η hηatomic hηtan
  have hpushAtomic := directPushSignedIncl_atomicLinear r hηatomic
  have hpushTan := directPushSignedIncl_tangent r hηatomic hηtan
  have hq_nd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b := by
    obtain ⟨a, b, hab, _ha, _hb⟩ := hrnd
    exact ⟨a, b, hab, hq a, hq b⟩
  have hrel := hpath.linear_part_scalar_relation_on_tangent
    q' q hq' hq hq_nd (directPushSignedIncl r η)
      hpushAtomic hpushTan
  have hTqDirect :
      hlin.linearPart F hV q (directPushSignedIncl r η) =
        boundaryAtomicLinearTangentCoeffOfA1Spanning
            hlin directAtomicLinearTangentSpanning F hax hV q r *
          hlin.linearPart F hV r.restrictToSupport η := by
    change hlin.linearPart F hV q
        (fun φ : Dist A → ℝ => η (fun d =>
          φ (Channel.actionPushforward d (supportIncludeKernel r)))) = _
    exact hTq
  have hTq'Direct :
      hlin.linearPart F hV q' (directPushSignedIncl r η) =
        boundaryAtomicLinearTangentCoeffOfA1Spanning
            hlin directAtomicLinearTangentSpanning F hax hV q' r *
          hlin.linearPart F hV r.restrictToSupport η := by
    change hlin.linearPart F hV q'
        (fun φ : Dist A → ℝ => η (fun d =>
          φ (Channel.actionPushforward d (supportIncludeKernel r)))) = _
    exact hTq'
  rw [hTqDirect, hTq'Direct] at hrel
  have hstep :
      boundaryAtomicLinearTangentCoeffOfA1Spanning
            hlin directAtomicLinearTangentSpanning F hax hV q' r *
          hlin.linearPart F hV r.restrictToSupport η =
        (boundaryAtomicLinearTangentCoeffOfA1Spanning
            hlin directAtomicLinearTangentSpanning F hax hV q r *
          hpath.branchPathCoeff q' q) *
          hlin.linearPart F hV r.restrictToSupport η := by
    rw [hrel]
    ring
  have hcancel := mul_right_cancel₀ hηnz hstep
  linarith [hcancel]

/-- The boundary branch summand follows directly from the atomic tangent
coefficient relation.  No posterior integrand or marginal-value transport is
used: the only tangent needed is the posterior-law difference generated by the
continuation experiment on the support face. -/
theorem directBranchFormulaBoundarySummand
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchFormulaBoundarySummandFor F hax hV
      finiteAffineLinearPartAssumptions_of_posteriorValue
      (directBoundaryFaceScale F hax hV) where
  boundary_summand_linearPart_eq := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ target
      hr_nonempty hr_nondegenerate hr_boundary Q
    classical
    let hlin := finiteAffineLinearPartAssumptions_of_posteriorValue
    let htangent := directAtomicLinearTangentSpanning
    let r : Dist A := branchPosterior P₁ q target
    let m : ℝ := (Channel.outcomeMarginal P₁ q) target
    haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
    let η : PosteriorLawSigned (supportSubtype r) :=
      posteriorLawDifferenceExp r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel
          (Channel.uninformativeChannelU (supportSubtype r)))
    have hηatomic : PosteriorLawSigned.AtomicLinear η := by
      exact posteriorLawDifferenceExp_atomicLinear r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel
          (Channel.uninformativeChannelU (supportSubtype r)))
    have hηtan : PosteriorLawTangent η := by
      exact posteriorLawDifferenceExp_tangent r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport Q r))
        (experimentOfChannel
          (Channel.uninformativeChannelU (supportSubtype r)))
    have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
        0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
      obtain ⟨a, b, hab, ha, hb⟩ := hr_nondegenerate
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
      · intro h
        exact hab (congrArg Subtype.val h)
      · rw [Dist.restrictToSupport_apply]
        exact ha
      · rw [Dist.restrictToSupport_apply]
        exact hb
    have hdiff_ext :
        ∀ φ : Dist A → ℝ,
          posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A)) φ =
            (fun φ : Dist A → ℝ =>
              η (fun d => φ
                (Channel.actionPushforward d (supportIncludeKernel r)))) φ := by
      intro φ
      exact posteriorLawDifferenceExp_restrictToSupport_pushforward r Q φ
    have hdiff_linear :
        hlin.linearPart F hV q
            (posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))) =
          hlin.linearPart F hV q
            (fun φ : Dist A → ℝ =>
              η (fun d => φ
                (Channel.actionPushforward d (supportIncludeKernel r)))) :=
      hlin.linearPart_ext F hV q _ _ hdiff_ext
    have hscalar :
        hlin.linearPart F hV q
            (posteriorLawDifferenceExp r
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A))) =
          (directBoundaryFaceScale F hax hV).boundaryCoeff q r *
            hlin.linearPart F hV r.restrictToSupport η := by
      rw [hdiff_linear]
      exact boundaryAtomicLinearTangentCoeffOfA1Spanning_relation
        hlin htangent F hax hV q r hq hrs_nd η hηatomic hηtan
    have hface_linear :
        hlin.linearPart F hV r.restrictToSupport η =
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport Q r)) := by
      have hdiff :=
        (hlin.value_difference F hV r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport Q r))
          (experimentOfChannel
            (Channel.uninformativeChannelU (supportSubtype r)))).symm
      have hzero :
          hV.V r.restrictToSupport
            (experimentOfChannel
              (Channel.uninformativeChannelU (supportSubtype r))) = 0 :=
        hV.zero_normalized r.restrictToSupport
          (Dist.restrictToSupport_fullSupport r)
      rw [hzero, sub_zero] at hdiff
      simpa [η] using hdiff
    have hvalue_transport :
        hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport Q r)) =
          hV.V r (experimentOfChannel Q) :=
      (hvalue.boundary_value_transport r Q).symm
    calc
      hlin.linearPart F hV q
          (posteriorLawSignedSMul ((Channel.outcomeMarginal P₁ q) target)
            (posteriorLawDifferenceExp (branchPosterior P₁ q target)
              (experimentOfChannel Q)
              (experimentOfChannel (Channel.uninformativeChannelU A)))) =
        m * hlin.linearPart F hV q
          (posteriorLawDifferenceExp r
            (experimentOfChannel Q)
            (experimentOfChannel (Channel.uninformativeChannelU A))) := by
          rw [hlin.linearPart_smul]
      _ = m * ((directBoundaryFaceScale F hax hV).boundaryCoeff q r *
          hlin.linearPart F hV r.restrictToSupport η) := by
          rw [hscalar]
      _ = m * (directBoundaryFaceScale F hax hV).boundaryCoeff q r *
          hV.V r (experimentOfChannel Q) := by
          rw [hface_linear, hvalue_transport]
          ring
      _ = (Channel.outcomeMarginal P₁ q) target *
          (directBoundaryFaceScale F hax hV).boundaryCoeff q
            (branchPosterior P₁ q target) *
          hV.V (branchPosterior P₁ q target)
            (experimentOfChannel Q) := by
          simp [m, r]

/-- Singleton normalization compatible with the full-support base scale.  Its
value-zero field follows from support-face transport and the fact that the
intrinsic support type is subsingleton. -/
noncomputable def directBranchSingletonScaleNormalization
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchSingletonScaleNormalizationFor F hV := by
  classical
  let hpath := directBranchPathTangentScalar F hax hV
  refine
    { singletonCoeff := fun {A} _ _ _ q _ =>
        hpath.branchPathCoeff q (Dist.uniform (A := A))
      singletonCoeff_pos := ?_
      singleton_branch_value_zero := ?_ }
  · intro A _ _ _ q _r hq _hr_singleton
    by_cases hnd : ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b
    · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
        hq Dist.uniform_fullSupport hnd
    · have hpath_eq :
          hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
        simp only [hpath, directBranchPathTangentScalar,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hnd]
      rw [hpath_eq]
      exact one_pos
  · intro A O _ _ _ _ _ r hr_singleton P
    haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
    letI : Subsingleton (supportSubtype r) :=
      supportSubtype_subsingleton_of_singleton_support r hr_singleton
    calc
      hV.V r (experimentOfChannel P) =
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport P r)) :=
        hvalue.boundary_value_transport r P
      _ = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F hV
          r.restrictToSupport (Dist.restrictToSupport_fullSupport r)
          (Channel.restrictToSupport P r)

/-- The branch aggregation formula produced by the direct affine/tangent
route. -/
noncomputable def directBranchAggregationFormula
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchAggregationFormulaTangentFor F hax hV
      finiteAffineLinearPartAssumptions_of_posteriorValue
      (directBranchPathTangentScalar F hax hV)
      (directBoundaryFaceScale F hax hV)
      (directBranchSingletonScaleNormalization F hax hV hvalue) :=
  branchAggregationFormulaTangentFor_of_boundarySummandsFor
    F hax hV finiteAffineLinearPartAssumptions_of_posteriorValue
    (directBranchPathTangentScalar F hax hV)
    (directBoundaryFaceScale F hax hV)
    (directBranchSingletonScaleNormalization F hax hV hvalue)
    (directBranchFormulaBoundarySummand F hax hV hvalue)

/-- Public branch aggregation assembled from the direct affine/tangent route. -/
noncomputable def directBranchAggregationStructure
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    BranchAggregationStructure F :=
  branchAggregationStructure_of_tangentFormulaFor
    F hax hV finiteAffineLinearPartAssumptions_of_posteriorValue
    (directBranchPathTangentScalar F hax hV)
    (directBoundaryFaceScale F hax hV)
    (directBranchSingletonScaleNormalization F hax hV hvalue)
    (directBranchAggregationFormula F hax hV hvalue)

/-- Full-support cocycle for the direct branch aggregation. -/
noncomputable def directBranchCoeffCocycle
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchCoeffCocycleAssumptionsFor
      (directBranchAggregationStructure F hax hV hvalue) :=
  branchCoeffCocycleFor_of_tangentScalar
    F hax hV finiteAffineLinearPartAssumptions_of_posteriorValue
    (directBranchPathTangentScalar F hax hV)
    (directBoundaryFaceScale F hax hV)
    (directBranchSingletonScaleNormalization F hax hV hvalue)
    (directBranchAggregationFormula F hax hV hvalue)

/-- Full-support basepoint scale induced by the direct cocycle. -/
noncomputable def directBranchFullSupportScale
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (directBranchAggregationStructure F hax hV hvalue) :=
  branchScaleFactorizationFullSupport_of_cocycle
    (directBranchAggregationStructure F hax hV hvalue)
    (directBranchCoeffCocycle F hax hV hvalue)

/-- Selected scale on every prior.  On a full-support simplex it is the
path-to-uniform coefficient; on a nondegenerate boundary face it is the
inverse uniform-to-face coefficient; the singleton case is normalized to one. -/
noncomputable def directSelectedBranchScale
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ := by
  classical
  exact
    if hq : q.FullSupport then
      (directBranchPathTangentScalar F hax hV).branchPathCoeff
        q (Dist.uniform (A := A))
    else if hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b then
      1 / (directBoundaryFaceScale F hax hV).boundaryCoeff
        (Dist.uniform (A := A)) q
    else
      1

theorem directSelectedBranchScale_fullSupport
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    directSelectedBranchScale F hax hV q =
      (directBranchPathTangentScalar F hax hV).branchPathCoeff
        q (Dist.uniform (A := A)) := by
  classical
  simp [directSelectedBranchScale, hq]

theorem directSelectedBranchScale_boundary
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    directSelectedBranchScale F hax hV r =
      1 / (directBoundaryFaceScale F hax hV).boundaryCoeff
        (Dist.uniform (A := A)) r := by
  classical
  simp [directSelectedBranchScale, hrb, hrnd]

theorem directSelectedBranchScale_pos
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    0 < directSelectedBranchScale F hax hV q := by
  classical
  let hpath := directBranchPathTangentScalar F hax hV
  rw [directSelectedBranchScale_fullSupport F hax hV q hq]
  by_cases hnd : ∃ a b : A, a ≠ b ∧
      0 < (Dist.uniform (A := A)) a ∧
      0 < (Dist.uniform (A := A)) b
  · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
      hq Dist.uniform_fullSupport hnd
  · have hpath_eq :
        hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      simp only [hpath, directBranchPathTangentScalar,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hq, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnd]
    rw [hpath_eq]
    exact one_pos

/-- Full-support factorization expressed using the selected all-prior scale. -/
noncomputable def directSelectedFullSupportScale
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (directBranchAggregationStructure F hax hV hvalue) where
  scale := fun q => directSelectedBranchScale F hax hV q
  scale_pos := by
    intro A _ _ _ q hq _hnd
    exact directSelectedBranchScale_pos F hax hV q hq
  branchCoeff_factorization_fullSupport := by
    intro A _ _ _ q r hq hr hnd
    classical
    let hpath := directBranchPathTangentScalar F hax hV
    let hboundary := directBoundaryFaceScale F hax hV
    let hsingle :=
      directBranchSingletonScaleNormalization F hax hV hvalue
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      directSelectedBranchScale F hax hV q /
        directSelectedBranchScale F hax hV r
    rw [directSelectedBranchScale_fullSupport F hax hV q hq,
      directSelectedBranchScale_fullSupport F hax hV r hr]
    rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
        hpath.branchPathCoeff q r by
      simp [branchCoeffFromTangentRepParts, hr]]
    have hU_nd : ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
      obtain ⟨a, b, hab⟩ := hnd
      exact ⟨a, b, hab, Dist.uniform_fullSupport a,
        Dist.uniform_fullSupport b⟩
    have hpos :
        0 < hpath.branchPathCoeff r (Dist.uniform (A := A)) :=
      hpath.branchPathCoeff_pos r (Dist.uniform (A := A))
        hr Dist.uniform_fullSupport hU_nd
    have hcoc :=
      branchCoeffTangentScalar_cocycle_fullSupport
        finiteAffineLinearPartAssumptions_of_posteriorValue
        F hax hV hpath q r (Dist.uniform (A := A))
        hq hr Dist.uniform_fullSupport hnd
    rw [hcoc]
    change hpath.branchPathCoeff q r =
      hpath.branchPathCoeff q r *
          hpath.branchPathCoeff r (Dist.uniform (A := A)) /
        hpath.branchPathCoeff r (Dist.uniform (A := A))
    field_simp [ne_of_gt hpos]

/-- Boundary extension of the selected scale factorization. -/
noncomputable def directSelectedBoundaryScaleFactorization
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchScaleFactorizationBoundaryTransportAssumptions
      (directBranchAggregationStructure F hax hV hvalue)
      (directSelectedFullSupportScale F hax hV hvalue) where
  branchCoeff_factorization_boundary := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hrnd hrb
    classical
    let r : Dist A := Channel.posterior P₁ q o₁
    let hpath := directBranchPathTangentScalar F hax hV
    let hboundary := directBoundaryFaceScale F hax hV
    let hsingle :=
      directBranchSingletonScaleNormalization F hax hV hvalue
    have hrnd_r : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      simpa [r] using hrnd
    have hrb_r : ¬ r.FullSupport := by
      simpa [r] using hrb
    have hrn : ∃ a : A, 0 < r a := by
      rcases hrnd_r with ⟨a, _b, _hab, ha, _hb⟩
      exact ⟨a, ha⟩
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      directSelectedBranchScale F hax hV q /
        directSelectedBranchScale F hax hV r
    rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
        hboundary.boundaryCoeff q r by
      unfold branchCoeffFromTangentRepParts
      rw [dif_neg hrb_r, dif_pos hrnd_r]]
    rw [directSelectedBranchScale_fullSupport F hax hV q hq,
      directSelectedBranchScale_boundary F hax hV r hrnd_r hrb_r]
    have hbc_pos :
        0 < hboundary.boundaryCoeff (Dist.uniform (A := A)) r :=
      hboundary.boundaryCoeff_pos (Dist.uniform (A := A)) r
        Dist.uniform_fullSupport hrn hrnd_r hrb_r
    have hqi := directBoundaryCoeff_qIndep F hax hV
      (Dist.uniform (A := A)) q r Dist.uniform_fullSupport hq hrnd_r
    rw [← hqi]
    field_simp [ne_of_gt hbc_pos]

/-- Singleton extension of the selected scale factorization. -/
noncomputable def directSelectedSingletonScaleFactorization
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchScaleFactorizationSingletonNormalization
      (directBranchAggregationStructure F hax hV hvalue)
      (directSelectedFullSupportScale F hax hV hvalue) where
  scale_pos_singleton := by
    intro A _ _ _ q hq _hr_singleton
    exact directSelectedBranchScale_pos F hax hV q hq
  branchCoeff_factorization_singleton := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hsingle_support
    classical
    let r : Dist A := Channel.posterior P₁ q o₁
    let hpath := directBranchPathTangentScalar F hax hV
    let hboundary := directBoundaryFaceScale F hax hV
    let hsingle :=
      directBranchSingletonScaleNormalization F hax hV hvalue
    have hnotnd : ¬ ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b :=
      not_nondegenerate_of_singleton_support r
        (by simpa [r] using hsingle_support)
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      directSelectedBranchScale F hax hV q /
        directSelectedBranchScale F hax hV r
    by_cases hrfull : r.FullSupport
    · have hsub : Subsingleton A := by
        rcases hsingle_support with ⟨c, _hc, huniq⟩
        refine ⟨?_⟩
        intro a b
        exact (huniq a (hrfull a)).trans (huniq b (hrfull b)).symm
      have hU_notnd : ¬ ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hne, _ha, _hb⟩
        exact hne (Subsingleton.elim a b)
      have hpath_qr_one : hpath.branchPathCoeff q r = 1 := by
        simp only [hpath, directBranchPathTangentScalar,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, hrfull, dif_pos]
        rw [dif_neg hnotnd]
      have hscale_q_one : directSelectedBranchScale F hax hV q = 1 := by
        rw [directSelectedBranchScale_fullSupport F hax hV q hq]
        change hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1
        simp only [hpath, directBranchPathTangentScalar,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      have hscale_r_one : directSelectedBranchScale F hax hV r = 1 := by
        rw [directSelectedBranchScale_fullSupport F hax hV r hrfull]
        change hpath.branchPathCoeff r (Dist.uniform (A := A)) = 1
        simp only [hpath, directBranchPathTangentScalar,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hrfull, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
          hpath.branchPathCoeff q r by
        simp [branchCoeffFromTangentRepParts, hrfull]]
      rw [hpath_qr_one, hscale_q_one, hscale_r_one]
      norm_num
    · have hbranch_qr :
          branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
            hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
        unfold branchCoeffFromTangentRepParts
        rw [dif_neg hrfull, dif_neg hnotnd]
        rfl
      have hscale_r_one : directSelectedBranchScale F hax hV r = 1 := by
        simp [directSelectedBranchScale, hrfull, hnotnd]
      rw [hbranch_qr,
        directSelectedBranchScale_fullSupport F hax hV q hq,
        hscale_r_one, div_one]

/-- Complete all-prior scale factorization for the direct branch structure. -/
noncomputable def directBranchScaleFactorization
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    FiniteBranchScaleFactorizationAssumptions
      (directBranchAggregationStructure F hax hV hvalue) :=
  branchScaleFactorization_of_fullSupport_boundary_singleton
    (directBranchAggregationStructure F hax hV hvalue)
    (directSelectedFullSupportScale F hax hV hvalue)
    (directSelectedBoundaryScaleFactorization F hax hV hvalue)
    (directSelectedSingletonScaleFactorization F hax hV hvalue)

/-- End-to-end branch aggregation, cocycle, selected scale factorization, and
normalized chain rule from an arbitrary support-face-coherent selected
posterior value.  No posterior integral representation is selected. -/
noncomputable def directBranchChain_of_posteriorValue
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV) :
    BranchAggregationCocycleNormalizedChainRuleStructure F where
  branch_agg := directBranchAggregationStructure F hax hV hvalue
  coeff_cocycle := directBranchCoeffCocycle F hax hV hvalue
  full_support_scale := directSelectedFullSupportScale F hax hV hvalue
  scale_factorization := directBranchScaleFactorization F hax hV hvalue

end TraceableAgency
