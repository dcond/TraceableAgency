/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.TangentInterfaces

namespace TraceableAgency

universe u v

/-!
## Atomic tangent-spanning theorem

The corrected atomic tangent-spanning theorem.  Given an atomic signed
posterior law with zero mass, zero barycentre, and positive displayed
positive mass, realize its evaluation as a positive scalar multiple of a
feasible posterior-law difference. -/

namespace AtomicTangentSpanning

variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def positiveBaryCoord
    (ν : AtomicPosteriorSignedLaw A) (a : A) : ℝ := by
  letI : Fintype ν.I := ν.instFintypeI
  exact ∑ i : ν.I, ν.positiveWeight i * ν.point i a

theorem positiveBaryCoord_nonneg
    (ν : AtomicPosteriorSignedLaw A) (a : A) :
    0 ≤ positiveBaryCoord ν a := by
  letI : Fintype ν.I := ν.instFintypeI
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (AtomicPosteriorSignedLaw.positiveWeight_nonneg ν i)
    ((ν.point i).nonneg a)

theorem positiveBaryCoord_sum
    (ν : AtomicPosteriorSignedLaw A) :
    ∑ a : A, positiveBaryCoord ν a = ν.positiveMass := by
  letI : Fintype ν.I := ν.instFintypeI
  simp only [positiveBaryCoord, AtomicPosteriorSignedLaw.positiveMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, (ν.point i).sum_eq_one, mul_one]

noncomputable def smallEpsilon
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) : ℝ :=
  (Finset.univ : Finset A).inf' ⟨Classical.arbitrary A, Finset.mem_univ _⟩
    (fun a => r a / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')))

private theorem smallEpsilon_denom_pos
    (ν : AtomicPosteriorSignedLaw A) :
    (0 : ℝ) < 2 * (1 + ∑ a' : A, positiveBaryCoord ν a') := by
  have : (0 : ℝ) ≤ ∑ a' : A, positiveBaryCoord ν a' :=
    Finset.sum_nonneg (fun a _ => positiveBaryCoord_nonneg ν a)
  linarith

theorem smallEpsilon_pos
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) :
    0 < smallEpsilon r hr ν hV := by
  unfold smallEpsilon
  rw [Finset.lt_inf'_iff]
  intro a _
  exact div_pos (hr a) (smallEpsilon_denom_pos ν)

theorem smallEpsilon_le
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) (a : A) :
    smallEpsilon r hr ν hV ≤
      r a / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by
  unfold smallEpsilon
  exact Finset.inf'_le _ (Finset.mem_univ a)

theorem smallEpsilon_mul_V_lt_one
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) :
    smallEpsilon r hr ν hV * ν.positiveMass < 1 := by
  have hS := positiveBaryCoord_sum ν
  have hSge : 0 ≤ ∑ a : A, positiveBaryCoord ν a :=
    Finset.sum_nonneg (fun a _ => positiveBaryCoord_nonneg ν a)
  have hdenom_pos := smallEpsilon_denom_pos ν
  have hε_le := smallEpsilon_le r hr ν hV (Classical.arbitrary A)
  have hra_le := r.prob_le_one (Classical.arbitrary A)
  have hV_eq : ν.positiveMass = ∑ a' : A, positiveBaryCoord ν a' := hS.symm
  calc smallEpsilon r hr ν hV * ν.positiveMass
      ≤ (r (Classical.arbitrary A) / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a'))) *
          ν.positiveMass := by
        apply mul_le_mul_of_nonneg_right hε_le (le_of_lt hV)
    _ = r (Classical.arbitrary A) * ν.positiveMass /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by ring
    _ ≤ 1 * ν.positiveMass /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hdenom_pos)
        exact mul_le_mul_of_nonneg_right hra_le (le_of_lt hV)
    _ < 1 := by
        rw [one_mul, hV_eq, div_lt_one hdenom_pos]
        linarith

theorem smallEpsilon_mul_S_le_r
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) (a : A) :
    smallEpsilon r hr ν hV * positiveBaryCoord ν a ≤ r a := by
  have hdenom_pos := smallEpsilon_denom_pos ν
  have hε_le := smallEpsilon_le r hr ν hV a
  have hSa_le : positiveBaryCoord ν a ≤ ∑ a' : A, positiveBaryCoord ν a' :=
    Finset.single_le_sum (fun b _ => positiveBaryCoord_nonneg ν b) (Finset.mem_univ a)
  calc smallEpsilon r hr ν hV * positiveBaryCoord ν a
      ≤ (r a / (2 * (1 + ∑ a' : A, positiveBaryCoord ν a'))) *
          positiveBaryCoord ν a := by
        apply mul_le_mul_of_nonneg_right hε_le (positiveBaryCoord_nonneg ν a)
    _ = r a * positiveBaryCoord ν a /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by ring
    _ ≤ r a * (∑ a' : A, positiveBaryCoord ν a') /
          (2 * (1 + ∑ a' : A, positiveBaryCoord ν a')) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt hdenom_pos)
        exact mul_le_mul_of_nonneg_left hSa_le (le_of_lt (hr a))
    _ ≤ r a := by
        rw [div_le_iff₀ hdenom_pos]
        have hra_nn := le_of_lt (hr a)
        have hSnn : (0 : ℝ) ≤ ∑ a' : A, positiveBaryCoord ν a' :=
          Finset.sum_nonneg (fun a' _ => positiveBaryCoord_nonneg ν a')
        nlinarith [mul_nonneg hra_nn hSnn]

noncomputable def correctionDist
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) : Dist A := by
  letI : Fintype ν.I := ν.instFintypeI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hdenom_pos : (0 : ℝ) < 1 - ε * V := by linarith
  refine ⟨fun a => (r a - ε * positiveBaryCoord ν a) / (1 - ε * V), ?_, ?_⟩
  · intro a
    apply div_nonneg
    · linarith [smallEpsilon_mul_S_le_r r hr ν hV a]
    · linarith
  · rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hdenom_pos)]
    have hr_sum := r.sum_eq_one
    have hS_sum := positiveBaryCoord_sum ν
    calc ∑ a : A, (r a - ε * positiveBaryCoord ν a)
        = (∑ a : A, r a) - ε * ∑ a : A, positiveBaryCoord ν a := by
          simp [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 1 - ε * V := by rw [hr_sum, hS_sum]

noncomputable def completedPositiveProbLaw
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) : AtomicPosteriorProbLaw A := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hε_pos := smallEpsilon_pos r hr ν hV
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  exact {
    I := Option ν.I
    instFintypeI := inferInstance
    instDecidableEqI := inferInstance
    mass := fun oi => match oi with
      | none => 1 - ε * V
      | some i => ε * ν.positiveWeight i
    point := fun oi => match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i
    mass_nonneg := fun oi => by
      match oi with
      | none => simp; linarith
      | some i =>
        simp
        exact mul_nonneg (le_of_lt hε_pos) (AtomicPosteriorSignedLaw.positiveWeight_nonneg ν i)
    mass_sum := by
      simp only [Fintype.sum_option]
      ring_nf
      have h1 : ∑ i : ν.I, ε * ν.positiveWeight i = ε * V := by
        rw [← Finset.mul_sum]; rfl
      linarith
  }

noncomputable def completedNegativeProbLaw
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hV : 0 < ν.positiveMass) : AtomicPosteriorProbLaw A := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hε_pos := smallEpsilon_pos r hr ν hV
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hVeq := AtomicPosteriorSignedLaw.positiveMass_eq_negativeMass_of_totalMass_zero ν hmass
  exact {
    I := Option ν.I
    instFintypeI := inferInstance
    instDecidableEqI := inferInstance
    mass := fun oi => match oi with
      | none => 1 - ε * V
      | some i => ε * ν.negativeWeight i
    point := fun oi => match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i
    mass_nonneg := fun oi => by
      match oi with
      | none => simp; linarith
      | some i =>
        simp
        exact mul_nonneg (le_of_lt hε_pos) (AtomicPosteriorSignedLaw.negativeWeight_nonneg ν i)
    mass_sum := by
      simp only [Fintype.sum_option]
      ring_nf
      have h1 : ∑ i : ν.I, ε * ν.negativeWeight i = ε * ν.negativeMass := by
        rw [← Finset.mul_sum]; rfl
      rw [← hVeq] at h1
      linarith
  }

theorem completedPositiveProbLaw_barycenter
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hV : 0 < ν.positiveMass) (a : A) :
    (completedPositiveProbLaw r hr ν hV).barycenterCoord a = r a := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hdenom_pos : (0 : ℝ) < 1 - ε * V := by linarith
  show (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * V
      | some i => ε * ν.positiveWeight i) *
    (match oi with
      | none => (correctionDist r hr ν hV : Dist A)
      | some i => ν.point i) a) = r a
  rw [Fintype.sum_option]
  simp only []
  have h_corr_val : (correctionDist r hr ν hV : Dist A) a =
      (r a - ε * positiveBaryCoord ν a) / (1 - ε * V) := rfl
  rw [h_corr_val]
  have h_sum_eq : ∑ i : ν.I, ε * ν.positiveWeight i * (ν.point i) a =
      ε * positiveBaryCoord ν a := by
    unfold positiveBaryCoord
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  rw [h_sum_eq]
  field_simp [ne_of_gt hdenom_pos]
  ring

theorem completedNegativeProbLaw_barycenter
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hbary : ∀ a, ν.barycenterCoord a = 0)
    (hV : 0 < ν.positiveMass) (a : A) :
    (completedNegativeProbLaw r hr ν hmass hV).barycenterCoord a = r a := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  let V := ν.positiveMass
  have hεV : ε * V < 1 := smallEpsilon_mul_V_lt_one r hr ν hV
  have hdenom_pos : (0 : ℝ) < 1 - ε * V := by linarith
  have hpb :=
    AtomicPosteriorSignedLaw.positive_barycenter_eq_negative_barycenter_of_barycenter_zero
      ν a (hbary a)
  show (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * V
      | some i => ε * ν.negativeWeight i) *
    (match oi with
      | none => (correctionDist r hr ν hV : Dist A)
      | some i => ν.point i) a) = r a
  rw [Fintype.sum_option]
  simp only []
  have hNS_eq : ∑ i : ν.I, ε * ν.negativeWeight i * (ν.point i) a =
      ε * positiveBaryCoord ν a := by
    have : ∑ i : ν.I, ε * ν.negativeWeight i * (ν.point i) a =
        ε * ∑ i : ν.I, ν.negativeWeight i * (ν.point i) a := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this, show positiveBaryCoord ν a =
        ∑ i : ν.I, ν.positiveWeight i * (ν.point i) a from rfl, ← hpb]
  rw [hNS_eq]
  have h_corr_val : (correctionDist r hr ν hV : Dist A) a =
      (r a - ε * positiveBaryCoord ν a) / (1 - ε * V) := rfl
  rw [h_corr_val]
  field_simp [ne_of_gt hdenom_pos]
  ring

theorem completedProbLaw_eval_difference
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hbary : ∀ a, ν.barycenterCoord a = 0)
    (hV : 0 < ν.positiveMass) (φ : Dist A → ℝ) :
    (completedPositiveProbLaw r hr ν hV).eval φ -
      (completedNegativeProbLaw r hr ν hmass hV).eval φ =
    smallEpsilon r hr ν hV * ν.eval φ := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := smallEpsilon r hr ν hV
  show (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * ν.positiveMass
      | some i => ε * ν.positiveWeight i) *
    φ (match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i)) -
    (∑ oi : Option ν.I, (match oi with
      | none => 1 - ε * ν.positiveMass
      | some i => ε * ν.negativeWeight i) *
    φ (match oi with
      | none => correctionDist r hr ν hV
      | some i => ν.point i)) =
    ε * ∑ i : ν.I, ν.weight i * φ (ν.point i)
  rw [Fintype.sum_option, Fintype.sum_option]
  simp only []
  have h_cancel : (1 - ε * ν.positiveMass) * φ (correctionDist r hr ν hV) -
      (1 - ε * ν.positiveMass) * φ (correctionDist r hr ν hV) = 0 := by ring
  have h_sums : (∑ i : ν.I, ε * ν.positiveWeight i * φ (ν.point i)) -
      (∑ i : ν.I, ε * ν.negativeWeight i * φ (ν.point i)) =
    ε * ∑ i : ν.I, ν.weight i * φ (ν.point i) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    have hw := AtomicPosteriorSignedLaw.weight_eq_positiveWeight_sub_negativeWeight ν i
    rw [hw]; ring
  linarith

end AtomicTangentSpanning

theorem atomic_zero_mass_barycenter_as_feasible_difference_of_positiveMass
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport)
    (ν : AtomicPosteriorSignedLaw A)
    (hmass : ν.totalMass = 0)
    (hbary : ∀ a, ν.barycenterCoord a = 0)
    (hpos : 0 < ν.positiveMass) :
    ∃ (t : ℝ) (_ : 0 < t) (E E' : FiniteExperimentOn A),
      ∀ φ : Dist A → ℝ,
        ν.eval φ = t * posteriorLawDifferenceExp r E E' φ := by
  letI : Fintype ν.I := ν.instFintypeI
  letI : DecidableEq ν.I := ν.instDecidableEqI
  let ε := AtomicTangentSpanning.smallEpsilon r hr ν hpos
  have hε_pos := AtomicTangentSpanning.smallEpsilon_pos r hr ν hpos
  let μ_pos := AtomicTangentSpanning.completedPositiveProbLaw r hr ν hpos
  let μ_neg := AtomicTangentSpanning.completedNegativeProbLaw r hr ν hmass hpos
  have hbary_pos : ∀ a : A, μ_pos.barycenterCoord a = r a :=
    AtomicTangentSpanning.completedPositiveProbLaw_barycenter r hr ν hpos
  have hbary_neg : ∀ a : A, μ_neg.barycenterCoord a = r a :=
    AtomicTangentSpanning.completedNegativeProbLaw_barycenter r hr ν hmass hbary hpos
  let E := μ_pos.experimentOfPosteriorProbLaw r hr hbary_pos
  let E' := μ_neg.experimentOfPosteriorProbLaw r hr hbary_neg
  refine ⟨1 / ε, by positivity, E, E', ?_⟩
  intro φ
  have heval_pos :=
    AtomicPosteriorProbLaw.posteriorLawIntegralExp_experimentOfPosteriorProbLaw
      r hr μ_pos hbary_pos φ
  have heval_neg :=
    AtomicPosteriorProbLaw.posteriorLawIntegralExp_experimentOfPosteriorProbLaw
      r hr μ_neg hbary_neg φ
  have hdiff := AtomicTangentSpanning.completedProbLaw_eval_difference
    r hr ν hmass hbary hpos φ
  have hne : ε ≠ 0 := ne_of_gt hε_pos
  have hgoal : ν.eval φ = 1 / ε * (μ_pos.eval φ - μ_neg.eval φ) := by
    field_simp; linarith
  rw [hgoal]
  simp only [posteriorLawDifferenceExp_apply]
  congr 1
  rw [← heval_pos, ← heval_neg]

theorem finiteAtomicPosteriorTangentSpanning :
    FiniteAtomicPosteriorTangentSpanningAssumptions.{u} where
  atomic_zero_mass_barycenter_as_feasible_difference := by
    intro A _ _ _ r hr ν hmass hbary hne
    have hpos := AtomicPosteriorSignedLaw.positiveMass_pos_of_eval_ne_zero ν hmass hne
    obtain ⟨t, ht, E, E', hreal⟩ :=
      atomic_zero_mass_barycenter_as_feasible_difference_of_positiveMass
        r hr ν hmass hbary hpos
    exact ⟨t, ht, E, E', hreal⟩

/-- Common-outcome realization of tangent directions.

The finite-branch continuation step derived from main-text A8 compares two
continuation channels in the same branch outcome alphabet.  The older tangent
spanning interface realizes a tangent
direction by two finite experiments, whose bundled outcome types may differ.
This interface isolates the padding/realization strengthening needed before
the finite-branch property can be applied directly. -/
structure FiniteCommonOutcomeTangentRealizationAssumptions : Prop where
  tangent_as_common_outcome_difference :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (r : Dist A) (_hr : r.FullSupport) (η : PosteriorLawSigned A),
      PosteriorLawTangent η →
      η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
      ∃ (t : ℝ), ∃ (_ht : 0 < t), ∃ (O : Type v),
      ∃ (hO : Fintype O), ∃ (hOdec : DecidableEq O),
        letI : Fintype O := hO
        letI : DecidableEq O := hOdec
        ∃ P R : Channel A O,
          ∀ φ : Dist A → ℝ,
            η φ =
              t * posteriorLawDifferenceExp r
                (experimentOfChannel P) (experimentOfChannel R) φ

/-- Full-support branch reachability.

This is the finite-probability step that any full-support posterior `r` can be
reached with positive probability from any full-support prior `q`. -/
structure FiniteFullSupportBranchReachabilityAssumptions : Prop where
  reaches :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A), q.FullSupport → r.FullSupport →
      ∃ (O₁ : Type v), ∃ (hO₁ : Fintype O₁),
      ∃ (hO₁dec : DecidableEq O₁),
        letI : Fintype O₁ := hO₁
        letI : DecidableEq O₁ := hO₁dec
        ∃ (P₁ : Channel A O₁), ∃ target : O₁,
          BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r

/-- Tangent-space spanning by feasible differences can be upgraded to
common-outcome feasible differences by padding the two bundled outcome types into
a disjoint sum. -/
theorem commonOutcomeTangentRealization_of_tangentSpanning
    (htangent : FinitePosteriorTangentSpaceSpanningAssumptions.{u}) :
    FiniteCommonOutcomeTangentRealizationAssumptions.{u} where
  tangent_as_common_outcome_difference := by
    intro A _ _ _ r hr η htan hηne
    rcases htangent.zero_mass_barycenter_as_feasible_difference
        r hr η htan.1 htan.2 hηne with
      ⟨t, ht, E, E', hη⟩
    classical
    letI : Fintype E.OutcomeType := E.outFintype
    letI : DecidableEq E.OutcomeType := E.outDecEq
    letI : Fintype E'.OutcomeType := E'.outFintype
    letI : DecidableEq E'.OutcomeType := E'.outDecEq
    let O : Type u := E.OutcomeType ⊕ E'.OutcomeType
    refine ⟨t, ht, O, inferInstance, inferInstance, ?_⟩
    refine ⟨outcomePadLeft (Y := E'.OutcomeType) E.P,
      outcomePadRight (O := E.OutcomeType) E'.P, ?_⟩
    intro φ
    have hdiff :
        posteriorLawDifferenceExp r E E' φ =
          posteriorLawDifferenceExp r
            (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
            (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
      simp [posteriorLawDifferenceExp, posteriorLawIntegral_outcomePadLeft,
        posteriorLawIntegral_outcomePadRight, experimentOfChannel,
        FiniteExperimentOn.ofChannel, FiniteExperimentOn.P]
    calc
      η φ = t * posteriorLawDifferenceExp r E E' φ := hη φ
      _ =
          t * posteriorLawDifferenceExp r
            (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
            (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
            rw [hdiff]

/-- Atomic-linear common-outcome tangent realization from atomic-linear spanning.

Given the corrected atomic-linear spanning, every atomic-linear tangent η ≠ 0
can be realized as a positive scalar multiple of a common-outcome posterior-law
difference. -/
theorem commonOutcomeAtomicLinearTangentRealization_of_atomicLinearSpanning
    (htangent : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) (η : PosteriorLawSigned A)
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (htan : PosteriorLawTangent η)
    (hηne : η ≠ ((fun _ => 0) : PosteriorLawSigned A)) :
    ∃ (t : ℝ), ∃ (_ht : 0 < t), ∃ (O : Type u),
    ∃ (hO : Fintype O), ∃ (hOdec : DecidableEq O),
      letI : Fintype O := hO
      letI : DecidableEq O := hOdec
      ∃ P R : Channel A O,
        ∀ φ : Dist A → ℝ,
          η φ =
            t * posteriorLawDifferenceExp r
              (experimentOfChannel P) (experimentOfChannel R) φ := by
  have hmass : hηatomic.witness.totalMass = 0 := by
    have htan1 := htan.1
    rw [← hηatomic.eval_eq] at htan1
    rwa [AtomicPosteriorSignedLaw.eval_const_one] at htan1
  have hbary : ∀ a : A, hηatomic.witness.barycenterCoord a = 0 := by
    intro a
    have htan2 := htan.2 a
    rw [← hηatomic.eval_eq] at htan2
    rwa [AtomicPosteriorSignedLaw.eval_coord] at htan2
  rcases htangent.atomicLinear_zero_mass_barycenter_as_feasible_difference
      r hr η hηatomic hmass hbary hηne with
    ⟨t, ht, E, E', hη⟩
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype E'.OutcomeType := E'.outFintype
  letI : DecidableEq E'.OutcomeType := E'.outDecEq
  let O : Type u := E.OutcomeType ⊕ E'.OutcomeType
  refine ⟨t, ht, O, inferInstance, inferInstance, ?_⟩
  refine ⟨outcomePadLeft (Y := E'.OutcomeType) E.P,
    outcomePadRight (O := E.OutcomeType) E'.P, ?_⟩
  intro φ
  have hdiff :
      posteriorLawDifferenceExp r E E' φ =
        posteriorLawDifferenceExp r
          (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
          (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
    simp [posteriorLawDifferenceExp, posteriorLawIntegral_outcomePadLeft,
      posteriorLawIntegral_outcomePadRight, experimentOfChannel,
      FiniteExperimentOn.ofChannel, FiniteExperimentOn.P]
  calc
    η φ = t * posteriorLawDifferenceExp r E E' φ := hη φ
    _ =
        t * posteriorLawDifferenceExp r
          (experimentOfChannel (outcomePadLeft (Y := E'.OutcomeType) E.P))
          (experimentOfChannel (outcomePadRight (O := E.OutcomeType) E'.P)) φ := by
          rw [hdiff]

/-- Common-outcome tangent realization is closed under negating the signed
tangent law: swap the two realizing experiments. -/
theorem commonOutcomeTangentRealization_neg
    (hreal : FiniteCommonOutcomeTangentRealizationAssumptions.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) (η : PosteriorLawSigned A)
    (htan : PosteriorLawTangent η)
    (hηne : η ≠ ((fun _ => 0) : PosteriorLawSigned A)) :
    ∃ (t : ℝ), ∃ (_ht : 0 < t), ∃ (O : Type u),
    ∃ (hO : Fintype O), ∃ (hOdec : DecidableEq O),
      letI : Fintype O := hO
      letI : DecidableEq O := hOdec
      ∃ P R : Channel A O,
        ∀ φ : Dist A → ℝ,
          posteriorLawSignedSMul (-1) η φ =
            t * posteriorLawDifferenceExp r
              (experimentOfChannel P) (experimentOfChannel R) φ := by
  rcases hreal.tangent_as_common_outcome_difference r hr η htan hηne with
    ⟨t, ht, O, hO, hOdec, hrealized⟩
  letI : Fintype O := hO
  letI : DecidableEq O := hOdec
  rcases hrealized with ⟨P, R, hη⟩
  refine ⟨t, ht, O, hO, hOdec, R, P, ?_⟩
  intro φ
  calc
    posteriorLawSignedSMul (-1) η φ = -η φ := by
      simp [posteriorLawSignedSMul]
    _ = -(t * posteriorLawDifferenceExp r
            (experimentOfChannel P) (experimentOfChannel R) φ) := by
      rw [hη φ]
    _ = t * posteriorLawDifferenceExp r
            (experimentOfChannel R) (experimentOfChannel P) φ := by
      unfold posteriorLawDifferenceExp
      ring

end TraceableAgency
