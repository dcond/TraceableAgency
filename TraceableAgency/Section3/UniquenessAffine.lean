import TraceableAgency.Section3.UniquenessMixture

/-! # Positive affine uniqueness of branch-additive indices -/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1

universe u

variable {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
variable {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}

/-- Branch additivity fixes the ordinal transform to one positive affine map
on all finite alphabets and all priors, including boundary priors. -/
theorem positiveAffine_of_commonScale_branchAdditive
    (hlambda : 0 < lambda) (hrep : WithinChannelRepresentation F u lambda)
    {W : CommonIndex O} (hW : CommonScaleRepresentation F W)
    (hadd : BranchAdditiveIndex W) :
    ∃ alpha beta : ℝ, 0 < alpha ∧
      ∀ E, W E = alpha * valueIndex u lambda E + beta := by
  let o := minimumOutcome u
  let B : FiniteExperiment O := .ofChannel (Dist.pure PUnit.unit) (deterministicPayoffChannel o)
  have hB : valueIndex u lambda B = minPayoff u :=
    traceTemperedValue_deterministicPayoffChannel u lambda o
  obtain ⟨J, hJ⟩ := exists_valueIndex_eq_add u hlambda o (x := 1) (by norm_num)
  change valueIndex u lambda J = minPayoff u + 1 at hJ
  have hpos : 0 < W J - W B := by
    apply sub_pos.mpr
    apply lt_of_not_ge
    intro hh
    have hv := (commonScale_order_iff hrep hW J B).mp hh
    rw [hJ, hB] at hv
    linarith
  refine ⟨W J - W B, W B - (W J - W B) * minPayoff u, hpos, ?_⟩
  intro E
  let x := valueIndex u lambda E - minPayoff u
  have hx0 : 0 ≤ x := sub_nonneg.mpr (minPayoff_le_valueIndex u hlambda.le E)
  by_cases hx : x = 0
  · have heq : valueIndex u lambda E = valueIndex u lambda B := by
      rw [hB]
      exact sub_eq_zero.mp hx
    have hw := commonScale_eq_of_value_eq hrep hW heq
    rw [hw, heq, hB]
    ring
  have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
  by_cases hx1 : x ≤ 1
  · obtain ⟨D, hDv, hDw⟩ :=
      commonScale_branchAdditive_dilution hrep hW hadd o J x hxpos hx1
    have hDE : valueIndex u lambda D = valueIndex u lambda E := by
      rw [hJ] at hDv
      change valueIndex u lambda D = minPayoff u + x * (minPayoff u + 1 - minPayoff u) at hDv
      dsimp only [x] at hDv
      linarith
    have hWDE := commonScale_eq_of_value_eq hrep hW hDE
    change W D - W B = x * (W J - W B) at hDw
    rw [hWDE] at hDw
    dsimp only [x] at hDw
    nlinarith [hDw]
  · have hxge : 1 ≤ x := le_of_lt (lt_of_not_ge hx1)
    obtain ⟨D, hDv, hDw⟩ :=
      commonScale_branchAdditive_dilution hrep hW hadd o E (1/x)
        (one_div_pos.mpr hxpos) ((div_le_one hxpos).mpr hxge)
    have hDJ : valueIndex u lambda D = valueIndex u lambda J := by
      change valueIndex u lambda D = minPayoff u + (1/x) * x at hDv
      rw [one_div_mul_cancel hx] at hDv
      exact hDv.trans hJ.symm
    have hWDJ := commonScale_eq_of_value_eq hrep hW hDJ
    change W D - W B = (1/x) * (W E - W B) at hDw
    rw [hWDJ] at hDw
    have hh : (W J - W B) * x = W E - W B := by
      calc
        (W J - W B) * x = ((1/x) * (W E - W B)) * x := by rw [hDw]
        _ = W E - W B := by field_simp
    dsimp only [x] at hh
    nlinarith [hh]

 theorem branchAdditive_of_affine
    {W : CommonIndex O} {alpha beta : ℝ}
    (hform : ∀ E, W E = alpha * valueIndex u lambda E + beta) :
    BranchAdditiveIndex W := by
  intro A Y R _ _ _ _ _ _ _ _ _ q P K L
  simp_rw [hform]
  have h := branchAdditive_valueIndex u lambda q P K L
  calc
    _ = alpha * (valueIndex u lambda (.ofChannel q (commonPayoffCompound (fun _ : Y => R) P K)) -
          valueIndex u lambda (.ofChannel q (commonPayoffCompound (fun _ : Y => R) P L))) := by ring
    _ = alpha * ∑ y, (Channel.outcomeMarginal P q) y *
        (valueIndex u lambda (.ofChannel (branchPosterior P q y) (K y)) -
          valueIndex u lambda (.ofChannel (branchPosterior P q y) (L y))) := by rw [h]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

 theorem commonScale_of_positiveAffine
    (hrep : WithinChannelRepresentation F u lambda)
    {W : CommonIndex O} {alpha beta : ℝ} (halpha : 0 < alpha)
    (hform : ∀ E, W E = alpha * valueIndex u lambda E + beta) :
    CommonScaleRepresentation F W := by
  rw [commonScale_iff_order hrep]
  intro E D
  rw [hform, hform, add_le_add_iff_right]
  exact mul_le_mul_iff_right₀ halpha

 theorem commonScale_branchAdditive_iff_positiveAffine
    (hlambda : 0 < lambda) (hrep : WithinChannelRepresentation F u lambda)
    (W : CommonIndex O) :
    CommonScaleRepresentation F W ∧ BranchAdditiveIndex W ↔
      ∃ alpha beta : ℝ, 0 < alpha ∧
        ∀ E, W E = alpha * valueIndex u lambda E + beta := by
  constructor
  · rintro ⟨hW, hadd⟩
    exact positiveAffine_of_commonScale_branchAdditive hlambda hrep hW hadd
  · rintro ⟨alpha, beta, halpha, hform⟩
    exact ⟨commonScale_of_positiveAffine hrep halpha hform, branchAdditive_of_affine hform⟩

 theorem branchAdditive_iff_positiveAffine
    (hlambda : 0 < lambda) (hrep : WithinChannelRepresentation F u lambda)
    {W : CommonIndex O} (hW : CommonScaleRepresentation F W) :
    BranchAdditiveIndex W ↔ ∃ alpha beta : ℝ, 0 < alpha ∧
      ∀ E, W E = alpha * valueIndex u lambda E + beta := by
  exact ⟨positiveAffine_of_commonScale_branchAdditive hlambda hrep hW,
    fun ⟨_, _, _, hform⟩ => branchAdditive_of_affine hform⟩

end TraceableAgency.Section3
