import TraceableAgency.Info.Entropy
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.Deriv

/-! Differential identities for the binary mixture of arbitrary finite output
rows, including coordinates absent from both rows. -/
namespace TraceableAgency.Section4
open TraceableAgency Set Filter Topology
universe u
variable {Z : Type u} [Fintype Z]

noncomputable def mixMass (p r : Dist Z) (x : ℝ) (z : Z) : ℝ :=
  p z + x * (r z - p z)
noncomputable def mixEntropy (p r : Dist Z) (x : ℝ) : ℝ :=
  ∑ z, Real.negMulLog (mixMass p r x z)
noncomputable def mixEntropySlope (p r : Dist Z) (x : ℝ) : ℝ :=
  ∑ z, (r z - p z) * (-Real.log (mixMass p r x z) - 1)
noncomputable def mixEntropyCurvature (p r : Dist Z) (x : ℝ) : ℝ :=
  -(∑ z, (r z - p z)^2 / mixMass p r x z)

 theorem hasDerivAt_mixMass (p r : Dist Z) (x : ℝ) (z : Z) :
    HasDerivAt (fun t => mixMass p r t z) (r z - p z) x := by
  convert! ((hasDerivAt_id x).mul_const (r z - p z)).const_add (p z) using 1 <;>
    simp only [mixMass, id_eq, one_mul]

 theorem hasDerivAt_mixEntropy (p r : Dist Z) (x : ℝ)
    (hx : ∀ z, mixMass p r x z ≠ 0 ∨ (p z = 0 ∧ r z = 0)) :
    HasDerivAt (mixEntropy p r) (mixEntropySlope p r x) x := by
  apply HasDerivAt.fun_sum
  intro z _
  rcases hx z with hz | ⟨hp, hr⟩
  · convert! (Real.hasDerivAt_negMulLog hz).comp x (hasDerivAt_mixMass p r x z) using 1 <;>
      simp only [Function.comp_apply, mul_comm]
  · simpa [mixMass, hp, hr] using (hasDerivAt_const x (0 : ℝ))

 theorem hasDerivAt_mixEntropySlope (p r : Dist Z) (x : ℝ)
    (hx : ∀ z, mixMass p r x z ≠ 0 ∨ (p z = 0 ∧ r z = 0)) :
    HasDerivAt (mixEntropySlope p r) (mixEntropyCurvature p r x) x := by
  unfold mixEntropySlope mixEntropyCurvature
  rw [← Finset.sum_neg_distrib]
  apply HasDerivAt.fun_sum
  intro z _
  rcases hx z with hz | ⟨hp, hr⟩
  · have hh := (((Real.hasDerivAt_log hz).comp x
      (hasDerivAt_mixMass p r x z)).neg.sub_const 1).const_mul (r z - p z)
    convert! hh using 1 <;> simp [Function.comp_apply, div_eq_mul_inv] <;> ring
  · simpa [mixMass, hp, hr] using (hasDerivAt_const x (0 : ℝ))

 theorem mixMass_nonneg (p r : Dist Z) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (z : Z) :
    0 ≤ mixMass p r x z := by
  have hh := add_nonneg (mul_nonneg (sub_nonneg.mpr hx.2) (p.nonneg z))
    (mul_nonneg hx.1 (r.nonneg z))
  dsimp [mixMass]
  nlinarith

 theorem mixMass_pos_or_both_zero (p r : Dist Z) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (z : Z) :
    0 < mixMass p r x z ∨ (p z = 0 ∧ r z = 0) := by
  by_cases hp : p z = 0
  · by_cases hr : r z = 0
    · exact Or.inr ⟨hp, hr⟩
    · left
      have hpos := mul_pos hx.1 (lt_of_le_of_ne (r.nonneg z) (Ne.symm hr))
      simpa [mixMass, hp] using hpos
  · left
    have hpos := mul_pos (sub_pos.mpr hx.2) (lt_of_le_of_ne (p.nonneg z) (Ne.symm hp))
    have hn := mul_nonneg hx.1.le (r.nonneg z)
    dsimp [mixMass]
    nlinarith

 theorem mixEntropyCurvature_neg (p r : Dist Z) (hne : p ≠ r) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) : mixEntropyCurvature p r x < 0 := by
  have hex : ∃ z, p z ≠ r z := by
    by_contra hn
    push Not at hn
    exact hne (Dist.ext hn)
  obtain ⟨z, hz⟩ := hex
  have hm : 0 < mixMass p r x z := by
    rcases mixMass_pos_or_both_zero p r hx z with hh | ⟨hp, hr⟩
    · exact hh
    · exact (hz (hp.trans hr.symm)).elim
  have hterm : 0 < (r z - p z)^2 / mixMass p r x z :=
    div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm hz))) hm
  have hsum : 0 < ∑ z, (r z - p z)^2 / mixMass p r x z :=
    Finset.sum_pos' (fun z _ => div_nonneg (sq_nonneg _)
      (mixMass_nonneg p r ⟨hx.1.le, hx.2.le⟩ z)) ⟨z, Finset.mem_univ z, hterm⟩
  exact neg_neg_of_pos hsum

 theorem mixEntropySlope_strictAnti (p r : Dist Z) (hne : p ≠ r) :
    StrictAntiOn (mixEntropySlope p r) (Ioo (0 : ℝ) 1) := by
  have hd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :=
    hasDerivAt_mixEntropySlope p r x (fun z =>
      (mixMass_pos_or_both_zero p r hx z).imp (fun h => ne_of_gt h) id)
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 1)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := interior_subset hx
    rw [(hd x hx').deriv]
    exact mixEntropyCurvature_neg p r hne hx'

 theorem hasDerivAt_mixEntropy_zero (p r : Dist Z)
    (hc : ∀ z, p z = 0 → r z = 0) :
    HasDerivAt (mixEntropy p r) (mixEntropySlope p r 0) 0 := by
  apply hasDerivAt_mixEntropy
  intro z
  by_cases hz : p z = 0
  · exact Or.inr ⟨hz, hc z hz⟩
  · exact Or.inl (by simpa [mixMass] using hz)

 theorem continuous_mixEntropy (p r : Dist Z) : Continuous (mixEntropy p r) := by
  unfold mixEntropy mixMass
  fun_prop

 theorem mixEntropy_eq_distMix (p r : Dist Z) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    mixEntropy p r x = entropy (Dist.mix x hx0 hx1 r p) := by
  unfold mixEntropy entropy
  apply Finset.sum_congr rfl
  intro z _
  rw [entropyTerm_eq_negMulLog (Dist.mix x hx0 hx1 r p |>.nonneg z)]
  congr 1
  simp [mixMass, Dist.mix_apply]
  ring

end TraceableAgency.Section4
