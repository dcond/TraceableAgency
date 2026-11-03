import TraceableAgency.Section4.Binary.Classification

/-! The infinite endpoint limits in v11 Proposition 24(i).  Missing output
support is treated by an actual limit to infinity, never by `Real.log 0`. -/
namespace TraceableAgency.Section4
open TraceableAgency Set Filter Topology
universe u
variable {Z : Type u} [Fintype Z]

private noncomputable def missingMass (p r : Dist Z) : ℝ :=
  ∑ z, if p z = 0 then r z else 0

private noncomputable def regularSlope (p r : Dist Z) (x : ℝ) : ℝ :=
  ∑ z, if p z = 0 then r z * (-Real.log (r z) - 1)
    else (r z-p z)*(-Real.log (mixMass p r x z)-1)

private theorem missingMass_pos (p r : Dist Z) (hc : ¬ SupportIncluded r p) :
    0 < missingMass p r := by
  classical
  have hex : ∃ z, p z = 0 ∧ 0 < r z := by
    by_contra hn
    apply hc
    intro z hz
    have hp : p z ≠ 0 := by
      intro he
      exact hn ⟨z,he,hz⟩
    exact lt_of_le_of_ne (p.nonneg z) (Ne.symm hp)
  obtain ⟨z,hp,hr⟩ := hex
  apply Finset.sum_pos'
  · intro y _
    split_ifs <;> first | exact r.nonneg y | rfl
  · exact ⟨z,Finset.mem_univ z,by simpa [hp] using hr⟩

private theorem regularSlope_tendsto_zero (p r : Dist Z) :
    Tendsto (regularSlope p r) (𝓝 0) (𝓝 (regularSlope p r 0)) := by
  classical
  apply tendsto_finsetSum
  intro z _
  by_cases hz : p z = 0
  · simp only [hz,if_true]
    exact tendsto_const_nhds
  · simp only [hz,if_false]
    have hm : mixMass p r 0 z ≠ 0 := by simpa [mixMass] using hz
    have hh : ContinuousAt (fun x : ℝ => Real.log (mixMass p r x z)) 0 :=
      (hasDerivAt_mixMass p r 0 z).continuousAt.log hm
    exact (hh.neg.sub_const 1).const_mul (r z-p z)

private theorem mixEntropySlope_split (p r : Dist Z) {x : ℝ} (hx : 0 < x) :
    mixEntropySlope p r x = regularSlope p r x - missingMass p r * Real.log x := by
  classical
  unfold mixEntropySlope regularSlope missingMass
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : p z = 0
  · simp only [hp,if_true,sub_zero,mixMass,zero_add]
    by_cases hr : r z = 0
    · simp [hr]
    · rw [Real.log_mul (ne_of_gt hx) hr]
      ring
  · simp [hp]

/-- If the second row has an output absent from the first, the binary marginal
information gain tends to positive infinity as its mixing weight falls to zero. -/
theorem binaryGain_tendsto_zero_of_not_support (p r : Dist Z)
    (hc : ¬ SupportIncluded r p) :
    Tendsto (binaryGain p r) (𝓝[>] 0) atTop := by
  have hr : Tendsto (fun x => regularSlope p r x + (entropy p-entropy r))
      (𝓝[>] 0) (𝓝 (regularSlope p r 0 + (entropy p-entropy r))) :=
    ((regularSlope_tendsto_zero p r).mono_left nhdsWithin_le_nhds).add tendsto_const_nhds
  have hi := tendsto_neg_atBot_atTop.comp
    (Real.tendsto_log_nhdsGT_zero.const_mul_atBot (missingMass_pos p r hc))
  have ht := hr.add_atTop hi
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [binaryGain,mixEntropySlope_split p r hx]
  dsimp only [Function.comp_apply]
  ring

/-- Swapping the two output rows reverses the information slope. -/
theorem binaryGain_swap (p r : Dist Z) (x : ℝ) :
    binaryGain p r x = -binaryGain r p (1-x) := by
  unfold binaryGain mixEntropySlope
  have hm (z : Z) : mixMass r p (1-x) z = mixMass p r x z := by
    unfold mixMass
    ring
  simp_rw [hm]
  have hs : (∑ z, (p z-r z)*(-Real.log (mixMass p r x z)-1)) =
      -(∑ z, (r z-p z)*(-Real.log (mixMass p r x z)-1)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [hs]
  ring

/-- If the first row has an output absent from the second, the binary marginal
information gain tends to negative infinity as the second row's weight rises to one. -/
theorem binaryGain_tendsto_one_of_not_support (p r : Dist Z)
    (hc : ¬ SupportIncluded p r) :
    Tendsto (binaryGain p r) (𝓝[<] 1) atBot := by
  have hs : Tendsto (fun x : ℝ => 1-x) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (tendsto_const_nhds (x := (1:ℝ))).sub
        (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1))
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (show x < 1 from hx)
  have hh := tendsto_neg_atTop_atBot.comp
    ((binaryGain_tendsto_zero_of_not_support r p hc).comp hs)
  exact hh.congr' (Filter.Eventually.of_forall (fun x => (binaryGain_swap p r x).symm))

end TraceableAgency.Section4
