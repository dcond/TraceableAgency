import TraceableAgency.Section4.OptimizationKKT

/-! The paper's explicit equal-payoff example of menu-dependent choice odds. -/
namespace TraceableAgency.Section4

noncomputable def overlapThirdRow : Dist (Fin 3) where
  prob := ![1/2,0,1/2]
  nonneg := by intro i; fin_cases i <;> norm_num
  sum_eq_one := by norm_num [Fin.sum_univ_succ]

noncomputable def overlapChannel : Channel (Fin 3) (Fin 3) :=
  ![Dist.pure 0,Dist.pure 1,overlapThirdRow]

noncomputable def overlapOptimum : Dist (Fin 3) where
  prob := ![1/3,4/9,2/9]
  nonneg := by intro i; fin_cases i <;> norm_num
  sum_eq_one := by norm_num [Fin.sum_univ_succ]

noncomputable def overlapOutput : Dist (Fin 3) where
  prob := ![4/9,4/9,1/9]
  nonneg := by intro i; fin_cases i <;> norm_num
  sum_eq_one := by norm_num [Fin.sum_univ_succ]

theorem overlap_output : Channel.outcomeMarginal overlapChannel overlapOptimum = overlapOutput := by
  ext z
  fin_cases z <;> norm_num [Channel.outcomeMarginal_apply, overlapChannel, overlapOptimum,
    overlapOutput, overlapThirdRow, Dist.pure_apply, Fin.sum_univ_succ]

theorem overlap_divergences (a : Fin 3) :
    finiteKL (overlapChannel a) overlapOutput = Real.log (9/4) := by
  have h4 : Real.log (4:ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num, Real.log_pow]; norm_num
  have h9 : Real.log (9:ℝ) = 2*Real.log 3 := by
    rw [show (9:ℝ)=3^2 by norm_num, Real.log_pow]; norm_num
  fin_cases a <;>
    simp [finiteKL, overlapChannel, overlapOutput, overlapThirdRow, Dist.pure_apply,
      Fin.sum_univ_succ, Real.log_div, h4, h9] <;> ring

theorem overlap_optimal (v : ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    IsOptimal (fun _ : Fin 3 => v) lambda overlapChannel overlapOptimum := by
  apply (optimal_iff_kkt _ hl _ _).mpr
  rw [overlap_output]
  refine ⟨?_,v+lambda*Real.log (9/4),?_,?_⟩
  · intro a z _
    fin_cases z <;> norm_num [overlapOutput]
  · intro a
    simp [rowScore,overlap_divergences]
  · intro a _
    simp [rowScore,overlap_divergences]

theorem overlap_output_injective : Function.Injective (Channel.outcomeMarginal overlapChannel) := by
  intro q p h
  have h0 := congrArg (fun d : Dist (Fin 3) => d 0) h
  have h1 := congrArg (fun d : Dist (Fin 3) => d 1) h
  have h2 := congrArg (fun d : Dist (Fin 3) => d 2) h
  norm_num [Channel.outcomeMarginal_apply, overlapChannel, overlapThirdRow,
    Dist.pure_apply, Fin.sum_univ_succ] at h0 h1 h2
  simp only [show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    if_false, zero_add] at h2
  have hv : (![1/2,0,1/2] : Fin 3 → ℝ) 2 = 1/2 := rfl
  rw [hv] at h2
  apply Dist.ext
  intro a
  fin_cases a <;> dsimp <;> linarith

theorem overlap_unique_optimum (v : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (q : Dist (Fin 3)) (hq : IsOptimal (fun _ : Fin 3 => v) lambda overlapChannel q) :
    q = overlapOptimum :=
  optimal_unique_of_output_injective _ hl _ overlap_output_injective _ _ hq (overlap_optimal v hl)

noncomputable def twoMenuChannel : Channel (Fin 2) (Fin 3) := ![Dist.pure 0,Dist.pure 1]

noncomputable def twoMenuOutput : Dist (Fin 3) where
  prob := ![1/2,1/2,0]
  nonneg := by intro i; fin_cases i <;> norm_num
  sum_eq_one := by norm_num [Fin.sum_univ_succ]

theorem twoMenu_output : Channel.outcomeMarginal twoMenuChannel Dist.uniform = twoMenuOutput := by
  ext z
  fin_cases z <;> norm_num [Channel.outcomeMarginal_apply, twoMenuChannel, twoMenuOutput,
    Dist.uniform_apply, Dist.pure_apply, Fin.sum_univ_succ]

theorem twoMenu_divergences (a : Fin 2) :
    finiteKL (twoMenuChannel a) twoMenuOutput = Real.log 2 := by
  fin_cases a <;> simp [finiteKL, twoMenuChannel, twoMenuOutput,
    Dist.pure_apply, Fin.sum_univ_succ, Real.log_div]

theorem twoMenu_optimal (v : ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    IsOptimal (fun _ : Fin 2 => v) lambda twoMenuChannel Dist.uniform := by
  apply (optimal_iff_kkt _ hl _ _).mpr
  rw [twoMenu_output]
  refine ⟨?_,v+lambda*Real.log 2,?_,?_⟩
  · intro a z hz
    fin_cases a <;> fin_cases z
    all_goals norm_num [twoMenuChannel,twoMenuOutput,Dist.pure_apply] at *
  · intro a
    simp [rowScore,twoMenu_divergences]
  · intro a _
    simp [rowScore,twoMenu_divergences]

theorem twoMenu_output_injective : Function.Injective (Channel.outcomeMarginal twoMenuChannel) := by
  intro q p h
  have h0 := congrArg (fun d : Dist (Fin 3) => d 0) h
  have h1 := congrArg (fun d : Dist (Fin 3) => d 1) h
  norm_num [Channel.outcomeMarginal_apply, twoMenuChannel, Dist.pure_apply,
    Fin.sum_univ_succ] at h0 h1
  ext a
  fin_cases a <;> assumption

theorem twoMenu_unique_optimum (v : ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (q : Dist (Fin 2)) (hq : IsOptimal (fun _ : Fin 2 => v) lambda twoMenuChannel q) :
    q = Dist.uniform :=
  optimal_unique_of_output_injective _ hl _ twoMenu_output_injective _ _ hq (twoMenu_optimal v hl)

theorem overlap_restricts_to_twoMenu (a : Fin 2) :
    overlapChannel (Fin.castLE (by omega) a) = twoMenuChannel a := by
  fin_cases a <;> rfl

theorem overlap_iia_ratios :
    (Dist.uniform (A := Fin 2)) 0 / (Dist.uniform (A := Fin 2)) 1 = 1 ∧
      overlapOptimum 0 / overlapOptimum 1 = 3/4 := by
  norm_num [Dist.uniform_apply,overlapOptimum]

end TraceableAgency.Section4
