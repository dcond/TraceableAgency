import TraceableAgency.Section4.OptimizationBasic
import TraceableAgency.Section4.SupportEntropy

/-! Every optimum with positive information weight covers every reachable output. -/
namespace TraceableAgency.Section4

universe u
variable {A Z : Type u} [Fintype A] [DecidableEq A]
  [Fintype Z] [DecidableEq Z]

theorem outcomeMarginal_pure_action (K : Channel A Z) (a : A) :
    Channel.outcomeMarginal K (Dist.pure a) = K a := by
  ext z
  simp [Channel.outcomeMarginal_apply, Dist.pure_apply]

theorem rowRewardValue_pure_action (r : A → ℝ) (lambda : ℝ)
    (K : Channel A Z) (a : A) :
    rowRewardValue r lambda (Dist.pure a) K = r a := by
  simp [rowRewardValue, mutualInfo, outcomeMarginal_pure_action, Dist.pure_apply]

theorem exists_improvement_of_missing_output (r : A → ℝ)
    {lambda : ℝ} (hl : 0 < lambda) (K : Channel A Z) (q : Dist A)
    (a : A) (z : Z) (hz : 0 < K a z)
    (hm : Channel.outcomeMarginal K q z = 0) :
    ∃ p : Dist A, rowRewardValue r lambda q K < rowRewardValue r lambda p K := by
  let v := rowRewardValue r lambda q K
  let d := lambda * K a z
  have hd : 0 < d := mul_pos hl hz
  let M := max 0 ((v-r a)/d)+1
  have hM : 0 < M := by dsimp [M]; have := le_max_left 0 ((v-r a)/d); linarith
  have hratio : (v-r a)/d < M := by
    dsimp [M]; have := le_max_right 0 ((v-r a)/d); linarith
  have hlarge : v-r a < d*M := by
    have := (div_lt_iff₀ hd).mp hratio
    linarith
  let t := Real.exp (-M)
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hlog : Real.log t = -M := Real.log_exp _
  let p := Dist.mix (1-t) (by linarith) (by linarith) q (Dist.pure a)
  refine ⟨p, ?_⟩
  have he := entropy_mix_gain_at_zero (Channel.outcomeMarginal K q) (K a) z hm t ht0 ht1
  have hev := mul_le_mul_of_nonneg_left he hl.le
  have hv := rowRewardValue_mix_gap r lambda K q (Dist.pure a) (1-t)
    (by linarith) (by linarith)
  rw [outcomeMarginal_pure_action, rowRewardValue_pure_action] at hv
  simp only [sub_sub_cancel] at hv
  rw [hlog] at hev
  have hpositive : 0 < t*(r a-v+d*M) :=
    mul_pos ht0 (by linarith)
  change v < rowRewardValue r lambda p K
  change rowRewardValue r lambda p K = _ at hv
  change _ ≤ lambda * entropy _ at hev
  dsimp only [v, d] at hpositive
  nlinarith [hev]

theorem optimal_coversRows (r : A → ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (K : Channel A Z) (q : Dist A) (hq : IsOptimal r lambda K q) :
    CoversRows K (Channel.outcomeMarginal K q) := by
  intro a z hz
  by_contra hn
  have hm : Channel.outcomeMarginal K q z = 0 :=
    le_antisymm (le_of_not_gt hn) ((Channel.outcomeMarginal K q).nonneg z)
  obtain ⟨p,hp⟩ := exists_improvement_of_missing_output r hl K q a z hz hm
  exact (not_lt_of_ge (hq p)) hp

end TraceableAgency.Section4
