import TraceableAgency.Section4.MoralHazard.Basic
import TraceableAgency.Section4.OptimizationKL
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Averaging teammates' random efforts produces Bernoulli rows. A uniform
quadratic divergence bound makes the trace component of the incentive bonus
vanish as the agent's effect vanishes. -/
namespace TraceableAgency.Section4
open TraceableAgency Set Filter Topology
universe u

 theorem finiteKL_bernoulli (p r : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    finiteKL (bernoulli p hp0 hp1) (bernoulli r hr0 hr1) = bernoulliKL p r := by
  simp [finiteKL, Fintype.sum_bool, bernoulli, bernoulliKL, add_comm]

 theorem bernoulliKL_nonneg {p r : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) : 0 ≤ bernoulliKL p r := by
  rw [← finiteKL_bernoulli p r hp.1 hp.2 hr.1.le hr.2.le]
  apply finiteKL_nonneg
  intro b _
  cases b <;> simp [bernoulli] <;> linarith [hr.1,hr.2]

 theorem bernoulliKL_pos {p r : ℝ} (hp : p ∈ Icc (0 : ℝ) 1)
    (hr : r ∈ Ioo (0 : ℝ) 1) (hne : p ≠ r) : 0 < bernoulliKL p r := by
  have hs : SupportIncluded (bernoulli p hp.1 hp.2) (bernoulli r hr.1.le hr.2.le) := by
    intro b _
    cases b <;> simp [bernoulli] <;> linarith [hr.1,hr.2]
  have hn := finiteKL_nonneg (bernoulli p hp.1 hp.2) (bernoulli r hr.1.le hr.2.le) hs
  have hneq : finiteKL (bernoulli p hp.1 hp.2) (bernoulli r hr.1.le hr.2.le) ≠ 0 := by
    intro hh
    have he := (finiteKL_eq_zero_iff _ _ hs).mp hh
    have hpq := congrArg (fun d : Dist Bool => d true) he
    exact hne hpq
  rw [← finiteKL_bernoulli p r hp.1 hp.2 hr.1.le hr.2.le]
  exact lt_of_le_of_ne hn (Ne.symm hneq)

 theorem bernoulliKL_le_chiSquare {p r : ℝ}
    (hp : p ∈ Ioo (0 : ℝ) 1) (hr : r ∈ Ioo (0 : ℝ) 1) :
    bernoulliKL p r ≤ (p-r)^2/(r*(1-r)) := by
  have hp1 : 0 < 1-p := sub_pos.mpr hp.2
  have hr1 : 0 < 1-r := sub_pos.mpr hr.2
  have h0 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hp.1 hr.1)) hp.1.le
  have h1 := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hp1 hr1)) hp1.le
  rw [Real.log_div (ne_of_gt hp.1) (ne_of_gt hr.1)] at h0
  rw [Real.log_div (ne_of_gt hp1) (ne_of_gt hr1)] at h1
  have he : p*(p/r-1)+(1-p)*((1-p)/(1-r)-1) = (p-r)^2/(r*(1-r)) := by
    field_simp [ne_of_gt hr.1, ne_of_gt hr1]
    <;> ring
  rw [← he]
  exact add_le_add h0 h1

 theorem bernoulliKL_uniform_quadratic_bound {p d epsilon : ℝ}
    (he : 0 < epsilon) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hr : p+d ∈ Icc epsilon (1-epsilon)) :
    0 ≤ bernoulliKL p (p+d) ∧ bernoulliKL p (p+d) ≤ d^2/epsilon^2 := by
  have hr' : p+d ∈ Ioo (0 : ℝ) 1 := ⟨he.trans_le hr.1, lt_of_le_of_lt hr.2 (by linarith)⟩
  refine ⟨bernoulliKL_nonneg ⟨hp.1.le,hp.2.le⟩ hr', ?_⟩
  have hden : epsilon^2 ≤ (p+d)*(1-p-d) := by
    have hh := mul_le_mul hr.1 (by linarith [hr.2] : epsilon ≤ 1-p-d) he.le hr'.1.le
    nlinarith
  calc
    bernoulliKL p (p+d) ≤ (p-(p+d))^2/((p+d)*(1-(p+d))) :=
      bernoulliKL_le_chiSquare hp hr'
    _ = d^2/((p+d)*(1-p-d)) := by ring
    _ ≤ d^2/epsilon^2 := div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos he) hden

 theorem traceBonus_uniform_bound {p d epsilon lambda : ℝ}
    (he : 0 < epsilon) (hp : p ∈ Ioo (0 : ℝ) 1)
    (hr : p+d ∈ Icc epsilon (1-epsilon)) (hd : 0 < d) (hl : 0 ≤ lambda) :
    0 ≤ lambda*bernoulliKL p (p+d)/d ∧
      lambda*bernoulliKL p (p+d)/d ≤ lambda*d/epsilon^2 := by
  have hb := bernoulliKL_uniform_quadratic_bound he hp hr
  refine ⟨div_nonneg (mul_nonneg hl hb.1) hd.le, ?_⟩
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb.2 hl) hd.le
  calc
    _ ≤ lambda*(d^2/epsilon^2)/d := hh
    _ = lambda*d/epsilon^2 := by
      field_simp [ne_of_gt hd]
      <;> ring

 theorem traceBonus_tendsto_zero {p d : ℕ → ℝ} {epsilon lambda : ℝ}
    (he : 0 < epsilon) (hl : 0 ≤ lambda)
    (hp : ∀ n, p n ∈ Ioo (0 : ℝ) 1)
    (hr : ∀ n, p n+d n ∈ Icc epsilon (1-epsilon))
    (hd : ∀ n, 0 < d n) (hdlim : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => lambda*bernoulliKL (p n) (p n+d n)/d n) atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => lambda*d n/epsilon^2) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hdlim).div_const (epsilon^2)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => (traceBonus_uniform_bound he (hp n) (hr n) (hd n) hl).1)
    (fun n => (traceBonus_uniform_bound he (hp n) (hr n) (hd n) hl).2)

noncomputable def teamSuccess {S : Type u} [Fintype S]
    (mu : Dist S) (g : Bool → S → ℝ) (a : Bool) : ℝ := ∑ s, mu s*g a s

 theorem teamSuccess_bounds {S : Type u} [Fintype S] (mu : Dist S)
    (g : Bool → S → ℝ) {lo hi : ℝ} (hg : ∀ a s, lo ≤ g a s ∧ g a s ≤ hi) (a : Bool) :
    lo ≤ teamSuccess mu g a ∧ teamSuccess mu g a ≤ hi := by
  have hl := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hg a s).1 (mu.nonneg s))
  have hh := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hg a s).2 (mu.nonneg s))
  simpa [teamSuccess, ← Finset.sum_mul, mu.sum_eq_one] using And.intro hl hh

 theorem teamSuccess_marginal_bound {S : Type u} [Fintype S] (mu : Dist S)
    (g : Bool → S → ℝ) {bound : ℝ}
    (hg : ∀ s, 0 ≤ g true s-g false s ∧ g true s-g false s ≤ bound) :
    0 ≤ teamSuccess mu g true-teamSuccess mu g false ∧
      teamSuccess mu g true-teamSuccess mu g false ≤ bound := by
  have hh := teamSuccess_bounds mu (fun _ s => g true s-g false s)
    (fun _ s => hg s) true
  simpa [teamSuccess, mul_sub, Finset.sum_sub_distrib] using hh


 theorem team_fraction_gap_le {S : Type u} [Fintype S]
    (mu : Dist S) (count : S → ℝ) (G : ℝ → ℝ) {L : NNReal}
    (hG : LipschitzWith L G) (hm : Monotone G) {n : ℝ} (hn : 0 < n) :
    let g := fun a s => G ((count s + if a then 1 else 0)/n)
    0 ≤ teamSuccess mu g true-teamSuccess mu g false ∧
      teamSuccess mu g true-teamSuccess mu g false ≤ (L : ℝ)/n := by
  dsimp only
  apply teamSuccess_marginal_bound
  intro s
  simp only [Bool.true_eq, Bool.false_eq_true, if_true, if_false, add_zero]
  have hstep : count s/n ≤ (count s+1)/n := by
    apply div_le_div_of_nonneg_right _ hn.le
    linarith
  have hnonneg : 0 ≤ G ((count s+1)/n)-G (count s/n) := sub_nonneg.mpr (hm hstep)
  refine ⟨hnonneg, ?_⟩
  have hh := hG.dist_le_mul ((count s+1)/n) (count s/n)
  rw [Real.dist_eq, abs_of_nonneg hnonneg, Real.dist_eq] at hh
  have he : (count s+1)/n-count s/n = 1/n := by ring
  rw [he, abs_of_nonneg (div_nonneg zero_le_one hn.le)] at hh
  simpa only [mul_one_div] using hh

 theorem mixture_bernoulli {S : Type u} [Fintype S] (mu : Dist S)
    (g : S → ℝ) (hg : ∀ s, g s ∈ Icc (0 : ℝ) 1) :
    Channel.outcomeMarginal (fun s => bernoulli (g s) (hg s).1 (hg s).2) mu =
      bernoulli (∑ s, mu s*g s)
        (Finset.sum_nonneg fun s _ => mul_nonneg (mu.nonneg s) (hg s).1)
        (by
          have hh := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) =>
            mul_le_mul_of_nonneg_left (hg s).2 (mu.nonneg s)
          simpa [mu.sum_eq_one] using hh) := by
  ext b
  cases b
  · simp [Channel.outcomeMarginal_apply, bernoulli, mul_sub, Finset.sum_sub_distrib, mu.sum_eq_one]
  · rfl

/-- A fixed positive effort cost requires a diverging incentive share when
one agent's positive effect on success tends to zero. -/
 theorem costBonus_tendsto_atTop {d : ℕ → ℝ} {cost : ℝ}
    (hc : 0 < cost) (hd : ∀ n, 0 < d n) (hdlim : Tendsto d atTop (𝓝 0)) :
    Tendsto (fun n => cost/d n) atTop atTop := by
  have hright : Tendsto d atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hdlim, Eventually.of_forall hd⟩
  simpa only [div_eq_mul_inv, Function.comp_def] using
    (tendsto_inv_nhdsGT_zero.comp hright).const_mul_atTop hc

end TraceableAgency.Section4
