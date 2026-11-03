import TraceableAgency.Section4.OptimizationLogit
import TraceableAgency.Section4.OptimizationCollapse

/-! # Odds, equal rewards, and duplicate-channel consequences -/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1
universe u

 theorem logitDist_odds {A : Type u} [Fintype A] [Nonempty A]
    (r : A → ℝ) (lambda : ℝ) (a b : A) :
    logitDist r lambda a / logitDist r lambda b = Real.exp ((r a-r b)/lambda) := by
  change (Real.exp (r a/lambda)/logitNormalizer r lambda) /
    (Real.exp (r b/lambda)/logitNormalizer r lambda) = _
  rw [sub_div,Real.exp_sub]
  field_simp [ne_of_gt (logitNormalizer_pos r lambda)]

 theorem disjoint_optimal_odds {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (hd : DisjointRows K) (q : Dist A) (hq : IsOptimal r lambda K q) (a b : A) :
    q a / q b = Real.exp ((r a-r b)/lambda) := by
  rw [(disjoint_optimal_iff_logit r hlambda K hd q).mp hq]
  exact logitDist_odds r lambda a b

/-- Changes elsewhere in a disjoint-support menu cannot alter the odds between
retained actions whose rewards remain the same. -/
 theorem disjoint_menu_independent_odds {A B Z Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
    (r : A → ℝ) (s : B → ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (K : Channel A Z) (L : Channel B Y) (hK : DisjointRows K) (hL : DisjointRows L)
    (q : Dist A) (p : Dist B) (hq : IsOptimal r lambda K q) (hp : IsOptimal s lambda L p)
    (a b : A) (a' b' : B) (ha : r a = s a') (hb : r b = s b') :
    q a / q b = p a' / p b' := by
  rw [disjoint_optimal_odds r hlambda K hK q hq,
    disjoint_optimal_odds s hlambda L hL p hp,ha,hb]

 theorem logitDist_constant {A : Type u} [Fintype A] [Nonempty A]
    (c lambda : ℝ) : logitDist (fun _ : A => c) lambda = Dist.uniform := by
  apply Dist.ext
  intro a
  change Real.exp (c/lambda)/(∑ _ : A,Real.exp (c/lambda)) = 1/(Fintype.card A : ℝ)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

 theorem disjoint_equal_rewards_iff_uniform {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z] [DecidableEq Z]
    (c : ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (K : Channel A Z) (hd : DisjointRows K) (q : Dist A) :
    IsOptimal (fun _ => c) lambda K q ↔ q = Dist.uniform := by
  rw [disjoint_optimal_iff_logit _ hlambda K hd,logitDist_constant]

/-- Three equally rewarded, separately recorded alternatives each get mass 1/3. -/
 theorem disjoint_three_equal_rewards {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z] [DecidableEq Z]
    (hcard : Fintype.card A = 3) (c : ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (K : Channel A Z) (hd : DisjointRows K) (q : Dist A)
    (hq : IsOptimal (fun _ => c) lambda K q) (a : A) : q a = 1/3 := by
  rw [(disjoint_equal_rewards_iff_uniform c hlambda K hd q).mp hq,Dist.uniform_apply,hcard]
  norm_num

 theorem material_constant_channel_all_optimal {A O R : Type u}
    [Fintype A] [Fintype O] [Fintype R]
    (v : O → ℝ) (lambda : ℝ) (p : Dist (O × R)) (q : Dist A) :
    IsOptimal (fun _ => ∑ z, p z * v z.1) lambda (fun _ => p) q :=
  constant_channel_all_optimal _ _ p q

/-- With equal row rewards, maximizing the criterion is precisely channel capacity. -/
 theorem constant_rewards_optimal_iff_capacity {A Z : Type u}
    [Fintype A] [Fintype Z] (c : ℝ) {lambda : ℝ} (hlambda : 0 < lambda)
    (K : Channel A Z) (q : Dist A) :
    IsOptimal (fun _ => c) lambda K q ↔ ∀ p, mutualInfo p K ≤ mutualInfo q K := by
  unfold IsOptimal rowRewardValue
  simp only [← Finset.sum_mul, Dist.sum_eq_one, one_mul, add_le_add_iff_left]
  exact forall_congr' fun p => mul_le_mul_iff_right₀ hlambda

/-- A rival reaching a missing consequence rules out pure choice at any finite reward gap. -/
 theorem pure_not_optimal_of_missing_output {A Z : Type u}
    [Fintype A] [DecidableEq A] [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (a b : A) (z : Z) (hb : 0 < K b z) (ha : K a z = 0) :
    ¬ IsOptimal r lambda K (Dist.pure a) := by
  intro h
  have hc := ((pure_optimal_iff r hlambda K a).mp h).1 b z hb
  rw [ha] at hc
  exact lt_irrefl 0 hc

end TraceableAgency.Section4
