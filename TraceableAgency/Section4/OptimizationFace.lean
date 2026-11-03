import TraceableAgency.Section4.OptimizationKKT
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-! # The exact set of optimal input lotteries -/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1
universe u

 theorem optimal_iff_output_and_active {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (qstar : Dist A) (hqstar : IsOptimal r lambda K qstar) (q : Dist A) :
    IsOptimal r lambda K q ↔
      Channel.outcomeMarginal K q = Channel.outcomeMarginal K qstar ∧
      ∀ a, 0 < q a → rowScore r lambda K (Channel.outcomeMarginal K qstar) a =
        rowRewardValue r lambda qstar K := by
  constructor
  · intro hq
    have he := optimal_output_unique r hlambda K q qstar hq hqstar
    refine ⟨he, ?_⟩
    intro a ha
    have hh := optimal_rowScore_eq_on_support r hlambda K q hq a ha
    have hv := le_antisymm (hqstar q) (hq qstar)
    simpa only [he,hv] using hh
  · rintro ⟨he,hs⟩
    have hv : rowRewardValue r lambda q K = rowRewardValue r lambda qstar K := by
      rw [rowRewardValue_eq_weighted_scores, he]
      exact (weightedAverage_eq_iff q _ _ (optimal_rowScore_le r hlambda K qstar hqstar)).mpr hs
    intro p
    rw [hv]
    exact hqstar p

/-- Strict inequalities at every unused action make a pure optimum unique. -/
 theorem pure_unique_of_strict_scores {A Z : Type u} [Fintype A] [DecidableEq A]
    [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z) (a : A)
    (hc : CoversRows K (K a))
    (hs : ∀ b, b ≠ a → r b + lambda * finiteKL (K b) (K a) < r a)
    (q : Dist A) (hq : IsOptimal r lambda K q) : q = Dist.pure a := by
  have ha : IsOptimal r lambda K (Dist.pure a) := (pure_optimal_iff r hlambda K a).mpr
    ⟨hc, fun b => by
      by_cases hb : b = a
      · subst b; simp
      · exact (hs b hb).le⟩
  have hactive := ((optimal_iff_output_and_active r hlambda K (Dist.pure a) ha q).mp hq).2
  have hz (b : A) (hb : b ≠ a) : q b = 0 := by
    apply le_antisymm _ (q.nonneg b)
    apply le_of_not_gt
    intro hp
    have hh := hactive b hp
    simp only [outcomeMarginal_pure_action, rowRewardValue_pure_action, rowScore] at hh
    exact (ne_of_lt (hs b hb)) hh
  have hqa : q a = 1 := by
    have hh := q.sum_eq_one
    rw [Finset.sum_eq_single a] at hh
    · exact hh
    · intro b _ hb; exact hz b hb
    · simp
  apply Dist.ext
  intro b
  by_cases hb : b = a
  · subst b; simp [hqa]
  · simp [Dist.pure_apply,hb,hz b hb]

/-- An affinely independent family of rows gives an injective output map. -/
 theorem output_injective_of_affineIndependent {A Z : Type u}
    [Fintype A] [Fintype Z] (K : Channel A Z)
    (h : AffineIndependent ℝ (fun a => (K a).prob)) :
    Function.Injective (Channel.outcomeMarginal K) := by
  intro q p he
  have hw : (∑ a, q a) = ∑ a, p a := by rw [q.sum_eq_one,p.sum_eq_one]
  have hv : (∑ a, q a • (K a).prob) = ∑ a, p a • (K a).prob := by
    funext z
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Channel.outcomeMarginal_apply] using
      congrArg (fun d : Dist Z => d z) he
  exact Dist.ext fun a => h.eq_of_sum_eq_sum hw hv a (Finset.mem_univ a)

private theorem sum_members_eq_sum {A : Type u} [Fintype A]
    (s : Set A) [DecidablePred (· ∈ s)] (f : A → ℝ) (hz : ∀ a, a ∉ s → f a = 0) :
    (∑ a : s, f a.1) = ∑ a, f a := by
  classical
  rw [← Finset.sum_subtype (s := Finset.univ.filter (fun a => a ∈ s))
    (by intro a; simp) f, Finset.sum_filter]
  exact Finset.sum_congr rfl fun a _ => by
    by_cases h : a ∈ s <;> simp [h, hz a]

/-- Affine independence is needed only for the rows permitted in the support. -/
 theorem dist_eq_of_affineIndependent_on {A Z : Type u} [Fintype A] [Fintype Z]
    (K : Channel A Z) (s : Set A)
    (hind : AffineIndependent ℝ (fun a : s => (K a.1).prob))
    (q p : Dist A) (hq : ∀ a, 0 < q a → a ∈ s)
    (hp : ∀ a, 0 < p a → a ∈ s)
    (he : Channel.outcomeMarginal K q = Channel.outcomeMarginal K p) : q = p := by
  classical
  have hq0 (a : A) (ha : a ∉ s) : q a = 0 :=
    le_antisymm (le_of_not_gt fun hh => ha (hq a hh)) (q.nonneg a)
  have hp0 (a : A) (ha : a ∉ s) : p a = 0 :=
    le_antisymm (le_of_not_gt fun hh => ha (hp a hh)) (p.nonneg a)
  have hw : (∑ a : s, q a.1) = ∑ a : s, p a.1 := by
    rw [sum_members_eq_sum s _ hq0, sum_members_eq_sum s _ hp0,
      q.sum_eq_one, p.sum_eq_one]
  have hv : (∑ a : s, q a.1 • (K a.1).prob) = ∑ a : s, p a.1 • (K a.1).prob := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_members_eq_sum s (fun a => q a * K a z) (fun a ha => by rw [hq0 a ha, zero_mul]),
      sum_members_eq_sum s (fun a => p a * K a z) (fun a ha => by rw [hp0 a ha, zero_mul])]
    exact congrArg (fun d : Dist Z => d z) he
  apply Dist.ext
  intro a
  by_cases ha : a ∈ s
  · exact hind.eq_of_sum_eq_sum hw hv ⟨a,ha⟩ (Finset.mem_univ _)
  · rw [hq0 a ha,hp0 a ha]

/-- The optimum is unique when its active rows are affinely independent. -/
 theorem optimal_unique_of_active_affineIndependent {A Z : Type u}
    [Fintype A] [DecidableEq A] [Fintype Z] [DecidableEq Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 < lambda) (K : Channel A Z)
    (qstar : Dist A) (hqstar : IsOptimal r lambda K qstar)
    (hind : AffineIndependent ℝ (fun a :
      {a // rowScore r lambda K (Channel.outcomeMarginal K qstar) a =
        rowRewardValue r lambda qstar K} => (K a.1).prob))
    (q : Dist A) (hq : IsOptimal r lambda K q) : q = qstar := by
  have hh := (optimal_iff_output_and_active r hlambda K qstar hqstar q).mp hq
  exact dist_eq_of_affineIndependent_on K _ hind q qstar hh.2
    (optimal_rowScore_eq_on_support r hlambda K qstar hqstar) hh.1

end TraceableAgency.Section4
