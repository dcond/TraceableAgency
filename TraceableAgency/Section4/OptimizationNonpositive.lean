import TraceableAgency.Section4.OptimizationSupport
import TraceableAgency.Section4.InformationZero

/-! Negative information weights select payoff-maximising, uninformative lotteries. -/
namespace TraceableAgency.Section4
universe u
variable {A Z : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype Z] [DecidableEq Z]

def RewardMaximizingSupport (r : A → ℝ) (q : Dist A) : Prop :=
  ∀ a, 0 < q a → ∀ b, r b ≤ r a

theorem reward_average_le (r : A → ℝ) (q : Dist A) (M : ℝ) (hm : ∀ a, r a ≤ M) :
    (∑ a, q a * r a) ≤ M := by
  calc
    (∑ a, q a * r a) ≤ ∑ a, q a * M :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hm a) (q.nonneg a)
    _ = M := by rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

theorem reward_average_eq_iff (r : A → ℝ) (q : Dist A) (M : ℝ) (hm : ∀ a, r a ≤ M) :
    (∑ a, q a * r a) = M ↔ ∀ a, 0 < q a → r a = M := by
  have heq : (∑ a, q a * (M-r a)) = M-(∑ a, q a*r a) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, q.sum_eq_one, one_mul]
  constructor
  · intro h a ha
    have hz : (∑ a, q a * (M-r a)) = 0 := by rw [heq,h]; ring
    have hh := summand_eq_zero_of_sum_eq_zero_of_nonneg' _
      (fun a => mul_nonneg (q.nonneg a) (sub_nonneg.mpr (hm a))) hz a
    have := (mul_eq_zero.mp hh).resolve_left (ne_of_gt ha)
    linarith
  · intro h
    calc
      (∑ a, q a*r a) = ∑ a, q a*M := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : 0 < q a
        · rw [h a ha]
        · have hz : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
          simp [hz]
      _ = M := by rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

theorem nonpositive_optimal_iff (r : A → ℝ) {lambda : ℝ} (hl : lambda ≤ 0)
    (K : Channel A Z) (q : Dist A) :
    IsOptimal r lambda K q ↔
      RewardMaximizingSupport r q ∧ lambda * mutualInfo q K = 0 := by
  obtain ⟨a₀,_,hmax⟩ := Finset.exists_max_image Finset.univ r Finset.univ_nonempty
  have hm : ∀ a, r a ≤ r a₀ := fun a => hmax a (Finset.mem_univ a)
  have hbound (p : Dist A) : rowRewardValue r lambda p K ≤ r a₀ := by
    have ha := reward_average_le r p (r a₀) hm
    have hi := mul_nonpos_of_nonpos_of_nonneg hl (mutualInfo_nonneg p K)
    unfold rowRewardValue
    linarith
  constructor
  · intro hq
    have hv : r a₀ ≤ rowRewardValue r lambda q K := by
      simpa only [rowRewardValue_pure_action] using hq (Dist.pure a₀)
    have ha := reward_average_le r q (r a₀) hm
    have hi := mul_nonpos_of_nonpos_of_nonneg hl (mutualInfo_nonneg q K)
    have he : (∑ a, q a*r a) = r a₀ := by unfold rowRewardValue at hv; linarith
    refine ⟨?_, ?_⟩
    · intro a hqa b
      rw [(reward_average_eq_iff r q (r a₀) hm).mp he a hqa]
      exact hm b
    · unfold rowRewardValue at hv
      linarith
  · rintro ⟨hq,hi⟩
    have ha : (∑ a, q a*r a) = r a₀ := by
      apply (reward_average_eq_iff r q (r a₀) hm).mpr
      intro a hqa
      exact le_antisymm (hm a) (hq a hqa a₀)
    have hv : rowRewardValue r lambda q K = r a₀ := by
      unfold rowRewardValue
      rw [ha,hi,add_zero]
    intro p
    rw [hv]
    exact hbound p

theorem negative_optimal_iff (r : A → ℝ) {lambda : ℝ} (hl : lambda < 0)
    (K : Channel A Z) (q : Dist A) :
    IsOptimal r lambda K q ↔ RewardMaximizingSupport r q ∧ mutualInfo q K = 0 := by
  rw [nonpositive_optimal_iff r hl.le K q, mul_eq_zero]
  simp only [ne_of_lt hl, false_or]

theorem zero_optimal_iff (r : A → ℝ) (K : Channel A Z) (q : Dist A) :
    IsOptimal r 0 K q ↔ RewardMaximizingSupport r q := by
  rw [nonpositive_optimal_iff r (le_refl 0) K q]
  simp

theorem nonpositive_pure_optimal (r : A → ℝ) {lambda : ℝ} (hl : lambda ≤ 0)
    (K : Channel A Z) (a : A) (ha : ∀ b, r b ≤ r a) :
    IsOptimal r lambda K (Dist.pure a) := by
  intro p
  rw [rowRewardValue_pure_action]
  have hu := reward_average_le r p (r a) ha
  have hi := mul_nonpos_of_nonpos_of_nonneg hl (mutualInfo_nonneg p K)
  unfold rowRewardValue
  linarith

end TraceableAgency.Section4
