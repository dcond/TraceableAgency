import TraceableAgency.Section4.OptimizationBasic

/-! Zero information is exactly independence, including priors on the boundary. -/
namespace TraceableAgency.Section4

universe u
variable {A Z : Type u} [Fintype A] [DecidableEq A] [Fintype Z] [DecidableEq Z]

def ActionOutputIndependent (q : Dist A) (K : Channel A Z) : Prop :=
  ∀ a z, q a * K a z = q a * Channel.outcomeMarginal K q z

theorem mutualInfo_eq_zero_iff_rows (q : Dist A) (K : Channel A Z) :
    mutualInfo q K = 0 ↔
      ∀ a, 0 < q a → K a = Channel.outcomeMarginal K q := by
  let m := Channel.outcomeMarginal K q
  let gap (z : Z) := entropyTerm (m z)-∑ a, q a * entropyTerm (K a z)
  have hg (z : Z) : 0 ≤ gap z := by
    apply sub_nonneg.mpr
    simp_rw [entropyTerm_eq_negMulLog ((K _).nonneg z)]
    rw [entropyTerm_eq_negMulLog (m.nonneg z)]
    exact Real.concaveOn_negMulLog.le_map_sum
      (fun a (_ : a ∈ (Finset.univ : Finset A)) => q.nonneg a)
      q.sum_eq_one (fun a _ => (K a).nonneg z)
  have hsum : (∑ z, gap z) = mutualInfo q K := by
    simp only [gap, mutualInfo, entropy, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  constructor
  · intro h a ha
    have hz := summand_eq_zero_of_sum_eq_zero_of_nonneg' gap hg (hsum.trans h)
    apply Dist.ext
    intro z
    have heq : Real.negMulLog (∑ a, q a * K a z) =
        ∑ a, q a * Real.negMulLog (K a z) := by
      have hh := sub_eq_zero.mp (hz z)
      change entropyTerm (m z) = _ at hh
      rw [entropyTerm_eq_negMulLog (m.nonneg z)] at hh
      simpa only [m, Channel.outcomeMarginal_apply,
        entropyTerm_eq_negMulLog ((K _).nonneg z)] using hh
    have hj := (Real.strictConcaveOn_negMulLog.map_sum_eq_iff'
      (t := (Finset.univ : Finset A)) (w := fun a => q a) (p := fun a => K a z)
      (fun a _ => q.nonneg a) q.sum_eq_one (fun a _ => (K a).nonneg z)).mp
        (by simpa only [smul_eq_mul] using heq)
    exact hj a (Finset.mem_univ a) (ne_of_gt ha)
  · intro h
    have heq (a : A) : q a * entropy (K a) = q a * entropy m := by
      by_cases ha : 0 < q a
      · rw [h a ha]
      · have hz : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
        simp [hz]
    unfold mutualInfo
    rw [show (∑ a, q a * entropy (K a)) = ∑ a, q a * entropy m from
      Finset.sum_congr rfl (fun a _ => heq a), ← Finset.sum_mul, q.sum_eq_one, one_mul]
    exact sub_self _

theorem mutualInfo_eq_zero_iff_independent (q : Dist A) (K : Channel A Z) :
    mutualInfo q K = 0 ↔ ActionOutputIndependent q K := by
  rw [mutualInfo_eq_zero_iff_rows]
  constructor
  · intro h a z
    by_cases ha : 0 < q a
    · rw [h a ha]
    · have hz : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
      simp [hz]
  · intro h a ha
    ext z
    exact mul_left_cancel₀ (ne_of_gt ha) (h a z)

end TraceableAgency.Section4
