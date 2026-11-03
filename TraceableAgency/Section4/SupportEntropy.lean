import TraceableAgency.Info.DataProcessing
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Entropy gains from introducing an output absent from the current mixture.
The explicit bound handles boundary lotteries without assuming differentiability.+-/
namespace TraceableAgency.Section4

universe u
variable {X : Type u} [Fintype X] [DecidableEq X]

theorem entropyTerm_mix_gain_nonneg (p r : Dist X) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (x : X) :
    (1-t)*entropyTerm (p x)+t*entropyTerm (r x) ≤
      entropyTerm (Dist.mix (1-t) (by linarith) (by linarith) p r x) := by
  have h := Real.concaveOn_negMulLog.2 (p.nonneg x) (r.nonneg x)
    (by linarith : 0 ≤ 1-t) ht0 (by ring : 1-t+t=1)
  simp only [smul_eq_mul] at h
  rw [entropyTerm_eq_negMulLog (p.nonneg x), entropyTerm_eq_negMulLog (r.nonneg x),
    entropyTerm_eq_negMulLog
      ((Dist.mix (1-t) (by linarith) (by linarith) p r).nonneg x)]
  simpa only [Dist.mix_apply, sub_sub_cancel] using h

theorem entropy_mix_gain_at_zero (p r : Dist X) (z : X) (hpz : p z = 0)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (1-t)*entropy p+t*entropy r-t*r z*Real.log t ≤
      entropy (Dist.mix (1-t) (by linarith) (by linarith) p r) := by
  let m := Dist.mix (1-t) (by linarith) (by linarith) p r
  let gap (x : X) := entropyTerm (m x)-((1-t)*entropyTerm (p x)+t*entropyTerm (r x))
  have hg (x : X) : 0 ≤ gap x := sub_nonneg.mpr (entropyTerm_mix_gain_nonneg p r t ht0.le ht1 x)
  have hz : gap z = -t*r z*Real.log t := by
    dsimp [gap, m]
    simp only [Dist.mix_apply, hpz, mul_zero, zero_add, sub_sub_cancel, entropyTerm_zero]
    rw [entropyTerm_mul ht0.le (r.nonneg z), entropyTerm_eq_neg_mul_log ht0]
    ring
  have hsum : (∑ x, gap x) = entropy m-(1-t)*entropy p-t*entropy r := by
    simp only [gap, entropy, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    ring
  have h := Finset.single_le_sum (fun x (_ : x ∈ (Finset.univ : Finset X)) => hg x)
    (Finset.mem_univ z)
  rw [hz, hsum] at h
  dsimp [m] at h
  linarith

end TraceableAgency.Section4
