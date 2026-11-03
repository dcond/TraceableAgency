import TraceableAgency.Theorem1.Benchmark
import Mathlib.Analysis.Convex.StdSimplex

/-! # Finite-action objectives with arbitrary row rewards

The row reward can be expected material utility, or expected utility net of
an action-specific effort cost. No information formula is imposed on rewards.
-/
namespace TraceableAgency.Section4

open TraceableAgency Theorem1

universe u

noncomputable def rowRewardValue {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (q : Dist A) (K : Channel A Z) : ℝ :=
  (∑ a, q a * r a) + lambda * mutualInfo q K

def IsOptimal {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) (q : Dist A) : Prop :=
  ∀ p : Dist A, rowRewardValue r lambda p K ≤ rowRewardValue r lambda q K

/-- The reference output distribution is positive wherever any row is positive. -/
def CoversRows {A Z : Type u} [Fintype Z] (K : Channel A Z) (p : Dist Z) : Prop :=
  ∀ a z, 0 < K a z → 0 < p z

/-- Support inclusion, the finite-divergence condition. -/
def SupportIncluded {Z : Type u} [Fintype Z] (p s : Dist Z) : Prop :=
  ∀ z, 0 < p z → 0 < s z

/-- Finite KL sum. It represents KL only under `SupportIncluded`; unsupported
references are handled explicitly rather than by Lean's value of `log 0`. -/
noncomputable def finiteKL {Z : Type u} [Fintype Z] (p s : Dist Z) : ℝ :=
  ∑ z, p z * (Real.log (p z) - Real.log (s z))

noncomputable def rowScore {A Z : Type u} [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) (p : Dist Z) (a : A) : ℝ :=
  r a + lambda * finiteKL (K a) p

 theorem rowRewardValue_material
    {O A R : Type u} [Fintype O] [Fintype A] [Fintype R]
    (u : O → ℝ) (lambda : ℝ) (q : Dist A) (K : Channel A (O × R)) :
    rowRewardValue (fun a => ∑ z, K a z * u z.1) lambda q K =
      traceTemperedValue u lambda q K := rfl

 theorem rowRewardValue_entropy {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (q : Dist A) (K : Channel A Z) :
    rowRewardValue r lambda q K = lambda * entropy (Channel.outcomeMarginal K q) +
      ∑ a, q a * (r a - lambda * entropy (K a)) := by
  unfold rowRewardValue mutualInfo
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  ring

 theorem outcomeMarginal_mix {A Z : Type u} [Fintype A] [Fintype Z]
    (K : Channel A Z) (q p : Dist A) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Channel.outcomeMarginal K (Dist.mix t ht0 ht1 q p) =
      Dist.mix t ht0 ht1 (Channel.outcomeMarginal K q) (Channel.outcomeMarginal K p) := by
  apply Dist.ext
  intro z
  simp only [Channel.outcomeMarginal_apply, Dist.mix_apply, add_mul, mul_assoc,
    Finset.sum_add_distrib, ← Finset.mul_sum]

 theorem entropyTerm_mix_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * entropyTerm x + (1-t) * entropyTerm y ≤ entropyTerm (t*x+(1-t)*y) := by
  rw [entropyTerm_eq_negMulLog hx, entropyTerm_eq_negMulLog hy,
    entropyTerm_eq_negMulLog (add_nonneg (mul_nonneg ht0 hx) (mul_nonneg (sub_nonneg.mpr ht1) hy))]
  exact Real.concaveOn_negMulLog.2 hx hy ht0 (sub_nonneg.mpr ht1) (by ring)

 theorem entropy_mix_le {Z : Type u} [Fintype Z]
    (q p : Dist Z) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * entropy q + (1-t) * entropy p ≤ entropy (Dist.mix t ht0 ht1 q p) := by
  unfold entropy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun z _ => entropyTerm_mix_le _ _ (q.nonneg z) (p.nonneg z) t ht0 ht1

 theorem mutualInfo_nonneg {A Z : Type u} [Fintype A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) : 0 ≤ mutualInfo q K := by
  classical
  exact sub_nonneg.mpr (sum_weighted_entropy_le_entropy_actionPushforward q K)

 theorem rowRewardValue_mix_gap {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) (q p : Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    rowRewardValue r lambda (Dist.mix t ht0 ht1 q p) K =
      t * rowRewardValue r lambda q K + (1-t) * rowRewardValue r lambda p K +
      lambda * (entropy (Dist.mix t ht0 ht1 (Channel.outcomeMarginal K q)
        (Channel.outcomeMarginal K p)) - t * entropy (Channel.outcomeMarginal K q) -
        (1-t) * entropy (Channel.outcomeMarginal K p)) := by
  simp only [rowRewardValue_entropy, outcomeMarginal_mix, Dist.mix_apply, add_mul,
    Finset.sum_add_distrib]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

 theorem rowRewardValue_concave {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) {lambda : ℝ} (hlambda : 0 ≤ lambda) (K : Channel A Z)
    (q p : Dist A) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * rowRewardValue r lambda q K + (1-t) * rowRewardValue r lambda p K ≤
      rowRewardValue r lambda (Dist.mix t ht0 ht1 q p) K := by
  rw [rowRewardValue_mix_gap]
  have h := entropy_mix_le (Channel.outcomeMarginal K q) (Channel.outcomeMarginal K p) t ht0 ht1
  nlinarith

 theorem continuous_rowRewardValue {A Z : Type u} [Fintype A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) :
    Continuous (fun q : Dist A => rowRewardValue r lambda q K) := by
  classical
  simp_rw [rowRewardValue_entropy]
  apply Continuous.add
  · apply continuous_const.mul
    apply continuous_entropy.comp
    apply continuous_induced_rng.mpr
    apply continuous_pi
    intro z
    exact continuous_finsetSum _ fun a _ => (Dist.continuous_prob_apply a).mul_const _
  · exact continuous_finsetSum _ fun a _ => (Dist.continuous_prob_apply a).mul_const _

 theorem exists_optimal {A Z : Type u} [Fintype A] [Nonempty A] [Fintype Z]
    (r : A → ℝ) (lambda : ℝ) (K : Channel A Z) :
    ∃ q : Dist A, IsOptimal r lambda K q := by
  let f : (A → ℝ) → ℝ := fun x => lambda * (∑ z, entropyTerm (∑ a, x a * K a z)) +
    ∑ a, x a * (r a - lambda * entropy (K a))
  have hf : Continuous f := by
    apply Continuous.add
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro z _
      apply continuous_entropyTerm.comp
      exact continuous_finsetSum _ fun a _ => (continuous_apply a).mul_const _
    · exact continuous_finsetSum _ fun a _ => (continuous_apply a).mul_const _
  have hne : (stdSimplex ℝ A).Nonempty :=
    ⟨Dist.uniform.prob, Dist.uniform.nonneg, Dist.uniform.sum_eq_one⟩
  obtain ⟨x, hx, hmax⟩ := (isCompact_stdSimplex ℝ A).exists_isMaxOn hne hf.continuousOn
  refine ⟨⟨x,hx.1,hx.2⟩, ?_⟩
  intro p
  have hp := hmax (show p.prob ∈ stdSimplex ℝ A from ⟨p.nonneg,p.sum_eq_one⟩)
  change f p.prob ≤ f x at hp
  simpa only [rowRewardValue_entropy, entropy, Channel.outcomeMarginal_apply, f] using hp

end TraceableAgency.Section4
