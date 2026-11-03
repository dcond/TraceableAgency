import TraceableAgency.Section3.UniquenessTransform

/-! # Public dilution implied by numerical branch additivity -/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1

universe u

 theorem outcomeMarginal_constant
    {A Y : Type u} [Fintype A] [Fintype Y]
    (q : Dist A) (p : Dist Y) : Channel.outcomeMarginal (fun _ : A => p) q = p := by
  apply Dist.ext
  intro y
  simp only [Channel.outcomeMarginal_apply]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

 theorem mutualInfo_constant
    {A Y : Type u} [Fintype A] [Fintype Y]
    (q : Dist A) (p : Dist Y) : mutualInfo q (fun _ : A => p) = 0 := by
  unfold mutualInfo
  rw [outcomeMarginal_constant, ← Finset.sum_mul, q.sum_eq_one]
  ring

 theorem posterior_constant_of_pos
    {A Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Y]
    (q : Dist A) (p : Dist Y) (y : Y) (hy : 0 < p y) :
    branchPosterior (fun _ : A => p) q y = q := by
  have hpos : 0 < Channel.outcomeMarginal (fun _ : A => p) q y := by
    rw [outcomeMarginal_constant]
    exact hy
  unfold branchPosterior Channel.posterior
  rw [dif_pos hpos]
  apply Dist.ext
  intro a
  change q a * p y / Channel.outcomeMarginal (fun _ : A => p) q y = q a
  rw [outcomeMarginal_constant]
  exact mul_div_cancel_right₀ (q a) (ne_of_gt hy)

noncomputable def silentChannel
    {O A R : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R] [DecidableEq R]
    (o : O) (r : R) : Channel A (O × R) := fun _ => Dist.pure (o,r)

 theorem value_silentChannel
    {O A R : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [Fintype R] [DecidableEq R]
    (u : O → ℝ) (lambda : ℝ) (q : Dist A) (o : O) (r : R) :
    traceTemperedValue u lambda q (silentChannel o r) = u o := by
  unfold traceTemperedValue silentChannel
  rw [mutualInfo_constant]
  simp only [mul_zero, add_zero, expectedPayoffUtility, Dist.pure_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]

noncomputable def publicCoin (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Dist RelevanceBit.{u} :=
  Dist.mix t ht0 ht1 (Dist.pure (ULift.up true)) (Dist.pure (ULift.up false))

@[simp] theorem publicCoin_true (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    publicCoin.{u} t ht0 ht1 (ULift.up true) = t := by
  simp [publicCoin, Dist.mix_apply, Dist.pure_apply]

@[simp] theorem publicCoin_false (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    publicCoin.{u} t ht0 ht1 (ULift.up false) = 1-t := by
  simp [publicCoin, Dist.mix_apply, Dist.pure_apply]

theorem sum_relevanceBit (f : RelevanceBit.{u} → ℝ) :
    ∑ b, f b = f (ULift.up true) + f (ULift.up false) := by
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp f]
  simp [Fintype.sum_bool, Equiv.ulift]

/-- A branch-additive common index values public dilution by its probability,
including at the endpoints. The baseline is a deterministic material payoff. -/
theorem commonScale_branchAdditive_dilution
    {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda)
    {W : CommonIndex O} (hW : CommonScaleRepresentation F W)
    (hadd : BranchAdditiveIndex W)
    (o : O) (E : FiniteExperiment O)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ D : FiniteExperiment O,
      valueIndex u lambda D = u o + t * (valueIndex u lambda E - u o) ∧
      W D - W (.ofChannel (Dist.pure PUnit.unit) (deterministicPayoffChannel o)) =
        t * (W E - W (.ofChannel (Dist.pure PUnit.unit) (deterministicPayoffChannel o))) := by
  classical
  let r : E.Rec := Classical.choice E.recNonempty
  let S : Channel E.Act (O × E.Rec) := silentChannel o r
  let P : Channel E.Act RelevanceBit := fun _ => publicCoin t ht0.le ht1
  let K : RelevanceBit → Channel E.Act (O × E.Rec) :=
    fun b => if b.down then E.channel else S
  let L : RelevanceBit → Channel E.Act (O × E.Rec) := fun _ => S
  let D : FiniteExperiment O := .ofChannel E.prior
    (commonPayoffCompound (fun _ : RelevanceBit => E.Rec) P K)
  let B : FiniteExperiment O := .ofChannel E.prior
    (commonPayoffCompound (fun _ : RelevanceBit => E.Rec) P L)
  let B0 : FiniteExperiment O := .ofChannel (Dist.pure PUnit.unit) (deterministicPayoffChannel o)
  have hbase : valueIndex u lambda B0 = u o :=
    traceTemperedValue_deterministicPayoffChannel u lambda o
  have hS (p : Dist E.Act) : valueIndex u lambda (.ofChannel p S) = u o :=
    value_silentChannel u lambda p o r
  have hm : Channel.outcomeMarginal P E.prior = publicCoin t ht0.le ht1 :=
    outcomeMarginal_constant E.prior _
  have hp : branchPosterior P E.prior (ULift.up true) = E.prior :=
    posterior_constant_of_pos E.prior _ _ (by simpa using ht0)
  have hB : valueIndex u lambda B = u o := by
    dsimp only [B, valueIndex, FiniteExperiment.ofChannel]
    rw [traceTemperedValue_commonCompound, mutualInfo_constant]
    simp only [L, show ∀ p : Dist E.Act, traceTemperedValue u lambda p S = u o from hS]
    rw [← Finset.sum_mul, (Channel.outcomeMarginal P E.prior).sum_eq_one]
    ring
  have hD : valueIndex u lambda D = u o + t * (valueIndex u lambda E - u o) := by
    dsimp only [D, valueIndex, FiniteExperiment.ofChannel]
    rw [traceTemperedValue_commonCompound, mutualInfo_constant]
    rw [hm]
    simp only [sum_relevanceBit, K, Bool.false_eq_true, if_false, if_true,
      publicCoin_false, publicCoin_true, hp]
    rw [show traceTemperedValue u lambda (branchPosterior P E.prior (ULift.up false)) S = u o
      from hS _]
    ring
  have hWbase : W B = W B0 := commonScale_eq_of_value_eq hrep hW (hB.trans hbase.symm)
  have hWS (p : Dist E.Act) : W (.ofChannel p S) = W B0 :=
    commonScale_eq_of_value_eq hrep hW ((hS p).trans hbase.symm)
  have h := hadd E.prior P K L
  change W D - W B = _ at h
  rw [hm] at h
  simp only [sum_relevanceBit, K, L, Bool.false_eq_true, if_false, if_true,
    publicCoin_false, publicCoin_true, hp, sub_self, mul_zero, zero_add, add_zero] at h
  rw [hWbase, hWS] at h
  exact ⟨D, hD, h⟩

end TraceableAgency.Section3
