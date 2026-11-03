import TraceableAgency.Section3.Independence.GiniStructure
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Continuity at null outputs and record data processing for Gini reduction.
The column bound squeezes a vanishing output's contribution to zero. A
zero-safe weighted Cauchy--Schwarz inequality proves the garbling comparison. -/
namespace TraceableAgency.Section3.Independence
open TraceableAgency Theorem1 Filter Topology
universe u

noncomputable def giniColumn {A Z : Type u} [Fintype A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) (z : Z) : ℝ :=
  (∑ a, (q a * K a z)^2) / (Channel.outcomeMarginal K q) z

theorem giniColumn_nonneg {A Z : Type u} [Fintype A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) (z : Z) : 0 ≤ giniColumn q K z :=
  div_nonneg (Finset.sum_nonneg fun a _ => sq_nonneg _)
    ((Channel.outcomeMarginal K q).nonneg z)

theorem giniColumn_le_marginal {A Z : Type u} [Fintype A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) (z : Z) :
    giniColumn q K z ≤ (Channel.outcomeMarginal K q) z := by
  have hs := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun a => q a * K a z)
    (fun a _ => mul_nonneg (q.nonneg a) ((K a).nonneg z))
  change (∑ a, (q a * K a z)^2) ≤ ((Channel.outcomeMarginal K q) z)^2 at hs
  exact div_le_of_le_mul₀ ((Channel.outcomeMarginal K q).nonneg z)
    ((Channel.outcomeMarginal K q).nonneg z) (by simpa only [pow_two] using hs)

theorem tendsto_giniColumn_of_converges
    {A Z : Type u} [Fintype A] [DecidableEq A] [Fintype Z] [DecidableEq Z]
    (Kn : ℕ → Channel A Z) (K : Channel A Z)
    (qn : ℕ → Dist A) (q : Dist A)
    (hK : ChannelConverges Kn K) (hq : DistConverges qn q) (z : Z) :
    Tendsto (fun n => giniColumn (qn n) (Kn n) z) atTop (𝓝 (giniColumn q K z)) := by
  have hm := tendsto_outcomeMarginal_of_converges' Kn K qn q hK hq z
  by_cases hz : (Channel.outcomeMarginal K q) z = 0
  · have hc : giniColumn q K z = 0 := by
      unfold giniColumn
      rw [hz, div_zero]
    rw [hc]
    rw [hz] at hm
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
      (fun n => giniColumn_nonneg (qn n) (Kn n) z)
      (fun n => giniColumn_le_marginal (qn n) (Kn n) z)
  · apply Tendsto.div _ hm hz
    apply tendsto_finsetSum
    intro a _
    exact ((hq a).mul (hK a z)).pow 2

theorem tendsto_giniInformation_of_converges
    {A Z : Type u} [Fintype A] [DecidableEq A] [Fintype Z] [DecidableEq Z]
    (Kn : ℕ → Channel A Z) (K : Channel A Z)
    (qn : ℕ → Dist A) (q : Dist A)
    (hK : ChannelConverges Kn K) (hq : DistConverges qn q) :
    Tendsto (fun n => giniInformation (qn n) (Kn n)) atTop
      (𝓝 (giniInformation q K)) := by
  apply Tendsto.sub
  · apply tendsto_finsetSum
    intro z _
    exact tendsto_giniColumn_of_converges Kn K qn q hK hq z
  · apply tendsto_finsetSum
    intro a _
    exact (hq a).pow 2

/-- Weighted Cauchy--Schwarz with zero weights admitted. The corresponding
numerator must vanish on a zero denominator, as it does for joint masses. -/
theorem weighted_square_sum_div_le
    {I : Type u} [Fintype I] (x w t : I → ℝ)
    (hw : ∀ i, 0 ≤ w i) (ht : ∀ i, 0 ≤ t i)
    (hz : ∀ i, w i = 0 → x i = 0) :
    (∑ i, x i * t i)^2 / (∑ i, w i * t i) ≤
      ∑ i, (x i)^2 / w i * t i := by
  have hpos : ∀ i, 0 ≤ (x i)^2 / w i * t i :=
    fun i => mul_nonneg (div_nonneg (sq_nonneg _) (hw i)) (ht i)
  apply div_le_of_le_mul₀ (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (ht i))
    (Finset.sum_nonneg fun i _ => hpos i)
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun i _ => hpos i) (fun i _ => mul_nonneg (hw i) (ht i))
  intro i _
  by_cases hi : w i = 0
  · simp [hi, hz i hi]
  · have he : (x i * t i)^2 = (x i)^2 / w i * t i * (w i * t i) := by
      field_simp
    exact he.le

theorem giniInformation_record_postprocess_le
    {A Z Y : Type u} [Fintype A] [Fintype Z] [Fintype Y]
    (q : Dist A) (K : Channel A Z) (T : Channel Z Y) :
    giniInformation q (Channel.postprocess K T) ≤ giniInformation q K := by
  classical
  have hzero (a : A) (z : Z) (hz : (Channel.outcomeMarginal K q) z = 0) :
      q a * K a z = 0 := by
    have hle : q a * K a z ≤ (Channel.outcomeMarginal K q) z :=
      Finset.single_le_sum (fun b _ => mul_nonneg (q.nonneg b) ((K b).nonneg z))
        (Finset.mem_univ a)
    exact le_antisymm (hz ▸ hle) (mul_nonneg (q.nonneg a) ((K a).nonneg z))
  have hlocal (a : A) (y : Y) :
      (q a * Channel.postprocess K T a y)^2 /
          (Channel.outcomeMarginal (Channel.postprocess K T) q) y ≤
        ∑ z, (q a * K a z)^2 / (Channel.outcomeMarginal K q) z * T z y := by
    have hh := weighted_square_sum_div_le
      (fun z => q a * K a z) (fun z => (Channel.outcomeMarginal K q) z)
      (fun z => T z y) (fun z => (Channel.outcomeMarginal K q).nonneg z)
      (fun z => (T z).nonneg y) (fun z => hzero a z)
    have hm : (Channel.outcomeMarginal (Channel.postprocess K T) q) y =
        ∑ z, (Channel.outcomeMarginal K q) z * T z y := by
      rw [outcomeMarginal_postprocess_eq_actionPushforward]
      rfl
    rw [hm]
    simpa only [Channel.postprocess, Finset.mul_sum, mul_assoc] using hh
  unfold giniInformation
  apply sub_le_sub_right
  calc
    (∑ y, (∑ a, (q a * Channel.postprocess K T a y)^2) /
        (Channel.outcomeMarginal (Channel.postprocess K T) q) y) =
        ∑ y, ∑ a, (q a * Channel.postprocess K T a y)^2 /
          (Channel.outcomeMarginal (Channel.postprocess K T) q) y := by
      simp only [Finset.sum_div]
    _ ≤ ∑ y, ∑ a, ∑ z,
        (q a * K a z)^2 / (Channel.outcomeMarginal K q) z * T z y :=
      Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun a _ => hlocal a y
    _ = ∑ a, ∑ z, ∑ y,
        (q a * K a z)^2 / (Channel.outcomeMarginal K q) z * T z y := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ a, ∑ z, (q a * K a z)^2 / (Channel.outcomeMarginal K q) z := by
      simp_rw [← Finset.mul_sum, Dist.sum_eq_one, mul_one]
    _ = ∑ z, (∑ a, (q a * K a z)^2) / (Channel.outcomeMarginal K q) z := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_div]

theorem giniFamily_a2 {O : Type u} [Fintype O] [DecidableEq O] (v : O → ℝ) :
    A2_Continuity (giniFamily v) := by
  apply scoreFamily_a2
  intro A R _ _ _ _ _ _ Kn K qn q hK hq
  exact (tendsto_expectedPayoffUtility_of_converges v Kn K qn q hK hq).add
    (tendsto_giniInformation_of_converges Kn K qn q hK hq)

theorem giniFamily_a6 {O : Type u} [Fintype O] [DecidableEq O] (v : O → ℝ) :
    A6_RecordDataProcessing (giniFamily v) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [giniFamily_pairWeak, expectedPayoffUtility_recordPostprocess]
  simpa only [add_comm, recordPostprocess] using
    (add_le_add_left (giniInformation_record_postprocess_le q K
      (payoffPreservingRecordKernel T)) (expectedPayoffUtility v q K))

end TraceableAgency.Section3.Independence
