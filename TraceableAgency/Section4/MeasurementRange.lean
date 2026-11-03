import TraceableAgency.Section3.Range
import TraceableAgency.Section3.UniquenessMixture
import TraceableAgency.Section3.Independence.Basic

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

noncomputable def informationIndex (E : FiniteExperiment O) : ℝ :=
  mutualInfo E.prior E.channel

noncomputable def materialIndex (v : O → ℝ) (E : FiniteExperiment O) : ℝ :=
  expectedPayoffUtility v E.prior E.channel

theorem valueIndex_eq_material_information (v : O → ℝ) (lambda : ℝ) (E : FiniteExperiment O) :
    valueIndex v lambda E = materialIndex v E + lambda * informationIndex E := rfl

noncomputable def binaryPayoffLaw (op om : O) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) : Dist O :=
  Dist.mix b hb0 hb1 (Dist.pure op) (Dist.pure om)

theorem expected_binaryPayoffLaw (v : O → ℝ) (op om : O)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    payoffLotteryExpected v (binaryPayoffLaw op om b hb0 hb1) =
      b * v op + (1-b) * v om := by
  unfold payoffLotteryExpected binaryPayoffLaw
  simp only [Dist.mix_apply, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  simp [Dist.pure_apply]

noncomputable def maxPayoff [Nonempty O] (v : O → ℝ) : ℝ := -minPayoff (fun o => -v o)

noncomputable def maximumOutcome [Nonempty O] (v : O → ℝ) : O := minimumOutcome (fun o => -v o)

theorem maxPayoff_eq [Nonempty O] (v : O → ℝ) : maxPayoff v = v (maximumOutcome v) := by
  simp [maxPayoff,minPayoff,maximumOutcome]

theorem payoff_le_max [Nonempty O] (v : O → ℝ) (o : O) : v o ≤ maxPayoff v := by
  have h := minPayoff_le (fun o => -v o) o
  unfold maxPayoff
  linarith

theorem minPayoff_le_max [Nonempty O] (v : O → ℝ) : minPayoff v ≤ maxPayoff v :=
  payoff_le_max v (minimumOutcome v)

theorem minPayoff_lt_max [Nonempty O] (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) :
    minPayoff v < maxPayoff v := by
  by_contra hn
  have he : maxPayoff v = minPayoff v := le_antisymm (le_of_not_gt hn) (minPayoff_le_max v)
  apply hv
  refine ⟨minPayoff v,fun o => ?_⟩
  exact le_antisymm (by simpa [he] using payoff_le_max v o) (minPayoff_le v o)

theorem exists_payoffLotteryExpected [Nonempty O] (v : O → ℝ) {w : ℝ}
    (hlo : minPayoff v ≤ w) (hhi : w ≤ maxPayoff v) :
    ∃ ell : Dist O, payoffLotteryExpected v ell = w := by
  by_cases he : minPayoff v = maxPayoff v
  · refine ⟨Dist.pure (minimumOutcome v), ?_⟩
    have hw : w = minPayoff v := le_antisymm (by simpa [he] using hhi) hlo
    simp [payoffLotteryExpected,Dist.pure_apply,hw,minPayoff]
  have hd : 0 < maxPayoff v-minPayoff v := sub_pos.mpr (lt_of_le_of_ne (minPayoff_le_max v) he)
  let b := (w-minPayoff v)/(maxPayoff v-minPayoff v)
  have hb0 : 0 ≤ b := div_nonneg (sub_nonneg.mpr hlo) hd.le
  have hb1 : b ≤ 1 := (div_le_one hd).mpr (by linarith)
  refine ⟨binaryPayoffLaw (maximumOutcome v) (minimumOutcome v) b hb0 hb1, ?_⟩
  rw [expected_binaryPayoffLaw, ← maxPayoff_eq v]
  change b * maxPayoff v + (1-b)*minPayoff v = w
  dsimp [b]
  field_simp
  ring

/-- Replace the terminal payoff by an independent lottery, preserving the
entire old visible consequence as an explicit record. -/
noncomputable def attachPayoffLottery [Nonempty O] (E : FiniteExperiment O) (ell : Dist O) :
    FiniteExperiment O :=
  .ofChannel E.prior (commonPayoffCompound (fun _ : O × E.Rec => PUnit.{u+1}) E.channel
    (fun _ => payoffLotteryChannel ell))

theorem attachPayoffLottery_material [Nonempty O] (v : O → ℝ)
    (E : FiniteExperiment O) (ell : Dist O) :
    materialIndex v (attachPayoffLottery E ell) = payoffLotteryExpected v ell := by
  unfold materialIndex attachPayoffLottery
  dsimp only [FiniteExperiment.ofChannel]
  rw [expectedPayoffUtility_commonCompound]
  simp_rw [expectedPayoffUtility_payoffLotteryChannel]
  rw [← Finset.sum_mul,(Channel.outcomeMarginal E.channel E.prior).sum_eq_one,one_mul]

theorem attachPayoffLottery_information [Nonempty O]
    (E : FiniteExperiment O) (ell : Dist O) :
    informationIndex (attachPayoffLottery E ell) = informationIndex E := by
  unfold informationIndex attachPayoffLottery
  dsimp only [FiniteExperiment.ofChannel]
  rw [mutualInfo_commonCompound]
  have hz (q : Dist E.Act) : mutualInfo q (payoffLotteryChannel (A := E.Act) ell) = 0 :=
    mutualInfo_constant _ _
  simp only [hz,mul_zero,Finset.sum_const_zero,add_zero]

theorem exists_informationIndex [Nonempty O] {t : ℝ} (ht : 0 ≤ t) :
    ∃ E : FiniteExperiment O, informationIndex E = t := by
  let o : O := Classical.choice ‹Nonempty O›
  obtain ⟨E,hE⟩ := exists_valueIndex_eq_add (fun _ : O => 0) (by norm_num : (0:ℝ)<1) o ht
  refine ⟨E,?_⟩
  simpa [valueIndex,traceTemperedValue,Independence.expectedPayoffUtility_zero,informationIndex] using hE

theorem materialIndex_bounds [Nonempty O] (v : O → ℝ) (E : FiniteExperiment O) :
    minPayoff v ≤ materialIndex v E ∧ materialIndex v E ≤ maxPayoff v := by
  constructor
  · simpa [traceTemperedValue,materialIndex] using
      lower_bound_value v (by norm_num : (0:ℝ)≤0) (minPayoff_le v) E.prior E.channel
  · unfold materialIndex
    rw [expectedPayoffUtility_eq_marginal]
    calc
      _ ≤ ∑ z, (Channel.outcomeMarginal E.channel E.prior) z * maxPayoff v :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (payoff_le_max v z.1)
          ((Channel.outcomeMarginal E.channel E.prior).nonneg z)
      _ = maxPayoff v := by
        rw [← Finset.sum_mul,(Channel.outcomeMarginal E.channel E.prior).sum_eq_one,one_mul]

theorem informationIndex_nonneg (E : FiniteExperiment O) : 0 ≤ informationIndex E :=
  sub_nonneg.mpr (sum_weighted_entropy_le_entropy_actionPushforward _ _)

/-- The full information/material strip is attained by actual finite experiments. -/
theorem attainable_information_material [Nonempty O] (v : O → ℝ) (t w : ℝ) :
    (∃ E : FiniteExperiment O, informationIndex E = t ∧ materialIndex v E = w) ↔
      0 ≤ t ∧ minPayoff v ≤ w ∧ w ≤ maxPayoff v := by
  constructor
  · rintro ⟨E,rfl,rfl⟩
    exact ⟨informationIndex_nonneg E,materialIndex_bounds v E⟩
  · rintro ⟨ht,hlo,hhi⟩
    obtain ⟨E,hE⟩ := exists_informationIndex (O := O) ht
    obtain ⟨ell,hell⟩ := exists_payoffLotteryExpected v hlo hhi
    exact ⟨attachPayoffLottery E ell,by rw [attachPayoffLottery_information,hE],
      by rw [attachPayoffLottery_material,hell]⟩

theorem indifference_information_price (v : O → ℝ) (lambda : ℝ)
    (E D : FiniteExperiment O) (hV : valueIndex v lambda E = valueIndex v lambda D)
    (hI : informationIndex E ≠ informationIndex D) :
    (materialIndex v D-materialIndex v E)/(informationIndex E-informationIndex D) = lambda := by
  apply (div_eq_iff (sub_ne_zero.mpr hI)).mpr
  simp only [valueIndex_eq_material_information] at hV
  linarith

theorem indifference_lines (v : O → ℝ) (lambda c : ℝ) (E : FiniteExperiment O) :
    valueIndex v lambda E = c ↔ materialIndex v E = c-lambda*informationIndex E := by
  rw [valueIndex_eq_material_information]
  constructor <;> intro h <;> linarith

theorem exists_price_identifying_indifference [Nonempty O]
    (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) {lambda : ℝ} (hl : 0 < lambda) :
    ∃ E D : FiniteExperiment O,
      valueIndex v lambda E = valueIndex v lambda D ∧ informationIndex E ≠ informationIndex D := by
  let t := (maxPayoff v-minPayoff v)/(2*lambda)
  have ht : 0 < t := div_pos (sub_pos.mpr (minPayoff_lt_max v hv)) (by positivity)
  have hmul : lambda*t = (maxPayoff v-minPayoff v)/2 := by
    dsimp [t]
    field_simp
  have hwlo : minPayoff v ≤ maxPayoff v-lambda*t := by
    rw [hmul]
    linarith [minPayoff_le_max v]
  have hwhi : maxPayoff v-lambda*t ≤ maxPayoff v := by nlinarith
  obtain ⟨E,hEI,hEU⟩ := (attainable_information_material v t (maxPayoff v-lambda*t)).mpr
    ⟨ht.le,hwlo,hwhi⟩
  obtain ⟨D,hDI,hDU⟩ := (attainable_information_material v 0 (maxPayoff v)).mpr
    ⟨le_rfl,minPayoff_le_max v,le_rfl⟩
  refine ⟨E,D,?_,?_⟩
  · rw [valueIndex_eq_material_information,valueIndex_eq_material_information,hEI,hEU,hDI,hDU]
    ring
  · rw [hEI,hDI]
    exact ne_of_gt ht

theorem unique_information_price [Nonempty O]
    (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) {lambda : ℝ} (hl : 0 < lambda)
    (price : ℝ)
    (hprice : ∀ E D : FiniteExperiment O,
      valueIndex v lambda E = valueIndex v lambda D → informationIndex E ≠ informationIndex D →
        (materialIndex v D-materialIndex v E)/(informationIndex E-informationIndex D) = price) :
    price = lambda := by
  obtain ⟨E,D,hV,hI⟩ := exists_price_identifying_indifference v hv hl
  exact (hprice E D hV hI).symm.trans (indifference_information_price v lambda E D hV hI)

end TraceableAgency.Section4
