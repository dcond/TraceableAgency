import TraceableAgency.Section4.MoralHazard.Basic
import TraceableAgency.Info.Identities

/-! A candidate-plan-dependent independent cost lottery implements expected
cost without revealing effort. The observable coordinates are the production
output and a cost flag; wages are a deterministic function of the former. -/
namespace TraceableAgency.Section4
open TraceableAgency
universe u

noncomputable def appendIndependentOutput {A Z C : Type u}
    [Fintype A] [Fintype Z] [Fintype C]
    (K : Channel A Z) (d : Dist C) : Channel A (Z × C) := fun a => prodDist (K a) d

 theorem outcomeMarginal_appendIndependentOutput {A Z C : Type u}
    [Fintype A] [Fintype Z] [Fintype C]
    (q : Dist A) (K : Channel A Z) (d : Dist C) :
    Channel.outcomeMarginal (appendIndependentOutput K d) q =
      prodDist (Channel.outcomeMarginal K q) d := by
  ext z
  rcases z with ⟨z,c⟩
  simp only [Channel.outcomeMarginal_apply, appendIndependentOutput, prodDist_apply_pair]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

 theorem mutualInfo_appendIndependentOutput {A Z C : Type u}
    [Fintype A] [Fintype Z] [Fintype C]
    (q : Dist A) (K : Channel A Z) (d : Dist C) :
    mutualInfo q (appendIndependentOutput K d) = mutualInfo q K := by
  unfold mutualInfo
  rw [outcomeMarginal_appendIndependentOutput, entropy_prodDist]
  simp only [appendIndependentOutput, entropy_prodDist, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  ring

noncomputable def augmentedEffortChannel (t : BernoulliTechnology)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : Channel Bool (Bool × Bool) :=
  appendIndependentOutput t.channel (bernoulli q hq0 hq1)

noncomputable def wageNetCost (w0 bonus cost : ℝ) (z : Bool × Bool) : ℝ :=
  w0 + (if z.1 then bonus else 0) - (if z.2 then cost else 0)

 theorem independentCost_expected (q cost : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ z, bernoulli q hq0 hq1 z * (if z then cost else 0)) = q*cost := by
  simp [Fintype.sum_bool, bernoulli]

 theorem augmentedEffort_expectedUtility (t : BernoulliTechnology)
    (q w0 bonus cost : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ a, bernoulli q hq0 hq1 a *
      ∑ z, augmentedEffortChannel t q hq0 hq1 a z * wageNetCost w0 bonus cost z) =
      w0+t.mean q*bonus-q*cost := by
  simp [augmentedEffortChannel, appendIndependentOutput, prodDist_apply_pair,
    wageNetCost, Fintype.sum_prod_type, Fintype.sum_bool, bernoulli,
    BernoulliTechnology.channel, BernoulliTechnology.mean, BernoulliTechnology.gap]
  ring

 theorem augmentedEffort_information (t : BernoulliTechnology)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    mutualInfo (bernoulli q hq0 hq1) (augmentedEffortChannel t q hq0 hq1) =
      mutualInfo (bernoulli q hq0 hq1) t.channel :=
  mutualInfo_appendIndependentOutput _ _ _

 theorem augmentedEffort_value (t : BernoulliTechnology)
    (q w0 bonus cost lambda : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (∑ a, bernoulli q hq0 hq1 a *
      ∑ z, augmentedEffortChannel t q hq0 hq1 a z * wageNetCost w0 bonus cost z) +
      lambda*mutualInfo (bernoulli q hq0 hq1) (augmentedEffortChannel t q hq0 hq1) =
      t.value w0 bonus cost lambda q := by
  rw [augmentedEffort_expectedUtility, augmentedEffort_information, t.mutualInfo_eq]
  rfl

end TraceableAgency.Section4
