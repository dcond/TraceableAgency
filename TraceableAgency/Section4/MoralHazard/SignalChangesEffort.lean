import TraceableAgency.Section4.MoralHazard.SignalCompensation
import TraceableAgency.Section4.MoralHazard.Incentives
import TraceableAgency.Section4.OptimizationLogit

/-! An actual signal extension can change the chosen effort lottery, even
though the signal leaves wages and the production marginal unchanged. -/
namespace TraceableAgency.Section4.BernoulliTechnology
open TraceableAgency Set
variable (t : BernoulliTechnology)

/-- Production output together with a truthful action record. -/
noncomputable def fullActionRecord : Channel Bool (Bool × Bool) :=
  fun a => prodDist (t.channel a) (Dist.pure a)

 theorem fullActionRecord_production : productionMarginal t.fullActionRecord = t.channel := by
  funext a
  apply Dist.ext
  intro x
  rw [productionMarginal_apply]
  cases a <;> simp [fullActionRecord,prodDist_apply_pair,Dist.pure_apply]

 theorem fullActionRecord_disjoint : DisjointRows t.fullActionRecord := by
  intro a b hab z hz
  have hza : z.2 = a := by
    by_contra hn
    simp [fullActionRecord,prodDist_apply,Dist.pure_apply,hn] at hz
  simp [fullActionRecord,prodDist_apply,Dist.pure_apply,hza,Ne.symm hab]

 theorem fullActionRecord_optimal_iff (bonus cost lambda : ℝ) (hl : 0 < lambda)
    (q : Dist Bool) :
    IsOptimal (t.effortRewards bonus cost) lambda t.fullActionRecord q ↔
      q = logitDist (t.effortRewards bonus cost) lambda :=
  disjoint_optimal_iff_logit _ hl _ t.fullActionRecord_disjoint q

 theorem flat_fullActionRecord_probability (cost lambda : ℝ) :
    logitDist (t.effortRewards 0 cost) lambda true =
      Real.exp (-cost/lambda)/(1+Real.exp (-cost/lambda)) := by
  simp [logitDist,logitNormalizer,Fintype.sum_bool,effortRewards]
  ring

 theorem fullActionRecord_logit_interior (bonus cost lambda : ℝ) :
    logitDist (t.effortRewards bonus cost) lambda true ∈ Ioo (0 : ℝ) 1 := by
  have h0 := logitDist_pos (t.effortRewards bonus cost) lambda false
  have h1 := logitDist_pos (t.effortRewards bonus cost) lambda true
  have hs := (logitDist (t.effortRewards bonus cost) lambda).sum_eq_one
  rw [Fintype.sum_bool] at hs
  exact ⟨h1,by linarith⟩

/-- With a sufficiently high effort cost, a flat wage induces uniquely zero
effort from production alone. Revealing the action instead induces a unique,
strictly interior logit lottery, for the same rewards and production law. -/
 theorem flat_signal_changes_effort (cost lambda : ℝ) (hl : 0 < lambda)
    (hc : lambda*bernoulliKL t.high t.low ≤ cost) :
    productionMarginal t.fullActionRecord = t.channel ∧
    (∀ q, IsOptimal (t.effortRewards 0 cost) lambda t.channel q ↔ q = Dist.pure false) ∧
    (∀ q, IsOptimal (t.effortRewards 0 cost) lambda t.fullActionRecord q ↔
      q = logitDist (t.effortRewards 0 cost) lambda) ∧
    logitDist (t.effortRewards 0 cost) lambda true ∈ Ioo (0 : ℝ) 1 := by
  refine ⟨t.fullActionRecord_production,?_,t.fullActionRecord_optimal_iff 0 cost lambda hl,
    t.fullActionRecord_logit_interior 0 cost lambda⟩
  have hzero : IsOptimal (t.effortRewards 0 cost) lambda t.channel (Dist.pure false) := by
    apply (t.pure_low_optimal_iff 0 cost lambda hl).mpr
    nlinarith
  intro q
  constructor
  · intro hq
    exact optimal_unique_of_output_injective (t.effortRewards 0 cost) hl t.channel
      t.output_injective q (Dist.pure false) hq hzero
  · intro he
    simpa [he] using hzero

end TraceableAgency.Section4.BernoulliTechnology
