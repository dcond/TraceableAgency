import TraceableAgency.Section4.MoralHazard.Optimization
import TraceableAgency.Section4.SignalValue

/-! Extra-signal participation compensation, instantiated with the actual
conditional-information gain of the Bernoulli effort model. -/
namespace TraceableAgency.Section4
open TraceableAgency Set

 theorem mutualInfo_bernoulli {Z : Type} [Fintype Z]
    (K : Channel Bool Z) (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    mutualInfo (bernoulli q h0 h1) K =
      mixEntropy (K false) (K true) q-(1-q)*entropy (K false)-q*entropy (K true) := by
  have hm : Channel.outcomeMarginal K (bernoulli q h0 h1) =
      Dist.mix q h0 h1 (K true) (K false) := by
    ext z
    simp [Channel.outcomeMarginal_apply,Fintype.sum_bool,bernoulli,Dist.mix_apply]
  unfold mutualInfo
  rw [hm,← mixEntropy_eq_distMix (K false) (K true) h0 h1]
  simp only [Fintype.sum_bool,bernoulli_true,bernoulli_false]
  ring

namespace BernoulliTechnology
variable (t : BernoulliTechnology)
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

/-- A continuous real-coordinate formula for the additional information value.
On the feasible interval it equals lambda times I(A;S | X). -/
noncomputable def signalGain (lambda : ℝ) (L : Channel Bool (Bool × S)) (q : ℝ) : ℝ :=
  lambda*(mixEntropy (L false) (L true) q-(1-q)*entropy (L false)-q*entropy (L true)-
    t.information q)

 theorem continuous_information : Continuous t.information := by
  unfold information mean
  fun_prop

 theorem continuous_value (w0 bonus cost lambda : ℝ) :
    Continuous (t.value w0 bonus cost lambda) := by
  unfold value mean
  exact (continuous_const.add ((continuous_const.add (continuous_id.mul continuous_const)).mul
    continuous_const)).sub (continuous_id.mul continuous_const) |>.add
      (continuous_const.mul t.continuous_information)

 theorem continuous_signalGain (lambda : ℝ) (L : Channel Bool (Bool × S)) :
    Continuous (t.signalGain lambda L) := by
  unfold signalGain
  exact continuous_const.mul ((((continuous_mixEntropy (L false) (L true)).sub
    ((continuous_const.sub continuous_id).mul continuous_const)).sub
      (continuous_id.mul continuous_const)).sub t.continuous_information)

 theorem signalGain_eq_conditional (lambda : ℝ) (L : Channel Bool (Bool × S))
    (hL : productionMarginal L = t.channel) (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    t.signalGain lambda L q = lambda*signalInformation (bernoulli q h0 h1) L := by
  have hh := signal_information_chain (bernoulli q h0 h1) L
  rw [hL,t.mutualInfo_eq,mutualInfo_bernoulli] at hh
  unfold signalGain
  rw [hh]
  ring

 theorem signal_value_eq (bonus cost lambda : ℝ) (L : Channel Bool (Bool × S))
    (hL : productionMarginal L = t.channel) (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    rowRewardValue (t.effortRewards bonus cost) lambda (bernoulli q h0 h1) L =
      t.value 0 bonus cost lambda q+t.signalGain lambda L q := by
  have hh := signal_value_gain (t.effortRewards bonus cost) lambda (bernoulli q h0 h1) L
  rw [hL,t.rowRewardValue_eq,← t.signalGain_eq_conditional lambda L hL q h0 h1] at hh
  linarith

 theorem signalGain_nonneg {lambda : ℝ} (hl : 0 ≤ lambda)
    (L : Channel Bool (Bool × S)) (hL : productionMarginal L = t.channel)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) : 0 ≤ t.signalGain lambda L q := by
  rw [t.signalGain_eq_conditional lambda L hL q hq.1 hq.2]
  exact signal_gain_nonneg hl _ L

/-- Both effort optima and the largest conditional-information gain exist;
the exact compensating reduction in base pay lies between the gain at the
old optimum and the largest gain. No continuity or gain identity is assumed. -/
 theorem exists_signal_compensation_bounds (bonus cost lambda : ℝ)
    (L : Channel Bool (Bool × S)) (hL : productionMarginal L = t.channel) :
    ∃ oldPlan newPlan gainPlan,
      IsIntervalOptimal (t.value 0 bonus cost lambda) oldPlan ∧
      IsIntervalOptimal (fun q => t.value 0 bonus cost lambda q+t.signalGain lambda L q) newPlan ∧
      IsIntervalOptimal (t.signalGain lambda L) gainPlan ∧
      (∀ h0 h1, t.signalGain lambda L oldPlan =
        lambda*signalInformation (bernoulli oldPlan h0 h1) L) ∧
      t.signalGain lambda L oldPlan ≤
        compensation (t.value 0 bonus cost lambda) (t.signalGain lambda L) oldPlan newPlan ∧
      compensation (t.value 0 bonus cost lambda) (t.signalGain lambda L) oldPlan newPlan ≤
        t.signalGain lambda L gainPlan := by
  obtain ⟨q0,q1,qG,h0,h1,hG,hlo,hhi⟩ := exists_compensation_bounds
    (t.value 0 bonus cost lambda) (t.signalGain lambda L)
    (t.continuous_value 0 bonus cost lambda).continuousOn
    (t.continuous_signalGain lambda L).continuousOn
  exact ⟨q0,q1,qG,h0,h1,hG,fun hq0 hq1 => t.signalGain_eq_conditional lambda L hL q0 hq0 hq1,hlo,hhi⟩

 theorem signal_compensation_zero (bonus cost : ℝ) (L : Channel Bool (Bool × S))
    {oldPlan newPlan : ℝ}
    (hold : IsIntervalOptimal (t.value 0 bonus cost 0) oldPlan)
    (hnew : IsIntervalOptimal (fun q => t.value 0 bonus cost 0 q+t.signalGain 0 L q) newPlan) :
    compensation (t.value 0 bonus cost 0) (t.signalGain 0 L) oldPlan newPlan = 0 := by
  apply compensation_zero_of_zero_gain _ _ _ hold hnew
  intro q _
  simp [signalGain]

end BernoulliTechnology
end TraceableAgency.Section4
