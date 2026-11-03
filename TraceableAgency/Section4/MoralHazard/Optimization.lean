import TraceableAgency.Section4.MoralHazard.Teams
import TraceableAgency.Section4.MoralHazard.Compensation
import TraceableAgency.Section4.OptimizationKKT
import TraceableAgency.Section4.OptimizationGeometry

/-! Exact incentive thresholds and the unique optimal effort lottery. -/
namespace TraceableAgency.Section4
open TraceableAgency Set

 theorem dist_bool_eq_bernoulli (q : Dist Bool) :
    q = bernoulli (q true) (q.nonneg true) (q.prob_le_one true) := by
  ext b
  have hs := q.sum_eq_one
  simp only [Fintype.sum_bool] at hs
  cases b <;> simp [bernoulli] <;> linarith

namespace BernoulliTechnology
variable (t : BernoulliTechnology)
noncomputable def effortRewards (bonus cost : ℝ) (a : Bool) : ℝ :=
  if a then t.high*bonus-cost else t.low*bonus

 theorem rowRewardValue_eq (bonus cost lambda q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    rowRewardValue (t.effortRewards bonus cost) lambda (bernoulli q h0 h1) t.channel =
      t.value 0 bonus cost lambda q := by
  rw [rowRewardValue, t.mutualInfo_eq]
  simp [Fintype.sum_bool, bernoulli, effortRewards, value, mean, gap]
  ring

 theorem value_add_base (w0 bonus cost lambda q : ℝ) :
    t.value w0 bonus cost lambda q = w0+t.value 0 bonus cost lambda q := by
  dsimp [value]
  ring

 theorem intervalOptimal_iff (w0 bonus cost lambda q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    IsIntervalOptimal (t.value w0 bonus cost lambda) q ↔
      IsOptimal (t.effortRewards bonus cost) lambda t.channel (bernoulli q h0 h1) := by
  have he : t.value w0 bonus cost lambda = fun x => w0+t.value 0 bonus cost lambda x :=
    funext (t.value_add_base w0 bonus cost lambda)
  rw [he, intervalOptimal_add_base_iff]
  constructor
  · intro ho p
    have hh := ho.2 (p true) ⟨p.nonneg true,p.prob_le_one true⟩
    rw [← t.rowRewardValue_eq bonus cost lambda (p true) (p.nonneg true) (p.prob_le_one true),
      ← t.rowRewardValue_eq bonus cost lambda q h0 h1] at hh
    simpa only [← dist_bool_eq_bernoulli p] using hh
  · intro ho
    refine ⟨⟨h0,h1⟩, fun x hx => ?_⟩
    have hh := ho (bernoulli x hx.1 hx.2)
    simpa only [t.rowRewardValue_eq] using hh

 theorem channel_positive (a z : Bool) : 0 < t.channel a z := by
  cases a <;> cases z <;> simp [channel,bernoulli] <;>
    linarith [t.low_pos,t.productive,t.high_lt_one]

 theorem covers_channel (a : Bool) : CoversRows t.channel (t.channel a) :=
  fun _ z _ => t.channel_positive a z

 theorem pure_high_optimal_iff (bonus cost lambda : ℝ) (hl : 0 < lambda) :
    IsOptimal (t.effortRewards bonus cost) lambda t.channel (Dist.pure true) ↔
      (cost+lambda*bernoulliKL t.low t.high)/t.gap ≤ bonus := by
  rw [pure_optimal_iff (t.effortRewards bonus cost) hl t.channel true]
  constructor
  · intro hh
    have hb := hh.2 false
    change t.low*bonus+lambda*finiteKL
      (bernoulli t.low t.low_pos.le (t.productive.trans t.high_lt_one).le) (bernoulli t.high (t.low_pos.trans t.productive).le t.high_lt_one.le) ≤ t.high*bonus-cost at hb
    rw [finiteKL_bernoulli] at hb
    apply (div_le_iff₀ t.gap_pos).mpr
    dsimp [gap]
    nlinarith
  · intro hb
    refine ⟨t.covers_channel true, ?_⟩
    intro a
    cases a
    · change t.low*bonus+lambda*finiteKL
        (bernoulli t.low t.low_pos.le (t.productive.trans t.high_lt_one).le) (bernoulli t.high (t.low_pos.trans t.productive).le t.high_lt_one.le) ≤ t.high*bonus-cost
      rw [finiteKL_bernoulli]
      have hh := (div_le_iff₀ t.gap_pos).mp hb
      dsimp [gap] at hh
      nlinarith
    · simp [finiteKL_self]

 theorem pure_low_optimal_iff (bonus cost lambda : ℝ) (hl : 0 < lambda) :
    IsOptimal (t.effortRewards bonus cost) lambda t.channel (Dist.pure false) ↔
      t.gap*bonus-cost+lambda*bernoulliKL t.high t.low ≤ 0 := by
  rw [pure_optimal_iff (t.effortRewards bonus cost) hl t.channel false]
  constructor
  · intro hh
    have hb := hh.2 true
    change t.high*bonus-cost+lambda*finiteKL
      (bernoulli t.high (t.low_pos.trans t.productive).le t.high_lt_one.le) (bernoulli t.low t.low_pos.le (t.productive.trans t.high_lt_one).le) ≤ t.low*bonus at hb
    rw [finiteKL_bernoulli] at hb
    dsimp [gap]
    nlinarith
  · intro hb
    refine ⟨t.covers_channel false, ?_⟩
    intro a
    cases a
    · simp [finiteKL_self]
    · change t.high*bonus-cost+lambda*finiteKL
        (bernoulli t.high (t.low_pos.trans t.productive).le t.high_lt_one.le) (bernoulli t.low t.low_pos.le (t.productive.trans t.high_lt_one).le) ≤ t.low*bonus
      rw [finiteKL_bernoulli]
      dsimp [gap] at hb
      nlinarith

 theorem interval_high_optimal_iff (w0 bonus cost lambda : ℝ) (hl : 0 < lambda) :
    IsIntervalOptimal (t.value w0 bonus cost lambda) 1 ↔
      (cost+lambda*bernoulliKL t.low t.high)/t.gap ≤ bonus := by
  rw [t.intervalOptimal_iff w0 bonus cost lambda 1 (by norm_num) (by norm_num)]
  have hh : bernoulli 1 (by norm_num) (by norm_num) = Dist.pure true := by
    ext b
    cases b <;> simp [bernoulli,Dist.pure_apply]
  rw [hh,t.pure_high_optimal_iff bonus cost lambda hl]

 theorem interval_low_optimal_iff (w0 bonus cost lambda : ℝ) (hl : 0 < lambda) :
    IsIntervalOptimal (t.value w0 bonus cost lambda) 0 ↔
      t.gap*bonus-cost+lambda*bernoulliKL t.high t.low ≤ 0 := by
  rw [t.intervalOptimal_iff w0 bonus cost lambda 0 (by norm_num) (by norm_num)]
  have hh : bernoulli 0 (by norm_num) (by norm_num) = Dist.pure false := by
    ext b
    cases b <;> simp [bernoulli,Dist.pure_apply]
  rw [hh,t.pure_low_optimal_iff bonus cost lambda hl]

 theorem output_injective : Function.Injective (Channel.outcomeMarginal t.channel) := by
  intro q p he
  have ht := congrArg (fun s : Dist Bool => s true) he
  have hq := dist_bool_eq_bernoulli q
  have hp := dist_bool_eq_bernoulli p
  rw [hq,hp,t.outcomeMarginal_eq,t.outcomeMarginal_eq] at ht
  simp only [bernoulli_true,mean] at ht
  have hsame : q true = p true := by nlinarith [t.gap_pos]
  apply Dist.ext
  intro b
  cases b
  · have hs0 := q.sum_eq_one
    have hs1 := p.sum_eq_one
    simp only [Fintype.sum_bool] at hs0 hs1
    linarith
  · exact hsame

 theorem exists_unique_intervalOptimal (w0 bonus cost lambda : ℝ) (hl : 0 < lambda) :
    ∃! q, IsIntervalOptimal (t.value w0 bonus cost lambda) q := by
  obtain ⟨q,hq⟩ := exists_optimal (t.effortRewards bonus cost) lambda t.channel
  refine ⟨q true, ?_, ?_⟩
  · apply (t.intervalOptimal_iff w0 bonus cost lambda (q true) (q.nonneg true) (q.prob_le_one true)).mpr
    simpa only [← dist_bool_eq_bernoulli q] using hq
  · intro p hp
    have hp' := (t.intervalOptimal_iff w0 bonus cost lambda p hp.1.1 hp.1.2).mp hp
    have he := optimal_unique_of_output_injective (t.effortRewards bonus cost) hl t.channel
      t.output_injective (bernoulli p hp.1.1 hp.1.2) q hp' hq
    exact congrArg (fun s : Dist Bool => s true) he

 theorem flat_wage_interior_iff (w0 cost lambda : ℝ) (hc : 0 < cost) (hl : 0 < lambda) :
    (∃ q ∈ Ioo (0 : ℝ) 1, IsIntervalOptimal (t.value w0 0 cost lambda) q) ↔
      cost < lambda*bernoulliKL t.high t.low := by
  have hnot1 : ¬ IsIntervalOptimal (t.value w0 0 cost lambda) 1 := by
    rw [t.interval_high_optimal_iff w0 0 cost lambda hl]
    have hk := bernoulliKL_nonneg ⟨t.low_pos.le,(t.productive.trans t.high_lt_one).le⟩
      ⟨t.low_pos.trans t.productive,t.high_lt_one⟩
    have hh : 0 < (cost+lambda*bernoulliKL t.low t.high)/t.gap :=
      div_pos (by nlinarith) t.gap_pos
    exact not_le_of_gt hh
  have hzero := t.interval_low_optimal_iff w0 0 cost lambda hl
  constructor
  · rintro ⟨q,hq,ho⟩
    by_contra hn
    have hz : IsIntervalOptimal (t.value w0 0 cost lambda) 0 := hzero.mpr (by nlinarith)
    obtain ⟨p,hp,hu⟩ := t.exists_unique_intervalOptimal w0 0 cost lambda hl
    have he := (hu q ho).trans (hu 0 hz).symm
    exact (ne_of_gt hq.1) he
  · intro hh
    obtain ⟨q,hq,hu⟩ := t.exists_unique_intervalOptimal w0 0 cost lambda hl
    refine ⟨q, ?_, hq⟩
    have hn0 : q ≠ 0 := by
      intro he
      subst q
      have hz := hzero.mp hq
      nlinarith
    have hn1 : q ≠ 1 := by intro he; subst q; exact hnot1 hq
    exact ⟨lt_of_le_of_ne hq.1.1 (Ne.symm hn0),lt_of_le_of_ne hq.1.2 hn1⟩

end BernoulliTechnology
end TraceableAgency.Section4
