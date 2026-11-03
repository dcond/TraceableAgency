import TraceableAgency.Section4.Interpretation.AudienceBasic

/-! Proposition 34: matching entropy rewards for every finite channel identifies
exactly the actual prior. Identification uses partial merging of two actions;
it requires neither full support nor an entropy endpoint expansion. -/
namespace TraceableAgency.Section4.Interpretation

open TraceableAgency Section4 Set

universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

/-- The expectation always uses q; the posterior always uses the observer's r. -/
def AudienceMatchesAllChannels (q r : Dist A) (lambda : ℝ) : Prop :=
  ∀ {Z : Type u} [Fintype Z] [DecidableEq Z] [Nonempty Z] (K : Channel A Z),
    audienceReward q r lambda K = lambda * mutualInfo q K

private theorem equal_entropy_of_matches (q r : Dist A) {lambda : ℝ}
    (hlambda : lambda ≠ 0) (h : AudienceMatchesAllChannels q r lambda) :
    entropy r = entropy q := by
  have hh := h Channel.idChannel
  rw [audienceReward_fullReveal, mutualInfo_idChannel'] at hh
  exact mul_left_cancel₀ hlambda hh

private theorem equal_binary_entropy_of_matches (q r : Dist A) {lambda : ℝ}
    (hlambda : lambda ≠ 0) (h : AudienceMatchesAllChannels q r lambda)
    (a b : A) (hab : a ≠ b) (hqb : 0 < q b) (hrb : 0 < r b)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.binEntropy (r a*x/(r a*x+r b)) = Real.binEntropy (q a*x/(q a*x+q b)) := by
  have hh := h (audienceTestChannel a b x hx0 hx1)
  rw [← audienceReward_correct q lambda,
    audienceReward_test q r lambda a b hab x hx0 hx1 hrb,
    audienceReward_test q q lambda a b hab x hx0 hx1 hqb] at hh
  have he := mul_left_cancel₀ hlambda hh
  rw [equal_entropy_of_matches q r hlambda h] at he
  have hm : 0 < q a*x+q b := add_pos_of_nonneg_of_pos (mul_nonneg (q.nonneg a) hx0) hqb
  nlinarith

omit [DecidableEq A] [Nonempty A] in
private theorem ratio_small (p : Dist A) (a b : A) (hpb : 0 < p b)
    (x : ℝ) (hx0 : 0 ≤ x) (hxb : x ≤ p b) :
    p a*x/(p a*x+p b) ∈ Icc (0 : ℝ) 2⁻¹ := by
  have hm : 0 < p a*x+p b := add_pos_of_nonneg_of_pos (mul_nonneg (p.nonneg a) hx0) hpb
  constructor
  · exact div_nonneg (mul_nonneg (p.nonneg a) hx0) hm.le
  · apply (div_le_iff₀ hm).mpr
    have hpa := p.prob_le_one a
    norm_num
    nlinarith

private theorem cross_ratio_of_matches (q r : Dist A) (hqr : SupportIncluded q r)
    {lambda : ℝ} (hlambda : lambda ≠ 0) (h : AudienceMatchesAllChannels q r lambda)
    (b : A) (hqb : 0 < q b) (a : A) : q a * r b = r a * q b := by
  by_cases hab : a = b
  · subst a; ring
  have hrb := hqr b hqb
  let x := min (q b) (r b) / 2
  have hx : 0 < x := div_pos (lt_min hqb hrb) (by norm_num)
  have hxq : x ≤ q b := by
    have hm := min_le_left (q b) (r b)
    dsimp [x]
    linarith
  have hxr : x ≤ r b := by
    have hm := min_le_right (q b) (r b)
    dsimp [x]
    linarith
  have hx1 : x ≤ 1 := hxq.trans (q.prob_le_one b)
  have he := equal_binary_entropy_of_matches q r hlambda h a b hab hqb hrb x hx.le hx1
  have hrsmall := ratio_small r a b hrb x hx.le hxr
  have hqsmall := ratio_small q a b hqb x hx.le hxq
  have heq := Real.binEntropy_strictMonoOn.injOn hrsmall hqsmall he
  have hqm : 0 < q a*x+q b := add_pos_of_nonneg_of_pos (mul_nonneg (q.nonneg a) hx.le) hqb
  have hrm : 0 < r a*x+r b := add_pos_of_nonneg_of_pos (mul_nonneg (r.nonneg a) hx.le) hrb
  have hcross := (div_eq_div_iff (ne_of_gt hrm) (ne_of_gt hqm)).mp heq
  have hzero : (q a*r b-r a*q b)*x = 0 := by nlinarith [hcross]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right (ne_of_gt hx))

/-- Necessity includes pure actual priors and observer mass outside their support. -/
theorem audience_prior_eq_of_matches (q r : Dist A) (hqr : SupportIncluded q r)
    {lambda : ℝ} (hlambda : lambda ≠ 0) (h : AudienceMatchesAllChannels q r lambda) :
    r = q := by
  have hb : ∃ b, 0 < q b := by
    by_contra! hh
    have hs : (∑ b, q b) ≤ 0 := Finset.sum_nonpos fun b _ => hh b
    rw [q.sum_eq_one] at hs
    norm_num at hs
  obtain ⟨b, hqb⟩ := hb
  have heq (a : A) := cross_ratio_of_matches q r hqr hlambda h b hqb a
  have hsum : (∑ a, q a*r b) = ∑ a, r a*q b :=
    Finset.sum_congr rfl (fun a _ => heq a)
  simp only [← Finset.sum_mul, q.sum_eq_one, r.sum_eq_one, one_mul] at hsum
  apply Dist.ext
  intro a
  have ha := heq a
  rw [hsum] at ha
  exact (mul_right_cancel₀ (ne_of_gt hqb) ha).symm

/-- The exact finite-domain audience proposition, with no sign restriction on
lambda beyond nonzero and no full-support requirement on either prior. -/
theorem audience_reward_matches_iff (q r : Dist A) (hqr : SupportIncluded q r)
    {lambda : ℝ} (hlambda : lambda ≠ 0) :
    AudienceMatchesAllChannels q r lambda ↔ r = q := by
  constructor
  · exact audience_prior_eq_of_matches q r hqr hlambda
  · intro heq
    subst r
    intro Z _ _ _ K
    exact audienceReward_correct q lambda K

/-- Paper-facing form: the support premise is literal set inclusion, and the
expectation is displayed explicitly under the actual output marginal. -/
theorem audience_entropy_reduction_iff (q r : Dist A)
    (hqr : q.support ⊆ r.support) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    (∀ {Z : Type u} [Fintype Z] [DecidableEq Z] [Nonempty Z] (K : Channel A Z),
      lambda * (entropy r - ∑ z, Channel.outcomeMarginal K q z *
        entropy (Channel.posterior K r z)) = lambda * mutualInfo q K) ↔ r = q :=
  audience_reward_matches_iff q r hqr hlambda

end TraceableAgency.Section4.Interpretation
