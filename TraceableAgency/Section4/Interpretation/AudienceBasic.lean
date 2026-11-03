import TraceableAgency.Section4.OptimizationBasic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-! Finite entropy rewards evaluated under the actual lottery, while the
observer updates a possibly different prior using the same channel. -/
namespace TraceableAgency.Section4.Interpretation

open TraceableAgency Section4

universe u
variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def audienceReward {Z : Type u} [Fintype Z]
    (q r : Dist A) (lambda : ℝ) (K : Channel A Z) : ℝ :=
  lambda * (entropy r - ∑ z, Channel.outcomeMarginal K q z *
    entropy (Channel.posterior K r z))

omit [DecidableEq A] [Nonempty A] in
theorem observer_reaches_actual_output {Z : Type u} [Fintype Z]
    (q r : Dist A) (hqr : SupportIncluded q r) (K : Channel A Z) (z : Z)
    (hz : 0 < Channel.outcomeMarginal K q z) :
    0 < Channel.outcomeMarginal K r z := by
  have hex : ∃ a, 0 < q a * K a z := by
    by_contra! hh
    have hs : Channel.outcomeMarginal K q z ≤ 0 := Finset.sum_nonpos fun a _ => hh a
    linarith
  obtain ⟨a, ha⟩ := hex
  have hqa : 0 < q a := by nlinarith [(K a).nonneg z]
  have hka : 0 < K a z := by nlinarith [q.nonneg a]
  exact lt_of_lt_of_le (mul_pos (hqr a hqa) hka)
    (Finset.single_le_sum (fun b _ => mul_nonneg (r.nonneg b) ((K b).nonneg z))
      (Finset.mem_univ a))

theorem audienceReward_correct {Z : Type u} [Fintype Z] [DecidableEq Z]
    (q : Dist A) (lambda : ℝ) (K : Channel A Z) :
    audienceReward q q lambda K = lambda * mutualInfo q K := by
  rw [mutualInfo_entropyReduction]
  rfl

private theorem entropy_posterior_id (r : Dist A) (a : A) :
    entropy (Channel.posterior Channel.idChannel r a) = 0 := by
  by_cases ha : 0 < r a
  · have heq : Channel.posterior Channel.idChannel r a = Dist.pure a := by
      apply Dist.ext
      intro b
      simp only [Channel.posterior, outcomeMarginal_idChannel', ha, dite_true]
      by_cases hb : b = a
      · subst b
        simp [Channel.idChannel, ne_of_gt ha]
      · simp [Channel.idChannel, hb, Ne.symm hb]
    rw [heq, entropy_pure']
  · simp [Channel.posterior, outcomeMarginal_idChannel', ha, entropy_pure']

theorem audienceReward_fullReveal (q r : Dist A) (lambda : ℝ) :
    audienceReward q r lambda Channel.idChannel = lambda * entropy r := by
  simp [audienceReward, entropy_posterior_id]

omit [Nonempty A] in
/-- Two atoms suffice for the audience-identification test. -/
theorem entropy_of_two_atoms (p : Dist A) (a b : A) (hab : a ≠ b)
    (hz : ∀ i, i ≠ a → i ≠ b → p i = 0) :
    entropy p = Real.binEntropy (p a) := by
  have hs (f : ℝ → ℝ) (hf : f 0 = 0) : ∑ i, f (p i) = f (p a) + f (p b) := by
    have heq (i : A) : f (p i) = (if i = a then f (p a) else 0) +
        (if i = b then f (p b) else 0) := by
      by_cases hia : i = a
      · subst i; simp [hab]
      · by_cases hib : i = b
        · subst i; simp [Ne.symm hab]
        · simp [hia, hib, hz i hia hib, hf]
    calc
      (∑ i, f (p i)) = ∑ i, ((if i = a then f (p a) else 0) +
          (if i = b then f (p b) else 0)) := Finset.sum_congr rfl (fun i _ => heq i)
      _ = f (p a) + f (p b) := by simp [Finset.sum_add_distrib]
  have hpab : p a + p b = 1 := by
    simpa using (hs id rfl).symm.trans p.sum_eq_one
  rw [entropy, hs entropyTerm entropyTerm_zero,
    entropyTerm_eq_negMulLog (p.nonneg a), entropyTerm_eq_negMulLog (p.nonneg b),
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  congr 1
  congr 1
  linarith

/-- Action b always shares the exceptional record; action a shares it with
probability x. Every other observed record identifies the action exactly. -/
noncomputable def audienceTestChannel (a b : A) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Channel A (Option A) := fun i =>
  if i = a then Dist.mix x hx0 hx1 (Dist.pure none) (Dist.pure (some i))
  else if i = b then Dist.pure none else Dist.pure (some i)

omit [Nonempty A] in
theorem audienceTest_none (a b i : A) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    audienceTestChannel a b x hx0 hx1 i none =
      if i = a then x else if i = b then 1 else 0 := by
  unfold audienceTestChannel
  split_ifs <;> simp_all [Dist.mix_apply]

omit [Nonempty A] in
theorem audienceTest_some (a b i j : A) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    audienceTestChannel a b x hx0 hx1 i (some j) =
      if i = j then (if i = a then 1-x else if i = b then 0 else 1) else 0 := by
  unfold audienceTestChannel
  split_ifs <;> simp_all [Dist.mix_apply, eq_comm]

omit [Nonempty A] in
theorem audienceTest_marginal_none (p : Dist A) (a b : A) (hab : a ≠ b)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Channel.outcomeMarginal (audienceTestChannel a b x hx0 hx1) p none = p a*x+p b := by
  simp only [Channel.outcomeMarginal_apply, audienceTest_none]
  have heq (i : A) : p i * (if i = a then x else if i = b then 1 else 0) =
      (if i = a then p a*x else 0) + (if i = b then p b else 0) := by
    by_cases hia : i = a
    · subst i; simp [hab]
    · by_cases hib : i = b
      · subst i; simp [Ne.symm hab]
      · simp [hia, hib]
  simp_rw [heq]
  simp [Finset.sum_add_distrib]

omit [Nonempty A] in
theorem audienceTest_marginal_some (p : Dist A) (a b j : A)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Channel.outcomeMarginal (audienceTestChannel a b x hx0 hx1) p (some j) =
      p j * audienceTestChannel a b x hx0 hx1 j (some j) := by
  rw [Channel.outcomeMarginal_apply, Finset.sum_eq_single j]
  · intro i _ hij
    rw [audienceTest_some, if_neg hij, mul_zero]
  · simp

theorem audienceTest_posterior_some_entropy (p : Dist A) (a b j : A)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    entropy (Channel.posterior (audienceTestChannel a b x hx0 hx1) p (some j)) = 0 := by
  let K := audienceTestChannel a b x hx0 hx1
  by_cases hm : 0 < Channel.outcomeMarginal K p (some j)
  · have heq : Channel.posterior K p (some j) = Dist.pure j := by
      apply Dist.ext
      intro i
      simp only [Channel.posterior, hm, dite_true, Dist.pure_apply]
      by_cases hij : i = j
      · subst i
        rw [if_pos rfl, audienceTest_marginal_some]
        exact div_self (ne_of_gt (audienceTest_marginal_some p a b j x hx0 hx1 ▸ hm))
      · rw [if_neg hij]
        change p i * audienceTestChannel a b x hx0 hx1 i (some j) / _ = 0
        rw [audienceTest_some, if_neg hij, mul_zero, zero_div]
    rw [heq, entropy_pure']
  · change entropy (Channel.posterior K p (some j)) = 0
    rw [Channel.posterior, dif_neg hm, entropy_pure']

theorem audienceTest_posterior_none_entropy (p : Dist A) (a b : A) (hab : a ≠ b)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hpb : 0 < p b) :
    entropy (Channel.posterior (audienceTestChannel a b x hx0 hx1) p none) =
      Real.binEntropy (p a*x/(p a*x+p b)) := by
  have hm : 0 < Channel.outcomeMarginal (audienceTestChannel a b x hx0 hx1) p none := by
    rw [audienceTest_marginal_none p a b hab]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (p.nonneg a) hx0) hpb
  rw [entropy_of_two_atoms _ a b hab]
  · congr 1
    simp only [Channel.posterior, dif_pos hm]
    rw [audienceTest_none, if_pos rfl, audienceTest_marginal_none p a b hab]
  · intro i hia hib
    simp only [Channel.posterior, dif_pos hm]
    rw [audienceTest_none, if_neg hia, if_neg hib, mul_zero, zero_div]

theorem audienceReward_test (q r : Dist A) (lambda : ℝ) (a b : A) (hab : a ≠ b)
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hrb : 0 < r b) :
    audienceReward q r lambda (audienceTestChannel a b x hx0 hx1) =
      lambda * (entropy r - (q a*x+q b)*Real.binEntropy (r a*x/(r a*x+r b))) := by
  simp only [audienceReward, Fintype.sum_option, audienceTest_posterior_some_entropy,
    mul_zero, Finset.sum_const_zero, add_zero,
    audienceTest_marginal_none q a b hab,
    audienceTest_posterior_none_entropy r a b hab x hx0 hx1 hrb]

end TraceableAgency.Section4.Interpretation
