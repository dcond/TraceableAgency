import TraceableAgency.Section4.Binary.Entropy
import TraceableAgency.Section4.OptimizationKKT
import TraceableAgency.Section4.OptimizationGeometry
import TraceableAgency.Section3.UniquenessMixture

/-! Binary choice for arbitrary finite output rows. The finite threshold is
stated together with support inclusion, so an infinite KL threshold is never
silently replaced by Lean's finite value of `log 0`. -/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1 Set
universe u
variable {Z : Type u} [Fintype Z]

noncomputable def binaryChannel (p r : Dist Z) : Channel RelevanceBit.{u} Z :=
  fun a => if a.down then r else p
noncomputable def binaryRewards (gap : ℝ) (a : RelevanceBit.{u}) : ℝ :=
  if a.down then -gap else 0
noncomputable def binaryInformation (p r : Dist Z) (x : ℝ) : ℝ :=
  mixEntropy p r x-(1-x)*entropy p-x*entropy r
noncomputable def binaryValue (p r : Dist Z) (gap lambda x : ℝ) : ℝ :=
  -x*gap+lambda*binaryInformation p r x
noncomputable def binaryGain (p r : Dist Z) (x : ℝ) : ℝ :=
  mixEntropySlope p r x+entropy p-entropy r

 theorem bit_dist_eq_publicCoin (q : Dist RelevanceBit.{u}) :
    q = Section3.publicCoin (q (ULift.up true)) (q.nonneg _) (q.prob_le_one _) := by
  ext b
  have hs := q.sum_eq_one
  rw [Section3.sum_relevanceBit] at hs
  rcases b with ⟨b⟩
  cases b <;> simp [Section3.publicCoin_true,Section3.publicCoin_false] <;> linarith

 theorem binary_outcomeMarginal (p r : Dist Z) (q : Dist RelevanceBit.{u}) (z : Z) :
    Channel.outcomeMarginal (binaryChannel p r) q z =
      mixMass p r (q (ULift.up true)) z := by
  have hs := q.sum_eq_one
  rw [Section3.sum_relevanceBit] at hs
  simp only [Channel.outcomeMarginal_apply,Section3.sum_relevanceBit,binaryChannel,
    ULift.down_up,Bool.true_eq,Bool.false_eq_true,if_true,if_false,mixMass]
  have hf : q (ULift.up false) = 1-q (ULift.up true) := by linarith
  rw [hf]
  ring

 theorem binary_value_eq (p r : Dist Z) (gap lambda x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    rowRewardValue (binaryRewards gap) lambda (Section3.publicCoin x h0 h1) (binaryChannel p r) =
      binaryValue p r gap lambda x := by
  have hm : Channel.outcomeMarginal (binaryChannel p r) (Section3.publicCoin x h0 h1) =
      Dist.mix x h0 h1 r p := by
    ext z
    rw [binary_outcomeMarginal]
    simp [mixMass,Dist.mix_apply]
    ring
  unfold rowRewardValue mutualInfo
  rw [hm,← mixEntropy_eq_distMix p r h0 h1]
  simp only [Section3.sum_relevanceBit,binaryRewards,binaryChannel,ULift.down_up,
    Bool.true_eq,Bool.false_eq_true,if_true,if_false,Section3.publicCoin_true,
    Section3.publicCoin_false,binaryValue,binaryInformation]
  ring

 theorem binary_output_injective (p r : Dist Z) (hne : p ≠ r) :
    Function.Injective (Channel.outcomeMarginal (binaryChannel p r)) := by
  intro q s he
  have hex : ∃ z, p z ≠ r z := by
    by_contra hn
    push Not at hn
    exact hne (Dist.ext hn)
  obtain ⟨z,hz⟩ := hex
  have hh := congrArg (fun d : Dist Z => d z) he
  rw [binary_outcomeMarginal,binary_outcomeMarginal] at hh
  have hsame : q (ULift.up true) = s (ULift.up true) := by
    dsimp [mixMass] at hh
    have hp : r z-p z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have heq : (q (ULift.up true)-s (ULift.up true))*(r z-p z) = 0 := by nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right hp)
  have hq := q.sum_eq_one
  have hs := s.sum_eq_one
  rw [Section3.sum_relevanceBit] at hq hs
  ext b
  rcases b with ⟨b⟩
  cases b <;> linarith

 theorem binary_exists_unique_optimal (p r : Dist Z) (hne : p ≠ r)
    (gap : ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    ∃! q, IsOptimal (binaryRewards gap) lambda (binaryChannel p r) q := by
  obtain ⟨q,hq⟩ := exists_optimal (binaryRewards gap) lambda (binaryChannel p r)
  exact ⟨q,hq,fun s hs => optimal_unique_of_output_injective (binaryRewards gap) hl
    (binaryChannel p r) (binary_output_injective p r hne) s q hs hq⟩

/-- Pure high-payoff choice is optimal iff the opposite row has no new output
and its finite KL value is below the payoff/trace threshold. -/
 theorem binary_pure_high_iff (p r : Dist Z) (gap : ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    IsOptimal (binaryRewards gap) lambda (binaryChannel p r) (Dist.pure (ULift.up false)) ↔
      SupportIncluded r p ∧ lambda*finiteKL r p ≤ gap := by
  classical
  rw [pure_optimal_iff (binaryRewards gap) hl (binaryChannel p r) (ULift.up false)]
  constructor
  · rintro ⟨hc,hh⟩
    refine ⟨fun z hz => hc (ULift.up true) z hz, ?_⟩
    have h := hh (ULift.up true)
    change -gap+lambda*finiteKL r p ≤ 0 at h
    linarith
  · rintro ⟨hc,hh⟩
    constructor
    · intro a z hz
      rcases a with ⟨a⟩
      cases a
      · exact hz
      · exact hc z hz
    · intro a
      rcases a with ⟨a⟩
      cases a
      · simp [binaryRewards,binaryChannel,finiteKL_self]
      · change -gap+lambda*finiteKL r p ≤ 0
        linarith

 theorem binary_not_pure_low (p r : Dist Z) (hne : p ≠ r)
    {gap lambda : ℝ} (hg : 0 ≤ gap) (hl : 0 < lambda) :
    ¬ IsOptimal (binaryRewards gap) lambda (binaryChannel p r) (Dist.pure (ULift.up true)) := by
  classical
  intro ho
  obtain ⟨hc,hh⟩ := (pure_optimal_iff (binaryRewards gap) hl (binaryChannel p r) (ULift.up true)).mp ho
  have hsupport : SupportIncluded p r := fun z hz => hc (ULift.up false) z hz
  have hkl : 0 < finiteKL p r := lt_of_le_of_ne (finiteKL_nonneg p r hsupport)
    (Ne.symm (fun he => hne ((finiteKL_eq_zero_iff p r hsupport).mp he)))
  have h := hh (ULift.up false)
  change 0+lambda*finiteKL p r ≤ -gap at h
  nlinarith

 theorem binary_optimal_interior (p r : Dist Z) (hne : p ≠ r)
    {gap lambda : ℝ} (hg : 0 ≤ gap) (hl : 0 < lambda)
    (hthreshold : ¬ (SupportIncluded r p ∧ lambda*finiteKL r p ≤ gap))
    (q : Dist RelevanceBit.{u}) (hq : IsOptimal (binaryRewards gap) lambda (binaryChannel p r) q) :
    q (ULift.up true) ∈ Ioo (0 : ℝ) 1 := by
  have hn0 : q (ULift.up true) ≠ 0 := by
    intro hz
    have he : q = Dist.pure (ULift.up false) := by
      ext b
      have hs := q.sum_eq_one
      rw [Section3.sum_relevanceBit] at hs
      rcases b with ⟨b⟩
      cases b <;> simp [Dist.pure_apply] <;> linarith
    rw [he] at hq
    exact hthreshold ((binary_pure_high_iff p r gap hl).mp hq)
  have hn1 : q (ULift.up true) ≠ 1 := by
    intro hz
    have he : q = Dist.pure (ULift.up true) := by
      ext b
      have hs := q.sum_eq_one
      rw [Section3.sum_relevanceBit] at hs
      rcases b with ⟨b⟩
      cases b <;> simp [Dist.pure_apply] <;> linarith
    rw [he] at hq
    exact binary_not_pure_low p r hne hg hl hq
  exact ⟨lt_of_le_of_ne (q.nonneg _) (Ne.symm hn0),lt_of_le_of_ne (q.prob_le_one _) hn1⟩

end TraceableAgency.Section4
