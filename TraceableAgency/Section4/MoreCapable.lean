import TraceableAgency.Section4.MoreCapableAnalysis
import TraceableAgency.Section4.RecordInformation
import TraceableAgency.Section4.MoralHazard.Optimization
import TraceableAgency.Theorem1.ConstantTraceAnchorGeneral
import TraceableAgency.Section3.UniquenessMixture

/-! The uniform record-technology order and its strict distinction from
payoff-preserving garbling, as in v11 Proposition 30. -/
namespace TraceableAgency.Section4.MoreCapable
open TraceableAgency Theorem1 Set
universe u

section Orders
variable {O A R S : Type u} [Fintype O] [DecidableEq O]
  [Fintype A] [Fintype R] [Fintype S] [DecidableEq S]

/-- Every action induces the same distribution of material payoffs. -/
def SamePayoffKernels (K : Channel A (O × R)) (L : Channel A (O × S)) : Prop :=
  ∀ a o, (∑ r, K a (o,r)) = ∑ s, L a (o,s)

/-- More-capable comparison: the whole visible output is more informative at
 every action prior. -/
def InformationDominates (K : Channel A (O × R)) (L : Channel A (O × S)) : Prop :=
  ∀ q : Dist A, mutualInfo q L ≤ mutualInfo q K

/-- A single payoff-preserving record processor carries the first channel to
 the second, independently of the action prior. -/
def GarblingDominates (K : Channel A (O × R)) (L : Channel A (O × S)) : Prop :=
  ∃ T : RecordProcessor O R S, recordPostprocess K T = L

theorem samePayoff_expectedUtility (K : Channel A (O × R)) (L : Channel A (O × S))
    (h : SamePayoffKernels K L) (v : O → ℝ) (q : Dist A) :
    expectedPayoffUtility v q K = expectedPayoffUtility v q L := by
  unfold expectedPayoffUtility
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp only [Fintype.sum_prod_type, ← Finset.sum_mul]
  simp_rw [h a]

/-- At the common positive trace coefficient, uniform value dominance is
 exactly the more-capable order when payoff kernels coincide. -/
theorem uniform_value_dominance_iff (K : Channel A (O × R)) (L : Channel A (O × S))
    (h : SamePayoffKernels K L) (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda) :
    (∀ q, traceTemperedValue v lambda q L ≤ traceTemperedValue v lambda q K) ↔
      InformationDominates K L := by
  unfold InformationDominates traceTemperedValue
  simp_rw [samePayoff_expectedUtility K L h v]
  simp only [add_le_add_iff_left, mul_le_mul_iff_right₀ hl]

theorem garbling_implies_information_dominance (K : Channel A (O × R))
    (L : Channel A (O × S)) (h : GarblingDominates K L) :
    InformationDominates K L := by
  classical
  obtain ⟨T,rfl⟩ := h
  intro q
  exact mutualInfo_outcome_postprocess_le q K (payoffPreservingRecordKernel T)

end Orders

/-- Reveal the binary action with probability one half; otherwise report the
 distinct erasure output `Sum.inr ()`. -/
noncomputable def erasure : Channel Bool (Bool ⊕ Unit) :=
  publicMixChannel (1/2) (by norm_num) (by norm_num) Channel.idChannel
    (fun _ => Dist.pure ())

private noncomputable def noisyTechnology : BernoulliTechnology where
  low := 1/5
  high := 4/5
  low_pos := by norm_num
  productive := by norm_num
  high_lt_one := by norm_num

/-- Binary symmetric noise with crossover probability one fifth. -/
noncomputable def noisyBinary : Channel Bool Bool := noisyTechnology.channel

theorem erasure_information (q : Dist Bool) :
    mutualInfo q erasure = (1/2)*Real.binEntropy (q true) := by
  unfold erasure
  rw [mutualInfo_publicMixChannel, mutualInfo_idChannel', Section3.mutualInfo_constant]
  simp only [mul_zero,add_zero]
  congr 1
  rw [dist_bool_eq_bernoulli q,entropy_bernoulli]
  rfl

theorem noisyBinary_information (q : Dist Bool) :
    mutualInfo q noisyBinary = Real.binEntropy (1/5+3/5*q true)-Real.binEntropy (1/5) := by
  have hh := noisyTechnology.mutualInfo_eq (q true) (q.nonneg true) (q.prob_le_one true)
  rw [← dist_bool_eq_bernoulli q] at hh
  change mutualInfo q noisyBinary = _ at hh
  rw [hh]
  have hs : Real.binEntropy (4/5) = Real.binEntropy (1/5) := by
    rw [show (4/5:ℝ) = 1-(1/5) by norm_num,Real.binEntropy_one_sub]
  simp only [BernoulliTechnology.information,BernoulliTechnology.mean,
    BernoulliTechnology.gap,noisyTechnology]
  rw [hs]
  norm_num
  rw [show (1/5:ℝ) + q true*(3/5) = 1/5+3/5*q true by ring]
  ring

/-- The erasure channel is more capable at every binary prior. -/
theorem erasure_moreCapable_noisyBinary (q : Dist Bool) :
    mutualInfo q noisyBinary ≤ mutualInfo q erasure := by
  rw [erasure_information,noisyBinary_information]
  exact binary_entropy_comparison ⟨q.nonneg true,q.prob_le_one true⟩

/-- No stochastic postprocessor of the erasure output yields the noisy row:
 the common erasure part cancels, leaving a row difference at most one half,
 whereas the noisy binary channel has difference three fifths. -/
theorem erasure_not_garbling_noisyBinary :
    ¬ ∃ T : Channel (Bool ⊕ Unit) Bool, Channel.postprocess erasure T = noisyBinary := by
  rintro ⟨T,h⟩
  have h0 := congrArg (fun K : Channel Bool Bool => K false false) h
  have h1 := congrArg (fun K : Channel Bool Bool => K true false) h
  simp [Channel.postprocess,erasure,publicMixChannel,Channel.idChannel,
    Dist.pure_apply,Fintype.sum_sum_type,Fintype.sum_bool,noisyBinary,
    BernoulliTechnology.channel,noisyTechnology,bernoulli] at h0 h1
  have hle := (T (Sum.inl false)).prob_le_one false
  have hge := (T (Sum.inl true)).nonneg false
  linarith

/-- Attach a common sure payoff to the two concrete record technologies. -/
noncomputable def erasureMarked : Channel Bool (Unit × (Bool ⊕ Unit)) :=
  constantPayoffLift () erasure
noncomputable def noisyMarked : Channel Bool (Unit × Bool) :=
  constantPayoffLift () noisyBinary

theorem counterexample_same_payoff_kernels : SamePayoffKernels erasureMarked noisyMarked := by
  intro a o
  cases o
  change (∑ r, erasure a r) = ∑ s, noisyBinary a s
  rw [(erasure a).sum_eq_one,(noisyBinary a).sum_eq_one]

theorem counterexample_information_dominance : InformationDominates erasureMarked noisyMarked := by
  intro q
  simpa only [erasureMarked,noisyMarked,mutualInfo_constantPayoffLift] using
    erasure_moreCapable_noisyBinary q

theorem counterexample_not_record_garbling : ¬ GarblingDominates erasureMarked noisyMarked := by
  rintro ⟨T,h⟩
  apply erasure_not_garbling_noisyBinary
  refine ⟨fun r => T ((),r),?_⟩
  funext a
  apply Dist.ext
  intro s
  have he := congrArg (fun K : Channel Bool (Unit × Bool) => K a ((),s)) h
  simpa [recordPostprocess,Channel.postprocess,payoffPreservingRecordKernel,
    erasureMarked,noisyMarked,constantPayoffLift_apply,Fintype.sum_prod_type] using he

/-- Proposition 30(ii)'s counterexample uses the same sure material payoff and
 dominates for every prior, but admits no payoff-preserving record processor. -/
theorem exists_moreCapable_not_garbling :
    ∃ (K : Channel Bool (Unit × (Bool ⊕ Unit))) (L : Channel Bool (Unit × Bool)),
      SamePayoffKernels K L ∧ InformationDominates K L ∧ ¬ GarblingDominates K L :=
  ⟨erasureMarked,noisyMarked,counterexample_same_payoff_kernels,
    counterexample_information_dominance,counterexample_not_record_garbling⟩

end TraceableAgency.Section4.MoreCapable
