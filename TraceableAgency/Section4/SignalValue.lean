import TraceableAgency.Section4.RecordInformation

/-! A non-contractible signal adds conditional information while leaving row
rewards unchanged. With wages based on output alone, those rewards already
include wages and effort costs. -/
namespace TraceableAgency.Section4
universe u
variable {A X S : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype X] [DecidableEq X] [Nonempty X]
  [Fintype S] [DecidableEq S] [Nonempty S]

noncomputable def signalProjection : Channel (X × S) X := fun z => Dist.pure z.1

noncomputable def productionMarginal (L : Channel A (X × S)) : Channel A X :=
  Channel.postprocess L signalProjection

theorem productionMarginal_apply (L : Channel A (X × S)) (a : A) (x : X) :
    productionMarginal L a x = ∑ s, L a (x,s) := by
  simp only [productionMarginal, Channel.postprocess, signalProjection, Dist.pure_apply,
    mul_ite, mul_one, mul_zero,
    Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- I(A;S | X), using the conditional-law definition of mutual information. -/
noncomputable def signalInformation (q : Dist A) (L : Channel A (X × S)) : ℝ :=
  processingConditionalInfo q L signalProjection

theorem signal_information_chain (q : Dist A) (L : Channel A (X × S)) :
    mutualInfo q L = mutualInfo q (productionMarginal L) + signalInformation q L := by
  have := information_loss_eq_conditional q L signalProjection
  change mutualInfo q L - mutualInfo q (productionMarginal L) = signalInformation q L at this
  linarith

theorem signal_information_nonneg (q : Dist A) (L : Channel A (X × S)) :
    0 ≤ signalInformation q L := processingConditionalInfo_nonneg q L signalProjection

theorem signal_value_gain (r : A → ℝ) (lambda : ℝ) (q : Dist A) (L : Channel A (X × S)) :
    rowRewardValue r lambda q L - rowRewardValue r lambda q (productionMarginal L) =
      lambda * signalInformation q L := by
  unfold rowRewardValue
  rw [signal_information_chain q L]
  ring

theorem continuous_signal_value_gain (lambda : ℝ) (L : Channel A (X × S)) :
    Continuous (fun q : Dist A => lambda * signalInformation q L) := by
  have h := (continuous_rowRewardValue (fun _ : A => 0) lambda L).sub
    (continuous_rowRewardValue (fun _ : A => 0) lambda (productionMarginal L))
  convert h using 1
  funext q
  exact (signal_value_gain (fun _ : A => 0) lambda q L).symm

theorem signal_gain_nonneg {lambda : ℝ} (hl : 0 ≤ lambda)
    (q : Dist A) (L : Channel A (X × S)) : 0 ≤ lambda * signalInformation q L :=
  mul_nonneg hl (signal_information_nonneg q L)

theorem signal_information_eq_zero_iff (q : Dist A) (L : Channel A (X × S)) :
    signalInformation q L = 0 ↔ ProcessingConditionalIndependent q L signalProjection :=
  processingConditionalInfo_eq_zero_iff q L signalProjection

end TraceableAgency.Section4
