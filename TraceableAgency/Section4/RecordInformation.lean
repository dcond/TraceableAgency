import TraceableAgency.Section4.InformationZero

/-! The information lost in processing is conditional mutual information.
Conditional independence is stated as factorisation of every reached
conditional joint law, so it remains meaningful at boundary priors.
-/
namespace TraceableAgency.Section4
open Theorem1

universe u
variable {A Z Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype Z] [DecidableEq Z] [Nonempty Z] [Fintype Y] [DecidableEq Y]

noncomputable def extendedChannel (K : Channel A Z) (T : Channel Z Y) :
    Channel A (Z × Y) := fun a => jointDist (K a) T

theorem outcomeMarginal_extendedChannel (q : Dist A) (K : Channel A Z) (T : Channel Z Y) :
    Channel.outcomeMarginal (extendedChannel K T) q =
      jointDist (Channel.outcomeMarginal K q) T := by
  ext x
  rcases x with ⟨z,y⟩
  simp only [Channel.outcomeMarginal_apply, extendedChannel, jointDist_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem mutualInfo_extendedChannel (q : Dist A) (K : Channel A Z) (T : Channel Z Y) :
    mutualInfo q (extendedChannel K T) = mutualInfo q K := by
  unfold mutualInfo
  rw [outcomeMarginal_extendedChannel, entropy_jointDist_prior]
  simp only [extendedChannel, entropy_jointDist_prior, mul_add, Finset.sum_add_distrib]
  have hn : (∑ a, q a * ∑ z, K a z * entropy (T z)) =
      ∑ z, Channel.outcomeMarginal K q z * entropy (T z) := by
    simp only [Finset.mul_sum, Channel.outcomeMarginal_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hn]
  ring

def swapToSigma : (Z × Y) ≃ ((y : Y) × Z) where
  toFun x := ⟨x.2,x.1⟩
  invFun x := (x.2,x.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Distribution of the original output given an action and its processed output. -/
noncomputable def residualChannel (K : Channel A Z) (T : Channel Z Y) (y : Y) :
    Channel A Z := fun a => Channel.posterior T (K a) y

theorem extendedChannel_reversed (K : Channel A Z) (T : Channel Z Y) :
    Relabeling.relabelChannel (Equiv.refl A) swapToSigma (extendedChannel K T) =
      seqComposeDep (Channel.postprocess K T) (fun _ : Y => Z) (residualChannel K T) := by
  funext a
  apply Dist.ext
  intro x
  change K a x.2 * T x.2 x.1 =
    Channel.outcomeMarginal T (K a) x.1 * Channel.posterior T (K a) x.1 x.2
  exact (posterior_mul_marginal (K a) T x.1 x.2).symm

/-- I(A;Z | Y) under q(a) K(z|a) T(y|z). -/
noncomputable def processingConditionalInfo (q : Dist A) (K : Channel A Z) (T : Channel Z Y) : ℝ :=
  ∑ y, Channel.outcomeMarginal (Channel.postprocess K T) q y *
    mutualInfo (Channel.posterior (Channel.postprocess K T) q y) (residualChannel K T y)

theorem information_loss_eq_conditional (q : Dist A) (K : Channel A Z) (T : Channel Z Y) :
    mutualInfo q K - mutualInfo q (Channel.postprocess K T) = processingConditionalInfo q K T := by
  have h := mutualInfo_relabelOutcome swapToSigma q (extendedChannel K T)
  rw [extendedChannel_reversed, mutualInfo_extendedChannel, mutualInfo_seqComposeDep] at h
  unfold processingConditionalInfo
  linarith

theorem processingConditionalInfo_nonneg (q : Dist A) (K : Channel A Z) (T : Channel Z Y) :
    0 ≤ processingConditionalInfo q K T := by
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg ((Channel.outcomeMarginal _ q).nonneg y) (mutualInfo_nonneg _ _)

def ProcessingConditionalIndependent (q : Dist A) (K : Channel A Z) (T : Channel Z Y) : Prop :=
  ∀ y, 0 < Channel.outcomeMarginal (Channel.postprocess K T) q y →
    ActionOutputIndependent (Channel.posterior (Channel.postprocess K T) q y) (residualChannel K T y)

theorem processingConditionalInfo_eq_zero_iff (q : Dist A) (K : Channel A Z) (T : Channel Z Y) :
    processingConditionalInfo q K T = 0 ↔ ProcessingConditionalIndependent q K T := by
  constructor
  · intro h y hy
    have hh := summand_eq_zero_of_sum_eq_zero_of_nonneg' _
      (fun y => mul_nonneg ((Channel.outcomeMarginal _ q).nonneg y) (mutualInfo_nonneg _ _)) h y
    exact (mutualInfo_eq_zero_iff_independent _ _).mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt hy))
  · intro h
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : 0 < Channel.outcomeMarginal (Channel.postprocess K T) q y
    · rw [(mutualInfo_eq_zero_iff_independent _ _).mpr (h y hy), mul_zero]
    · have hz := le_antisymm (le_of_not_gt hy) ((Channel.outcomeMarginal _ q).nonneg y)
      rw [hz, zero_mul]

theorem record_garbling_value_loss
    {O R S : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype R] [DecidableEq R] [Nonempty R] [Fintype S] [DecidableEq S]
    (v : O → ℝ) (lambda : ℝ) (q : Dist A) (K : Channel A (O × R))
    (T : RecordProcessor O R S) :
    traceTemperedValue v lambda q K - traceTemperedValue v lambda q (recordPostprocess K T) =
      lambda * processingConditionalInfo q K (payoffPreservingRecordKernel T) := by
  unfold traceTemperedValue
  rw [expectedPayoffUtility_recordPostprocess]
  rw [← information_loss_eq_conditional]
  change _ = lambda * (mutualInfo q K - mutualInfo q (recordPostprocess K T))
  ring

theorem record_garbling_value_eq_iff
    {O R S : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
    [Fintype R] [DecidableEq R] [Nonempty R] [Fintype S] [DecidableEq S]
    (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda) (q : Dist A) (K : Channel A (O × R))
    (T : RecordProcessor O R S) :
    traceTemperedValue v lambda q K = traceTemperedValue v lambda q (recordPostprocess K T) ↔
      ProcessingConditionalIndependent q K (payoffPreservingRecordKernel T) := by
  rw [← sub_eq_zero, record_garbling_value_loss, mul_eq_zero]
  simp only [ne_of_gt hl, false_or, processingConditionalInfo_eq_zero_iff]

end TraceableAgency.Section4
