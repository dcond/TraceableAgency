import TraceableAgency.Section4.RecordInformation
import TraceableAgency.Section3.Range

/-! The recorded public coin: affinity when the tag is visible, and the exact
conditional-information cost of hiding it. -/
namespace TraceableAgency.Section4
open Theorem1
universe u
variable {O A R : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
  [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype R] [DecidableEq R] [Nonempty R]

noncomputable def recordedCoinChannel (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (K L : Channel A (O × R)) : Channel A (O × (R ⊕ R)) :=
  Relabeling.relabelChannel (Equiv.refl A) (sumPayoffRecordEquiv O R R)
    (publicMixChannel t ht0 ht1 K L)

noncomputable def hiddenCoinChannel (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (K L : Channel A (O × R)) : Channel A (O × R) :=
  fun a => Dist.mix t ht0.le ht1.le (K a) (L a)

noncomputable def eraseCoin : RecordProcessor O (R ⊕ R) R :=
  fun z => Dist.pure (Sum.elim id id z.2)

theorem recorded_coin_value (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (K L : Channel A (O × R)) :
    traceTemperedValue v lambda q (recordedCoinChannel t ht0 ht1 K L) =
      t * traceTemperedValue v lambda q K + (1-t) * traceTemperedValue v lambda q L := by
  let E : MarkedTerminalExperiment O A :=
    ⟨R,inferInstance,inferInstance,inferInstance,K⟩
  let G : MarkedTerminalExperiment O A :=
    ⟨R,inferInstance,inferInstance,inferInstance,L⟩
  exact Section3.markedValue_publicMix v lambda q t ht0 ht1 E G

theorem erase_recordedCoin (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (K L : Channel A (O × R)) :
    recordPostprocess (recordedCoinChannel t ht0 ht1 K L) eraseCoin =
      hiddenCoinChannel t ht0 ht1 K L := by
  funext a
  apply Dist.ext
  intro x
  rcases x with ⟨o,r⟩
  simp [recordPostprocess, Channel.postprocess, payoffPreservingRecordKernel,
    eraseCoin, recordedCoinChannel, hiddenCoinChannel, Relabeling.relabelChannel,
    Relabeling.relabelDist, sumPayoffRecordEquiv, publicMixChannel,
    Fintype.sum_prod_type, Fintype.sum_sum_type, Dist.pure_apply, Dist.mix_apply]

theorem recorded_coin_hiding_cost (v : O → ℝ) (lambda : ℝ) (q : Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (K L : Channel A (O × R)) :
    traceTemperedValue v lambda q (recordedCoinChannel t ht0 ht1 K L) -
      traceTemperedValue v lambda q (hiddenCoinChannel t ht0 ht1 K L) =
      lambda * processingConditionalInfo q (recordedCoinChannel t ht0 ht1 K L)
        (payoffPreservingRecordKernel eraseCoin) := by
  rw [← erase_recordedCoin]
  exact record_garbling_value_loss v lambda q _ eraseCoin

theorem recorded_coin_hiding_cost_nonneg (v : O → ℝ) {lambda : ℝ} (hl : 0 ≤ lambda)
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (K L : Channel A (O × R)) :
    traceTemperedValue v lambda q (hiddenCoinChannel t ht0 ht1 K L) ≤
      traceTemperedValue v lambda q (recordedCoinChannel t ht0 ht1 K L) := by
  apply sub_nonneg.mp
  rw [recorded_coin_hiding_cost]
  exact mul_nonneg hl (processingConditionalInfo_nonneg _ _ _)

theorem recorded_coin_hiding_eq_iff (v : O → ℝ) {lambda : ℝ} (hl : 0 < lambda)
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (K L : Channel A (O × R)) :
    traceTemperedValue v lambda q (recordedCoinChannel t ht0 ht1 K L) =
      traceTemperedValue v lambda q (hiddenCoinChannel t ht0 ht1 K L) ↔
      ProcessingConditionalIndependent q (recordedCoinChannel t ht0 ht1 K L)
        (payoffPreservingRecordKernel eraseCoin) := by
  rw [← erase_recordedCoin]
  exact record_garbling_value_eq_iff v hl q _ eraseCoin

end TraceableAgency.Section4
