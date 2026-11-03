import TraceableAgency.Theorem1.MaterialCalibration.CompoundValue

/-!
# Entropy reduction from material-calibrated branch comparisons

Reveal the action after every first-stage record, and compare this compound
with stopping at the first-stage record. Exact branch weights give the
full-revelation value minus its expected posterior value.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A Y R : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]
variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- A fixed payoff and fixed record leave the prior unchanged. -/
theorem markedChannelIntegral_constantPure
    (q : Dist A) (o : O) (r : R) (phi : O × Dist A → ℝ) :
    markedChannelIntegral q (fun _ : A ↦ Dist.pure (o, r)) phi = phi (o, q) := by
  classical
  have hm : Channel.outcomeMarginal (fun _ : A ↦ Dist.pure (o, r)) q (o, r) = 1 := by
    simp [Channel.outcomeMarginal_apply, q.sum_eq_one]
  have hp : Channel.posterior (fun _ : A ↦ Dist.pure (o, r)) q (o, r) = q := by
    have hpos : 0 < Channel.outcomeMarginal
        (fun _ : A ↦ Dist.pure (o, r)) q (o, r) := by rw [hm]; norm_num
    ext a
    unfold Channel.posterior
    rw [dif_pos hpos]
    simp [Channel.outcomeMarginal_apply, q.sum_eq_one]
  unfold markedChannelIntegral
  rw [Finset.sum_eq_single (o, r)]
  · rw [hm, hp, one_mul]
  · intro z _hz hne
    simp [Channel.outcomeMarginal_apply, Dist.pure_apply, hne]
  · simp

theorem normalizedMarkedUtility_constantLow
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (r : R) :
    normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel
          (fun _ : A ↦ Dist.pure (materialLowOutcome F h, r))) = 0 := by
  have hlaw : SameMarkedTerminalLaw q
      (markedExperimentOfChannel
        (fun _ : A ↦ Dist.pure (materialLowOutcome F h, r)))
      (markedMaterialLowExperiment F h) := by
    intro phi
    change markedChannelIntegral q
      (fun _ : A ↦ Dist.pure (materialLowOutcome F h, r)) phi = _
    rw [markedChannelIntegral_constantPure,
      markedTerminalIntegral_markedPayoffLottery]
    simp [payoffLotteryExpected, Dist.pure_apply]
  rw [normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _ hlaw,
    normalizedMarkedUtility_low]

theorem supportPushforwardPosterior_pure (q : Dist A) (a : supportSubtype q) :
    supportPushforwardPosterior q (Dist.pure a) = Dist.pure a.val := by
  ext b
  change (∑ x : supportSubtype q, Dist.pure a x * supportIncludeKernel q x b) = _
  rw [Finset.sum_eq_single a]
  · simp [supportIncludeKernel]
  · intro x _hx hxa
    simp [Dist.pure_apply, hxa]
  · simp

/-- Extending support-face full revelation has the ambient full-revelation law. -/
theorem markedChannelIntegral_supportExtend_fullReveal
    (q : Dist A) (o : O) (phi : O × Dist A → ℝ) :
    markedChannelIntegral q
        (supportExtendChannel q
          (fullRevealWithPayoff (fun _ : supportSubtype q ↦ o))) phi =
      ∑ a, q a * phi (o, Dist.pure a) := by
  have ht := markedTerminalIntegral_supportExtend q
    (fullRevealWithPayoffExperiment (fun _ : supportSubtype q ↦ o)) phi
  change markedChannelIntegral q
    (supportExtendChannel q
      (fullRevealWithPayoff (fun _ : supportSubtype q ↦ o))) phi = _ at ht
  rw [ht, markedTerminalIntegral_fullRevealWithPayoffExperiment]
  simp only [supportPushforwardPosterior_pure, Dist.restrictToSupport_apply]
  exact sum_supportSubtype_eq_sum_of_zero q
    (fun a ↦ q a * phi (o, Dist.pure a)) (fun a ha ↦ by rw [ha, zero_mul])

/-- Restricting full revelation to a support face only changes its record labels. -/
theorem sameMarkedTerminalLaw_restrict_fullReveal (q : Dist A) (o : O) :
    SameMarkedTerminalLaw q.restrictToSupport
      (markedExperimentOfChannel
        (Channel.restrictToSupport (fullRevealWithPayoff (fun _ : A ↦ o)) q))
      (fullRevealWithPayoffExperiment (fun _ : supportSubtype q ↦ o)) := by
  classical
  intro psi
  let phi : O × Dist A → ℝ := fun op ↦
    Function.extend (supportPushforwardPosterior q)
      (fun d ↦ psi (op.1, d)) (fun _ ↦ 0) op.2
  have hinj : Function.Injective (supportPushforwardPosterior q) :=
    supportFaceInclude_injective q
  have hphi (o' : O) (d : Dist (supportSubtype q)) :
      phi (o', supportPushforwardPosterior q d) = psi (o', d) :=
    hinj.extend_apply _ _ d
  have heq : markedChannelIntegral q (fullRevealWithPayoff (fun _ : A ↦ o)) phi =
      markedChannelIntegral q (supportExtendChannel q
        (fullRevealWithPayoff (fun _ : supportSubtype q ↦ o))) phi := by
    rw [markedChannelIntegral_fullRevealWithPayoff,
      markedChannelIntegral_supportExtend_fullReveal]
  have hext := markedTerminalIntegral_supportExtend q
    (fullRevealWithPayoffExperiment (fun _ : supportSubtype q ↦ o)) phi
  change markedChannelIntegral q (supportExtendChannel q
    (fullRevealWithPayoff (fun _ : supportSubtype q ↦ o))) phi = _ at hext
  rw [markedChannelIntegral_restrictToSupport_material, hext] at heq
  have htest : (fun op : O × Dist (supportSubtype q) ↦
      phi (op.1, supportPushforwardPosterior q op.2)) = psi := by
    funext op
    rw [hphi]
  rw [htest] at heq
  exact heq

/-- Revealing the action after every record has exactly the full-revelation law. -/
theorem sameMarkedTerminalLaw_compound_supportFullReveal
    (q : Dist A) (P : Channel A Y) (o : O) :
    SameMarkedTerminalLaw q
      (markedExperimentOfChannel
        (commonPayoffCompound (fun y ↦ supportSubtype (branchPosterior P q y)) P
          (fun y ↦ supportExtendChannel (branchPosterior P q y)
            (fullRevealWithPayoff
              (fun _ : supportSubtype (branchPosterior P q y) ↦ o)))))
      (fullRevealWithPayoffExperiment (fun _ : A ↦ o)) := by
  intro phi
  change markedChannelIntegral q (commonPayoffCompound _ P _) phi = _
  rw [markedChannelIntegral_commonPayoffCompound,
    markedTerminalIntegral_fullRevealWithPayoffExperiment]
  change (∑ y, Channel.outcomeMarginal P q y *
    markedChannelIntegral (branchPosterior P q y)
      (supportExtendChannel (branchPosterior P q y)
        (fullRevealWithPayoff (fun _ : supportSubtype (branchPosterior P q y) ↦ o))) phi) = _
  simp_rw [markedChannelIntegral_supportExtend_fullReveal, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  simp_rw [← mul_assoc, branchPosterior, posterior_mul_marginal]
  rw [← Finset.sum_mul, ← Finset.mul_sum, (P a).sum_eq_one, mul_one]

/-- Stopping after the first record is unaffected by its fixed terminal label. -/
theorem sameMarkedTerminalLaw_compound_constantPure
    (q : Dist A) (P : Channel A Y) (o : O)
    (Rec : Y → Type u)
    [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
    [∀ y, Nonempty (Rec y)] (record : ∀ y, Rec y) :
    SameMarkedTerminalLaw q
      (markedExperimentOfChannel
        (commonPayoffCompound Rec P (fun y _ ↦ Dist.pure (o, record y))))
      (payoffBranchExperiment P (fun _ ↦ o)) := by
  intro phi
  change markedChannelIntegral q (commonPayoffCompound Rec P _) phi =
    markedChannelIntegral q (payoffBranchCompound P _) phi
  rw [payoffBranchCompound, markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [markedChannelIntegral_constantPure]
  simp only [payoffBranchContinuation]
  rw [markedChannelIntegral_uninformativeAtPayoff]

/-- Exact entropy reduction, obtained before identifying entropy with Shannon's
formula. Null records are included with zero coefficient. -/
theorem materialTraceValue_eq_entropy_sub_expected
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y) :
    materialTraceValue F h q hq P =
      materialEntropy F h q -
        ∑ y, Channel.outcomeMarginal P q y *
          materialEntropy F h (branchPosterior P q y) := by
  classical
  let low := materialLowOutcome F h
  let Rec := fun y ↦ supportSubtype (branchPosterior P q y)
  let K : ∀ y, Channel A (O × Rec y) := fun y ↦
    supportExtendChannel (branchPosterior P q y)
      (fullRevealWithPayoff (fun _ : Rec y ↦ low))
  let L : ∀ y, Channel A (O × Rec y) := fun y _ ↦
    Dist.pure (low, supportDefault (branchPosterior P q y))
  have hv := normalizedMarkedUtility_compound_difference_material F h Rec q hq P K L
  have hK := normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _
    (sameMarkedTerminalLaw_compound_supportFullReveal q P low)
  have hL := normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _
    (sameMarkedTerminalLaw_compound_constantPure q P low Rec
      (fun y ↦ supportDefault (branchPosterior P q y)))
  change normalizedMarkedUtility F h q hq
    (markedExperimentOfChannel (commonPayoffCompound Rec P K)) = _ at hK
  change normalizedMarkedUtility F h q hq
    (markedExperimentOfChannel (commonPayoffCompound Rec P L)) = _ at hL
  rw [hK, hL, ← materialEntropy_eq_fullReveal F h q hq] at hv
  have hlocalK (y : Y) :
      normalizedMarkedUtility F h (branchPosterior P q y).restrictToSupport
          (Dist.restrictToSupport_fullSupport _)
          (markedExperimentOfChannel
            (Channel.restrictToSupport (K y) (branchPosterior P q y))) =
        materialEntropy F h (branchPosterior P q y) := by
    dsimp [K]
    rw [restrictToSupport_supportExtendChannel]
    rfl
  have hlocalL (y : Y) :
      normalizedMarkedUtility F h (branchPosterior P q y).restrictToSupport
          (Dist.restrictToSupport_fullSupport _)
          (markedExperimentOfChannel
            (Channel.restrictToSupport (L y) (branchPosterior P q y))) = 0 := by
    exact normalizedMarkedUtility_constantLow F h _ _ _
  simp_rw [hlocalK, hlocalL, sub_zero] at hv
  change materialEntropy F h q - materialTraceValue F h q hq P = _ at hv
  linarith

end TraceableAgency.Theorem1.MaterialCalibration
