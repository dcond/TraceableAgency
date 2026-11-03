import TraceableAgency.Theorem1.MaterialCalibration.TraceValue
import TraceableAgency.PureTrace.Support.GenericFaddeev

/-! Elementary properties of the material-normalized full-revelation functional.
These precede, and do not use, any Shannon identification. -/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency
universe u

variable {O A B : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]

theorem materialEntropy_support_restriction
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (q : Dist A) :
    materialEntropy F h q = materialEntropy F h q.restrictToSupport := by
  exact (materialEntropy_eq_fullReveal F h q.restrictToSupport
    (Dist.restrictToSupport_fullSupport q)).symm

theorem relabelFullReveal_material (e : A ≃ B) (o : O) :
    Relabeling.relabelChannel e (Equiv.prodCongr (Equiv.refl O) e)
      (fullRevealWithPayoff (fun _ : A ↦ o)) =
        fullRevealWithPayoff (fun _ : B ↦ o) := by
  ext a z
  rcases z with ⟨o', b⟩
  simp [Relabeling.relabelChannel, Relabeling.relabelDist,
    fullRevealWithPayoff, Dist.pure_apply, e.symm.injective.eq_iff]

theorem materialEntropy_fullSupport_relabel
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    materialEntropy F h (Relabeling.relabelDist e q) = materialEntropy F h q := by
  rw [materialEntropy_eq_fullReveal F h q hq,
    materialEntropy_eq_fullReveal F h _ (Relabeling.relabelDist_fullSupport e q hq)]
  have hv := normalizedMarkedUtility_actionRecordEquiv F h e e q hq
    (fullRevealWithPayoff (fun _ : A ↦ materialLowOutcome F h))
  simp only [relabelFullReveal_material] at hv
  exact hv

theorem materialEntropy_relabel
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (e : A ≃ B) (q : Dist A) :
    materialEntropy F h (Relabeling.relabelDist e q) = materialEntropy F h q := by
  rw [materialEntropy_support_restriction F h (Relabeling.relabelDist e q),
    GenericFaddeev.restrict_relabel_eq_relabel_restrict,
    materialEntropy_fullSupport_relabel F h _ _ (Dist.restrictToSupport_fullSupport q),
    ← materialEntropy_support_restriction]

theorem materialEntropy_pure
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (a : A) :
    materialEntropy F h (Dist.pure a) = 0 := by
  letI : Subsingleton (supportSubtype (Dist.pure a)) := ⟨by
    intro b c
    apply Subtype.ext
    have hb : b.1 = a := by
      by_contra hb
      simpa [Dist.pure_apply, hb] using b.2
    have hc : c.1 = a := by
      by_contra hc
      simpa [Dist.pure_apply, hc] using c.2
    exact hb.trans hc.symm⟩
  unfold materialEntropy
  rw [normalizedMarkedUtility_fullReveal_const_eq_payoffLottery_of_subsingleton]
  exact normalizedMarkedUtility_low F h _ _

theorem recordPostprocess_fullReveal_forget_material (o : O) :
    recordPostprocess (fullRevealWithPayoff (fun _ : A ↦ o))
      (fun _ ↦ Dist.pure (PUnit.unit : PUnit.{u+1})) =
        uninformativeAtPayoff (A := A) o := by
  ext a z
  rcases z with ⟨o', s⟩
  cases s
  by_cases ho : o' = o
  · subst o'
    simp [recordPostprocess, payoffPreservingRecordKernel, Channel.postprocess,
      fullRevealWithPayoff, uninformativeAtPayoff, Dist.pure_apply,
      Fintype.sum_prod_type, Finset.filter_eq']
  · simp [recordPostprocess, payoffPreservingRecordKernel, Channel.postprocess,
    fullRevealWithPayoff, uninformativeAtPayoff, Dist.pure_apply,
    Fintype.sum_prod_type, ho]

theorem materialEntropy_nonneg
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (q : Dist A) :
    0 ≤ materialEntropy F h q := by
  let r := q.restrictToSupport
  have hr := Dist.restrictToSupport_fullSupport q
  have hp := h.a4 (fullRevealWithPayoff (fun _ : supportSubtype q ↦
    materialLowOutcome F h)) (fun _ ↦ Dist.pure (PUnit.unit : PUnit.{u+1})) r
  rw [recordPostprocess_fullReveal_forget_material,
    ← payoffLotteryChannel_pure_eq_uninformative] at hp
  have hv := (pairWeak_markedExperiments_iff_normalizedMarkedUtility F h r r hr hr
    (fullRevealWithPayoffExperiment (fun _ : supportSubtype q ↦ materialLowOutcome F h))
    (markedPayoffLotteryExperiment (Dist.pure (materialLowOutcome F h)))).mp hp
  rw [normalizedMarkedUtility_low] at hv
  exact hv

theorem material_supportPushforward_apply (q : Dist A)
    (d : Dist (supportSubtype q)) (a : A) :
    supportPushforwardPosterior q d a = if h : q a > 0 then d ⟨a, h⟩ else 0 := by
  classical
  change (∑ c : supportSubtype q, d c * (Dist.pure c.1) a) = _
  by_cases ha : q a > 0
  · rw [dif_pos ha]
    erw [Finset.sum_eq_single (⟨a, ha⟩ : supportSubtype q)]
    · simp
    · intro c _ hc
      have hca : c.1 ≠ a := fun he ↦ hc (Subtype.ext he)
      simp [Dist.pure_apply, Ne.symm hca]
    · intro hc
      exact absurd (Finset.mem_univ (⟨a, ha⟩ : supportSubtype q)) hc
  · rw [dif_neg ha]
    apply Finset.sum_eq_zero
    intro c _
    have hca : c.1 ≠ a := by rintro rfl; exact ha c.2
    simp [Dist.pure_apply, Ne.symm hca]

noncomputable def materialSupportIncludeEquiv (q : Dist A)
    (d : Dist (supportSubtype q)) :
    supportSubtype d ≃ supportSubtype (supportPushforwardPosterior q d) where
  toFun b := ⟨b.1.1, by
    rw [material_supportPushforward_apply, dif_pos b.1.2]
    exact b.2⟩
  invFun b := by
    have hq : q b.1 > 0 := by
      by_contra hn
      have hz := material_supportPushforward_apply q d b.1
      rw [dif_neg hn] at hz
      have := b.2
      rw [hz] at this
      linarith
    exact ⟨⟨b.1, hq⟩, by
      have := b.2
      rwa [material_supportPushforward_apply, dif_pos hq] at this⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem material_restrict_supportPushforward_eq (q : Dist A)
    (d : Dist (supportSubtype q)) :
    (supportPushforwardPosterior q d).restrictToSupport =
      Relabeling.relabelDist (materialSupportIncludeEquiv q d) d.restrictToSupport := by
  ext b
  have hq : q b.1 > 0 := by
    by_contra hn
    have hz := material_supportPushforward_apply q d b.1
    rw [dif_neg hn] at hz
    have := b.2
    rw [hz] at this
    linarith
  simp [Dist.restrictToSupport_apply, Relabeling.relabelDist,
    materialSupportIncludeEquiv, material_supportPushforward_apply, hq]

theorem materialEntropy_supportPushforward
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (d : Dist (supportSubtype q)) :
    materialEntropy F h (supportPushforwardPosterior q d) = materialEntropy F h d := by
  rw [materialEntropy_support_restriction F h (supportPushforwardPosterior q d),
    material_restrict_supportPushforward_eq, materialEntropy_relabel,
    ← materialEntropy_support_restriction]

section Blocks

variable {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
variable (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
variable [∀ k, Nonempty (Act k)] [Nonempty (Sigma Act)]

/-- The support of a block-supported distribution is its intrinsic support. -/
noncomputable def materialBlockSupportEquiv (k : K) (q : Dist (Act k)) :
    supportSubtype (blockEmbedDist Act k q) ≃ supportSubtype q where
  toFun b := by
    rcases b with ⟨⟨j, a⟩, hb⟩
    have hjk : j = k := by
      by_contra hne
      rw [blockEmbedDist_apply_ne Act hne q a] at hb
      linarith
    subst j
    exact ⟨a, by simpa using hb⟩
  invFun a := ⟨⟨k, a.1⟩, by simpa using a.2⟩
  left_inv b := by
    rcases b with ⟨⟨j, a⟩, hb⟩
    have hjk : j = k := by
      by_contra hne
      rw [blockEmbedDist_apply_ne Act hne q a] at hb
      linarith
    subst j
    rfl
  right_inv _ := rfl

theorem material_restrict_blockEmbed_eq_relabel_support
    (k : K) (q : Dist (Act k)) :
    (blockEmbedDist Act k q).restrictToSupport =
      Relabeling.relabelDist (materialBlockSupportEquiv Act k q).symm
        q.restrictToSupport := by
  ext b
  rcases b with ⟨⟨j, a⟩, hb⟩
  have hjk : j = k := by
    by_contra hne
    rw [blockEmbedDist_apply_ne Act hne q a] at hb
    linarith
  subst j
  simp [Relabeling.relabelDist, materialBlockSupportEquiv, Dist.restrictToSupport_apply]

theorem materialEntropy_blockEmbed
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (k : K) (q : Dist (Act k)) :
    materialEntropy F h (blockEmbedDist Act k q) = materialEntropy F h q := by
  rw [materialEntropy_support_restriction F h (blockEmbedDist Act k q),
    material_restrict_blockEmbed_eq_relabel_support,
    materialEntropy_relabel, ← materialEntropy_support_restriction]

end Blocks

end TraceableAgency.Theorem1.MaterialCalibration
