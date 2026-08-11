/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.EmbeddingDefect

namespace TraceableAgency

universe u

/-- Selected embedding-defect cocycle. -/
theorem cardDefect_cocycleFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m l : ℕ) [NeZero l] [NeZero m] [NeZero n]
    (hl2 : 2 ≤ l) (hlm : l < m) (hmn : m < n) :
    cardDefectFor hhm hax hbranchData n m *
        cardDefectFor hhm hax hbranchData m l =
      cardDefectFor hhm hax hbranchData n l := by
  classical
  have hle_ml : l ≤ m := le_of_lt hlm
  have hle_mn : m ≤ n := le_of_lt hmn
  have hle_ln : l ≤ n := hle_ml.trans hle_mn
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hintdef
  set hlin := affineLinearPart_of_FinalHMInterface hhm with hlindef
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n l hle_ln)) :=
    supportSubtype_nonempty _
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hle_mn)) :=
    supportSubtype_nonempty _
  have hfaceNL_fs :
      ((canonBoundary.{u} n l hle_ln).restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport _
  have hfaceNL_nd :
      ∃ a b : supportSubtype (canonBoundary.{u} n l hle_ln), a ≠ b ∧
        0 < (canonBoundary.{u} n l hle_ln).restrictToSupport a ∧
        0 < (canonBoundary.{u} n l hle_ln).restrictToSupport b := by
    have hcard :
        Fintype.card (supportSubtype (canonBoundary.{u} n l hle_ln)) = l := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n l hle_ln)]
      simp [canonType]
    obtain ⟨a, b, hab⟩ :=
      Fintype.exists_pair_of_one_lt_card
        (by omega :
          1 < Fintype.card (supportSubtype (canonBoundary.{u} n l hle_ln)))
    exact ⟨a, b, hab, hfaceNL_fs a, hfaceNL_fs b⟩
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      (canonBoundary.{u} n l hle_ln).restrictToSupport
      (canonBoundary.{u} n l hle_ln).restrictToSupport
      hfaceNL_fs hfaceNL_fs hfaceNL_nd
  have hηnz' :
      η (hint.marginalValue F hV
        (canonBoundary.{u} n l hle_ln).restrictToSupport) ≠ 0 := hηnz
  have hT_nl :=
    cardDefect_transportFor hhm hax hbranchData n l hl2
      (lt_of_lt_of_le hlm hle_mn) η hηatomic hηtan
  set η'' : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m hle_mn)) :=
    (fun ψ => η (fun d => ψ (Channel.actionPushforward d
      (fun a => Dist.pure (nestSupportMap n m l hle_mn hle_ml a))))) with hη''def
  have hη''tan : PosteriorLawTangent η'' := by
    refine ⟨?_, ?_⟩
    · show η (fun d => (1:ℝ)) = 0
      exact hηtan.1
    · intro a
      show η (fun d => (Channel.actionPushforward d
        (fun a' => Dist.pure (nestSupportMap n m l hle_mn hle_ml a'))) a) = 0
      by_cases hex : ∃ a'₀ : supportSubtype (canonBoundary.{u} n l hle_ln),
          nestSupportMap n m l hle_mn hle_ml a'₀ = a
      · obtain ⟨a'₀, ha'₀⟩ := hex
        have hfn : (fun d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)) =>
            (Channel.actionPushforward d
              (fun a' => Dist.pure (nestSupportMap n m l hle_mn hle_ml a'))) a) =
            (fun d => d a'₀) := by
          funext d
          show (∑ a' : supportSubtype (canonBoundary.{u} n l hle_ln),
            d a' * (Dist.pure (nestSupportMap n m l hle_mn hle_ml a') : Dist _) a) =
              d a'₀
          rw [Finset.sum_eq_single a'₀]
          · rw [ha'₀, Dist.pure_apply_self, mul_one]
          · intro b _ hb
            rw [Dist.pure_apply_ne, mul_zero]
            intro hc
            apply hb
            have hb1 : (nestSupportMap n m l hle_mn hle_ml b).1 = a.1 := by
              rw [← hc]
            have ha1 : (nestSupportMap n m l hle_mn hle_ml a'₀).1 = a.1 := by
              rw [ha'₀]
            apply Subtype.ext
            have : (b.1 : canonType.{u} n) = a'₀.1 := by
              have := hb1.trans ha1.symm
              simpa [nestSupportMap] using this
            exact this
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [hfn]
        exact hηtan.2 a'₀
      · have hfn : (fun d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)) =>
            (Channel.actionPushforward d
              (fun a' => Dist.pure (nestSupportMap n m l hle_mn hle_ml a'))) a) =
            (fun _ => (0:ℝ)) := by
          funext d
          show (∑ a' : supportSubtype (canonBoundary.{u} n l hle_ln),
            d a' * (Dist.pure (nestSupportMap n m l hle_mn hle_ml a') : Dist _) a) = 0
          apply Finset.sum_eq_zero
          intro a' _
          rw [Dist.pure_apply_ne, mul_zero]
          intro hc
          exact hex ⟨a', hc.symm⟩
        rw [hfn]
        have h0 := congrFun hηatomic.eval_eq (fun _ => (0:ℝ))
        rw [AtomicPosteriorSignedLaw.eval_apply] at h0
        rw [← h0]
        simp
  have hη''atomic : PosteriorLawSigned.AtomicLinear η'' := by
    rw [hη''def]
    exact atomicLinear_pushSignedDet
      (nestSupportMap n m l hle_mn hle_ml) hηatomic
  have hLHS_link :
      η (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} n))
            (Channel.actionPushforward d
              (supportIncludeKernel (canonBoundary.{u} n l hle_ln)))) =
      η'' (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} n))
            (Channel.actionPushforward d
              (supportIncludeKernel (canonBoundary.{u} n m hle_mn)))) := by
    rw [hη''def]
    congr 1
    funext d
    rw [supportInclude_nest n m l hle_mn hle_ml d]
  have h2m : 2 ≤ m := le_of_lt (lt_of_le_of_lt hl2 hlm)
  have hT_nm :=
    cardDefect_transportFor hhm hax hbranchData n m h2m hmn
      η'' hη''atomic hη''tan
  have hchain1 :
      cardDefectFor hhm hax hbranchData n l *
        η (hint.marginalValue F hV
          (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      cardDefectFor hhm hax hbranchData n m *
        η'' (hint.marginalValue F hV
          (canonBoundary.{u} n m hle_mn).restrictToSupport) := by
    rw [← hT_nl, hLHS_link, hT_nm]
  have hbridge :
      η'' (hint.marginalValue F hV
          (canonBoundary.{u} n m hle_mn).restrictToSupport) =
      cardDefectFor hhm hax hbranchData m l *
        η (hint.marginalValue F hV
          (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
    let eNM :=
      canonBoundarySupportEquiv n m hle_mn
    have hfaceNM :
        Relabeling.relabelDist eNM
            (canonBoundary.{u} n m hle_mn).restrictToSupport =
          Dist.uniform (A := canonType.{u} m) := by
      rw [cBface_eq_relabel_uniform n m hle_mn]
      ext a
      simp [Relabeling.relabelDist_apply]
    have hnatural :=
      finalHM_affineLinearPart_relabel_atomic_eval hhm hax eNM
        (canonBoundary.{u} n m hle_mn).restrictToSupport
        (Dist.restrictToSupport_fullSupport _)
        η'' hη''atomic hη''tan
    rw [hfaceNM] at hnatural
    rw [← hnatural]
    change η (fun d => hint.marginalValue F hV
      (Dist.uniform (A := canonType.{u} m))
      (Relabeling.relabelDist eNM
        (Channel.actionPushforward d
          (fun a => Dist.pure
            (nestSupportMap n m l hle_mn hle_ml a))))) = _
    have hpush : ∀ d,
        Relabeling.relabelDist eNM
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (nestSupportMap n m l hle_mn hle_ml a))) =
          Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml) := by
      intro d
      calc
        Relabeling.relabelDist eNM
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (nestSupportMap n m l hle_mn hle_ml a))) =
            Relabeling.relabelDist eNM
              (Relabeling.relabelDist eNM.symm
                (Channel.actionPushforward
                  (Channel.actionPushforward d
                    (fun a => Dist.pure
                      (canonBoundarySupportEquiv n l hle_ln a)))
                  (canonInclKernel m l hle_ml))) :=
              congrArg (Relabeling.relabelDist eNM)
                (push_nest_eq_relabel n m l hle_mn hle_ml d)
        _ = _ := by
          ext a
          simp [Relabeling.relabelDist_apply]
    have hleft :
        η (fun d => hint.marginalValue F hV
          (Dist.uniform (A := canonType.{u} m))
          (Relabeling.relabelDist eNM
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (nestSupportMap n m l hle_mn hle_ml a))))) =
        η (fun d => hint.marginalValue F hV
          (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure
                (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml))) := by
      congr 1
      funext d
      rw [hpush d]
    rw [hleft]
    set φ :
        supportSubtype (canonBoundary.{u} n l hle_ln) ≃
          supportSubtype (canonBoundary.{u} m l hle_ml) :=
      (canonBoundarySupportEquiv n l hle_ln).trans
        (canonBoundarySupportEquiv m l hle_ml).symm with hφdef
    haveI : Nonempty (supportSubtype (canonBoundary.{u} m l hle_ml)) :=
      supportSubtype_nonempty _
    have hreindex : ∀ d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)),
        Channel.actionPushforward
          (Channel.actionPushforward d
            (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
          (canonInclKernel m l hle_ml) =
        Channel.actionPushforward (relabelDist φ d)
          (supportIncludeKernel (canonBoundary.{u} m l hle_ml)) := by
      intro d
      rw [canonIncl_eq_supportInclude m l hle_ml
        (Channel.actionPushforward d
          (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))]
      congr 1
      rw [relabelDist_eq_actionPushforward]
      rw [actionPushforward_pure_comp d
        (fun a => canonBoundarySupportEquiv n l hle_ln a)
        (fun b => (canonBoundarySupportEquiv m l hle_ml).symm b)]
      apply congrArg (Channel.actionPushforward d)
      funext a
      rfl
    rw [show (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml))) =
        (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward (relabelDist φ d)
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) from
      funext (fun d => by rw [hreindex d])]
    set ζ : PosteriorLawSigned (supportSubtype (canonBoundary.{u} m l hle_ml)) :=
      (fun ψ => η (fun d => ψ (relabelDist φ d))) with hζdef
    have hζtan : PosteriorLawTangent ζ := by
      refine ⟨?_, ?_⟩
      · show η (fun d => (1:ℝ)) = 0
        exact hηtan.1
      · intro a
        show η (fun d => (relabelDist φ d) a) = 0
        have : (fun d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)) =>
            (relabelDist φ d) a) =
            (fun d => d (φ.symm a)) := by
          funext d
          rw [relabelDist_apply]
        rw [this]
        exact hηtan.2 _
    have hζatomic : PosteriorLawSigned.AtomicLinear ζ := by
      rw [hζdef]
      exact atomicLinear_relabelPullbackDirect φ hηatomic
    have hT_ml :=
      cardDefect_transportFor hhm hax hbranchData m l hl2 hlm
        ζ hζatomic hζtan
    have hLHS_eq :
        η (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward (relabelDist φ d)
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) =
        ζ (fun d' => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward d'
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) := rfl
    rw [hLHS_eq, hT_ml]
    congr 1
    change relabelPosteriorLawSigned φ η
        (hint.marginalValue F hV
          (canonBoundary.{u} m l hle_ml).restrictToSupport) =
      η (hint.marginalValue F hV
        (canonBoundary.{u} n l hle_ln).restrictToSupport)
    have hfaceML_rel :
        (canonBoundary.{u} m l hle_ml).restrictToSupport =
          relabelDist φ (canonBoundary.{u} n l hle_ln).restrictToSupport := by
      rw [canonBoundary_face_uniform m l hle_ml,
        canonBoundary_face_uniform n l hle_ln]
      ext a
      rw [Dist.uniform_apply, relabelDist_apply, Dist.uniform_apply]
      congr 1
      rw [Fintype.card_congr (canonBoundarySupportEquiv m l hle_ml),
        Fintype.card_congr (canonBoundarySupportEquiv n l hle_ln)]
    rw [hfaceML_rel]
    exact finalHM_affineLinearPart_relabel_atomic_eval hhm hax φ
      (canonBoundary.{u} n l hle_ln).restrictToSupport
      hfaceNL_fs η hηatomic hηtan
  have hfin :
      cardDefectFor hhm hax hbranchData n l *
        η (hint.marginalValue F hV
          (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefectFor hhm hax hbranchData n m *
          cardDefectFor hhm hax hbranchData m l) *
        η (hint.marginalValue F hV
          (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
    rw [hchain1, hbridge]
    ring
  have := mul_right_cancel₀ hηnz' (by linarith [hfin] : _)
  linarith [hfin, mul_right_cancel₀ hηnz'
    (show cardDefectFor hhm hax hbranchData n l *
        η (hint.marginalValue F hV
          (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefectFor hhm hax hbranchData n m *
          cardDefectFor hhm hax hbranchData m l) *
        η (hint.marginalValue F hV
          (canonBoundary.{u} n l hle_ln).restrictToSupport) from hfin)]

/-- Selected cardinal-gauge scale `t_n`. -/
noncomputable def cardScaleTFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n : ℕ) : ℝ :=
  if n = 2 then 1
  else if 3 ≤ n then cardDefectFor hhm hax hbranchData n 2
  else 1

/-- Selected embedding defect factors through the selected cardinal scale. -/
theorem cardDefect_eq_ratioFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n) :
    cardDefectFor hhm hax hbranchData n m =
      cardScaleTFor hhm hax hbranchData n /
        cardScaleTFor hhm hax hbranchData m := by
  have hn3 : 3 ≤ n := by omega
  have htn :
      cardScaleTFor hhm hax hbranchData n =
        cardDefectFor hhm hax hbranchData n 2 := by
    rw [cardScaleTFor]
    rw [if_neg (by omega), if_pos hn3]
  rcases eq_or_lt_of_le hm2 with hm2eq | hm2lt
  · subst hm2eq
    rw [htn]
    have htm : cardScaleTFor hhm hax hbranchData 2 = 1 := by
      rw [cardScaleTFor, if_pos rfl]
    rw [htm, div_one]
  · have hm3 : 3 ≤ m := by omega
    haveI : NeZero (2:ℕ) := ⟨by norm_num⟩
    have hcoc :=
      cardDefect_cocycleFor hhm hax hbranchData n m 2
        (le_refl 2) hm2lt hmn
    have htm :
        cardScaleTFor hhm hax hbranchData m =
          cardDefectFor hhm hax hbranchData m 2 := by
      rw [cardScaleTFor, if_neg (by omega), if_pos hm3]
    have hpos : 0 < cardDefectFor hhm hax hbranchData m 2 :=
      cardDefect_posFor hhm hax hbranchData m 2 (by norm_num) hm2lt
    rw [htn, htm]
    field_simp
    linarith [hcoc]

/-- Positivity of the selected cardinal-gauge scale. -/
theorem cardScaleT_posFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n : ℕ) :
    0 < cardScaleTFor hhm hax hbranchData n := by
  rw [cardScaleTFor]
  by_cases h2 : n = 2
  · rw [if_pos h2]
    exact one_pos
  · rw [if_neg h2]
    by_cases h3 : 3 ≤ n
    · rw [if_pos h3]
      exact cardDefect_posFor hhm hax hbranchData n 2
        (le_refl 2) (by omega)
    · rw [if_neg h3]
      exact one_pos

/-- Selected cardinal gauge depending only on the finite action cardinality. -/
noncomputable def cardinalGaugeFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    PositiveFaceScaleGauge.{u} where
  gauge := fun {A} _ _ _ _ =>
    cardScaleTFor hhm hax hbranchData (Fintype.card A)
  gauge_pos := fun {A} _ _ _ _ =>
    cardScaleT_posFor hhm hax hbranchData (Fintype.card A)

/-- The selected cardinal gauge is relabelling-invariant. -/
theorem cardinalGauge_gaugeRelFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (e : A ≃ B) (q : Dist A) :
    (cardinalGaugeFor hhm hax hbranchData).gauge
        (Relabeling.relabelDist e q) =
      (cardinalGaugeFor hhm hax hbranchData).gauge q := by
  show cardScaleTFor hhm hax hbranchData (Fintype.card B) =
    cardScaleTFor hhm hax hbranchData (Fintype.card A)
  rw [Fintype.card_congr e.symm]

/-- Selected cardinal-gauge scale-relabel equation. -/
theorem cardinalGauge_hrelFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (cardinalGaugeFor hhm hax hbranchData).gauge
        (Relabeling.relabelDist e q) *
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
          hhm hax hbranchData
        ).scale_factorization.scale (Relabeling.relabelDist e q) =
      (cardinalGaugeFor hhm hax hbranchData).gauge q *
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
          hhm hax hbranchData
        ).scale_factorization.scale q := by
  rw [cardinalGauge_gaugeRelFor hhm hax hbranchData e q,
    scaleRelabel_of_FinalHM_covarianceAtomicFor hhm hax hbranchData e q hq]

/-- **The cardinal gauge scale `t_n`.**  `t_n := cardDefect n 2` for `n ≥ 3`,
`t_2 := 1`.  By the cocycle `cardDefect n m = t_n / t_m`. -/
noncomputable def cardScaleT
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F) (n : ℕ) : ℝ :=
  if n = 2 then 1
  else if 3 ≤ n then cardDefect hhm hbranchData hax n 2
  else 1

/-- The embedding defect factors as `cardDefect n m = t_n / t_m` (the cocycle,
setting `ℓ = 2`). -/
theorem cardDefect_eq_ratio
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n) :
    cardDefect hhm hbranchData hax n m =
      cardScaleT hhm hbranchData hax n / cardScaleT hhm hbranchData hax m := by
  have hn3 : 3 ≤ n := by omega
  have htn : cardScaleT hhm hbranchData hax n = cardDefect hhm hbranchData hax n 2 := by
    rw [cardScaleT]; rw [if_neg (by omega), if_pos hn3]
  rcases eq_or_lt_of_le hm2 with hm2eq | hm2lt
  · subst hm2eq
    rw [htn]
    have htm : cardScaleT hhm hbranchData hax 2 = 1 := by rw [cardScaleT, if_pos rfl]
    rw [htm, div_one]
  · have hm3 : 3 ≤ m := by omega
    haveI : NeZero (2:ℕ) := ⟨by norm_num⟩
    have hcoc := cardDefect_cocycle hhm hbranchData hax n m 2 (le_refl 2) hm2lt hmn
    have htm : cardScaleT hhm hbranchData hax m = cardDefect hhm hbranchData hax m 2 := by
      rw [cardScaleT, if_neg (by omega), if_pos hm3]
    have hpos : 0 < cardDefect hhm hbranchData hax m 2 :=
      cardDefect_pos hhm hbranchData hax m 2 (by norm_num) hm2lt
    rw [htn, htm]
    field_simp
    linarith [hcoc]

/-- The faithful chain scale is positive for **every** prior (full-support via
`scale_pos`; boundary/singleton priors have `scale = branchPathCoeff q u = 1`). -/
theorem faithful_scale_pos
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 < (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale q := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
  show 0 < (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff q (Dist.uniform (A := A))
  rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
    ).branch_agg.branchCoeff q (Dist.uniform (A := A)) =
    branchCoeffFromTangentRepParts hpath
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
      hfaith.singleton_scale q (Dist.uniform (A := A)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  by_cases hqfs : q.FullSupport
  · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧ 0 < (Dist.uniform (A := A)) b
    · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A)) hqfs Dist.uniform_fullSupport hnd
    · rw [show hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 from by
        simp only [hpath, branchPathTangentScalarStructure_of_faithfulAssumptions,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hqfs, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hnd]]
      exact one_pos
  · rw [show hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 from by
      simp only [hpath, branchPathTangentScalarStructure_of_faithfulAssumptions,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
      rw [dif_neg hqfs]]
    exact one_pos

/-- The positive support of a relabelled prior is equivalent to the support of
the original, via the underlying bijection. -/
noncomputable def relabelSupportEquiv {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (r : Dist A) :
    supportSubtype (Relabeling.relabelDist e r) ≃ supportSubtype r where
  toFun b := ⟨e.symm b.1, by
    have := b.2
    rw [show (Relabeling.relabelDist e r) b.1 = r (e.symm b.1) from
      Relabeling.relabelDist_apply e r b.1] at this
    exact this⟩
  invFun a := ⟨e a.1, by
    rw [show (Relabeling.relabelDist e r) (e a.1) = r (e.symm (e a.1)) from
      Relabeling.relabelDist_apply e r (e a.1), Equiv.symm_apply_apply]
    exact a.2⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

/-- Support-restriction commutes with relabelling: `(relabel e r)|supp` is the
relabelling of `r|supp` along the induced support bijection. -/
theorem restrictToSupport_relabelDist {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (r : Dist A) :
    (Relabeling.relabelDist e r).restrictToSupport =
      Relabeling.relabelDist (relabelSupportEquiv e r).symm r.restrictToSupport := by
  ext b
  rw [Dist.restrictToSupport_apply, Relabeling.relabelDist_apply,
    Relabeling.relabelDist_apply, Dist.restrictToSupport_apply]
  simp [relabelSupportEquiv]

/-- The inclusion pushforward commutes with relabelling: pushing the
relabel-transported support-face distribution into `relabel e r` equals
relabelling the pushforward into `r`.  (The tangent-space naturality square for
the support inclusion.) -/
theorem push_relabel_comm {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (e : A ≃ B) (r : Dist A)
    [Nonempty (supportSubtype r)] [Nonempty (supportSubtype (Relabeling.relabelDist e r))]
    (d : Dist (supportSubtype r)) :
    Channel.actionPushforward
        (Relabeling.relabelDist (relabelSupportEquiv e r).symm d)
        (supportIncludeKernel (Relabeling.relabelDist e r)) =
      Relabeling.relabelDist e (Channel.actionPushforward d (supportIncludeKernel r)) := by
  ext b
  have hL : (Channel.actionPushforward (Relabeling.relabelDist (relabelSupportEquiv e r).symm d)
      (supportIncludeKernel (Relabeling.relabelDist e r))) b =
      if h : (Relabeling.relabelDist e r) b > 0 then
        (Relabeling.relabelDist (relabelSupportEquiv e r).symm d) ⟨b, h⟩ else 0 :=
    actionPushforward_supportIncludeKernel_apply (Relabeling.relabelDist e r) _ b
  have hR : (Channel.actionPushforward d (supportIncludeKernel r)) (e.symm b) =
      if h : r (e.symm b) > 0 then d ⟨e.symm b, h⟩ else 0 :=
    actionPushforward_supportIncludeKernel_apply r d (e.symm b)
  rw [show (Relabeling.relabelDist e (Channel.actionPushforward d (supportIncludeKernel r))) b =
      (Channel.actionPushforward d (supportIncludeKernel r)) (e.symm b) from
      Relabeling.relabelDist_apply e _ b]
  rw [hL, hR]
  by_cases hb : (Relabeling.relabelDist e r) b > 0
  · have hesymm : r (e.symm b) > 0 := by rw [← Relabeling.relabelDist_apply e r b]; exact hb
    rw [dif_pos hb, dif_pos hesymm, Relabeling.relabelDist_apply]
    congr 1
  · have hesymm : ¬ r (e.symm b) > 0 := by rw [← Relabeling.relabelDist_apply e r b]; exact hb
    rw [dif_neg hb, dif_neg hesymm]


/-! ### Relabel-invariance of the boundary embedding coefficient (R1 for the face). -/

noncomputable def relabelTangent {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (e : A ≃ B) (r : Dist A)
    [Nonempty (supportSubtype r)] [Nonempty (supportSubtype (Relabeling.relabelDist e r))]
    (η : PosteriorLawSigned (supportSubtype r)) :
    PosteriorLawSigned (supportSubtype (Relabeling.relabelDist e r)) :=
  fun ψ => η (fun d => ψ (Relabeling.relabelDist (relabelSupportEquiv e r).symm d))

/-- Relabelling a support-face signed posterior law preserves atomic-linearity. -/
noncomputable def atomicLinear_relabelTangent
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (r : Dist A)
    [Nonempty (supportSubtype r)]
    [Nonempty (supportSubtype (Relabeling.relabelDist e r))]
    {η : PosteriorLawSigned (supportSubtype r)}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (relabelTangent e r η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i =>
        Relabeling.relabelDist (relabelSupportEquiv e r).symm
          (hη.witness.point i)
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext ψ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        ψ (Relabeling.relabelDist (relabelSupportEquiv e r).symm
          (hη.witness.point i))) =
      η (fun d => ψ (Relabeling.relabelDist
        (relabelSupportEquiv e r).symm d))
    have h := congrFun hη.eval_eq
      (fun d => ψ (Relabeling.relabelDist
        (relabelSupportEquiv e r).symm d))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

theorem boundaryCoeff_relabel_of_FinalHM
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q r : Dist A)
    (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) =
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff q r := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
    with hfaith_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hint_def
  set hb := branchBoundaryFaceScale_of_faithfulAssumptions hfaith with hbdef
  have hrqn : (Relabeling.relabelDist e q).FullSupport := Relabeling.relabelDist_fullSupport e q hq
  have hrbn : ¬ (Relabeling.relabelDist e r).FullSupport := by
    intro hfs; apply hrb; intro a
    have := hfs (e a); rwa [Relabeling.relabelDist_apply, Equiv.symm_apply_apply] at this
  have hrnn : ∃ b : B, 0 < (Relabeling.relabelDist e r) b := by
    obtain ⟨a, ha⟩ := hrn
    exact ⟨e a, by rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact ha⟩
  have hrndn : ∃ a b : B, a ≠ b ∧ 0 < (Relabeling.relabelDist e r) a ∧ 0 < (Relabeling.relabelDist e r) b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hrnd
    exact ⟨e a, e b, fun h => hab (e.injective h),
      by rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact ha,
      by rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact hb'⟩
  have hrs_fs : (r.restrictToSupport).FullSupport := Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hrnd
    exact ⟨⟨a, ha⟩, ⟨b, hb'⟩, by intro h; exact hab (congrArg Subtype.val h),
      by rw [Dist.restrictToSupport_apply]; exact ha, by rw [Dist.restrictToSupport_apply]; exact hb'⟩
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hfaith.linear_part F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have hTqr := hbranchData.marginal_value.support_face_marginalValue_scalar
    F hax hV q r hq hrn hrnd hrb η hηtan
  set η' : PosteriorLawSigned (supportSubtype (Relabeling.relabelDist e r)) := relabelTangent e r η with hη'def
  have hη'tan : PosteriorLawTangent η' := by
    refine ⟨hηtan.1, ?_⟩
    intro a
    show η (fun d => (Relabeling.relabelDist (relabelSupportEquiv e r).symm d) a) = 0
    have : (fun d : Dist (supportSubtype r) =>
        (Relabeling.relabelDist (relabelSupportEquiv e r).symm d) a) =
        (fun d : Dist (supportSubtype r) => d ((relabelSupportEquiv e r) a)) := by
      funext d; rw [Relabeling.relabelDist_apply, Equiv.symm_symm]
    rw [this]; exact hηtan.2 _
  have hTqr' := hbranchData.marginal_value.support_face_marginalValue_scalar
    F hax hV (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) hrqn hrnn hrndn hrbn η' hη'tan
  have hLHS : η' (fun d' => hint.marginalValue F hV (Relabeling.relabelDist e q)
        (Channel.actionPushforward d' (supportIncludeKernel (Relabeling.relabelDist e r)))) =
      η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel r))) := by
    let θ := pushSignedIncl r η
    have hθatomic : PosteriorLawSigned.AtomicLinear θ :=
      atomicLinear_pushSignedIncl r hηatomic
    have hθtan : PosteriorLawTangent θ :=
      pushSignedIncl_tangent r hηatomic hηtan
    have hnatural :=
      finalHM_affineLinearPart_relabel_atomic_eval hhm hax
        e q hq θ hθatomic hθtan
    calc
      η' (fun d' => hint.marginalValue F hV
          (Relabeling.relabelDist e q)
          (Channel.actionPushforward d'
            (supportIncludeKernel (Relabeling.relabelDist e r)))) =
          relabelPosteriorLawSigned e θ
            (hint.marginalValue F hV
              (Relabeling.relabelDist e q)) := by
            change η (fun d => hint.marginalValue F hV
              (Relabeling.relabelDist e q)
              (Channel.actionPushforward
                (Relabeling.relabelDist
                  (relabelSupportEquiv e r).symm d)
                (supportIncludeKernel
                  (Relabeling.relabelDist e r)))) =
              η (fun d => hint.marginalValue F hV
                (Relabeling.relabelDist e q)
                (Relabeling.relabelDist e
                  (Channel.actionPushforward d
                    (supportIncludeKernel r))))
            congr 1
            funext d
            rw [push_relabel_comm e r d]
      _ = θ (hint.marginalValue F hV q) := hnatural
      _ = η (fun d => hint.marginalValue F hV q
          (Channel.actionPushforward d (supportIncludeKernel r))) := rfl
  have hRHS : η' (hint.marginalValue F hV (Relabeling.relabelDist e r).restrictToSupport) =
      η (hint.marginalValue F hV r.restrictToSupport) := by
    change relabelPosteriorLawSigned
        (relabelSupportEquiv e r).symm η
        (hint.marginalValue F hV
          (Relabeling.relabelDist e r).restrictToSupport) =
      η (hint.marginalValue F hV r.restrictToSupport)
    have hface : (Relabeling.relabelDist e r).restrictToSupport =
        Relabeling.relabelDist (relabelSupportEquiv e r).symm r.restrictToSupport :=
      restrictToSupport_relabelDist e r
    rw [hface]
    exact finalHM_affineLinearPart_relabel_atomic_eval hhm hax
      (relabelSupportEquiv e r).symm r.restrictToSupport
      hrs_fs η hηatomic hηtan
  rw [hLHS, hRHS] at hTqr'
  have hnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  -- hTqr'  : bc (relabel q)(relabel r) · η(mV(r|supp)) = ... wait it equals the LHS transport = η(...)
  -- both hTqr and hTqr' now equal η(fun d => mV q (push_r d)); so their boundaryCoeff·L are equal
  -- hTqr' : η(fun d => mV q (push_r d)) = bc(relabel q)(relabel r)·η(mV(r|supp))
  -- hTqr  : η(fun d => mV q (push_r d)) = bc q r·η(mV(r|supp))
  have hcomb : (branchBoundaryFaceScale_of_faithfulAssumptions hfaith).boundaryCoeff
        (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) * η (hint.marginalValue F hV r.restrictToSupport) =
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith).boundaryCoeff q r *
        η (hint.marginalValue F hV r.restrictToSupport) :=
    hTqr'.symm.trans hTqr
  exact mul_right_cancel₀ hnz hcomb

/-- Selected relabel-invariance of the boundary embedding coefficient. -/
theorem boundaryCoeff_relabel_of_FinalHMFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q r : Dist A)
    (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
    ).boundaryCoeff (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) =
    (boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
    ).boundaryCoeff q r := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hb := boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  have hrqn : (Relabeling.relabelDist e q).FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  have hrbn : ¬ (Relabeling.relabelDist e r).FullSupport := by
    intro hfs
    apply hrb
    intro a
    have := hfs (e a)
    rwa [Relabeling.relabelDist_apply, Equiv.symm_apply_apply] at this
  have hrnn : ∃ b : B, 0 < (Relabeling.relabelDist e r) b := by
    obtain ⟨a, ha⟩ := hrn
    exact ⟨e a, by
      rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]
      exact ha⟩
  have hrndn :
      ∃ a b : B, a ≠ b ∧ 0 < (Relabeling.relabelDist e r) a ∧
        0 < (Relabeling.relabelDist e r) b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hrnd
    exact ⟨e a, e b, fun h => hab (e.injective h),
      by rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact ha,
      by rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact hb'⟩
  have hrs_fs : (r.restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hrnd
    exact ⟨⟨a, ha⟩, ⟨b, hb'⟩,
      by intro h; exact hab (congrArg Subtype.val h),
      by rw [Dist.restrictToSupport_apply]; exact ha,
      by rw [Dist.restrictToSupport_apply]; exact hb'⟩
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have hTqr :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := A) q r hq hrn hrnd hrb η hηatomic hηtan
  set η' : PosteriorLawSigned (supportSubtype (Relabeling.relabelDist e r)) :=
    relabelTangent e r η with hη'def
  have hη'tan : PosteriorLawTangent η' := by
    refine ⟨hηtan.1, ?_⟩
    intro a
    show η (fun d => (Relabeling.relabelDist
      (relabelSupportEquiv e r).symm d) a) = 0
    have : (fun d : Dist (supportSubtype r) =>
        (Relabeling.relabelDist (relabelSupportEquiv e r).symm d) a) =
        (fun d : Dist (supportSubtype r) =>
          d ((relabelSupportEquiv e r) a)) := by
      funext d
      rw [Relabeling.relabelDist_apply, Equiv.symm_symm]
    rw [this]
    exact hηtan.2 _
  have hη'atomic : PosteriorLawSigned.AtomicLinear η' := by
    rw [hη'def]
    exact atomicLinear_relabelTangent e r hηatomic
  have hTqr' :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := B) (Relabeling.relabelDist e q)
      (Relabeling.relabelDist e r) hrqn hrnn hrndn hrbn
      η' hη'atomic hη'tan
  have hLHS :
      η' (fun d' => hint.marginalValue F hV (Relabeling.relabelDist e q)
        (Channel.actionPushforward d'
          (supportIncludeKernel (Relabeling.relabelDist e r)))) =
      η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel r))) := by
    let θ := pushSignedIncl r η
    have hθatomic : PosteriorLawSigned.AtomicLinear θ :=
      atomicLinear_pushSignedIncl r hηatomic
    have hθtan : PosteriorLawTangent θ :=
      pushSignedIncl_tangent r hηatomic hηtan
    have hnatural :=
      finalHM_affineLinearPart_relabel_atomic_eval hhm hax
        e q hq θ hθatomic hθtan
    calc
      η' (fun d' => hint.marginalValue F hV
          (Relabeling.relabelDist e q)
          (Channel.actionPushforward d'
            (supportIncludeKernel (Relabeling.relabelDist e r)))) =
          relabelPosteriorLawSigned e θ
            (hint.marginalValue F hV
              (Relabeling.relabelDist e q)) := by
            change η (fun d => hint.marginalValue F hV
              (Relabeling.relabelDist e q)
              (Channel.actionPushforward
                (Relabeling.relabelDist
                  (relabelSupportEquiv e r).symm d)
                (supportIncludeKernel
                  (Relabeling.relabelDist e r)))) =
              η (fun d => hint.marginalValue F hV
                (Relabeling.relabelDist e q)
                (Relabeling.relabelDist e
                  (Channel.actionPushforward d
                    (supportIncludeKernel r))))
            congr 1
            funext d
            rw [push_relabel_comm e r d]
      _ = θ (hint.marginalValue F hV q) := hnatural
      _ = η (fun d => hint.marginalValue F hV q
          (Channel.actionPushforward d (supportIncludeKernel r))) := rfl
  have hRHS :
      η' (hint.marginalValue F hV
        (Relabeling.relabelDist e r).restrictToSupport) =
      η (hint.marginalValue F hV r.restrictToSupport) := by
    change relabelPosteriorLawSigned
        (relabelSupportEquiv e r).symm η
        (hint.marginalValue F hV
          (Relabeling.relabelDist e r).restrictToSupport) =
      η (hint.marginalValue F hV r.restrictToSupport)
    have hface : (Relabeling.relabelDist e r).restrictToSupport =
        Relabeling.relabelDist (relabelSupportEquiv e r).symm
          r.restrictToSupport :=
      restrictToSupport_relabelDist e r
    rw [hface]
    exact finalHM_affineLinearPart_relabel_atomic_eval hhm hax
      (relabelSupportEquiv e r).symm r.restrictToSupport
      hrs_fs η hηatomic hηtan
  rw [hLHS, hRHS] at hTqr'
  have hnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  have hcomb :
      hb.boundaryCoeff (Relabeling.relabelDist e q)
          (Relabeling.relabelDist e r) *
          η (hint.marginalValue F hV r.restrictToSupport) =
        hb.boundaryCoeff q r *
          η (hint.marginalValue F hV r.restrictToSupport) :=
    hTqr'.symm.trans hTqr
  exact mul_right_cancel₀ hnz hcomb

/-! ### Tier-C foundations: alignment equivalence and within-face independence. -/

/-- Alignment equivalence: a bijection `A ≃ canonType (card A)` sending the
positive support of `r` to the first `card (supp r)` canonical indices.  Used to
reduce the embedding defect at an arbitrary boundary prior to the canonical
`cardDefect`. -/
noncomputable def alignEquiv {A : Type u} [Fintype A] [DecidableEq A] (r : Dist A) :
    A ≃ canonType.{u} (Fintype.card A) := by
  classical
  have hcard : Fintype.card (supportSubtype r) + Fintype.card {a // ¬ (r a > 0)} =
      Fintype.card A := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (Equiv.sumCompl (fun a => r a > 0))
  exact
    ((Equiv.sumCompl (fun a => r a > 0)).symm.trans
      ((Fintype.equivFin (supportSubtype r)).sumCongr (Fintype.equivFin {a // ¬ (r a > 0)}))).trans
      ((finSumFinEquiv).trans ((Fin.castOrderIso hcard).toEquiv.trans Equiv.ulift.symm))

/-- Support elements map below `card (supp r)` under `alignEquiv`. -/
theorem alignEquiv_lt_of_pos {A : Type u} [Fintype A] [DecidableEq A] (r : Dist A) (a : A)
    (ha : r a > 0) :
    ((alignEquiv r a).down : ℕ) < Fintype.card (supportSubtype r) := by
  classical
  have hsc : (Equiv.sumCompl (fun x => r x > 0)).symm a = Sum.inl ⟨a, ha⟩ := by
    rw [Equiv.symm_apply_eq]; rfl
  have hval : ((alignEquiv r a).down : ℕ) =
      ((Fintype.equivFin (supportSubtype r) ⟨a, ha⟩ :
        Fin (Fintype.card (supportSubtype r))) : ℕ) := by
    simp only [alignEquiv, Equiv.trans_apply, hsc]
    simp [Fin.castOrderIso]
    rfl
  rw [hval]
  exact (Fintype.equivFin (supportSubtype r) ⟨a, ha⟩).isLt

/-- Non-support elements map at or above `card (supp r)` under `alignEquiv`. -/
theorem alignEquiv_ge_of_not_pos {A : Type u} [Fintype A] [DecidableEq A] (r : Dist A) (a : A)
    (ha : ¬ (r a > 0)) :
    Fintype.card (supportSubtype r) ≤ ((alignEquiv r a).down : ℕ) := by
  classical
  have hsc : (Equiv.sumCompl (fun x => r x > 0)).symm a = Sum.inr ⟨a, ha⟩ := by
    rw [Equiv.symm_apply_eq]; rfl
  have hval : ((alignEquiv r a).down : ℕ) =
      Fintype.card (supportSubtype r) +
        ((Fintype.equivFin {a // ¬ (r a > 0)} ⟨a, ha⟩ :
          Fin (Fintype.card {a // ¬ (r a > 0)})) : ℕ) := by
    simp only [alignEquiv, Equiv.trans_apply, hsc]
    simp [Fin.castOrderIso]
    rfl
  rw [hval]; omega

/-- Same-support equivalence between the positive-support subtypes of two priors
on the same type sharing the same support set. -/
def sameSupportEquiv {C : Type u} [Fintype C] [DecidableEq C] (ρ σ : Dist C)
    (h : ∀ c, ρ c > 0 ↔ σ c > 0) : supportSubtype ρ ≃ supportSubtype σ where
  toFun a := ⟨a.1, (h a.1).mp a.2⟩
  invFun b := ⟨b.1, (h b.1).mpr b.2⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; rfl

/-- Inclusion pushforwards agree across a same-support equivalence. -/
theorem push_sameSupport_comm {C : Type u} [Fintype C] [DecidableEq C] (ρ σ : Dist C)
    (h : ∀ c, ρ c > 0 ↔ σ c > 0) (d : Dist (supportSubtype ρ)) :
    Channel.actionPushforward d (supportIncludeKernel ρ) =
      Channel.actionPushforward (Relabeling.relabelDist (sameSupportEquiv ρ σ h) d)
        (supportIncludeKernel σ) := by
  classical
  ext c
  have hL : (Channel.actionPushforward d (supportIncludeKernel ρ)) c =
      if hc : ρ c > 0 then d ⟨c, hc⟩ else 0 :=
    actionPushforward_supportIncludeKernel_apply ρ d c
  have hR : (Channel.actionPushforward (Relabeling.relabelDist (sameSupportEquiv ρ σ h) d)
        (supportIncludeKernel σ)) c =
      if hc : σ c > 0 then (Relabeling.relabelDist (sameSupportEquiv ρ σ h) d) ⟨c, hc⟩ else 0 :=
    actionPushforward_supportIncludeKernel_apply σ _ c
  rw [hL, hR]
  by_cases hc : ρ c > 0
  · have hcσ : σ c > 0 := (h c).mp hc
    rw [dif_pos hc, dif_pos hcσ, Relabeling.relabelDist_apply]
    congr 1
  · have hcσ : ¬ σ c > 0 := fun hcσ => hc ((h c).mpr hcσ)
    rw [dif_neg hc, dif_neg hcσ]

/-- Pullback of a signed posterior law along a `Dist`-relabelling `E : S ≃ T`. -/
noncomputable def relabelPullback {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T] (E : S ≃ T)
    (η : PosteriorLawSigned S) : PosteriorLawSigned T :=
  fun ψ => η (fun d => ψ (Relabeling.relabelDist E d))

/-- The pullback preserves the atomic-linear witness. -/
noncomputable def atomicLinear_relabelPullback {S T : Type u}
    [Fintype S] [DecidableEq S] [Nonempty S] [Fintype T] [DecidableEq T] [Nonempty T]
    (E : S ≃ T) {η : PosteriorLawSigned S} (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (relabelPullback E η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i => Relabeling.relabelDist E (hη.witness.point i)
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext ψ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        ψ (Relabeling.relabelDist E (hη.witness.point i))) =
      η (fun d => ψ (Relabeling.relabelDist E d))
    have h := congrFun hη.eval_eq (fun d => ψ (Relabeling.relabelDist E d))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- The pullback preserves tangency. -/
theorem relabelPullback_tangent {S T : Type u}
    [Fintype S] [DecidableEq S] [Nonempty S] [Fintype T] [DecidableEq T] [Nonempty T]
    (E : S ≃ T) {η : PosteriorLawSigned S} (htan : PosteriorLawTangent η) :
    PosteriorLawTangent (relabelPullback E η) := by
  refine ⟨?_, ?_⟩
  · show η (fun _ => (1:ℝ)) = 0
    exact htan.1
  · intro t
    show η (fun d => (Relabeling.relabelDist E d) t) = 0
    have heq : (fun d : Dist S => (Relabeling.relabelDist E d) t) =
        (fun d : Dist S => d (E.symm t)) := by
      funext d; rw [Relabeling.relabelDist_apply]
    rw [heq]; exact htan.2 (E.symm t)

/-- **Face scalar relation.**  For a tangent `η` on the positive support of `r`,
the intrinsic face marginal value against `mV(r|supp)` is `scale(r|supp)` times
the value against `mV(uniform)` on the support face. -/
theorem face_scalar_relation
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    {C : Type u} [Fintype C] [DecidableEq C] [Nonempty C] (r : Dist C)
    [Nonempty (supportSubtype r)]
    (hrnd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b)
    (η : PosteriorLawSigned (supportSubtype r))
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax) r.restrictToSupport) =
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport *
      η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        (Dist.uniform (A := supportSubtype r))) := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
    with hfaith_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hint_def
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
    with hpath_def
  have hrs_fs : (r.restrictToSupport).FullSupport := Dist.restrictToSupport_fullSupport r
  have hscale_eq : (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).scale_factorization.scale r.restrictToSupport =
      hpath.branchPathCoeff r.restrictToSupport (Dist.uniform (A := supportSubtype r)) := by
    show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).branch_agg.branchCoeff r.restrictToSupport (Dist.uniform (A := supportSubtype r)) = _
    rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff r.restrictToSupport (Dist.uniform (A := supportSubtype r)) =
      branchCoeffFromTangentRepParts hpath
        (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
        hfaith.singleton_scale r.restrictToSupport (Dist.uniform (A := supportSubtype r)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  rw [hscale_eq]
  have hndU : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < (Dist.uniform (A := supportSubtype r)) a ∧
      0 < (Dist.uniform (A := supportSubtype r)) b := by
    obtain ⟨a, b, hab, _, _⟩ := hrnd
    exact ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  have hrel := hpath.linear_part_scalar_relation_on_tangent
    r.restrictToSupport (Dist.uniform (A := supportSubtype r)) hrs_fs Dist.uniform_fullSupport
    hndU η hηatomic hηtan
  show hfaith.linear_part.linearPart F hV r.restrictToSupport η = _
  rw [hrel]
  rfl

/-- Selected face scalar relation. -/
theorem face_scalar_relationFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {C : Type u} [Fintype C] [DecidableEq C] [Nonempty C] (r : Dist C)
    [Nonempty (supportSubtype r)]
    (hrnd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b)
    (η : PosteriorLawSigned (supportSubtype r))
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax) r.restrictToSupport) =
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale r.restrictToSupport *
      η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        (Dist.uniform (A := supportSubtype r))) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  have hrs_fs : (r.restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hscale_eq :
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale r.restrictToSupport =
        hpath.branchPathCoeff r.restrictToSupport
          (Dist.uniform (A := supportSubtype r)) := by
    change selectedAtomicBranchScaleFor hhm hax hbranchData
        r.restrictToSupport =
      hpath.branchPathCoeff r.restrictToSupport
        (Dist.uniform (A := supportSubtype r))
    exact selectedAtomicBranchScaleFor_fullSupport
      hhm hax hbranchData r.restrictToSupport hrs_fs
  rw [hscale_eq]
  have hndU : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < (Dist.uniform (A := supportSubtype r)) a ∧
      0 < (Dist.uniform (A := supportSubtype r)) b := by
    obtain ⟨a, b, hab, _, _⟩ := hrnd
    exact ⟨a, b, hab, Dist.uniform_fullSupport a,
      Dist.uniform_fullSupport b⟩
  have hrel := hpath.linear_part_scalar_relation_on_tangent
    r.restrictToSupport (Dist.uniform (A := supportSubtype r))
    hrs_fs Dist.uniform_fullSupport hndU η hηatomic hηtan
  show hlin.linearPart F hV r.restrictToSupport η = _
  rw [hrel]
  rfl

/-- **Within-face independence of the scaled embedding defect.**  For two boundary
priors `ρ, σ` on the same type with the *same positive support set*, the products
`boundaryCoeff q · scale (·|supp)` agree.  Hence `boundaryCoeff q r · scale (r|supp)`
depends on `r` only through its support set, not its within-face values.  Proof:
the support-face marginal-value transport pins each `boundaryCoeff` against a
tangent; the same-support inclusion pushforward identifies the two ambient
transports; the face scalar relation converts each intrinsic face value to a
common uniform value scaled by `scale (·|supp)`; cancel the shared nonzero tangent
value. -/
theorem boundaryCoeff_scale_within_face
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : PureTraceConditions F)
    {C : Type u} [Fintype C] [DecidableEq C] [Nonempty C]
    (q ρ σ : Dist C) (hq : q.FullSupport)
    (hsupp : ∀ c, ρ c > 0 ↔ σ c > 0)
    (hρn : ∃ a : C, 0 < ρ a)
    (hρnd : ∃ a b : C, a ≠ b ∧ 0 < ρ a ∧ 0 < ρ b)
    (hρb : ¬ ρ.FullSupport) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff q ρ *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale ρ.restrictToSupport =
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff q σ *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale σ.restrictToSupport := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
    with hfaith_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hint_def
  set hb := branchBoundaryFaceScale_of_faithfulAssumptions hfaith with hbdef
  -- σ boundary data from same-support
  have hσn : ∃ a : C, 0 < σ a := by obtain ⟨a, ha⟩ := hρn; exact ⟨a, (hsupp a).mp ha⟩
  have hσnd : ∃ a b : C, a ≠ b ∧ 0 < σ a ∧ 0 < σ b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hρnd; exact ⟨a, b, hab, (hsupp a).mp ha, (hsupp b).mp hb'⟩
  have hσb : ¬ σ.FullSupport := by
    intro hfs; apply hρb; intro c; exact (hsupp c).mpr (hfs c)
  -- face nondegeneracy
  have hρs_nd : ∃ a b : supportSubtype ρ, a ≠ b ∧
      0 < ρ.restrictToSupport a ∧ 0 < ρ.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hρnd
    exact ⟨⟨a, ha⟩, ⟨b, hb'⟩, by intro h; exact hab (congrArg Subtype.val h),
      by rw [Dist.restrictToSupport_apply]; exact ha, by rw [Dist.restrictToSupport_apply]; exact hb'⟩
  -- tangent η on suppSub ρ nonzero on mV(ρ|supp)
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hfaith.linear_part F hax hV
      ρ.restrictToSupport ρ.restrictToSupport (Dist.restrictToSupport_fullSupport ρ)
      (Dist.restrictToSupport_fullSupport ρ) hρs_nd
  -- transport at ρ:  η(fun d => mV q (push_ρ d)) = bc q ρ · η(mV ρ|supp)
  have hTρ :=
    hbranchData.marginal_value.support_face_marginalValue_scalar
      F hax hV q ρ hq hρn hρnd hρb η hηtan
  -- E : suppSub ρ ≃ suppSub σ
  set E := sameSupportEquiv ρ σ hsupp with hEdef
  -- transported tangent η' on suppSub σ (pullback along E⁻¹? no: relabelPullback E)
  set η' : PosteriorLawSigned (supportSubtype σ) := relabelPullback E η with hη'def
  have hη'atomic : PosteriorLawSigned.AtomicLinear η' := atomicLinear_relabelPullback E hηatomic
  have hη'tan : PosteriorLawTangent η' := relabelPullback_tangent E hηtan
  -- transport at σ:  η'(fun d' => mV q (push_σ d')) = bc q σ · η'(mV σ|supp)
  have hTσ :=
    hbranchData.marginal_value.support_face_marginalValue_scalar
      F hax hV q σ hq hσn hσnd hσb η' hη'tan
  -- LHS equality via push_sameSupport_comm:  η'(fun d' => mV q (push_σ d')) = η(fun d => mV q (push_ρ d))
  have hLHS : η' (fun d' => hint.marginalValue F hV q
        (Channel.actionPushforward d' (supportIncludeKernel σ))) =
      η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel ρ))) := by
    show η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward (Relabeling.relabelDist E d) (supportIncludeKernel σ))) = _
    congr 1
    funext d
    have := push_sameSupport_comm ρ σ hsupp d
    rw [← this]
  -- face scalar relation for ρ and σ
  have hfρ := face_scalar_relation hhm hbranchData hax ρ hρs_nd η hηatomic hηtan
  have hσs_nd : ∃ a b : supportSubtype σ, a ≠ b ∧
      0 < σ.restrictToSupport a ∧ 0 < σ.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hσnd
    exact ⟨⟨a, ha⟩, ⟨b, hb'⟩, by intro h; exact hab (congrArg Subtype.val h),
      by rw [Dist.restrictToSupport_apply]; exact ha, by rw [Dist.restrictToSupport_apply]; exact hb'⟩
  have hfσ := face_scalar_relation hhm hbranchData hax σ hσs_nd η' hη'atomic hη'tan
  -- Equality on the uniform-prior atomic tangent, plus uniform preservation.
  have huniσ : Relabeling.relabelDist E (Dist.uniform (A := supportSubtype ρ)) =
      Dist.uniform (A := supportSubtype σ) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply, Fintype.card_congr E]
  have huninz : η' (hint.marginalValue F hV (Dist.uniform (A := supportSubtype σ))) =
      η (hint.marginalValue F hV (Dist.uniform (A := supportSubtype ρ))) := by
    change relabelPosteriorLawSigned E η
        (hint.marginalValue F hV
          (Dist.uniform (A := supportSubtype σ))) =
      η (hint.marginalValue F hV
        (Dist.uniform (A := supportSubtype ρ)))
    rw [← huniσ]
    exact finalHM_affineLinearPart_relabel_atomic_eval hhm hax E
      (Dist.uniform (A := supportSubtype ρ))
      Dist.uniform_fullSupport η hηatomic hηtan
  -- assemble:  bc q ρ · η(mV ρ|supp) = η(push_ρ) = η'(push_σ) = bc q σ · η'(mV σ|supp)
  -- align defeq: transport boundaryCoeff = hb.boundaryCoeff
  have hTρ' : η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel ρ))) =
      hb.boundaryCoeff q ρ * η (hint.marginalValue F hV ρ.restrictToSupport) := hTρ
  have hTσ' : η' (fun d' => hint.marginalValue F hV q
        (Channel.actionPushforward d' (supportIncludeKernel σ))) =
      hb.boundaryCoeff q σ * η' (hint.marginalValue F hV σ.restrictToSupport) := hTσ
  have hchain : hb.boundaryCoeff q ρ * η (hint.marginalValue F hV ρ.restrictToSupport) =
      hb.boundaryCoeff q σ * η' (hint.marginalValue F hV σ.restrictToSupport) := by
    rw [← hTρ', ← hLHS, hTσ']
  set X := η (hint.marginalValue F hV (Dist.uniform (A := supportSubtype ρ))) with hXdef
  set sρ := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).scale_factorization.scale ρ.restrictToSupport with hsρdef
  set sσ := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).scale_factorization.scale σ.restrictToSupport with hsσdef
  -- hfρ : η(mV ρ|supp) = sρ · X ; hfσ : η'(mV σ|supp) = sσ · η'(mVuni_σ) ; huninz : η'(mVuni_σ)=X
  have hfρ' : η (hint.marginalValue F hV ρ.restrictToSupport) = sρ * X := hfρ
  have hfσ' : η' (hint.marginalValue F hV σ.restrictToSupport) = sσ * X := by
    rw [hfσ, huninz]
  have hXnz : X ≠ 0 := by
    intro hX0
    apply hηnz
    rw [show hfaith.linear_part.linearPart F hV ρ.restrictToSupport η =
      η (hint.marginalValue F hV ρ.restrictToSupport) from rfl, hfρ', hX0, mul_zero]
  have hexp : hb.boundaryCoeff q ρ * sρ * X = hb.boundaryCoeff q σ * sσ * X := by
    rw [hfρ', hfσ'] at hchain; linarith [hchain]
  exact mul_right_cancel₀ hXnz hexp

/-- Selected within-face independence of the scaled embedding defect. -/
theorem boundaryCoeff_scale_within_faceFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {C : Type u} [Fintype C] [DecidableEq C] [Nonempty C]
    (q ρ σ : Dist C) (hq : q.FullSupport)
    (hsupp : ∀ c, ρ c > 0 ↔ σ c > 0)
    (hρn : ∃ a : C, 0 < ρ a)
    (hρnd : ∃ a b : C, a ≠ b ∧ 0 < ρ a ∧ 0 < ρ b)
    (hρb : ¬ ρ.FullSupport) :
    (boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
    ).boundaryCoeff q ρ *
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale ρ.restrictToSupport =
    (boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
    ).boundaryCoeff q σ *
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale σ.restrictToSupport := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hb := boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  have hσn : ∃ a : C, 0 < σ a := by
    obtain ⟨a, ha⟩ := hρn
    exact ⟨a, (hsupp a).mp ha⟩
  have hσnd : ∃ a b : C, a ≠ b ∧ 0 < σ a ∧ 0 < σ b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hρnd
    exact ⟨a, b, hab, (hsupp a).mp ha, (hsupp b).mp hb'⟩
  have hσb : ¬ σ.FullSupport := by
    intro hfs
    apply hρb
    intro c
    exact (hsupp c).mpr (hfs c)
  have hρs_nd : ∃ a b : supportSubtype ρ, a ≠ b ∧
      0 < ρ.restrictToSupport a ∧ 0 < ρ.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hρnd
    exact ⟨⟨a, ha⟩, ⟨b, hb'⟩,
      by intro h; exact hab (congrArg Subtype.val h),
      by rw [Dist.restrictToSupport_apply]; exact ha,
      by rw [Dist.restrictToSupport_apply]; exact hb'⟩
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      ρ.restrictToSupport ρ.restrictToSupport
      (Dist.restrictToSupport_fullSupport ρ)
      (Dist.restrictToSupport_fullSupport ρ) hρs_nd
  have hTρ :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := C) q ρ hq hρn hρnd hρb η hηatomic hηtan
  set E := sameSupportEquiv ρ σ hsupp with hEdef
  set η' : PosteriorLawSigned (supportSubtype σ) :=
    relabelPullback E η with hη'def
  have hη'atomic : PosteriorLawSigned.AtomicLinear η' :=
    atomicLinear_relabelPullback E hηatomic
  have hη'tan : PosteriorLawTangent η' :=
    relabelPullback_tangent E hηtan
  have hTσ :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := C) q σ hq hσn hσnd hσb η' hη'atomic hη'tan
  have hLHS : η' (fun d' => hint.marginalValue F hV q
        (Channel.actionPushforward d' (supportIncludeKernel σ))) =
      η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel ρ))) := by
    show η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward (Relabeling.relabelDist E d)
          (supportIncludeKernel σ))) = _
    congr 1
    funext d
    have := push_sameSupport_comm ρ σ hsupp d
    rw [← this]
  have hfρ := face_scalar_relationFor hhm hax hbranchData
    ρ hρs_nd η hηatomic hηtan
  have hσs_nd : ∃ a b : supportSubtype σ, a ≠ b ∧
      0 < σ.restrictToSupport a ∧ 0 < σ.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hσnd
    exact ⟨⟨a, ha⟩, ⟨b, hb'⟩,
      by intro h; exact hab (congrArg Subtype.val h),
      by rw [Dist.restrictToSupport_apply]; exact ha,
      by rw [Dist.restrictToSupport_apply]; exact hb'⟩
  have hfσ := face_scalar_relationFor hhm hax hbranchData
    σ hσs_nd η' hη'atomic hη'tan
  have huniσ : Relabeling.relabelDist E
        (Dist.uniform (A := supportSubtype ρ)) =
      Dist.uniform (A := supportSubtype σ) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply,
      Dist.uniform_apply, Fintype.card_congr E]
  have huninz :
      η' (hint.marginalValue F hV
        (Dist.uniform (A := supportSubtype σ))) =
      η (hint.marginalValue F hV
        (Dist.uniform (A := supportSubtype ρ))) := by
    change relabelPosteriorLawSigned E η
        (hint.marginalValue F hV
          (Dist.uniform (A := supportSubtype σ))) =
      η (hint.marginalValue F hV
        (Dist.uniform (A := supportSubtype ρ)))
    rw [← huniσ]
    exact finalHM_affineLinearPart_relabel_atomic_eval hhm hax E
      (Dist.uniform (A := supportSubtype ρ))
      Dist.uniform_fullSupport η hηatomic hηtan
  have hTρ' : η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel ρ))) =
      hb.boundaryCoeff q ρ *
        η (hint.marginalValue F hV ρ.restrictToSupport) := hTρ
  have hTσ' : η' (fun d' => hint.marginalValue F hV q
        (Channel.actionPushforward d' (supportIncludeKernel σ))) =
      hb.boundaryCoeff q σ *
        η' (hint.marginalValue F hV σ.restrictToSupport) := hTσ
  have hchain :
      hb.boundaryCoeff q ρ *
          η (hint.marginalValue F hV ρ.restrictToSupport) =
        hb.boundaryCoeff q σ *
          η' (hint.marginalValue F hV σ.restrictToSupport) := by
    rw [← hTρ', ← hLHS, hTσ']
  set X := η (hint.marginalValue F hV
    (Dist.uniform (A := supportSubtype ρ))) with hXdef
  set sρ :=
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale ρ.restrictToSupport with hsρdef
  set sσ :=
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale σ.restrictToSupport with hsσdef
  have hfρ' : η (hint.marginalValue F hV ρ.restrictToSupport) = sρ * X := hfρ
  have hfσ' : η' (hint.marginalValue F hV σ.restrictToSupport) = sσ * X := by
    rw [hfσ, huninz]
  have hXnz : X ≠ 0 := by
    intro hX0
    apply hηnz
    rw [show hlin.linearPart F hV ρ.restrictToSupport η =
      η (hint.marginalValue F hV ρ.restrictToSupport) from rfl,
      hfρ', hX0, mul_zero]
  have hexp : hb.boundaryCoeff q ρ * sρ * X =
      hb.boundaryCoeff q σ * sσ * X := by
    rw [hfρ', hfσ'] at hchain
    linarith [hchain]
  exact mul_right_cancel₀ hXnz hexp

end TraceableAgency
