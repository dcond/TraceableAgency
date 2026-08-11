/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence.BranchResult

namespace TraceableAgency

universe u

/-!
## Coherent relabelling and face scales

The next named paper result is pre-universal: it coherently chooses the
prior-dependent chain scales across finite action alphabets and support faces.
It is weaker than `ScaleCoherenceStructure`, which also contains the later
universal-scale collapse.  The following interfaces split the relabelling and
support-face scale normalizations away from that later theorem.
-/

/-- Chain-scale relabelling invariance for a fixed faithful branch-chain
package.

This is the scale-level analogue of exact value relabelling: after choosing the
chain scales, relabelling the action alphabet by a bijection does not change
the numerical scale. -/
structure FiniteChainScaleRelabelingAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F) : Prop where
  scale_relabel_eq :
    ∀ {A B : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
      hbranch.scale_factorization.scale (Relabeling.relabelDist e q) =
        hbranch.scale_factorization.scale q

/-- Canonical support-face scale compatibility for a fixed faithful
branch-chain package.

The paper states the face-scale equation for arbitrary injections.  Current
Lean support-restriction infrastructure has a canonical support-face inclusion
`supportSubtype r -> A`; arbitrary injections can be reduced to this form by
relabeling.  This interface records the canonical support-face equation. -/
structure FiniteSupportFaceScaleAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F) : Prop where
  support_face_scale :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      hbranch.branch_agg.branchCoeff q r =
        hbranch.scale_factorization.scale q /
          hbranch.scale_factorization.scale r.restrictToSupport

/-- Faithful output package for the named result "Coherent relabelling and
face scales".

It extends the faithful branch/cocycle/chain package with scale relabelling and
canonical support-face scale compatibility.  It intentionally stops before the
next named result, the universal-scale collapse. -/
structure CoherentRelabelingFaceScalesStructure (F : PrefFamily.{u}) where
  branch_result : BranchAggregationCocycleNormalizedChainRuleStructure F
  scale_relabeling :
    FiniteChainScaleRelabelingAssumptionsFor branch_result
  support_face_scale :
    FiniteSupportFaceScaleAssumptionsFor branch_result

namespace CoherentRelabelingFaceScalesStructure

/-- The branch-chain structure inherited from the branch result. -/
noncomputable def chain
    {F : PrefFamily.{u}} (h : CoherentRelabelingFaceScalesStructure F) :
    BranchChainStructure F :=
  h.branch_result.chain

/-- The normalised chain rule inherited from the branch result. -/
theorem normalizedChainRule
    {F : PrefFamily.{u}} (h : CoherentRelabelingFaceScalesStructure F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : O → Channel A Y) :
    branchNormalizedValue h.chain q (P ▷ Q)
    =
    branchNormalizedValue h.chain q P
      + ∑ o : O,
          (Channel.outcomeMarginal P q) o *
          branchNormalizedValue h.chain
            (Channel.posterior P q o) (Q o) :=
  h.branch_result.normalizedChainRule q hq P Q

/-- Scale invariance under finite action relabelling. -/
theorem scale_relabel_eq
    {F : PrefFamily.{u}} (h : CoherentRelabelingFaceScalesStructure F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    h.branch_result.scale_factorization.scale (Relabeling.relabelDist e q) =
      h.branch_result.scale_factorization.scale q :=
  h.scale_relabeling.scale_relabel_eq e q hq

/-- Canonical support-face scale compatibility. -/
theorem support_face_scale_eq
    {F : PrefFamily.{u}} (h : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A)
    [Nonempty (supportSubtype r)]
    (hr_nonempty : ∃ a : A, 0 < r a)
    (hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hr_boundary : ¬ r.FullSupport) :
    h.branch_result.branch_agg.branchCoeff q r =
      h.branch_result.scale_factorization.scale q /
        h.branch_result.scale_factorization.scale r.restrictToSupport :=
  h.support_face_scale.support_face_scale
    q hq r hr_nonempty hr_nondegenerate hr_boundary

end CoherentRelabelingFaceScalesStructure

/-- Positive prior gauge data, without relabelling/support compatibility.

This weaker gauge is useful before the paper's coherent gauge has been chosen:
the transformed branch scale itself can be required to satisfy relabelling and
support-face compatibility, rather than requiring the raw representative to
already have those properties. -/
structure PositiveFaceScaleGauge.{v} where
  gauge :
    {A : Type v} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ
  gauge_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A), 0 < gauge q

/-- Positive prior gauge data that can be applied coherently across finite
action alphabets and support faces. -/
structure CoherentFaceScaleGauge.{v} where
  gauge :
    {A : Type v} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ
  gauge_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A), 0 < gauge q
  gauge_relabel_eq :
    ∀ {A B : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A),
      gauge (Relabeling.relabelDist e q) = gauge q
  gauge_support_restrict_eq :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (r : Dist A) [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      gauge r = gauge r.restrictToSupport

/-- Forget relabelling/support compatibility from a coherent gauge. -/
def CoherentFaceScaleGauge.toPositive
    (hgauge : CoherentFaceScaleGauge.{u}) :
    PositiveFaceScaleGauge.{u} where
  gauge := hgauge.gauge
  gauge_pos := hgauge.gauge_pos

/-- Positive prior-gauge rescaling of a posterior value representative. -/
noncomputable def posteriorValueRepresentation_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hV : PosteriorValueRepresentation F)
    (hgauge : PositiveFaceScaleGauge.{u}) :
    PosteriorValueRepresentation F where
  V := fun q E => hgauge.gauge q * hV.V q E
  respects_same_posterior_law := by
    intro A _ _ _ q E E' hsame
    rw [hV.respects_same_posterior_law q E E' hsame]
  represents_block_comparisons := by
    intro A _ _ _ q hq E₁ E₂
    have hpos : 0 < hgauge.gauge q := hgauge.gauge_pos q
    constructor
    · intro hpref
      have hge :
          hV.V q E₂ ≤ hV.V q E₁ :=
        (hV.represents_block_comparisons q hq E₁ E₂).mp hpref
      exact mul_le_mul_of_nonneg_left hge (le_of_lt hpos)
    · intro hge'
      have hge :
          hV.V q E₂ ≤ hV.V q E₁ :=
        le_of_mul_le_mul_left hge' hpos
      exact (hV.represents_block_comparisons q hq E₁ E₂).mpr hge
  affine_of_posteriorLawIntegral_mix := by
    intro A _ _ _ q t ht0 ht1 E_mix E₁ E₂ hmix
    rw [hV.affine_of_posteriorLawIntegral_mix
      q t ht0 ht1 E_mix E₁ E₂ hmix]
    ring
  zero_normalized := by
    intro A _ _ _ q hq
    rw [hV.zero_normalized q hq, mul_zero]

/-- Prior-gauge transformation of branch coefficients for a merely positive
gauge. -/
noncomputable def branchCoeff_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hgauge : PositiveFaceScaleGauge.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ :=
  (hgauge.gauge q / hgauge.gauge r) * hbranch.branchCoeff q r

/-- Branch aggregation is preserved under a positive prior-gauge rescaling. -/
noncomputable def branchAggregationStructure_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hgauge : PositiveFaceScaleGauge.{u}) :
    BranchAggregationStructure F where
  value_rep :=
    posteriorValueRepresentation_positiveGaugeTransform hbranch.value_rep hgauge
  branchCoeff := fun q r =>
    branchCoeff_positiveGaugeTransform hbranch hgauge q r
  branchCoeff_pos := by
    intro A _ _ _ q r hq hr
    exact mul_pos
      (div_pos (hgauge.gauge_pos q) (hgauge.gauge_pos r))
      (hbranch.branchCoeff_pos q r hq hr)
  branch_aggregation := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ Q
    dsimp [posteriorValueRepresentation_positiveGaugeTransform,
      branchCoeff_positiveGaugeTransform]
    rw [hbranch.branch_aggregation q hq P₁ Q]
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro o ho
    have hg_ne :
        hgauge.gauge (Channel.posterior P₁ q o) ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos (Channel.posterior P₁ q o))
    field_simp [hg_ne]
    simp only [Channel.outcomeMarginal_apply]
    ring

/-- Full-support branch-coefficient cocycles are preserved by positive
prior-gauge rescaling. -/
theorem finiteBranchCoeffCocycle_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hcocycle : FiniteBranchCoeffCocycleAssumptionsFor hbranch) :
    FiniteBranchCoeffCocycleAssumptionsFor
      (branchAggregationStructure_positiveGaugeTransform hbranch hgauge) where
  coeff_cocycle_fullSupport := by
    intro A _ _ _ q r s hq hr hs hnd
    dsimp [branchAggregationStructure_positiveGaugeTransform,
      branchCoeff_positiveGaugeTransform]
    rw [hcocycle.coeff_cocycle_fullSupport q r s hq hr hs hnd]
    have hgr_ne : hgauge.gauge r ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos r)
    have hgs_ne : hgauge.gauge s ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos s)
    field_simp [hgr_ne, hgs_ne]

/-- Full-support branch scale factorization is preserved by positive
prior-gauge rescaling. -/
noncomputable def finiteBranchScaleFactorizationFullSupport_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hfull : FiniteBranchScaleFactorizationFullSupportAssumptions hbranch)
    (hgauge : PositiveFaceScaleGauge.{u}) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (branchAggregationStructure_positiveGaugeTransform hbranch hgauge) where
  scale := fun q => hgauge.gauge q * hfull.scale q
  scale_pos := by
    intro A _ _ _ q hq hnd
    exact mul_pos (hgauge.gauge_pos q) (hfull.scale_pos q hq hnd)
  branchCoeff_factorization_fullSupport := by
    intro A _ _ _ q r hq hr hnd
    dsimp [branchAggregationStructure_positiveGaugeTransform,
      branchCoeff_positiveGaugeTransform]
    rw [hfull.branchCoeff_factorization_fullSupport q r hq hr hnd]
    have hgr_ne : hgauge.gauge r ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos r)
    have hsr_ne : hfull.scale r ≠ 0 :=
      ne_of_gt (hfull.scale_pos r hr hnd)
    field_simp [hgr_ne, hsr_ne]

/-- Public branch scale factorization is preserved by positive prior-gauge
rescaling. -/
noncomputable def finiteBranchScaleFactorization_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hfactor : FiniteBranchScaleFactorizationAssumptions hbranch)
    (hgauge : PositiveFaceScaleGauge.{u}) :
    FiniteBranchScaleFactorizationAssumptions
      (branchAggregationStructure_positiveGaugeTransform hbranch hgauge) where
  scale := fun q => hgauge.gauge q * hfactor.scale q
  scale_pos := by
    intro A _ _ _ q hq
    exact mul_pos (hgauge.gauge_pos q) (hfactor.scale_pos q hq)
  branchCoeff_factorization := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ hpos
    dsimp [branchAggregationStructure_positiveGaugeTransform,
      branchCoeff_positiveGaugeTransform]
    rw [hfactor.branchCoeff_factorization q hq P₁ o₁ hpos]
    ring_nf

/-- The branch/cocycle/scale package is preserved by positive prior-gauge
rescaling. -/
noncomputable def branchAggregationCocycleNormalizedChainRuleStructure_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hgauge : PositiveFaceScaleGauge.{u}) :
    BranchAggregationCocycleNormalizedChainRuleStructure F where
  branch_agg :=
    branchAggregationStructure_positiveGaugeTransform
      hbranch.branch_agg hgauge
  coeff_cocycle :=
    finiteBranchCoeffCocycle_positiveGaugeTransform
      hbranch.branch_agg hgauge hbranch.coeff_cocycle
  full_support_scale :=
    finiteBranchScaleFactorizationFullSupport_positiveGaugeTransform
      hbranch.branch_agg hbranch.full_support_scale hgauge
  scale_factorization :=
    finiteBranchScaleFactorization_positiveGaugeTransform
      hbranch.branch_agg hbranch.scale_factorization hgauge

/-- Relabelling compatibility for the transformed scale, supplied as a
condition on the chosen positive gauge and raw branch scale. -/
theorem finiteChainScaleRelabeling_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            hbranch.scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q * hbranch.scale_factorization.scale q) :
    FiniteChainScaleRelabelingAssumptionsFor
      (branchAggregationCocycleNormalizedChainRuleStructure_positiveGaugeTransform
        hbranch hgauge) where
  scale_relabel_eq := by
    intro A B _ _ _ _ _ _ e q hq
    dsimp [branchAggregationCocycleNormalizedChainRuleStructure_positiveGaugeTransform,
      finiteBranchScaleFactorization_positiveGaugeTransform]
    exact hrel e q hq

/-- Support-face compatibility for the transformed scale, supplied as a
condition on the chosen positive gauge and raw branch coefficient/scale. -/
theorem finiteSupportFaceScale_positiveGaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            hbranch.branch_agg.branchCoeff q r =
          (hgauge.gauge q * hbranch.scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              hbranch.scale_factorization.scale r.restrictToSupport)) :
    FiniteSupportFaceScaleAssumptionsFor
      (branchAggregationCocycleNormalizedChainRuleStructure_positiveGaugeTransform
        hbranch hgauge) where
  support_face_scale := by
    intro A _ _ _ q hq r _hr_support hr_nonempty hr_nondegenerate hr_boundary
    dsimp [branchAggregationCocycleNormalizedChainRuleStructure_positiveGaugeTransform,
      branchAggregationStructure_positiveGaugeTransform,
      branchCoeff_positiveGaugeTransform,
      finiteBranchScaleFactorization_positiveGaugeTransform]
    exact hsupport q hq r hr_nonempty hr_nondegenerate hr_boundary

/-- Build coherent relabelled face scales by first choosing a positive gauge on
the branch/cocycle/scale package and proving the transformed scale relabelling
and support-face equations. -/
noncomputable def CoherentRelabelingFaceScales_of_positiveGaugeBranch
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            hbranch.scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q * hbranch.scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            hbranch.branch_agg.branchCoeff q r =
          (hgauge.gauge q * hbranch.scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              hbranch.scale_factorization.scale r.restrictToSupport)) :
    CoherentRelabelingFaceScalesStructure F where
  branch_result :=
    branchAggregationCocycleNormalizedChainRuleStructure_positiveGaugeTransform
      hbranch hgauge
  scale_relabeling :=
    finiteChainScaleRelabeling_positiveGaugeTransform
      hbranch hgauge hrel
  support_face_scale :=
    finiteSupportFaceScale_positiveGaugeTransform
      hbranch hgauge hsupport

/-- Positive prior-gauge rescaling of a posterior value representative. -/
noncomputable def posteriorValueRepresentation_gaugeTransform
    {F : PrefFamily.{u}}
    (hV : PosteriorValueRepresentation F)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    PosteriorValueRepresentation F where
  V := fun q E => hgauge.gauge q * hV.V q E
  respects_same_posterior_law := by
    intro A _ _ _ q E E' hsame
    rw [hV.respects_same_posterior_law q E E' hsame]
  represents_block_comparisons := by
    intro A _ _ _ q hq E₁ E₂
    have hpos : 0 < hgauge.gauge q := hgauge.gauge_pos q
    constructor
    · intro hpref
      have hge :
          hV.V q E₂ ≤ hV.V q E₁ :=
        (hV.represents_block_comparisons q hq E₁ E₂).mp hpref
      exact mul_le_mul_of_nonneg_left hge (le_of_lt hpos)
    · intro hge'
      have hge :
          hV.V q E₂ ≤ hV.V q E₁ :=
        le_of_mul_le_mul_left hge' hpos
      exact (hV.represents_block_comparisons q hq E₁ E₂).mpr hge
  affine_of_posteriorLawIntegral_mix := by
    intro A _ _ _ q t ht0 ht1 E_mix E₁ E₂ hmix
    rw [hV.affine_of_posteriorLawIntegral_mix
      q t ht0 ht1 E_mix E₁ E₂ hmix]
    ring
  zero_normalized := by
    intro A _ _ _ q hq
    rw [hV.zero_normalized q hq, mul_zero]

/-- Prior-gauge transformation of branch coefficients. -/
noncomputable def branchCoeff_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hgauge : CoherentFaceScaleGauge.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) : ℝ :=
  (hgauge.gauge q / hgauge.gauge r) * hbranch.branchCoeff q r

/-- Branch aggregation is preserved under a positive prior-gauge rescaling of
the value representatives, with branch coefficients transformed by
`beta'(q,r)=gauge(q)/gauge(r) * beta(q,r)`. -/
noncomputable def branchAggregationStructure_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    BranchAggregationStructure F where
  value_rep :=
    posteriorValueRepresentation_gaugeTransform hbranch.value_rep hgauge
  branchCoeff := fun q r => branchCoeff_gaugeTransform hbranch hgauge q r
  branchCoeff_pos := by
    intro A _ _ _ q r hq hr
    exact mul_pos
      (div_pos (hgauge.gauge_pos q) (hgauge.gauge_pos r))
      (hbranch.branchCoeff_pos q r hq hr)
  branch_aggregation := by
    intro A O₁ O₂ _ _ _ _ _ _ _ q hq P₁ Q
    dsimp [posteriorValueRepresentation_gaugeTransform,
      branchCoeff_gaugeTransform]
    rw [hbranch.branch_aggregation q hq P₁ Q]
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro o ho
    have hg_ne :
        hgauge.gauge (Channel.posterior P₁ q o) ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos (Channel.posterior P₁ q o))
    field_simp [hg_ne]
    simp only [Channel.outcomeMarginal_apply]
    ring

/-- Full-support branch-coefficient cocycles are preserved by coherent positive
prior-gauge rescaling. -/
theorem finiteBranchCoeffCocycle_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hgauge : CoherentFaceScaleGauge.{u})
    (hcocycle : FiniteBranchCoeffCocycleAssumptionsFor hbranch) :
    FiniteBranchCoeffCocycleAssumptionsFor
      (branchAggregationStructure_gaugeTransform hbranch hgauge) where
  coeff_cocycle_fullSupport := by
    intro A _ _ _ q r s hq hr hs hnd
    dsimp [branchAggregationStructure_gaugeTransform,
      branchCoeff_gaugeTransform]
    rw [hcocycle.coeff_cocycle_fullSupport q r s hq hr hs hnd]
    have hgr_ne : hgauge.gauge r ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos r)
    have hgs_ne : hgauge.gauge s ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos s)
    field_simp [hgr_ne, hgs_ne]

/-- Scale transformation associated with a coherent positive prior gauge. -/
noncomputable def branchScale_gaugeTransform
    {F : PrefFamily.{u}}
    {hbranch : BranchAggregationStructure F}
    (hfactor : FiniteBranchScaleFactorizationAssumptions hbranch)
    (hgauge : CoherentFaceScaleGauge.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  hgauge.gauge q * hfactor.scale q

/-- Full-support branch scale factorization is preserved by coherent positive
prior-gauge rescaling, with scales transformed by `a'_q = g(q) a_q`. -/
noncomputable def finiteBranchScaleFactorizationFullSupport_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hfull : FiniteBranchScaleFactorizationFullSupportAssumptions hbranch)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (branchAggregationStructure_gaugeTransform hbranch hgauge) where
  scale := fun q => hgauge.gauge q * hfull.scale q
  scale_pos := by
    intro A _ _ _ q hq hnd
    exact mul_pos (hgauge.gauge_pos q) (hfull.scale_pos q hq hnd)
  branchCoeff_factorization_fullSupport := by
    intro A _ _ _ q r hq hr hnd
    dsimp [branchAggregationStructure_gaugeTransform,
      branchCoeff_gaugeTransform]
    rw [hfull.branchCoeff_factorization_fullSupport q r hq hr hnd]
    have hgr_ne : hgauge.gauge r ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos r)
    have hsr_ne : hfull.scale r ≠ 0 :=
      ne_of_gt (hfull.scale_pos r hr hnd)
    field_simp [hgr_ne, hsr_ne]

/-- Public branch scale factorization is preserved by coherent positive
prior-gauge rescaling, with scales transformed by `a'_q = g(q) a_q`. -/
noncomputable def finiteBranchScaleFactorization_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationStructure F)
    (hfactor : FiniteBranchScaleFactorizationAssumptions hbranch)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteBranchScaleFactorizationAssumptions
      (branchAggregationStructure_gaugeTransform hbranch hgauge) where
  scale := fun q => hgauge.gauge q * hfactor.scale q
  scale_pos := by
    intro A _ _ _ q hq
    exact mul_pos (hgauge.gauge_pos q) (hfactor.scale_pos q hq)
  branchCoeff_factorization := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ hpos
    dsimp [branchAggregationStructure_gaugeTransform,
      branchCoeff_gaugeTransform]
    rw [hfactor.branchCoeff_factorization q hq P₁ o₁ hpos]
    ring_nf

/-- The faithful branch/cocycle/scale package is preserved by coherent
positive prior-gauge rescaling. -/
noncomputable def branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    BranchAggregationCocycleNormalizedChainRuleStructure F where
  branch_agg :=
    branchAggregationStructure_gaugeTransform hbranch.branch_agg hgauge
  coeff_cocycle :=
    finiteBranchCoeffCocycle_gaugeTransform
      hbranch.branch_agg hgauge hbranch.coeff_cocycle
  full_support_scale :=
    finiteBranchScaleFactorizationFullSupport_gaugeTransform
      hbranch.branch_agg hbranch.full_support_scale hgauge
  scale_factorization :=
    finiteBranchScaleFactorization_gaugeTransform
      hbranch.branch_agg hbranch.scale_factorization hgauge

/-- Chain-scale relabelling is preserved by coherent relabelling-invariant
prior-gauge rescaling. -/
theorem finiteChainScaleRelabeling_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hrel : FiniteChainScaleRelabelingAssumptionsFor hbranch)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteChainScaleRelabelingAssumptionsFor
      (branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform
        hbranch hgauge) where
  scale_relabel_eq := by
    intro A B _ _ _ _ _ _ e q hq
    dsimp [branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      finiteBranchScaleFactorization_gaugeTransform]
    rw [hgauge.gauge_relabel_eq e q, hrel.scale_relabel_eq e q hq]

/-- Canonical support-face scale compatibility is preserved by coherent
support-compatible prior-gauge rescaling. -/
theorem finiteSupportFaceScale_gaugeTransform
    {F : PrefFamily.{u}}
    (hbranch : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hsupport : FiniteSupportFaceScaleAssumptionsFor hbranch)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteSupportFaceScaleAssumptionsFor
      (branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform
        hbranch hgauge) where
  support_face_scale := by
    intro A _ _ _ q hq r _hr_support hr_nonempty hr_nondegenerate hr_boundary
    dsimp [branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      branchAggregationStructure_gaugeTransform,
      branchCoeff_gaugeTransform,
      finiteBranchScaleFactorization_gaugeTransform]
    rw [hsupport.support_face_scale
      q hq r hr_nonempty hr_nondegenerate hr_boundary]
    rw [hgauge.gauge_support_restrict_eq
      r hr_nonempty hr_nondegenerate hr_boundary]
    ring_nf

/-- Coherent relabelled face scales are preserved by coherent positive
prior-gauge rescaling.  This is the structural operation needed to formalise
the paper's "choose a product-normalised gauge, then keep the same notation"
step. -/
noncomputable def CoherentRelabelingFaceScalesStructure.gaugeTransform
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    CoherentRelabelingFaceScalesStructure F where
  branch_result :=
    branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform
      hfaces.branch_result hgauge
  scale_relabeling :=
    finiteChainScaleRelabeling_gaugeTransform
      hfaces.branch_result hfaces.scale_relabeling hgauge
  support_face_scale :=
    finiteSupportFaceScale_gaugeTransform
      hfaces.branch_result hfaces.support_face_scale hgauge

/--
Herstein--Milnor/coherent-representative relabeling interface. Structural
posterior-law transport can compare a relabeled experiment only after pulling
test functions across the action equivalence; `PosteriorValueRepresentation`
itself records same-posterior-law invariance only inside one action type. This
field isolates the missing coherence of the chosen cardinal representatives
under simultaneous action/outcome relabeling.
-/
structure FinitePosteriorValueRelabelingAssumptions.{v} where
  V_relabel_eq :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hV : PosteriorValueRepresentation F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (eA : A ≃ B) (eO : O ≃ Y)
      (q : Dist A) (P : Channel A O),
      hV.V (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        hV.V q (experimentOfChannel P)

/-- Named Lean form of exact relabeling invariance for the selected posterior
value representatives. -/
theorem exactRelabelingInvariance_of_valueRelabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) :
    hV.V (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      hV.V q (experimentOfChannel P) :=
  hrelV.V_relabel_eq F hax hV eA eO q P

/-- Product priors are associative up to the canonical product-label
equivalence. -/
theorem relabelDist_prodAssoc
    {A B C : Type u} [Fintype A] [Fintype B] [Fintype C]
    (q : Dist A) (r : Dist B) (s : Dist C) :
    Relabeling.relabelDist (Equiv.prodAssoc A B C)
        (prodDist (prodDist q r) s) =
      prodDist q (prodDist r s) := by
  ext x
  rcases x with ⟨a, b, c⟩
  simp [Relabeling.relabelDist, prodDist_apply_pair]
  ring

/-- Product channels are associative up to the canonical product-label
equivalence on actions and outcomes. -/
theorem relabelChannel_prodAssoc
    {A B C O Y Z : Type u}
    [Fintype A] [Fintype B] [Fintype C]
    [Fintype O] [Fintype Y] [Fintype Z]
    (P : Channel A O) (R : Channel B Y) (S : Channel C Z) :
    Relabeling.relabelChannel (Equiv.prodAssoc A B C) (Equiv.prodAssoc O Y Z)
        (prodChannel (prodChannel P R) S) =
      prodChannel P (prodChannel R S) := by
  ext x o
  rcases x with ⟨a, b, c⟩
  rcases o with ⟨o, y, z⟩
  simp [Relabeling.relabelChannel, prodChannel_apply_pair]
  ring

/-- Faithful theorem statement for "Coherent relabelling and face scales".

The branch input is the Stage 24 faithful branch theorem.  The remaining inputs
are the two sharply named scale normalizations: relabelling invariance of the
chosen chain scales and support-face scale compatibility. -/
noncomputable def CoherentRelabelingFaceScales_of_faithfulBranch
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          hfaith F hax hV))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          hfaith F hax hV)) :
    CoherentRelabelingFaceScalesStructure F where
  branch_result :=
    BranchAggregationCocycleNormalizedChainRule_of_faithful
      hfaith F hax hV
  scale_relabeling := hscaleRelabel
  support_face_scale := hfaceScale

/-- Forget the later universal-scale field and keep only the branch-chain
content of a `ScaleCoherenceStructure`. -/
noncomputable def branchChainStructure_of_scaleCoherence
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F) :
    BranchChainStructure F where
  branch_agg := hs.branch_agg
  scale := hs.scale
  scale_pos := hs.scale_pos
  branchCoeff_factorization := hs.branchCoeff_factorization

end TraceableAgency
