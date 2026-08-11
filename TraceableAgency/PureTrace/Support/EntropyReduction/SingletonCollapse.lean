/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.PosteriorCompatibility

namespace TraceableAgency

universe u

/-!
## Singleton Posterior-Law Collapse

When the action set A is a singleton, every distribution on A is the same
(the unique point mass), hence every experiment induces the same posterior law.
This is a purely structural / domain-collapse fact requiring no behavioral axiom.

Paper: Step 5 of Lemma coherentnorm:
"Let q_* = δ_* be the prior on a singleton. Its zero-normalised representative
is identically zero."
-/

/-- On a singleton type, any two distributions are equal. -/
theorem Dist.eq_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Subsingleton A]
    (q q' : Dist A) : q = q' := by
  ext a
  have huniq : ∀ b : A, b = a := fun b => Subsingleton.elim b a
  have hq : q a = ∑ b : A, q b :=
    (Finset.sum_eq_single a (fun b _ hba => absurd (huniq b) hba)
      (fun h => absurd (Finset.mem_univ a) h)).symm
  have hq' : q' a = ∑ b : A, q' b :=
    (Finset.sum_eq_single a (fun b _ hba => absurd (huniq b) hba)
      (fun h => absurd (Finset.mem_univ a) h)).symm
  linarith [q.sum_eq_one, q'.sum_eq_one]

/-- On a singleton type, the posterior of any experiment at any outcome equals q. -/
theorem posterior_eq_prior_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E : FiniteExperimentOn A) (o : E.OutcomeType) :
    @FiniteExperimentOn.posterior A _ _ _ E q o = q :=
  Dist.eq_of_subsingleton _ _

/-- On a singleton type, posteriorLawIntegralExp evaluates to φ(q) for any
experiment, because all posteriors collapse to q. -/
theorem posteriorLawIntegralExp_singleton
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E : FiniteExperimentOn A) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q E φ = φ q := by
  unfold posteriorLawIntegralExp
  have hpost : ∀ o : E.OutcomeType,
      @FiniteExperimentOn.posterior A _ _ _ E q o = q :=
    posterior_eq_prior_of_subsingleton q E
  simp_rw [hpost]
  letI := E.outFintype
  have hmarg_sum : (∑ o : E.OutcomeType, (E.outcomeMarginal q) o) = 1 :=
    (E.outcomeMarginal q).sum_eq_one
  rw [← Finset.sum_mul, hmarg_sum, one_mul]

/-- On a singleton action set, all experiments induce the same posterior law. -/
theorem samePosteriorLawExp_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    SamePosteriorLawExp q E E' := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_singleton q E φ, posteriorLawIntegralExp_singleton q E' φ]

/-- On a singleton action set, V q E = 0 for any experiment E. -/
theorem V_eq_zero_of_subsingleton
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A) :
    hV.V q E = 0 := by
  have heq : hV.V q E =
      hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) :=
    hV.respects_same_posterior_law q E
      (experimentOfChannel (Channel.uninformativeChannelU A))
      (samePosteriorLawExp_of_subsingleton q E _)
  rw [heq, hV.zero_normalized q hq]

/-- On a singleton action set, V q (experimentOfChannel P) = 0 for any channel P. -/
theorem V_channel_eq_zero_of_subsingleton
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    hV.V q (experimentOfChannel P) = 0 :=
  V_eq_zero_of_subsingleton F hV q hq (experimentOfChannel P)

/-- On a singleton first-coordinate, the product-left-slice value is constant
in P. This uses derived background inertness with same-type channels. -/
theorem productLeftSliceValue_singleton_const_sameType
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y)
    (P Q : Channel A O) :
    productLeftSliceValue hs q r R P =
      productLeftSliceValue hs q r R Q := by
  unfold productLeftSliceValue
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hVP : hs.branch_agg.value_rep.V q (experimentOfChannel P) = 0 :=
    V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P
  have hVQ : hs.branch_agg.value_rep.V q (experimentOfChannel Q) = 0 :=
    V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq Q
  have hlift_eq : hs.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (leftProductLiftChannel (B := B) P)) =
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) Q)) := by
    have hord_fwd := (product_left_noInfo_value_order_iff_base F hax hs q r hq hr P Q).mpr
    have hord_bwd := (product_left_noInfo_value_order_iff_base F hax hs q r hq hr Q P).mpr
    linarith [hord_fwd (by linarith : hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q)),
      hord_bwd (by linarith : hs.branch_agg.value_rep.V q (experimentOfChannel Q) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel P))]
  have hrepr_fwd := hs.branch_agg.value_rep.represents_block_comparisons
    (prodDist q r) hprod
    (experimentOfChannel (prodChannel P R))
    (experimentOfChannel (prodChannel Q R))
  have hrepr_bwd := hs.branch_agg.value_rep.represents_block_comparisons
    (prodDist q r) hprod
    (experimentOfChannel (prodChannel Q R))
    (experimentOfChannel (prodChannel P R))
  have hbackground_fwd :=
    ((independentBackgroundSeparability_of_axioms F hax).1
      q r hq hr P Q R (Channel.uninformativeChannelU B)).mpr
  have hbackground_bwd :=
    ((independentBackgroundSeparability_of_axioms F hax).1
      q r hq hr Q P R (Channel.uninformativeChannelU B)).mpr
  have hlift_pref : ExperimentPairPref F
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
      (prodDist q r) (prodDist q r) := by
    rw [hs.branch_agg.value_rep.represents_block_comparisons (prodDist q r) hprod]
    linarith [hlift_eq]
  have hlift_pref' : ExperimentPairPref F
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (prodDist q r) (prodDist q r) := by
    rw [hs.branch_agg.value_rep.represents_block_comparisons (prodDist q r) hprod]
    linarith [hlift_eq]
  have hge_fwd : hs.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (prodChannel P R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q R)) := by
    rw [← hrepr_fwd]
    exact hbackground_fwd hlift_pref
  have hge_bwd : hs.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (prodChannel Q R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) := by
    rw [← hrepr_bwd]
    exact hbackground_bwd hlift_pref'
  linarith

/-- On a singleton first-coordinate, any experiment `prodChannel P R` has the same
posterior law at `prodDist q r` as `prodChannel (uninformativeChannelU A) R`,
because the posterior only depends on the R-outcome (not on P or its outcome). -/
theorem samePosteriorLawExp_prodChannel_singleton_fst
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (P : Channel A O) (R : Channel B Y) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R)) := by
  obtain ⟨a₀⟩ : Nonempty A := inferInstance
  have huniq : ∀ a : A, a = a₀ := fun a => Subsingleton.elim a a₀
  have hq_eq : q a₀ = 1 := by
    have hsum := q.sum_eq_one
    rw [show (∑ a : A, q a) = q a₀ from
      Finset.sum_eq_single a₀ (fun b _ hb => absurd (huniq b) hb)
        (fun h => absurd (Finset.mem_univ a₀) h)] at hsum
    exact hsum
  have hU_val : ∀ (u : PUnit.{u+1}),
      (Channel.uninformativeChannelU A a₀ : Dist PUnit.{u+1}) u = 1 := by
    intro u; cases u; simp [Channel.uninformativeChannelU]
  have hP_sum : (∑ o : O, (P a₀).prob o) = 1 := (P a₀).sum_eq_one
  intro φ _hcont
  show posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel P R)) φ =
    posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R)) φ
  simp only [posteriorLawIntegralExp, experimentOfChannel, FiniteExperimentOn.ofChannel,
    FiniteExperimentOn.outcomeMarginal, FiniteExperimentOn.posterior]
  -- Both sides are sums of marginal * φ(posterior). Key: marginal(o,y) = P(a₀)(o) * mR(y).
  -- When P(a₀)(o) = 0, the term is 0. When P(a₀)(o) > 0, the posteriors agree.
  -- So the integral factors as (Σ_o P(a₀)(o)) * Σ_y mR(y) * φ(postR(y)) = RHS.
  have hmarg_factored : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
      (P a₀).prob o * Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) (PUnit.unit, y) := by
    intro o y
    simp only [Channel.outcomeMarginal_apply]
    have hstep_P : ∀ x : A × B, (prodDist q r) x * (prodChannel P R) x (o, y) =
        (P a₀).prob o * (r x.2 * R x.2 y) := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq a, hq_eq, one_mul]; ring
    have hstep_U : ∀ x : A × B, (prodDist q r) x *
        (prodChannel (Channel.uninformativeChannelU A) R) x (PUnit.unit, y) =
        r x.2 * R x.2 y := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq a, hq_eq, one_mul,
        hU_val, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => hstep_P x), ← Finset.mul_sum,
      Finset.sum_congr rfl (fun x _ => hstep_U x)]
  -- Key: when P(a₀)(o) > 0 and marginal_U > 0, posteriors are equal
  have hpost_when_pos : ∀ (o : O) (y : Y),
      (P a₀).prob o > 0 →
      Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) (PUnit.unit, y) > 0 →
      Channel.posterior (prodChannel P R) (prodDist q r) (o, y) =
        Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) := by
    intro o y hPo hUy
    have hmarg_P_pos : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) > 0 := by
      rw [hmarg_factored o y]; exact mul_pos hPo hUy
    unfold Channel.posterior
    rw [dif_pos hmarg_P_pos, dif_pos hUy]
    ext ⟨a, b⟩
    simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq a, hq_eq, one_mul,
      hU_val, mul_one]
    rw [show Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
        (P a₀).prob o * Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) from hmarg_factored o y]
    have hPo_ne : (P a₀).prob o ≠ 0 := ne_of_gt hPo
    have hUy_ne : (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) : Dist (PUnit.{u+1} × Y)).prob (PUnit.unit, y) ≠ 0 := ne_of_gt hUy
    field_simp
  -- Now prove the integral equality by factoring
  suffices h : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
      (P a₀).prob o *
        (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y))) by
    have hlhs : (∑ o : O × Y,
        Channel.outcomeMarginal (prodChannel P R) (prodDist q r) o *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) o)) =
      ∑ y : Y, Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [h]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hP_sum, one_mul]
    have hrhs : (∑ o : PUnit.{u+1} × Y,
        Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) o *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) o)) =
      ∑ y : Y, Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y)) := by
      rw [Fintype.sum_prod_type]
      simp [Finset.univ_unique]
    exact hlhs.trans hrhs.symm
  intro o y
  rcases eq_or_lt_of_le ((P a₀).nonneg o) with hPo | hPo
  · -- P(a₀)(o) = 0: marginal is 0, whole product is 0
    have hmarg0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
      rw [hmarg_factored o y]; simp [hPo.symm]
    simp only [Channel.outcomeMarginal_apply] at hmarg0
    simp [hmarg0, hPo.symm]
  · -- P(a₀)(o) > 0: need marginal_U positivity
    have hUy_nn : (0 : ℝ) ≤ Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) (PUnit.unit, y) :=
      (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r)).nonneg (PUnit.unit, y)
    rcases eq_or_lt_of_le hUy_nn with hUy | hUy
    · -- marginal_U = 0: both sides are 0
      have hmU0 : Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) = 0 := hUy.symm
      have hmP0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
        rw [hmarg_factored o y, hmU0, mul_zero]
      change Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
          φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
        (P a₀).prob o *
          (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
            (prodDist q r) (PUnit.unit, y) *
          φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
            (prodDist q r) (PUnit.unit, y)))
      rw [hmP0, hmU0]; ring
    · -- Both positive: posteriors agree
      rw [hmarg_factored o y, hpost_when_pos o y hPo hUy, mul_assoc]

/-- On a singleton first-coordinate, productLeftSliceValue is constant across
all outcome types. -/
theorem productLeftSliceValue_singleton_const
    {F : PrefFamily.{u}} (_hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (R : Channel B Y)
    (P : Channel A O) :
    productLeftSliceValue hs q r R P =
      productLeftSliceValue hs q r R (Channel.uninformativeChannelU A) := by
  unfold productLeftSliceValue
  exact hs.branch_agg.value_rep.respects_same_posterior_law (prodDist q r) _ _
    (samePosteriorLawExp_prodChannel_singleton_fst q r P R)

/--
**Singleton Product Slice Affinity**

The paper handles singleton factors separately after the nondegenerate
coherent-product argument. The affine-uniqueness theorem needs a nonconstant
base representative, so singleton first-coordinate action sets are isolated
instead of hidden in the classical uniqueness statement.

NOTE: This assumption is now proved internally via
`singletonSliceAffine_of_singletonCollapse` and is retained only for
backwards-compatibility of the structure definition until the cross-prior
bundle is updated.
-/
structure FiniteSingletonSliceAffineAssumptions.{v} where
  singleton_left_slice_positive_affine_transform :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          productLeftSliceValue hs q r R P =
            a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b

/-- The singleton slice affine assumption is provable internally:
take a = 1, b = productLeftSliceValue for the canonical uninformative channel.
Since V q (experimentOfChannel P) = 0 on singletons and the product-left-slice
value is constant in P (by derived background inertness and value zero), the identity holds trivially.

Paper: Step 5 of Lemma coherentnorm. -/
private theorem singletonSliceAffine_proof
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    ∃ a b : ℝ, 0 < a ∧
      ∀ {O : Type u} [Fintype O] [DecidableEq O]
        (P : Channel A O),
        productLeftSliceValue hs q r R P =
          a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b := by
  refine ⟨1, productLeftSliceValue hs q r R (Channel.uninformativeChannelU _), one_pos, ?_⟩
  intro O _ _ P
  have hVzero : hs.branch_agg.value_rep.V q (experimentOfChannel P) = 0 :=
    V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P
  have hconst : productLeftSliceValue hs q r R P =
      productLeftSliceValue hs q r R (Channel.uninformativeChannelU _) :=
    productLeftSliceValue_singleton_const hax hs q r hq hr R P
  linarith

theorem singletonSliceAffine_of_singletonCollapse :
    FiniteSingletonSliceAffineAssumptions.{u} :=
  ⟨singletonSliceAffine_proof⟩

/--
**Base Value Nonconstancy**

Value consequence of local nontriviality: at full-support non-singleton priors,
full revelation and no information have different posterior values. Stage 10L
reduced this to strict experiment-pair preference, and Stage 10M derives that
strictness from A1 plus structural Unit/PUnit relabeling and block-swap
plumbing. This compatibility structure is no longer a live external field.
-/
structure FiniteValueNonconstancyAssumptions.{v} where
  base_value_nonconstant :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hnot_subsingleton : ¬ Subsingleton A),
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))

/-- Strict experiment-pair preference at a full-support prior forces the value
representative to assign different values. -/
theorem value_ne_of_strict_experiment_pref
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (E₁ E₂ : FiniteExperimentOn A)
    (hpref : ExperimentPairPref F E₁ E₂ q q)
    (hnrev : ¬ ExperimentPairPref F E₂ E₁ q q) :
    hV.V q E₁ ≠ hV.V q E₂ := by
  intro heq
  have hge₂₁ : hV.V q E₂ ≥ hV.V q E₁ := by
    simp [heq]
  have _hge₁₂ : hV.V q E₁ ≥ hV.V q E₂ :=
    (hV.represents_block_comparisons q hq E₁ E₂).mp hpref
  exact hnrev ((hV.represents_block_comparisons q hq E₂ E₁).mpr hge₂₁)

/-- Reversing deterministic bijective outcome postprocessing recovers the
original channel. -/
theorem postprocess_posteriorLawEquivKernel_symm_eq_original
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (P : Channel A O) :
    Channel.postprocess
        (Channel.postprocess P (posteriorLawEquivKernel e))
        (posteriorLawEquivKernel e.symm) =
      P := by
  ext a o
  simp [postprocess_posteriorLawEquivKernel_apply]

/-- Outcome relabeling by a deterministic equivalence preserves the preference
relation. This local version uses only A4, A3, and A1 transitivity. -/
theorem rel_postprocess_posteriorLawEquivKernel_of_A4
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (e : O ≃ Y) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (Channel.postprocess P (posteriorLawEquivKernel e)) q r := by
  let P' := Channel.postprocess P (posteriorLawEquivKernel e)
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q) := by
    simpa [P'] using hax.recordProcessing P (posteriorLawEquivKernel e) q
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist q) (inrDist q) := by
    have h := hax.recordProcessing P' (posteriorLawEquivKernel e.symm) q
    simpa [P', postprocess_posteriorLawEquivKernel_symm_eq_original] using h
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r) := by
    simpa [P'] using hax.recordProcessing P (posteriorLawEquivKernel e) r
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist r) (inrDist r) := by
    have h := hax.recordProcessing P' (posteriorLawEquivKernel e.symm) r
    simpa [P', postprocess_posteriorLawEquivKernel_symm_eq_original] using h
  have hblock :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      P P' P P' q q r r
      hq_to_new hq_to_old hr_to_new hr_to_old
  exact (hax.blockCoherence.duplication P q r).trans (hblock.trans (hax.blockCoherence.duplication P' q r).symm)

/--
**A1 Experiment-Pair Strictness Bridge**

Narrow ordinal compatibility bridge isolated in Stage 10L and proved in
Stage 10M. A1 gives strictness for the ordinary
`Unit` no-information channel as a reverse-lottery failure in the same block
environment. The value representation needs strictness as an experiment-pair
comparison against `Channel.uninformativeChannelU`, whose reverse comparison is
encoded in the swapped two-block environment. The proof below uses the
upstream structural Unit/PUnit lift and block-swap/relabeling transfer; this is
not a cardinal value or product assumption.
-/
structure FiniteA1ExperimentPairStrictnessAssumptions.{v} where
  id_uninformativeU_strict :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hnot_subsingleton : ¬ Subsingleton A),
      ExperimentPairPref F
        (experimentOfChannel (Channel.idChannel : Channel A A))
        (experimentOfChannel (Channel.uninformativeChannelU A))
        q q
      ∧
      ¬ ExperimentPairPref F
        (experimentOfChannel (Channel.uninformativeChannelU A))
        (experimentOfChannel (Channel.idChannel : Channel A A))
        q q

/-- A1's ordinary Unit no-information strictness, after the structural
Unit/PUnit relabeling and block-swap transfers, gives exactly the
ExperimentPairPref strictness needed by the value nonconstancy witness. -/
theorem id_uninformativeU_experiment_strict_of_A1
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hnot_subsingleton : ¬ Subsingleton A) :
    ExperimentPairPref F
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      q q
    ∧
    ¬ ExperimentPairPref F
      (experimentOfChannel (Channel.uninformativeChannelU A))
      (experimentOfChannel (Channel.idChannel : Channel A A))
      q q := by
  classical
  haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
  have hstrict :=
    Relabeling.lifted_uninformative_strict_of_A1 F hax q hq
  constructor
  · change
      F.rel
        (blockChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A))
        (inlDist q) (inrDist q)
    exact hstrict.1
  · intro hrev
    change
      F.rel
        (blockChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel A A))
        (inlDist q) (inrDist q) at hrev
    have hrev_same :
        F.rel
          (blockChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU A))
          (inrDist q) (inlDist q) := by
      exact
        (Relabeling.block_swap_rel_of_axioms F hax
          (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A) q q).mpr hrev
    exact hstrict.2 hrev_same

/-- Package the A1-to-experiment strictness transfer as a derived structure. -/
theorem a1ExperimentPairStrictness_of_axioms :
    FiniteA1ExperimentPairStrictnessAssumptions.{u} where
  id_uninformativeU_strict := by
    intro F hax A _ _ _ q hq hnot_subsingleton
    exact id_uninformativeU_experiment_strict_of_A1 F hax q hq hnot_subsingleton

/-- Base value nonconstancy follows from A1 and the posterior value
representation. -/
theorem valueNonconstancy_of_A1_experiment_strictness
    (hstrictness : FiniteA1ExperimentPairStrictnessAssumptions.{u}) :
    FiniteValueNonconstancyAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hs A _ _ _ q hq hnot_subsingleton
  have hstrict :=
    hstrictness.id_uninformativeU_strict F hax q hq hnot_subsingleton
  exact
    value_ne_of_strict_experiment_pref F hs.branch_agg.value_rep q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      hstrict.1 hstrict.2

/--
**Classical Affine Utility Uniqueness**

Classical affine-geometry theorem specialized to the finite experiment channel
domain used here. If the base representative and product slice are affine under
public mixtures, the base representative is nonconstant, and the two
functionals represent the same weak order, then the product slice is a positive
affine transform of the base representative.
-/
structure ClassicalAffineUtilityUniquenessAssumptions.{v} where
  positive_affine_transform :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hnot_subsingleton : ¬ Subsingleton A)
      (R : Channel B Y),
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        hs.branch_agg.value_rep.V q
            (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
          t * hs.branch_agg.value_rep.V q (experimentOfChannel P) +
            (1 - t) * hs.branch_agg.value_rep.V q (experimentOfChannel Q)) →
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q) =
          t * productLeftSliceValue hs q r R P +
            (1 - t) * productLeftSliceValue hs q r R Q) →
      (hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))) →
      (∀ {O : Type v} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        productLeftSliceValue hs q r R P ≥ productLeftSliceValue hs q r R Q ↔
          hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
            hs.branch_agg.value_rep.V q (experimentOfChannel Q)) →
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          productLeftSliceValue hs q r R P =
            a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b

/-- Assemble the Stage 10G affine-slice uniqueness package from the sharper
affinity, nonconstancy/singleton, and classical affine-utility uniqueness
components. -/
theorem affineSliceUniqueness_of_parts
    (hVaff : FinitePosteriorValueAffineAssumptions.{u})
    (hsliceAff : FiniteProductLeftSlicePublicMixAffineAssumptions.{u})
    (hnonconst : FiniteValueNonconstancyAssumptions.{u})
    (hsingle : FiniteSingletonSliceAffineAssumptions.{u})
    (huniq : ClassicalAffineUtilityUniquenessAssumptions.{u}) :
    FiniteAffineSliceUniquenessAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
  classical
  by_cases hsub : Subsingleton A
  · letI : Subsingleton A := hsub
    exact
      hsingle.singleton_left_slice_positive_affine_transform
        F hax hs q r hq hr R
  · have hbase_aff :
      ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        hs.branch_agg.value_rep.V q
            (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
          t * hs.branch_agg.value_rep.V q (experimentOfChannel P) +
            (1 - t) * hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
      intro O Z _ _ _ _ t ht0 ht1 P Q
      exact
        hVaff.V_publicMix_affine F hax hs.branch_agg.value_rep
          q hq t ht0 ht1 P Q
    have hslice_aff :
      ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q) =
          t * productLeftSliceValue hs q r R P +
            (1 - t) * productLeftSliceValue hs q r R Q := by
      intro O Z _ _ _ _ t ht0 ht1 P Q
      exact
        hsliceAff.product_left_slice_publicMix_affine
          F hax hs q r hq hr R t ht0 ht1 P Q
    have hnonconstant :=
      hnonconst.base_value_nonconstant F hax hs q hq hsub
    have hsame_order :
      ∀ {O : Type u} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        productLeftSliceValue hs q r R P ≥ productLeftSliceValue hs q r R Q ↔
          hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
            hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
      intro O _ _ P Q
      exact product_left_slice_same_order F hax hs q r hq hr P Q R
    exact
      huniq.positive_affine_transform
        F hax hs q r hq hr hsub R
        hbase_aff hslice_aff hnonconstant hsame_order

noncomputable def affineSliceUniquenessSlope
    (haff : FiniteAffineSliceUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (haff.left_slice_positive_affine_transform F hax hs q r h.1 h.2 R)
    else 0

noncomputable def affineSliceUniquenessIntercept
    (haff : FiniteAffineSliceUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform F hax hs q r h.1 h.2 R))
    else 0

/-- Recover the previous Stage 10F compatibility package from the narrower
affine-slice uniqueness assumption. -/
noncomputable def productLeftSliceAffine_of_affineUniqueness
    (haff : FiniteAffineSliceUniquenessAssumptions.{u}) :
    FiniteProductLeftSliceAffineAssumptions.{u} where
  leftSliceSlope := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r R
    exact affineSliceUniquenessSlope haff F hax hs q r R
  leftSliceIntercept := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r R
    exact affineSliceUniquenessIntercept haff F hax hs q r R
  leftSliceSlope_pos := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hpos :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform F hax hs q r hq hr R))).1
    simpa [affineSliceUniquenessSlope, hq, hr] using hpos
  left_slice_affine := by
    intro F hax hs A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    classical
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform F hax hs q r hq hr R))).2
        (P := P)
    simpa [productLeftSliceValue, affineSliceUniquenessSlope,
      affineSliceUniquenessIntercept, hq, hr] using hspec

/-- The left-slice intercept equals the product-left-slice value at the
uninformative first-coordinate channel. This is immediate from the affine
identity `V(P⊗R) = α_R V_q(P) + γ_R` at P = U_A where V_q(U_A) = 0.

Paper: Step 2 of Lemma coherentnorm: Taking μ = δ_p shows
γ(ν) = L_{p,r}(δ_p,ν). -/
theorem leftSliceIntercept_eq_noInfo_productLeftSliceValue
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hslice.leftSliceIntercept F hax hs q r R =
      productLeftSliceValue hs q r R (Channel.uninformativeChannelU A) := by
  have haffine := hslice.left_slice_affine F hax hs q r hq hr
    (Channel.uninformativeChannelU A) R
  have hVzero : hs.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hs.branch_agg.value_rep.zero_normalized q hq
  unfold productLeftSliceValue
  rw [hVzero, mul_zero, zero_add] at haffine
  exact haffine.symm

/-- The left-slice intercept at the uninformative second-coordinate background
R = U_B is zero. From the intercept = no-info identity, this equals
V_{q⊗r}(U_A ⊗ U_B) = 0 since PUnit × PUnit is subsingleton. -/
theorem leftSliceIntercept_uninformative_eq_zero
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hslice.leftSliceIntercept F hax hs q r
      (Channel.uninformativeChannelU B) = 0 := by
  rw [leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr]
  simp only [productLeftSliceValue]
  exact V_eq_zero_of_subsingleton_outcome F hs.branch_agg.value_rep
    (prodDist q r) (prodDist_fullSupport q r hq hr)
    (prodChannel (Channel.uninformativeChannelU A) (Channel.uninformativeChannelU B))

/-- The left-slice intercept function R ↦ γ_R represents the same weak order as
V_r. That is, γ_R ≥ γ_S iff V_r(R) ≥ V_r(S). This follows from:
1. γ_R = productLeftSliceValue at U_A = V_{q⊗r}(U_A ⊗ R)
2. The product right-slice same-order theorem. -/
theorem leftSliceIntercept_same_order_as_Vr
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R S : Channel B Y) :
    hslice.leftSliceIntercept F hax hs q r R ≥
      hslice.leftSliceIntercept F hax hs q r S ↔
    hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
  rw [leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr R,
      leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr S]
  exact product_right_slice_same_order F hax hs q r hq hr
    (Channel.uninformativeChannelU A) R S

/-- The left-slice intercept is public-mix affine in R. This is the missing
"γ is affine" premise from the paper's Step 2.
Derived from: intercept = no-info product value + right-slice public-mix affinity. -/
theorem leftSliceIntercept_publicMix_affine
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    hslice.leftSliceIntercept F hax hs q r (publicMixChannel t ht0 ht1 R S) =
      t * hslice.leftSliceIntercept F hax hs q r R +
        (1 - t) * hslice.leftSliceIntercept F hax hs q r S := by
  rw [leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr,
      leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr R,
      leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr S]
  simp only [productLeftSliceValue]
  exact product_right_slice_publicMix_affine hVaff hax hs q r hq hr
    (Channel.uninformativeChannelU A) t ht0 ht1 R S

/--
**Second-Coordinate Affine Utility Uniqueness**

Narrow classical/HM uniqueness interface for the intercept step in Step 2 of
Lemma `coherentnorm`. If a second-coordinate functional γ is public-mix affine,
represents the same weak order as the posterior value representative `V_r`, and
vanishes at the no-information experiment, then γ is a positive linear multiple
of `V_r`.

This is deliberately separated from the first-coordinate
`ClassicalAffineUtilityUniquenessAssumptions`, whose conclusion is hard-coded to
`productLeftSliceValue`.
-/
structure ClassicalSecondCoordinateAffineUniquenessAssumptions.{v} where
  positive_linear_of_same_order_affine_zero :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (γ : {Y : Type v} → [Fintype Y] → [DecidableEq Y] → Channel B Y → ℝ),
      (∀ {Y Z : Type v} [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (R : Channel B Y) (S : Channel B Z),
        γ (publicMixChannel t ht0 ht1 R S) =
          t * γ R + (1 - t) * γ S) →
      (∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
        (R S : Channel B Y),
        γ R ≥ γ S ↔
          hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
            hs.branch_agg.value_rep.V r (experimentOfChannel S)) →
      γ (Channel.uninformativeChannelU B) = 0 →
      ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          γ R =
            Bcoeff * hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Apply second-coordinate affine uniqueness to the left-slice intercept
function γ_R. The same-order, zero, and public-mix affine hypotheses are exactly
the Stage 10O/10P internal theorems. -/
theorem leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateAffineUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
      ∀ {Y : Type u} [Fintype Y] [DecidableEq Y]
        (R : Channel B Y),
        hslice.leftSliceIntercept F hax hs q r R =
          Bcoeff * hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  let γ : {Y : Type u} → [Fintype Y] → [DecidableEq Y] → Channel B Y → ℝ :=
    fun {Y} [Fintype Y] [DecidableEq Y] R =>
      hslice.leftSliceIntercept F hax hs q r R
  have haff :
      ∀ {Y Z : Type u} [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (R : Channel B Y) (S : Channel B Z),
        γ (publicMixChannel t ht0 ht1 R S) =
          t * γ R + (1 - t) * γ S := by
    intro Y Z _ _ _ _ t ht0 ht1 R S
    change
      hslice.leftSliceIntercept F hax hs q r
          (publicMixChannel t ht0 ht1 R S) =
        t * hslice.leftSliceIntercept F hax hs q r R +
          (1 - t) * hslice.leftSliceIntercept F hax hs q r S
    exact leftSliceIntercept_publicMix_affine hslice hVaff hax hs
      q r hq hr t ht0 ht1 R S
  have horder :
      ∀ {Y : Type u} [Fintype Y] [DecidableEq Y]
        (R S : Channel B Y),
        γ R ≥ γ S ↔
          hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
            hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
    intro Y _ _ R S
    change
      hslice.leftSliceIntercept F hax hs q r R ≥
        hslice.leftSliceIntercept F hax hs q r S ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S)
    exact leftSliceIntercept_same_order_as_Vr hslice F hax hs q r hq hr R S
  have hzero : γ (Channel.uninformativeChannelU B) = 0 := by
    change
      hslice.leftSliceIntercept F hax hs q r
        (Channel.uninformativeChannelU B) = 0
    exact leftSliceIntercept_uninformative_eq_zero hslice F hax hs q r hq hr
  exact
    huniq.positive_linear_of_same_order_affine_zero
      F hax hs q r hq hr γ haff horder hzero

/--
**Product Slice Intercept Assumptions**

Paper-specific content identifying the first-coordinate slice intercept
`γ_R = L(δ_q,R)` as a positive multiple of the second-coordinate value:

`γ_R = B_{q,r} V_r(R)`.
-/
structure FiniteProductSliceInterceptAssumptions.{v}
    (hslice : FiniteProductLeftSliceAffineAssumptions.{v}) where
  rightCoeff :
    ∀ (F : PrefFamily.{v}), PureTraceConditions F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff F hax hs q r
  leftSliceIntercept_value :
    ∀ (F : PrefFamily.{v})
      (hax : PureTraceConditions F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      hslice.leftSliceIntercept F hax hs q r R =
        rightCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- The positive coefficient in the intercept theorem supplied by
second-coordinate affine uniqueness. It is only read at full-support priors; the
fallback value is irrelevant and keeps the total function well-defined. -/
noncomputable def leftSliceInterceptRightCoeff
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateAffineUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
          hslice hVaff huniq F hax hs q r h.1 h.2)
    else 1

/-- Recover the previous intercept compatibility package from the narrower
second-coordinate affine-uniqueness interface plus the internal Stage 10O/10P
same-order, zero, and public-mix affine facts. -/
noncomputable def productSliceIntercept_of_secondCoordinateAffineUniqueness
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateAffineUniquenessAssumptions.{u}) :
    FiniteProductSliceInterceptAssumptions.{u} hslice where
  rightCoeff := by
    intro F hax hs A B _ _ _ _ _ _ q r
    exact leftSliceInterceptRightCoeff hslice hVaff huniq F hax hs q r
  rightCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    classical
    have hpos :=
      (Classical.choose_spec
        (leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
          hslice hVaff huniq F hax hs q r hq hr)).1
    simpa [leftSliceInterceptRightCoeff, hq, hr] using hpos
  leftSliceIntercept_value := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hspec :=
      (Classical.choose_spec
        (leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
          hslice hVaff huniq F hax hs q r hq hr)).2 (R := R)
    simpa [leftSliceInterceptRightCoeff, hq, hr] using hspec

end TraceableAgency
