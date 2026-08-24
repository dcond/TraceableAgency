/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.HMInterface

namespace TraceableAgency

universe u

/-!
## Stage ER-B: Entropy regularity for the concrete entropy candidate

`EntropyRegularity` (nonnegativity + singleton-zero) is proved for any
cross-prior block representation whose `Hfun` is the full-revelation
normalized value (definitional for every constructor in this file).

* nonnegativity at full support: main-text A6 (record-postprocessing aversion) with
  `postprocess id T = T` and the cross-prior bridge give
  `V̂_q(id) ≥ V̂_q(U_A) = 0`;
* singleton-zero: a point mass restricts to a subsingleton support face,
  where every experiment has zero value;
* boundary priors: routed through the single named residual
  `FiniteNormalizedValueSupportBoundaryAssumptions` (a projection of the root
  `FiniteCardinalSupportBoundaryAssumptions`).

The old target `FiniteEntropyRegularityFromAxiomsAssumptions` (∀ `hentropy`)
is not produced: it quantifies over arbitrary entropy representations and is
too strong.  The repaired target fixes `Hfun` to full revelation.
-/

/-- Post-processing the identity channel is the post-processing kernel itself. -/
theorem postprocess_idChannel_left
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O]
    (T : Channel A O) :
    Channel.postprocess Channel.idChannel T = T := by
  funext a
  ext o
  change (∑ b, (Dist.pure a) b * T b o) = T a o
  rw [Finset.sum_eq_single a
    (fun b _ hba => by rw [Dist.pure_apply, if_neg hba, zero_mul])
    (fun h => absurd (Finset.mem_univ a) h)]
  rw [Dist.pure_apply_self, one_mul]

/-- Full revelation dominates no information in normalized value at
full-support priors: A4 with `T = U_A` plus the scaled cross-prior bridge. -/
theorem normalizedValue_id_nonneg_of_crossPrior_fullSupport
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    0 ≤ normalizedValue hcross.entropy_reduction.scale_coherence q
      Channel.idChannel := by
  have ha4 :=
    hax.recordProcessing (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU A) q
  rw [postprocess_idChannel_left] at ha4
  have hbridge :=
    (hcross.cross_prior_block_rep q q hq hq
      (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU A)).mp ha4
  have hzero :
      hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.zero_normalized
      q hq
  simp only [normalizedValue]
  calc (0 : ℝ)
      = hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) /
        hcross.entropy_reduction.scale_coherence.scale q := by
        rw [hzero, zero_div]
    _ ≤ _ := hbridge

/-- Nonnegativity of the full-revelation normalized value at every prior,
with the boundary case routed through the support-restriction residual. -/
theorem normalizedValue_id_nonneg_of_crossPrior
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    0 ≤ normalizedValue hcross.entropy_reduction.scale_coherence q
      Channel.idChannel := by
  by_cases hq : q.FullSupport
  · exact normalizedValue_id_nonneg_of_crossPrior_fullSupport hax hcross q hq
  · haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    rw [hnorm.normalizedValue_support_restrict_boundary F hax hcross
        Channel.idChannel q hq,
      normalizedValue_restrict_idChannel_eq_idSupport
        hcross.entropy_reduction q]
    exact normalizedValue_id_nonneg_of_crossPrior_fullSupport hax hcross
      q.restrictToSupport (Dist.restrictToSupport_fullSupport q)

/-- A positive coordinate of a point mass identifies the point. -/
theorem eq_of_pure_pos
    {A : Type u} [Fintype A] [DecidableEq A]
    {a b : A} (hb : 0 < (Dist.pure a) b) : b = a := by
  by_contra hne
  rw [Dist.pure_apply, if_neg hne] at hb
  exact lt_irrefl 0 hb

/-- The support face of a point mass is a subsingleton. -/
theorem subsingleton_supportSubtype_pure
    {A : Type u} [Fintype A] [DecidableEq A] (a : A) :
    Subsingleton (supportSubtype (Dist.pure a)) := by
  refine ⟨fun b c => Subtype.ext ?_⟩
  rw [eq_of_pure_pos b.property, eq_of_pure_pos c.property]

/-- The full-revelation normalized value of a point mass vanishes: its support
face is a subsingleton, where every experiment is uninformative. -/
theorem normalizedValue_id_pure_eq_zero_of_crossPrior
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (a : A) :
    normalizedValue hcross.entropy_reduction.scale_coherence (Dist.pure a)
      Channel.idChannel = 0 := by
  by_cases hq : (Dist.pure a).FullSupport
  · haveI : Subsingleton A :=
      ⟨fun b c => by rw [eq_of_pure_pos (hq b), eq_of_pure_pos (hq c)]⟩
    have hV0 :
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V
          (Dist.pure a) (experimentOfChannel Channel.idChannel) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep
        (Dist.pure a) hq Channel.idChannel
    simp [normalizedValue, hV0]
  · haveI : Nonempty (supportSubtype (Dist.pure a)) :=
      supportSubtype_nonempty (Dist.pure a)
    haveI : Subsingleton (supportSubtype (Dist.pure a)) :=
      subsingleton_supportSubtype_pure a
    rw [hnorm.normalizedValue_support_restrict_boundary F hax hcross
        Channel.idChannel (Dist.pure a) hq,
      normalizedValue_restrict_idChannel_eq_idSupport
        hcross.entropy_reduction (Dist.pure a)]
    have hV0 :
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V
          (Dist.pure a).restrictToSupport
          (experimentOfChannel
            (Channel.idChannel :
              Channel (supportSubtype (Dist.pure a))
                (supportSubtype (Dist.pure a)))) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep
        (Dist.pure a).restrictToSupport
        (Dist.restrictToSupport_fullSupport (Dist.pure a))
        Channel.idChannel
    simp [normalizedValue, hV0]

/--
**Entropy regularity for full-revelation entropy candidates.**

Repaired Stage ER-B target: `EntropyRegularity` for any cross-prior block
representation whose `Hfun` is the full-revelation normalized value.  The
boundary residual is the single named support-restriction interface.
-/
theorem entropyRegularity_of_crossPrior_boundary
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hcross : CrossPriorBlockRepresentation F)
    (hHfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        hcross.entropy_reduction.Hfun q =
          normalizedValue hcross.entropy_reduction.scale_coherence q
            Channel.idChannel) :
    EntropyRegularity F hcross.entropy_reduction where
  H_nonneg := fun q => by
    rw [hHfun q]
    exact normalizedValue_id_nonneg_of_crossPrior hnorm hax hcross q
  H_singleton := fun a => by
    rw [hHfun (Dist.pure a)]
    exact normalizedValue_id_pure_eq_zero_of_crossPrior hnorm hax hcross a

/-- Entropy regularity for the pre-entropy-ready cross-prior representation:
its `Hfun` is `Hcandidate`, i.e. definitionally the full-revelation normalized
value, so the alignment hypothesis is `rfl`. -/
theorem entropyRegularity_of_preEntropyReady
    (hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hax : PureTraceConditions F) :
    EntropyRegularity F
      (crossPriorBlockRepresentation_of_preEntropyReady
        hready hhm huniq hax).entropy_reduction :=
  entropyRegularity_of_crossPrior_boundary hnorm hax _ (fun _ => rfl)

end TraceableAgency
