/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.PreEntropyConstruction

/-!
# Stage ER-C: Entropy Reduction from the Closed Pre-Entropy Spine

This file replaces the legacy monolith consumers (`entropyReduction_of_axioms`,
`crossPriorBlock_of_axioms`, which consume `FiniteScaleCoherenceAssumptions` and
`FiniteBranchAggregationAssumptions`) by constructors that run through the
closed interaction-collapse spine:

* `EntropyReductionRepresentation_of_interactionCollapse` — entropy reduction
  from any `InteractionCollapseUniversalChainScaleStructure`;
* `crossPriorBlockRepresentation_of_preUniversalBridge` — the scaled paper
  blockbridge from the pre-universal unscaled bridge, replacing the
  `FiniteCrossPriorBlockAssumptions` monolith;
* `entropyReduction_of_preEntropyReady` /
  `crossPriorBlockRepresentation_of_preEntropyReady` — both targets from a
  single `PreEntropyReadyFaceScalesStructure`.

Route hygiene for the pre-Faddeev constructors below: no
`FiniteScaleCoherenceAssumptions`, `FiniteBranchAggregationAssumptions`,
or `FiniteCrossPriorBlockAssumptions` is consumed.  The final sections of this
file then deliberately enter the Faddeev/Shannon and MI spine interfaces.
-/

namespace TraceableAgency

universe u

/-- Combined final Herstein--Milnor/Blackwell interface for the cleaned route.

The current development uses two HM-shaped interfaces: `FiniteHersteinMilnorAssumptions`
constructs the selected posterior value representative once posterior-law
sufficiency is available, while
`ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions` supplies the
affine and integral consequences used later.

The Blackwell field is the *pure* finite Blackwell equivalence theorem
`FiniteSamePosteriorLawBlackwellEquivalenceAssumptions` (same posterior law at a
full-support prior ⇒ the two experiments are mutual garblings/post-processings).
The paper-specific block-comparison replacement package
`FiniteBlackwellPosteriorAssumptions` is *not* an input here: it is reconstructed
internally from this pure theorem plus the A4/A3/A1 replacement plumbing via
`blackwellPosteriorReplacement_of_samePosteriorGarblings`.  This keeps the external
boundary exactly at the classical Blackwell theorem. -/
structure FinalHMInterface.{v} where
  blackwell : FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{v}
  hm_rep : FiniteHersteinMilnorAssumptions.{v}
  hm_affine : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{v}

/-- Posterior-law sufficiency from the combined final HM interface.

The pure Blackwell equivalence theorem is first upgraded to the block-comparison
replacement package by `blackwellPosteriorReplacement_of_samePosteriorGarblings`
(A4/A3/A1 plumbing, proved internally), then fed to
`from_axioms_to_posterior_of_blackwell`. -/
theorem posteriorLawSufficiency_of_FinalHMInterface
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : TraceAxioms F) :
    PosteriorLawSufficiency F :=
  from_axioms_to_posterior_of_blackwell F
    (blackwellPosteriorReplacement_of_samePosteriorGarblings hhm.blackwell) hax

/-- Data-carrying posterior value representative from the combined final HM
interface. -/
noncomputable def posteriorValueRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : TraceAxioms F) :
    PosteriorValueRepresentation F :=
  posteriorValueRep_of_HersteinMilnor F hhm.hm_rep
    (posteriorLawSufficiency_of_FinalHMInterface hhm hax)

/-- Affine/integral HM consequences from the combined final HM interface. -/
def classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u}) :
    ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u} :=
  hhm.hm_affine

/-- **Exact relabelling covariance (naturality) of the constructed HM value
functional.**

This is a genuine property of the canonically constructed Herstein--Milnor
posterior-law value functional: relabelling the action/outcome alphabets by
finite bijections carries the value to the value at the relabelled data
(`cor:permutationinvariance`, exact relabelling invariance).  It is *not* a new
economic premise; it is a covariance clause on the classical HM interface, of
the same status as the `marginalValue_support_face` support-face coherence
clause added by the cardinal-boundary elimination.  It is provided by the HM
data rather than assumed downstream as the `product_normalized` /
`FiniteSelectedPosteriorValueRelabelingFor` convention.

The clause is stated for the representative `posteriorValueRepresentation_of_
FinalHMInterface`, which is exactly the functional the pre-entropy spine uses. -/
structure FinalHMRelabelCovariance
    (hhm : FinalHMInterface.{u}) : Prop where
  V_relabel_eq :
    ∀ {F : PrefFamily.{u}} (hax : TraceAxioms F)
      {A B O Y : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (eA : A ≃ B) (eO : O ≃ Y)
      (q : Dist A) (P : Channel A O),
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P)

/-- The HM covariance clause yields exact relabelling invariance for **any**
coherent face-scale representative whose value functional is (definitionally)
the constructed HM functional scaled by a gauge that is constant on relabelling
orbits.  For the special case of the constant gauge this is the identity used to
discharge `product_normalized` without the pinning convention.

This is the general helper; callers instantiate it with the concrete coherent
face-scale representative built from `hhm`. -/
theorem finiteSelectedPosteriorValueRelabeling_of_FinalHM_covariance
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hVeq :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (E : FiniteExperimentOn A),
        hfaces.branch_result.branch_agg.value_rep.V q E =
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q E)
    (hcov : FinalHMRelabelCovariance hhm) :
    FiniteSelectedPosteriorValueRelabelingFor hfaces where
  V_relabel_eq := by
    intro _hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    rw [hVeq (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)),
      hVeq q (experimentOfChannel P)]
    exact hcov.V_relabel_eq hax eA eO q P

/-- **R1 core: branch tangent-scalar coefficient relabelling covariance.**

The faithful tangent-scalar coefficient `branchPathCoeff` is invariant under
finite action relabellings, derived from the marginal-value relabel naturality
clause on the integral representation.  The argument transports the identity/
no-information tangent on the reached posterior across the relabelling: its
`linearPart` is a value difference (`value_difference`), the posterior-law
integral is relabel-covariant (`posteriorLawIntegral_relabelChannel`), and the
representing test function is relabel-natural (`marginalValue_relabel`), so the
scalar relation `linearPart q η = branchPathCoeff q r · linearPart r η`
transports and the nonzero tangent (A1) cancels. -/
theorem branchPathCoeff_relabel_of_marginalValue_relabel
    {F : PrefFamily.{u}}
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hpath : BranchPathTangentScalarStructure F hV
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint))
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (eA : A ≃ B) (q r : Dist A)
    (hq : q.FullSupport) (hr : r.FullSupport)
    (hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    hpath.branchPathCoeff (Relabeling.relabelDist eA q) (Relabeling.relabelDist eA r) =
      hpath.branchPathCoeff q r := by
  classical
  have hqB : (Relabeling.relabelDist eA q).FullSupport :=
    Relabeling.relabelDist_fullSupport eA q hq
  have hrB : (Relabeling.relabelDist eA r).FullSupport :=
    Relabeling.relabelDist_fullSupport eA r hr
  have hndB : ∃ a b : B, a ≠ b ∧ 0 < (Relabeling.relabelDist eA r) a ∧
      0 < (Relabeling.relabelDist eA r) b := by
    rcases hnd with ⟨a, b, hab, ha, hb⟩
    exact ⟨eA a, eA b, fun h => hab (eA.injective h),
      by rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact ha,
      by rw [Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact hb⟩
  have hnotsubA : ¬ Subsingleton A := not_subsingleton_of_dist_nondegenerate _ hnd
  set idA : Channel A A := Channel.idChannel
  set UA : Channel A PUnit.{u+1} := Channel.uninformativeChannelU A
  set idB : Channel B B := Channel.idChannel
  set UB : Channel B PUnit.{u+1} := Channel.uninformativeChannelU B
  set ηA : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r (experimentOfChannel idA) (experimentOfChannel UA) with hηA_def
  set ηB : PosteriorLawSigned B :=
    posteriorLawDifferenceExp (Relabeling.relabelDist eA r)
      (experimentOfChannel idB) (experimentOfChannel UB) with hηB_def
  have hηA_atomic : PosteriorLawSigned.AtomicLinear ηA :=
    posteriorLawDifferenceExp_atomicLinear _ _ _
  have hηA_tan : PosteriorLawTangent ηA := posteriorLawDifferenceExp_tangent _ _ _
  have hηB_atomic : PosteriorLawSigned.AtomicLinear ηB :=
    posteriorLawDifferenceExp_atomicLinear _ _ _
  have hηB_tan : PosteriorLawTangent ηB := posteriorLawDifferenceExp_tangent _ _ _
  have hidA : Relabeling.relabelChannel eA eA (Channel.idChannel : Channel A A) = idB := by
    funext b; ext b'
    rw [Relabeling.relabelChannel_apply]; simp only [idB, Channel.idChannel]
    by_cases hbb : b' = b
    · subst hbb; rw [Dist.pure_apply_self, Dist.pure_apply_self]
    · rw [Dist.pure_apply_ne (eA.symm b) (eA.symm b') (fun h => hbb (eA.symm.injective h)),
        Dist.pure_apply_ne b b' hbb]
  have hUA : Relabeling.relabelChannel eA (Equiv.refl PUnit.{u+1})
      (Channel.uninformativeChannelU A) = UB :=
    relabelChannel_uninformative_action eA
  have transport : ∀ (s : Dist A),
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV
          (Relabeling.relabelDist eA s) ηB =
        (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV s ηA := by
    intro s
    show ηB (hint.marginalValue F hV (Relabeling.relabelDist eA s)) =
      ηA (hint.marginalValue F hV s)
    simp only [hηB_def, hηA_def, posteriorLawDifferenceExp,
      posteriorLawIntegralExp_experimentOfChannel]
    have t1 :
        posteriorLawIntegral (Relabeling.relabelDist eA r)
            (Relabeling.relabelChannel eA eA (Channel.idChannel : Channel A A))
            (hint.marginalValue F hV (Relabeling.relabelDist eA s)) =
          posteriorLawIntegral r (Channel.idChannel : Channel A A)
            (hint.marginalValue F hV s) :=
      (posteriorLawIntegral_relabelChannel eA eA r (Channel.idChannel : Channel A A)
        (hint.marginalValue F hV (Relabeling.relabelDist eA s))).trans
        (by refine congrArg _ ?_; funext d; exact hint.marginalValue_relabel F hV eA s d)
    have t2 :
        posteriorLawIntegral (Relabeling.relabelDist eA r)
            (Relabeling.relabelChannel eA (Equiv.refl PUnit.{u+1})
              (Channel.uninformativeChannelU A))
            (hint.marginalValue F hV (Relabeling.relabelDist eA s)) =
          posteriorLawIntegral r (Channel.uninformativeChannelU A)
            (hint.marginalValue F hV s) :=
      (posteriorLawIntegral_relabelChannel eA (Equiv.refl PUnit.{u+1}) r
        (Channel.uninformativeChannelU A)
        (hint.marginalValue F hV (Relabeling.relabelDist eA s))).trans
        (by refine congrArg _ ?_; funext d; exact hint.marginalValue_relabel F hV eA s d)
    rw [hidA] at t1
    rw [hUA] at t2
    rw [t1, t2]
  have hLA_r :
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV r ηA =
        hV.V r (experimentOfChannel idA) - hV.V r (experimentOfChannel UA) := by
    show ηA (hint.marginalValue F hV r) = _
    rw [hint.value_eq_integral F hV r (experimentOfChannel idA),
        hint.value_eq_integral F hV r (experimentOfChannel UA)]
    simp only [hηA_def, posteriorLawDifferenceExp, posteriorLawIntegralExp_experimentOfChannel]
  have hstrict := branch_id_uninformativeU_experiment_strict_of_A1 F hax r hr hnotsubA
  have hVne : hV.V r (experimentOfChannel idA) ≠ hV.V r (experimentOfChannel UA) :=
    branch_value_ne_of_strict_experiment_pref F hV r hr _ _ hstrict.1 hstrict.2
  have hT3 :
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV r ηA ≠ 0 := by
    rw [hLA_r]; exact sub_ne_zero.mpr hVne
  have relA := hpath.linear_part_scalar_relation_on_tangent q r hq hr hnd ηA hηA_atomic hηA_tan
  have relB := hpath.linear_part_scalar_relation_on_tangent
    (Relabeling.relabelDist eA q) (Relabeling.relabelDist eA r) hqB hrB hndB ηB hηB_atomic hηB_tan
  have hT1 :
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV
          (Relabeling.relabelDist eA q) ηB =
        (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV q ηA :=
    transport q
  have hT2 :
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV
          (Relabeling.relabelDist eA r) ηB =
        (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV r ηA :=
    transport r
  rw [hT1, hT2, relA] at relB
  have hEq : hpath.branchPathCoeff (Relabeling.relabelDist eA q) (Relabeling.relabelDist eA r) *
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV r ηA =
      hpath.branchPathCoeff q r *
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV r ηA := by
    linarith [relA, relB]
  exact mul_right_cancel₀ hT3 hEq

/--
**Entropy reduction from interaction collapse.**

Paper Lemma faddeevsketch, entropy-reduction part: once the universal chain
scale is available, the entropy-reduction identity is the already proved
`value_entropy_reduction_of_scale` applied to the `scale_coherence` field.
-/
noncomputable def EntropyReductionRepresentation_of_interactionCollapse
    {F : PrefFamily.{u}}
    (h : InteractionCollapseUniversalChainScaleStructure F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_scale F h.scale_coherence

/--
**Scaled cross-prior blockbridge from the pre-universal unscaled bridge.**

Paper Lemma blockbridge, rescaled (TeX lines 1776–1827, 2547–2557).  The
unscaled bridge is stated for the face-scale value functional; the hypothesis
`hagg` records that the entropy-reduction representation carries the same
branch-aggregation structure (definitional for the pre-entropy closure
constructors).  Division by the universal positive scale then mirrors
`crossPriorBlockRepresentation_of_unscaled` without consuming the
`FiniteCrossPriorBlockAssumptions` monolith.
-/
noncomputable def crossPriorBlockRepresentation_of_preUniversalBridge
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbridge : FinitePreUniversalCrossPriorBlockBridgeFor hfaces)
    (hax : TraceAxioms F)
    (hentropy : EntropyReductionRepresentation F)
    (hagg :
      hentropy.scale_coherence.branch_agg =
        hfaces.branch_result.branch_agg) :
    CrossPriorBlockRepresentation F where
  entropy_reduction := hentropy
  cross_prior_block_rep := by
    intro A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P Q
    have hraw := hbridge.unscaled_cross_prior_block_rep hax q r hq hr P Q
    rw [hagg, hraw]
    have hscale :
        hentropy.scale_coherence.scale q = hentropy.scale_coherence.scale r :=
      hentropy.scale_coherence.scale_universal q r hq hr
    have hpos : 0 < hentropy.scale_coherence.scale q :=
      hentropy.scale_coherence.scale_pos q hq
    rw [← hscale]
    exact (div_le_div_iff_of_pos_right hpos).symm

/--
**Entropy reduction from the pre-entropy-ready construction object.**

Composes `InteractionCollapseUniversalScale_of_preEntropyReady` with the
internal `ScaleCoherenceStructure → EntropyReductionRepresentation` bridge.
-/
noncomputable def entropyReduction_of_preEntropyReady
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hax : TraceAxioms F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_interactionCollapse
    (InteractionCollapseUniversalScale_of_preEntropyReady hready hhm huniq hax)

/--
**Scaled cross-prior blockbridge from the pre-entropy-ready construction
object.**

The interaction-collapse constructor builds its `ScaleCoherenceStructure` with
`branch_agg := hready.hfaces.branch_result.branch_agg`, so the value functional
of the resulting entropy-reduction representation is definitionally the
face-scale value functional of `hready.cross_prior_blockbridge`; the alignment
hypothesis is discharged by `rfl`.
-/
noncomputable def crossPriorBlockRepresentation_of_preEntropyReady
    {F : PrefFamily.{u}}
    (hready : PreEntropyReadyFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hax : TraceAxioms F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_preUniversalBridge
    hready.cross_prior_blockbridge hax
    (entropyReduction_of_preEntropyReady hready hhm huniq hax)
    rfl

/-!
## Stage ER-B: Entropy regularity for the concrete entropy candidate

`EntropyRegularity` (nonnegativity + singleton-zero) is proved for any
cross-prior block representation whose `Hfun` is the full-revelation
normalized value (definitional for every constructor in this file).

* nonnegativity at full support: A4 (outcome-postprocessing aversion) with
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
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    0 ≤ normalizedValue hcross.entropy_reduction.scale_coherence q
      Channel.idChannel := by
  have ha4 :=
    hax.a4 (Channel.idChannel : Channel A A)
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
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
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
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
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
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
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
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hax : TraceAxioms F) :
    EntropyRegularity F
      (crossPriorBlockRepresentation_of_preEntropyReady
        hready hhm huniq hax).entropy_reduction :=
  entropyRegularity_of_crossPrior_boundary hnorm hax _ (fun _ => rfl)

/-!
## Stage ER-D: concrete Faddeev-recursion inputs

The legacy recursion-input structures in `Faddeev.lean` quantify over an
arbitrary `EntropyReductionRepresentation`.  The closed pre-entropy route
constructs a specific representation, with `Hfun` definitionally equal to the
full-revelation normalized value.  The declarations below target that concrete
representation rather than strengthening the old public structures.
-/

/-- Entropy reduction produced by the minimal full pre-entropy closure route. -/
noncomputable def entropyReduction_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_interactionCollapse
    (InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax)

/-- Cross-prior block representation produced by the minimal full
pre-entropy closure route and the product-quasi-additive blockbridge. -/
noncomputable def crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_preUniversalBridge
    (finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod)
    hax
    (entropyReduction_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax)
    rfl

/-- Entropy regularity for the minimal full pre-entropy closure route. -/
theorem entropyRegularity_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    EntropyRegularity F
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax).entropy_reduction :=
  entropyRegularity_of_crossPrior_boundary
    (normalizedValueSupportBoundary_of_cardinalBoundary hcard) hax _ (fun _ => rfl)

/-- The positive support of a block-embedded fibre distribution is equivalent
to the fibre's positive support. -/
noncomputable def blockEmbedSupportEquiv
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (k : K) (q : Dist (Act k)) :
    supportSubtype (blockEmbedDist Act k q) ≃ supportSubtype q where
  toFun b := by
    rcases b with ⟨ka, hb⟩
    rcases ka with ⟨j, a⟩
    have hjk : j = k := by
      by_contra hne
      have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
        blockEmbedDist_apply_ne Act hne q a
      rw [hzero] at hb
      linarith
    subst j
    exact ⟨a, by simpa using hb⟩
  invFun a := ⟨⟨k, a.1⟩, by simpa using a.2⟩
  left_inv b := by
    rcases b with ⟨ka, hb⟩
    rcases ka with ⟨j, a⟩
    have hjk : j = k := by
      by_contra hne
      have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
        blockEmbedDist_apply_ne Act hne q a
      rw [hzero] at hb
      linarith
    subst j
    rfl
  right_inv a := by
    rfl

/-- Support restriction of a block-embedded distribution is the relabeling of
the intrinsic support-restricted fibre distribution. -/
theorem restrict_blockEmbed_eq_relabel_support
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (k : K) (q : Dist (Act k)) :
    (blockEmbedDist Act k q).restrictToSupport =
      Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
        q.restrictToSupport := by
  ext b
  rcases b with ⟨ka, hb⟩
  rcases ka with ⟨j, a⟩
  have hjk : j = k := by
    by_contra hne
    have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
      blockEmbedDist_apply_ne Act hne q a
    rw [hzero] at hb
    linarith
  subst j
  simp [Relabeling.relabelDist, blockEmbedSupportEquiv, Dist.restrictToSupport_apply]

/-- Pointwise formula for pushing a support-face distribution back to the
ambient action type by support inclusion. -/
theorem actionPushforward_supportIncludeKernel_apply
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (t : Dist (supportSubtype q)) (a : A) :
    Channel.actionPushforward t (supportIncludeKernel q) a =
      if h : q a > 0 then t ⟨a, h⟩ else 0 := by
  unfold Channel.actionPushforward supportIncludeKernel
  change (∑ c : supportSubtype q, t c * (Dist.pure c.1) a) =
    if h : q a > 0 then t ⟨a, h⟩ else 0
  by_cases hqa : q a > 0
  · rw [dif_pos hqa]
    let b : supportSubtype q := ⟨a, hqa⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro c _ hc
      have hne : c.1 ≠ a := by
        intro hca
        apply hc
        exact Subtype.ext hca
      rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · rw [dif_neg hqa]
    apply Finset.sum_eq_zero
    intro c _
    have hne : c.1 ≠ a := by
      intro hca
      exact hqa (hca ▸ c.2)
    rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]

/-- **Inclusion pushforward of a signed posterior law.**

A signed law on the support face `supportSubtype r` is pushed to the ambient
action type `A` by precomposing test functions with the support inclusion.  This
is the tangent-space map `i_ι` in the paper's face-scale argument. -/
noncomputable def pushSignedIncl {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (η : PosteriorLawSigned (supportSubtype r)) : PosteriorLawSigned A :=
  fun φ => η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))

/-- The inclusion pushforward preserves the atomic-linear witness: push each
atom's point along the support inclusion. -/
noncomputable def atomicLinear_pushSignedIncl {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    {η : PosteriorLawSigned (supportSubtype r)}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (pushSignedIncl r η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i => Channel.actionPushforward (hη.witness.point i) (supportIncludeKernel r)
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext φ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        φ (Channel.actionPushforward (hη.witness.point i) (supportIncludeKernel r))) =
      η (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))
    have h := congrFun hη.eval_eq
      (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- The inclusion pushforward preserves tangency (zero mass, zero barycentre). -/
theorem pushSignedIncl_tangent {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    {η : PosteriorLawSigned (supportSubtype r)}
    (hη : PosteriorLawSigned.AtomicLinear η)
    (htan : PosteriorLawTangent η) :
    PosteriorLawTangent (pushSignedIncl r η) := by
  refine ⟨?_, ?_⟩
  · show η (fun _ => (1:ℝ)) = 0
    exact htan.1
  · intro a
    show η (fun d => (Channel.actionPushforward d (supportIncludeKernel r)) a) = 0
    by_cases ha : r a > 0
    · have heq :
          (fun d : Dist (supportSubtype r) =>
            (Channel.actionPushforward d (supportIncludeKernel r)) a) =
          (fun d : Dist (supportSubtype r) => d ⟨a, ha⟩) := by
        funext d; rw [actionPushforward_supportIncludeKernel_apply, dif_pos ha]
      rw [heq]; exact htan.2 ⟨a, ha⟩
    · have heq :
          (fun d : Dist (supportSubtype r) =>
            (Channel.actionPushforward d (supportIncludeKernel r)) a) =
          (fun _ => (0:ℝ)) := by
        funext d; rw [actionPushforward_supportIncludeKernel_apply, dif_neg ha]
      rw [heq]
      have h := congrFun hη.eval_eq (fun _ => (0:ℝ))
      rw [AtomicPosteriorSignedLaw.eval_apply] at h
      rw [← h]; simp

/-- The support of a support-included distribution is equivalent to the
distribution's intrinsic positive support. -/
noncomputable def supportIncludePushforwardSupportEquiv
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (t : Dist (supportSubtype q)) :
    supportSubtype (Channel.actionPushforward t (supportIncludeKernel q)) ≃
      supportSubtype t where
  toFun b := by
    rcases b with ⟨a, hb⟩
    have hqa : q a > 0 := by
      by_contra hnot
      have happly :=
        actionPushforward_supportIncludeKernel_apply q t a
      rw [happly, dif_neg hnot] at hb
      linarith
    refine ⟨⟨a, hqa⟩, ?_⟩
    have happly :=
      actionPushforward_supportIncludeKernel_apply q t a
    rw [happly, dif_pos hqa] at hb
    exact hb
  invFun b := by
    refine ⟨b.1.1, ?_⟩
    have happly :=
      actionPushforward_supportIncludeKernel_apply q t b.1.1
    rw [happly, dif_pos b.1.2]
    exact b.2
  left_inv b := by
    rcases b with ⟨a, hb⟩
    apply Subtype.ext
    rfl
  right_inv b := by
    rcases b with ⟨a, hb⟩
    apply Subtype.ext
    rfl

/-- Restricting a support-included distribution is the relabeling of the
intrinsic support restriction. -/
theorem restrict_supportInclude_eq_relabel_support
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (t : Dist (supportSubtype q)) :
    (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport =
      Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
        t.restrictToSupport := by
  ext b
  rcases b with ⟨a, hb⟩
  have hqa : q a > 0 := by
    by_contra hnot
    have happly :=
      actionPushforward_supportIncludeKernel_apply q t a
    rw [happly, dif_neg hnot] at hb
    linarith
  simp [Relabeling.relabelDist, supportIncludePushforwardSupportEquiv,
    Dist.restrictToSupport_apply, actionPushforward_supportIncludeKernel_apply,
    hqa]

/-- Full-support fibre block embedding preserves the concrete entropy
candidate of the minimal full pre-entropy closure route. -/
theorem Hfun_blockEmbed_fullSupport_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (k : K) (q : Dist (Act k)) (hq : q.FullSupport) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun
        (blockEmbedDist Act k q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun q := by
  change
    hfaces.branch_result.branch_agg.value_rep.V (blockEmbedDist Act k q)
        (experimentOfChannel
          (Channel.idChannel : Channel ((k : K) × Act k) ((k : K) × Act k))) /
      hfaces.branch_result.scale_factorization.scale (blockEmbedDist Act k q)
    =
    hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel
          (Channel.idChannel : Channel (Act k) (Act k))) /
      hfaces.branch_result.scale_factorization.scale q
  rw [hconv.block_value.block_face_value hax Act k q hq]
  rw [hconv.block_scale.block_face_scale hax Act k q hq]
  rfl

/-- Full-support relabeling invariance for the concrete entropy candidate
constructed by the minimal full pre-entropy closure route. -/
theorem Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun
        (Relabeling.relabelDist e q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun q := by
  have hq' : (Relabeling.relabelDist e q).FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  by_cases hA : Subsingleton A
  · haveI : Subsingleton A := hA
    haveI : Subsingleton B :=
      ⟨fun b₁ b₂ => by
        apply e.symm.injective
        exact Subsingleton.elim (e.symm b₁) (e.symm b₂)⟩
    have hV_left :
        hfaces.branch_result.branch_agg.value_rep.V
            (Relabeling.relabelDist e q)
            (experimentOfChannel
              (Channel.idChannel : Channel B B)) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hfaces.branch_result.branch_agg.value_rep
        (Relabeling.relabelDist e q) hq'
        (Channel.idChannel : Channel B B)
    have hV_right :
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel
              (Channel.idChannel : Channel A A)) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hfaces.branch_result.branch_agg.value_rep q hq
        (Channel.idChannel : Channel A A)
    change
      hfaces.branch_result.branch_agg.value_rep.V
          (Relabeling.relabelDist e q)
          (experimentOfChannel
            (Channel.idChannel : Channel B B)) /
        hfaces.branch_result.scale_factorization.scale
          (Relabeling.relabelDist e q)
      =
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel
            (Channel.idChannel : Channel A A)) /
        hfaces.branch_result.scale_factorization.scale q
    rw [hV_left, hV_right]
    simp
  · have hpos :
        FiniteProductScaleZPositiveAssumptionsFor hfaces hprod :=
      productScaleZpositive_of_sliceTransform hprod haff
    have hfull :
        FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces :=
      finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
        hhm huniq hpos
    have hV :
        fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) =
          fullRevelationValueForFaceScales hfaces q :=
      fullRevelationValueForFaceScales_relabel_eq_fullSupport
        hfull hax e q hq hA
    have hscale :
        hfaces.branch_result.scale_factorization.scale (Relabeling.relabelDist e q) =
          hfaces.branch_result.scale_factorization.scale q := by
      exact
        (InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hconv hax).scale_coherence.scale_universal
          (Relabeling.relabelDist e q) q hq' hq
    change
      fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) /
        hfaces.branch_result.scale_factorization.scale (Relabeling.relabelDist e q)
      =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q
    rw [hV, hscale]

/-- Embedding a distribution on a support face back into the ambient action
type preserves the concrete entropy candidate of the minimal full pre-entropy
closure route. -/
theorem Hfun_supportInclude_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    ∀ (t : Dist (supportSubtype q)),
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)) =
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun t := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  intro t
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax
  let hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hreg : EntropyRegularity F hcross.entropy_reduction :=
    entropyRegularity_of_fullPreEntropyClosure_minimal
      hcard hfaces hhm huniq hprod haff hconv hax
  let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
    hfunSupportRestriction_of_boundaryIdentity hnorm hid
  haveI :
      Nonempty (supportSubtype (Channel.actionPushforward t (supportIncludeKernel q))) :=
    supportSubtype_nonempty (Channel.actionPushforward t (supportIncludeKernel q))
  haveI : Nonempty (supportSubtype t) := supportSubtype_nonempty t
  have hleft :
      hcross.entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)) =
        hcross.entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport :=
    hhfun.Hfun_support_restrict F hax hcross hreg
      (Channel.actionPushforward t (supportIncludeKernel q))
  have hright :
      hcross.entropy_reduction.Hfun t =
        hcross.entropy_reduction.Hfun t.restrictToSupport :=
    hhfun.Hfun_support_restrict F hax hcross hreg t
  have hrestrict :
      (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport =
        Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
          t.restrictToSupport :=
    restrict_supportInclude_eq_relabel_support q t
  have hrel :
      hcross.entropy_reduction.Hfun
          (Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
            t.restrictToSupport) =
        hcross.entropy_reduction.Hfun t.restrictToSupport :=
    Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
      hhm huniq haff hconv hax
      (supportIncludePushforwardSupportEquiv q t).symm t.restrictToSupport
      (Dist.restrictToSupport_fullSupport t)
  calc
    hcross.entropy_reduction.Hfun
        (Channel.actionPushforward t (supportIncludeKernel q))
        = hcross.entropy_reduction.Hfun
            (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport := hleft
    _ = hcross.entropy_reduction.Hfun
          (Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
            t.restrictToSupport) := by rw [hrestrict]
    _ = hcross.entropy_reduction.Hfun t.restrictToSupport := hrel
    _ = hcross.entropy_reduction.Hfun t := hright.symm

/-- Block embedding preserves the concrete entropy candidate of the minimal
full pre-entropy closure route.  Boundary fibres are routed through the single
cardinal support-boundary interface and the support-face relabeling above. -/
theorem Hfun_blockEmbed_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (k : K) (q : Dist (Act k)) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun
        (blockEmbedDist Act k q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun q := by
  by_cases hq : q.FullSupport
  · exact Hfun_blockEmbed_fullSupport_of_fullPreEntropyClosure_minimal
      hhm huniq haff hconv hax Act k q hq
  · let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax
    let hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
      normalizedValueSupportBoundary_of_cardinalBoundary hcard
    let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
      hfunBoundaryIdentity_of_cardinalBoundary hcard
    let hreg : EntropyRegularity F hcross.entropy_reduction :=
      entropyRegularity_of_fullPreEntropyClosure_minimal
        hcard hfaces hhm huniq hprod haff hconv hax
    let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
      hfunSupportRestriction_of_boundaryIdentity hnorm hid
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    haveI : Nonempty (supportSubtype (blockEmbedDist Act k q)) :=
      supportSubtype_nonempty (blockEmbedDist Act k q)
    have hleft :
        hcross.entropy_reduction.Hfun (blockEmbedDist Act k q) =
          hcross.entropy_reduction.Hfun
            (blockEmbedDist Act k q).restrictToSupport :=
      hhfun.Hfun_support_restrict F hax hcross hreg (blockEmbedDist Act k q)
    have hright :
        hcross.entropy_reduction.Hfun q =
          hcross.entropy_reduction.Hfun q.restrictToSupport :=
      hhfun.Hfun_support_restrict F hax hcross hreg q
    have hrestrict :
        (blockEmbedDist Act k q).restrictToSupport =
          Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
            q.restrictToSupport :=
      restrict_blockEmbed_eq_relabel_support Act k q
    have hrel :
        hcross.entropy_reduction.Hfun
            (Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
              q.restrictToSupport) =
          hcross.entropy_reduction.Hfun q.restrictToSupport :=
      Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
        hhm huniq haff hconv hax
        (blockEmbedSupportEquiv Act k q).symm q.restrictToSupport
        (Dist.restrictToSupport_fullSupport q)
    calc
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k q)
          = hcross.entropy_reduction.Hfun
              (blockEmbedDist Act k q).restrictToSupport := hleft
      _ = hcross.entropy_reduction.Hfun
            (Relabeling.relabelDist (blockEmbedSupportEquiv Act k q).symm
              q.restrictToSupport) := by rw [hrestrict]
      _ = hcross.entropy_reduction.Hfun q.restrictToSupport := hrel
      _ = hcross.entropy_reduction.Hfun q := hright.symm

/-- Posterior-law integrals are preserved by support restriction for the
concrete entropy candidate of the minimal full pre-entropy closure route. -/
theorem posteriorLawIntegral_supportRestrict_Hfun_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O]
    (P : Channel A O) (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    posteriorLawIntegral q P
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun =
      posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hconv hax).entropy_reduction.Hfun := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax
  letI : DecidableEq O := Classical.decEq O
  have hsupport :=
    posteriorLawIntegral_restrictToSupport P q
      (fun d => hcross.entropy_reduction.Hfun d)
  rw [hsupport]
  unfold posteriorLawIntegral
  apply Finset.sum_congr rfl
  intro o _
  congr 1
  exact
    Hfun_supportInclude_of_fullPreEntropyClosure_minimal
      hcard hhm huniq haff hconv hax q
      (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)

/-- Coarse-reveal entropy reduction for the concrete entropy candidate of the
minimal full pre-entropy closure route. -/
theorem coarseReveal_entropyReduction_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax
    hcross.entropy_reduction.Hfun (sigmaDist p q) =
      normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
        (coarseRevealChannel Act) +
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
        hcross.entropy_reduction.Hfun := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax
  let s : Dist ((k : K) × Act k) := sigmaDist p q
  let C : Channel ((k : K) × Act k) K := coarseRevealChannel Act
  by_cases hs : s.FullSupport
  · have hER :=
      hcross.entropy_reduction.value_entropy_reduction s hs C
    have hER' :
        normalizedValue hcross.entropy_reduction.scale_coherence s C =
          hcross.entropy_reduction.Hfun s -
            posteriorLawIntegral s C hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    linarith
  · let hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
      normalizedValueSupportBoundary_of_cardinalBoundary hcard
    let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
      hfunBoundaryIdentity_of_cardinalBoundary hcard
    let hreg : EntropyRegularity F hcross.entropy_reduction :=
      entropyRegularity_of_fullPreEntropyClosure_minimal
        hcard hfaces hhm huniq hprod haff hconv hax
    let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
      hfunSupportRestriction_of_boundaryIdentity hnorm hid
    haveI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
    have hH :
        hcross.entropy_reduction.Hfun s =
          hcross.entropy_reduction.Hfun s.restrictToSupport :=
      hhfun.Hfun_support_restrict F hax hcross hreg s
    have hV :
        normalizedValue hcross.entropy_reduction.scale_coherence s C =
          normalizedValue hcross.entropy_reduction.scale_coherence
            s.restrictToSupport (Channel.restrictToSupport C s) :=
      normalizedValue_support_restrict_of_boundary hnorm F hax hcross C s
    have hI :
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun =
          posteriorLawIntegral s.restrictToSupport (Channel.restrictToSupport C s)
            hcross.entropy_reduction.Hfun :=
      posteriorLawIntegral_supportRestrict_Hfun_of_fullPreEntropyClosure_minimal
        hcard hhm huniq haff hconv hax C s
    have hER :=
      hcross.entropy_reduction.value_entropy_reduction
        s.restrictToSupport (Dist.restrictToSupport_fullSupport s)
        (Channel.restrictToSupport C s)
    have hER' :
        normalizedValue hcross.entropy_reduction.scale_coherence
            s.restrictToSupport (Channel.restrictToSupport C s) =
          hcross.entropy_reduction.Hfun s.restrictToSupport -
            posteriorLawIntegral s.restrictToSupport
              (Channel.restrictToSupport C s)
              hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    rw [hH, hV, hI]
    linarith

/-- Finite Faddeev recursion for the concrete entropy candidate produced by
the minimal full pre-entropy closure route. -/
theorem satisfiesFiniteFaddeevRecursion_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax
  let hnorm : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u} :=
    restrictedCoarseRevealValue_of_cardinalBoundary hcard
  let hreg : EntropyRegularity F hcross.entropy_reduction :=
    entropyRegularity_of_fullPreEntropyClosure_minimal
      hcard hfaces hhm huniq hprod haff hconv hax
  let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
    hfunSupportRestriction_of_boundaryIdentity hnorm hid
  change SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun
  intro K _ _ _ Act _ _ _ _ p q
  have hER :=
    coarseReveal_entropyReduction_of_fullPreEntropyClosure_minimal
      (hcard := hcard) (hhm := hhm) (huniq := huniq)
      (haff := haff) (hconv := hconv) (hax := hax)
      (Act := Act) (p := p) (q := q)
  have hV :=
    coarseReveal_value_eq_Hfun_of_axioms
      hnorm hhfun hrestricted F hax hcross hreg Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) := by
    exact posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k =>
        Hfun_blockEmbed_of_fullPreEntropyClosure_minimal
          (hcard := hcard) (hhm := hhm) (huniq := huniq)
          (haff := haff) (hconv := hconv) (hax := hax)
          (Act := Act) (k := k) (q := q k))
  change hcross.entropy_reduction.Hfun (sigmaDist p q) =
    hcross.entropy_reduction.Hfun p +
      ∑ k, p k * hcross.entropy_reduction.Hfun (q k)
  rw [hER, hV, hInt]

/-- `FaddeevRecursionForm` for the concrete entropy candidate produced by the
minimal full pre-entropy closure route. -/
theorem faddeevRecursionForm_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hconv hax
    FaddeevRecursionForm F hcross.entropy_reduction := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax
  exact
    { regularity :=
        entropyRegularity_of_fullPreEntropyClosure_minimal
          hcard hfaces hhm huniq hprod haff hconv hax
      grouping_recursion :=
        satisfiesFiniteFaddeevRecursion_of_fullPreEntropyClosure_minimal
          (hcard := hcard) (hhm := hhm) (huniq := huniq)
          (haff := haff) (hconv := hconv) (hax := hax) }

/-- `FaddeevEntropyForm` for the concrete entropy candidate produced by the
minimal full pre-entropy closure route.  The only Faddeev/Shannon input is the
classical finite Faddeev theorem interface. -/
noncomputable def FaddeevEntropyForm_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    FaddeevEntropyForm F := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hconv hax
  let hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    faddeevRecursionForm_of_fullPreEntropyClosure_minimal
      (hcard := hcard) (hhm := hhm) (huniq := huniq)
      (haff := haff) (hconv := hconv) (hax := hax)
  let hex := hfad.of_recursion F hrecForm
  let alpha := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hH :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        hcross.entropy_reduction.Hfun q = alpha * H(q) :=
    hspec.2
  have hHfun_pos :
      0 < hcross.entropy_reduction.Hfun
        (Dist.uniform (A := ULift.{u, 0} Bool)) :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrecForm
  exact
    { cross_prior := hcross
      alpha := alpha
      alpha_pos :=
        alpha_strict_pos_of_positive_Hfun_witness
          F hax hcross hrecForm hHfun_pos alpha hH
      H_eq_alpha_shannon := hH
      a3_block_equivalence := a3_block_equivalence_of_traceAxioms F hax }

/-- Same Faddeev/Shannon interface as
`FaddeevEntropyForm_of_fullPreEntropyClosure_minimal`, with affine uniqueness
filled by the internal finite uniqueness theorem. -/
noncomputable def FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    FaddeevEntropyForm F :=
  FaddeevEntropyForm_of_fullPreEntropyClosure_minimal
    (hcard := hcard) (hfad := hfad) (hhm := hhm)
    (huniq := classicalFiniteAffineUtilityUniquenessAssumptions)
    (haff := haff) (hconv := hconv) (hax := hax)

/-- Full-support MI representation package obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem fullSupportSufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    FullSupportSufficiencyMIPackage F :=
  FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F
    (FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hconv := hconv) (hax := hax))

/-- Full-support block MI representation package obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem fullSupportBlockMI_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    FullSupportBlockMI F :=
  FullSupportBlockMI_of_FaddeevEntropyForm F
    (FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hconv := hconv) (hax := hax))

/-- Boundary extension for MI representation obtained internally from the
support-restriction theorem and the full-support block MI package. -/
theorem fullSupportMIRepExtendsToBoundary_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    FullSupportMIRepExtendsToBoundary F :=
  FullSupportMIRepExtendsToBoundary_of_supportRestriction F
    (fullSupportBlockMI_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hconv := hconv) (hax := hax))

/-- Final sufficiency package obtained from the closed pre-entropy spine,
internal boundary extension, and the classical finite Faddeev theorem
interface. -/
theorem sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    SufficiencyMIPackage F :=
  (fullSupportMIRepExtendsToBoundary_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard := hcard) (hfad := hfad) (hhm := hhm)
    (haff := haff) (hconv := hconv) (hax := hax))
    hax
    (fullSupportSufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hconv := hconv) (hax := hax))

/-- Final mutual-information representation obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem MIRep_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hconv : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hax : TraceAxioms F) :
    MIRep F :=
  MIRep_of_SufficiencyMIPackage F
    (sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hconv := hconv) (hax := hax))

/-- Left-slice affine transform for the selected face-scale representative
from HM public-mixture affinity, A8 same-order transport, internal finite
affine-utility uniqueness, and the singleton slice convention. -/
theorem finiteFaceScaleProductLeftSliceAffineTransform_of_HM
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hsingle : FiniteFaceScaleSingletonSliceAffineConventionFor hfaces) :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces :=
  faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
    (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
    (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
    (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
    hsingle
    classicalFiniteAffineUtilityUniquenessAssumptions

/-- Harmless conventions still needed after the final MI assembly.

The pre-entropy representative/gauge bundle fixes support-face representatives,
product-reference `Z`, and singleton universal scale.  The singleton slice field
fixes the degenerate one-action left-slice affine normalization.

The boundary support-restriction field (`FiniteCardinalSupportBoundaryAssumptions`)
has been **removed**: its content is now proved rather than assumed
(`field1_boundaryComplete`, `hfun_eq_normalizedValue_idChannel_of_scale`,
`field3_restricted_coarse_reveal`), and the final MI route goes through
`MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal`. -/
structure FinalHarmlessConventions
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  singleton_slice :
    FiniteFaceScaleSingletonSliceAffineConventionFor hfaces
  pre_entropy :
    PreEntropyRepresentativeGaugeConventions hfaces hprod

/-- Affine linear-part package supplied by the HM component of the final
interface. -/
noncomputable def affineLinearPart_of_FinalHMInterface
    (hhm : FinalHMInterface.{u}) :
    FiniteAffineLinearPartAssumptions.{u} :=
  finiteAffineLinearPartAssumptions_of_HM
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)

/-- Posterior integral representation supplied by the HM component of the
final interface. -/
noncomputable def posteriorIntegralRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u}) :
    FinitePosteriorIntegralRepresentationAssumptions.{u} :=
  finitePosteriorIntegralRepresentation_of_HM
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)

/-- Boundary linear-part transport from the HM integral representation plus the
support-face marginal-value transport convention. -/
theorem boundaryLinearPartTransport_of_FinalHM_marginalConvention
    (hhm : FinalHMInterface.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportConvention
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        hboundary) :
    FiniteBoundaryLinearPartTransportAssumptions
      (affineLinearPart_of_FinalHMInterface hhm)
      hboundary :=
  boundaryLinearPartTransport_of_integralRepresentation
    (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
    hboundary hmarginal

/-- Faithful branch package with the internal HM/finite-linear-algebra fields
filled automatically.

The remaining inputs are exactly the boundary/support representative choices
and the boundary/singleton scale-factorization transports.  This exposes more
of the proof order than passing an opaque `FiniteFaithfulBranchAggregationAssumptions`
bundle. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_components
    (hhm : FinalHMInterface.{u})
    (hatomic : FiniteAtomicPosteriorTangentSpanningAssumptions.{u})
    (hsupportFace : FiniteSupportFaceRepresentativeConventionAssumptions.{u})
    (hboundaryCoeff : FiniteBoundaryCoefficientScaleConventionAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleConventionAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportConvention
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        (boundaryFaceScale_of_coefficientScaleConvention hboundaryCoeff))
    (hboundaryScale :
      ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic hatomic) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleConvention hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeConvention
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalConvention
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationBoundaryTransportAssumptions
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff))
    (hsingleScale :
      ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic hatomic) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleConvention hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeConvention
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalConvention
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationSingletonConvention
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    FiniteFaithfulBranchAggregationAssumptions.{u} where
  linear_part := affineLinearPart_of_FinalHMInterface hhm
  tangent_spanning := atomicLinearTangentSpanning_of_atomic hatomic
  same_sign_scalar := finiteLinearFunctionalSameSignScalarOnTangent_of_direct
  support_face_rep := hsupportFace
  boundary_coeff_scale := hboundaryCoeff
  singleton_scale := hsingle
  boundary_linear_transport :=
    boundaryLinearPartTransport_of_FinalHM_marginalConvention
      hhm (boundaryFaceScale_of_coefficientScaleConvention hboundaryCoeff)
      hmarginal
  boundary_scale_factorization := hboundaryScale
  singleton_scale_factorization := hsingleScale

/-- Faithful branch package from the final HM interface and explicit
support/boundary conventions, with finite atomic tangent spanning discharged by
the internal theorem `finiteAtomicPosteriorTangentSpanning`. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_conventions
    (hhm : FinalHMInterface.{u})
    (hsupportFace : FiniteSupportFaceRepresentativeConventionAssumptions.{u})
    (hboundaryCoeff : FiniteBoundaryCoefficientScaleConventionAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleConventionAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportConvention
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        (boundaryFaceScale_of_coefficientScaleConvention hboundaryCoeff))
    (hboundaryScale :
      ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic
              finiteAtomicPosteriorTangentSpanning) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleConvention hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeConvention
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalConvention
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationBoundaryTransportAssumptions
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff))
    (hsingleScale :
      ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic
              finiteAtomicPosteriorTangentSpanning) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleConvention hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeConvention
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalConvention
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationSingletonConvention
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    FiniteFaithfulBranchAggregationAssumptions.{u} :=
  faithfulBranchAggregationAssumptions_of_FinalHM_components
    hhm finiteAtomicPosteriorTangentSpanning
    hsupportFace hboundaryCoeff hsingle hmarginal
    hboundaryScale hsingleScale

/-- Harmless support/boundary/singleton conventions needed to build the
faithful branch package from the data-carrying HM interface.

These fields only choose support-face representatives, boundary coefficient
scales, singleton normalisations, and the corresponding support-restricted
scale transports; the finite tangent-spanning and same-sign linear-algebra
content is proved internally. -/
structure FinalFaithfulBranchConventions
    (hhm : FinalHMInterface.{u}) where
  support_face : FiniteSupportFaceRepresentativeConventionAssumptions.{u}
  boundary_coeff : FiniteBoundaryCoefficientScaleConventionAssumptions.{u}
  singleton_scale : FiniteBranchSingletonScaleConventionAssumptions.{u}
  marginal_value :
    FiniteSupportFaceMarginalValueTransportConvention
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleConvention boundary_coeff)
  boundary_scale :
    ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
      (hV : PosteriorValueRepresentation F),
      let hlin := affineLinearPart_of_FinalHMInterface hhm
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
          (atomicLinearTangentSpanning_of_atomic
            finiteAtomicPosteriorTangentSpanning) F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleConvention boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeConvention
          support_face
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalConvention
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary singleton_scale hvalue hcoeff)
  singleton_scale_factorization :
    ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
      (hV : PosteriorValueRepresentation F),
      let hlin := affineLinearPart_of_FinalHMInterface hhm
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
          (atomicLinearTangentSpanning_of_atomic
            finiteAtomicPosteriorTangentSpanning) F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleConvention boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeConvention
          support_face
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalConvention
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationSingletonConvention
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary singleton_scale hvalue hcoeff)

/-- Producer from the explicit faithful-branch convention bundle. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
    (hhm : FinalHMInterface.{u})
    (hconv : FinalFaithfulBranchConventions hhm) :
    FiniteFaithfulBranchAggregationAssumptions.{u} :=
  faithfulBranchAggregationAssumptions_of_FinalHM_conventions
    hhm hconv.support_face hconv.boundary_coeff hconv.singleton_scale
    hconv.marginal_value hconv.boundary_scale
    hconv.singleton_scale_factorization

/-- **R1: raw chain-scale relabelling invariance from the HM covariance clause.**

The faithful branch chain scale is `scale q = branchCoeff q u_A` (the branch
coefficient to the uniform prior).  Relabelling carries `u_A` to `u_B`
(`Fintype.card_congr`), the full-support branch coefficient equals the tangent
scalar `branchPathCoeff`, and `branchPathCoeff` is relabel-invariant
(`branchPathCoeff_relabel_of_marginalValue_relabel`).  On a subsingleton action
type both coefficients are the degenerate value `1`.  This discharges the raw
form of the `scale_relabel` gauge convention (under the constant gauge). -/
theorem scaleRelabel_of_FinalHM_covariance
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Relabeling.relabelDist e q) =
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale q := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
    with hfaith_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
    with hpath_def
  have hscale_eq : ∀ (C : Type u) [Fintype C] [DecidableEq C] [Nonempty C] (s : Dist C),
      (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).scale_factorization.scale s =
      hpath.branchPathCoeff s (Dist.uniform (A := C)) := by
    intro C _ _ _ s
    show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).branch_agg.branchCoeff s (Dist.uniform (A := C)) = _
    rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff s (Dist.uniform (A := C)) =
      branchCoeffFromTangentRepParts hpath
        (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
        hfaith.singleton_scale s (Dist.uniform (A := C)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  rw [hscale_eq B (Relabeling.relabelDist e q), hscale_eq A q]
  have huni : Relabeling.relabelDist e (Dist.uniform (A := A)) = Dist.uniform (A := B) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply, Fintype.card_congr e]
  by_cases hA : Subsingleton A
  · have hqfsB : (Relabeling.relabelDist e q).FullSupport :=
      Relabeling.relabelDist_fullSupport e q hq
    have h1A : hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      have hnn : ¬ ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hab, _, _⟩; exact hab (Subsingleton.elim a b)
      rw [hpath_def]
      simp only [branchPathTangentScalarStructure_of_faithfulAssumptions,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hq, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    have h1B : hpath.branchPathCoeff (Relabeling.relabelDist e q) (Dist.uniform (A := B)) = 1 := by
      have hnn : ¬ ∃ a b : B, a ≠ b ∧ 0 < (Dist.uniform (A := B)) a ∧
          0 < (Dist.uniform (A := B)) b := by
        haveI : Subsingleton B := Equiv.subsingleton e.symm
        rintro ⟨a, b, hab, _, _⟩; exact hab (Subsingleton.elim a b)
      rw [hpath_def]
      simp only [branchPathTangentScalarStructure_of_faithfulAssumptions,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hqfsB, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    rw [h1B, h1A]
  · have hndU : ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
      rw [not_subsingleton_iff_nontrivial] at hA
      obtain ⟨a, b, hab⟩ := hA
      exact ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
    rw [← huni]
    exact branchPathCoeff_relabel_of_marginalValue_relabel
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm) hax hV hpath e q
      (Dist.uniform (A := A)) hq Dist.uniform_fullSupport hndU

/-- **R2a: prior-independence of the boundary embedding defect.**

For a fixed boundary posterior `r` and two full-support ambient priors `q, q'`,
the boundary coefficients satisfy
`boundaryCoeff q r · branchPathCoeff q' q = boundaryCoeff q' r`.
Equivalently `boundaryCoeff q r / scale q` is independent of `q` (paper: the
embedding defect `K(ι)` does not depend on the ambient prior).  The proof uses
the support-face marginal-value transport (which pins each `boundaryCoeff`), the
full-support tangent-scalar relation applied to the *pushed* support-face tangent
(`pushSignedIncl`), and cancellation of the A1-nonzero support-face tangent.  It
does **not** use the cross-prior block bridge, so the defect is definable
non-circularly. -/
theorem boundaryCoeff_qIndep_of_FinalHM
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      ).boundaryCoeff q r *
      (branchPathTangentScalarStructure_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q' q =
    (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      ).boundaryCoeff q' r := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
    with hfaith_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
    with hpath_def
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hint_def
  set hboundary := branchBoundaryFaceScale_of_faithfulAssumptions hfaith with hbdef
  have hrs_fs : (r.restrictToSupport).FullSupport := Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h; exact hab (congrArg Subtype.val h)
    · rw [Dist.restrictToSupport_apply]; exact ha
    · rw [Dist.restrictToSupport_apply]; exact hb
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hfaith.linear_part F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have htrans := hbranchConv.marginal_value.support_face_marginalValue_scalar
  have hTq := htrans F hax hV q r hq hrn hrnd hrb η hηtan
  have hTq' := htrans F hax hV q' r hq' hrn hrnd hrb η hηtan
  have hpush_atomic := atomicLinear_pushSignedIncl r hηatomic
  have hpush_tan := pushSignedIncl_tangent r hηatomic hηtan
  have hrel := hpath.linear_part_scalar_relation_on_tangent q' q hq' hq
    (by obtain ⟨a, b, hab, _, _⟩ := hrnd; exact ⟨a, b, hab, hq a, hq b⟩)
    (pushSignedIncl r η) hpush_atomic hpush_tan
  have hLq : hfaith.linear_part.linearPart F hV q (pushSignedIncl r η) =
      hboundary.boundaryCoeff q r * η (hint.marginalValue F hV r.restrictToSupport) := hTq
  have hLq' : hfaith.linear_part.linearPart F hV q' (pushSignedIncl r η) =
      hboundary.boundaryCoeff q' r * η (hint.marginalValue F hV r.restrictToSupport) := hTq'
  rw [hLq, hLq'] at hrel
  have hLnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  have hstep : hboundary.boundaryCoeff q' r * η (hint.marginalValue F hV r.restrictToSupport) =
      (hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q) *
        η (hint.marginalValue F hV r.restrictToSupport) := by
    rw [hrel]; ring
  have hcancel := mul_right_cancel₀ hLnz hstep
  linarith [hcancel]

/-- Canonical `n`-element action type in `Type u` (for the cardinal gauge). -/
abbrev canonType (n : ℕ) : Type u := ULift.{u} (Fin n)

/-- The faithful chain scale of the uniform prior on the canonical `n`-element
action type.  By R1 (`scaleRelabel_of_FinalHM_covariance`) it equals the chain
scale of the uniform prior on *any* `n`-element type (`scale_uniform_eq_cardScale`
below), so it depends only on `n`.

**Caveat (not the cardinal gauge `t_n`).**  This value is in fact `1` for every
nondegenerate `n` (`scale (u_A) = branchCoeff (u_A) (u_A) = branchPathCoeff (u_A)
(u_A) = 1` by the full-support cocycle at `q = r = s = u_A`).  So it is a true but
degenerate quantity and is **not** the paper's cardinal gauge `t_n = K_{n,2}`,
which is a genuine cross-cardinality embedding defect.  The real `t_n` is defined
from `boundaryCoeff` on a canonical boundary prior (see the R2b plan in
`ELIMINATE_PRODUCT_NORMALIZED_PROGRESS.md`); `cardScale` is retained only as the
`scale (u_A)`-value bookkeeping lemma. -/
noncomputable def cardScale
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (n : ℕ) : ℝ :=
  if h : n = 0 then 1
  else
    haveI : NeZero n := ⟨h⟩
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := canonType.{u} n))

/-- The chain scale of the uniform prior depends only on the cardinality: it
equals `cardScale (card A)`.  Immediate from R1 via the equivalence
`A ≃ canonType (card A)`, which carries the uniform prior to the uniform prior. -/
theorem scale_uniform_eq_cardScale
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := A)) =
      cardScale hhm hbranchConv hax (Fintype.card A) := by
  classical
  have hcard0 : Fintype.card A ≠ 0 := Fintype.card_ne_zero
  rw [cardScale, dif_neg hcard0]
  haveI : NeZero (Fintype.card A) := ⟨hcard0⟩
  set e : A ≃ canonType.{u} (Fintype.card A) :=
    (Fintype.equivFin A).trans Equiv.ulift.symm with he
  have huni : Relabeling.relabelDist e (Dist.uniform (A := A)) =
      Dist.uniform (A := canonType.{u} (Fintype.card A)) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply]
    congr 1
    simp [canonType]
  rw [← huni]
  exact (scaleRelabel_of_FinalHM_covariance hhm hbranchConv hax e
    (Dist.uniform (A := A)) Dist.uniform_fullSupport).symm

/-! ### Canonical boundary priors for the cardinal-gauge (`t_n`) construction

`canonBoundary n m` is the uniform prior on the first `m` actions of the canonical
`n`-element type — the paper's canonical `m`-point face inside an `n`-point action
set.  The embedding defect `K_{n,m}` is read off from the boundary coefficient at
`(u_n, canonBoundary n m)`; the cocycle over nested faces yields `t_n`. -/

/-- Inclusion kernel `canonType m → canonType n` (m ≤ n) via `Fin.castLE`. -/
noncomputable def canonInclKernel (n m : ℕ) (hmn : m ≤ n) :
    Channel.ActionKernel (canonType.{u} m) (canonType.{u} n) :=
  fun a => Dist.pure (ULift.up (Fin.castLE hmn a.down))

/-- Canonical `m`-point boundary prior inside the `n`-point action set: the
uniform prior on `canonType m` pushed forward along the inclusion. -/
noncomputable def canonBoundary (n m : ℕ) (hmn : m ≤ n) [NeZero m] :
    Dist (canonType.{u} n) :=
  Channel.actionPushforward (Dist.uniform (A := canonType.{u} m)) (canonInclKernel n m hmn)

theorem canonBoundary_apply (n m : ℕ) (hmn : m ≤ n) [NeZero m] (j : Fin n) :
    (canonBoundary.{u} n m hmn) (ULift.up j) =
      if (j : ℕ) < m then (1 : ℝ) / m else 0 := by
  classical
  have hcard : Fintype.card (canonType.{u} m) = m := by simp [canonType]
  unfold canonBoundary canonInclKernel Channel.actionPushforward
  show (∑ a : canonType.{u} m, (Dist.uniform (A := canonType.{u} m)) a *
      (Dist.pure (ULift.up (Fin.castLE hmn a.down)) : Dist (canonType.{u} n)) (ULift.up j)) = _
  have hterm : ∀ a : canonType.{u} m,
      (Dist.pure (ULift.up (Fin.castLE hmn a.down)) : Dist (canonType.{u} n)) (ULift.up j) =
        if (a.down : ℕ) = (j : ℕ) then (1:ℝ) else 0 := by
    intro a
    by_cases h : (a.down : ℕ) = (j : ℕ)
    · rw [if_pos h]
      have : (ULift.up (Fin.castLE hmn a.down) : canonType.{u} n) = ULift.up j := by
        apply ULift.ext; apply Fin.ext; rw [Fin.val_castLE]; exact h
      rw [this, Dist.pure_apply_self]
    · rw [if_neg h, Dist.pure_apply_ne]
      intro hc
      apply h
      have : Fin.castLE hmn a.down = j := ULift.up.inj hc.symm
      rw [← Fin.val_castLE (h := hmn), this]
  simp only [hterm, Dist.uniform_apply, hcard, mul_ite, mul_one, mul_zero]
  by_cases hj : (j : ℕ) < m
  · rw [if_pos hj]
    rw [Finset.sum_eq_single (ULift.up (⟨(j:ℕ), hj⟩ : Fin m))]
    · rw [if_pos rfl]
    · intro b _ hb
      rw [if_neg]
      intro hc
      apply hb
      apply ULift.ext; apply Fin.ext; simpa using hc
    · intro hne; exact absurd (Finset.mem_univ _) hne
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro a _
    rw [if_neg]
    intro hc; exact hj (hc ▸ a.down.isLt)

theorem canonBoundary_pos (n m : ℕ) (hmn : m ≤ n) [NeZero m] (j : Fin n) :
    0 < (canonBoundary.{u} n m hmn) (ULift.up j) ↔ (j : ℕ) < m := by
  rw [canonBoundary_apply]
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  split
  · rename_i h; constructor
    · intro _; assumption
    · intro _
      have : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
      positivity
  · rename_i h; constructor
    · intro hc; exact absurd hc (lt_irrefl 0)
    · intro hc; exact absurd hc h

theorem canonBoundary_support_nonempty (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hn : 0 < n) :
    ∃ a : canonType.{u} n, 0 < (canonBoundary.{u} n m hmn) a := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  exact ⟨ULift.up ⟨0, hn⟩, (canonBoundary_pos n m hmn ⟨0, hn⟩).mpr hm⟩

theorem canonBoundary_nondeg (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m) :
    ∃ a b : canonType.{u} n, a ≠ b ∧
      0 < (canonBoundary.{u} n m hmn) a ∧ 0 < (canonBoundary.{u} n m hmn) b := by
  have h0 : (0:ℕ) < n := lt_of_lt_of_le (by omega) hmn
  have h1 : (1:ℕ) < n := lt_of_lt_of_le hm2 hmn
  refine ⟨ULift.up ⟨0, h0⟩, ULift.up ⟨1, h1⟩, ?_, ?_, ?_⟩
  · intro h
    rw [ULift.up.injEq] at h
    have : (0:ℕ) = 1 := Fin.val_eq_of_eq h
    exact absurd this (by norm_num)
  · exact (canonBoundary_pos n m hmn ⟨0, h0⟩).mpr (by show (0:ℕ) < m; omega)
  · exact (canonBoundary_pos n m hmn ⟨1, h1⟩).mpr (by show (1:ℕ) < m; omega)

theorem canonBoundary_boundary (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hmlt : m < n) :
    ¬ (canonBoundary.{u} n m hmn).FullSupport := by
  intro hfs
  have := hfs (ULift.up ⟨m, hmlt⟩)
  rw [canonBoundary_apply] at this
  simp at this

/-- The positive support of `canonBoundary n m` is the canonical `m`-element type. -/
noncomputable def canonBoundarySupportEquiv (n m : ℕ) (hmn : m ≤ n) [NeZero m] :
    supportSubtype (canonBoundary.{u} n m hmn) ≃ canonType.{u} m where
  toFun a := ULift.up ⟨(a.1.down : ℕ), by
    have := (canonBoundary_pos n m hmn a.1.down).mp (by simpa using a.2)
    simpa using this⟩
  invFun b := ⟨ULift.up (Fin.castLE hmn b.down), by
    show 0 < (canonBoundary n m hmn) (ULift.up (Fin.castLE hmn b.down))
    rw [canonBoundary_pos]; simpa using b.down.isLt⟩
  left_inv a := by apply Subtype.ext; apply ULift.ext; apply Fin.ext; simp
  right_inv b := by apply ULift.ext; apply Fin.ext; simp

/-- The faithful chain scale of the uniform prior on a nondegenerate action type
is `1`: `scale (u_A) = branchCoeff (u_A) (u_A) = branchPathCoeff (u_A) (u_A) = 1`
by the full-support tangent-scalar cocycle at `q = r = s = u_A`. -/
theorem scale_uniform_eq_one
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (hnd : ∃ a b : A, a ≠ b) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := A)) = 1 := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
  show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff (Dist.uniform (A := A)) (Dist.uniform (A := A)) = 1
  rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
    ).branch_agg.branchCoeff (Dist.uniform (A := A)) (Dist.uniform (A := A)) =
    branchCoeffFromTangentRepParts hpath
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
      hfaith.singleton_scale (Dist.uniform (A := A)) (Dist.uniform (A := A)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  have hcoc := branchCoeffTangentScalar_cocycle_fullSupport hfaith.linear_part F hax hV hpath
    (Dist.uniform (A := A)) (Dist.uniform (A := A)) (Dist.uniform (A := A))
    Dist.uniform_fullSupport Dist.uniform_fullSupport Dist.uniform_fullSupport hnd
  have hpos : 0 < hpath.branchPathCoeff (Dist.uniform (A := A)) (Dist.uniform (A := A)) := by
    obtain ⟨a, b, hab⟩ := hnd
    exact hpath.branchPathCoeff_pos _ _ Dist.uniform_fullSupport Dist.uniform_fullSupport
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  nlinarith [hcoc, hpos]

/-- The support-face of `canonBoundary n m` carries the uniform prior on its
`m`-element support (each surviving action has probability `1/m`). -/
theorem canonBoundary_face_uniform (n m : ℕ) (hmn : m ≤ n) [NeZero m]
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    (canonBoundary.{u} n m hmn).restrictToSupport =
      Dist.uniform (A := supportSubtype (canonBoundary.{u} n m hmn)) := by
  classical
  have hcard : Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) = m := by
    rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]; simp [canonType]
  ext a
  rw [Dist.restrictToSupport_apply, Dist.uniform_apply, hcard]
  obtain ⟨⟨j⟩, hj⟩ := a
  rw [canonBoundary_apply]
  have : (j : ℕ) < m := by
    have := (canonBoundary_pos n m hmn j).mp (by simpa using hj); simpa using this
  rw [if_pos this]

/-- The chain scale of the `canonBoundary n m` support-face is `1` (it is the
uniform prior on an `m ≥ 2`-element type; `scale_uniform_eq_one`). -/
theorem canonBoundary_face_scale_eq_one
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m)
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (canonBoundary.{u} n m hmn).restrictToSupport = 1 := by
  rw [canonBoundary_face_uniform n m hmn]
  have hnd : ∃ a b : supportSubtype (canonBoundary.{u} n m hmn), a ≠ b := by
    have hcard : Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) = m := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]; simp [canonType]
    have : 1 < Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) := by omega
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    exact ⟨a, b, hab⟩
  exact scale_uniform_eq_one hhm hbranchConv hax hnd

/-- **The embedding defect `K_{n,m}`** (`2 ≤ m ≤ n`): the boundary coefficient
from the uniform prior on the `n`-point action set to the canonical `m`-point
face.  Since both `scale (u_n)` and the face scale are `1`
(`scale_uniform_eq_one`, `canonBoundary_face_scale_eq_one`), this boundary
coefficient *is* the paper's embedding defect for the canonical inclusion.  The
cardinal gauge `t_n` is `cardDefect n 2`. -/
noncomputable def cardDefect
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (n m : ℕ) : ℝ :=
  if h : 2 ≤ m ∧ m ≤ n then
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
    ).boundaryCoeff (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m h.2)
  else 1

/-- The embedding defect is positive for `2 ≤ m < n`. -/
theorem cardDefect_pos
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (n m : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    0 < cardDefect hhm hbranchConv hax n m := by
  classical
  have hle : m ≤ n := le_of_lt hmn
  rw [cardDefect, dif_pos ⟨hm2, hle⟩]
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
  apply (branchBoundaryFaceScale_of_faithfulAssumptions
    (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)).boundaryCoeff_pos
  · exact Dist.uniform_fullSupport
  · exact canonBoundary_support_nonempty n m hle (by omega)
  · exact canonBoundary_nondeg n m hle hm2
  · exact canonBoundary_boundary n m hle hmn

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

theorem boundaryCoeff_relabel_of_FinalHM
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q r : Dist A)
    (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
    ).boundaryCoeff (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) =
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
    ).boundaryCoeff q r := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
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
  have hTqr := hbranchConv.marginal_value.support_face_marginalValue_scalar
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
  have hTqr' := hbranchConv.marginal_value.support_face_marginalValue_scalar
    F hax hV (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) hrqn hrnn hrndn hrbn η' hη'tan
  have hLHS : η' (fun d' => hint.marginalValue F hV (Relabeling.relabelDist e q)
        (Channel.actionPushforward d' (supportIncludeKernel (Relabeling.relabelDist e r)))) =
      η (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel r))) := by
    show η (fun d => hint.marginalValue F hV (Relabeling.relabelDist e q)
        (Channel.actionPushforward (Relabeling.relabelDist (relabelSupportEquiv e r).symm d)
          (supportIncludeKernel (Relabeling.relabelDist e r)))) = _
    congr 1
    funext d
    have hpc := push_relabel_comm e r d
    calc hint.marginalValue F hV (Relabeling.relabelDist e q)
          (Channel.actionPushforward (Relabeling.relabelDist (relabelSupportEquiv e r).symm d)
            (supportIncludeKernel (Relabeling.relabelDist e r)))
        = hint.marginalValue F hV (Relabeling.relabelDist e q)
          (Relabeling.relabelDist e (Channel.actionPushforward d (supportIncludeKernel r))) :=
            congrArg (hint.marginalValue F hV (Relabeling.relabelDist e q)) hpc
      _ = hint.marginalValue F hV q (Channel.actionPushforward d (supportIncludeKernel r)) :=
            hint.marginalValue_relabel F hV e q _
  have hRHS : η' (hint.marginalValue F hV (Relabeling.relabelDist e r).restrictToSupport) =
      η (hint.marginalValue F hV r.restrictToSupport) := by
    show η (fun d => (hint.marginalValue F hV (Relabeling.relabelDist e r).restrictToSupport)
        (Relabeling.relabelDist (relabelSupportEquiv e r).symm d)) = _
    congr 1
    funext d
    have hface : (Relabeling.relabelDist e r).restrictToSupport =
        Relabeling.relabelDist (relabelSupportEquiv e r).symm r.restrictToSupport :=
      restrictToSupport_relabelDist e r
    have hmv := hint.marginalValue_relabel F hV (relabelSupportEquiv e r).symm r.restrictToSupport d
    -- hmv : mV(relabel eq.symm (r|supp))(relabel eq.symm d) = mV(r|supp) d
    rw [← hmv]
    congr 1
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

/-- Raw coherent face scales from the data-carrying HM interface and the
faithful branch/coherent scale components.

This is the formal dependency order used by the paper before product gauge
normalisation.  It does not assert that an arbitrary already-selected
`hfaces` is product-normalised. -/
noncomputable def rawCoherentFaceScales_of_FinalHM_faithfulBranch
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax))) :
    CoherentRelabelingFaceScalesStructure F :=
  CoherentRelabelingFaceScales_of_faithfulBranch
    hfaith F hax
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    hscaleRelabel hfaceScale

/-- Coherent face scales obtained by applying a positive gauge directly to the
faithful branch/cocycle/scale package, then proving the transformed scale
relabeling and support-face equations.

This is closer to the paper's proof order than first requiring raw face scales
to be coherent: the gauge choice itself is what fixes the coherent
representative. -/
noncomputable def coherentFaceScales_of_FinalHM_positiveGauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport)) :
    CoherentRelabelingFaceScalesStructure F :=
  CoherentRelabelingFaceScales_of_positiveGaugeBranch
    (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax))
    hgauge hrel hsupport

/-- **Selected relabelling invariance for the positive-gauge representative,
from the HM covariance clause and gauge relabelling-equivariance.**

The positive-gauge value functional is `gauge q · V_HM q E`.  Under a finite
relabelling `eA`, `V_HM` is invariant (`FinalHMRelabelCovariance`) and the chosen
gauge is invariant (`hgaugeRel`, a harmless equivariance normalization on the
gauge — the same status as the `scale_relabel` field it strengthens), so the
gauged value is invariant.  This produces the selected relabelling package
*without* the `product_normalized` pinning convention (which is in fact false at
subsingleton priors). -/
theorem finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hcov : FinalHMRelabelCovariance hhm)
    (hgaugeRel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A),
        hgauge.gauge (Relabeling.relabelDist e q) = hgauge.gauge q) :
    FiniteSelectedPosteriorValueRelabelingFor
      (coherentFaceScales_of_FinalHM_positiveGauge hhm hfaith hax hgauge hrel hsupport) where
  V_relabel_eq := by
    intro _hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    show hgauge.gauge (Relabeling.relabelDist eA q) *
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      hgauge.gauge q *
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P)
    rw [hgaugeRel eA q]
    rw [show (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P)
        from hcov.V_relabel_eq hax eA eO q P]

/-- Product quasi-additivity for a face-scale representative built by the
positive-gauge branch route. -/
noncomputable def productQuasiAdditivity_of_FinalHM_positiveGauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hsingle :
      FiniteFaceScaleSingletonInteractionConventionFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivityForFaceScales_of_finalProductComponents
    hpair hcurrentGauge hassoc hsingle

/-- Product quasi-additivity for a positive-gauge representative, using
value-level triple-product associativity as the source of the interaction
associativity equations. -/
noncomputable def productQuasiAdditivity_of_FinalHM_positiveGaugeProductData
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingle :
      FiniteFaceScaleSingletonInteractionConventionFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivity_of_FinalHM_positiveGauge
    hhm hfaith hax hgauge hrel hsupport hpair hcurrentGauge
    (faceScaleProductInteractionAssociativity_of_valueAssociativity_currentGauge
      hcurrentGauge htriple)
    hsingle

/-- Product quasi-additivity for a positive-gauge representative from the
source product-data fields: the left-slice affine transform is supplied by HM,
and pairwise bilinearity is reconstructed from intercept linearity and slope
affinity. -/
noncomputable def productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          hintercept hslope)) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivity_of_FinalHM_positiveGaugeProductData
    hhm hfaith hax hgauge hrel hsupport
    (faceScaleProductPairwiseBilinearity_of_multiPieces
      (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
        (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
          hhm)
        hsingleSlice)
      hintercept hslope)
    hcurrentGauge htriple hsingleInteraction

/-- Intercept positive-linearity for the constructed positive-gauge
representative, derived from the HM left-slice theorem, A8 intercept
same-order, HM public-mix affinity, and internal finite affine-utility
uniqueness. -/
theorem productInterceptPositiveLinear_of_FinalHM_positiveGauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport)) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          hsingleSlice)) :=
  faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
    (faceScaleProductInterceptSameOrder_of_A8
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          hsingleSlice)))
    (faceScaleProductInterceptPublicMixAffinity_of_HM
      (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          hsingleSlice)))
    (classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
      (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          hsingleSlice))
      classicalFiniteAffineUtilityUniquenessAssumptions)

/-- Face-scale product-swap value equality from selected value relabeling.

This is the selected-representative replacement for
`faceScaleProduct_value_swap_eq_of_value_relabeling`: it does not consume the
obsolete all-representatives relabeling package. -/
theorem faceScaleProduct_value_swap_eq_of_selectedRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hfaces.branch_result.branch_agg.value_rep.V (prodDist r q)
        (experimentOfChannel (prodChannel R P)) := by
  have hrel :=
    hsel.V_relabel_eq hax
      (Equiv.prodComm A B) (Equiv.prodComm O Y)
      (prodDist q r) (prodChannel P R)
  have hrel' :
      hfaces.branch_result.branch_agg.value_rep.V (prodDist r q)
          (experimentOfChannel (prodChannel R P)) =
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) := by
    simpa [relabelDist_prodComm q r, relabelChannel_prodComm P R] using hrel
  exact hrel'.symm

/-- Product-slope affinity from selected relabeling.

This is the same coefficient-swap argument as
`faceScaleProductSlopeAffine_of_HM_A8_relabeling`, but it uses the selected
product-normalized representative instead of the obsolete broad relabeling
interface. -/
theorem faceScaleProductSlopeAffine_of_selectedRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hlin :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice) :
    FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice where
  slope_affine_in_second_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA
    classical
    have hHq :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    obtain ⟨Bqr, _hBqr_pos, hBqr⟩ := hlin.intercept_positive_linear hax q r hq hr
    obtain ⟨Brq, hBrq_pos, hBrq⟩ := hlin.intercept_positive_linear hax r q hr hq
    refine ⟨Brq,
      (hslice.leftSliceSlope hax r q (Channel.idChannel : Channel A A) - Bqr) /
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)),
      hBrq_pos, ?_⟩
    intro Y _ _ R
    have h1 :=
      hslice.left_slice_affine hax q r hq hr
        (Channel.idChannel : Channel A A) R
    have h2 :=
      faceScaleProduct_value_swap_eq_of_selectedRelabeling hsel hax
        q r (Channel.idChannel : Channel A A) R
    have h3 :=
      hslice.left_slice_affine hax r q hr hq R
        (Channel.idChannel : Channel A A)
    have hIqr := hBqr R
    have hIrq := hBrq (Channel.idChannel : Channel A A)
    have key :
        hslice.leftSliceSlope hax q r R *
            hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel (Channel.idChannel : Channel A A)) =
          hslice.leftSliceSlope hax r q (Channel.idChannel : Channel A A) *
              hfaces.branch_result.branch_agg.value_rep.V r
                (experimentOfChannel R) +
            Brq * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel (Channel.idChannel : Channel A A)) -
            Bqr * hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) := by
      have hchain := h1.symm.trans (h2.trans h3)
      rw [hIqr, hIrq] at hchain
      linarith [hchain]
    have hgoal :
        hslice.leftSliceSlope hax q r R =
          Brq +
            (hslice.leftSliceSlope hax r q (Channel.idChannel : Channel A A) - Bqr) /
              hfaces.branch_result.branch_agg.value_rep.V q
                (experimentOfChannel (Channel.idChannel : Channel A A)) *
              hfaces.branch_result.branch_agg.value_rep.V r
                (experimentOfChannel R) := by
      field_simp
      linear_combination key
    exact hgoal

/-- Product quasi-additivity for a positive-gauge representative with the
intercept positive-linearity field discharged internally. -/
noncomputable def productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData_internalIntercept
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          hslope)) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData
    hhm hfaith hax hgauge hrel hsupport hsingleSlice
    (productInterceptPositiveLinear_of_FinalHM_positiveGauge
      hhm hfaith hax hgauge hrel hsupport hsingleSlice)
    hslope hcurrentGauge htriple hsingleInteraction

/-- Product quasi-additivity for a positive-gauge representative whose selected
representatives have already been product-normalized.

The product-normalized selected representative package supplies selected value
relabeling; selected relabeling supplies both the product-swap slope proof and
triple-product value associativity.  Thus this constructor no longer takes the
obsolete all-representatives relabeling package, an explicit slope-affinity
field, or an explicit triple-product associativity field. -/
noncomputable def productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hnorm :
      FiniteProductNormalizedSelectedRepresentativesFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
              hnorm)
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm hfaith hax hgauge hrel hsupport hsingleSlice))))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
              hnorm)
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm hfaith hax hgauge hrel hsupport hsingleSlice)))) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData_internalIntercept
    hhm hfaith hax hgauge hrel hsupport hsingleSlice
    (faceScaleProductSlopeAffine_of_selectedRelabeling
      (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
        hnorm)
      (productInterceptPositiveLinear_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport hsingleSlice))
    hcurrentGauge
    (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport)
      (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
        hnorm))
    hsingleInteraction

/-- Product-normalised coherent face scales obtained by applying the selected
positive product gauge to the raw coherent representatives. -/
noncomputable def productNormalizedFaceScales_of_FinalHM_gauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair) :
    CoherentRelabelingFaceScalesStructure F :=
  (rawCoherentFaceScales_of_FinalHM_faithfulBranch
    hhm hfaith hax hscaleRelabel hfaceScale).gaugeTransform hgauge.gauge

/-- Product quasi-additivity for the product-gauge-normalised representatives.

The product quasi-additivity package is constructed for the transformed
witness, not required for arbitrary raw face scales. -/
noncomputable def productQuasiAdditivity_of_FinalHM_gauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hsingle :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)) :
    FiniteProductQuasiAdditivityForFaceScales
      (productNormalizedFaceScales_of_FinalHM_gauge
        hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge) :=
  productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData
    hpair hgauge htriple hsingle

/-- Existential form of the corrected product-normalised representative
construction.

The witnesses are the post-gauge face-scale representatives and their product
quasi-additivity package.  This is the target shape needed to avoid the false
claim that every arbitrary coherent representative is already normalised. -/
theorem existsProductNormalizedFaceScales_of_FinalHM_gauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hsingle :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge))
    (hconv :
      FinalHarmlessConventions
        (productNormalizedFaceScales_of_FinalHM_gauge
          hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge)
        (productQuasiAdditivity_of_FinalHM_gauge
          hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge
          htriple hsingle)) :
    ∃ hfaces : CoherentRelabelingFaceScalesStructure F,
      ∃ hprod : FiniteProductQuasiAdditivityForFaceScales hfaces,
        FinalHarmlessConventions hfaces hprod :=
  ⟨productNormalizedFaceScales_of_FinalHM_gauge
      hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge,
    productQuasiAdditivity_of_FinalHM_gauge
      hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge htriple hsingle,
    hconv⟩

/-! ## Boundary-completed scale: eliminating the boundary normalized-value support field

The following machinery proves `FiniteNormalizedValueSupportBoundaryAssumptions`
(field 1 of `FiniteCardinalSupportBoundaryAssumptions`) rather than assuming it,
for a boundary-completed scale.  `wrapScale` completes the prior-dependent scale
to its support-face value at nondegenerate boundary priors (leaving full-support
and singleton priors untouched); `boundaryCompleteScale` re-proves the four
`ScaleCoherenceStructure` fields; `wrapCross` transports the cross-prior block
representation (whose comparison clause is full-support-guarded, where the
wrapped scale agrees with the original); and `field1_wrapper` /
`normalizedValueSupportBoundary_of_boundaryComplete` prove the boundary
normalized-value support restriction from the Herstein--Milnor marginal-value
support-face coherence clause plus the coherent support-face scale relation. -/

/-- Equivalence `A ≃ supportSubtype q` for a full-support `q`. -/
noncomputable def fsSupportEquiv {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (hq : q.FullSupport) : A ≃ supportSubtype q where
  toFun a := ⟨a, hq a⟩
  invFun s := s.1
  left_inv a := rfl
  right_inv s := by cases s; rfl

theorem restrictToSupport_eq_relabel_fullSupport {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (hq : q.FullSupport) :
    q.restrictToSupport = Relabeling.relabelDist (fsSupportEquiv q hq) q := by
  ext s; rcases s with ⟨a, ha⟩
  simp [Relabeling.relabelDist, fsSupportEquiv, Dist.restrictToSupport_apply]

open Classical in
/-- Scale completed to the support-face value at nondegenerate boundary priors. -/
noncomputable def wrapScale
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  if (¬ q.FullSupport ∧ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) then
    hs.scale q.restrictToSupport
  else hs.scale q

theorem wrapScale_fullSupport
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    wrapScale hs q = hs.scale q := by
  classical
  simp only [wrapScale]
  rw [if_neg (by rintro ⟨hnf, _⟩; exact hnf hq)]

theorem wrapScale_boundary_nondeg
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnf : ¬ q.FullSupport)
    (hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    wrapScale hs q = hs.scale q.restrictToSupport := by
  classical
  simp only [wrapScale]
  rw [if_pos ⟨hnf, hnd⟩]

theorem wrapScale_singleton
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnd : ¬ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    wrapScale hs q = hs.scale q := by
  classical
  simp only [wrapScale]
  rw [if_neg (by rintro ⟨_, hc⟩; exact hnd hc)]

/-- The boundary-completed scale coherence structure. -/
noncomputable def boundaryCompleteScale
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hs.branch_agg.branchCoeff q r = hs.scale q / hs.scale r.restrictToSupport)
    : ScaleCoherenceStructure F where
  branch_agg := hs.branch_agg
  scale := fun {A} _ _ _ q => wrapScale hs q
  scale_pos := by
    intro A _ _ _ q hq
    rw [wrapScale_fullSupport hs q hq]; exact hs.scale_pos q hq
  scale_universal := by
    intro A B _ _ _ _ _ _ q r hq hr
    rw [wrapScale_fullSupport hs q hq, wrapScale_fullSupport hs r hr]
    exact hs.scale_universal q r hq hr
  branchCoeff_factorization := by
    classical
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ hpos
    set r := Channel.posterior P₁ q o₁ with hrdef
    rw [wrapScale_fullSupport hs q hq]
    by_cases hrfull : r.FullSupport
    · rw [wrapScale_fullSupport hs r hrfull]
      exact hs.branchCoeff_factorization q hq P₁ o₁ hpos
    · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b
      · haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
        obtain ⟨a0, b0, hab0, ha0, hb0⟩ := hnd
        rw [wrapScale_boundary_nondeg hs r hrfull ⟨a0, b0, hab0, ha0, hb0⟩]
        exact hsf q hq r ⟨a0, ha0⟩ ⟨a0, b0, hab0, ha0, hb0⟩ hrfull
      · rw [wrapScale_singleton hs r hnd]
        exact hs.branchCoeff_factorization q hq P₁ o₁ hpos

/-- Field 1 (boundary normalized-value support restriction) proved for the
boundary-completed scale. -/
theorem field1_boundaryComplete
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hs.branch_agg.branchCoeff q r = hs.scale q / hs.scale r.restrictToSupport)
    (hcoh : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) [Nonempty (supportSubtype q)] (d : Dist (supportSubtype q)),
      hint.marginalValue F hs.branch_agg.value_rep q
        (Channel.actionPushforward d (supportIncludeKernel q)) =
        hint.marginalValue F hs.branch_agg.value_rep q.restrictToSupport d)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (hqb : ¬ q.FullSupport) :
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    normalizedValue (boundaryCompleteScale hs hsf) q P =
      normalizedValue (boundaryCompleteScale hs hsf) q.restrictToSupport
        (Channel.restrictToSupport P q) := by
  classical
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hnum : hs.branch_agg.value_rep.V q (experimentOfChannel P) =
      hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) := by
    rw [hint.value_eq_integral F hs.branch_agg.value_rep q (experimentOfChannel P)]
    rw [hint.value_eq_integral F hs.branch_agg.value_rep q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q))]
    rw [posteriorLawIntegralExp_experimentOfChannel]
    rw [posteriorLawIntegral_restrictToSupport P q]
    rw [posteriorLawIntegralExp_experimentOfChannel]
    unfold posteriorLawIntegral
    apply Finset.sum_congr rfl
    intro o _
    congr 1
    exact hcoh q (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)
  change hs.branch_agg.value_rep.V q (experimentOfChannel P) / wrapScale hs q =
      hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) / wrapScale hs q.restrictToSupport
  rw [hnum]
  rw [wrapScale_fullSupport hs q.restrictToSupport (Dist.restrictToSupport_fullSupport q)]
  by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
  · rw [wrapScale_boundary_nondeg hs q hqb hnd]
  · have hss : Subsingleton (supportSubtype q) := by
      rw [subsingleton_iff]
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      by_contra hne
      exact hnd ⟨a, b, fun h => hne (Subtype.ext h), ha, hb⟩
    haveI := hss
    have hz : hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) = 0 :=
      branchValue_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep
        q.restrictToSupport (Dist.restrictToSupport_fullSupport q)
        (Channel.restrictToSupport P q)
    rw [hz, zero_div, zero_div]




/-! ## Field 3 (restricted coarse-reveal value) proved via support reindexing -/

noncomputable def sigmaSupportEquiv
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    supportSubtype (sigmaDist p q) ≃
      Σ (k' : supportSubtype p), supportSubtype (q k'.1) where
  toFun := fun ⟨⟨k, a⟩, hpos⟩ =>
    have hp : p k > 0 := by
      rw [sigmaDist_apply] at hpos
      rcases (p.nonneg k).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hpos; simp at hpos
    have hq : (q k) a > 0 := by
      rw [sigmaDist_apply] at hpos
      rcases ((q k).nonneg a).lt_or_eq with h | h
      · exact h
      · exfalso; rw [← h] at hpos; simp at hpos
    ⟨⟨k, hp⟩, ⟨a, hq⟩⟩
  invFun := fun ⟨⟨k, hp⟩, ⟨a, hq⟩⟩ =>
    ⟨⟨k, a⟩, by rw [sigmaDist_apply]; exact mul_pos hp hq⟩
  left_inv := by rintro ⟨⟨k, a⟩, hpos⟩; rfl
  right_inv := by rintro ⟨⟨k, hp⟩, ⟨a, hq⟩⟩; rfl

theorem sigma_restrict_reindex
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Relabeling.relabelDist (sigmaSupportEquiv Act p q) (sigmaDist p q).restrictToSupport =
      sigmaDist p.restrictToSupport (fun k' => (q k'.1).restrictToSupport) := by
  ext y
  rcases y with ⟨⟨k, hk⟩, ⟨a, ha⟩⟩
  rw [Relabeling.relabelDist_apply, sigmaDist_apply]
  simp only [sigmaSupportEquiv, Equiv.coe_fn_symm_mk, Dist.restrictToSupport_apply, sigmaDist_apply]



theorem normalizedValue_relabelAction_of_crossPrior
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    (eA : A ≃ B) (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    haveI : Nonempty B := ⟨eA (Classical.arbitrary A)⟩
    normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist eA q) (Relabeling.relabelChannel eA (Equiv.refl O) P) =
      normalizedValue hcross.entropy_reduction.scale_coherence q P := by
  haveI : Nonempty B := ⟨eA (Classical.arbitrary A)⟩
  set P' : Channel B O := Relabeling.relabelChannel eA (Equiv.refl O) P with hP'
  have hqB : (Relabeling.relabelDist eA q).FullSupport :=
    Relabeling.relabelDist_fullSupport eA q hq
  -- A5 both directions between P (on q) and P' (on relabel q)
  have hq_to_new : F.rel (blockChannel P P') (inlDist q) (inrDist (Relabeling.relabelDist eA q)) := by
    have h := hax.a5 P q (Relabeling.actionEquivKernel eA) P'
      (Relabeling.relabelChannel_isBayesPushforwardCompletion eA P q)
    simpa [P', Relabeling.actionPushforward_equiv] using h
  have hq_to_old : F.rel (blockChannel P' P) (inlDist (Relabeling.relabelDist eA q)) (inrDist q) := by
    have h := hax.a5 P' (Relabeling.relabelDist eA q) (Relabeling.actionEquivKernel eA.symm) P
      (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion eA P q)
    simpa [P', Relabeling.actionPushforward_equiv, Relabeling.relabelDist_symm] using h
  -- convert each block comparison to a normalizedValue inequality
  have hge₁ := (hcross.cross_prior_block_rep q (Relabeling.relabelDist eA q) hq hqB P P').mp hq_to_new
  have hge₂ := (hcross.cross_prior_block_rep (Relabeling.relabelDist eA q) q hqB hq P' P).mp hq_to_old
  have e₁ : normalizedValue hcross.entropy_reduction.scale_coherence q P ≥
      normalizedValue hcross.entropy_reduction.scale_coherence (Relabeling.relabelDist eA q) P' := by
    simpa [normalizedValue] using hge₁
  have e₂ : normalizedValue hcross.entropy_reduction.scale_coherence (Relabeling.relabelDist eA q) P' ≥
      normalizedValue hcross.entropy_reduction.scale_coherence q P := by
    simpa [normalizedValue] using hge₂
  exact le_antisymm e₁ e₂


/- Target coarse channel on supp(s): reveal the block index in supportSubtype p. -/
noncomputable def coarseTgt
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    Channel (supportSubtype (sigmaDist p q)) (supportSubtype p) :=
  fun x =>
    haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    Dist.pure ((sigmaSupportEquiv Act p q x).1)

/- coarseTgt is the action-relabel (outcome refl) of coarseReveal over the reindexed Act'. -/
theorem coarseTgt_eq_relabel
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    coarseTgt Act p q =
      Relabeling.relabelChannel (sigmaSupportEquiv Act p q).symm (Equiv.refl (supportSubtype p))
        (coarseRevealChannel (fun k' : supportSubtype p => supportSubtype (q k'.1))) := by
  haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
  ext x y
  simp only [coarseTgt, Relabeling.relabelChannel_apply, Equiv.refl_symm, Equiv.refl_apply,
    coarseRevealChannel, Equiv.symm_symm, Equiv.apply_symm_apply]

/- Step B (outcome collapse): C|supp and coarseTgt have the same posterior law at s|supp.
   Both deterministically reveal the block; posteriors are the fibres.  The K-valued reveal
   has zero marginal off supp(p), so its posterior-law integral matches the supp(p)-valued one. -/
theorem samePosteriorLaw_coarse_restrict_tgt
    {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    [Nonempty (supportSubtype (sigmaDist p q))] :
    SamePosteriorLawExp (sigmaDist p q).restrictToSupport
      (experimentOfChannel (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)))
      (experimentOfChannel (coarseTgt Act p q)) := by
  intro φ _
  rw [posteriorLawIntegralExp_experimentOfChannel, posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  classical
  haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
  -- RHS sum over supportSubtype p equals a sum over K of terms zero off supp(p)
  rw [← sum_supportSubtype_eq_sum_of_zero p
        (fun k =>
          (Channel.outcomeMarginal (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport) k *
          φ (Channel.posterior (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport k))
        ?_]
  · -- Now both are sums over supportSubtype p; match termwise.
    apply Finset.sum_congr rfl
    intro k' _
    have hind : ∀ x : supportSubtype (sigmaDist p q),
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) x (k'.1) =
        (coarseTgt Act p q) x k' := by
      intro x
      have hfst : ((sigmaSupportEquiv Act p q x).1).1 = x.1.1 := by
        rcases x with ⟨⟨j, a⟩, hxpos⟩
        rfl
      simp only [coarseTgt, Channel.restrictToSupport_apply, coarseRevealChannel, Dist.pure_apply]
      by_cases hx : k'.1 = x.1.1
      · have h2 : (k' = (sigmaSupportEquiv Act p q x).1) := by
          apply Subtype.ext; rw [hfst]; exact hx
        rw [if_pos hx, if_pos h2]
      · have h2 : ¬ (k' = (sigmaSupportEquiv Act p q x).1) := by
          intro h; apply hx; rw [← hfst]; exact congrArg Subtype.val h
        rw [if_neg hx, if_neg h2]
    have hmarg : (Channel.outcomeMarginal
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
        (sigmaDist p q).restrictToSupport) k'.1 =
        (Channel.outcomeMarginal (coarseTgt Act p q) (sigmaDist p q).restrictToSupport) k' := by
      rw [Channel.outcomeMarginal_apply, Channel.outcomeMarginal_apply]
      apply Finset.sum_congr rfl
      intro x _; rw [hind x]
    have hpost : (Channel.posterior
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
        (sigmaDist p q).restrictToSupport) k'.1 =
        (Channel.posterior (coarseTgt Act p q) (sigmaDist p q).restrictToSupport) k' := by
      by_cases hpos : (Channel.outcomeMarginal (coarseTgt Act p q)
          (sigmaDist p q).restrictToSupport) k' > 0
      · have hposC : (Channel.outcomeMarginal
            (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport) k'.1 > 0 := by rw [hmarg]; exact hpos
        ext y
        simp only [Channel.posterior, dif_pos hposC, dif_pos hpos]
        rw [hind y, hmarg]
      · have hnegC : ¬ (Channel.outcomeMarginal
            (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
            (sigmaDist p q).restrictToSupport) k'.1 > 0 := by rw [hmarg]; exact hpos
        simp only [Channel.posterior, dif_neg hnegC, dif_neg hpos]
    rw [hmarg, hpost]
  · -- off-support terms vanish: for p k = 0, outcomeMarginal of restricted coarseReveal at k is 0
    intro k hk0
    have hm : (Channel.outcomeMarginal
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q))
        (sigmaDist p q).restrictToSupport) k = 0 := by
      rw [Channel.outcomeMarginal_apply]
      apply Finset.sum_eq_zero
      intro x _
      rcases x with ⟨⟨j, a⟩, hx⟩
      have hjne : j ≠ k := by
        rintro rfl
        rw [sigmaDist_apply] at hx
        have : p j = 0 := hk0
        rw [this, zero_mul] at hx
        exact lt_irrefl 0 hx
      simp only [Channel.restrictToSupport_apply, coarseRevealChannel, Dist.pure_apply]
      rw [if_neg (by simpa [eq_comm] using hjne), mul_zero]
    rw [hm, zero_mul]


/- normalizedValue respects same posterior law (numerator respects, scale unaffected). -/
theorem normalizedValue_congr_samePosteriorLaw
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A O O' : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype O'] [DecidableEq O']
    (q : Dist A) (P : Channel A O) (P' : Channel A O')
    (hsame : SamePosteriorLawExp q (experimentOfChannel P) (experimentOfChannel P')) :
    normalizedValue hs q P = normalizedValue hs q P' := by
  unfold normalizedValue
  rw [hs.branch_agg.value_rep.respects_same_posterior_law q
    (experimentOfChannel P) (experimentOfChannel P') hsame]

/- FIELD 3: restricted coarse-reveal value equals Hfun of the restricted coarse prior. -/
theorem field3_restricted_coarse_reveal
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k))
    (hnot : ¬ (sigmaDist p q).FullSupport) :
    letI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
    letI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    normalizedValue hcross.entropy_reduction.scale_coherence
        (sigmaDist p q).restrictToSupport
        (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) =
      hcross.entropy_reduction.Hfun p.restrictToSupport := by
  haveI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
  haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
  set hs := hcross.entropy_reduction.scale_coherence with hsdef
  set p' : Dist (supportSubtype p) := p.restrictToSupport with hp'
  set q' : (k' : supportSubtype p) → Dist (supportSubtype (q k'.1)) :=
    fun k' => (q k'.1).restrictToSupport with hq'
  haveI : ∀ k' : supportSubtype p, Nonempty (supportSubtype (q k'.1)) :=
    fun k' => supportSubtype_nonempty _
  haveI : Nonempty ((k' : supportSubtype p) × supportSubtype (q k'.1)) :=
    (sigmaSupportEquiv Act p q).nonempty_congr.mp inferInstance
  -- Step B: collapse the K-outcome to coarseTgt (into supp p)
  have hstepB : normalizedValue hs (sigmaDist p q).restrictToSupport
      (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) =
      normalizedValue hs (sigmaDist p q).restrictToSupport (coarseTgt Act p q) :=
    normalizedValue_congr_samePosteriorLaw hs _ _ _
      (samePosteriorLaw_coarse_restrict_tgt Act p q)
  rw [hstepB]
  -- coarseTgt = relabelChannel eA.symm (refl) (coarseReveal Act'), s|supp = relabelDist eA.symm (sigmaDist p' q')
  set eA := (sigmaSupportEquiv Act p q) with heA
  have hs_eq : (sigmaDist p q).restrictToSupport = Relabeling.relabelDist eA.symm (sigmaDist p' q') := by
    conv_lhs => rw [← Relabeling.relabelDist_symm eA (sigmaDist p q).restrictToSupport]
    rw [sigma_restrict_reindex Act p q]
  have hC_eq : coarseTgt Act p q =
      Relabeling.relabelChannel eA.symm (Equiv.refl (supportSubtype p))
        (coarseRevealChannel (fun k' : supportSubtype p => supportSubtype (q k'.1))) :=
    coarseTgt_eq_relabel Act p q
  rw [hs_eq, hC_eq]
  -- action engine transports the normalized value across the reindex relabeling
  have hp'full : (sigmaDist p' q').FullSupport := by
    intro x
    rw [sigmaDist_apply]
    exact mul_pos (Dist.restrictToSupport_fullSupport p x.1)
      (Dist.restrictToSupport_fullSupport (q x.1.1) x.2)
  rw [normalizedValue_relabelAction_of_crossPrior F hax hcross eA.symm (sigmaDist p' q')
      hp'full
      (coarseRevealChannel (fun k' : supportSubtype p => supportSubtype (q k'.1)))]
  -- full-support coarse lemma: normValue (sigmaDist p' q') (coarseReveal Act') = Hfun p'
  rw [coarseReveal_value_eq_Hfun_of_axioms_fullSupport F hax hcross hreg
      (fun k' : supportSubtype p => supportSubtype (q k'.1)) p' q'
      (by
        -- sigmaDist p' q' is full support (p' and each q' full support)
        intro x
        rw [sigmaDist_apply]
        exact mul_pos (Dist.restrictToSupport_fullSupport p x.1)
          (Dist.restrictToSupport_fullSupport (q x.1.1) x.2))]



/-! ## hcard-free MI route from per-cross boundary facts -/

/- Per-hcross coarse-reveal value: assemble from the three boundary facts (all now
   proved theorems for the wrapped structure), reusing the full-support lemma. -/
theorem coarseVal_forCross
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    -- field 1 (boundary normalized-value support restriction) for THIS hcross:
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    -- field 3 (restricted coarse-reveal) for THIS hcross:
    (hrestrC : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)), ¬ (sigmaDist p q).FullSupport →
      haveI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
      haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q).restrictToSupport
          (Channel.restrictToSupport (coarseRevealChannel Act) (sigmaDist p q)) =
        hcross.entropy_reduction.Hfun p.restrictToSupport)
    -- Hfun support restriction for THIS hcross (field 2 + field 1 at id):
    (hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q = hcross.entropy_reduction.Hfun q.restrictToSupport)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    normalizedValue hcross.entropy_reduction.scale_coherence
        (sigmaDist p q) (coarseRevealChannel Act) =
      hcross.entropy_reduction.Hfun p := by
  by_cases hsig : (sigmaDist p q).FullSupport
  · exact coarseReveal_value_eq_Hfun_of_axioms_fullSupport F hax hcross hreg Act p q hsig
  · haveI : Nonempty (supportSubtype (sigmaDist p q)) := supportSubtype_nonempty _
    haveI : Nonempty (supportSubtype p) := supportSubtype_nonempty p
    have h1 := hnormC (coarseRevealChannel Act) (sigmaDist p q) hsig
    have h3 := hrestrC Act p q hsig
    have hH := hhfunC p
    rw [h1, h3, ← hH]

/- Faddeev recursion from per-hcross coarse value. -/
theorem satisfiesFaddeevRecursion_forCross
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p) :
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  intro K _ _ _ Act _ _ _ _ p q
  have hER := hred.coarse_reveal_entropy_reduction F hax hreg Act p q
  have hV := hcoarse Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) :=
    posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k => hblock.Hfun_blockEmbed F hax hreg Act k (q k))
  change hcross.entropy_reduction.Hfun (sigmaDist p q) =
    hcross.entropy_reduction.Hfun p +
      ∑ k, p k * hcross.entropy_reduction.Hfun (q k)
  rw [hER, hV, hInt]

/- FaddeevEntropyForm from per-hcross coarse value. -/
noncomputable def FaddeevEntropyForm_forCross
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p) :
    FaddeevEntropyForm F := by
  have hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    { regularity := hreg
      grouping_recursion :=
        satisfiesFaddeevRecursion_forCross hblock hred F hax hcross hreg hcoarse }
  have hex := hfad.of_recursion F hrecForm
  have hH : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hcross.entropy_reduction.Hfun q = (Classical.choose hex) * H(q) :=
    (Classical.choose_spec hex).2
  have hHfun_pos : 0 < hcross.entropy_reduction.Hfun (Dist.uniform (A := ULift.{u,0} Bool)) :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrecForm
  exact
    { cross_prior := hcross
      alpha := Classical.choose hex
      alpha_pos :=
        alpha_strict_pos_of_positive_Hfun_witness F hax hcross hrecForm hHfun_pos
          (Classical.choose hex) hH
      H_eq_alpha_shannon := hH
      a3_block_equivalence := a3_block_equivalence_of_traceAxioms F hax }

/- MIRep from per-hcross coarse value (no FiniteCardinalSupportBoundaryAssumptions). -/
theorem MIRep_forCross
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p) :
    MIRep F :=
  let hfe : FaddeevEntropyForm F :=
    FaddeevEntropyForm_forCross hblock hred hfad F hax hcross hreg hcoarse
  MIRep_of_SufficiencyMIPackage F
    (FullSupportMIRepExtendsToBoundary_of_supportRestriction F
      (FullSupportBlockMI_of_FaddeevEntropyForm F hfe) hax
      (FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F hfe))



/-! ## Capstone: boundary-completed MI route with no cardinal-boundary assumption -/

/- Wrapped cross-prior representation: same as hcross but with the boundary-completed scale. -/
noncomputable def wrapCross
    {F : PrefFamily.{u}} (hcross : CrossPriorBlockRepresentation F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross.entropy_reduction.scale_coherence.scale q /
          hcross.entropy_reduction.scale_coherence.scale r.restrictToSupport)
    : CrossPriorBlockRepresentation F where
  entropy_reduction :=
    EntropyReductionRepresentation_of_scale F
      (boundaryCompleteScale hcross.entropy_reduction.scale_coherence hsf)
  cross_prior_block_rep := by
    intro A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P Q
    have hsq : wrapScale hcross.entropy_reduction.scale_coherence q =
        hcross.entropy_reduction.scale_coherence.scale q :=
      wrapScale_fullSupport _ q hq
    have hsr : wrapScale hcross.entropy_reduction.scale_coherence r =
        hcross.entropy_reduction.scale_coherence.scale r :=
      wrapScale_fullSupport _ r hr
    have hb := hcross.cross_prior_block_rep q r hq hr P Q
    rw [← hsq, ← hsr] at hb
    exact hb

/- Per-hcross nonneg of normalizedValue at id (boundary case uses per-hcross field1). -/
theorem normalizedValue_id_nonneg_forCross
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 ≤ normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel := by
  by_cases hq : q.FullSupport
  · exact normalizedValue_id_nonneg_of_crossPrior_fullSupport hax hcross q hq
  · haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    rw [hnormC Channel.idChannel q hq,
      normalizedValue_restrict_idChannel_eq_idSupport hcross.entropy_reduction q]
    exact normalizedValue_id_nonneg_of_crossPrior_fullSupport hax hcross
      q.restrictToSupport (Dist.restrictToSupport_fullSupport q)

/- Per-hcross pure-zero. -/
theorem normalizedValue_id_pure_zero_forCross
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (a : A) :
    normalizedValue hcross.entropy_reduction.scale_coherence (Dist.pure a) Channel.idChannel = 0 := by
  by_cases hq : (Dist.pure a).FullSupport
  · haveI : Subsingleton A :=
      ⟨fun b c => by rw [eq_of_pure_pos (hq b), eq_of_pure_pos (hq c)]⟩
    have hV0 : hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V
        (Dist.pure a) (experimentOfChannel Channel.idChannel) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep (Dist.pure a) hq Channel.idChannel
    simp [normalizedValue, hV0]
  · haveI : Nonempty (supportSubtype (Dist.pure a)) := supportSubtype_nonempty (Dist.pure a)
    haveI : Subsingleton (supportSubtype (Dist.pure a)) := subsingleton_supportSubtype_pure a
    rw [hnormC Channel.idChannel (Dist.pure a) hq,
      normalizedValue_restrict_idChannel_eq_idSupport hcross.entropy_reduction (Dist.pure a)]
    have hV0 : hcross.entropy_reduction.scale_coherence.branch_agg.value_rep.V
        (Dist.pure a).restrictToSupport
        (experimentOfChannel (Channel.idChannel :
          Channel (supportSubtype (Dist.pure a)) (supportSubtype (Dist.pure a)))) = 0 :=
      V_channel_eq_zero_of_subsingleton F
        hcross.entropy_reduction.scale_coherence.branch_agg.value_rep
        (Dist.pure a).restrictToSupport (Dist.restrictToSupport_fullSupport _) Channel.idChannel
    simp [normalizedValue, hV0]

/- Per-hcross EntropyRegularity, when Hfun = normalizedValue·id (constructed rep). -/
theorem entropyRegularity_forCross
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hcross.entropy_reduction.Hfun q =
        normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q)) :
    EntropyRegularity F hcross.entropy_reduction where
  H_nonneg := fun q => by
    rw [hHfunId q]; exact normalizedValue_id_nonneg_forCross hax hcross hnormC q
  H_singleton := fun a => by
    rw [hHfunId (Dist.pure a)]; exact normalizedValue_id_pure_zero_forCross hax hcross hnormC a

/- CAPSTONE: MIRep with NO FiniteCardinalSupportBoundaryAssumptions, from wrapCross. -/
theorem MIRep_of_boundaryComplete
    (hblock : FiniteHfunBlockEmbeddingInvarianceAssumptions.{u})
    (hred : FiniteCoarseRevealEntropyReductionAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hcross0 : CrossPriorBlockRepresentation F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross0.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross0.entropy_reduction.scale_coherence.scale q /
          hcross0.entropy_reduction.scale_coherence.scale r.restrictToSupport)
    (hcoh : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) [Nonempty (supportSubtype q)] (d : Dist (supportSubtype q)),
      hint.marginalValue F (boundaryCompleteScale hcross0.entropy_reduction.scale_coherence hsf).branch_agg.value_rep q
        (Channel.actionPushforward d (supportIncludeKernel q)) =
        hint.marginalValue F (boundaryCompleteScale hcross0.entropy_reduction.scale_coherence hsf).branch_agg.value_rep
          q.restrictToSupport d) :
    MIRep F := by
  set hc := wrapCross hcross0 hsf with hcdef
  -- Hfun of hc = normalizedValue (wrapped) id  (definitional via EntropyReductionRepresentation_of_scale)
  have hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hc.entropy_reduction.Hfun q =
        normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel :=
    fun q => rfl
  -- field 1 for hc:
  have hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hc.entropy_reduction.scale_coherence q P =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    intro A O _ _ _ _ _ P q hqb
    exact field1_boundaryComplete hint (hcross0.entropy_reduction.scale_coherence) hsf hcoh P q hqb
  have hreg : EntropyRegularity F hc.entropy_reduction :=
    entropyRegularity_forCross hax hc hHfunId hnormC
  -- per-hcross coarse value from the three facts:
  have hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hc.entropy_reduction.Hfun p := by
    intro K _ _ _ Act _ _ _ _ p q
    refine coarseVal_forCross F hax hc hreg hnormC ?_ ?_ Act p q
    · -- field 3 for hc
      intro K2 _ _ _ Act2 _ _ _ _ p2 q2 hnot2
      exact field3_restricted_coarse_reveal F hax hc hreg Act2 p2 q2 hnot2
    · -- Hfun support restriction: Hfun q = Hfun (q|supp), via hHfunId + field1 at id
      intro A _ _ _ q
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      rw [hHfunId q, hHfunId q.restrictToSupport]
      rw [show normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel =
            normalizedValue hc.entropy_reduction.scale_coherence
              q.restrictToSupport (Channel.restrictToSupport Channel.idChannel q) from ?_,
          normalizedValue_restrict_idChannel_eq_idSupport hc.entropy_reduction q]
      by_cases hqf : q.FullSupport
      · exact normalizedValue_support_restrict_fullSupport_of_crossPrior
          F hax hc Channel.idChannel q hqf
      · exact hnormC Channel.idChannel q hqf
  apply MIRep_forCross hblock hred hfad F hax hc hreg
  intro K _ _ _ Act _ _ _ _ p q
  exact hcoarse Act p q


/-! ## hcard-free producers: Faddeev recursion / entropy form / MIRep from per-cross facts -/

theorem satisfiesFaddeevRecursion_ofCrossFacts
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hcross.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun)
    (hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
        hcross.entropy_reduction.Hfun qk)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hcross.entropy_reduction.Hfun p) :
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  intro K _ _ _ Act _ _ _ _ p q
  have hE := hER Act p q
  have hV := hcoarse Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) :=
    posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k => hblockE Act k (q k))
  change hcross.entropy_reduction.Hfun (sigmaDist p q) =
    hcross.entropy_reduction.Hfun p +
      ∑ k, p k * hcross.entropy_reduction.Hfun (q k)
  rw [hE, hV, hInt]

/- FaddeevEntropyForm from per-cross facts (hER, hblockE, hcoarse). -/
noncomputable def FaddeevEntropyForm_ofCrossFacts
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hcross.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun)
    (hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
        hcross.entropy_reduction.Hfun qk)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hcross.entropy_reduction.Hfun p) :
    FaddeevEntropyForm F := by
  have hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    { regularity := hreg
      grouping_recursion :=
        satisfiesFaddeevRecursion_ofCrossFacts F hax hcross hreg hER hblockE hcoarse }
  have hex := hfad.of_recursion F hrecForm
  have hH : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hcross.entropy_reduction.Hfun q = (Classical.choose hex) * H(q) :=
    (Classical.choose_spec hex).2
  have hHfun_pos : 0 < hcross.entropy_reduction.Hfun (Dist.uniform (A := ULift.{u,0} Bool)) :=
    uniform_ulift_bool_Hfun_pos_of_A1 F hax hcross hrecForm
  exact
    { cross_prior := hcross
      alpha := Classical.choose hex
      alpha_pos :=
        alpha_strict_pos_of_positive_Hfun_witness F hax hcross hrecForm hHfun_pos
          (Classical.choose hex) hH
      H_eq_alpha_shannon := hH
      a3_block_equivalence := a3_block_equivalence_of_traceAxioms F hax }

/- MIRep from per-cross facts. -/
theorem MIRep_ofCrossFacts
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hreg : EntropyRegularity F hcross.entropy_reduction)
    (hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hcross.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun)
    (hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
        hcross.entropy_reduction.Hfun qk)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hcross.entropy_reduction.Hfun p) :
    MIRep F :=
  let hfe : FaddeevEntropyForm F :=
    FaddeevEntropyForm_ofCrossFacts hfad F hax hcross hreg hER hblockE hcoarse
  MIRep_of_SufficiencyMIPackage F
    (FullSupportMIRepExtendsToBoundary_of_supportRestriction F
      (FullSupportBlockMI_of_FaddeevEntropyForm F hfe) hax
      (FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F hfe))



/-! ## Producers for wrapCross (bridge full-support Hfun, block-embed, entropy reduction) -/

/- On full support, wrapCross's Hfun equals the original hcross's Hfun. -/
theorem wrapCross_Hfun_fullSupport
    {F : PrefFamily.{u}} (hcross : CrossPriorBlockRepresentation F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross.entropy_reduction.scale_coherence.scale q /
          hcross.entropy_reduction.scale_coherence.scale r.restrictToSupport)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    (wrapCross hcross hsf).entropy_reduction.Hfun q =
      normalizedValue hcross.entropy_reduction.scale_coherence q Channel.idChannel := by
  -- LHS: Hfun(wrapCross) q = normalizedValue (boundaryComplete) q id  (definitional)
  --     = V q id / wrapScale q = V q id / scale q  (full support) = normalizedValue original q id
  show normalizedValue (boundaryCompleteScale hcross.entropy_reduction.scale_coherence hsf) q
      Channel.idChannel = _
  unfold normalizedValue
  change _ / wrapScale hcross.entropy_reduction.scale_coherence q = _
  rw [wrapScale_fullSupport _ q hq]
  rfl

/- Generic block-embed Hfun invariance from: per-cross Hfun-support-restriction (hhfunC) +
   per-cross full-support relabel invariance (hrelabC). Mirrors the closure proof. -/
theorem Hfun_blockEmbed_ofFacts
    (F : PrefFamily.{u}) (hcross : CrossPriorBlockRepresentation F)
    (hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q = hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hrelabC : ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A), q.FullSupport →
      hcross.entropy_reduction.Hfun (Relabeling.relabelDist e q) =
        hcross.entropy_reduction.Hfun q)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
    (k : K) (qk : Dist (Act k)) :
    hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
      hcross.entropy_reduction.Hfun qk := by
  haveI : Nonempty (supportSubtype qk) := supportSubtype_nonempty qk
  haveI : Nonempty (supportSubtype (blockEmbedDist Act k qk)) :=
    supportSubtype_nonempty (blockEmbedDist Act k qk)
  have hleft := hhfunC (blockEmbedDist Act k qk)
  have hright := hhfunC qk
  have hrestrict : (blockEmbedDist Act k qk).restrictToSupport =
      Relabeling.relabelDist (blockEmbedSupportEquiv Act k qk).symm qk.restrictToSupport :=
    restrict_blockEmbed_eq_relabel_support Act k qk
  have hrel := hrelabC (blockEmbedSupportEquiv Act k qk).symm qk.restrictToSupport
    (Dist.restrictToSupport_fullSupport qk)
  calc
    hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk)
        = hcross.entropy_reduction.Hfun (blockEmbedDist Act k qk).restrictToSupport := hleft
    _ = hcross.entropy_reduction.Hfun
          (Relabeling.relabelDist (blockEmbedSupportEquiv Act k qk).symm qk.restrictToSupport) := by
          rw [hrestrict]
    _ = hcross.entropy_reduction.Hfun qk.restrictToSupport := hrel
    _ = hcross.entropy_reduction.Hfun qk := hright.symm

/- Generic coarse-reveal entropy reduction (hER) from per-cross facts. -/
theorem coarseReveal_entropyReduction_ofFacts
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hcross : CrossPriorBlockRepresentation F)
    (hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hcross.entropy_reduction.scale_coherence q P =
        normalizedValue hcross.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q))
    (hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q = hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hIntC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      posteriorLawIntegral q P hcross.entropy_reduction.Hfun =
        posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
          hcross.entropy_reduction.Hfun)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    hcross.entropy_reduction.Hfun (sigmaDist p q) =
      normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
        (coarseRevealChannel Act) +
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
        hcross.entropy_reduction.Hfun := by
  set s : Dist ((k : K) × Act k) := sigmaDist p q with hsdef
  set C : Channel ((k : K) × Act k) K := coarseRevealChannel Act with hCdef
  by_cases hs : s.FullSupport
  · have hER := hcross.entropy_reduction.value_entropy_reduction s hs C
    have hER' : normalizedValue hcross.entropy_reduction.scale_coherence s C =
        hcross.entropy_reduction.Hfun s -
          posteriorLawIntegral s C hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    linarith
  · haveI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
    have hH := hhfunC s
    have hV := hnormC C s hs
    have hI := hIntC C s
    have hER := hcross.entropy_reduction.value_entropy_reduction
      s.restrictToSupport (Dist.restrictToSupport_fullSupport s) (Channel.restrictToSupport C s)
    have hER' : normalizedValue hcross.entropy_reduction.scale_coherence
          s.restrictToSupport (Channel.restrictToSupport C s) =
        hcross.entropy_reduction.Hfun s.restrictToSupport -
          posteriorLawIntegral s.restrictToSupport (Channel.restrictToSupport C s)
            hcross.entropy_reduction.Hfun := by
      simpa [normalizedValue] using hER
    change hcross.entropy_reduction.Hfun s =
      normalizedValue hcross.entropy_reduction.scale_coherence s C +
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun
    rw [hH, hV, hI]
    linarith



/-! ## Exported MI theorem with NO cardinal-boundary assumption -/

/- The exported final theorem WITHOUT FiniteCardinalSupportBoundaryAssumptions.
   Uses the boundary-completed cross-prior representation built from the closure hcross. -/
theorem MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hpre : PreEntropyRepresentativeGaugeConventions hfaces hprod)
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    -- coherence clause supplied by the HM interface (marginalValue support-face):
    (hcohRaw : ∀ (hV : PosteriorValueRepresentation F)
      {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) [Nonempty (supportSubtype q)] (d : Dist (supportSubtype q)),
      hint.marginalValue F hV q (Channel.actionPushforward d (supportIncludeKernel q)) =
        hint.marginalValue F hV q.restrictToSupport d)
    (hax : TraceAxioms F) :
    MIRep F := by
  set hcross := crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
    hfaces hhm huniq hprod haff hpre hax with hcrossdef
  -- support_face_scale from hfaces (hcross.scale = hfaces scale by construction)
  have hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A) [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a) (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
        hcross.entropy_reduction.scale_coherence.scale q /
          hcross.entropy_reduction.scale_coherence.scale r.restrictToSupport := by
    intro A _ _ _ q hq r _ hn hnd hb
    exact hfaces.support_face_scale_eq q hq r hn hnd hb
  set hc := wrapCross hcross hsf with hcdef
  -- Hfun of hc is definitionally normalizedValue (boundaryComplete) · id
  have hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hc.entropy_reduction.Hfun q =
        normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel :=
    fun q => rfl
  -- field 1 for hc:
  have hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hc.entropy_reduction.scale_coherence q P =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    intro A O _ _ _ _ _ P q hqb
    exact field1_boundaryComplete hint hcross.entropy_reduction.scale_coherence hsf
      (fun {A} _ _ _ q _ d => hcohRaw hcross.entropy_reduction.scale_coherence.branch_agg.value_rep q d)
      P q hqb
  -- hhfunC: Hfun q = Hfun (q|supp) for hc
  have hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hc.entropy_reduction.Hfun q = hc.entropy_reduction.Hfun q.restrictToSupport := by
    intro A _ _ _ q
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    rw [hHfunId q, hHfunId q.restrictToSupport,
      show normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport Channel.idChannel q) from ?_,
      normalizedValue_restrict_idChannel_eq_idSupport hc.entropy_reduction q]
    by_cases hqf : q.FullSupport
    · exact normalizedValue_support_restrict_fullSupport_of_crossPrior
        F hax hc Channel.idChannel q hqf
    · exact hnormC Channel.idChannel q hqf
  -- hrelabC: full-support relabel invariance of Hfun for hc, via wrapCross bridge + closure relabel
  have hrelabC : ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (qA : Dist A), qA.FullSupport →
      hc.entropy_reduction.Hfun (Relabeling.relabelDist e qA) =
        hc.entropy_reduction.Hfun qA := by
    intro A B _ _ _ _ _ _ e qA hqA
    have hqB : (Relabeling.relabelDist e qA).FullSupport :=
      Relabeling.relabelDist_fullSupport e qA hqA
    rw [wrapCross_Hfun_fullSupport hcross hsf (Relabeling.relabelDist e qA) hqB,
      wrapCross_Hfun_fullSupport hcross hsf qA hqA]
    -- now goal: normalizedValue hcross (relabel e qA) id = normalizedValue hcross qA id
    -- = Hfun(hcross)(relabel) = Hfun(hcross) qA via closure Hfun_relabel_fullSupport + Hcandidate rfl
    have h1 : normalizedValue hcross.entropy_reduction.scale_coherence
        (Relabeling.relabelDist e qA) Channel.idChannel =
        hcross.entropy_reduction.Hfun (Relabeling.relabelDist e qA) := by
      rw [hcrossdef]; rfl
    have h2 : normalizedValue hcross.entropy_reduction.scale_coherence qA Channel.idChannel =
        hcross.entropy_reduction.Hfun qA := by
      rw [hcrossdef]; rfl
    rw [h1, h2, hcrossdef]
    exact Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
      hhm huniq haff hpre hax e qA hqA
  -- hIntC: posterior-law integral support restriction for hc
  have hIntC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      posteriorLawIntegral q P hc.entropy_reduction.Hfun =
        posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
          hc.entropy_reduction.Hfun := by
    intro A O _ _ _ _ _ P q
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    classical
    have hsupport := posteriorLawIntegral_restrictToSupport P q
      (fun d => hc.entropy_reduction.Hfun d)
    rw [hsupport]
    unfold posteriorLawIntegral
    apply Finset.sum_congr rfl
    intro o _
    congr 1
    -- Hfun_supportInclude for hc: Hfun (incl-pushforward t) = Hfun t
    set t := Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o with htdef
    haveI : Nonempty (supportSubtype (Channel.actionPushforward t (supportIncludeKernel q))) :=
      supportSubtype_nonempty _
    haveI : Nonempty (supportSubtype t) := supportSubtype_nonempty t
    have hl := hhfunC (Channel.actionPushforward t (supportIncludeKernel q))
    have hr := hhfunC t
    have hrestrict : (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport =
        Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm t.restrictToSupport :=
      restrict_supportInclude_eq_relabel_support q t
    have hrel := hrelabC (supportIncludePushforwardSupportEquiv q t).symm t.restrictToSupport
      (Dist.restrictToSupport_fullSupport t)
    calc hc.entropy_reduction.Hfun (Channel.actionPushforward t (supportIncludeKernel q))
        = hc.entropy_reduction.Hfun
            (Channel.actionPushforward t (supportIncludeKernel q)).restrictToSupport := hl
      _ = hc.entropy_reduction.Hfun
            (Relabeling.relabelDist (supportIncludePushforwardSupportEquiv q t).symm
              t.restrictToSupport) := by rw [hrestrict]
      _ = hc.entropy_reduction.Hfun t.restrictToSupport := hrel
      _ = hc.entropy_reduction.Hfun t := hr.symm
  -- regularity for hc
  have hreg : EntropyRegularity F hc.entropy_reduction :=
    entropyRegularity_forCross hax hc hHfunId hnormC
  have hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hc.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hc.entropy_reduction.scale_coherence (sigmaDist p q)
          (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hc.entropy_reduction.Hfun :=
    fun {K} _ _ _ Act _ _ _ _ p q => coarseReveal_entropyReduction_ofFacts F hax hc hnormC hhfunC hIntC Act p q
  have hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hc.entropy_reduction.Hfun (blockEmbedDist Act k qk) = hc.entropy_reduction.Hfun qk :=
    fun {K} _ _ _ Act _ _ _ _ k qk => Hfun_blockEmbed_ofFacts F hc hhfunC hrelabC Act k qk
  have hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hc.entropy_reduction.Hfun p :=
    fun {K} _ _ _ Act _ _ _ _ p q => coarseVal_forCross F hax hc hreg hnormC
      (field3_restricted_coarse_reveal F hax hc hreg) hhfunC Act p q
  intro A O instA instDA instO instDO P qq qq'
  exact MIRep_ofCrossFacts hfad F hax hc hreg hER hblockE hcoarse P qq qq' 


/-- Cleanest currently valid final wrapper.

This wrapper discharges the left-slice affine input internally and bundles only
the harmless singleton, representative/gauge, and support-boundary conventions.
The face-scale structure and product quasi-additivity remain explicit because
the current Lean development has no producer for them from just
`TraceAxioms F` and HM. -/
theorem MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hconv : FinalHarmlessConventions hfaces hprod)
    (hax : TraceAxioms F) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal
    hfad hfaces hhm classicalFiniteAffineUtilityUniquenessAssumptions
    (haff := finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      hhm hconv.singleton_slice)
    hconv.pre_entropy
    (finitePosteriorIntegralRepresentation_of_HM hhm)
    (fun hV {A} _ _ _ q _ d =>
      (finitePosteriorIntegralRepresentation_of_HM hhm).marginalValue_support_face
        F hV q d)
    hax

/-- Final MI route through an explicitly constructed product-normalised
face-scale representative.

The theorem no longer takes `hfaces` or `hprod` as standalone inputs.  It first
constructs the raw face-scale representative from the data-carrying HM
interface and faithful branch/coherent-scale components, applies the selected
positive product gauge, constructs product quasi-additivity for that
post-gauge representative, and then calls the existing Stage-F MI theorem. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConstructedPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hscaleRelabel :
      FiniteChainScaleRelabelingAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hfaceScale :
      FiniteSupportFaceScaleAssumptionsFor
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (rawCoherentFaceScales_of_FinalHM_faithfulBranch
          hhm hfaith hax hscaleRelabel hfaceScale))
    (hsingle :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge))
    (hconv :
      FinalHarmlessConventions
        (productNormalizedFaceScales_of_FinalHM_gauge
          hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge)
        (productQuasiAdditivity_of_FinalHM_gauge
          hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge
          htriple hsingle)) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    hfad
    (productNormalizedFaceScales_of_FinalHM_gauge
      hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge)
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
    (hprod :=
      productQuasiAdditivity_of_FinalHM_gauge
        hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge
        htriple hsingle)
    hconv hax

/-- Final MI route through the corrected "choose gauge, then name the coherent
face scales" dependency order.

Compared with `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConstructedPreEntropy`,
this theorem does not require raw chain-scale relabelling or raw support-face
scale compatibility.  Instead, it starts from the faithful branch/cocycle/scale
package and a positive gauge whose transformed scale satisfies those two
coherence equations. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withPositiveGaugePreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hcurrentGauge : FiniteFaceScaleProductGaugeConventionFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hsingle :
      FiniteFaceScaleSingletonInteractionConventionFor hpair)
    (hconv :
      FinalHarmlessConventions
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport)
        (productQuasiAdditivity_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport
          hpair hcurrentGauge hassoc hsingle)) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    hfad
    (coherentFaceScales_of_FinalHM_positiveGauge
      hhm hfaith hax hgauge hrel hsupport)
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
    (hprod :=
      productQuasiAdditivity_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport
        hpair hcurrentGauge hassoc hsingle)
    hconv hax

/-- Final MI route through the corrected positive-gauge dependency order, with
product interaction associativity derived internally from value-level
triple-product associativity. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withPositiveGaugeProductData
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hcurrentGauge : FiniteFaceScaleProductGaugeConventionFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingle :
      FiniteFaceScaleSingletonInteractionConventionFor hpair)
    (hconv :
      FinalHarmlessConventions
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport)
        (productQuasiAdditivity_of_FinalHM_positiveGaugeProductData
          hhm hfaith hax hgauge hrel hsupport
          hpair hcurrentGauge htriple hsingle)) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    hfad
    (coherentFaceScales_of_FinalHM_positiveGauge
      hhm hfaith hax hgauge hrel hsupport)
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
    (hprod :=
      productQuasiAdditivity_of_FinalHM_positiveGaugeProductData
        hhm hfaith hax hgauge hrel hsupport
        hpair hcurrentGauge htriple hsingle)
    hconv hax

/-- Final MI route through positive-gauge source product data.  This theorem
does not take `hfaces`, `hprod`, or the opaque pairwise-bilinearity package as
inputs: the face scales are constructed from the positive gauge, product
quasi-additivity is reconstructed from HM left-slice affinity plus
intercept/slope product data, and then the existing Stage-F theorem is applied.
-/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withPositiveGaugeSourceProductData
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          hintercept hslope))
    (hconv :
      FinalHarmlessConventions
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport)
        (productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData
          hhm hfaith hax hgauge hrel hsupport hsingleSlice
          hintercept hslope hcurrentGauge htriple hsingleInteraction)) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    hfad
    (coherentFaceScales_of_FinalHM_positiveGauge
      hhm hfaith hax hgauge hrel hsupport)
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
    (hprod :=
      productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData
        hhm hfaith hax hgauge hrel hsupport hsingleSlice
        hintercept hslope hcurrentGauge htriple hsingleInteraction)
    hconv hax

/-- Final MI route with the faithful branch package constructed from explicit
support/boundary/singleton conventions, and product quasi-additivity
constructed from positive-gauge source product data.

This is the strongest current theorem in this file: it does not take
`hfaces`, `hprod`, `hfaith`, or `hpair` as standalone inputs. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withBranchConventionsAndPositiveGaugeSourceProductData
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm hbranchConv)
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm hbranchConv)
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport))
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          hintercept hslope))
    (hconv :
      FinalHarmlessConventions
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport)
        (productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport hsingleSlice
          hintercept hslope hcurrentGauge htriple hsingleInteraction)) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_withPositiveGaugeSourceProductData
    hfad hhm
    (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
      hhm hbranchConv)
    hax hgauge hrel hsupport hsingleSlice
    hintercept hslope hcurrentGauge htriple hsingleInteraction hconv

/-- Final MI route with faithful branch conventions and positive-gauge product
data, with product intercept positive-linearity discharged internally. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withBranchConventionsAndPositiveGaugeProductData_internalIntercept
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm hbranchConv)
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm hbranchConv)
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm hbranchConv)
            hax hgauge hrel hsupport hsingleSlice)
          hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm hbranchConv)
            hax hgauge hrel hsupport hsingleSlice)
          hslope))
    (hconv :
      FinalHarmlessConventions
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport)
        (productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData_internalIntercept
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport hsingleSlice
          hslope hcurrentGauge htriple hsingleInteraction)) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    hfad
    (coherentFaceScales_of_FinalHM_positiveGauge
      hhm
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
        hhm hbranchConv)
      hax hgauge hrel hsupport)
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
    (hprod :=
      productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData_internalIntercept
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm hbranchConv)
        hax hgauge hrel hsupport hsingleSlice
        hslope hcurrentGauge htriple hsingleInteraction)
    hconv hax

/-- Final MI route through constructed positive-gauge face scales and
product-normalized selected representatives.

Compared with
`MIRep_of_TraceAxioms_FinalHM_Faddeev_withBranchConventionsAndPositiveGaugeProductData_internalIntercept`,
this theorem no longer asks for product-slope affinity or triple-product value
associativity.  Both are derived from the selected relabeling package obtained
from `FiniteProductNormalizedSelectedRepresentativesFor`. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withProductNormalizedSelectedRepresentatives
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    (hgauge : PositiveFaceScaleGauge.{u})
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
        hgauge.gauge (Relabeling.relabelDist e q) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale (Relabeling.relabelDist e q) =
          hgauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q)
    (hsupport :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
        [Nonempty (supportSubtype r)]
        (_hr_nonempty : ∃ a : A, 0 < r a)
        (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
        (_hr_boundary : ¬ r.FullSupport),
        (hgauge.gauge q / hgauge.gauge r) *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).branch_agg.branchCoeff q r =
          (hgauge.gauge q *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm hbranchConv)
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale q) /
            (hgauge.gauge r.restrictToSupport *
              (BranchAggregationCocycleNormalizedChainRule_of_faithful
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm hbranchConv)
                F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
              ).scale_factorization.scale r.restrictToSupport))
    (hsingleSlice :
      FiniteFaceScaleSingletonSliceAffineConventionFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport))
    (hnorm :
      FiniteProductNormalizedSelectedRepresentativesFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport))
    (hcurrentGauge :
      FiniteFaceScaleProductGaugeConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm hbranchConv)
            hax hgauge hrel hsupport hsingleSlice)
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
              hnorm)
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              hax hgauge hrel hsupport hsingleSlice))))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionConventionFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm hbranchConv)
            hax hgauge hrel hsupport hsingleSlice)
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
              hnorm)
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hbranchConv)
              hax hgauge hrel hsupport hsingleSlice))))
    (hconv :
      FinalHarmlessConventions
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport)
        (productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hbranchConv)
          hax hgauge hrel hsupport hsingleSlice hnorm
          hcurrentGauge hsingleInteraction)) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    hfad
    (coherentFaceScales_of_FinalHM_positiveGauge
      hhm
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
        hhm hbranchConv)
      hax hgauge hrel hsupport)
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
    (hprod :=
      productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm hbranchConv)
        hax hgauge hrel hsupport hsingleSlice hnorm
        hcurrentGauge hsingleInteraction)
    hconv hax

/-- Final harmless representative/gauge/support conventions for the constructed
pre-entropy route.

The bundle is deliberately dependent on the data-carrying HM interface and the
primitive trace axioms because the selected face-scale representative is
constructed from them before the product-normalising gauge is chosen.  It does
not contain `hfaces` or `hprod` as fields; those are reconstructed from the
preceding fields. -/
structure FinalConstructedRepresentativeConventions
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) where
  branch : FinalFaithfulBranchConventions hhm
  gauge : PositiveFaceScaleGauge.{u}
  scale_relabel :
    ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A) (_hq : q.FullSupport),
      gauge.gauge (Relabeling.relabelDist e q) *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale (Relabeling.relabelDist e q) =
        gauge.gauge q *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale q
  support_scale :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      (gauge.gauge q / gauge.gauge r) *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).branch_agg.branchCoeff q r =
        (gauge.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm branch)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q) /
          (gauge.gauge r.restrictToSupport *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm branch)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale r.restrictToSupport)
  singleton_slice :
    FiniteFaceScaleSingletonSliceAffineConventionFor
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax gauge scale_relabel support_scale)
  product_normalized :
    FiniteProductNormalizedSelectedRepresentativesFor
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax gauge scale_relabel support_scale)
  current_product_gauge :
    FiniteFaceScaleProductGaugeConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          singleton_slice)
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax gauge scale_relabel support_scale singleton_slice)
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
            product_normalized)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale singleton_slice)))
  singleton_interaction :
    FiniteFaceScaleSingletonInteractionConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          singleton_slice)
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax gauge scale_relabel support_scale singleton_slice)
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
            product_normalized)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale singleton_slice)))
  harmless :
    FinalHarmlessConventions
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax gauge scale_relabel support_scale)
      (productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax gauge scale_relabel support_scale singleton_slice
        product_normalized current_product_gauge singleton_interaction)

/-- Clean final route through the constructed product-normalised representative.

This is the exported theorem matching the corrected TeX dependency order:
`TraceAxioms + HM data + Faddeev + harmless representative/gauge/support
conventions` produce `MIRep F`.  The coherent face-scale representative and its
product quasi-additivity proof are constructed internally and are not theorem
inputs. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventions hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_withProductNormalizedSelectedRepresentatives
    hfad hhm hconv.branch hax hconv.gauge hconv.scale_relabel
    hconv.support_scale hconv.singleton_slice hconv.product_normalized
    hconv.current_product_gauge hconv.singleton_interaction hconv.harmless


end TraceableAgency
