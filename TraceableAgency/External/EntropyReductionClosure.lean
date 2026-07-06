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

/-- The trivial (constant `1`) positive face-scale gauge.  Choosing this gauge
makes the gauge-equivariance conventions (`gauge_relabel`) hold by `rfl` and
reduces the gauged `scale_relabel`/`support_scale` obligations to their raw
(ungauged) forms. -/
noncomputable def constGaugeOne : PositiveFaceScaleGauge.{u} where
  gauge := fun _ => 1
  gauge_pos := fun _ => one_pos

/-- **The singleton-slice affine convention is a theorem** (for every coherent
face-scale representative).

On a subsingleton first factor `A`, the product left-slice value
`faceScaleProductLeftSliceValue q r R P = V (q⊗r) (P⊗R)` is `P`-invariant: the
first-factor observation is uninformative, so `P⊗R` and `U_A⊗R` induce the same
posterior law (`samePosteriorLawExp_prodChannel_singleton_fst`), and `V` respects
posterior-law equivalence.  Since also `V q (exp P) = 0` on a subsingleton
(`V_channel_eq_zero_of_subsingleton`), the affine relation holds with slope `a = 1`
and intercept the (`P`-independent) value at `U_A`.  This discharges the
`singleton_slice` convention with no assumption. -/

theorem finiteFaceScaleSingletonSliceAffine_of_faces
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleSingletonSliceAffineConventionFor hfaces where
  singleton_left_slice_positive_affine_transform := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr hA R
    refine ⟨1, faceScaleProductLeftSliceValue hfaces q r R (Channel.uninformativeChannelU A),
      one_pos, ?_⟩
    intro O _ _ P
    haveI : Subsingleton A := hA
    have hVzero : hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) = 0 :=
      V_channel_eq_zero_of_subsingleton F hfaces.branch_result.branch_agg.value_rep q hq P
    rw [hVzero, mul_zero, zero_add]
    show hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R))
    exact hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law _ _ _
      (samePosteriorLawExp_prodChannel_singleton_fst q r P R)

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

/-- Precomposition of an atomic-linear law by an arbitrary map on distributions
is atomic-linear: push each atom's point along the map. -/
noncomputable def atomicLinear_precompose {S T : Type u}
    [Fintype S] [DecidableEq S] [Nonempty S] [Fintype T] [DecidableEq T] [Nonempty T]
    (g : Dist S → Dist T) {η : PosteriorLawSigned S}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear
      (fun ψ : Dist T → ℝ => η (fun d => ψ (g d))) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i => g (hη.witness.point i)
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext ψ
    show (∑ i : hη.witness.I, hη.witness.weight i * ψ (g (hη.witness.point i))) =
      η (fun d => ψ (g d))
    have h := congrFun hη.eval_eq (fun d => ψ (g d))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

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

/-- **Harmless conventions with the singleton-slice field eliminated.**

The `singleton_slice` field of `FinalHarmlessConventions`
(`FiniteFaceScaleSingletonSliceAffineConventionFor`) is a **theorem** for every
coherent face-scale representative (`finiteFaceScaleSingletonSliceAffine_of_faces`):
on a subsingleton first factor the product left-slice value is `P`-invariant (the
first-factor observation is uninformative, so `P⊗R` and `U_A⊗R` induce the same
posterior law) and the base value is zero, so the affine relation holds with
slope `1` and the (`P`-independent) intercept.  Hence it need not be assumed.
This bundle carries only the genuine residual `pre_entropy`. -/
structure FinalHarmlessConventionsWithoutSingletonSlice
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  pre_entropy :
    PreEntropyRepresentativeGaugeConventions hfaces hprod

/-- The singleton-slice field is discharged by
`finiteFaceScaleSingletonSliceAffine_of_faces`, so the full harmless bundle is
reconstructed from the slimmer one carrying only `pre_entropy`. -/
theorem finalHarmlessConventions_of_withoutSingletonSlice
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (h : FinalHarmlessConventionsWithoutSingletonSlice hfaces hprod) :
    FinalHarmlessConventions hfaces hprod where
  singleton_slice := finiteFaceScaleSingletonSliceAffine_of_faces hfaces
  pre_entropy := h.pre_entropy

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


/-! ## Boundary block-comparison lift (support face → ambient boundary prior)

`boundary_block_lift` transports a block preference comparison from the
full-support face `supp(r)` to the ambient boundary prior `r`, via support
restriction on `A ⊕ A`, a bijective action relabel, and an A4 outcome garbling
(extra outcome slots carry zero posterior mass).  Boundary analogue of
`block_rel_of_channel_value_ge`. -/

noncomputable def inlSupportEquiv {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) : supportSubtype (inlDist r : Dist (A ⊕ A)) ≃ supportSubtype r where
  toFun := fun x => by rcases x with ⟨ab, hab⟩; cases ab with
    | inl a => exact ⟨a, hab⟩
    | inr a => exact absurd hab (by simp [inlDist])
  invFun := fun y => ⟨Sum.inl y.1, y.2⟩
  left_inv := by rintro ⟨ab, hab⟩; cases ab with
    | inl a => rfl
    | inr a => exact absurd hab (by simp [inlDist])
  right_inv := by rintro ⟨a, ha⟩; rfl
noncomputable def inrSupportEquiv {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) : supportSubtype (inrDist r : Dist (A ⊕ A)) ≃ supportSubtype r where
  toFun := fun x => by rcases x with ⟨ab, hab⟩; cases ab with
    | inl a => exact absurd hab (by simp [inrDist])
    | inr a => exact ⟨a, hab⟩
  invFun := fun y => ⟨Sum.inr y.1, y.2⟩
  left_inv := by rintro ⟨ab, hab⟩; cases ab with
    | inl a => exact absurd hab (by simp [inrDist])
    | inr a => rfl
  right_inv := by rintro ⟨a, ha⟩; rfl

theorem inlSupportEquiv_symm_apply {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (y : supportSubtype r) :
    (inlSupportEquiv r).symm y = ⟨Sum.inl y.1, y.2⟩ := rfl

theorem inrSupportEquiv_symm_apply {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (y : supportSubtype r) :
    (inrSupportEquiv r).symm y = ⟨Sum.inr y.1, y.2⟩ := rfl

/-! ## Prior relabelling identities -/

section Priors
variable {A B C D : Type u}

theorem relabelDist_sumCongr_inlDist
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (e1 : A ≃ C) (e2 : B ≃ D) (d : Dist A) :
    Relabeling.relabelDist (Equiv.sumCongr e1 e2) (inlDist d : Dist (A ⊕ B)) =
      (inlDist (Relabeling.relabelDist e1 d) : Dist (C ⊕ D)) := by
  ext x
  cases x with
  | inl c => simp [Relabeling.relabelDist, inlDist, Equiv.sumCongr]
  | inr d => simp [Relabeling.relabelDist, inlDist, Equiv.sumCongr]

theorem relabelDist_sumCongr_inrDist
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C] [Fintype D] [DecidableEq D]
    (e1 : A ≃ C) (e2 : B ≃ D) (d : Dist B) :
    Relabeling.relabelDist (Equiv.sumCongr e1 e2) (inrDist d : Dist (A ⊕ B)) =
      (inrDist (Relabeling.relabelDist e2 d) : Dist (C ⊕ D)) := by
  ext x
  cases x with
  | inl c => simp [Relabeling.relabelDist, inrDist, Equiv.sumCongr]
  | inr d => simp [Relabeling.relabelDist, inrDist, Equiv.sumCongr]
end Priors

theorem relabel_inlSupportEquiv_restrict {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) :
    Relabeling.relabelDist (inlSupportEquiv r) ((inlDist r).restrictToSupport) =
      r.restrictToSupport := by
  ext y
  rw [Relabeling.relabelDist_apply, inlSupportEquiv_symm_apply]
  simp [Dist.restrictToSupport, inlDist]

theorem relabel_inrSupportEquiv_restrict {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) :
    Relabeling.relabelDist (inrSupportEquiv r) ((inrDist r).restrictToSupport) =
      r.restrictToSupport := by
  ext y
  rw [Relabeling.relabelDist_apply, inrSupportEquiv_symm_apply]
  simp [Dist.restrictToSupport, inrDist]

/-! ## Outcome embedding / collapse kernels -/

section Kernels
variable {O Y : Type u} [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]

noncomputable def embedLeftKernel : Channel O (O ⊕ Y) := fun o => Dist.pure (Sum.inl o)
noncomputable def embedRightKernel : Channel Y (O ⊕ Y) := fun y => Dist.pure (Sum.inr y)
noncomputable def collapseLeftKernel [Nonempty O] : Channel (O ⊕ Y) O :=
  fun oy => match oy with
    | Sum.inl o => Dist.pure o
    | Sum.inr _ => Dist.pure (Classical.arbitrary O)
noncomputable def collapseRightKernel [Nonempty Y] : Channel (O ⊕ Y) Y :=
  fun oy => match oy with
    | Sum.inl _ => Dist.pure (Classical.arbitrary Y)
    | Sum.inr y => Dist.pure y

/-- Embedding left outcomes then collapsing recovers the original channel. -/
theorem postprocess_embedLeft_collapseLeft {A : Type u} [Fintype A] [DecidableEq A] [Nonempty O]
    (R : Channel A O) :
    Channel.postprocess (Channel.postprocess R (embedLeftKernel (Y := Y))) collapseLeftKernel = R := by
  funext a
  apply Dist.ext
  intro o
  show (∑ w : O ⊕ Y, (Channel.postprocess R embedLeftKernel) a w * collapseLeftKernel w o) = R a o
  have step : ∀ w : O ⊕ Y, (Channel.postprocess R (embedLeftKernel (Y := Y))) a w
      = (match w with | Sum.inl o' => R a o' | Sum.inr _ => 0) := by
    intro w
    show (∑ o' : O, R a o' * embedLeftKernel o' w) = _
    cases w with
    | inl v =>
      rw [Fintype.sum_eq_single v]
      · simp [embedLeftKernel]
      · intro o'' ho''
        rw [embedLeftKernel, Dist.pure_apply_ne _ _ (fun h => ho'' (Sum.inl.inj h).symm), mul_zero]
    | inr v =>
      apply Finset.sum_eq_zero
      intro o' _
      rw [embedLeftKernel, Dist.pure_apply_ne _ _ (by simp), mul_zero]
  rw [Fintype.sum_congr _ _ (fun w => by rw [step w])]
  rw [Fintype.sum_sum_type]
  simp only [collapseLeftKernel]
  rw [Fintype.sum_eq_single o]
  · simp
  · intro o'' ho''
    rw [Dist.pure_apply_ne _ _ (fun h => ho'' h.symm), mul_zero]

/-- Embedding right outcomes then collapsing recovers the original channel. -/
theorem postprocess_embedRight_collapseRight {A : Type u} [Fintype A] [DecidableEq A] [Nonempty Y]
    (R : Channel A Y) :
    Channel.postprocess (Channel.postprocess R (embedRightKernel (O := O))) collapseRightKernel = R := by
  funext a
  apply Dist.ext
  intro y
  show (∑ w : O ⊕ Y, (Channel.postprocess R embedRightKernel) a w * collapseRightKernel w y) = R a y
  have step : ∀ w : O ⊕ Y, (Channel.postprocess R (embedRightKernel (O := O))) a w
      = (match w with | Sum.inl _ => 0 | Sum.inr y' => R a y') := by
    intro w
    show (∑ y' : Y, R a y' * embedRightKernel y' w) = _
    cases w with
    | inl v =>
      apply Finset.sum_eq_zero
      intro y' _
      rw [embedRightKernel, Dist.pure_apply_ne _ _ (by simp), mul_zero]
    | inr v =>
      rw [Fintype.sum_eq_single v]
      · simp [embedRightKernel]
      · intro y'' hy''
        rw [embedRightKernel, Dist.pure_apply_ne _ _ (fun h => hy'' (Sum.inr.inj h).symm), mul_zero]
  rw [Fintype.sum_congr _ _ (fun w => by rw [step w])]
  rw [Fintype.sum_sum_type]
  simp only [collapseRightKernel]
  rw [Fintype.sum_eq_single y]
  · simp
  · intro y'' hy''
    rw [Dist.pure_apply_ne _ _ (fun h => hy'' h.symm), mul_zero]

end Kernels

/-! ## Boundary block channel equals a block of embedded face channels -/

theorem relabel_boundaryBlock_eq_embeddedFace
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (r : Dist A) (P : Channel A O) (Q : Channel A Y) :
    Relabeling.relabelChannel (Equiv.sumCongr (inlSupportEquiv r) (inrSupportEquiv r))
        (Equiv.refl ((O ⊕ Y) ⊕ (O ⊕ Y)))
        (blockChannel ((blockChannel P Q).restrictToSupport (inlDist r))
          ((blockChannel P Q).restrictToSupport (inrDist r)))
      =
      blockChannel (Channel.postprocess (Channel.restrictToSupport P r) embedLeftKernel)
        (Channel.postprocess (Channel.restrictToSupport Q r) embedRightKernel) := by
  funext b
  cases b with
  | inl s =>
    apply Dist.ext
    intro w
    cases w with
    | inl v =>
      show (blockChannel P Q) (Sum.inl s.1) v
        = ∑ o : O, P s.1 o * (embedLeftKernel o v)
      cases v with
      | inl o' =>
        simp only [embedLeftKernel]
        rw [Fintype.sum_eq_single o']
        · simp [blockChannel]
        · intro o'' ho''
          rw [Dist.pure_apply_ne _ _ (fun h => ho'' (Sum.inl.inj h).symm), mul_zero]
      | inr y' =>
        simp only [embedLeftKernel, blockChannel]
        symm
        apply Finset.sum_eq_zero
        intro o _
        simp [Dist.pure_apply_ne]
    | inr v =>
      show (0 : ℝ) = 0
      rfl
  | inr s =>
    apply Dist.ext
    intro w
    cases w with
    | inl v =>
      show (0 : ℝ) = 0
      rfl
    | inr v =>
      show (blockChannel P Q) (Sum.inr s.1) v
        = ∑ y : Y, Q s.1 y * (embedRightKernel y v)
      cases v with
      | inl o' =>
        simp only [embedRightKernel, blockChannel]
        symm
        apply Finset.sum_eq_zero
        intro y _
        simp [Dist.pure_apply_ne]
      | inr y' =>
        simp only [embedRightKernel]
        rw [Fintype.sum_eq_single y']
        · simp [blockChannel]
        · intro y'' hy''
          rw [Dist.pure_apply_ne _ _ (fun h => hy'' (Sum.inr.inj h).symm), mul_zero]

/-! ## Main theorem -/

theorem boundary_block_lift
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P : Channel A O) (Q : Channel A Y)
    (hface : F.rel (blockChannel (Channel.restrictToSupport P r) (Channel.restrictToSupport Q r))
      (inlDist r.restrictToSupport) (inrDist r.restrictToSupport)) :
    F.rel (blockChannel P Q) (inlDist r) (inrDist r) := by
  classical
  -- Nonempty O, Nonempty Y from a support element.
  obtain ⟨s0⟩ := (inferInstance : Nonempty (supportSubtype r))
  haveI hNO : Nonempty O := Relabeling.nonempty_of_dist (P s0.1)
  haveI hNY : Nonempty Y := Relabeling.nonempty_of_dist (Q s0.1)
  -- Step 0: support restriction reduces to the boundary restricted block comparison.
  rw [preference_support_restriction_of_axioms F hax (blockChannel P Q) (inlDist r) (inrDist r)]
  -- Step 1: action-relabel the boundary block channel to the support of `r`.
  set eA : (supportSubtype (inlDist r : Dist (A ⊕ A))) ⊕ (supportSubtype (inrDist r : Dist (A ⊕ A)))
      ≃ supportSubtype r ⊕ supportSubtype r :=
    Equiv.sumCongr (inlSupportEquiv r) (inrSupportEquiv r) with heA
  rw [relabel_rel_action_of_axioms F hax eA
        (blockChannel ((blockChannel P Q).restrictToSupport (inlDist r))
          ((blockChannel P Q).restrictToSupport (inrDist r)))
        (inlDist (inlDist r).restrictToSupport)
        (inrDist (inrDist r).restrictToSupport)]
  -- Rewrite the relabelled channel and priors (matching the goal's `eA`).
  have hC : Relabeling.relabelChannel eA (Equiv.refl ((O ⊕ Y) ⊕ (O ⊕ Y)))
        (blockChannel ((blockChannel P Q).restrictToSupport (inlDist r))
          ((blockChannel P Q).restrictToSupport (inrDist r)))
      = blockChannel (Channel.postprocess (Channel.restrictToSupport P r) (embedLeftKernel (Y := Y)))
          (Channel.postprocess (Channel.restrictToSupport Q r) (embedRightKernel (O := O))) := by
    rw [heA]; exact relabel_boundaryBlock_eq_embeddedFace r P Q
  have hpl : Relabeling.relabelDist eA (inlDist (inlDist r).restrictToSupport)
      = (inlDist r.restrictToSupport : Dist (supportSubtype r ⊕ supportSubtype r)) := by
    rw [heA, relabelDist_sumCongr_inlDist, relabel_inlSupportEquiv_restrict]
  have hpr : Relabeling.relabelDist eA (inrDist (inrDist r).restrictToSupport)
      = (inrDist r.restrictToSupport : Dist (supportSubtype r ⊕ supportSubtype r)) := by
    rw [heA, relabelDist_sumCongr_inrDist, relabel_inrSupportEquiv_restrict]
  -- Step 2: replace embedded face channels by the face channels via A4 garbling.
  set Ps : Channel (supportSubtype r) O := Channel.restrictToSupport P r with hPs
  set Qs : Channel (supportSubtype r) Y := Channel.restrictToSupport Q r with hQs
  set rs : Dist (supportSubtype r) := r.restrictToSupport with hrs
  have hleft_to_new :
      F.rel (blockChannel Ps (Channel.postprocess Ps (embedLeftKernel (Y := Y)))) (inlDist rs) (inrDist rs) :=
    hax.a4 Ps (embedLeftKernel (Y := Y)) rs
  have hleft_to_old :
      F.rel (blockChannel (Channel.postprocess Ps (embedLeftKernel (Y := Y))) Ps) (inlDist rs) (inrDist rs) := by
    have h := hax.a4 (Channel.postprocess Ps (embedLeftKernel (Y := Y))) collapseLeftKernel rs
    rwa [postprocess_embedLeft_collapseLeft Ps] at h
  have hright_to_new :
      F.rel (blockChannel Qs (Channel.postprocess Qs (embedRightKernel (O := O)))) (inlDist rs) (inrDist rs) :=
    hax.a4 Qs (embedRightKernel (O := O)) rs
  have hright_to_old :
      F.rel (blockChannel (Channel.postprocess Qs (embedRightKernel (O := O))) Qs) (inlDist rs) (inrDist rs) := by
    have h := hax.a4 (Channel.postprocess Qs (embedRightKernel (O := O))) collapseRightKernel rs
    rwa [postprocess_embedRight_collapseRight Qs] at h
  have hgoal :
      F.rel (blockChannel (Channel.postprocess Ps (embedLeftKernel (Y := Y)))
          (Channel.postprocess Qs (embedRightKernel (O := O)))) (inlDist rs) (inrDist rs) :=
    (blackwell_pairwise_block_replacement_from_weak_equiv F hax
      Ps (Channel.postprocess Ps (embedLeftKernel (Y := Y)))
      Qs (Channel.postprocess Qs (embedRightKernel (O := O)))
      rs rs rs rs
      hleft_to_new hleft_to_old hright_to_new hright_to_old).mp hface
  -- Transport hgoal back to the relabelled form via hC, hpl, hpr.
  rw [← hC, ← hpl, ← hpr] at hgoal
  exact hgoal


#print axioms TraceableAgency.boundary_block_lift

/-- **Boundary block-comparison IFF.**  The whole `boundary_block_lift` chain
(support restriction, action relabelling, Blackwell block replacement) is an
equivalence, so the ambient boundary block comparison is equivalent to the
support-face block comparison in BOTH directions. -/
theorem boundary_block_lift_iff
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P : Channel A O) (Q : Channel A Y) :
    F.rel (blockChannel P Q) (inlDist r) (inrDist r) ↔
      F.rel (blockChannel (Channel.restrictToSupport P r) (Channel.restrictToSupport Q r))
        (inlDist r.restrictToSupport) (inrDist r.restrictToSupport) := by
  classical
  obtain ⟨s0⟩ := (inferInstance : Nonempty (supportSubtype r))
  haveI hNO : Nonempty O := Relabeling.nonempty_of_dist (P s0.1)
  haveI hNY : Nonempty Y := Relabeling.nonempty_of_dist (Q s0.1)
  set eA : (supportSubtype (inlDist r : Dist (A ⊕ A))) ⊕ (supportSubtype (inrDist r : Dist (A ⊕ A)))
      ≃ supportSubtype r ⊕ supportSubtype r :=
    Equiv.sumCongr (inlSupportEquiv r) (inrSupportEquiv r) with heA
  have hC : Relabeling.relabelChannel eA (Equiv.refl ((O ⊕ Y) ⊕ (O ⊕ Y)))
        (blockChannel ((blockChannel P Q).restrictToSupport (inlDist r))
          ((blockChannel P Q).restrictToSupport (inrDist r)))
      = blockChannel (Channel.postprocess (Channel.restrictToSupport P r) (embedLeftKernel (Y := Y)))
          (Channel.postprocess (Channel.restrictToSupport Q r) (embedRightKernel (O := O))) := by
    rw [heA]; exact relabel_boundaryBlock_eq_embeddedFace r P Q
  have hpl : Relabeling.relabelDist eA (inlDist (inlDist r).restrictToSupport)
      = (inlDist r.restrictToSupport : Dist (supportSubtype r ⊕ supportSubtype r)) := by
    rw [heA, relabelDist_sumCongr_inlDist, relabel_inlSupportEquiv_restrict]
  have hpr : Relabeling.relabelDist eA (inrDist (inrDist r).restrictToSupport)
      = (inrDist r.restrictToSupport : Dist (supportSubtype r ⊕ supportSubtype r)) := by
    rw [heA, relabelDist_sumCongr_inrDist, relabel_inrSupportEquiv_restrict]
  set Ps : Channel (supportSubtype r) O := Channel.restrictToSupport P r with hPs
  set Qs : Channel (supportSubtype r) Y := Channel.restrictToSupport Q r with hQs
  set rs : Dist (supportSubtype r) := r.restrictToSupport with hrs
  have hleft_to_new :
      F.rel (blockChannel Ps (Channel.postprocess Ps (embedLeftKernel (Y := Y)))) (inlDist rs) (inrDist rs) :=
    hax.a4 Ps (embedLeftKernel (Y := Y)) rs
  have hleft_to_old :
      F.rel (blockChannel (Channel.postprocess Ps (embedLeftKernel (Y := Y))) Ps) (inlDist rs) (inrDist rs) := by
    have h := hax.a4 (Channel.postprocess Ps (embedLeftKernel (Y := Y))) collapseLeftKernel rs
    rwa [postprocess_embedLeft_collapseLeft Ps] at h
  have hright_to_new :
      F.rel (blockChannel Qs (Channel.postprocess Qs (embedRightKernel (O := O)))) (inlDist rs) (inrDist rs) :=
    hax.a4 Qs (embedRightKernel (O := O)) rs
  have hright_to_old :
      F.rel (blockChannel (Channel.postprocess Qs (embedRightKernel (O := O))) Qs) (inlDist rs) (inrDist rs) := by
    have h := hax.a4 (Channel.postprocess Qs (embedRightKernel (O := O))) collapseRightKernel rs
    rwa [postprocess_embedRight_collapseRight Qs] at h
  have hbw :
      F.rel (blockChannel Ps Qs) (inlDist rs) (inrDist rs)
      ↔ F.rel (blockChannel (Channel.postprocess Ps (embedLeftKernel (Y := Y)))
          (Channel.postprocess Qs (embedRightKernel (O := O)))) (inlDist rs) (inrDist rs) :=
    blackwell_pairwise_block_replacement_from_weak_equiv F hax
      Ps (Channel.postprocess Ps (embedLeftKernel (Y := Y)))
      Qs (Channel.postprocess Qs (embedRightKernel (O := O)))
      rs rs rs rs
      hleft_to_new hleft_to_old hright_to_new hright_to_old
  have step1 := preference_support_restriction_of_axioms F hax (blockChannel P Q) (inlDist r) (inrDist r)
  have step2 := relabel_rel_action_of_axioms F hax eA
        (blockChannel ((blockChannel P Q).restrictToSupport (inlDist r))
          ((blockChannel P Q).restrictToSupport (inrDist r)))
        (inlDist (inlDist r).restrictToSupport)
        (inrDist (inrDist r).restrictToSupport)
  constructor
  · intro hamb
    have hrel := step2.mp (step1.mp hamb)
    apply hbw.mpr
    rw [← hC, ← hpl, ← hpr]
    exact hrel
  · intro hface
    have h := hbw.mp hface
    rw [← hC, ← hpl, ← hpr] at h
    exact step1.mpr (step2.mpr h)

/-- **STRICT boundary block-comparison lift.**  A strict support-face block
comparison lifts to a strict ambient boundary block comparison.  The weak part
uses `boundary_block_lift_iff`; the "not reversed" part descends the hypothetical
reversal back to the face via block-swap and the iff, contradicting the strict
face hypothesis. -/
theorem boundary_block_lift_strict
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (P : Channel A O) (Q : Channel A Y)
    (hface_strict : F.strictRel (blockChannel (Channel.restrictToSupport P r) (Channel.restrictToSupport Q r))
      (inlDist r.restrictToSupport) (inrDist r.restrictToSupport)) :
    F.strictRel (blockChannel P Q) (inlDist r) (inrDist r) := by
  obtain ⟨hface_rel, hface_nrev⟩ := hface_strict
  refine ⟨(boundary_block_lift_iff F hax r P Q).mpr hface_rel, ?_⟩
  intro hrev
  have hQP : F.rel (blockChannel Q P) (inlDist r) (inrDist r) :=
    (Relabeling.block_swap_rel_of_axioms F hax P Q r r).mp hrev
  have hface_QP : F.rel (blockChannel (Channel.restrictToSupport Q r) (Channel.restrictToSupport P r))
      (inlDist r.restrictToSupport) (inrDist r.restrictToSupport) :=
    (boundary_block_lift_iff F hax r Q P).mp hQP
  have hface_rev : F.rel (blockChannel (Channel.restrictToSupport P r) (Channel.restrictToSupport Q r))
      (inrDist r.restrictToSupport) (inlDist r.restrictToSupport) :=
    (Relabeling.block_swap_rel_of_axioms F hax (Channel.restrictToSupport P r)
      (Channel.restrictToSupport Q r) r.restrictToSupport r.restrictToSupport).mpr hface_QP
  exact hface_nrev hface_rev

/-! ## Phase 4: boundary marginal-value transport core (proved from the strict
boundary block lift).  These build the atomic-linear boundary sign-agreement and
the per-representative boundary scalar. -/

noncomputable def extendFace {A Z : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Z] [DecidableEq Z]
    (r : Dist A) (Q : Channel (supportSubtype r) Z) (ζ : Dist Z) : Channel A Z :=
  fun a => if h : 0 < r a then Q ⟨a, h⟩ else ζ

theorem restrictToSupport_extendFace {A Z : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Z] [DecidableEq Z]
    (r : Dist A) (Q : Channel (supportSubtype r) Z) (ζ : Dist Z) :
    Channel.restrictToSupport (extendFace r Q ζ) r = Q := by
  funext a
  rw [Channel.restrictToSupport_apply]
  show extendFace r Q ζ a.1 = Q a
  unfold extendFace
  rw [dif_pos a.2]; congr

theorem exists_domination_of_fullSupport
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : A, ε * r a ≤ q a := by
  classical
  have hpos : ∀ a : A, 0 < q a := hq
  obtain ⟨a0, -, ha0min⟩ := Finset.exists_min_image Finset.univ (fun a => q a) ⟨Classical.arbitrary A, Finset.mem_univ _⟩
  refine ⟨q a0, hpos a0, ?_⟩
  intro a
  have hqa0_le : q a0 ≤ q a := ha0min a (Finset.mem_univ a)
  have hra_le_one : r a ≤ 1 := by
    have := r.sum_eq_one
    have hle : r a ≤ ∑ b : A, r b := Finset.single_le_sum (fun b _ => r.nonneg b) (Finset.mem_univ a)
    rw [this] at hle; exact hle
  calc q a0 * r a ≤ q a0 * 1 := by
        apply mul_le_mul_of_nonneg_left hra_le_one (le_of_lt (hpos a0))
    _ = q a0 := by ring
    _ ≤ q a := hqa0_le

theorem posteriorLawDifference_extendFace_pushforward
    {A Z : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Z] [DecidableEq Z]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (Pf Rf : Channel (supportSubtype r) Z) (ζ : Dist Z)
    (φ : Dist A → ℝ) :
    posteriorLawDifferenceExp r.restrictToSupport
        (experimentOfChannel Pf) (experimentOfChannel Rf)
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) =
      posteriorLawDifferenceExp r
        (experimentOfChannel (extendFace r Pf ζ)) (experimentOfChannel (extendFace r Rf ζ)) φ := by
  unfold posteriorLawDifferenceExp
  rw [posteriorLawIntegralExp_experimentOfChannel, posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel, posteriorLawIntegralExp_experimentOfChannel]
  have hP := posteriorLawIntegral_restrictToSupport (extendFace r Pf ζ) r φ
  have hR := posteriorLawIntegral_restrictToSupport (extendFace r Rf ζ) r φ
  rw [restrictToSupport_extendFace r Pf ζ] at hP
  rw [restrictToSupport_extendFace r Rf ζ] at hR
  rw [hP, hR]

-- Boundary feasible-difference variants (block comparison given directly).
theorem branch_feasible_difference_pos_of_branch_block_strict
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (hpos : BranchPositive P₁ q target)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o))
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (htarget_weak :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target)) (inrDist (branchPosterior P₁ q target)))
    (htarget_strict :
      F.strictRel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target)) (inrDist (branchPosterior P₁ q target))) :
    0 < hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R))) := by
  have hagg_strict :
      F.strictRel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R)) (inlDist q) (inrDist q) :=
    A7_strict_one_branch_of_strict F hax O₂ q P₁ Q R target hpos hsame htarget_weak htarget_strict
  have hagg_gt :
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) <
        hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) := by
    have hpref : ExperimentPairPref F
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R)) q q := by
      change F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R)) (inlDist q) (inrDist q)
      exact hagg_strict.1
    have hge := (hV.represents_block_comparisons q hq _ _).mp hpref
    by_contra hnot_gt
    have hge_rev := le_of_not_gt hnot_gt
    have hpref_rev : ExperimentPairPref F
        (experimentOfChannel (seqComposeDep P₁ O₂ R))
        (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q :=
      (hV.represents_block_comparisons q hq _ _).mpr hge_rev
    have hrel_rev : F.rel (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q)) (inlDist q) (inrDist q) :=
      hpref_rev
    have hrel_rev_same : F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R)) (inrDist q) (inlDist q) :=
      (Relabeling.block_swap_rel_of_axioms F hax (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R) q q).mpr hrel_rev
    exact hagg_strict.2 hrel_rev_same
  exact (linearPart_difference_pos_iff_value_gt hlin F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q)) (experimentOfChannel (seqComposeDep P₁ O₂ R))).mpr hagg_gt

theorem branch_feasible_difference_zero_of_branch_block_weak
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O₁] [DecidableEq O₁]
    (q : Dist A) (hq : q.FullSupport)
    (P₁ : Channel A O₁) (target : O₁)
    (O₂ : O₁ → Type u)
    [∀ o, Fintype (O₂ o)] [∀ o, DecidableEq (O₂ o)]
    (Q R : ∀ o, Channel A (O₂ o))
    (hsame : ∀ o, o ≠ target → Q o = R o)
    (htarget_QR :
      F.rel (blockChannel (Q target) (R target))
        (inlDist (branchPosterior P₁ q target)) (inrDist (branchPosterior P₁ q target)))
    (htarget_RQ :
      F.rel (blockChannel (R target) (Q target))
        (inlDist (branchPosterior P₁ q target)) (inrDist (branchPosterior P₁ q target))) :
    hlin.linearPart F hV q
      (posteriorLawDifferenceExp q
        (experimentOfChannel (seqComposeDep P₁ O₂ Q))
        (experimentOfChannel (seqComposeDep P₁ O₂ R))) = 0 := by
  have hagg_QR : F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R)) (inlDist q) (inrDist q) :=
    A7_weak_one_branch_of_rel F hax O₂ q P₁ Q R target hsame htarget_QR
  have hagg_RQ : F.rel (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q)) (inlDist q) (inrDist q) :=
    A7_weak_one_branch_of_rel F hax O₂ q P₁ R Q target (fun o ho => (hsame o ho).symm) htarget_RQ
  have hpref_QR : ExperimentPairPref F
      (experimentOfChannel (seqComposeDep P₁ O₂ Q))
      (experimentOfChannel (seqComposeDep P₁ O₂ R)) q q := by
    change F.rel (blockChannel (seqComposeDep P₁ O₂ Q) (seqComposeDep P₁ O₂ R)) (inlDist q) (inrDist q)
    exact hagg_QR
  have hpref_RQ : ExperimentPairPref F
      (experimentOfChannel (seqComposeDep P₁ O₂ R))
      (experimentOfChannel (seqComposeDep P₁ O₂ Q)) q q := by
    change F.rel (blockChannel (seqComposeDep P₁ O₂ R) (seqComposeDep P₁ O₂ Q)) (inlDist q) (inrDist q)
    exact hagg_RQ
  have hge_QR := (hV.represents_block_comparisons q hq _ _).mp hpref_QR
  have hge_RQ := (hV.represents_block_comparisons q hq _ _).mp hpref_RQ
  have hagg_eq : hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ Q)) =
      hV.V q (experimentOfChannel (seqComposeDep P₁ O₂ R)) := le_antisymm hge_RQ hge_QR
  exact (linearPart_difference_zero_iff_value_eq hlin F hV q
    (experimentOfChannel (seqComposeDep P₁ O₂ Q)) (experimentOfChannel (seqComposeDep P₁ O₂ R))).mpr hagg_eq

-- THE boundary forward-zero.
theorem boundary_branch_tangent_forward_zero_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    [Nonempty (supportSubtype r)]
    (σ : PosteriorLawSigned (supportSubtype r))
    (hσatomic : PosteriorLawSigned.AtomicLinear σ)
    (hσtan : PosteriorLawTangent σ)
    (hσne : σ ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r))) :
    (0 < hlin.linearPart F hV r.restrictToSupport σ →
      0 < hlin.linearPart F hV q (pushSignedIncl r σ)) ∧
    (hlin.linearPart F hV r.restrictToSupport σ = 0 →
      hlin.linearPart F hV q (pushSignedIncl r σ) = 0) := by
  classical
  set rs : Dist (supportSubtype r) := r.restrictToSupport with hrs
  have hrs_fs : rs.FullSupport := Dist.restrictToSupport_fullSupport r
  obtain ⟨t, ht, Z, hZ, hZdec, hreal⟩ :=
    commonOutcomeAtomicLinearTangentRealization_of_atomicLinearSpanning
      (atomicLinearTangentSpanning_of_atomic finiteAtomicPosteriorTangentSpanning)
      rs hrs_fs σ hσatomic hσtan hσne
  letI : Fintype Z := hZ
  letI : DecidableEq Z := hZdec
  obtain ⟨Pf, Rf, hσeval⟩ := hreal
  haveI hNZ : Nonempty Z := Relabeling.nonempty_of_dist (Pf (Classical.arbitrary (supportSubtype r)))
  let ζ : Dist Z := Pf (Classical.arbitrary (supportSubtype r))
  let Pe : Channel A Z := extendFace r Pf ζ
  let Re : Channel A Z := extendFace r Rf ζ
  let ambientDiff : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r (experimentOfChannel Pe) (experimentOfChannel Re)
  -- pushSignedIncl r σ = SMul t ambientDiff.
  have hpush_eq : pushSignedIncl r σ = posteriorLawSignedSMul t ambientDiff := by
    funext φ
    show σ (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) = _
    rw [hσeval (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r)))]
    show t * posteriorLawDifferenceExp rs (experimentOfChannel Pf) (experimentOfChannel Rf)
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel r))) = _
    rw [posteriorLawDifference_extendFace_pushforward r Pf Rf ζ φ]
    rfl
  have hL1 :
      hlin.linearPart F hV q (pushSignedIncl r σ) =
        t * hlin.linearPart F hV q ambientDiff := by
    rw [hpush_eq, hlin.linearPart_smul]
  -- L2 σ = t * linearPart rs (facediff Pf Rf).
  have hσeq : σ = posteriorLawSignedSMul t
      (posteriorLawDifferenceExp rs (experimentOfChannel Pf) (experimentOfChannel Rf)) := by
    funext φ; rw [hσeval φ]; rfl
  have hL2 :
      hlin.linearPart F hV rs σ =
        t * hlin.linearPart F hV rs
          (posteriorLawDifferenceExp rs (experimentOfChannel Pf) (experimentOfChannel Rf)) := by
    rw [hσeq, hlin.linearPart_smul]
  -- Reach r as a branch of full-support q.
  obtain ⟨ε, hε_pos, hdom⟩ := exists_domination_of_fullSupport q r hq
  let P₁ : Channel A (ULift.{u} Bool) := binaryReachChannel q r ε (le_of_lt hε_pos) hdom
  have hbrpos : BranchPositive P₁ q (ULift.up true) := by
    show (Channel.outcomeMarginal P₁ q) (ULift.up true) > 0
    rw [outcomeMarginal_binaryReachChannel_true q r ε (le_of_lt hε_pos) hdom]; exact hε_pos
  have hbrpost : branchPosterior P₁ q (ULift.up true) = r :=
    branchPosterior_binaryReachChannel_true q r ε hε_pos hdom
  let O₂ : ULift.{u} Bool → Type u := fun _ => Z
  let QQ : ∀ o, Channel A (O₂ o) := fun o => if o = ULift.up true then Pe else Pe
  let RR : ∀ o, Channel A (O₂ o) := fun o => if o = ULift.up true then Re else Pe
  have hsame : ∀ o, o ≠ ULift.up true → QQ o = RR o := by
    intro o ho; simp [QQ, RR, ho]
  have hQtarget : QQ (ULift.up true) = Pe := by simp [QQ]
  have hRtarget : RR (ULift.up true) = Re := by simp [RR]
  set m : ℝ := (Channel.outcomeMarginal P₁ q) (ULift.up true) with hm
  have hm_pos : 0 < m := hbrpos
  -- seqDiff = SMul m ambientDiff (as functions), so linearPart q seqDiff = m * linearPart q ambientDiff.
  have hseq_eq :
      posteriorLawDifferenceExp q
          (experimentOfChannel (seqComposeDep P₁ O₂ QQ))
          (experimentOfChannel (seqComposeDep P₁ O₂ RR)) =
        posteriorLawSignedSMul m ambientDiff := by
    funext φ
    have h := posteriorLawDifference_seqComposeDep_one_branch q P₁ O₂ QQ RR (ULift.up true) hsame φ
    rw [h]
    show m * posteriorLawDifferenceExp (branchPosterior P₁ q (ULift.up true))
        (experimentOfChannel (QQ (ULift.up true))) (experimentOfChannel (RR (ULift.up true))) φ = _
    rw [hQtarget, hRtarget, hbrpost]
    rfl
  have hLseq :
      hlin.linearPart F hV q
        (posteriorLawDifferenceExp q
          (experimentOfChannel (seqComposeDep P₁ O₂ QQ))
          (experimentOfChannel (seqComposeDep P₁ O₂ RR))) =
        m * hlin.linearPart F hV q ambientDiff := by
    rw [hseq_eq, hlin.linearPart_smul]
  refine ⟨?_, ?_⟩
  · -- forward positivity
    intro hpos
    have hface_pos : 0 < hlin.linearPart F hV rs
        (posteriorLawDifferenceExp rs (experimentOfChannel Pf) (experimentOfChannel Rf)) := by
      rw [hL2] at hpos
      by_contra hle
      have : hlin.linearPart F hV rs
          (posteriorLawDifferenceExp rs (experimentOfChannel Pf) (experimentOfChannel Rf)) ≤ 0 :=
        le_of_not_gt hle
      nlinarith [hpos, ht]
    have hface_gap : hV.V rs (experimentOfChannel Rf) < hV.V rs (experimentOfChannel Pf) :=
      (linearPart_difference_pos_iff_value_gt hlin F hV rs
        (experimentOfChannel Pf) (experimentOfChannel Rf)).mp hface_pos
    have hstrict_face : F.strictRel (blockChannel Pf Rf) (inlDist rs) (inrDist rs) :=
      block_strictRel_of_channel_value_gt F hax hV rs hrs_fs Pf Rf hface_gap
    have hstrict_r : F.strictRel (blockChannel Pe Re) (inlDist r) (inrDist r) := by
      apply boundary_block_lift_strict F hax r Pe Re
      show F.strictRel (blockChannel (Channel.restrictToSupport Pe r) (Channel.restrictToSupport Re r))
        (inlDist rs) (inrDist rs)
      rw [show Channel.restrictToSupport Pe r = Pf from restrictToSupport_extendFace r Pf ζ,
        show Channel.restrictToSupport Re r = Rf from restrictToSupport_extendFace r Rf ζ]
      exact hstrict_face
    -- assemble strict/weak block at branchPosterior form.
    have htarget_strict : F.strictRel (blockChannel (QQ (ULift.up true)) (RR (ULift.up true)))
        (inlDist (branchPosterior P₁ q (ULift.up true))) (inrDist (branchPosterior P₁ q (ULift.up true))) := by
      rw [hQtarget, hRtarget, hbrpost]; exact hstrict_r
    have htarget_weak : F.rel (blockChannel (QQ (ULift.up true)) (RR (ULift.up true)))
        (inlDist (branchPosterior P₁ q (ULift.up true))) (inrDist (branchPosterior P₁ q (ULift.up true))) :=
      htarget_strict.1
    have hseq_pos := branch_feasible_difference_pos_of_branch_block_strict hlin F hax hV q hq
      P₁ (ULift.up true) hbrpos O₂ QQ RR hsame htarget_weak htarget_strict
    rw [hLseq] at hseq_pos
    have hamb_pos : 0 < hlin.linearPart F hV q ambientDiff := by
      by_contra hle
      have : hlin.linearPart F hV q ambientDiff ≤ 0 := le_of_not_gt hle
      nlinarith [hseq_pos, hm_pos]
    rw [hL1]; exact mul_pos ht hamb_pos
  · -- zero case
    intro hzero
    have hface_zero : hlin.linearPart F hV rs
        (posteriorLawDifferenceExp rs (experimentOfChannel Pf) (experimentOfChannel Rf)) = 0 := by
      rw [hL2] at hzero
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (ne_of_gt ht)
      · exact h
    have hface_eq : hV.V rs (experimentOfChannel Pf) = hV.V rs (experimentOfChannel Rf) :=
      (linearPart_difference_zero_iff_value_eq hlin F hV rs
        (experimentOfChannel Pf) (experimentOfChannel Rf)).mp hface_zero
    have hweak_PR_face : F.rel (blockChannel Pf Rf) (inlDist rs) (inrDist rs) :=
      block_rel_of_channel_value_ge F hV rs hrs_fs Pf Rf (by rw [hface_eq])
    have hweak_RP_face : F.rel (blockChannel Rf Pf) (inlDist rs) (inrDist rs) :=
      block_rel_of_channel_value_ge F hV rs hrs_fs Rf Pf (by rw [hface_eq])
    have hweak_PR_r : F.rel (blockChannel Pe Re) (inlDist r) (inrDist r) := by
      apply boundary_block_lift F hax r Pe Re
      rw [show Channel.restrictToSupport Pe r = Pf from restrictToSupport_extendFace r Pf ζ,
        show Channel.restrictToSupport Re r = Rf from restrictToSupport_extendFace r Rf ζ]
      exact hweak_PR_face
    have hweak_RP_r : F.rel (blockChannel Re Pe) (inlDist r) (inrDist r) := by
      apply boundary_block_lift F hax r Re Pe
      rw [show Channel.restrictToSupport Re r = Rf from restrictToSupport_extendFace r Rf ζ,
        show Channel.restrictToSupport Pe r = Pf from restrictToSupport_extendFace r Pf ζ]
      exact hweak_RP_face
    have htarget_QR : F.rel (blockChannel (QQ (ULift.up true)) (RR (ULift.up true)))
        (inlDist (branchPosterior P₁ q (ULift.up true))) (inrDist (branchPosterior P₁ q (ULift.up true))) := by
      rw [hQtarget, hRtarget, hbrpost]; exact hweak_PR_r
    have htarget_RQ : F.rel (blockChannel (RR (ULift.up true)) (QQ (ULift.up true)))
        (inlDist (branchPosterior P₁ q (ULift.up true))) (inrDist (branchPosterior P₁ q (ULift.up true))) := by
      rw [hQtarget, hRtarget, hbrpost]; exact hweak_RP_r
    have hseq_zero := branch_feasible_difference_zero_of_branch_block_weak hlin F hax hV q hq
      P₁ (ULift.up true) O₂ QQ RR hsame htarget_QR htarget_RQ
    rw [hLseq] at hseq_zero
    have hamb_zero : hlin.linearPart F hV q ambientDiff = 0 := by
      rcases mul_eq_zero.mp hseq_zero with h | h
      · exact absurd h (ne_of_gt hm_pos)
      · exact h
    rw [hL1, hamb_zero, mul_zero]





-- pushSignedIncl algebra.
theorem pushSignedIncl_add {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (σ τ : PosteriorLawSigned (supportSubtype r)) :
    pushSignedIncl r (posteriorLawSignedAdd σ τ) =
      posteriorLawSignedAdd (pushSignedIncl r σ) (pushSignedIncl r τ) := by
  funext φ; rfl

theorem pushSignedIncl_smul {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    (c : ℝ) (σ : PosteriorLawSigned (supportSubtype r)) :
    pushSignedIncl r (posteriorLawSignedSMul c σ) =
      posteriorLawSignedSMul c (pushSignedIncl r σ) := by
  funext φ; rfl

-- β-scalar for boundary r: for atomic-linear tangents σ on supportSubtype r,
--   linearPart q (pushSignedIncl r σ) = β * linearPart r.restrictToSupport σ.
theorem boundary_atomicLinear_tangent_scalar_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    [Nonempty (supportSubtype r)]
    (hr_nondegenerate : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b) :
    ∃ β : ℝ, 0 < β ∧
      ∀ (σ : PosteriorLawSigned (supportSubtype r)),
        PosteriorLawSigned.AtomicLinear σ → PosteriorLawTangent σ →
        hlin.linearPart F hV q (pushSignedIncl r σ) =
          β * hlin.linearPart F hV r.restrictToSupport σ := by
  classical
  set rs : Dist (supportSubtype r) := r.restrictToSupport with hrs
  have hrs_fs : rs.FullSupport := Dist.restrictToSupport_fullSupport r
  -- L1, L2 as functionals.
  let L1 : PosteriorLawSigned (supportSubtype r) → ℝ :=
    fun σ => hlin.linearPart F hV q (pushSignedIncl r σ)
  let L2 : PosteriorLawSigned (supportSubtype r) → ℝ :=
    fun σ => hlin.linearPart F hV rs σ
  have hL1add : ∀ σ τ, L1 (posteriorLawSignedAdd σ τ) = L1 σ + L1 τ := by
    intro σ τ; show hlin.linearPart F hV q (pushSignedIncl r (posteriorLawSignedAdd σ τ)) = _
    rw [pushSignedIncl_add, hlin.linearPart_add]
  have hL1smul : ∀ c σ, L1 (posteriorLawSignedSMul c σ) = c * L1 σ := by
    intro c σ; show hlin.linearPart F hV q (pushSignedIncl r (posteriorLawSignedSMul c σ)) = _
    rw [pushSignedIncl_smul, hlin.linearPart_smul]
  have hL2add : ∀ σ τ, L2 (posteriorLawSignedAdd σ τ) = L2 σ + L2 τ := by
    intro σ τ; exact hlin.linearPart_add F hV rs σ τ
  have hL2smul : ∀ c σ, L2 (posteriorLawSignedSMul c σ) = c * L2 σ := by
    intro c σ; exact hlin.linearPart_smul F hV rs c σ
  -- forward-zero for atomic-linear tangents.
  have hforward :
      ∀ (σ : PosteriorLawSigned (supportSubtype r)),
        PosteriorLawSigned.AtomicLinear σ → PosteriorLawTangent σ →
        σ ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) →
        (0 < L2 σ → 0 < L1 σ) ∧ (L2 σ = 0 → L1 σ = 0) :=
    fun σ hatom htan hne =>
      boundary_branch_tangent_forward_zero_of_A1 hlin F hax hV q r hq σ hatom htan hne
  -- sign agreement (both directions via negation).
  have hsign :
      ∀ (σ : PosteriorLawSigned (supportSubtype r)),
        PosteriorLawSigned.AtomicLinear σ → PosteriorLawTangent σ →
        σ ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) →
        (0 < L1 σ ↔ 0 < L2 σ) ∧ (L1 σ = 0 ↔ L2 σ = 0) := by
    intro σ hatom htan hne
    have hfwd := hforward σ hatom htan hne
    let negσ := posteriorLawSignedSMul (-1) σ
    have hneg_atom := PosteriorLawSigned.AtomicLinear.smul (-1) hatom
    have hneg_tan := PosteriorLawTangent_smul (-1) htan
    have hneg_ne := posteriorLawSignedSMul_neg_ne_zero hne
    have hfwd_neg := hforward negσ hneg_atom hneg_tan hneg_ne
    have hq_neg : L1 negσ = -L1 σ := by rw [show L1 negσ = L1 (posteriorLawSignedSMul (-1) σ) from rfl, hL1smul]; ring
    have hr_neg : L2 negσ = -L2 σ := by rw [show L2 negσ = L2 (posteriorLawSignedSMul (-1) σ) from rfl, hL2smul]; ring
    constructor
    · constructor
      · intro hqpos
        by_contra hrnot
        have hrle := le_of_not_gt hrnot
        by_cases hrzero : L2 σ = 0
        · linarith [hfwd.2 hrzero]
        · have hrlt : L2 σ < 0 := lt_of_le_of_ne hrle hrzero
          have hrnegpos : 0 < L2 negσ := by rw [hr_neg]; linarith
          linarith [hfwd_neg.1 hrnegpos, hq_neg]
      · intro hrpos; exact hfwd.1 hrpos
    · constructor
      · intro hqzero
        by_contra hrne
        rcases lt_or_gt_of_ne hrne with hrlt | hrpos
        · have hrnegpos : 0 < L2 negσ := by rw [hr_neg]; linarith
          linarith [hfwd_neg.1 hrnegpos, hq_neg]
        · linarith [hfwd.1 hrpos]
      · exact hfwd.2
  -- nonzero atomic-linear tangent witness on the full-support face rs.
  rcases branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV rs rs hrs_fs hrs_fs hr_nondegenerate with
    ⟨x0, hx0_atom, hx0_tan, hx0_nz⟩
  have hx0_ne : x0 ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) := by
    intro hx0_eq; exact hx0_nz (by rw [hx0_eq]; exact linearPart_zero hlin F hV rs)
  let x : PosteriorLawSigned (supportSubtype r) :=
    if 0 < L2 x0 then x0 else posteriorLawSignedSMul (-1) x0
  have hx_atom : PosteriorLawSigned.AtomicLinear x := by
    dsimp only [x]; split_ifs
    · exact hx0_atom
    · exact PosteriorLawSigned.AtomicLinear.smul (-1) hx0_atom
  have hx_tan : PosteriorLawTangent x := by
    dsimp only [x]; split_ifs
    · exact hx0_tan
    · exact PosteriorLawTangent_smul (-1) hx0_tan
  have hx_ne : x ≠ ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) := by
    dsimp only [x]; split_ifs
    · exact hx0_ne
    · exact posteriorLawSignedSMul_neg_ne_zero hx0_ne
  have hx_L2_pos : 0 < L2 x := by
    dsimp only [x]; split_ifs with hpos
    · exact hpos
    · have hle : L2 x0 ≤ 0 := le_of_not_gt hpos
      have hlt : L2 x0 < 0 := lt_of_le_of_ne hle hx0_nz
      show 0 < L2 (posteriorLawSignedSMul (-1) x0)
      rw [hL2smul]; linarith
  have hx_L2_ne : L2 x ≠ 0 := ne_of_gt hx_L2_pos
  have hx_L1_pos : 0 < L1 x := (hsign x hx_atom hx_tan hx_ne).1.mpr hx_L2_pos
  let β : ℝ := L1 x / L2 x
  have hβ_pos : 0 < β := div_pos hx_L1_pos hx_L2_pos
  refine ⟨β, hβ_pos, ?_⟩
  intro y hy_atom hy_tan
  by_cases hy_ne : y = ((fun _ => 0) : PosteriorLawSigned (supportSubtype r))
  · show L1 y = β * L2 y
    rw [hy_ne]
    show hlin.linearPart F hV q (pushSignedIncl r ((fun _ => 0))) = β * hlin.linearPart F hV rs (fun _ => 0)
    rw [show pushSignedIncl r ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) =
        ((fun _ => 0) : PosteriorLawSigned A) from by funext φ; rfl]
    rw [linearPart_zero hlin F hV q, linearPart_zero hlin F hV rs]; ring
  · let c : ℝ := -(L2 y / L2 x)
    let z : PosteriorLawSigned (supportSubtype r) :=
      posteriorLawSignedAdd y (posteriorLawSignedSMul c x)
    have hz_atom : PosteriorLawSigned.AtomicLinear z :=
      PosteriorLawSigned.AtomicLinear.add hy_atom (PosteriorLawSigned.AtomicLinear.smul c hx_atom)
    have hz_tan : PosteriorLawTangent z :=
      PosteriorLawTangent_add hy_tan (PosteriorLawTangent_smul c hx_tan)
    have hz_L2 : L2 z = 0 := by
      show L2 (posteriorLawSignedAdd y (posteriorLawSignedSMul c x)) = 0
      rw [hL2add, hL2smul]
      show L2 y + c * L2 x = 0
      have : c = -(L2 y / L2 x) := rfl
      have hdiv := div_mul_cancel₀ (L2 y) hx_L2_ne
      rw [this]; field_simp; ring
    have hz_L1 : L1 z = 0 := by
      by_cases hz_ne : z = ((fun _ => 0) : PosteriorLawSigned (supportSubtype r))
      · show L1 z = 0
        rw [hz_ne]
        show hlin.linearPart F hV q (pushSignedIncl r ((fun _ => 0))) = 0
        rw [show pushSignedIncl r ((fun _ => 0) : PosteriorLawSigned (supportSubtype r)) =
            ((fun _ => 0) : PosteriorLawSigned A) from by funext φ; rfl]
        exact linearPart_zero hlin F hV q
      · exact (hsign z hz_atom hz_tan hz_ne).2.mpr hz_L2
    have hz_L1_expand : L1 z = L1 y + c * L1 x := by
      show L1 (posteriorLawSignedAdd y (posteriorLawSignedSMul c x)) = _
      rw [hL1add, hL1smul]
    show L1 y = β * L2 y
    have hLqy : L1 y = -c * L1 x := by linarith [hz_L1, hz_L1_expand]
    have hc_expand : c = -(L2 y / L2 x) := rfl
    have hβ_eq : β = L1 x / L2 x := rfl
    rw [hLqy, hc_expand, hβ_eq]; field_simp

/-- Face nondegeneracy from ambient nondegeneracy. -/
theorem faceNondeg_of_ambientNondeg {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
  obtain ⟨a, b, hab, ha, hb⟩ := hrnd
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by intro hh; exact hab (congrArg Subtype.val hh),
    by rw [Dist.restrictToSupport_apply]; exact ha,
    by rw [Dist.restrictToSupport_apply]; exact hb⟩

/-- Support nonemptiness from ambient nondegeneracy. -/
theorem nonempty_support_of_nondeg {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    Nonempty (supportSubtype r) := by
  obtain ⟨a, _, _, ha, _⟩ := hrnd; exact ⟨⟨a, ha⟩⟩

/-- **Boundary coefficient scale from the FinalHM interface at a fixed `(F, hax)`.**

The positive boundary coefficient `β(q,r)` is `Classical.choose` of the boundary
tangent scalar `boundary_atomicLinear_tangent_scalar_of_A1` at the canonical HM
value representative `posteriorValueRepresentation_of_FinalHMInterface hhm hax`.
Off the boundary-nondegenerate domain it falls back to `1`.  This is a genuine
convention *value* (not a new assumption): it is the ratio of ambient to
support-face linear parts, which the strict boundary block lift makes positive. -/
noncomputable def boundaryCoeffForHM
    (hhm : FinalHMInterface.{u}) {F : PrefFamily.{u}} (hax : TraceAxioms F) :
    FiniteBoundaryCoefficientScaleConventionAssumptions.{u} where
  boundaryCoeff := fun {A} _ _ _ q r => by
    classical
    exact
      if h : q.FullSupport ∧ (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) ∧ ¬ r.FullSupport then
        haveI : Nonempty (supportSubtype r) := nonempty_support_of_nondeg r h.2.1
        Classical.choose (boundary_atomicLinear_tangent_scalar_of_A1
          (affineLinearPart_of_FinalHMInterface hhm) F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax) q r h.1
          (faceNondeg_of_ambientNondeg r h.2.1))
      else 1
  boundaryCoeff_pos := by
    intro A _ _ _ q r hq hrn hrnd hrb
    classical
    have hcond : q.FullSupport ∧ (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) ∧ ¬ r.FullSupport :=
      ⟨hq, hrnd, hrb⟩
    show (if h : q.FullSupport ∧ (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) ∧ ¬ r.FullSupport then
        haveI : Nonempty (supportSubtype r) := nonempty_support_of_nondeg r h.2.1
        Classical.choose (boundary_atomicLinear_tangent_scalar_of_A1
          (affineLinearPart_of_FinalHMInterface hhm) F hax
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax) q r h.1
          (faceNondeg_of_ambientNondeg r h.2.1))
      else 1) > 0
    rw [dif_pos hcond]
    haveI : Nonempty (supportSubtype r) := nonempty_support_of_nondeg r hcond.2.1
    exact (Classical.choose_spec (boundary_atomicLinear_tangent_scalar_of_A1
      (affineLinearPart_of_FinalHMInterface hhm) F hax
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax) q r hcond.1
      (faceNondeg_of_ambientNondeg r hcond.2.1))).1

/-- **Boundary marginal-value transport at the canonical HM representative.**

For the canonical value representative of `(F, hax)`, the ambient marginal test
function restricted along the support-face inclusion agrees, up to the chosen
positive boundary coefficient `boundaryCoeffForHM`, with the intrinsic
support-face marginal test function, on every atomic-linear tangent `σ`.  This is
exactly the `support_face_marginalValue_scalar` field body specialised to
`hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax`.  It is proved
(not assumed) from `boundary_atomicLinear_tangent_scalar_of_A1`. -/
theorem marginalValueTransport_canonical
    (hhm : FinalHMInterface.{u}) {F : PrefFamily.{u}} (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport)
    (σ : PosteriorLawSigned (supportSubtype r))
    (hσtan : PosteriorLawTangent σ)
    (hσatom : PosteriorLawSigned.AtomicLinear σ) :
    σ (fun d => (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax) q
          (Channel.actionPushforward d (supportIncludeKernel r))) =
      (boundaryCoeffForHM hhm hax).boundaryCoeff q r *
        σ ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax) r.restrictToSupport) := by
  classical
  set hlin := affineLinearPart_of_FinalHMInterface hhm with hlin_def
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hV_def
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hint_def
  have hcond : q.FullSupport ∧ (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) ∧ ¬ r.FullSupport :=
    ⟨hq, hrnd, hrb⟩
  have hbc : (boundaryCoeffForHM hhm hax).boundaryCoeff q r =
      Classical.choose (boundary_atomicLinear_tangent_scalar_of_A1 hlin F hax hV q r hq
        (faceNondeg_of_ambientNondeg r hrnd)) := by
    show (if h : q.FullSupport ∧ (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) ∧ ¬ r.FullSupport then
        haveI : Nonempty (supportSubtype r) := nonempty_support_of_nondeg r h.2.1
        Classical.choose (boundary_atomicLinear_tangent_scalar_of_A1 hlin F hax hV q r h.1
          (faceNondeg_of_ambientNondeg r h.2.1))
      else 1) = _
    rw [dif_pos hcond]
  have hβspec := Classical.choose_spec
    (boundary_atomicLinear_tangent_scalar_of_A1 hlin F hax hV q r hq
      (faceNondeg_of_ambientNondeg r hrnd))
  have hkey := hβspec.2 σ hσatom hσtan
  rw [hbc]
  have hL1 : hlin.linearPart F hV q (pushSignedIncl r σ) =
      σ (fun d => hint.marginalValue F hV q
        (Channel.actionPushforward d (supportIncludeKernel r))) := rfl
  have hL2 : hlin.linearPart F hV r.restrictToSupport σ =
      σ (hint.marginalValue F hV r.restrictToSupport) := rfl
  rw [← hL1, ← hL2]
  exact hkey



/-- **`support_face` PROVED from the HM integral representation.**

The support-face representative convention `V r E = V (r|supp) (E|supp)` follows
from the integral form `V q E = ∫ marginalValue q  d(posterior law)`
(`value_eq_integral`), relabel/support-covariance of the posterior-law integral
(`posteriorLawIntegral_restrictToSupport`), and the marginal-value support-face
naturality clause (`marginalValue_support_face`).  It is not a convention. -/
theorem supportFaceRepresentativeConvention_of_integralRepresentation
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u}) :
    FiniteSupportFaceRepresentativeConventionAssumptions.{u} where
  support_face_value_transport := by
    intro F hax hV A O _ _ _ _ _ r _ P
    rw [hint.value_eq_integral F hV r (experimentOfChannel P),
        hint.value_eq_integral F hV r.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P r))]
    rw [posteriorLawIntegralExp_experimentOfChannel, posteriorLawIntegralExp_experimentOfChannel]
    rw [posteriorLawIntegral_restrictToSupport P r (hint.marginalValue F hV r)]
    refine congrArg _ ?_
    funext d
    exact hint.marginalValue_support_face F hV r d

/-- **`singleton_scale` CONSTRUCTED: `singletonCoeff := 1` (WLOG) and the
singleton branch value is PROVED zero.**

`singletonCoeff` multiplies a zero value, so any positive choice works; we take
`1`.  `singleton_branch_value_zero` (`V r E = 0` when `r` has singleton support)
is proved by transporting to the support face
(`supportFaceRepresentativeConvention_of_integralRepresentation`), where the
support subtype is a subsingleton and the value is zero
(`branchValue_channel_eq_zero_of_subsingleton`). -/
noncomputable def branchSingletonScaleConvention_of_integralRepresentation
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u}) :
    FiniteBranchSingletonScaleConventionAssumptions.{u} where
  singletonCoeff := fun _ _ => 1
  singletonCoeff_pos := fun _ _ _ _ => one_pos
  singleton_branch_value_zero := by
    intro F hV A O _ _ _ _ _ r hr_single P
    obtain ⟨a, ha, huniq⟩ := hr_single
    haveI hsub : Subsingleton (supportSubtype r) := by
      constructor
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      exact Subtype.ext ((huniq x hx).trans (huniq y hy).symm)
    haveI : Nonempty (supportSubtype r) := ⟨⟨a, ha⟩⟩
    have htrans :
        hV.V r (experimentOfChannel P) =
          hV.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport P r)) := by
      rw [hint.value_eq_integral F hV r (experimentOfChannel P),
          hint.value_eq_integral F hV r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport P r))]
      rw [posteriorLawIntegralExp_experimentOfChannel, posteriorLawIntegralExp_experimentOfChannel]
      rw [posteriorLawIntegral_restrictToSupport P r (hint.marginalValue F hV r)]
      refine congrArg _ ?_; funext d
      exact hint.marginalValue_support_face F hV r d
    rw [htrans]
    exact branchValue_channel_eq_zero_of_subsingleton F hV r.restrictToSupport
      (Dist.restrictToSupport_fullSupport r) (Channel.restrictToSupport P r)

/-- **Minimal branch residual: the boundary-transport core (4 fields).**

`FinalFaithfulBranchConventions` has six fields; two of them (`support_face`,
`singleton_scale`) are theorems of the HM integral representation
(`supportFaceRepresentativeConvention_of_integralRepresentation`,
`branchSingletonScaleConvention_of_integralRepresentation`) and are dropped here.
The four remaining fields are exactly the coupled boundary-transport data:

* `boundary_coeff` — the positive boundary-coefficient choice
  (`FiniteBoundaryCoefficientScaleConventionAssumptions`), a representative choice;
* `marginal_value` — the marginal-value transport equation
  `η(φ_q ∘ incl) = boundaryCoeff · η(φ_{r|supp})` (the boundary linear-part
  transport; genuine mathematical content of the true HM functional, not a
  convention — see `FiniteBoundaryLinearPartTransportAssumptions`);
* `boundary_scale`, `singleton_scale_factorization` — the boundary/singleton
  scale-factorization equations `branchCoeff = scale q / scale(post)` coupling the
  chosen coefficients to the derived cocycle scale.

This is strictly smaller than `FinalFaithfulBranchConventions` (4 fields vs 6). -/
structure MinimalBranchResidual (hhm : FinalHMInterface.{u}) where
  boundary_coeff : FiniteBoundaryCoefficientScaleConventionAssumptions.{u}
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
      let hboundary := boundaryFaceScale_of_coefficientScaleConvention boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeConvention
          (supportFaceRepresentativeConvention_of_integralRepresentation
            (posteriorIntegralRepresentation_of_FinalHMInterface hhm))
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalConvention
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary
          (branchSingletonScaleConvention_of_integralRepresentation
            (posteriorIntegralRepresentation_of_FinalHMInterface hhm))
          hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary
          (branchSingletonScaleConvention_of_integralRepresentation
            (posteriorIntegralRepresentation_of_FinalHMInterface hhm))
          hvalue hcoeff)
  singleton_scale_factorization :
    ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
      (hV : PosteriorValueRepresentation F),
      let hlin := affineLinearPart_of_FinalHMInterface hhm
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
          (atomicLinearTangentSpanning_of_atomic
            finiteAtomicPosteriorTangentSpanning) F hax hV
      let hboundary := boundaryFaceScale_of_coefficientScaleConvention boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeConvention
          (supportFaceRepresentativeConvention_of_integralRepresentation
            (posteriorIntegralRepresentation_of_FinalHMInterface hhm))
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalConvention
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationSingletonConvention
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary
          (branchSingletonScaleConvention_of_integralRepresentation
            (posteriorIntegralRepresentation_of_FinalHMInterface hhm))
          hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary
          (branchSingletonScaleConvention_of_integralRepresentation
            (posteriorIntegralRepresentation_of_FinalHMInterface hhm))
          hvalue hcoeff)

/-- Rebuild the full six-field `FinalFaithfulBranchConventions` from the
four-field `MinimalBranchResidual`, supplying the two proved fields. -/
noncomputable def finalFaithfulBranchConventions_of_minimal
    {hhm : FinalHMInterface.{u}} (h : MinimalBranchResidual hhm) :
    FinalFaithfulBranchConventions hhm where
  support_face :=
    supportFaceRepresentativeConvention_of_integralRepresentation
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
  boundary_coeff := h.boundary_coeff
  singleton_scale :=
    branchSingletonScaleConvention_of_integralRepresentation
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
  marginal_value := h.marginal_value
  boundary_scale := h.boundary_scale
  singleton_scale_factorization := h.singleton_scale_factorization

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
  have hTq := htrans F hax hV q r hq hrn hrnd hrb η hηtan hηatomic
  have hTq' := htrans F hax hV q' r hq' hrn hrnd hrb η hηtan hηatomic
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

/-- **Nesting of canonical boundary priors.**  The canonical `ℓ`-point face
inside the `n`-point set is the pushforward of the canonical `ℓ`-point face
inside the `m`-point set along the `m ↪ n` inclusion (`ℓ ≤ m ≤ n`).  This is the
geometric identity underlying the embedding-defect cocycle. -/
theorem canonBoundary_nest (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] :
    canonBoundary.{u} n l (hml.trans hmn) =
      Channel.actionPushforward (canonBoundary.{u} m l hml) (canonInclKernel n m hmn) := by
  ext j
  obtain ⟨jn⟩ := j
  rw [canonBoundary_apply]
  show (if (jn:ℕ) < l then (1:ℝ)/l else 0) =
    ∑ c : canonType.{u} m, (canonBoundary.{u} m l hml) c *
      (Dist.pure (ULift.up (Fin.castLE hmn c.down)) : Dist (canonType.{u} n)) (ULift.up jn)
  by_cases hjm : (jn:ℕ) < m
  · rw [Finset.sum_eq_single (ULift.up (⟨(jn:ℕ), hjm⟩ : Fin m))]
    · have hpt : (ULift.up.{u} (Fin.castLE hmn ((ULift.up.{u} (⟨(jn:ℕ),hjm⟩ : Fin m)).down))
            : canonType.{u} n) = (ULift.up.{u} jn : canonType.{u} n) := by
        apply ULift.ext; apply Fin.ext; simp
      rw [hpt, Dist.pure_apply_self, mul_one, canonBoundary_apply]
    · intro c _ hc
      rw [Dist.pure_apply_ne, mul_zero]
      intro hcontra
      apply hc
      apply ULift.ext; apply Fin.ext
      have hce : Fin.castLE hmn c.down = jn := ULift.up.inj hcontra.symm
      have := Fin.ext_iff.mp hce
      simpa using this
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [if_neg (fun h => hjm (lt_of_lt_of_le h hml))]
    refine (Finset.sum_eq_zero ?_).symm
    intro c _
    rw [Dist.pure_apply_ne, mul_zero]
    intro hcontra
    apply hjm
    have hce : Fin.castLE hmn c.down = jn := ULift.up.inj hcontra.symm
    rw [← hce, Fin.val_castLE]
    exact c.down.isLt

/-- Deterministic (pure-kernel) pushforward composition: pushing by `pure ∘ f`
then `pure ∘ g` equals pushing by `pure ∘ (g ∘ f)`. -/
theorem actionPushforward_pure_comp {A B C : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (d : Dist A) (f : A → B) (g : B → C) :
    Channel.actionPushforward (Channel.actionPushforward d (fun a => Dist.pure (f a)))
        (fun b => Dist.pure (g b)) =
      Channel.actionPushforward d (fun a => Dist.pure (g (f a))) := by
  ext c
  show (∑ b : B, (Channel.actionPushforward d (fun a => Dist.pure (f a))) b *
        (Dist.pure (g b) : Dist C) c) =
      ∑ a : A, d a * (Dist.pure (g (f a)) : Dist C) c
  have hinner : ∀ b : B, (Channel.actionPushforward d (fun a => Dist.pure (f a))) b =
      ∑ a : A, d a * (Dist.pure (f a) : Dist B) b := fun b => rfl
  simp only [hinner, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : c = g (f a)
  · subst hc
    rw [Finset.sum_eq_single (f a)]
    · rw [Dist.pure_apply_self, Dist.pure_apply_self, mul_one, mul_one]
    · intro b _ hb
      rw [Dist.pure_apply_ne (f a) b hb, mul_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · rw [Dist.pure_apply_ne (g (f a)) c hc, mul_zero]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : b = f a
    · subst hb; rw [Dist.pure_apply_ne (g (f a)) c hc, mul_zero]
    · rw [Dist.pure_apply_ne (f a) b hb, mul_zero, zero_mul]

/-- The canonical inclusion kernels compose: `(m ↪ n) ∘ (ℓ ↪ m) = (ℓ ↪ n)`. -/
theorem canonInclKernel_comp (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) (d : Dist (canonType.{u} l)) :
    Channel.actionPushforward
        (Channel.actionPushforward d (canonInclKernel m l hml)) (canonInclKernel n m hmn) =
      Channel.actionPushforward d (canonInclKernel n l (hml.trans hmn)) := by
  have h := actionPushforward_pure_comp (C := canonType.{u} n) d
    (fun b : canonType.{u} l => ULift.up (Fin.castLE hml b.down))
    (fun c : canonType.{u} m => ULift.up (Fin.castLE hmn c.down))
  show Channel.actionPushforward
      (Channel.actionPushforward d (fun b => Dist.pure (ULift.up (Fin.castLE hml b.down))))
      (fun c => Dist.pure (ULift.up (Fin.castLE hmn c.down))) = _
  rw [h]
  apply congrArg (Channel.actionPushforward d)
  funext a
  congr 2

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

/-- Inclusion of the `ℓ`-face support into the `m`-face support (same ambient
element), for `ℓ ≤ m ≤ n`. -/
noncomputable def nestSupportMap (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] [NeZero m] :
    supportSubtype (canonBoundary.{u} n l (hml.trans hmn)) →
    supportSubtype (canonBoundary.{u} n m hmn) :=
  fun a => ⟨a.1, by
    obtain ⟨⟨jn⟩, hj⟩ := a
    show 0 < (canonBoundary n m hmn) (ULift.up jn)
    rw [canonBoundary_pos]
    have hjl : ((jn : Fin n) : ℕ) < l := (canonBoundary_pos n l (hml.trans hmn) jn).mp hj
    exact lt_of_lt_of_le hjl hml⟩

/-- The support inclusion of the `ℓ`-face factors through the `m`-face: pushing a
belief into the ambient space via the `ℓ`-face inclusion equals first mapping to
the `m`-face support then including. -/
theorem supportInclude_nest (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] [NeZero m]
    (d : Dist (supportSubtype (canonBoundary.{u} n l (hml.trans hmn)))) :
    Channel.actionPushforward d (supportIncludeKernel (canonBoundary.{u} n l (hml.trans hmn))) =
      Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)))
        (supportIncludeKernel (canonBoundary.{u} n m hmn)) := by
  show Channel.actionPushforward d
        (fun a => Dist.pure (a.1 : canonType.{u} n)) =
      Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)))
        (fun b => Dist.pure (b.1 : canonType.{u} n))
  rw [actionPushforward_pure_comp d (nestSupportMap n m l hmn hml) (fun b => (b.1 : canonType.{u} n))]
  rfl

/-- **Transport equation for the embedding defect.**  For `2 ≤ m < n` and a
tangent `η` on the `m`-face support, the ambient marginal value of the uniform
prior, restricted along the face inclusion, equals `cardDefect n m` times the
intrinsic face marginal value.  (This is the support-face marginal-value
transport, with `boundaryCoeff` identified as `cardDefect`.) -/
theorem cardDefect_transport
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n)
    (η : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m (le_of_lt hmn))))
    (hηtan : PosteriorLawTangent η)
    (hηatom : PosteriorLawSigned.AtomicLinear η) :
    η (fun d => (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (Dist.uniform (A := canonType.{u} n))
          (Channel.actionPushforward d
            (supportIncludeKernel (canonBoundary.{u} n m (le_of_lt hmn))))) =
      cardDefect hhm hbranchConv hax n m *
        η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (canonBoundary.{u} n m (le_of_lt hmn)).restrictToSupport) := by
  classical
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  have htr := hbranchConv.marginal_value.support_face_marginalValue_scalar
    F hax hV (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m (le_of_lt hmn))
    Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n m (le_of_lt hmn) (by omega))
    (canonBoundary_nondeg n m (le_of_lt hmn) hm2)
    (canonBoundary_boundary n m (le_of_lt hmn) hmn) η hηtan hηatom
  have hcd : cardDefect hhm hbranchConv hax n m =
      (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      ).boundaryCoeff (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m (le_of_lt hmn)) := by
    rw [cardDefect, dif_pos ⟨hm2, le_of_lt hmn⟩]
  rw [hcd]
  exact htr

theorem relabelDist_eq_actionPushforward {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (e : A ≃ B) (q : Dist A) :
    relabelDist e q = Channel.actionPushforward q (fun a => Dist.pure (e a)) := by
  ext b
  rw [relabelDist_apply]
  show q (e.symm b) = ∑ a : A, q a * (Dist.pure (e a) : Dist B) b
  rw [Finset.sum_eq_single (e.symm b)]
  · rw [Equiv.apply_symm_apply, Dist.pure_apply_self, mul_one]
  · intro a _ ha
    rw [Dist.pure_apply_ne (e a) b, mul_zero]
    intro hcontra; apply ha; rw [hcontra, Equiv.symm_apply_apply]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem cBface_eq_relabel_uniform (n m : ℕ) (hmn : m ≤ n) [NeZero m] :
    haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hmn)) := supportSubtype_nonempty _
    (canonBoundary.{u} n m hmn).restrictToSupport =
      relabelDist (canonBoundarySupportEquiv n m hmn).symm (Dist.uniform (A := canonType.{u} m)) := by
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hmn)) := supportSubtype_nonempty _
  rw [canonBoundary_face_uniform n m hmn]
  ext a
  rw [Dist.uniform_apply, relabelDist_apply, Dist.uniform_apply]
  congr 1
  rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]

-- push d along pure∘nestMap = relabel e.symm (push (push d along pure∘equiv_nl) along canonIncl)
theorem push_nest_eq_relabel (n m l : ℕ) (hmn : m ≤ n) (hml : l ≤ m) [NeZero l] [NeZero m]
    (d : Dist (supportSubtype (canonBoundary.{u} n l (hml.trans hmn)))) :
    Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)) =
      relabelDist (canonBoundarySupportEquiv n m hmn).symm
        (Channel.actionPushforward
          (Channel.actionPushforward d
            (fun a => Dist.pure (canonBoundarySupportEquiv n l (hml.trans hmn) a)))
          (canonInclKernel m l hml)) := by
  rw [relabelDist_eq_actionPushforward]
  show Channel.actionPushforward d (fun a => Dist.pure (nestSupportMap n m l hmn hml a)) =
    Channel.actionPushforward
      (Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (canonBoundarySupportEquiv n l (hml.trans hmn) a)))
        (fun b => Dist.pure (ULift.up (Fin.castLE hml b.down))))
      (fun c => Dist.pure ((canonBoundarySupportEquiv n m hmn).symm c))
  rw [actionPushforward_pure_comp _ (fun a => canonBoundarySupportEquiv n l (hml.trans hmn) a)
    (fun b => ULift.up (Fin.castLE hml b.down))]
  rw [actionPushforward_pure_comp _ (fun a => ULift.up (Fin.castLE hml (canonBoundarySupportEquiv n l (hml.trans hmn) a).down))
    (fun c => (canonBoundarySupportEquiv n m hmn).symm c)]
  apply congrArg (Channel.actionPushforward d)
  funext a
  congr 1


theorem canonIncl_eq_supportInclude (m l : ℕ) (hml : l ≤ m) [NeZero l] [NeZero m]
    (x : Dist (canonType.{u} l)) :
    haveI : Nonempty (supportSubtype (canonBoundary.{u} m l hml)) := supportSubtype_nonempty _
    Channel.actionPushforward x (canonInclKernel m l hml) =
      Channel.actionPushforward
        (Channel.actionPushforward x
          (fun b => Dist.pure ((canonBoundarySupportEquiv m l hml).symm b)))
        (supportIncludeKernel (canonBoundary.{u} m l hml)) := by
  haveI : Nonempty (supportSubtype (canonBoundary.{u} m l hml)) := supportSubtype_nonempty _
  show Channel.actionPushforward x (fun b => Dist.pure (ULift.up (Fin.castLE hml b.down))) =
    Channel.actionPushforward
      (Channel.actionPushforward x (fun b => Dist.pure ((canonBoundarySupportEquiv m l hml).symm b)))
      (fun a => Dist.pure (a.1 : canonType.{u} m))
  rw [actionPushforward_pure_comp x (fun b => (canonBoundarySupportEquiv m l hml).symm b)
    (fun a => (a.1 : canonType.{u} m))]
  apply congrArg (Channel.actionPushforward x)
  funext b
  congr 1

/-- **The embedding-defect cocycle.** -/
theorem cardDefect_cocycle
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    (n m l : ℕ) [NeZero l] [NeZero m] [NeZero n]
    (hl2 : 2 ≤ l) (hlm : l < m) (hmn : m < n) :
    cardDefect hhm hbranchConv hax n m * cardDefect hhm hbranchConv hax m l =
      cardDefect hhm hbranchConv hax n l := by
  classical
  have hle_ml : l ≤ m := le_of_lt hlm
  have hle_mn : m ≤ n := le_of_lt hmn
  have hle_ln : l ≤ n := hle_ml.trans hle_mn
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hintdef
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
    with hfaithdef
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n l hle_ln)) := supportSubtype_nonempty _
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hle_mn)) := supportSubtype_nonempty _
  -- A1 nonzero tangent η on supp(cB n l)
  have hfaceNL_fs : ((canonBoundary.{u} n l hle_ln).restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport _
  have hfaceNL_nd : ∃ a b : supportSubtype (canonBoundary.{u} n l hle_ln), a ≠ b ∧
      0 < (canonBoundary.{u} n l hle_ln).restrictToSupport a ∧
      0 < (canonBoundary.{u} n l hle_ln).restrictToSupport b := by
    have hcard : Fintype.card (supportSubtype (canonBoundary.{u} n l hle_ln)) = l := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n l hle_ln)]; simp [canonType]
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card (supportSubtype (canonBoundary.{u} n l hle_ln)))
    exact ⟨a, b, hab, hfaceNL_fs a, hfaceNL_fs b⟩
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hfaith.linear_part F hax hV
      (canonBoundary.{u} n l hle_ln).restrictToSupport (canonBoundary.{u} n l hle_ln).restrictToSupport
      hfaceNL_fs hfaceNL_fs hfaceNL_nd
  -- hηnz : linPart faceNL η ≠ 0, i.e. η(mV faceNL) ≠ 0
  have hηnz' : η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) ≠ 0 := hηnz
  -- Transport at (n, l):
  have hT_nl := cardDefect_transport hhm hbranchConv hax n l hl2 (lt_of_lt_of_le hlm hle_mn) η hηtan hηatomic
  -- The nest-pushed tangent η'' on supp(cB n m)
  set η'' : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m hle_mn)) :=
    (fun ψ => η (fun d => ψ (Channel.actionPushforward d
      (fun a => Dist.pure (nestSupportMap n m l hle_mn hle_ml a))))) with hη''def
  have hη''tan : PosteriorLawTangent η'' := by
    refine ⟨?_, ?_⟩
    · show η (fun d => (1:ℝ)) = 0; exact hηtan.1
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
            d a' * (Dist.pure (nestSupportMap n m l hle_mn hle_ml a') : Dist _) a) = d a'₀
          rw [Finset.sum_eq_single a'₀]
          · rw [ha'₀, Dist.pure_apply_self, mul_one]
          · intro b _ hb
            rw [Dist.pure_apply_ne, mul_zero]
            intro hc
            apply hb
            -- nestMap b = a = nestMap a'₀, and nestMap preserves .1, so b = a'₀
            have hb1 : (nestSupportMap n m l hle_mn hle_ml b).1 = a.1 := by rw [← hc]
            have ha1 : (nestSupportMap n m l hle_mn hle_ml a'₀).1 = a.1 := by rw [ha'₀]
            apply Subtype.ext
            have : (b.1 : canonType.{u} n) = a'₀.1 := by
              have := hb1.trans ha1.symm
              simpa [nestSupportMap] using this
            exact this
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hfn]; exact hηtan.2 a'₀
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
          intro hc; exact hex ⟨a', hc.symm⟩
        rw [hfn]
        have := hηtan.1
        -- η(fun _ => 0) = 0: use η is atomicLinear ⟹ η 0 = 0
        have h0 := congrFun hηatomic.eval_eq (fun _ => (0:ℝ))
        rw [AtomicPosteriorSignedLaw.eval_apply] at h0
        rw [← h0]; simp
-- LHS link via supportInclude_nest: η(mV(u_n)∘push_{cB n l}) = η''(mV(u_n)∘push_{cB n m})
  have hLHS_link :
      η (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} n))
            (Channel.actionPushforward d (supportIncludeKernel (canonBoundary.{u} n l hle_ln)))) =
      η'' (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} n))
            (Channel.actionPushforward d (supportIncludeKernel (canonBoundary.{u} n m hle_mn)))) := by
    rw [hη''def]
    congr 1
    funext d
    rw [supportInclude_nest n m l hle_mn hle_ml d]
  have h2m : 2 ≤ m := le_of_lt (lt_of_le_of_lt hl2 hlm)
  have hη''atom : PosteriorLawSigned.AtomicLinear η'' := by
    rw [hη''def]
    exact atomicLinear_precompose
      (fun d => Channel.actionPushforward d
        (fun a => Dist.pure (nestSupportMap n m l hle_mn hle_ml a))) hηatomic
  have hT_nm := cardDefect_transport hhm hbranchConv hax n m h2m hmn η'' hη''tan hη''atom
  -- Combine hT_nl, hLHS_link, hT_nm:
  --   cardDefect n l · η(mV faceNL) = LHS_nl = LHS_nm(via link) = cardDefect n m · η''(mV faceNM)
  have hchain1 : cardDefect hhm hbranchConv hax n l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      cardDefect hhm hbranchConv hax n m *
      η'' (hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport) := by
    rw [← hT_nl, hLHS_link, hT_nm]
  -- Bridge: η''(mV faceNM) = cardDefect m l · η(mV faceNL)
-- Bridge: η''(mV faceNM) = cardDefect m l · η(mV faceNL)
  have hbridge :
      η'' (hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport) =
      cardDefect hhm hbranchConv hax m l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
    -- η''(mV faceNM) = η(fun d => mV faceNM (push d along pure∘nestMap))   [def of η'']
    show η (fun d => hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport
        (Channel.actionPushforward d
          (fun a => Dist.pure (nestSupportMap n m l hle_mn hle_ml a)))) = _
    -- push_nest_eq_relabel : push d along pure∘nestMap = relabel e.symm (push (e_nl·d) along canonIncl)
    -- and faceNM = relabel e.symm u_m ; use marginalValue_relabel to convert to mV u_m (push (e_nl·d) along canonIncl)
    have hstep : ∀ d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)),
        hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport
          (Channel.actionPushforward d
            (fun a => Dist.pure (nestSupportMap n m l hle_mn hle_ml a))) =
        hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml)) := by
      intro d
      rw [push_nest_eq_relabel n m l hle_mn hle_ml d, cBface_eq_relabel_uniform n m hle_mn]
      exact hint.marginalValue_relabel F hV (canonBoundarySupportEquiv n m hle_mn).symm
          (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml))
    rw [show (fun d => hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport
          (Channel.actionPushforward d
            (fun a => Dist.pure (nestSupportMap n m l hle_mn hle_ml a)))) =
        (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml))) from funext hstep]
    -- Now this is η(fun d => mV u_m (push (e_nl·d) along canonIncl)).
    -- = (e_nl-pushed η)(fun d' => mV u_m (push d' along canonIncl)) — a transport at (m,l).
    -- Define the pushed tangent ζ on supp(cB m l), reindexing d ↦ e_nl·d then supp.
-- φ : supp(cB n l) ≃ supp(cB m l), the composite equiv (both faces ≃ canonType l)
    set φ : supportSubtype (canonBoundary.{u} n l hle_ln) ≃ supportSubtype (canonBoundary.{u} m l hle_ml) :=
      (canonBoundarySupportEquiv n l hle_ln).trans (canonBoundarySupportEquiv m l hle_ml).symm with hφdef
    haveI : Nonempty (supportSubtype (canonBoundary.{u} m l hle_ml)) := supportSubtype_nonempty _
    -- reindex: push (e_nl·d) along canonIncl m l = push (relabel φ d) along supportInclude(cB m l)
    have hreindex : ∀ d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)),
        Channel.actionPushforward
          (Channel.actionPushforward d (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
          (canonInclKernel m l hle_ml) =
        Channel.actionPushforward (relabelDist φ d)
          (supportIncludeKernel (canonBoundary.{u} m l hle_ml)) := by
      intro d
      rw [canonIncl_eq_supportInclude m l hle_ml
        (Channel.actionPushforward d (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))]
      congr 1
      rw [relabelDist_eq_actionPushforward]
      rw [actionPushforward_pure_comp d (fun a => canonBoundarySupportEquiv n l hle_ln a)
        (fun b => (canonBoundarySupportEquiv m l hle_ml).symm b)]
      apply congrArg (Channel.actionPushforward d)
      funext a
      rfl
    -- η(fun d => mV u_m (push (e_nl·d) along canonIncl)) = η(fun d => mV u_m (push (relabel φ d) along supportInclude(cB m l)))
    rw [show (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward
            (Channel.actionPushforward d
              (fun a => Dist.pure (canonBoundarySupportEquiv n l hle_ln a)))
            (canonInclKernel m l hle_ml))) =
        (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward (relabelDist φ d)
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) from
      funext (fun d => by rw [hreindex d])]
    -- this equals ζ(fun d' => mV u_m (push d' along supportInclude(cB m l))) with ζ = relabel-transported η
    set ζ : PosteriorLawSigned (supportSubtype (canonBoundary.{u} m l hle_ml)) :=
      (fun ψ => η (fun d => ψ (relabelDist φ d))) with hζdef
    have hζtan : PosteriorLawTangent ζ := by
      refine ⟨?_, ?_⟩
      · show η (fun d => (1:ℝ)) = 0; exact hηtan.1
      · intro a
        show η (fun d => (relabelDist φ d) a) = 0
        have : (fun d : Dist (supportSubtype (canonBoundary.{u} n l hle_ln)) => (relabelDist φ d) a) =
            (fun d => d (φ.symm a)) := by funext d; rw [relabelDist_apply]
        rw [this]; exact hηtan.2 _
    -- transport at (m,l) with ζ
    have hζatom : PosteriorLawSigned.AtomicLinear ζ := by
      rw [hζdef]
      exact atomicLinear_precompose (fun d => relabelDist φ d) hηatomic
    have hT_ml := cardDefect_transport hhm hbranchConv hax m l hl2 hlm ζ hζtan hζatom
    -- LHS of hT_ml IS our expression (ζ unfolded)
    have hLHS_eq : η (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward (relabelDist φ d)
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) =
        ζ (fun d' => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward d' (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) := rfl
    rw [hLHS_eq, hT_ml]
    -- goal: cardDefect m l · ζ(mV faceML) = cardDefect m l · η(mV faceNL). Need ζ(mV faceML)=η(mV faceNL).
    congr 1
    -- ζ(mV faceML) = η(fun d => mV faceML (relabel φ d)) = η(mV faceNL)
    show η (fun d => hint.marginalValue F hV (canonBoundary.{u} m l hle_ml).restrictToSupport
        (relabelDist φ d)) = η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport)
    congr 1
    funext d
    -- faceML = relabel φ faceNL ; mV(relabel φ faceNL)(relabel φ d) = mV faceNL d
    have hfaceML_rel : (canonBoundary.{u} m l hle_ml).restrictToSupport =
        relabelDist φ (canonBoundary.{u} n l hle_ln).restrictToSupport := by
      rw [canonBoundary_face_uniform m l hle_ml, canonBoundary_face_uniform n l hle_ln]
      ext a
      rw [Dist.uniform_apply, relabelDist_apply, Dist.uniform_apply]
      congr 1
      rw [Fintype.card_congr (canonBoundarySupportEquiv m l hle_ml),
        Fintype.card_congr (canonBoundarySupportEquiv n l hle_ln)]
    rw [hfaceML_rel]
    exact hint.marginalValue_relabel F hV φ (canonBoundary.{u} n l hle_ln).restrictToSupport d
  -- final cancellation
  have hfin : cardDefect hhm hbranchConv hax n l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefect hhm hbranchConv hax n m * cardDefect hhm hbranchConv hax m l) *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
    rw [hchain1, hbridge]; ring
  have := mul_right_cancel₀ hηnz' (by linarith [hfin] : _ )
  linarith [hfin, mul_right_cancel₀ hηnz'
    (show cardDefect hhm hbranchConv hax n l *
        η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefect hhm hbranchConv hax n m * cardDefect hhm hbranchConv hax m l) *
        η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) from hfin)]

/-- **The cardinal gauge scale `t_n`.**  `t_n := cardDefect n 2` for `n ≥ 3`,
`t_2 := 1`.  By the cocycle `cardDefect n m = t_n / t_m`. -/
noncomputable def cardScaleT
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F) (n : ℕ) : ℝ :=
  if n = 2 then 1
  else if 3 ≤ n then cardDefect hhm hbranchConv hax n 2
  else 1

/-- The embedding defect factors as `cardDefect n m = t_n / t_m` (the cocycle,
setting `ℓ = 2`). -/
theorem cardDefect_eq_ratio
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n) :
    cardDefect hhm hbranchConv hax n m =
      cardScaleT hhm hbranchConv hax n / cardScaleT hhm hbranchConv hax m := by
  have hn3 : 3 ≤ n := by omega
  have htn : cardScaleT hhm hbranchConv hax n = cardDefect hhm hbranchConv hax n 2 := by
    rw [cardScaleT]; rw [if_neg (by omega), if_pos hn3]
  rcases eq_or_lt_of_le hm2 with hm2eq | hm2lt
  · subst hm2eq
    rw [htn]
    have htm : cardScaleT hhm hbranchConv hax 2 = 1 := by rw [cardScaleT, if_pos rfl]
    rw [htm, div_one]
  · have hm3 : 3 ≤ m := by omega
    haveI : NeZero (2:ℕ) := ⟨by norm_num⟩
    have hcoc := cardDefect_cocycle hhm hbranchConv hax n m 2 (le_refl 2) hm2lt hmn
    have htm : cardScaleT hhm hbranchConv hax m = cardDefect hhm hbranchConv hax m 2 := by
      rw [cardScaleT, if_neg (by omega), if_pos hm3]
    have hpos : 0 < cardDefect hhm hbranchConv hax m 2 :=
      cardDefect_pos hhm hbranchConv hax m 2 (by norm_num) hm2lt
    rw [htn, htm]
    field_simp
    linarith [hcoc]

/-- The faithful chain scale is positive for **every** prior (full-support via
`scale_pos`; boundary/singleton priors have `scale = branchPathCoeff q u = 1`). -/
theorem faithful_scale_pos
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 < (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale q := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
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
    F hax hV q r hq hrn hrnd hrb η hηtan hηatomic
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
  have hη'atom : PosteriorLawSigned.AtomicLinear η' := by
    rw [hη'def]
    show PosteriorLawSigned.AtomicLinear
      (fun ψ => η (fun d => ψ (Relabeling.relabelDist (relabelSupportEquiv e r).symm d)))
    exact atomicLinear_precompose
      (fun d => Relabeling.relabelDist (relabelSupportEquiv e r).symm d) hηatomic
  have hTqr' := hbranchConv.marginal_value.support_face_marginalValue_scalar
    F hax hV (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) hrqn hrnn hrndn hrbn η' hη'tan hη'atom
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
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
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
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport *
      η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        (Dist.uniform (A := supportSubtype r))) := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
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
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {C : Type u} [Fintype C] [DecidableEq C] [Nonempty C]
    (q ρ σ : Dist C) (hq : q.FullSupport)
    (hsupp : ∀ c, ρ c > 0 ↔ σ c > 0)
    (hρn : ∃ a : C, 0 < ρ a)
    (hρnd : ∃ a b : C, a ≠ b ∧ 0 < ρ a ∧ 0 < ρ b)
    (hρb : ¬ ρ.FullSupport) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
    ).boundaryCoeff q ρ *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale ρ.restrictToSupport =
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
    ).boundaryCoeff q σ *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale σ.restrictToSupport := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
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
  have hTρ := hbranchConv.marginal_value.support_face_marginalValue_scalar
    F hax hV q ρ hq hρn hρnd hρb η hηtan hηatomic
  -- E : suppSub ρ ≃ suppSub σ
  set E := sameSupportEquiv ρ σ hsupp with hEdef
  -- transported tangent η' on suppSub σ (pullback along E⁻¹? no: relabelPullback E)
  set η' : PosteriorLawSigned (supportSubtype σ) := relabelPullback E η with hη'def
  have hη'atomic : PosteriorLawSigned.AtomicLinear η' := atomicLinear_relabelPullback E hηatomic
  have hη'tan : PosteriorLawTangent η' := relabelPullback_tangent E hηtan
  -- transport at σ:  η'(fun d' => mV q (push_σ d')) = bc q σ · η'(mV σ|supp)
  have hTσ := hbranchConv.marginal_value.support_face_marginalValue_scalar
    F hax hV q σ hq hσn hσnd hσb η' hη'tan hη'atomic
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
  have hfρ := face_scalar_relation hhm hbranchConv hax ρ hρs_nd η hηatomic hηtan
  have hσs_nd : ∃ a b : supportSubtype σ, a ≠ b ∧
      0 < σ.restrictToSupport a ∧ 0 < σ.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hσnd
    exact ⟨⟨a, ha⟩, ⟨b, hb'⟩, by intro h; exact hab (congrArg Subtype.val h),
      by rw [Dist.restrictToSupport_apply]; exact ha, by rw [Dist.restrictToSupport_apply]; exact hb'⟩
  have hfσ := face_scalar_relation hhm hbranchConv hax σ hσs_nd η' hη'atomic hη'tan
  -- η'(mV uniform_σ) = η(mV uniform_ρ) via marginalValue_relabel + uniform preservation
  have huniσ : Relabeling.relabelDist E (Dist.uniform (A := supportSubtype ρ)) =
      Dist.uniform (A := supportSubtype σ) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply, Fintype.card_congr E]
  have huninz : η' (hint.marginalValue F hV (Dist.uniform (A := supportSubtype σ))) =
      η (hint.marginalValue F hV (Dist.uniform (A := supportSubtype ρ))) := by
    show η (fun d => hint.marginalValue F hV (Dist.uniform (A := supportSubtype σ))
        (Relabeling.relabelDist E d)) = _
    congr 1
    funext d
    rw [← huniσ]
    exact hint.marginalValue_relabel F hV E (Dist.uniform (A := supportSubtype ρ)) d
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

/-- The relabelled boundary prior `relabel (alignEquiv r) r` and the canonical
`m`-face (`m = card supp r`) share the same positive support set. -/
theorem alignEquiv_relabel_support_eq {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (m : ℕ) (hm : m = Fintype.card (supportSubtype r)) [NeZero m]
    (hmn : m ≤ Fintype.card A) (c : canonType.{u} (Fintype.card A)) :
    (Relabeling.relabelDist (alignEquiv r) r) c > 0 ↔ (canonBoundary.{u} (Fintype.card A) m hmn) c > 0 := by
  classical
  rw [Relabeling.relabelDist_apply]
  obtain ⟨j⟩ := c
  rw [gt_iff_lt, gt_iff_lt, show ({ down := j } : canonType.{u} (Fintype.card A)) = ULift.up j from rfl,
    canonBoundary_pos]
  constructor
  · intro hpos
    have hlt := alignEquiv_lt_of_pos r ((alignEquiv r).symm (ULift.up j)) hpos
    rw [Equiv.apply_symm_apply] at hlt
    change (j : ℕ) < Fintype.card (supportSubtype r) at hlt
    omega
  · intro hjm
    by_contra hnp
    have hge := alignEquiv_ge_of_not_pos r ((alignEquiv r).symm (ULift.up j)) hnp
    rw [Equiv.apply_symm_apply] at hge
    change Fintype.card (supportSubtype r) ≤ (j : ℕ) at hge
    omega

/-- **Embedding-defect reduction at the uniform ambient prior.**  For the uniform
prior `u_A` and a boundary posterior `r` with `2 ≤ card supp r < card A`, the
scaled boundary coefficient equals the canonical `cardDefect`.  Proof: relabel to
`canonType (card A)` by `alignEquiv r` (uniform ↦ uniform, defect and face scale
relabel-invariant), whereupon `relabel (alignEquiv r) r` shares the support of the
canonical face, so within-face independence swaps it for the uniform face whose
scale is `1`, leaving `bc(u_n, canonBoundary) = cardDefect`. -/
theorem general_defect_uniform
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport)
    (hm2 : 2 ≤ Fintype.card (supportSubtype r))
    (hmn : Fintype.card (supportSubtype r) < Fintype.card A) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
    ).boundaryCoeff (Dist.uniform (A := A)) r *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport =
    cardDefect hhm hbranchConv hax (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  classical
  set n := Fintype.card A with hndef
  set m := Fintype.card (supportSubtype r) with hmdef
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
  set hb := branchBoundaryFaceScale_of_faithfulAssumptions hfaith
  set e := alignEquiv r with hedef
  set r' := Relabeling.relabelDist e r with hr'def
  -- uniform relabels to uniform
  have huni : Relabeling.relabelDist e (Dist.uniform (A := A)) = Dist.uniform (A := canonType.{u} n) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply]
    congr 1
    exact congrArg (Nat.cast) (Fintype.card_congr e)
  -- Step 1: bc(u_A,r) = bc(u_n, r') via boundaryCoeff_relabel
  have hbc_rel : hb.boundaryCoeff (Dist.uniform (A := A)) r =
      hb.boundaryCoeff (Dist.uniform (A := canonType.{u} n)) r' := by
    rw [← huni]
    exact (boundaryCoeff_relabel_of_FinalHM hhm hbranchConv hax e (Dist.uniform (A := A)) r
      Dist.uniform_fullSupport hrn hrnd hrb).symm
  -- Step 2: scale(r|supp) = scale(r'|supp) via scale-relabel on restrictToSupport_relabelDist
  have hscale_rel : (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport =
      (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r'.restrictToSupport := by
    have hface : r'.restrictToSupport =
        Relabeling.relabelDist (relabelSupportEquiv e r).symm r.restrictToSupport :=
      restrictToSupport_relabelDist e r
    rw [hface]
    exact (scaleRelabel_of_FinalHM_covariance hhm hbranchConv hax (relabelSupportEquiv e r).symm
      r.restrictToSupport (Dist.restrictToSupport_fullSupport r)).symm
  rw [hbc_rel, hscale_rel]
  -- Step 3: r' shares support with cB n m ; within-face independence
  have hmn' : m ≤ n := le_of_lt hmn
  have hsupp : ∀ c, r' c > 0 ↔ (canonBoundary.{u} n m hmn') c > 0 :=
    alignEquiv_relabel_support_eq r m hmdef hmn'
  -- boundary data for r'
  have hr'n : ∃ b : canonType.{u} n, 0 < r' b := by
    obtain ⟨a, ha⟩ := hrn
    exact ⟨e a, by rw [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact ha⟩
  have hr'nd : ∃ a b : canonType.{u} n, a ≠ b ∧ 0 < r' a ∧ 0 < r' b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hrnd
    exact ⟨e a, e b, fun h => hab (e.injective h),
      by rw [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact ha,
      by rw [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact hb'⟩
  have hr'b : ¬ r'.FullSupport := by
    intro hfs; apply hrb; intro a
    have := hfs (e a); rwa [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply] at this
  -- within-face: bc(u_n,r')·scale(r'|supp) = bc(u_n, cB n m)·scale(cB n m|supp)
  have hwf := boundaryCoeff_scale_within_face hhm hbranchConv hax
    (Dist.uniform (A := canonType.{u} n)) r' (canonBoundary.{u} n m hmn')
    Dist.uniform_fullSupport hsupp hr'n hr'nd hr'b
  rw [hwf]
  -- scale(cB n m|supp) = 1, and bc(u_n, cB n m) = cardDefect n m
  rw [canonBoundary_face_scale_eq_one hhm hbranchConv hax n m hmn' hm2, mul_one]
  rw [cardDefect, dif_pos ⟨hm2, hmn'⟩]

/-- **General embedding-defect reduction.**  For any full-support ambient prior
`q` and boundary posterior `r` (with `2 ≤ card supp r < card A`), the scaled
boundary coefficient is `scale q · cardDefect(card A, card supp r)`. -/
theorem general_defect
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport)
    (hm2 : 2 ≤ Fintype.card (supportSubtype r))
    (hmn : Fintype.card (supportSubtype r) < Fintype.card A) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
    ).boundaryCoeff q r *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport =
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale q *
      cardDefect hhm hbranchConv hax (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
  set hb := branchBoundaryFaceScale_of_faithfulAssumptions hfaith
  -- scale q = branchPathCoeff q uniform
  have hscale_q : (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).scale_factorization.scale q = hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
    show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).branch_agg.branchCoeff q (Dist.uniform (A := A)) = _
    rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff q (Dist.uniform (A := A)) =
      branchCoeffFromTangentRepParts hpath hb hfaith.singleton_scale q (Dist.uniform (A := A))
      from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  -- qIndep:  bc(u_A,r) · bpc(q,u_A) = bc(q,r)
  have hqi := boundaryCoeff_qIndep_of_FinalHM hhm hbranchConv hax
    (Dist.uniform (A := A)) q r Dist.uniform_fullSupport hq hrn hrnd hrb
  -- hqi : hb.boundaryCoeff u_A r * hpath.branchPathCoeff q u_A = hb.boundaryCoeff q r
  have hbcq : hb.boundaryCoeff q r =
      hb.boundaryCoeff (Dist.uniform (A := A)) r *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).scale_factorization.scale q := by
    rw [hscale_q]; exact hqi.symm
  rw [hbcq]
  -- now  bc(u_A,r)·scale q · scale(r|supp) = scale q · cardDefect
  have hgu := general_defect_uniform hhm hbranchConv hax r hrn hrnd hrb hm2 hmn
  -- hgu : bc(u_A,r)·scale(r|supp) = cardDefect
  set s := hb.boundaryCoeff (Dist.uniform (A := A)) r
  set sq := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).scale_factorization.scale q
  set srs := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).scale_factorization.scale r.restrictToSupport
  -- goal: s * sq * srs = sq * cardDefect ; hgu : s * srs = cardDefect
  have : s * sq * srs = sq * (s * srs) := by ring
  rw [this, hgu]

/-- At least two positive-support actions when `r` is nondegenerate. -/
theorem two_le_card_supp {A : Type u} [Fintype A] [DecidableEq A] (r : Dist A)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    2 ≤ Fintype.card (supportSubtype r) := by
  classical
  obtain ⟨a, b, hab, ha, hb⟩ := hrnd
  have : 1 < Fintype.card (supportSubtype r) :=
    Fintype.one_lt_card_iff.mpr ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  omega

/-- A boundary prior has strictly fewer support actions than the ambient set. -/
theorem card_supp_lt {A : Type u} [Fintype A] [DecidableEq A] (r : Dist A)
    (hrb : ¬ r.FullSupport) :
    Fintype.card (supportSubtype r) < Fintype.card A := by
  classical
  have hex : ∃ a : A, ¬ (r a > 0) := by
    by_contra hall
    exact hrb (fun a => not_not.mp (fun hna => hall ⟨a, hna⟩))
  obtain ⟨a, ha⟩ := hex
  exact Fintype.card_subtype_lt (p := fun x => r x > 0) ha

/-- The support face of a support-restricted prior has the same cardinality as
the original support. -/
theorem card_supp_restrict {A : Type u} [Fintype A] [DecidableEq A] (r : Dist A) :
    Fintype.card (supportSubtype (r.restrictToSupport)) = Fintype.card (supportSubtype r) := by
  apply Fintype.card_congr
  refine ⟨fun a => ⟨a.1.1, a.1.2⟩, fun b => ⟨⟨b.1, b.2⟩,
    by show r.restrictToSupport ⟨b.1, b.2⟩ > 0; rw [Dist.restrictToSupport_apply]; exact b.2⟩,
    fun a => by apply Subtype.ext; apply Subtype.ext; rfl, fun b => by apply Subtype.ext; rfl⟩

/-- The cardinal gauge scale is positive for every `n`. -/
theorem cardScaleT_pos
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F) (n : ℕ) :
    0 < cardScaleT hhm hbranchConv hax n := by
  rw [cardScaleT]
  by_cases h2 : n = 2
  · rw [if_pos h2]; exact one_pos
  · rw [if_neg h2]
    by_cases h3 : 3 ≤ n
    · rw [if_pos h3]
      exact cardDefect_pos hhm hbranchConv hax n 2 (le_refl 2) (by omega)
    · rw [if_neg h3]; exact one_pos

/-- **The cardinal gauge.**  `g(q) := cardScaleT (card A) = t_{card A}` — a positive
constant depending only on the cardinality of the action set.  It is internally
defined from the embedding defect (`cardDefect n 2`), not an external convention.
With this gauge the raw face-scale equation `support_scale` becomes provable from
the general embedding-defect reduction and the cocycle `cardDefect n m = t_n/t_m`. -/
noncomputable def cardinalGauge
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F) :
    PositiveFaceScaleGauge.{u} where
  gauge := fun {A} _ _ _ _ => cardScaleT hhm hbranchConv hax (Fintype.card A)
  gauge_pos := fun {A} _ _ _ _ => cardScaleT_pos hhm hbranchConv hax (Fintype.card A)

/-- The cardinal gauge is relabelling-invariant (depends only on cardinality). -/
theorem cardinalGauge_gaugeRel
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (e : A ≃ B) (q : Dist A) :
    (cardinalGauge hhm hbranchConv hax).gauge (Relabeling.relabelDist e q) =
      (cardinalGauge hhm hbranchConv hax).gauge q := by
  show cardScaleT hhm hbranchConv hax (Fintype.card B) =
    cardScaleT hhm hbranchConv hax (Fintype.card A)
  rw [Fintype.card_congr e.symm]

/-- The cardinal-gauge scale-relabelling equation (`hrel`): the gauged scale is
relabelling-invariant.  `g` is cardinality-only and the raw chain scale is
relabel-invariant (R1). -/
theorem cardinalGauge_hrel
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (cardinalGauge hhm hbranchConv hax).gauge (Relabeling.relabelDist e q) *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
          F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        ).scale_factorization.scale (Relabeling.relabelDist e q) =
      (cardinalGauge hhm hbranchConv hax).gauge q *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
          F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        ).scale_factorization.scale q := by
  rw [cardinalGauge_gaugeRel hhm hbranchConv hax e q,
    scaleRelabel_of_FinalHM_covariance hhm hbranchConv hax e q hq]

/-- **The cardinal-gauge support-face equation (`hsupport`).**  With the cardinal
gauge, the raw face-scale equation holds: `(g q / g r)·branchCoeff q r =
(g q·scale q)/(g(r|supp)·scale(r|supp))`.  Proof: `g q = g r = t_n` cancel on the
left; `branchCoeff q r = boundaryCoeff q r`; the general embedding-defect reduction
gives `boundaryCoeff q r·scale(r|supp) = scale q·cardDefect n m`; and the cocycle
`cardDefect n m = t_n / t_m` with `t_m = g(r|supp)` closes it. -/
theorem cardinalGauge_hsupport
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchConv : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    ((cardinalGauge hhm hbranchConv hax).gauge q /
        (cardinalGauge hhm hbranchConv hax).gauge r) *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
          F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        ).branch_agg.branchCoeff q r =
      ((cardinalGauge hhm hbranchConv hax).gauge q *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale q) /
        ((cardinalGauge hhm hbranchConv hax).gauge r.restrictToSupport *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale r.restrictToSupport) := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
  set hb := branchBoundaryFaceScale_of_faithfulAssumptions hfaith
  set n := Fintype.card A with hndef
  set m := Fintype.card (supportSubtype r) with hmdef
  haveI : NeZero m := ⟨by have := two_le_card_supp r hrnd; omega⟩
  haveI : NeZero n := ⟨Fintype.card_ne_zero⟩
  have hm2 : 2 ≤ m := two_le_card_supp r hrnd
  have hmn : m < n := card_supp_lt r hrb
  simp only [cardinalGauge, card_supp_restrict r]
  have hbcq : (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branch_agg.branchCoeff q r = hb.boundaryCoeff q r := by
    set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branch_agg.branchCoeff q r =
      branchCoeffFromTangentRepParts hpath hb hfaith.singleton_scale q r from rfl]
    unfold branchCoeffFromTangentRepParts
    rw [dif_neg hrb, dif_pos hrnd]
  rw [hbcq]
  have hgd := general_defect hhm hbranchConv hax q r hq hrn hrnd hrb hm2 hmn
  have hratio := cardDefect_eq_ratio hhm hbranchConv hax n m hm2 hmn
  have htn := cardScaleT_pos hhm hbranchConv hax n
  have htm := cardScaleT_pos hhm hbranchConv hax m
  have hscq := faithful_scale_pos hhm hbranchConv hax q
  have hscrs := faithful_scale_pos hhm hbranchConv hax r.restrictToSupport
  set bc := hb.boundaryCoeff q r
  set sq := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax)).scale_factorization.scale q
  set srs := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport
  set tn := cardScaleT hhm hbranchConv hax n
  set tm := cardScaleT hhm hbranchConv hax m
  rw [hratio] at hgd
  rw [div_self (ne_of_gt htn), one_mul]
  rw [eq_div_iff (by positivity)]
  have hcalc : bc * (tm * srs) = tm * (bc * srs) := by ring
  rw [hcalc, hgd]
  field_simp

/-- **Value relabelling invariance, PROVED from the integral representation.**

`V q E = ∫ marginalValue q  d(posterior law of (q,E))` (`value_eq_integral`); the
posterior-law integral is relabel-covariant (`posteriorLawIntegral_relabelChannel`),
and the representing test function is relabel-natural (`marginalValue_relabel`).
Hence `V (relabel q) (relabel E) = V q E` outright — the value-level relabelling
scalar is `1`, with no gauge, no product quasi-additivity, and no scalar-pinning
assumption. -/
theorem V_relabel_eq_of_integralRepresentation
    {F : PrefFamily.{u}}
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hV : PosteriorValueRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O) :
    hV.V (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      hV.V q (experimentOfChannel P) := by
  rw [hint.value_eq_integral F hV (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)),
      hint.value_eq_integral F hV q (experimentOfChannel P)]
  rw [posteriorLawIntegralExp_experimentOfChannel, posteriorLawIntegralExp_experimentOfChannel]
  rw [posteriorLawIntegral_relabelChannel eA eO q P
        (hint.marginalValue F hV (Relabeling.relabelDist eA q))]
  refine congrArg _ ?_
  funext d
  exact hint.marginalValue_relabel F hV eA q d

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

/-- **Selected value relabelling for the cardinal-gauge coherent representative,
PROVED (no assumption, no product-QA, no scalar pinning).**

The coherent value functional is `g(q)·V_HM q E` with `g = cardinalGauge`
(cardinality-only, hence relabel-invariant, `cardinalGauge_gaugeRel`) and `V_HM`
the constructed HM functional, whose relabelling invariance is a theorem from the
integral representation (`V_relabel_eq_of_integralRepresentation`, via the
`marginalValue_relabel` naturality clause).  The gauge factors cancel (same
cardinality under a bijection) and the HM value is invariant, so the selected
relabelling scalar is `1`. -/
theorem selectedValueRelabel_of_cardinalGauge
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (branch : FinalFaithfulBranchConventions hhm) (hax : TraceAxioms F) :
    FiniteSelectedPosteriorValueRelabelingFor
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
        hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
          cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)) where
  V_relabel_eq := by
    intro _hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    show (cardinalGauge hhm branch hax).gauge (Relabeling.relabelDist eA q) *
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      (cardinalGauge hhm branch hax).gauge q *
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P)
    rw [cardinalGauge_gaugeRel hhm branch hax eA q]
    rw [V_relabel_eq_of_integralRepresentation
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax) eA eO q P]

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

/-- Posterior-law integral of the doubly-uninformative product experiment is the
prior evaluation (single outcome, posterior = prior). -/
theorem prodChannel_uninformativeU_uninformativeU_posteriorLawIntegral
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (q : Dist A) (r : Dist B)
    (φ : Dist (A × B) → ℝ) :
    posteriorLawIntegral (prodDist q r)
      (prodChannel (Channel.uninformativeChannelU A) (Channel.uninformativeChannelU B)) φ =
      φ (prodDist q r) := by
  have hmarg : ∀ u : PUnit.{u+1} × PUnit.{u+1},
      Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B)) (prodDist q r) u = 1 := by
    intro u
    have h1 : ∀ x : A × B, (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B) x).prob u = 1 := by
      intro x; obtain ⟨o1, o2⟩ := u
      simp [prodChannel_apply, Channel.uninformativeChannelU]
    simp only [Channel.outcomeMarginal_apply, h1, mul_one]
    exact (prodDist q r).sum_eq_one
  have hpost : ∀ u : PUnit.{u+1} × PUnit.{u+1},
      Channel.posterior (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B)) (prodDist q r) u = prodDist q r := by
    intro u
    ext x
    rw [Channel.posterior, dif_pos (by rw [hmarg u]; norm_num)]
    show (prodDist q r).prob x *
        (prodChannel (Channel.uninformativeChannelU A) (Channel.uninformativeChannelU B) x).prob u /
        (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A)
          (Channel.uninformativeChannelU B)) (prodDist q r)).prob u = (prodDist q r).prob x
    have h1 : (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B) x).prob u = 1 := by
      obtain ⟨o1, o2⟩ := u
      simp [prodChannel_apply, Channel.uninformativeChannelU]
    rw [h1, mul_one, hmarg u, div_one]
  unfold posteriorLawIntegral
  rw [Finset.sum_eq_single (PUnit.unit, PUnit.unit)]
  · rw [hmarg, hpost]; ring
  · intro u _ hne; exact absurd (by obtain ⟨⟨⟩,⟨⟩⟩ := u; rfl) hne
  · intro h; exact absurd (Finset.mem_univ _) h

theorem productLift_value_affine_of_A5_HM
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) :
    ∃ a : ℝ, 0 < a ∧ ∀ {O : Type u} [Fintype O] [DecidableEq O] (P : Channel A O),
      faceScaleProductLeftSliceValue hfaces q r (Channel.uninformativeChannelU B) P =
        a * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) := by
  classical
  have hcoord := faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces
  have hbaseA := faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces
  have hsame := (faceScaleProductLeftSliceSameOrder_of_A8 hfaces).left_slice_same_order
  have hzeroB : hfaces.branch_result.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  obtain ⟨a, b, ha_pos, haffine⟩ :=
    classicalFiniteAffineUtilityUniquenessAssumptions.positive_affine_transform
      (A := A)
      (fun {O} _ _ P => hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P))
      (fun {O} _ _ P => faceScaleProductLeftSliceValue hfaces q r (Channel.uninformativeChannelU B) P)
      (by
        intro O Z _ _ _ _ t ht0 ht1 P Q
        exact hbaseA.base_value_publicMix_affine hax q hq t ht0 ht1 P Q)
      (by
        intro O Z _ _ _ _ t ht0 ht1 P Q
        exact hcoord.left_slice_publicMix_affine hax q r hq hr
          (Channel.uninformativeChannelU B) t ht0 ht1 P Q)
      (by
        show hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Channel.idChannel) ≠
          hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel (Channel.uninformativeChannelU A))
        rw [hzeroB]; exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA)
      (by
        intro O _ _ P Q
        exact hsame hax q r hq hr (Channel.uninformativeChannelU B) P Q)
  -- haffine : ∀ P, target P = a * base P + b.  Pin b=0 at P = U_A.
  refine ⟨a, ha_pos, ?_⟩
  intro O _ _ P
  have hb0 : b = 0 := by
    have hU := haffine (Channel.uninformativeChannelU A)
    -- target U_A = faceScaleProductLeftSliceValue hfaces q r U_B U_A = V(q⊗r, U_A ⊗ U_B)
    -- base U_A = V(q, U_A) = 0
    rw [hzeroB, mul_zero, zero_add] at hU
    -- hU : faceScaleProductLeftSliceValue ... (U_A) = b ; and LHS = V(q⊗r, U_A⊗U_B) = 0 (zero_normalized at q⊗r? U_A⊗U_B ~ U_{A×B})
    have hprodfs : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hUAB : faceScaleProductLeftSliceValue hfaces q r
        (Channel.uninformativeChannelU B) (Channel.uninformativeChannelU A) = 0 := by
      show hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A)
          (Channel.uninformativeChannelU B))) = 0
      -- V(q⊗r, U_A⊗U_B): its posterior law equals that of U_{A×B}, so V = 0.
      have hsame2 : SamePosteriorLawExp (prodDist q r)
          (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A)
            (Channel.uninformativeChannelU B)))
          (experimentOfChannel (Channel.uninformativeChannelU (A × B))) := by
        intro φ _hcont
        rw [posteriorLawIntegralExp_experimentOfChannel,
          posteriorLawIntegralExp_uninformativeChannelU_eq_prior]
        exact prodChannel_uninformativeU_uninformativeU_posteriorLawIntegral q r φ
      rw [hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law _ _ _ hsame2]
      exact hfaces.branch_result.branch_agg.value_rep.zero_normalized (prodDist q r) hprodfs
    rw [hUAB] at hU
    exact hU.symm
  have h := haffine (O := O) P
  rw [hb0, add_zero] at h
  exact h

/-- The canonical positive product-lift scale `a(q,r)` from
`productLift_value_affine_of_A5_HM`: the unique positive real with
`V(q⊗r, P⊗U_B) = a · V(q,P)` for all `P` (full-support `q,r`, `¬Subsingleton A`).
Defaults to `1` in the degenerate cases. -/
noncomputable def productLiftScale
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A then
      Classical.choose (productLift_value_affine_of_A5_HM hfaces hhm hax q r h.1 h.2.1 h.2.2)
    else 1

theorem productLiftScale_pos
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    0 < productLiftScale hfaces hhm hax q r := by
  classical
  unfold productLiftScale
  by_cases h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A
  · rw [dif_pos h]
    exact (Classical.choose_spec (productLift_value_affine_of_A5_HM hfaces hhm hax q r h.1 h.2.1 h.2.2)).1
  · rw [dif_neg h]; exact one_pos

/-- Characterization: `V(q⊗r, P⊗U_B) = productLiftScale · V(q,P)`. -/
theorem productLiftScale_spec
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A)
    {O : Type u} [Fintype O] [DecidableEq O] (P : Channel A O) :
    faceScaleProductLeftSliceValue hfaces q r (Channel.uninformativeChannelU B) P =
      productLiftScale hfaces hhm hax q r *
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) := by
  classical
  have h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A := ⟨hq, hr, hA⟩
  rw [productLiftScale, dif_pos h]
  exact (Classical.choose_spec (productLift_value_affine_of_A5_HM hfaces hhm hax q r hq hr hA)).2 P


/-- **Transparency identity: the product left-coefficient IS the proven-positive
`productLiftScale`.**  The multi-pieces `leftCoeff` — whose normalization to `1` is
exactly the `current_leftCoeff_normalized` field of `current_product_gauge` — equals
`productLiftScale q r` (`> 0`).  Hence `current_product_gauge` is transparently the
coherent gauge choice `productLiftScale ≡ 1`, a normalization of a value that A5/A8 +
HM-uniqueness *prove* exists and is positive; it is not an opaque assumption. -/
theorem leftCoeff_eq_productLiftScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hslope : FiniteFaceScaleProductSliceSlopeAssumptionsFor hslice)
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) :
    hslope.leftCoeff hax q r = productLiftScale hfaces hhm hax q r := by
  classical
  -- leftSliceSlope(q,r,U_B) = leftCoeff (since V(r,U_B)=0)
  have hVrU : hfaces.branch_result.branch_agg.value_rep.V r
      (experimentOfChannel (Channel.uninformativeChannelU B)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr
  have hslopeU : hslice.leftSliceSlope hax q r (Channel.uninformativeChannelU B) =
      hslope.leftCoeff hax q r := by
    rw [hslope.leftSliceSlope_value hax q r hq hr hA (Channel.uninformativeChannelU B), hVrU,
      mul_zero, add_zero]
  -- left_slice_affine at U_B and id: faceScaleProductLeftSliceValue = leftSliceSlope·V(q,·)+intercept
  -- Use two channels with different base values: idChannel and U_A.
  -- Step 2 spec at id and U_A
  have hspecId := productLiftScale_spec hfaces hhm hax q r hq hr hA Channel.idChannel
  have hspecU := productLiftScale_spec hfaces hhm hax q r hq hr hA (Channel.uninformativeChannelU A)
  -- left_slice_affine at id and U_A (R := U_B)
  have haffId := hslice.left_slice_affine hax q r hq hr Channel.idChannel (Channel.uninformativeChannelU B)
  have haffU := hslice.left_slice_affine hax q r hq hr (Channel.uninformativeChannelU A) (Channel.uninformativeChannelU B)
  -- faceScaleProductLeftSliceValue hfaces q r R P = V(q⊗r, prodChannel P R) by def
  -- so hspec* LHS = haff* LHS. Combine.
  set VqId := hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Channel.idChannel) with hVqId
  set VqU := hfaces.branch_result.branch_agg.value_rep.V q
    (experimentOfChannel (Channel.uninformativeChannelU A)) with hVqU
  set ic := hslice.leftSliceIntercept hax q r (Channel.uninformativeChannelU B) with hic
  set lc := hslope.leftCoeff hax q r with hlc
  set pls := productLiftScale hfaces hhm hax q r with hpls
  -- rewrite haff via hslopeU: leftSliceSlope U_B = lc
  rw [hslopeU] at haffId haffU
  -- hspecId : faceScaleProductLeftSliceValue .. Channel.idChannel = pls * VqId
  -- haffId  : V(q⊗r, prodChannel id U_B) = lc * VqId + ic   [LHS defeq faceScaleProductLeftSliceValue]
  have hId : pls * VqId = lc * VqId + ic := by
    rw [← hspecId]; exact haffId
  have hU0 : VqU = 0 := hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  have hU : pls * VqU = lc * VqU + ic := by
    rw [← hspecU]; exact haffU
  rw [hU0, mul_zero, mul_zero, zero_add] at hU
  -- hU : 0 = ic ; so ic = 0
  rw [← hU, add_zero] at hId
  -- hId : pls * VqId = lc * VqId
  have hVqId_ne : VqId ≠ 0 := faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
  exact (mul_right_cancel₀ hVqId_ne hId).symm


/-- **The product-lift scale is a cocycle** (WLOG certificate for the coherent
normalization `productLiftScale ≡ 1`): for full-support `q,r,s` with
`¬Subsingleton A`,
`productLiftScale q (r⊗s) = productLiftScale (q⊗r) s · productLiftScale q r`.
A cocycle is a coboundary here, so a normalizing gauge exists — the normalization
`current_product_gauge` is *without loss of generality*.  QA-free: two applications
of the gauge-free `productLiftScale_spec` reassociated by HM relabel-covariance. -/
theorem productLiftScale_cocycle
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hcov : ∀ {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B] [Fintype O] [DecidableEq O]
        [Fintype Y] [DecidableEq Y] (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O),
        hfaces.branch_result.branch_agg.value_rep.V (Relabeling.relabelDist eA q)
            (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P))
    (hax : TraceAxioms F)
    {A B C : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hs : s.FullSupport)
    (hA : ¬ Subsingleton A) :
    productLiftScale hfaces hhm hax q (prodDist r s) =
      productLiftScale hfaces hhm hax (prodDist q r) s *
        productLiftScale hfaces hhm hax q r := by
  classical
  -- base channel: idChannel on A, V(q, id) ≠ 0
  have hVqP_ne : hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  -- Abbreviations
  set Vrep := hfaces.branch_result.branch_agg.value_rep with hVrepdef
  set P : Channel A A := Channel.idChannel with hPdef
  -- Step 2 spec instances (each: faceScaleProductLeftSliceValue = productLiftScale · V(q,·))
  -- LHS: V(q⊗(r⊗s), P ⊗ U_{B×C}) = productLiftScale q (r⊗s) · V(q,P)
  have hLHS := productLiftScale_spec hfaces hhm hax q (prodDist r s) hq hrs hA P
  -- inner: V(q⊗r, P ⊗ U_B) = productLiftScale q r · V(q,P)
  have hInner := productLiftScale_spec hfaces hhm hax q r hq hr hA P
  -- outer: V((q⊗r)⊗s, (P⊗U_B) ⊗ U_C) = productLiftScale (q⊗r) s · V(q⊗r, P⊗U_B)
  have hAqr : ¬ Subsingleton (A × B) := by
    rw [not_subsingleton_iff_nontrivial] at hA ⊢
    obtain ⟨a, b, hab⟩ := hA
    exact ⟨(a, Classical.arbitrary B), (b, Classical.arbitrary B), by simp [hab]⟩
  have hOuter := productLiftScale_spec hfaces hhm hax (prodDist q r) s hqr hs hAqr
    (leftProductLiftChannel (B := B) P)
  -- unfold faceScaleProductLeftSliceValue definitionally
  rw [show faceScaleProductLeftSliceValue hfaces q (prodDist r s)
      (Channel.uninformativeChannelU (B × C)) P =
      Vrep.V (prodDist q (prodDist r s))
        (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU (B × C)))) from rfl] at hLHS
  rw [show faceScaleProductLeftSliceValue hfaces q r (Channel.uninformativeChannelU B) P =
      Vrep.V (prodDist q r) (experimentOfChannel (leftProductLiftChannel (B := B) P)) from rfl] at hInner
  rw [show faceScaleProductLeftSliceValue hfaces (prodDist q r) s
      (Channel.uninformativeChannelU C) (leftProductLiftChannel (B := B) P) =
      Vrep.V (prodDist (prodDist q r) s)
        (experimentOfChannel (prodChannel (leftProductLiftChannel (B := B) P)
          (Channel.uninformativeChannelU C))) from rfl] at hOuter
  -- V((q⊗r)⊗s, (P⊗U_B)⊗U_C) = V(q⊗(r⊗s), P⊗U_{B×C}) via associativity relabel + hcov
  have hassoc : Vrep.V (prodDist (prodDist q r) s)
        (experimentOfChannel (prodChannel (leftProductLiftChannel (B := B) P)
          (Channel.uninformativeChannelU C))) =
      Vrep.V (prodDist q (prodDist r s))
        (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU (B × C)))) := by
    -- (i) associativity: V((q⊗r)⊗s, (P⊗U_B)⊗U_C) = V(q⊗(r⊗s), P⊗(U_B⊗U_C))
    have hkey := hcov (Equiv.prodAssoc A B C) (Equiv.prodAssoc A PUnit.{u+1} PUnit.{u+1})
      (prodDist (prodDist q r) s)
      (prodChannel (leftProductLiftChannel (B := B) P) (Channel.uninformativeChannelU C))
    rw [relabelDist_prodAssoc,
      show Relabeling.relabelChannel (Equiv.prodAssoc A B C) (Equiv.prodAssoc A PUnit.{u+1} PUnit.{u+1})
          (prodChannel (leftProductLiftChannel (B := B) P) (Channel.uninformativeChannelU C)) =
        prodChannel P (prodChannel (Channel.uninformativeChannelU B) (Channel.uninformativeChannelU C)) from by
        rw [show (prodChannel (leftProductLiftChannel (B := B) P) (Channel.uninformativeChannelU C)) =
          prodChannel (prodChannel P (Channel.uninformativeChannelU B)) (Channel.uninformativeChannelU C) from rfl,
          relabelChannel_prodAssoc]] at hkey
    -- (ii) outcome collapse: V(q⊗(r⊗s), P⊗(U_B⊗U_C)) = V(q⊗(r⊗s), P⊗U_{B×C})
    have hcollapse := hcov (Equiv.refl (A × B × C))
      ((Equiv.refl A).prodCongr (Equiv.prodPUnit PUnit.{u+1}))
      (prodDist q (prodDist r s))
      (prodChannel P (prodChannel (Channel.uninformativeChannelU B) (Channel.uninformativeChannelU C)))
    rw [Relabeling.relabelDist_refl,
      show Relabeling.relabelChannel (Equiv.refl (A × B × C))
          ((Equiv.refl A).prodCongr (Equiv.prodPUnit PUnit.{u+1}))
          (prodChannel P (prodChannel (Channel.uninformativeChannelU B) (Channel.uninformativeChannelU C))) =
        prodChannel P (Channel.uninformativeChannelU (B × C)) from by
        ext x o
        obtain ⟨a, b, c⟩ := x
        obtain ⟨o1, o2⟩ := o
        simp [Relabeling.relabelChannel, prodChannel_apply_pair, Channel.uninformativeChannelU,
          Equiv.prodPUnit]] at hcollapse
    rw [← hkey, hcollapse]
  -- assemble
  rw [hOuter, hInner] at hassoc
  rw [hLHS] at hassoc
  -- hassoc : productLiftScale (q⊗r) s · (productLiftScale q r · V(q,P)) = productLiftScale q (r⊗s) · V(q,P)
  have := mul_right_cancel₀ hVqP_ne
    (show productLiftScale hfaces hhm hax (prodDist q r) s * productLiftScale hfaces hhm hax q r *
        Vrep.V q (experimentOfChannel P) =
      productLiftScale hfaces hhm hax q (prodDist r s) * Vrep.V q (experimentOfChannel P) from by
      rw [mul_assoc]; linarith [hassoc])
  linarith [this]


/-- **WLOG certificate for `singleton_interaction` (left factor).**  When the first
factor `A` is a subsingleton, `V(q,P) = 0`, so the bilinear interaction term
`κ · V(q,P) · V(r,R)` vanishes for *any* coefficient `κ`.  Hence the product value
is independent of the interaction coefficient on a subsingleton factor: normalizing
it to the reference `κ` (as `singleton_interaction` does) changes no observable
value and is therefore without loss of generality. -/
theorem interaction_term_indep_of_coeff_subsingleton_left
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport)
    (hA : Subsingleton A) (P : Channel A O) (R : Channel B Y)
    (κ κ' : ℝ) :
    κ * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) *
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) =
      κ' * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) *
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [V_channel_eq_zero_of_subsingleton F hfaces.branch_result.branch_agg.value_rep q hq P]
  ring

/-- **WLOG certificate for `singleton_interaction` (right factor).**  Symmetric:
`V(r,R) = 0` when `B` is a subsingleton. -/
theorem interaction_term_indep_of_coeff_subsingleton_right
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hr : r.FullSupport)
    (hB : Subsingleton B) (P : Channel A O) (R : Channel B Y)
    (κ κ' : ℝ) :
    κ * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) *
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) =
      κ' * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) *
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [V_channel_eq_zero_of_subsingleton F hfaces.branch_result.branch_agg.value_rep r hr R]
  ring


/-- Support of `pure a ⊗ r` ≃ support of `r` (the first coordinate is pinned to `a`). -/
def pureProdSupportEquiv {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (a : A) (r : Dist B) :
    supportSubtype (prodDist (Dist.pure a) r) ≃ supportSubtype r where
  toFun x := ⟨x.1.2, by
    rcases x with ⟨⟨a', b⟩, hab⟩
    rw [prodDist_apply_pair] at hab
    -- hab : pure a a' * r b > 0 ; so r b > 0
    by_contra hb
    have hb0 : r b = 0 := le_antisymm (le_of_not_gt hb) (r.nonneg b)
    rw [hb0, mul_zero] at hab
    exact lt_irrefl 0 hab⟩
  invFun b := ⟨(a, b.1), by
    rw [prodDist_apply_pair, Dist.pure_apply_self]; simpa using b.2⟩
  left_inv x := by
    rcases x with ⟨⟨a', b⟩, hab⟩
    apply Subtype.ext
    rw [prodDist_apply_pair] at hab
    have ha' : a' = a := by
      by_contra h
      rw [Dist.pure_apply_ne _ _ h, zero_mul] at hab
      exact lt_irrefl 0 hab
    subst ha'; rfl
  right_inv b := by apply Subtype.ext; rfl

-- restrictToSupport of pure a ⊗ r  =  relabel (E.symm) of (r|supp)
theorem restrict_pureProd {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (a : A) (r : Dist B) :
    (prodDist (Dist.pure a) r).restrictToSupport =
      Relabeling.relabelDist (pureProdSupportEquiv a r).symm r.restrictToSupport := by
  ext x
  rw [Dist.restrictToSupport_apply, Relabeling.relabelDist_apply, Dist.restrictToSupport_apply]
  rcases x with ⟨⟨a', b⟩, hab⟩
  rw [prodDist_apply_pair] at hab ⊢
  have ha' : a' = a := by
    by_contra h
    rw [Dist.pure_apply_ne _ _ h, zero_mul] at hab
    exact lt_irrefl 0 hab
  subst ha'
  rw [Dist.pure_apply_self, one_mul]
  congr 1

theorem restrictChannel_pureProd_secondReveal {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (a : A) (r : Dist B) :
    Channel.restrictToSupport (productSecondRevealChannel (A := A) (B := B)) (prodDist (Dist.pure a) r) =
      Relabeling.relabelChannel (pureProdSupportEquiv a r).symm (Equiv.refl B)
        (Channel.restrictToSupport (Channel.idChannel : Channel B B) r) := by
  ext x y
  rcases x with ⟨⟨a', b⟩, hab⟩
  simp only [Channel.restrictToSupport, productSecondRevealChannel,
    Relabeling.relabelChannel_apply, Equiv.symm_symm, Channel.idChannel]
  rfl

/-- **Bottom lemma (first coordinate face value), QA-free.**  Appending a degenerate
point-mass first coordinate does not change the full-revelation value:
`V(pure a ⊗ r, secondReveal) = V(r, id_B)`.  Proof: support-face value transport on
both sides (support of `pure a ⊗ r` is `{a}×supp r`), bridged by relabel-covariance
along `pureProdSupportEquiv`. -/
theorem first_coordinate_face_value_of_HM
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    (hsupp : ∀ (F' : PrefFamily.{u}) (hax : TraceAxioms F') (hV' : PosteriorValueRepresentation F')
      {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV'.V r (experimentOfChannel P) =
        hV'.V r.restrictToSupport (experimentOfChannel (Channel.restrictToSupport P r)))
    (hcov : ∀ {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B] [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O),
        hV.V (Relabeling.relabelDist eA q) (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hV.V q (experimentOfChannel P))
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (a : A) (r : Dist B) :
    hV.V (prodDist (Dist.pure a) r) (experimentOfChannel (productSecondRevealChannel (A := A) (B := B))) =
      hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  classical
  haveI : Nonempty (supportSubtype (prodDist (Dist.pure a) r)) :=
    ⟨(pureProdSupportEquiv a r).symm (Classical.arbitrary (supportSubtype r))⟩
  -- LHS support-face transport
  rw [hsupp F hax hV (prodDist (Dist.pure a) r) (productSecondRevealChannel (A := A) (B := B))]
  -- rewrite restricted dist + channel
  rw [restrict_pureProd a r, restrictChannel_pureProd_secondReveal a r]
  -- covariance: V(relabel E.symm (r|supp), relabelChannel E.symm refl (id|supp)) = V(r|supp, id|supp)
  rw [hcov (pureProdSupportEquiv a r).symm (Equiv.refl B) r.restrictToSupport
    (Channel.restrictToSupport (Channel.idChannel : Channel B B) r)]
  -- RHS support-face transport (backwards)
  rw [hsupp F hax hV r (Channel.idChannel : Channel B B)]

/-- **The chain scale of `pure a ⊗ r` is `1`** (it is a boundary prior — not full
support — so `branchPathCoeff` returns its `1` default).  Together with the value
lemma this shows the raw `scale` does NOT satisfy `scale(pure a⊗r)=scale r` (that is
an irreducible coherent-gauge normalization, false pre-gauge). -/
theorem scale_pure_prod_eq_one
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (a : A) (r : Dist B) (hAnd : ∃ x y : A, x ≠ y) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (prodDist (Dist.pure a) r) = 1 := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
  -- scale = branchCoeff · uniform = branchCoeffFromTangentRepParts, uniform full support ⟹ branchPathCoeff
  show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff (prodDist (Dist.pure a) r) (Dist.uniform (A := A × B)) = 1
  rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
    ).branch_agg.branchCoeff (prodDist (Dist.pure a) r) (Dist.uniform (A := A × B)) =
    branchCoeffFromTangentRepParts hpath
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
      hfaith.singleton_scale (prodDist (Dist.pure a) r) (Dist.uniform (A := A × B)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  -- now branchPathCoeff (pure a⊗r) uniform ; pure a⊗r NOT full support ⟹ 1
  have hnotfull : ¬ (prodDist (Dist.pure a) r).FullSupport := by
    obtain ⟨x, y, hxy⟩ := hAnd
    intro hfs
    -- pure a assigns 0 to some element ≠ a
    have : (prodDist (Dist.pure a) r) (if a = x then (y, Classical.arbitrary B) else (x, Classical.arbitrary B)) > 0 := hfs _
    rw [prodDist_apply_pair] at this
    by_cases hax2 : a = x
    · simp only [if_pos hax2] at this
      rw [Dist.pure_apply_ne _ _ (by rw [← hax2] at hxy; exact fun h => hxy h.symm), zero_mul] at this
      exact lt_irrefl 0 this
    · simp only [if_neg hax2] at this
      rw [Dist.pure_apply_ne _ _ (fun h => hax2 h.symm), zero_mul] at this
      exact lt_irrefl 0 this
  show hpath.branchPathCoeff (prodDist (Dist.pure a) r) (Dist.uniform (A := A × B)) = 1
  simp only [hpath, branchPathTangentScalarStructure_of_faithfulAssumptions,
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
  rw [dif_neg hnotfull]


-- The faithful-structure coordinate-face value: V(pure a⊗r, secondReveal) = V(r, id).
-- Instantiate first_coordinate_face_value_of_HM with the faithful V + branch.support_face + hm_covariance.
theorem faithful_first_coord_face_value
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (hcov : FinalHMRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (a : A) (r : Dist B) :
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
        (prodDist (Dist.pure a) r) (experimentOfChannel (productSecondRevealChannel (A := A) (B := B))) =
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  apply first_coordinate_face_value_of_HM
    (hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax)
  · -- support_face_value_transport (branch.support_face clause holds for any hV)
    intro F' hax' hV' A' O' _ _ _ _ _ r' _ P'
    exact hbranchConv.support_face.support_face_value_transport F' hax' hV' r' P'
  · -- covariance
    intro A' B' O' Y' _ _ _ _ _ _ _ _ _ _ eA eO q' P'
    exact hcov.V_relabel_eq hax eA eO q' P'
  · exact hax

/-- **Governing equation for the product scale (QA-free).**  From the faithful
normalized chain rule at `q⊗r` with first stage = first-coordinate reveal (posterior
`pure a ⊗ r`, scale `1`, continuation value `V(r,id)`):
`V(q⊗r,id)/scale(q⊗r) = V(q⊗r,firstReveal)/scale(q⊗r) + V(r,id)`.  Equivalently
`fullRev(q⊗r) = V(q⊗r,firstReveal) + scale(q⊗r)·V(r,id)`. -/
theorem product_scale_governing_left
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (hcov : FinalHMRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ∃ x y : A, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    branchNormalizedValue hcnr.chain (prodDist q r) (Channel.idChannel : Channel (A × B) (A × B)) =
      branchNormalizedValue hcnr.chain (prodDist q r) (productFirstRevealChannel (A := A) (B := B)) +
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  classical
  intro hcnr
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  -- chain rule at q⊗r
  have hchain := hcnr.normalizedChainRule (prodDist q r) hprod
    (productFirstRevealChannel (A := A) (B := B))
    (fun _ => productSecondRevealChannel (A := A) (B := B))
  rw [productFirstThenSecondReveal_eq_idChannel] at hchain
  rw [hchain]
  congr 1
  -- the sum: Σ_a marginal(a)·nv(posterior a, secondReveal) = V(r,id)
  rw [outcomeMarginal_productFirstRevealChannel_prodDist]
  -- each posterior = pure a ⊗ r ; nv = V(pure a⊗r, secondReveal)/scale(pure a⊗r) = V(r,id)/1
  have hterm : ∀ a : A, branchNormalizedValue hcnr.chain
      (Channel.posterior (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) a)
      (productSecondRevealChannel (A := A) (B := B)) =
      (if 0 < q a then hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) else
        branchNormalizedValue hcnr.chain
          (Channel.posterior (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) a)
          (productSecondRevealChannel (A := A) (B := B))) := by
    intro a
    by_cases ha : 0 < q a
    · rw [if_pos ha]
      rw [posterior_productFirstRevealChannel_prodDist_of_pos q r a ha]
      show hcnr.chain.branch_agg.value_rep.V (prodDist (Dist.pure a) r)
          (experimentOfChannel (productSecondRevealChannel (A := A) (B := B))) /
          hcnr.chain.scale (prodDist (Dist.pure a) r) = _
      rw [show hcnr.chain.branch_agg.value_rep.V = hV.V from rfl]
      rw [faithful_first_coord_face_value hhm hbranchConv hax hcov a r]
      rw [show hcnr.chain.scale (prodDist (Dist.pure a) r) = 1 from
        scale_pure_prod_eq_one hhm hbranchConv hax a r hAnd]
      rw [div_one]
    · rw [if_neg ha]
  -- Σ_a q a · nv(posterior a, secondReveal) = Σ_a q a · V(r,id) = V(r,id)
  have hsum : (∑ a : A, q a * branchNormalizedValue hcnr.chain
      (Channel.posterior (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) a)
      (productSecondRevealChannel (A := A) (B := B))) =
      hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    rw [show (∑ a : A, q a * branchNormalizedValue hcnr.chain
        (Channel.posterior (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) a)
        (productSecondRevealChannel (A := A) (B := B))) =
        ∑ a : A, q a * hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) from by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : 0 < q a
      · rw [hterm a, if_pos ha]
      · have ha0 : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
        rw [ha0, zero_mul, zero_mul]]
    rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  exact hsum


/-- Support of `q ⊗ pure b` ≃ support of `q`. -/
def prodPureSupportEquiv {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (q : Dist A) (b : B) :
    supportSubtype (prodDist q (Dist.pure b)) ≃ supportSubtype q where
  toFun x := ⟨x.1.1, by
    rcases x with ⟨⟨a, b'⟩, hab⟩
    rw [prodDist_apply_pair] at hab
    by_contra ha
    have ha0 : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
    rw [ha0, zero_mul] at hab; exact lt_irrefl 0 hab⟩
  invFun a := ⟨(a.1, b), by
    rw [prodDist_apply_pair, Dist.pure_apply_self, mul_one]; exact a.2⟩
  left_inv x := by
    rcases x with ⟨⟨a, b'⟩, hab⟩
    apply Subtype.ext
    rw [prodDist_apply_pair] at hab
    have hb' : b' = b := by
      by_contra h
      rw [Dist.pure_apply_ne _ _ h, mul_zero] at hab
      exact lt_irrefl 0 hab
    subst hb'; rfl
  right_inv a := by apply Subtype.ext; rfl

theorem restrict_prodPure {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (q : Dist A) (b : B) :
    (prodDist q (Dist.pure b)).restrictToSupport =
      Relabeling.relabelDist (prodPureSupportEquiv q b).symm q.restrictToSupport := by
  ext x
  rw [Dist.restrictToSupport_apply, Relabeling.relabelDist_apply, Dist.restrictToSupport_apply]
  rcases x with ⟨⟨a, b'⟩, hab⟩
  rw [prodDist_apply_pair] at hab ⊢
  have hb' : b' = b := by
    by_contra h
    rw [Dist.pure_apply_ne _ _ h, mul_zero] at hab
    exact lt_irrefl 0 hab
  subst hb'
  rw [Dist.pure_apply_self, mul_one]
  congr 1

theorem restrictChannel_prodPure_firstReveal {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (b : B) :
    Channel.restrictToSupport (productFirstRevealChannel (A := A) (B := B)) (prodDist q (Dist.pure b)) =
      Relabeling.relabelChannel (prodPureSupportEquiv q b).symm (Equiv.refl A)
        (Channel.restrictToSupport (Channel.idChannel : Channel A A) q) := by
  ext x y
  rcases x with ⟨⟨a, b'⟩, hab⟩
  simp only [Channel.restrictToSupport, productFirstRevealChannel,
    Relabeling.relabelChannel_apply, Equiv.symm_symm, Channel.idChannel]
  rfl


theorem second_coordinate_face_value_of_HM
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    (hsupp : ∀ (F' : PrefFamily.{u}) (hax : TraceAxioms F') (hV' : PosteriorValueRepresentation F')
      {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV'.V r (experimentOfChannel P) =
        hV'.V r.restrictToSupport (experimentOfChannel (Channel.restrictToSupport P r)))
    (hcov : ∀ {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B] [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O),
        hV.V (Relabeling.relabelDist eA q) (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hV.V q (experimentOfChannel P))
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (b : B) :
    hV.V (prodDist q (Dist.pure b)) (experimentOfChannel (productFirstRevealChannel (A := A) (B := B))) =
      hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) := by
  classical
  haveI : Nonempty (supportSubtype (prodDist q (Dist.pure b))) :=
    ⟨(prodPureSupportEquiv q b).symm (Classical.arbitrary (supportSubtype q))⟩
  rw [hsupp F hax hV (prodDist q (Dist.pure b)) (productFirstRevealChannel (A := A) (B := B))]
  rw [restrict_prodPure q b, restrictChannel_prodPure_firstReveal q b]
  rw [hcov (prodPureSupportEquiv q b).symm (Equiv.refl A) q.restrictToSupport
    (Channel.restrictToSupport (Channel.idChannel : Channel A A) q)]
  rw [hsupp F hax hV q (Channel.idChannel : Channel A A)]


theorem scale_prod_pure_eq_one
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (q : Dist A) (b : B) (hBnd : ∃ x y : B, x ≠ y) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (prodDist q (Dist.pure b)) = 1 := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hpath := branchPathTangentScalarStructure_of_faithfulAssumptions hfaith F hax hV
  show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).branch_agg.branchCoeff (prodDist q (Dist.pure b)) (Dist.uniform (A := A × B)) = 1
  rw [show (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
    ).branch_agg.branchCoeff (prodDist q (Dist.pure b)) (Dist.uniform (A := A × B)) =
    branchCoeffFromTangentRepParts hpath
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
      hfaith.singleton_scale (prodDist q (Dist.pure b)) (Dist.uniform (A := A × B)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  have hnotfull : ¬ (prodDist q (Dist.pure b)).FullSupport := by
    obtain ⟨x, y, hxy⟩ := hBnd
    intro hfs
    have := hfs (Classical.arbitrary A, if b = x then y else x)
    rw [prodDist_apply_pair] at this
    by_cases hbx : b = x
    · simp only [if_pos hbx] at this
      rw [Dist.pure_apply_ne _ _ (by rw [← hbx] at hxy; exact fun h => hxy h.symm), mul_zero] at this
      exact lt_irrefl 0 this
    · simp only [if_neg hbx] at this
      rw [Dist.pure_apply_ne _ _ (fun h => hbx h.symm), mul_zero] at this
      exact lt_irrefl 0 this
  show hpath.branchPathCoeff (prodDist q (Dist.pure b)) (Dist.uniform (A := A × B)) = 1
  simp only [hpath, branchPathTangentScalarStructure_of_faithfulAssumptions,
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
  rw [dif_neg hnotfull]


theorem product_scale_governing_right
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (hcov : FinalHMRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hBnd : ∃ x y : B, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    branchNormalizedValue hcnr.chain (prodDist q r)
        (productSecondRevealChannel (A := A) (B := B) ▷
          (fun _ => productFirstRevealChannel (A := A) (B := B))) =
      branchNormalizedValue hcnr.chain (prodDist q r) (productSecondRevealChannel (A := A) (B := B)) +
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) := by
  classical
  intro hcnr
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hchain := hcnr.normalizedChainRule (prodDist q r) hprod
    (productSecondRevealChannel (A := A) (B := B))
    (fun _ => productFirstRevealChannel (A := A) (B := B))
  rw [hchain]
  congr 1
  rw [outcomeMarginal_productSecondRevealChannel_prodDist]
  have hterm : ∀ b : B, branchNormalizedValue hcnr.chain
      (Channel.posterior (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) b)
      (productFirstRevealChannel (A := A) (B := B)) =
      (if 0 < r b then hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) else
        branchNormalizedValue hcnr.chain
          (Channel.posterior (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) b)
          (productFirstRevealChannel (A := A) (B := B))) := by
    intro b
    by_cases hb : 0 < r b
    · rw [if_pos hb, posterior_productSecondRevealChannel_prodDist_of_pos q r b hb]
      show hcnr.chain.branch_agg.value_rep.V (prodDist q (Dist.pure b))
          (experimentOfChannel (productFirstRevealChannel (A := A) (B := B))) /
          hcnr.chain.scale (prodDist q (Dist.pure b)) = _
      rw [show hcnr.chain.branch_agg.value_rep.V = hV.V from rfl]
      rw [second_coordinate_face_value_of_HM (hV := hV)
        (fun F' hax' hV' A' O' _ _ _ _ _ r' _ P' =>
          hbranchConv.support_face.support_face_value_transport F' hax' hV' r' P')
        (fun {A' B' O' Y'} _ _ _ _ _ _ _ _ _ _ eA eO q' P' => hcov.V_relabel_eq hax eA eO q' P')
        hax q b]
      rw [show hcnr.chain.scale (prodDist q (Dist.pure b)) = 1 from
        scale_prod_pure_eq_one hhm hbranchConv hax q b hBnd, div_one]
    · rw [if_neg hb]
  rw [show (∑ b : B, r b * branchNormalizedValue hcnr.chain
      (Channel.posterior (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) b)
      (productFirstRevealChannel (A := A) (B := B))) =
      ∑ b : B, r b * hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) from by
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : 0 < r b
    · rw [hterm b, if_pos hb]
    · have hb0 : r b = 0 := le_antisymm (le_of_not_gt hb) (r.nonneg b)
      rw [hb0, zero_mul, zero_mul]]
  rw [← Finset.sum_mul, r.sum_eq_one, one_mul]


/-- **Cleared product-scale identity (left), QA-free.**  Clearing the `scale(q⊗r)`
denominator in `product_scale_governing_left`:
`V(q⊗r, id) = V(q⊗r, firstReveal) + scale(q⊗r)·V(r, id)`. -/
theorem product_scale_cleared_left
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (hcov : FinalHMRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ∃ x y : A, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
        (experimentOfChannel (Channel.idChannel : Channel (A × B) (A × B))) =
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
          (experimentOfChannel (productFirstRevealChannel (A := A) (B := B))) +
        hcnr.scale_factorization.scale (prodDist q r) *
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  intro hcnr
  have hgov := product_scale_governing_left hhm hbranchConv hax hcov q r hq hr hAnd
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set s := hcnr.scale_factorization.scale (prodDist q r) with hsdef
  have hspos : 0 < s := faithful_scale_pos hhm hbranchConv hax (prodDist q r)
  have hsne : s ≠ 0 := ne_of_gt hspos
  -- branchNormalizedValue hcnr.chain (q⊗r) E = V(q⊗r,E)/s
  -- hgov : V(id)/s = V(firstReveal)/s + V(r,id)  (branchNormalizedValue = V/s definitionally)
  have hgov' : hV.V (prodDist q r) (experimentOfChannel (Channel.idChannel : Channel (A × B) (A × B))) / s =
      hV.V (prodDist q r) (experimentOfChannel (productFirstRevealChannel (A := A) (B := B))) / s +
        hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := hgov
  have hkey := hgov'
  field_simp at hkey
  -- hkey : V(id) = V(firstReveal) + V(r,id)·s   (some arrangement)
  linarith [hkey]



/-- **Cleared product-scale identity (right), QA-free.** -/
theorem product_scale_cleared_right
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (hcov : FinalHMRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hBnd : ∃ x y : B, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
        (experimentOfChannel (productSecondRevealChannel (A := A) (B := B) ▷
          (fun _ => productFirstRevealChannel (A := A) (B := B)))) =
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
          (experimentOfChannel (productSecondRevealChannel (A := A) (B := B))) +
        hcnr.scale_factorization.scale (prodDist q r) *
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
            (experimentOfChannel (Channel.idChannel : Channel A A)) := by
  intro hcnr
  have hgov := product_scale_governing_right hhm hbranchConv hax hcov q r hq hr hBnd
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set s := hcnr.scale_factorization.scale (prodDist q r) with hsdef
  have hspos : 0 < s := faithful_scale_pos hhm hbranchConv hax (prodDist q r)
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hgov' : hV.V (prodDist q r)
        (experimentOfChannel (productSecondRevealChannel (A := A) (B := B) ▷
          (fun _ => productFirstRevealChannel (A := A) (B := B)))) / s =
      hV.V (prodDist q r) (experimentOfChannel (productSecondRevealChannel (A := A) (B := B))) / s +
        hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) := hgov
  have hkey := hgov'
  field_simp at hkey
  linarith [hkey]


/-- **Formal obstruction (SC): the product scale is pinned by joint value data.**
Solving the cleared left identity,
`scale(q⊗r) = (V(q⊗r,id) − V(q⊗r,firstReveal)) / V(r,id)`  (for `V(r,id) ≠ 0`).

This is the formal reason `current_product_gauge` cannot be dropped by a coherent
single-distribution gauge: the product scale `scale(q⊗r)` is determined by the
*joint* value `V(q⊗r,id)` (equivalently the product coefficients depend on `q⊗r`),
which no gauge `g(q⊗r)/g(q)` factoring through single distributions can absorb.
Normalizing it therefore requires the joint (product-quasi-additivity) data, i.e. it
is an irreducible gauge choice, not a raw-axiom consequence. -/
theorem product_scale_pinned_by_joint_value
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchConv : FinalFaithfulBranchConventions hhm)
    (hax : TraceAxioms F) (hcov : FinalHMRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ∃ x y : A, x ≠ y)
    (hVr : (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
      (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm hbranchConv)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    hcnr.scale_factorization.scale (prodDist q r) =
      ((posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
          (experimentOfChannel (Channel.idChannel : Channel (A × B) (A × B))) -
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
          (experimentOfChannel (productFirstRevealChannel (A := A) (B := B)))) /
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  intro hcnr
  have hcl := product_scale_cleared_left hhm hbranchConv hax hcov q r hq hr hAnd
  -- hcl : V(id) = V(firstReveal) + s·V(r,id)
  rw [eq_div_iff hVr]
  linarith [hcl]

section FaceScaleProductCocycle
variable {F : PrefFamily.{u}} {hfaces : CoherentRelabelingFaceScalesStructure F}

theorem fs_bilinear_right_uninf
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) (P : Channel A O) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU B))) =
      hpair.leftCoeff hax q r *
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) := by
  rw [hpair.product_pair_bilinear hax q r hq hr P (Channel.uninformativeChannelU B)]
  rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr]; ring

theorem fs_bilinear_left_uninf
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) (R : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R)) =
      hpair.rightCoeff hax q r *
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear hax q r hq hr (Channel.uninformativeChannelU A) R]
  rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq]; ring

theorem fs_coeff_assoc_A
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hs : s.FullSupport)
    (hAnd : ¬ Subsingleton A) :
    hpair.leftCoeff hax (prodDist q r) s * hpair.leftCoeff hax q r =
      hpair.leftCoeff hax q (prodDist r s) := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hAnd
  have hli := fs_bilinear_right_uninf hpair hax q r hq hr (Channel.idChannel : Channel A A)
  have hrz : hfaces.branch_result.branch_agg.value_rep.V (prodDist r s)
      (experimentOfChannel (prodChannel (Channel.uninformativeChannelU B)
        (Channel.uninformativeChannelU C))) = 0 :=
    V_prod_uninformative_uninformative_eq_zero F hfaces.branch_result.branch_agg.value_rep r s hr hs
  have hval := htriple.triple_value_assoc hax q r s hq hr hs
    (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)
    (Channel.uninformativeChannelU C)
  rw [hpair.product_pair_bilinear hax (prodDist q r) s hqr hs
      (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear hax q (prodDist r s) hq hrs
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.uninformativeChannelU B) (Channel.uninformativeChannelU C))] at hval
  rw [hli, hfaces.branch_result.branch_agg.value_rep.zero_normalized s hs, hrz] at hval
  have hval2 : hpair.leftCoeff hax (prodDist q r) s * hpair.leftCoeff hax q r *
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel (Channel.idChannel : Channel A A)) =
      hpair.leftCoeff hax q (prodDist r s) *
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel (Channel.idChannel : Channel A A)) := by
    nlinarith [hval]
  exact mul_right_cancel₀ hVnz hval2


theorem fs_coeff_assoc_mixed
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hs : s.FullSupport)
    (hBnd : ¬ Subsingleton B) :
    hpair.leftCoeff hax (prodDist q r) s * hpair.rightCoeff hax q r =
      hpair.rightCoeff hax q (prodDist r s) * hpair.leftCoeff hax r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V r
      (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hBnd
  have hli := fs_bilinear_left_uninf hpair hax q r hq hr (Channel.idChannel : Channel B B)
  have hri := fs_bilinear_right_uninf hpair hax r s hr hs (Channel.idChannel : Channel B B)
  have hval := htriple.triple_value_assoc hax q r s hq hr hs
    (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B)
    (Channel.uninformativeChannelU C)
  rw [hpair.product_pair_bilinear hax (prodDist q r) s hqr hs
      (prodChannel (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear hax q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.idChannel : Channel B B) (Channel.uninformativeChannelU C))] at hval
  rw [hli, hri, hfaces.branch_result.branch_agg.value_rep.zero_normalized s hs,
      hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq] at hval
  have hval2 : hpair.leftCoeff hax (prodDist q r) s * hpair.rightCoeff hax q r *
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel (Channel.idChannel : Channel B B)) =
      (hpair.rightCoeff hax q (prodDist r s) * hpair.leftCoeff hax r s) *
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    nlinarith [hval]
  exact mul_right_cancel₀ hVnz hval2

theorem fs_coeff_assoc_B
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hs : s.FullSupport)
    (hCnd : ¬ Subsingleton C) :
    hpair.rightCoeff hax (prodDist q r) s =
      hpair.rightCoeff hax q (prodDist r s) * hpair.rightCoeff hax r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V s
      (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hCnd
  have hlz : hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B))) = 0 :=
    V_prod_uninformative_uninformative_eq_zero F hfaces.branch_result.branch_agg.value_rep q r hq hr
  have hri := fs_bilinear_left_uninf hpair hax r s hr hs (Channel.idChannel : Channel C C)
  have hval := htriple.triple_value_assoc hax q r s hq hr hs
    (Channel.uninformativeChannelU A) (Channel.uninformativeChannelU B)
    (Channel.idChannel : Channel C C)
  rw [hpair.product_pair_bilinear hax (prodDist q r) s hqr hs
      (prodChannel (Channel.uninformativeChannelU A) (Channel.uninformativeChannelU B))
      (Channel.idChannel : Channel C C)] at hval
  rw [hpair.product_pair_bilinear hax q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.uninformativeChannelU B) (Channel.idChannel : Channel C C))] at hval
  rw [hlz, hri, hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq] at hval
  have hval2 : hpair.rightCoeff hax (prodDist q r) s *
        hfaces.branch_result.branch_agg.value_rep.V s (experimentOfChannel (Channel.idChannel : Channel C C)) =
      (hpair.rightCoeff hax q (prodDist r s) * hpair.rightCoeff hax r s) *
        hfaces.branch_result.branch_agg.value_rep.V s (experimentOfChannel (Channel.idChannel : Channel C C)) := by
    nlinarith [hval]
  exact mul_right_cancel₀ hVnz hval2


/-- Face-scale swap: `A_{q,r} = B_{r,q}` (nondegenerate first coordinate). -/
theorem fs_leftCoeff_eq_swapped_rightCoeff
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ¬ Subsingleton A) :
    hpair.leftCoeff hax q r = hpair.rightCoeff hax r q := by
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hAnd
  have hval := faceScaleProduct_value_swap_eq_of_selectedRelabeling hsel hax
    q r (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)
  rw [fs_bilinear_right_uninf hpair hax q r hq hr (Channel.idChannel : Channel A A)] at hval
  rw [fs_bilinear_left_uninf hpair hax r q hr hq (Channel.idChannel : Channel A A)] at hval
  exact mul_right_cancel₀ hVnz (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Face-scale swap: `B_{q,r} = A_{r,q}` (nondegenerate second coordinate). -/
theorem fs_rightCoeff_eq_swapped_leftCoeff
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hBnd : ¬ Subsingleton B) :
    hpair.rightCoeff hax q r = hpair.leftCoeff hax r q := by
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V r
      (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hBnd
  have hval := faceScaleProduct_value_swap_eq_of_selectedRelabeling hsel hax
    q r (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B)
  rw [fs_bilinear_left_uninf hpair hax q r hq hr (Channel.idChannel : Channel B B)] at hval
  rw [fs_bilinear_right_uninf hpair hax r q hr hq (Channel.idChannel : Channel B B)] at hval
  exact mul_right_cancel₀ hVnz (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Coboundary gauge value: `φ(x) := ρ(q₀, x) = B(q₀,x)/A(q₀,x)` for the fixed
2-point reference prior `q₀`. -/
noncomputable def cobGauge
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : ℝ :=
  hpair.rightCoeff hax faceScaleInteractionReferencePrior x /
    hpair.leftCoeff hax faceScaleInteractionReferencePrior x

theorem cobGauge_pos
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) (hx : x.FullSupport) : 0 < cobGauge hpair hax x := by
  unfold cobGauge
  exact div_pos
    (hpair.rightCoeff_pos hax faceScaleInteractionReferencePrior x
      faceScaleInteractionReferencePrior_fullSupport hx)
    (hpair.leftCoeff_pos hax faceScaleInteractionReferencePrior x
      faceScaleInteractionReferencePrior_fullSupport hx)


/-- **Coboundary identity.**  `A(r,s) = φ(r)/φ(r⊗s)` where `φ := cobGauge`.  This is
the cocycle-integrability that makes the linear coefficient a coboundary; it is the
crux of the product-gauge normalization.  Proof: apply `coeff_assoc_A` and
`coeff_assoc_mixed` with first coordinate `= q₀` (reference), then solve. -/
theorem cobGauge_coboundary
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {B C : Type u}
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (r : Dist B) (s : Dist C) (hr : r.FullSupport) (hs : s.FullSupport) (hrnd : ¬ Subsingleton B) :
    hpair.leftCoeff hax r s =
      cobGauge hpair hax r / cobGauge hpair hax (prodDist r s) := by
  set q₀ := faceScaleInteractionReferencePrior with hq₀def
  have hq₀ : q₀.FullSupport := faceScaleInteractionReferencePrior_fullSupport
  have hq₀nd : ¬ Subsingleton faceScaleInteractionReferenceType :=
    faceScaleInteractionReference_not_subsingleton
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
  -- positivity of the four coefficients we divide by
  have hAqr : 0 < hpair.leftCoeff hax q₀ r := hpair.leftCoeff_pos hax q₀ r hq₀ hr
  have hArs : 0 < hpair.leftCoeff hax q₀ (prodDist r s) := hpair.leftCoeff_pos hax q₀ (prodDist r s) hq₀ hrs
  have hBqr : 0 < hpair.rightCoeff hax q₀ r := hpair.rightCoeff_pos hax q₀ r hq₀ hr
  have hBrs : 0 < hpair.rightCoeff hax q₀ (prodDist r s) := hpair.rightCoeff_pos hax q₀ (prodDist r s) hq₀ hrs
  -- cocycle (ii): A(q₀⊗r,s)·A(q₀,r)=A(q₀,r⊗s)
  have hii := fs_coeff_assoc_A hpair htriple hax q₀ r s hq₀ hr hs hq₀nd
  -- cocycle (i, mixed): A(q₀⊗r,s)·B(q₀,r)=B(q₀,r⊗s)·A(r,s)
  have hi := fs_coeff_assoc_mixed hpair htriple hax q₀ r s hq₀ hr hs hrnd
  -- Let X:=A(q₀⊗r,s). hii: X·A(q₀,r)=A(q₀,r⊗s); hi: X·B(q₀,r)=B(q₀,r⊗s)·A(r,s).
  -- ⟹ X=A(q₀,r⊗s)/A(q₀,r), then A(r,s)=X·B(q₀,r)/B(q₀,r⊗s)=[A(q₀,r⊗s)·B(q₀,r)]/[A(q₀,r)·B(q₀,r⊗s)].
  -- φ(r)/φ(r⊗s) = [B(q₀,r)/A(q₀,r)]/[B(q₀,r⊗s)/A(q₀,r⊗s)] = [B(q₀,r)·A(q₀,r⊗s)]/[A(q₀,r)·B(q₀,r⊗s)]. Same.
  -- First derive the pure cross-multiplied identity, then convert to the division form.
  have hAqr' : hpair.leftCoeff hax q₀ r ≠ 0 := ne_of_gt hAqr
  have hArs' : hpair.leftCoeff hax q₀ (prodDist r s) ≠ 0 := ne_of_gt hArs
  have hBrs' : hpair.rightCoeff hax q₀ (prodDist r s) ≠ 0 := ne_of_gt hBrs
  -- cross-multiplied target: A(r,s)·A(q₀,r)·B(q₀,r⊗s) = B(q₀,r)·A(q₀,r⊗s)
  have hcross : hpair.leftCoeff hax r s * hpair.leftCoeff hax q₀ r *
      hpair.rightCoeff hax q₀ (prodDist r s) =
      hpair.rightCoeff hax q₀ r * hpair.leftCoeff hax q₀ (prodDist r s) := by
    nlinarith [hii, hi, hAqr, hArs, hBqr, hBrs]
  -- Prove the division identity by rewriting both cobGauge's and clearing denominators manually.
  have hkey : hpair.leftCoeff hax r s =
      (hpair.rightCoeff hax q₀ r / hpair.leftCoeff hax q₀ r) /
        (hpair.rightCoeff hax q₀ (prodDist r s) / hpair.leftCoeff hax q₀ (prodDist r s)) := by
    rw [div_div_div_comm, div_div_div_comm]
    rw [eq_div_iff (by positivity)]
    -- goal: A(r,s) · (A(q₀,r⊗s)·A(q₀,r)... ) — clear via field then linear_combination
    field_simp
    nlinarith [hcross, hAqr, hArs, hBqr, hBrs, mul_pos hAqr hBrs, mul_pos hArs hBqr]
  unfold cobGauge
  exact hkey

-- leftCoeff is relabel-invariant in the SECOND argument (via value formula + covariance).
theorem fs_leftCoeff_relabel_right
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B B' : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype B'] [DecidableEq B'] [Nonempty B']
    (q : Dist A) (r : Dist B) (e : B ≃ B') (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ¬ Subsingleton A) :
    hpair.leftCoeff hax q (Relabeling.relabelDist e r) = hpair.leftCoeff hax q r := by
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hAnd
  have hrq : (Relabeling.relabelDist e r).FullSupport := Relabeling.relabelDist_fullSupport e r hr
  -- V(q⊗(relabel e r), id_A ⊗ U_B') = leftCoeff q (relabel e r) · V(q,id)
  have h1 := fs_bilinear_right_uninf hpair hax q (Relabeling.relabelDist e r) hq hrq (Channel.idChannel : Channel A A)
  -- V(q⊗r, id_A ⊗ U_B) = leftCoeff q r · V(q,id)
  have h2 := fs_bilinear_right_uninf hpair hax q r hq hr (Channel.idChannel : Channel A A)
  -- The two LHS values are equal via covariance: relabel (refl_A × e) carries q⊗r to q⊗(relabel e r)
  -- and id_A ⊗ U_B to id_A ⊗ U_B'.
  have hcov : hfaces.branch_result.branch_agg.value_rep.V (prodDist q (Relabeling.relabelDist e r))
        (experimentOfChannel (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B'))) =
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B))) := by
    have hc := hsel.V_relabel_eq hax
      ((Equiv.refl A).prodCongr e) ((Equiv.refl A).prodCongr (Equiv.refl PUnit.{u+1}))
      (prodDist q r) (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B))
    rw [Relabeling.relabelDist_prodCongr, Relabeling.relabelChannel_prodCongr] at hc
    -- relabel refl q = q ; relabel e r ; relabel refl id = id ; relabel e-outcome U_B = U_B'
    rw [show Relabeling.relabelDist (Equiv.refl A) q = q from Relabeling.relabelDist_refl q] at hc
    rw [show Relabeling.relabelChannel (Equiv.refl A) (Equiv.refl A) (Channel.idChannel : Channel A A)
          = (Channel.idChannel : Channel A A) from by
        ext a o; simp [Relabeling.relabelChannel, Channel.idChannel]] at hc
    rw [show Relabeling.relabelChannel e (Equiv.refl PUnit.{u+1}) (Channel.uninformativeChannelU B)
          = (Channel.uninformativeChannelU B') from by
        ext b o; cases o; simp [Relabeling.relabelChannel, Channel.uninformativeChannelU]] at hc
    exact hc
  rw [h1, h2] at hcov
  exact mul_right_cancel₀ hVnz hcov

theorem relabelChannel_id_eq {B B' : Type u} [Fintype B] [DecidableEq B] [Fintype B'] [DecidableEq B'] (e : B ≃ B') :
    Relabeling.relabelChannel e e (Channel.idChannel : Channel B B) = (Channel.idChannel : Channel B' B') := by
  ext b o
  simp only [Relabeling.relabelChannel, Channel.idChannel, Relabeling.relabelDist_apply]
  simp only [Dist.pure_apply, e.symm.injective.eq_iff]

theorem fs_rightCoeff_relabel_right
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B B' : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype B'] [DecidableEq B'] [Nonempty B']
    (q : Dist A) (r : Dist B) (e : B ≃ B') (hq : q.FullSupport) (hr : r.FullSupport)
    (hBnd : ¬ Subsingleton B) :
    hpair.rightCoeff hax q (Relabeling.relabelDist e r) = hpair.rightCoeff hax q r := by
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V r
      (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hBnd
  have hrq : (Relabeling.relabelDist e r).FullSupport := Relabeling.relabelDist_fullSupport e r hr
  have h1 := fs_bilinear_left_uninf hpair hax q (Relabeling.relabelDist e r) hq hrq
    (Channel.idChannel : Channel B' B')
  have h2 := fs_bilinear_left_uninf hpair hax q r hq hr (Channel.idChannel : Channel B B)
  -- V(rel e r, id_B') = V(r, id_B)
  have hVe : hfaces.branch_result.branch_agg.value_rep.V (Relabeling.relabelDist e r)
        (experimentOfChannel (Channel.idChannel : Channel B' B')) =
      hfaces.branch_result.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    have hc := hsel.V_relabel_eq hax e e r
      (Channel.idChannel : Channel B B)
    rw [relabelChannel_id_eq e] at hc
    exact hc
  -- LHS values equal via (refl_A × e) covariance
  have hcov : hfaces.branch_result.branch_agg.value_rep.V (prodDist q (Relabeling.relabelDist e r))
        (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B' B'))) =
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B))) := by
    have hc := hsel.V_relabel_eq hax
      ((Equiv.refl A).prodCongr e) ((Equiv.refl PUnit.{u+1}).prodCongr e)
      (prodDist q r) (prodChannel (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B))
    rw [Relabeling.relabelDist_prodCongr, Relabeling.relabelChannel_prodCongr] at hc
    rw [show Relabeling.relabelDist (Equiv.refl A) q = q from Relabeling.relabelDist_refl q] at hc
    rw [show Relabeling.relabelChannel (Equiv.refl A) (Equiv.refl PUnit.{u+1}) (Channel.uninformativeChannelU A)
          = (Channel.uninformativeChannelU A) from by
        ext a o; cases o; simp [Relabeling.relabelChannel, Channel.uninformativeChannelU]] at hc
    rw [relabelChannel_id_eq e] at hc
    exact hc
  rw [h1, h2, hVe] at hcov
  exact mul_right_cancel₀ hVnz hcov

/-- Support-face coboundary gauge: `ρ(q₀, x.restrictToSupport)`.  Evaluating at the
support face makes support-restriction invariance definitional. -/
noncomputable def cobGaugeSF
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : ℝ := by
  classical
  exact
    if Subsingleton (supportSubtype x) then 1
    else
      hpair.rightCoeff hax faceScaleInteractionReferencePrior x.restrictToSupport /
        hpair.leftCoeff hax faceScaleInteractionReferencePrior x.restrictToSupport

theorem cobGaugeSF_pos
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : TraceAxioms F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : 0 < cobGaugeSF hpair hax x := by
  classical
  unfold cobGaugeSF
  by_cases h : Subsingleton (supportSubtype x)
  · rw [if_pos h]; exact one_pos
  · rw [if_neg h]
    have hfs := Dist.restrictToSupport_fullSupport x
    exact div_pos
      (hpair.rightCoeff_pos hax faceScaleInteractionReferencePrior x.restrictToSupport
        faceScaleInteractionReferencePrior_fullSupport hfs)
      (hpair.leftCoeff_pos hax faceScaleInteractionReferencePrior x.restrictToSupport
        faceScaleInteractionReferencePrior_fullSupport hfs)


/-- For a full-support prior, restriction to support is a relabelling by the
support inclusion equivalence. -/
noncomputable def fullSupportRestrictEquiv {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) (hr : r.FullSupport) : supportSubtype r ≃ A where
  toFun x := x.1
  invFun a := ⟨a, hr a⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv a := rfl

theorem restrictToSupport_fullSupport_eq_relabel {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) :
    r.restrictToSupport = Relabeling.relabelDist (fullSupportRestrictEquiv r hr).symm r := by
  ext x; rw [Dist.restrictToSupport_apply, Relabeling.relabelDist_apply]; rfl

theorem cobGaugeSF_support_restrict
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) :
    cobGaugeSF hpair hax r = cobGaugeSF hpair hax r.restrictToSupport := by
  classical
  have hnd : ¬ Subsingleton (supportSubtype r) := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    rw [not_subsingleton_iff_nontrivial]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  have hrsfs : r.restrictToSupport.FullSupport := Dist.restrictToSupport_fullSupport r
  -- supportSubtype (r|supp) is also nondegenerate (≃ supportSubtype r)
  have hnd2 : ¬ Subsingleton (supportSubtype r.restrictToSupport) := by
    rw [not_subsingleton_iff_nontrivial] at hnd ⊢
    obtain ⟨a, b, hab⟩ := hnd
    refine ⟨⟨a, by rw [Dist.restrictToSupport_apply]; exact a.2⟩,
      ⟨b, by rw [Dist.restrictToSupport_apply]; exact b.2⟩, ?_⟩
    intro h; exact hab (congrArg Subtype.val h)
  unfold cobGaugeSF
  rw [if_neg hnd, if_neg hnd2]
  set rs := r.restrictToSupport with hrsdef
  -- rs.restrictToSupport = relabel (fullSupportRestrictEquiv rs hrsfs).symm rs
  rw [restrictToSupport_fullSupport_eq_relabel rs hrsfs]
  -- ρ(q₀, relabel e rs) = ρ(q₀, rs) via relabel-invariance of left/right coeff in 2nd arg
  have hnd : ¬ Subsingleton (supportSubtype r) := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    rw [not_subsingleton_iff_nontrivial]
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩
  rw [fs_leftCoeff_relabel_right hpair hsel hax faceScaleInteractionReferencePrior rs
      (fullSupportRestrictEquiv rs hrsfs).symm faceScaleInteractionReferencePrior_fullSupport hrsfs
      faceScaleInteractionReference_not_subsingleton]
  rw [fs_rightCoeff_relabel_right hpair hsel hax faceScaleInteractionReferencePrior rs
      (fullSupportRestrictEquiv rs hrsfs).symm faceScaleInteractionReferencePrior_fullSupport hrsfs hnd]


theorem cobGaugeSF_relabel
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) :
    cobGaugeSF hpair hax (Relabeling.relabelDist e q) = cobGaugeSF hpair hax q := by
  classical
  -- supportSubtype (relabel e q) ≃ supportSubtype q, so subsingleton-ness matches
  have hequiv : Subsingleton (supportSubtype (Relabeling.relabelDist e q)) ↔ Subsingleton (supportSubtype q) :=
    Equiv.subsingleton_congr (relabelSupportEquiv e q)
  unfold cobGaugeSF
  by_cases hnd : Subsingleton (supportSubtype q)
  · rw [if_pos (hequiv.mpr hnd), if_pos hnd]
  · rw [if_neg (fun h => hnd (hequiv.mp h)), if_neg hnd]
    have hface : (Relabeling.relabelDist e q).restrictToSupport =
        Relabeling.relabelDist (relabelSupportEquiv e q).symm q.restrictToSupport :=
      restrictToSupport_relabelDist e q
    rw [hface]
    have hqsfs : q.restrictToSupport.FullSupport := Dist.restrictToSupport_fullSupport q
    rw [fs_leftCoeff_relabel_right hpair hsel hax faceScaleInteractionReferencePrior
        q.restrictToSupport (relabelSupportEquiv e q).symm
        faceScaleInteractionReferencePrior_fullSupport hqsfs
        faceScaleInteractionReference_not_subsingleton]
    rw [fs_rightCoeff_relabel_right hpair hsel hax faceScaleInteractionReferencePrior
        q.restrictToSupport (relabelSupportEquiv e q).symm
        faceScaleInteractionReferencePrior_fullSupport hqsfs hnd]


/-- On full-support (nondegenerate) priors, `cobGaugeSF` agrees with `cobGauge`. -/
theorem cobGaugeSF_eq_cobGauge_of_fullSupport
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) (hnd : ¬ Subsingleton A) :
    cobGaugeSF hpair hax r = cobGauge hpair hax r := by
  have hndsupp : ¬ Subsingleton (supportSubtype r) := by
    rw [not_subsingleton_iff_nontrivial] at hnd ⊢
    obtain ⟨a, b, hab⟩ := hnd
    exact ⟨⟨a, hr a⟩, ⟨b, hr b⟩, fun h => hab (congrArg Subtype.val h)⟩
  unfold cobGaugeSF cobGauge
  rw [if_neg hndsupp]
  -- r|supp = relabel (fullSupportRestrictEquiv r hr).symm r ; ρ relabel-inv
  rw [restrictToSupport_fullSupport_eq_relabel r hr]
  rw [fs_leftCoeff_relabel_right hpair hsel hax faceScaleInteractionReferencePrior r
      (fullSupportRestrictEquiv r hr).symm faceScaleInteractionReferencePrior_fullSupport hr
      faceScaleInteractionReference_not_subsingleton]
  rw [fs_rightCoeff_relabel_right hpair hsel hax faceScaleInteractionReferencePrior r
      (fullSupportRestrictEquiv r hr).symm faceScaleInteractionReferencePrior_fullSupport hr hnd]

/-- cobGaugeSF is invariant under product-commutation relabel. -/
theorem cobGaugeSF_prodComm
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    cobGaugeSF hpair hax (prodDist r q) = cobGaugeSF hpair hax (prodDist q r) := by
  have h := cobGaugeSF_relabel hpair hsel hax (Equiv.prodComm B A) (prodDist r q)
  rw [relabelDist_prodComm r q] at h
  exact h.symm

/-- The coboundary gauge as a `CoherentFaceScaleGauge`. -/
noncomputable def cobCoherentGauge
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) : CoherentFaceScaleGauge.{u} where
  gauge := fun {A} _ _ _ x => cobGaugeSF hpair hax x
  gauge_pos := fun {A} _ _ _ x => cobGaugeSF_pos hpair hax x
  gauge_relabel_eq := fun {A B} _ _ _ _ _ _ e q => cobGaugeSF_relabel hpair hsel hax e q
  gauge_support_restrict_eq := fun {A} _ _ _ r _ hrn hrnd hrb =>
    cobGaugeSF_support_restrict hpair hsel hax r hrnd

theorem cobGaugeSF_coboundary
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {B C : Type u}
    [Fintype B] [DecidableEq B] [Nonempty B] [Fintype C] [DecidableEq C] [Nonempty C]
    (r : Dist B) (s : Dist C) (hr : r.FullSupport) (hs : s.FullSupport)
    (hBnd : ¬ Subsingleton B) (hCnd : ¬ Subsingleton C) :
    hpair.leftCoeff hax r s =
      cobGaugeSF hpair hax r / cobGaugeSF hpair hax (prodDist r s) := by
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
  have hrsnd : ¬ Subsingleton (B × C) := by
    rw [not_subsingleton_iff_nontrivial] at hBnd ⊢
    obtain ⟨b1, b2, hb⟩ := hBnd
    exact ⟨(b1, Classical.arbitrary C), (b2, Classical.arbitrary C), by simp [hb]⟩
  rw [cobGaugeSF_eq_cobGauge_of_fullSupport hpair hsel hax r hr hBnd,
      cobGaugeSF_eq_cobGauge_of_fullSupport hpair hsel hax (prodDist r s) hrs hrsnd]
  exact cobGauge_coboundary hpair htriple hax r s hr hs hBnd

noncomputable def subsingletonProdEquiv' {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Subsingleton A] [Fintype B] [DecidableEq B] : (A × B) ≃ B where
  toFun x := x.2
  invFun b := (Classical.arbitrary A, b)
  left_inv x := by obtain ⟨a,b⟩ := x; simp [Subsingleton.elim (Classical.arbitrary A) a]
  right_inv b := rfl


theorem relabel_subsingleton_prodDist' {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Subsingleton A] [Fintype B] [DecidableEq B] (q : Dist A) (r : Dist B) (hq : q.FullSupport) :
    Relabeling.relabelDist (subsingletonProdEquiv' (A := A) (B := B)) (prodDist q r) = r := by
  ext b
  rw [Relabeling.relabelDist_apply]
  show (prodDist q r) (Classical.arbitrary A, b) = r b
  have hq1 : q (Classical.arbitrary A) = 1 := by
    have hsum := q.sum_eq_one
    rw [Finset.sum_eq_single (Classical.arbitrary A)] at hsum
    · exact hsum
    · intro a _ hane; exact absurd (Subsingleton.elim a _) hane
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [prodDist_apply_pair, hq1, one_mul]

theorem relabel_subsingleton_prodChannel' {A B Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Subsingleton A] [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y] (R : Channel B Y) :
    Relabeling.relabelChannel (subsingletonProdEquiv' (A := A) (B := B)) (Equiv.punitProd Y)
        (prodChannel (Channel.uninformativeChannelU A) R) = R := by
  ext b y
  show (Relabeling.relabelDist (Equiv.punitProd Y)
      (prodChannel (Channel.uninformativeChannelU A) R (Classical.arbitrary A, b))) y = R b y
  rw [Relabeling.relabelDist_apply]
  show (prodChannel (Channel.uninformativeChannelU A) R (Classical.arbitrary A, b))
      ((Equiv.punitProd Y).symm y) = R b y
  rw [prodChannel_apply_pair]
  simp [Channel.uninformativeChannelU, Equiv.punitProd]


noncomputable def subsingletonProdEquivSnd {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B] : (A × B) ≃ A where
  toFun x := x.1
  invFun a := (a, Classical.arbitrary B)
  left_inv x := by obtain ⟨a,b⟩ := x; simp [Subsingleton.elim (Classical.arbitrary B) b]
  right_inv a := rfl

theorem relabel_subsingletonSnd_prodDist {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B] (q : Dist A) (r : Dist B) (hr : r.FullSupport) :
    Relabeling.relabelDist (subsingletonProdEquivSnd (A := A) (B := B)) (prodDist q r) = q := by
  ext a
  rw [Relabeling.relabelDist_apply]
  show (prodDist q r) (a, Classical.arbitrary B) = q a
  have hr1 : r (Classical.arbitrary B) = 1 := by
    have hsum := r.sum_eq_one
    rw [Finset.sum_eq_single (Classical.arbitrary B)] at hsum
    · exact hsum
    · intro b _ hbne; exact absurd (Subsingleton.elim b _) hbne
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [prodDist_apply_pair, hr1, mul_one]

theorem relabel_subsingletonSnd_prodChannel {A B O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B] [Fintype O] [DecidableEq O] (P : Channel A O) :
    Relabeling.relabelChannel (subsingletonProdEquivSnd (A := A) (B := B)) (Equiv.prodPUnit O)
        (prodChannel P (Channel.uninformativeChannelU B)) = P := by
  ext a o
  show (Relabeling.relabelDist (Equiv.prodPUnit O)
      (prodChannel P (Channel.uninformativeChannelU B) (a, Classical.arbitrary B))) o = P a o
  rw [Relabeling.relabelDist_apply]
  show (prodChannel P (Channel.uninformativeChannelU B) (a, Classical.arbitrary B))
      ((Equiv.prodPUnit O).symm o) = P a o
  rw [prodChannel_apply_pair]
  simp [Channel.uninformativeChannelU, Equiv.prodPUnit]

-- The gauged QA formula, case-split. Takes gauge g + nondeg-coboundary facts + subsingleton value facts.
theorem gauged_product_quasi_add
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (g : CoherentFaceScaleGauge.{u})
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F)
    -- κ common (all full-support q,r)
    (κ : ℝ)
    (hκ : ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B), q.FullSupport → r.FullSupport → ¬ Subsingleton A → ¬ Subsingleton B →
      hpair.interactionCoeff hax q r * (g.gauge (prodDist q r) / (g.gauge q * g.gauge r)) = κ)
    -- leftCoeff coboundary (nondeg both): leftCoeff q r = g(q)/g(q⊗r)
    (hleft : ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B), q.FullSupport → r.FullSupport → ¬ Subsingleton A → ¬ Subsingleton B →
      hpair.leftCoeff hax q r = g.gauge q / g.gauge (prodDist q r))
    -- rightCoeff coboundary (nondeg both): rightCoeff q r = g(r)/g(q⊗r)
    (hright : ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B), q.FullSupport → r.FullSupport → ¬ Subsingleton A → ¬ Subsingleton B →
      hpair.rightCoeff hax q r = g.gauge r / g.gauge (prodDist q r))
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    (hfaces.gaugeTransform g).branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      (hfaces.gaugeTransform g).branch_result.branch_agg.value_rep.V q (experimentOfChannel P) +
      (hfaces.gaugeTransform g).branch_result.branch_agg.value_rep.V r (experimentOfChannel R) +
      κ * (hfaces.gaugeTransform g).branch_result.branch_agg.value_rep.V q (experimentOfChannel P) *
        (hfaces.gaugeTransform g).branch_result.branch_agg.value_rep.V r (experimentOfChannel R) := by
  classical
  -- gauged values = g·V
  show g.gauge (prodDist q r) * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (prodChannel P R)) =
    g.gauge q * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) +
    g.gauge r * hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) +
    κ * (g.gauge q * hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P)) *
      (g.gauge r * hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R))
  rw [hpair.product_pair_bilinear hax q r hq hr P R]
  set Vqp := hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) with hVqp
  set Vrr := hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) with hVrr
  by_cases hA : Subsingleton A
  · -- Vqp = 0
    have hVqp0 : Vqp = 0 := by
      rw [hVqp]; exact V_channel_eq_zero_of_subsingleton F hfaces.branch_result.branch_agg.value_rep q hq P
    by_cases hB : Subsingleton B
    · have hVrr0 : Vrr = 0 := by
        rw [hVrr]; exact V_channel_eq_zero_of_subsingleton F hfaces.branch_result.branch_agg.value_rep r hr R
      rw [hVqp0, hVrr0]; ring
    · -- subsingleton A, nondeg B
      rw [hVqp0]
      -- goal: gqr·(leftCoeff·0 + rightCoeff·Vrr + κ_raw·0·Vrr) = gq·0 + gr·Vrr + κ·(gq·0)·(gr·Vrr)
      -- reduces to gqr·rightCoeff·Vrr = gr·Vrr
      -- rightCoeff q r · V(r,R) = V(q⊗r, U_A⊗R) = V(r,R) [V_subsingleton_fst_prod-style]
      haveI : Subsingleton A := hA
      have hVeq : hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R)) = Vrr := by
        have hc := hsel.V_relabel_eq hax
          (subsingletonProdEquiv' (A := A) (B := B)) (Equiv.punitProd Y)
          (prodDist q r) (prodChannel (Channel.uninformativeChannelU A) R)
        rw [relabel_subsingleton_prodDist' q r hq, relabel_subsingleton_prodChannel' R] at hc
        rw [hVrr]; exact hc.symm
      -- rightCoeff·Vrr = V(q⊗r,U_A⊗R) = Vrr
      have hrc : hpair.rightCoeff hax q r * Vrr = Vrr := by
        have := fs_bilinear_left_uninf hpair hax q r hq hr R
        rw [hVeq] at this; rw [hVrr]; linarith [this]
      -- gqr = gr  (q⊗r ≃ r relabel, gauge relabel-inv)
      have hgg : g.gauge (prodDist q r) = g.gauge r := by
        have := g.gauge_relabel_eq (subsingletonProdEquiv' (A := A) (B := B)) (prodDist q r)
        rw [relabel_subsingleton_prodDist' q r hq] at this
        exact this.symm
      -- close
      rw [hgg]
      have hgr : (0:ℝ) < g.gauge r := g.gauge_pos r
      nlinarith [hrc, hgr]
  · by_cases hB : Subsingleton B
    · -- nondeg A, subsingleton B
      have hVrr0 : Vrr = 0 := by
        rw [hVrr]; exact V_channel_eq_zero_of_subsingleton F hfaces.branch_result.branch_agg.value_rep r hr R
      rw [hVrr0]
      haveI : Subsingleton B := hB
      have hVeq : hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU B))) = Vqp := by
        have hc := hsel.V_relabel_eq hax
          (subsingletonProdEquivSnd (A := A) (B := B)) (Equiv.prodPUnit O)
          (prodDist q r) (prodChannel P (Channel.uninformativeChannelU B))
        rw [relabel_subsingletonSnd_prodDist q r hr, relabel_subsingletonSnd_prodChannel P] at hc
        rw [hVqp]; exact hc.symm
      have hlc : hpair.leftCoeff hax q r * Vqp = Vqp := by
        have := fs_bilinear_right_uninf hpair hax q r hq hr P
        rw [hVeq] at this; rw [hVqp]; linarith [this]
      have hgg : g.gauge (prodDist q r) = g.gauge q := by
        have := g.gauge_relabel_eq (subsingletonProdEquivSnd (A := A) (B := B)) (prodDist q r)
        rw [relabel_subsingletonSnd_prodDist q r hr] at this
        exact this.symm
      rw [hgg]
      have hgq : (0:ℝ) < g.gauge q := g.gauge_pos q
      nlinarith [hlc, hgq]
    · -- both nondeg: coboundary + gauged κ
      have hgq : 0 < g.gauge q := g.gauge_pos q
      have hgr : 0 < g.gauge r := g.gauge_pos r
      have hgqr : 0 < g.gauge (prodDist q r) := g.gauge_pos (prodDist q r)
      have hκraw : hpair.interactionCoeff hax q r =
          κ * (g.gauge q * g.gauge r) / g.gauge (prodDist q r) := by
        have hκe := hκ q r hq hr hA hB
        field_simp at hκe ⊢
        linarith [hκe]
      rw [hleft q r hq hr hA hB, hright q r hq hr hA hB, hκraw]
      field_simp [ne_of_gt hgq, ne_of_gt hgr, ne_of_gt hgqr]

theorem gaugedLeftCoeff_eq_one_nondeg
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    faceScaleGaugeTransformedLeftCoeff hpair (cobCoherentGauge hpair hsel hax) hax q r = 1 := by
  unfold faceScaleGaugeTransformedLeftCoeff
  show hpair.leftCoeff hax q r * (cobGaugeSF hpair hax (prodDist q r) / cobGaugeSF hpair hax q) = 1
  rw [cobGaugeSF_coboundary hpair htriple hsel hax q r hq hr hA hB]
  have h1 : 0 < cobGaugeSF hpair hax q := cobGaugeSF_pos hpair hax q
  have h2 : 0 < cobGaugeSF hpair hax (prodDist q r) := cobGaugeSF_pos hpair hax (prodDist q r)
  field_simp

theorem gaugedRightCoeff_eq_one_nondeg
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    faceScaleGaugeTransformedRightCoeff hpair (cobCoherentGauge hpair hsel hax) hax q r = 1 := by
  unfold faceScaleGaugeTransformedRightCoeff
  show hpair.rightCoeff hax q r * (cobGaugeSF hpair hax (prodDist q r) / cobGaugeSF hpair hax r) = 1
  -- rightCoeff q r = leftCoeff r q (swap, ¬Subsing B) = cobGaugeSF r/cobGaugeSF(r⊗q) [coboundary r,q]
  rw [fs_rightCoeff_eq_swapped_leftCoeff hpair hsel hax q r hq hr hB]
  rw [cobGaugeSF_coboundary hpair htriple hsel hax r q hr hq hB hA]
  -- cobGaugeSF(r⊗q) = cobGaugeSF(q⊗r) [prodComm]
  rw [cobGaugeSF_prodComm hpair hsel hax q r]
  have h1 : 0 < cobGaugeSF hpair hax r := cobGaugeSF_pos hpair hax r
  have h2 : 0 < cobGaugeSF hpair hax (prodDist q r) := cobGaugeSF_pos hpair hax (prodDist q r)
  field_simp

theorem gauged_bilinear_normalized_nondeg
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) (P : Channel A O) (R : Channel B Y) :
    (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax)).branch_result.branch_agg.value_rep.V
        (prodDist q r) (experimentOfChannel (prodChannel P R)) =
      (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax)).branch_result.branch_agg.value_rep.V q
        (experimentOfChannel P) +
      (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax)).branch_result.branch_agg.value_rep.V r
        (experimentOfChannel R) +
      (faceScaleProductPairwiseBilinearity_gaugeTransform hpair (cobCoherentGauge hpair hsel hax)).interactionCoeff hax q r *
        (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax)).branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) *
        (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax)).branch_result.branch_agg.value_rep.V r
          (experimentOfChannel R) := by
  set g := cobCoherentGauge hpair hsel hax
  rw [(faceScaleProductPairwiseBilinearity_gaugeTransform hpair g).product_pair_bilinear hax q r hq hr P R]
  rw [show (faceScaleProductPairwiseBilinearity_gaugeTransform hpair g).leftCoeff hax q r =
    faceScaleGaugeTransformedLeftCoeff hpair g hax q r from rfl]
  rw [show (faceScaleProductPairwiseBilinearity_gaugeTransform hpair g).rightCoeff hax q r =
    faceScaleGaugeTransformedRightCoeff hpair g hax q r from rfl]
  rw [gaugedLeftCoeff_eq_one_nondeg hpair htriple hsel hax q r hq hr hA hB,
      gaugedRightCoeff_eq_one_nondeg hpair htriple hsel hax q r hq hr hA hB]
  ring

private theorem prod_nondeg {A B : Type u} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (hA : ¬ Subsingleton A) : ¬ Subsingleton (A × B) := by
  rw [not_subsingleton_iff_nontrivial] at hA ⊢
  obtain ⟨a1,a2,ha⟩ := hA
  exact ⟨(a1, Classical.arbitrary B),(a2, Classical.arbitrary B), by simp [ha]⟩

private theorem prod_nondeg_r {A B : Type u} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (hB : ¬ Subsingleton B) : ¬ Subsingleton (A × B) := by
  rw [not_subsingleton_iff_nontrivial] at hB ⊢
  obtain ⟨b1,b2,hb⟩ := hB
  exact ⟨(Classical.arbitrary A, b1),(Classical.arbitrary A, b2), by simp [hb]⟩

theorem gaugedInteractionAssoc
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax0 : TraceAxioms F) :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor
      (faceScaleProductPairwiseBilinearity_gaugeTransform hpair
        (cobCoherentGauge hpair hsel hax0)) where
  interaction_assoc_xy := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    set GT := hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax0)
    have hgt := (faceScaleTripleProductValueAssociativity_gaugeTransform htriple (cobCoherentGauge hpair hsel hax0)).triple_value_assoc
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hxne : GT.branch_result.branch_agg.value_rep.V q (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 GT hax q hq hA
    have hyne : GT.branch_result.branch_agg.value_rep.V r (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 GT hax r hr hB
    have hxyne := mul_ne_zero hxne hyne
    have hval := hgt hax q r s hq hr hs
      (Channel.idChannel : Channel A A) (Channel.idChannel : Channel B B) (Channel.uninformativeChannelU C)
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax (prodDist q r) s hqr hs (prod_nondeg hA) hC
        (prodChannel (Channel.idChannel : Channel A A) (Channel.idChannel : Channel B B)) (Channel.uninformativeChannelU C)] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax q (prodDist r s) hq hrs hA (prod_nondeg hB)
        (Channel.idChannel : Channel A A) (prodChannel (Channel.idChannel : Channel B B) (Channel.uninformativeChannelU C))] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax q r hq hr hA hB
        (Channel.idChannel : Channel A A) (Channel.idChannel : Channel B B)] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax r s hr hs hB hC
        (Channel.idChannel : Channel B B) (Channel.uninformativeChannelU C)] at hval
    rw [GT.branch_result.branch_agg.value_rep.zero_normalized s hs] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxyne (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_xz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    set GT := hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax0)
    have hgt := (faceScaleTripleProductValueAssociativity_gaugeTransform htriple (cobCoherentGauge hpair hsel hax0)).triple_value_assoc
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hxne : GT.branch_result.branch_agg.value_rep.V q (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 GT hax q hq hA
    have hzne : GT.branch_result.branch_agg.value_rep.V s (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 GT hax s hs hC
    have hxzne := mul_ne_zero hxne hzne
    have hval := hgt hax q r s hq hr hs
      (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B) (Channel.idChannel : Channel C C)
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax (prodDist q r) s hqr hs (prod_nondeg hA) hC
        (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)) (Channel.idChannel : Channel C C)] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax q (prodDist r s) hq hrs hA (prod_nondeg_r hC)
        (Channel.idChannel : Channel A A) (prodChannel (Channel.uninformativeChannelU B) (Channel.idChannel : Channel C C))] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax q r hq hr hA hB
        (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax r s hr hs hB hC
        (Channel.uninformativeChannelU B) (Channel.idChannel : Channel C C)] at hval
    rw [GT.branch_result.branch_agg.value_rep.zero_normalized r hr] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxzne (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_yz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    set GT := hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax0)
    have hgt := (faceScaleTripleProductValueAssociativity_gaugeTransform htriple (cobCoherentGauge hpair hsel hax0)).triple_value_assoc
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hyne : GT.branch_result.branch_agg.value_rep.V r (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 GT hax r hr hB
    have hzne : GT.branch_result.branch_agg.value_rep.V s (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 GT hax s hs hC
    have hyzne := mul_ne_zero hyne hzne
    have hval := hgt hax q r s hq hr hs
      (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B) (Channel.idChannel : Channel C C)
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax (prodDist q r) s hqr hs (prod_nondeg_r hB) hC
        (prodChannel (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B)) (Channel.idChannel : Channel C C)] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax q (prodDist r s) hq hrs hA (prod_nondeg hB)
        (Channel.uninformativeChannelU A) (prodChannel (Channel.idChannel : Channel B B) (Channel.idChannel : Channel C C))] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax q r hq hr hA hB
        (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B)] at hval
    rw [gauged_bilinear_normalized_nondeg hpair htriple hsel hax r s hr hs hB hC
        (Channel.idChannel : Channel B B) (Channel.idChannel : Channel C C)] at hval
    rw [GT.branch_result.branch_agg.value_rep.zero_normalized q hq] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hyzne (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

noncomputable def productQuasiAdditivity_cobGauge
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax0 : TraceAxioms F) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax0)) where
  kappa := fun hax =>
    faceScaleInteractionReferenceKappa
      (faceScaleProductPairwiseBilinearity_gaugeTransform hpair (cobCoherentGauge hpair hsel hax0)) hax
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    refine gauged_product_quasi_add hpair (cobCoherentGauge hpair hsel hax0) hsel hax _ ?_ ?_ ?_ q r hq hr P R
    · -- hκ: gauged interaction = ref κ at nondeg
      intro A' B' _ _ _ _ _ _ q' r' hq' hr' hA' hB'
      -- gauged interactionCoeff = raw·g(q⊗r)/(g(q)g(r)) by def; = ref κ via assoc-nondeg
      rw [show hpair.interactionCoeff hax q' r' *
          ((cobCoherentGauge hpair hsel hax0).gauge (prodDist q' r') /
          ((cobCoherentGauge hpair hsel hax0).gauge q' * (cobCoherentGauge hpair hsel hax0).gauge r')) =
        (faceScaleProductPairwiseBilinearity_gaugeTransform hpair (cobCoherentGauge hpair hsel hax0)).interactionCoeff hax q' r'
        from rfl]
      exact faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
        (faceScaleProductPairwiseBilinearity_gaugeTransform hpair (cobCoherentGauge hpair hsel hax0))
        (gaugedInteractionAssoc hpair htriple hsel hax0) hax q' r' hq' hr' hA' hB'
    · intro A' B' _ _ _ _ _ _ q' r' hq' hr' hA' hB'
      exact cobGaugeSF_coboundary hpair htriple hsel hax q' r' hq' hr' hA' hB'
    · intro A' B' _ _ _ _ _ _ q' r' hq' hr' hA' hB'
      -- rightCoeff q' r' = g(r')/g(q'⊗r'): swap + coboundary + prodComm
      rw [fs_rightCoeff_eq_swapped_leftCoeff hpair hsel hax q' r' hq' hr' hB']
      rw [cobGaugeSF_coboundary hpair htriple hsel hax r' q' hr' hq' hB' hA']
      show (cobCoherentGauge hpair hsel hax0).gauge r' / cobGaugeSF hpair hax (prodDist r' q') = _
      rw [cobGaugeSF_prodComm hpair hsel hax q' r']
      rfl

theorem coordinateValueConvention_of_HM
    (hsupp : ∀ (F' : PrefFamily.{u}) (hax : TraceAxioms F') (hV' : PosteriorValueRepresentation F')
      {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV'.V r (experimentOfChannel P) =
        hV'.V r.restrictToSupport (experimentOfChannel (Channel.restrictToSupport P r)))
    (hcov : ∀ {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B] [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O),
        hfaces.branch_result.branch_agg.value_rep.V (Relabeling.relabelDist eA q)
            (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P)) :
    FiniteCoordinateSupportFaceValueConventionFor hfaces where
  first_coordinate_face_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB a
    have ha : 0 < q a := hq a
    rw [posterior_productFirstRevealChannel_prodDist_of_pos q r a ha]
    -- V(pure a ⊗ r, secondReveal) = V(r, id) = fullRev r
    rw [show fullRevelationValueForFaceScales hfaces r =
      hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel (Channel.idChannel : Channel B B))
      from rfl]
    exact first_coordinate_face_value_of_HM
      (hV := hfaces.branch_result.branch_agg.value_rep) hsupp hcov hax a r
  second_coordinate_face_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB b
    have hb : 0 < r b := hr b
    rw [posterior_productSecondRevealChannel_prodDist_of_pos q r b hb]
    rw [show fullRevelationValueForFaceScales hfaces q =
      hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel (Channel.idChannel : Channel A A))
      from rfl]
    exact second_coordinate_face_value_of_HM
      (hV := hfaces.branch_result.branch_agg.value_rep) hsupp hcov hax q b

/-- Value-side pre-entropy conventions (derivable from HM before universal-scale collapse). -/
structure PreEntropyValueConventions (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  coordinate_value : FiniteCoordinateSupportFaceValueConventionFor hfaces
  block_value : FiniteBlockSupportFaceValueConventionFor hfaces

/-- Scale-side pre-entropy conventions (universal-scale representative choice). -/
structure PreEntropyScaleConventions (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  coordinate_scale : FiniteCoordinateSupportFaceScaleConventionFor hfaces
  block_scale : FiniteBlockSupportFaceScaleConventionFor hfaces
  universal_singleton : FiniteUniversalScaleSingletonConventionFor hfaces

/-- Reference/Z normalization. -/
structure PreEntropyReferenceConventions (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  reference_z : FiniteProductReferenceZNormalizationFor hfaces hprod

/-- Compatibility wrapper: reassemble the monolithic bundle from the split parts. -/
theorem preEntropyRepresentativeGaugeConventions_of_parts
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hval : PreEntropyValueConventions hfaces)
    (hscale : PreEntropyScaleConventions hfaces)
    (href : PreEntropyReferenceConventions hfaces hprod) :
    PreEntropyRepresentativeGaugeConventions hfaces hprod where
  coordinate_value := hval.coordinate_value
  coordinate_scale := hscale.coordinate_scale
  block_value := hval.block_value
  block_scale := hscale.block_scale
  reference_z := href.reference_z
  universal_singleton := hscale.universal_singleton

end FaceScaleProductCocycle

/-- **Formal reduction of value-relabelling to the scalar pinning obligation.**

The full-support selected value-relabelling clause
(`FiniteFullSupportSelectedPosteriorValueRelabelingFor`) is *entirely* reduced,
from the classical HM affine representation and the (proved, hypothesis-free)
finite affine-utility uniqueness theorem, to the single scalar-pinning
obligation `hpin` (`c = 1`).  The actionbase scalar `V ∘ relabel = c · V` with
`c > 0` is derived by `selectedActionbaseScalar_of_orderRelabeling_HM_fullSupport`
(order transport via `relabel_rel_of_axioms` + HM public-mix affinity + affine
uniqueness + zero normalization pinning the additive constant to `0`); the
outcome-relabelling half is derived from posterior-law invariance.  The only
non-derived content of value-relabelling is therefore the scalar pinning
`c = 1` — which in the paper follows from product quasi-additivity, but in the
coboundary-gauge route that QA is *itself* built from relabelling, so importing
the pinning that way would be circular.  This theorem records exactly where the
residual sits: on `hpin`, and nowhere else. -/
theorem finitePosteriorValueRelabeling_blockedOn_pinning
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hpin : FiniteFullSupportSelectedPermutationInvariancePinningFor hfaces) :
    FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces :=
  finiteFullSupportSelectedPosteriorValueRelabeling_of_actionbase_pinning
    (selectedActionbaseScalar_of_orderRelabeling_HM_fullSupport
      hhm classicalFiniteAffineUtilityUniquenessAssumptions)
    hpin


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
      FiniteSelectedPosteriorValueRelabelingFor
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
            hnorm
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
            hnorm
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm hfaith hax hgauge hrel hsupport hsingleSlice)))) :
    FiniteProductQuasiAdditivityForFaceScales
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport) :=
  productQuasiAdditivity_of_FinalHM_positiveGaugeSourceProductData_internalIntercept
    hhm hfaith hax hgauge hrel hsupport hsingleSlice
    (faceScaleProductSlopeAffine_of_selectedRelabeling
      hnorm
      (productInterceptPositiveLinear_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport hsingleSlice))
    hcurrentGauge
    (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm hfaith hax hgauge hrel hsupport)
      hnorm)
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

/-- **Smaller-signature final MI theorem: `current_product_gauge` and
`singleton_interaction` are ELIMINATED.**

Compared with `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConstructedPreEntropy`
(and its downstream `…withProductNormalizedSelectedRepresentatives` /
`…withCardinalGauge` variants), this route does **not** take a
`FiniteFaceScaleProductGaugeTransformFor` (`current_product_gauge`) nor a
`FiniteFaceScaleSingletonInteractionConventionFor` (`singleton_interaction`)
input.  Product quasi-additivity for the working representative is *constructed*
internally by `productQuasiAdditivity_cobGauge`: the coboundary gauge built from
the associativity cocycle (`cobCoherentGauge`) normalises the left product
coefficient, and the right coefficient is then *proved* equal to `1` from the
product-swap symmetry — so no product-normalisation convention is assumed.

The only structural product input that remains is
`FinitePosteriorValueRelabelingAssumptions` (`hrelV`), a value-relabeling
assumption used to obtain triple-product value associativity; it is not a
product-gauge or singleton-interaction convention.  The remaining bundle
`FinalHarmlessConventions` carries exactly `singleton_slice` and `pre_entropy`
— neither of which is `current_product_gauge`, `singleton_interaction`, or
`product_normalized`. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_cobGaugeNoProductField
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hconv :
      FinalHarmlessConventions
        (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax))
        (productQuasiAdditivity_cobGauge hpair htriple hsel hax)) :
    MIRep F :=
  MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputsAndConventions
    hfad
    (hfaces.gaugeTransform (cobCoherentGauge hpair hsel hax))
    (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
    (hprod := productQuasiAdditivity_cobGauge hpair htriple hsel hax)
    hconv hax

/-- **Residual conventions for the product-gauge-free top-level route.**

This bundle carries exactly the inputs the coboundary-gauge MI route still
requires once the product-normalisation conventions are eliminated:
* the faithful-branch convention bundle, positive gauge, and its scale/support
  fields (`branch`, `gauge`, `scale_relabel`, `support_scale`) — the same
  representative-choice data the older routes carry;
* `selected_value_relabel` — the *per-representative* value-relabelling
  coherence clause (`FiniteSelectedPosteriorValueRelabelingFor` for the
  constructed coherent representative — strictly weaker than the
  all-representations `FinitePosteriorValueRelabelingAssumptions`), from which
  triple-product value associativity and the product-swap slope-affinity are
  *derived*;
* `harmless` — the `FinalHarmlessConventions` bundle (`singleton_slice` +
  `pre_entropy`) for the coboundary-gauge-transformed representative.

It does **not** contain `product_normalized`, `current_product_gauge`,
`singleton_interaction`, or `FiniteCardinalSupportBoundaryAssumptions`. -/
structure ResidualConventionsWithoutProductGauge
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
  selected_value_relabel :
    FiniteSelectedPosteriorValueRelabelingFor
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax gauge scale_relabel support_scale)
  harmless :
    FinalHarmlessConventions
      ((coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax gauge scale_relabel support_scale).gaugeTransform
        (cobCoherentGauge
          (faceScaleProductPairwiseBilinearity_of_multiPieces
            (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
              (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                    hhm branch)
                  hax gauge scale_relabel support_scale)))
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm branch)
              hax gauge scale_relabel support_scale
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                    hhm branch)
                  hax gauge scale_relabel support_scale)))
            (faceScaleProductSlopeAffine_of_selectedRelabeling
              selected_value_relabel
              (productInterceptPositiveLinear_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm branch)
                hax gauge scale_relabel support_scale
                (finiteFaceScaleSingletonSliceAffine_of_faces
                  (coherentFaceScales_of_FinalHM_positiveGauge
                    hhm
                    (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                      hhm branch)
                    hax gauge scale_relabel support_scale)))))
          selected_value_relabel hax))
      (productQuasiAdditivity_cobGauge
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm branch)
                hax gauge scale_relabel support_scale)))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm branch)
                hax gauge scale_relabel support_scale)))
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            selected_value_relabel
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm branch)
              hax gauge scale_relabel support_scale
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                    hhm branch)
                  hax gauge scale_relabel support_scale)))))
        (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale)
          selected_value_relabel)
        selected_value_relabel hax)

/-- **Top-level product-gauge-free, boundary-support-free final MI theorem.**

Reaches `MIRep F` from `TraceAxioms + HM + Faddeev` plus the residual bundle
`ResidualConventionsWithoutProductGauge`.  Relative to the older top-level route
`FinalConstructedRepresentativeConventions`, the fields `product_normalized`,
`current_product_gauge`, `singleton_interaction`, and the cardinal
boundary-support assumption are **removed**: product quasi-additivity is
constructed internally by the coboundary gauge (`productQuasiAdditivity_cobGauge`)
and the boundary content is proved.

This is **not** a convention-free theorem.  The residual interfaces
`selected_value_relabel` (the *per-representative* relabelling clause
`FiniteSelectedPosteriorValueRelabelingFor` — weaker than the earlier
all-representations `FinitePosteriorValueRelabelingAssumptions`; its actionbase
scalar is provable from HM/axioms, only the scalar pinning `c = 1` is residual —
see `finitePosteriorValueRelabeling_blockedOn_pinning`), `support_scale`
(the raw face-scale equation), and `harmless.pre_entropy`
(`PreEntropyRepresentativeGaugeConventions`) remain and are disclosed in
`TraceableAgency/CERTIFICATE_PRODUCT_GAUGE_FREE.md`.  The honest claim is:
**product-gauge-free and boundary-support-free, modulo residual
representative / relabelling / pre-entropy conventions.** -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hres : ResidualConventionsWithoutProductGauge hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_cobGaugeNoProductField
    hfad hhm hax
    (hpair :=
      faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
          (finiteFaceScaleSingletonSliceAffine_of_faces
            (coherentFaceScales_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hres.branch)
              hax hres.gauge hres.scale_relabel hres.support_scale)))
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hres.branch)
          hax hres.gauge hres.scale_relabel hres.support_scale
          (finiteFaceScaleSingletonSliceAffine_of_faces
            (coherentFaceScales_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm hres.branch)
              hax hres.gauge hres.scale_relabel hres.support_scale)))
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          hres.selected_value_relabel
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm hres.branch)
            hax hres.gauge hres.scale_relabel hres.support_scale
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                  hhm hres.branch)
                hax hres.gauge hres.scale_relabel hres.support_scale)))))
    (htriple :=
      faceScaleTripleProductValueAssociativity_of_selectedRelabeling
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm hres.branch)
          hax hres.gauge hres.scale_relabel hres.support_scale)
        hres.selected_value_relabel)
    (hsel := hres.selected_value_relabel)
    hres.harmless

/-- **Residual conventions for the product-gauge-free AND support-scale-free
top-level route.**

This bundle fixes the positive face-scale gauge to the *cardinal gauge*
`cardinalGauge` (the cardinality-indexed scale `t_n`), for which the raw
face-scale equation (`eq:facescale`, the `support_scale` field of
`ResidualConventionsWithoutProductGauge`) and the scale relabel-equivariance
(`scale_relabel`) are **theorems** (`cardinalGauge_hsupport`,
`cardinalGauge_hrel`), not assumptions.

Compared with `ResidualConventionsWithoutProductGauge`, the fields `gauge`,
`scale_relabel`, and `support_scale` are therefore all **removed**.  The
remaining fields are `branch`, `selected_value_relabel`, and `harmless` (for the
cardinal-gauge representative). -/
structure ResidualConventionsWithoutProductGaugeOrSupportScale
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) where
  branch : FinalFaithfulBranchConventions hhm
  selected_value_relabel :
    FiniteSelectedPosteriorValueRelabelingFor
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
        hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
          cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))
  harmless :
    FinalHarmlessConventions
      ((coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
          hax (cardinalGauge hhm branch hax)
          (cardinalGauge_hrel hhm branch hax)
          (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
            cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)).gaugeTransform
        (cobCoherentGauge
          (faceScaleProductPairwiseBilinearity_of_multiPieces
            (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
              (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
              hax (cardinalGauge hhm branch hax)
              (cardinalGauge_hrel hhm branch hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
            (faceScaleProductSlopeAffine_of_selectedRelabeling
              selected_value_relabel
              (productInterceptPositiveLinear_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
                (finiteFaceScaleSingletonSliceAffine_of_faces
                  (coherentFaceScales_of_FinalHM_positiveGauge
                    hhm
                    (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                    hax (cardinalGauge hhm branch hax)
                    (cardinalGauge_hrel hhm branch hax)
                    (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                      cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))))
          selected_value_relabel hax))
      (productQuasiAdditivity_cobGauge
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            hax (cardinalGauge hhm branch hax)
            (cardinalGauge_hrel hhm branch hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            selected_value_relabel
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
              hax (cardinalGauge hhm branch hax)
              (cardinalGauge_hrel hhm branch hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))))
        (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            hax (cardinalGauge hhm branch hax)
            (cardinalGauge_hrel hhm branch hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))
          selected_value_relabel)
        selected_value_relabel hax)

/-- **Top-level product-gauge-free AND support-scale-free final MI theorem.**

Extends `MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductConventions` by fixing the
positive gauge to `cardinalGauge`, for which the raw face-scale equation
(`support_scale`) and the scale relabel-equivariance (`scale_relabel`) are proved
(`cardinalGauge_hsupport`, `cardinalGauge_hrel`).  The residual bundle therefore
drops the `gauge`, `scale_relabel`, and `support_scale` fields entirely.

Remaining residual interfaces: `selected_value_relabel` (per-representative
relabelling, reduces to the scalar pinning `c = 1`) and `harmless.pre_entropy`.
The honest claim is: **product-gauge-free, boundary-support-free, and
raw-face-scale-free (`support_scale` discharged by the cardinal gauge), modulo
residual per-representative relabelling and pre-entropy conventions.** -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductOrSupportScaleConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hres : ResidualConventionsWithoutProductGaugeOrSupportScale hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductConventions
    hfad hhm hax
    { branch := hres.branch
      gauge := cardinalGauge hhm hres.branch hax
      scale_relabel := cardinalGauge_hrel hhm hres.branch hax
      support_scale := fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
        cardinalGauge_hsupport hhm hres.branch hax q hq r hrn hrnd hrb
      selected_value_relabel := hres.selected_value_relabel
      harmless := hres.harmless }

/-- **Residual conventions with product gauge, support scale, AND value
relabelling all eliminated.**

Extends `ResidualConventionsWithoutProductGaugeOrSupportScale` by discharging the
`selected_value_relabel` field: for the cardinal-gauge coherent representative the
selected relabelling clause is a **theorem** (`selectedValueRelabel_of_cardinalGauge`),
proved from the integral representation's `marginalValue_relabel` naturality (the
value scalar is `1`), so it is no longer a bundle input.  Only `branch` and
`harmless` remain. -/
structure ResidualConventionsWithoutProductGaugeOrSupportScaleOrValueRelabel
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) where
  branch : FinalFaithfulBranchConventions hhm
  harmless :
    FinalHarmlessConventions
      ((coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
          hax (cardinalGauge hhm branch hax)
          (cardinalGauge_hrel hhm branch hax)
          (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
            cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)).gaugeTransform
        (cobCoherentGauge
          (faceScaleProductPairwiseBilinearity_of_multiPieces
            (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
              (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
              hax (cardinalGauge hhm branch hax)
              (cardinalGauge_hrel hhm branch hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
            (faceScaleProductSlopeAffine_of_selectedRelabeling
              (selectedValueRelabel_of_cardinalGauge hhm branch hax)
              (productInterceptPositiveLinear_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
                (finiteFaceScaleSingletonSliceAffine_of_faces
                  (coherentFaceScales_of_FinalHM_positiveGauge
                    hhm
                    (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                    hax (cardinalGauge hhm branch hax)
                    (cardinalGauge_hrel hhm branch hax)
                    (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                      cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))))
          (selectedValueRelabel_of_cardinalGauge hhm branch hax) hax))
      (productQuasiAdditivity_cobGauge
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            hax (cardinalGauge hhm branch hax)
            (cardinalGauge_hrel hhm branch hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            (selectedValueRelabel_of_cardinalGauge hhm branch hax)
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
              hax (cardinalGauge hhm branch hax)
              (cardinalGauge_hrel hhm branch hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))))
        (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            hax (cardinalGauge hhm branch hax)
            (cardinalGauge_hrel hhm branch hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))
          (selectedValueRelabel_of_cardinalGauge hhm branch hax))
        (selectedValueRelabel_of_cardinalGauge hhm branch hax) hax)

/-- **Top-level product-gauge-free, support-scale-free, AND value-relabel-free
final MI theorem.**

The residual bundle carries only `branch` and `harmless`.  The gauge is fixed to
`cardinalGauge`; `scale_relabel` and `support_scale` are theorems
(`cardinalGauge_hrel`, `cardinalGauge_hsupport`); and the selected value
relabelling is the theorem `selectedValueRelabel_of_cardinalGauge` (value scalar
`= 1`, from `marginalValue_relabel`).  No product gauge, no support-scale, and no
relabelling clause is assumed.

Remaining residual interface: `harmless.pre_entropy`.  Honest claim:
**product-gauge-free, boundary-support-free, support-scale-free, and
value-relabel-free, modulo the pre-entropy representative conventions.** -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductSupportOrValueRelabelConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hres : ResidualConventionsWithoutProductGaugeOrSupportScaleOrValueRelabel hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductOrSupportScaleConventions
    hfad hhm hax
    { branch := hres.branch
      selected_value_relabel := selectedValueRelabel_of_cardinalGauge hhm hres.branch hax
      harmless := hres.harmless }

/-- **Residual conventions with product gauge, support scale, value relabelling,
AND singleton slice all eliminated.**

Extends `ResidualConventionsWithoutProductGaugeOrSupportScaleOrValueRelabel` by
discharging the `singleton_slice` component of `harmless`: it is a theorem
(`finiteFaceScaleSingletonSliceAffine_of_faces`), so only `pre_entropy` remains.
The bundle therefore carries only `branch` and `pre_entropy`. -/
structure ResidualConventionsWithoutProductGaugeSupportScaleValueRelabelOrSingletonSlice
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) where
  branch : FinalFaithfulBranchConventions hhm
  pre_entropy :
    PreEntropyRepresentativeGaugeConventions
      ((coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
          hax (cardinalGauge hhm branch hax)
          (cardinalGauge_hrel hhm branch hax)
          (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
            cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)).gaugeTransform
        (cobCoherentGauge
          (faceScaleProductPairwiseBilinearity_of_multiPieces
            (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
              (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
              hax (cardinalGauge hhm branch hax)
              (cardinalGauge_hrel hhm branch hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
            (faceScaleProductSlopeAffine_of_selectedRelabeling
              (selectedValueRelabel_of_cardinalGauge hhm branch hax)
              (productInterceptPositiveLinear_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
                (finiteFaceScaleSingletonSliceAffine_of_faces
                  (coherentFaceScales_of_FinalHM_positiveGauge
                    hhm
                    (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                    hax (cardinalGauge hhm branch hax)
                    (cardinalGauge_hrel hhm branch hax)
                    (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                      cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))))
          (selectedValueRelabel_of_cardinalGauge hhm branch hax) hax))
      (productQuasiAdditivity_cobGauge
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            hax (cardinalGauge hhm branch hax)
            (cardinalGauge_hrel hhm branch hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                hax (cardinalGauge hhm branch hax)
                (cardinalGauge_hrel hhm branch hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            (selectedValueRelabel_of_cardinalGauge hhm branch hax)
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
              hax (cardinalGauge hhm branch hax)
              (cardinalGauge_hrel hhm branch hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
                  hax (cardinalGauge hhm branch hax)
                  (cardinalGauge_hrel hhm branch hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))))))
        (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm branch)
            hax (cardinalGauge hhm branch hax)
            (cardinalGauge_hrel hhm branch hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm branch hax q hq r hrn hrnd hrb))
          (selectedValueRelabel_of_cardinalGauge hhm branch hax))
        (selectedValueRelabel_of_cardinalGauge hhm branch hax) hax)

/-- **Top-level MI theorem with product gauge, support scale, value relabelling,
AND singleton slice all eliminated.**

The residual bundle carries only `branch` and `pre_entropy`.  The gauge is fixed
to `cardinalGauge`; `scale_relabel`/`support_scale` are theorems; selected value
relabelling is a theorem; and `singleton_slice` is the theorem
`finiteFaceScaleSingletonSliceAffine_of_faces`.

Sole remaining residual interface: `pre_entropy`
(`PreEntropyRepresentativeGaugeConventions`).  Honest claim: **product-gauge-free,
boundary-support-free, support-scale-free, value-relabel-free, and
singleton-slice-free, modulo the pre-entropy representative conventions.** -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductSupportValueOrSingletonConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hres :
      ResidualConventionsWithoutProductGaugeSupportScaleValueRelabelOrSingletonSlice
        hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductSupportOrValueRelabelConventions
    hfad hhm hax
    { branch := hres.branch
      harmless :=
        finalHarmlessConventions_of_withoutSingletonSlice
          { pre_entropy := hres.pre_entropy } }

/-- **Residual with `branch` reduced to its 4-field boundary-transport core.**

Same as `ResidualConventionsWithoutProductGaugeSupportScaleValueRelabelOrSingletonSlice`
except the six-field `branch : FinalFaithfulBranchConventions hhm` is replaced by
the strictly smaller four-field `minimal : MinimalBranchResidual hhm` (the
`support_face` and `singleton_scale` fields are proved, not assumed).  The full
`branch` bundle is reconstructed internally by
`finalFaithfulBranchConventions_of_minimal`.  Residual content: `minimal`
(4 boundary-transport fields) and `pre_entropy`. -/
structure ResidualMinimalBranchAndPreEntropy
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) where
  minimal : MinimalBranchResidual hhm
  pre_entropy :
    PreEntropyRepresentativeGaugeConventions
      ((coherentFaceScales_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
          hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
          (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
          (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
            cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb)).gaugeTransform
        (cobCoherentGauge
          (faceScaleProductPairwiseBilinearity_of_multiPieces
            (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
              (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
                  hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                  (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb))))
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
              hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
              (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
                  hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                  (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb))))
            (faceScaleProductSlopeAffine_of_selectedRelabeling
              (selectedValueRelabel_of_cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
              (productInterceptPositiveLinear_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
                hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb)
                (finiteFaceScaleSingletonSliceAffine_of_faces
                  (coherentFaceScales_of_FinalHM_positiveGauge
                    hhm
                    (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
                    hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                    (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                    (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                      cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb))))))
          (selectedValueRelabel_of_cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax) hax))
      (productQuasiAdditivity_cobGauge
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface hhm)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
                hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb))))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
            hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
            (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb)
            (finiteFaceScaleSingletonSliceAffine_of_faces
              (coherentFaceScales_of_FinalHM_positiveGauge
                hhm
                (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
                hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                  cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb))))
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            (selectedValueRelabel_of_cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
              hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
              (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
              (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb)
              (finiteFaceScaleSingletonSliceAffine_of_faces
                (coherentFaceScales_of_FinalHM_positiveGauge
                  hhm
                  (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
                  hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                  (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
                  (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
                    cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb))))))
        (faceScaleTripleProductValueAssociativity_of_selectedRelabeling
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle hhm (finalFaithfulBranchConventions_of_minimal minimal))
            hax (cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
            (cardinalGauge_hrel hhm (finalFaithfulBranchConventions_of_minimal minimal) hax)
            (fun {_A} _ _ _ q hq r _ hrn hrnd hrb =>
              cardinalGauge_hsupport hhm (finalFaithfulBranchConventions_of_minimal minimal) hax q hq r hrn hrnd hrb))
          (selectedValueRelabel_of_cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax))
        (selectedValueRelabel_of_cardinalGauge hhm (finalFaithfulBranchConventions_of_minimal minimal) hax) hax)

/-- **Top-level MI theorem: residual is only the 4-field minimal branch core plus
`pre_entropy`.**

`branch` has been reduced from six fields to the four-field
`MinimalBranchResidual` (boundary-transport core); `support_face` and
`singleton_scale` are discharged by
`supportFaceRepresentativeConvention_of_integralRepresentation` and
`branchSingletonScaleConvention_of_integralRepresentation`.  All product-gauge,
support-scale, value-relabelling, and singleton-slice conventions remain
eliminated.  Residual: `minimal` (4 fields) + `pre_entropy`. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_onlyMinimalBranchAndPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hres : ResidualMinimalBranchAndPreEntropy hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductSupportValueOrSingletonConventions
    hfad hhm hax
    { branch := finalFaithfulBranchConventions_of_minimal hres.minimal
      pre_entropy := hres.pre_entropy }

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
      FiniteSelectedPosteriorValueRelabelingFor
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
            hnorm
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
            hnorm
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
        (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
          product_normalized)
        current_product_gauge singleton_interaction)

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
    hconv.support_scale hconv.singleton_slice
    (finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
      hconv.product_normalized)
    hconv.current_product_gauge hconv.singleton_interaction hconv.harmless

/-- **Covariance-route conventions: the `product_normalized` pinning is replaced
by the HM relabel-covariance clause plus gauge relabelling-equivariance.**

This bundle is `FinalConstructedRepresentativeConventions` with the
`product_normalized` field (the exact-relabelling *pinning* `c = 1`, which is
false at subsingleton priors and — for a general representative — is a genuine
convention) **removed**.  In its place it carries:
* `hm_covariance : FinalHMRelabelCovariance hhm` — value-level naturality of the
  constructed HM functional under finite relabellings (a coherence clause on the
  classical HM interface, not an economic premise), and
* `gauge_relabel` — relabelling-equivariance of the chosen positive gauge (a
  harmless equivariance normalization, the same status as `scale_relabel`).

From these the selected relabelling package is *derived*
(`finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance`),
so `FiniteProductNormalizedSelectedRepresentativesFor` no longer appears. -/
structure FinalConstructedRepresentativeConventionsCovariance
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
  hm_covariance : FinalHMRelabelCovariance hhm
  gauge_relabel :
    ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A),
      gauge.gauge (Relabeling.relabelDist e q) = gauge.gauge q
  current_product_gauge :
    FiniteFaceScaleProductGaugeConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale)))
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax gauge scale_relabel support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale)))
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale hm_covariance gauge_relabel)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale)))))
  singleton_interaction :
    FiniteFaceScaleSingletonInteractionConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale)))
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax gauge scale_relabel support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale)))
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale hm_covariance gauge_relabel)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale)))))
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
        hax gauge scale_relabel support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax gauge scale_relabel support_scale))
        (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax gauge scale_relabel support_scale hm_covariance gauge_relabel)
        current_product_gauge singleton_interaction)

/-- **Exported MI route with `product_normalized` eliminated.**

Identical to `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` except that
the exact-relabelling *pinning* convention `product_normalized`
(`FiniteProductNormalizedSelectedRepresentativesFor`) is gone: the selected
relabelling package is derived from the HM relabel-covariance clause and gauge
equivariance carried by `FinalConstructedRepresentativeConventionsCovariance`.
`#print` confirms `FiniteProductNormalizedSelectedRepresentativesFor` is absent
from the convention structure this theorem depends on. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withCovariance
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventionsCovariance hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_withProductNormalizedSelectedRepresentatives
    hfad hhm hconv.branch hax hconv.gauge hconv.scale_relabel
    hconv.support_scale
    (finiteFaceScaleSingletonSliceAffine_of_faces
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm hconv.branch)
        hax hconv.gauge hconv.scale_relabel hconv.support_scale))
    (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
      hhm
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
        hhm hconv.branch)
      hax hconv.gauge hconv.scale_relabel hconv.support_scale
      hconv.hm_covariance hconv.gauge_relabel)
    hconv.current_product_gauge hconv.singleton_interaction hconv.harmless


/-- **Const-gauge covariance conventions: `gauge`, `scale_relabel`, and
`gauge_relabel` are eliminated by fixing the trivial gauge `constGaugeOne`.**

This bundle refines `FinalConstructedRepresentativeConventionsCovariance` by
choosing the constant gauge `fun _ => 1`.  Then:
* `gauge` is no longer a caller field (fixed to `constGaugeOne`);
* `gauge_relabel` holds by `rfl` (constant gauge);
* `scale_relabel` holds by `scaleRelabel_of_FinalHM_covariance` (R1: raw chain
  scale relabel-invariance from the HM covariance clause).
Only `support_scale` (the raw face-scale equation `eq:facescale`) remains as a
scale field; it is the genuine cross-cardinality content (the `t_n` target). -/
structure FinalConstructedRepresentativeConventionsConstGauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) where
  branch : FinalFaithfulBranchConventions hhm
  support_scale :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport),
      (constGaugeOne.gauge q / constGaugeOne.gauge r) *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).branch_agg.branchCoeff q r =
        (constGaugeOne.gauge q *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm branch)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale q) /
          (constGaugeOne.gauge r.restrictToSupport *
            (BranchAggregationCocycleNormalizedChainRule_of_faithful
              (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
                hhm branch)
              F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            ).scale_factorization.scale r.restrictToSupport)
  hm_covariance : FinalHMRelabelCovariance hhm
  current_product_gauge :
    FiniteFaceScaleProductGaugeConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale)))
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale)))
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale hm_covariance
            (fun {A B} _ _ _ _ _ _ _ _ => rfl))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale)))))
  singleton_interaction :
    FiniteFaceScaleSingletonInteractionConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale)))
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale)))
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale hm_covariance
            (fun {A B} _ _ _ _ _ _ _ _ => rfl))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale)))))
  harmless :
    FinalHarmlessConventions
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale)
      (productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale))
        (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax constGaugeOne
        (fun {A B} _ _ _ _ _ _ e q hq => by
          show (1:ℝ) * _ = (1:ℝ) * _
          rw [one_mul, one_mul]
          exact scaleRelabel_of_FinalHM_covariance hhm branch hax e q hq)
        support_scale hm_covariance
            (fun {A B} _ _ _ _ _ _ _ _ => rfl))
        current_product_gauge singleton_interaction)

/-- **Exported MI route with `product_normalized` eliminated.**

Identical to `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` except that
the exact-relabelling *pinning* convention `product_normalized`
(`FiniteProductNormalizedSelectedRepresentativesFor`) is gone: the selected
relabelling package is derived from the HM relabel-covariance clause and gauge
equivariance carried by `FinalConstructedRepresentativeConventionsConstGauge`.
`#print` confirms `FiniteProductNormalizedSelectedRepresentativesFor` is absent
from the convention structure this theorem depends on. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConstGauge
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventionsConstGauge hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_withProductNormalizedSelectedRepresentatives
    hfad hhm hconv.branch hax constGaugeOne
    (fun {A B} _ _ _ _ _ _ e q hq => by
      show (1:ℝ) * _ = (1:ℝ) * _
      rw [one_mul, one_mul]
      exact scaleRelabel_of_FinalHM_covariance hhm hconv.branch hax e q hq)
    hconv.support_scale
    (finiteFaceScaleSingletonSliceAffine_of_faces
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm hconv.branch)
        hax constGaugeOne
      (fun {A B} _ _ _ _ _ _ e q hq => by
        show (1:ℝ) * _ = (1:ℝ) * _
        rw [one_mul, one_mul]
        exact scaleRelabel_of_FinalHM_covariance hhm hconv.branch hax e q hq)
      hconv.support_scale))
    (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
      hhm
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
        hhm hconv.branch)
      hax constGaugeOne
      (fun {A B} _ _ _ _ _ _ e q hq => by
        show (1:ℝ) * _ = (1:ℝ) * _
        rw [one_mul, one_mul]
        exact scaleRelabel_of_FinalHM_covariance hhm hconv.branch hax e q hq)
      hconv.support_scale
      hconv.hm_covariance (fun {A B} _ _ _ _ _ _ _ _ => rfl))
    hconv.current_product_gauge hconv.singleton_interaction hconv.harmless



/-- **Cardinal-gauge conventions: `support_scale` eliminated.**

This bundle refines `FinalConstructedRepresentativeConventionsConstGauge` by
choosing the internally-defined cardinal gauge `cardinalGauge` (`g q :=
cardScaleT (card A) = t_{card A}`) instead of the trivial constant gauge.  With
this gauge the raw face-scale equation is a *theorem* (`cardinalGauge_hsupport`,
from the general embedding-defect reduction and the cocycle `cardDefect n m =
t_n/t_m`), so it is no longer a caller field.  The only remaining scale content is
the HM covariance clause (Tier A) and the branch/product/singleton faithfulness
data; `support_scale` (`FiniteSupportFaceScaleAssumptionsFor`) is absent. -/
structure FinalConstructedRepresentativeConventionsCardinalGauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) where
  branch : FinalFaithfulBranchConventions hhm
  hm_covariance : FinalHMRelabelCovariance hhm
  current_product_gauge :
    FiniteFaceScaleProductGaugeConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax))))
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax)
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax))))
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax) hm_covariance
            (cardinalGauge_gaugeRel hhm branch hax))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax)
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax))))))
  singleton_interaction :
    FiniteFaceScaleSingletonInteractionConventionFor
      (faceScaleProductPairwiseBilinearity_of_multiPieces
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface
            hhm)
          (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax))))
        (productInterceptPositiveLinear_of_FinalHM_positiveGauge
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax)
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax))))
        (faceScaleProductSlopeAffine_of_selectedRelabeling
          (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax) hm_covariance
            (cardinalGauge_gaugeRel hhm branch hax))
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax)
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax))))))
  harmless :
    FinalHarmlessConventions
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax))
      (productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm branch)
        hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax)
        (finiteFaceScaleSingletonSliceAffine_of_faces
          (coherentFaceScales_of_FinalHM_positiveGauge
            hhm
            (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
              hhm branch)
            hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax)))
        (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
          hhm
          (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
            hhm branch)
          hax (cardinalGauge hhm branch hax)
        (cardinalGauge_hrel hhm branch hax)
        (cardinalGauge_hsupport hhm branch hax) hm_covariance
            (cardinalGauge_gaugeRel hhm branch hax))
        current_product_gauge singleton_interaction)


/-- **Exported MI route with both `product_normalized` and `support_scale`
eliminated.**  Uses the cardinal gauge; the face-scale equation is discharged by
`cardinalGauge_hsupport`.  `#print` confirms `FiniteSupportFaceScaleAssumptionsFor`
is absent from the convention structure this theorem depends on. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withCardinalGauge
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventionsCardinalGauge hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_withProductNormalizedSelectedRepresentatives
    hfad hhm hconv.branch hax (cardinalGauge hhm hconv.branch hax)
    (cardinalGauge_hrel hhm hconv.branch hax)
    (cardinalGauge_hsupport hhm hconv.branch hax)
    (finiteFaceScaleSingletonSliceAffine_of_faces
      (coherentFaceScales_of_FinalHM_positiveGauge
        hhm
        (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
          hhm hconv.branch)
        hax (cardinalGauge hhm hconv.branch hax)
      (cardinalGauge_hrel hhm hconv.branch hax)
      (cardinalGauge_hsupport hhm hconv.branch hax)))
    (finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance
      hhm
      (faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle
        hhm hconv.branch)
      hax (cardinalGauge hhm hconv.branch hax)
      (cardinalGauge_hrel hhm hconv.branch hax)
      (cardinalGauge_hsupport hhm hconv.branch hax)
      hconv.hm_covariance (cardinalGauge_gaugeRel hhm hconv.branch hax))
    hconv.current_product_gauge hconv.singleton_interaction hconv.harmless

end TraceableAgency
