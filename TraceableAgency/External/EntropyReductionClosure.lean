/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.PreEntropyConstruction
import TraceableAgency.External.CanonicalPosteriorValue
import TraceableAgency.External.FiniteIntegralRepresentation

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

/-- Auditable finite Herstein--Milnor boundary.

The selected posterior value is obtained from the preference-free
`ClassicalHersteinMilnorMixtureTheoremAssumptions`, after Lean has derived all
of its ordinal hypotheses and constructed the posterior-law quotient as an
abstract convex mixture space.  The theorem field itself mentions no project
objects. In particular, posterior-law continuity is not an input:
`posteriorLawContinuity_of_axioms` proves it from primitive A2 and A1/A3/A4.
Lean constructs the required continuous barycentric coordinates by explicit
finite vertex insertion and derives the spread/merge sandwich.

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
  hm_theorem : ClassicalHersteinMilnorMixtureTheoremAssumptions.{v}

/-- Posterior-law sufficiency from the auditable final HM interface.

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

/-- Posterior-law continuity is derived from the primitive ordinal axioms,
not postulated by `FinalHMInterface`. -/
theorem posteriorLawContinuity_of_FinalHMInterface
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : TraceAxioms F) :
    PosteriorLawContinuity F :=
  posteriorLawContinuity_of_axioms
    F hhm.blackwell hax

/-- Raw finite HM representative before the scale gauge is fixed. -/
noncomputable def rawPosteriorValueRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : TraceAxioms F) :
    PosteriorValueRepresentation F :=
  posteriorValueRep_of_axioms_HMTheorem
    F hhm.blackwell hhm.hm_theorem hax

/-- Canonical posterior value representative.

At a boundary prior it first restricts to the positive-support simplex; on a
non-singleton full-support simplex it divides by the value of full revelation.
The normalization is derived from A1/A4 positivity and finite affine-utility
uniqueness, so exact support and relabelling covariance are theorems rather
than conventions. -/
noncomputable def posteriorValueRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : TraceAxioms F) :
    PosteriorValueRepresentation F :=
  canonicalPosteriorValueRepresentation
    hax
    (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)

/-- The finite affine integral representation used downstream is proved
internally from the selected HM representative's law extensionality and binary
affinity. -/
noncomputable opaque integralRepresentationData_of_FinalHMInterface
    (_hhm : FinalHMInterface.{u}) :
    FinitePosteriorIntegralRepresentationData.{u} :=
  ⟨finitePosteriorIntegralRepresentation_of_finite⟩

/-- **Exact relabelling covariance (naturality) of the constructed HM value
functional.**

The clause is stated for the canonical representative selected by
`posteriorValueRepresentation_of_FinalHMInterface`. -/
structure FinalSelectedRelabelCovariance
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

/-- The selected-representative covariance property yields exact relabelling
invariance for **any**
coherent face-scale representative whose value functional is (definitionally)
the constructed HM functional scaled by a gauge that is constant on relabelling
orbits.  For the special case of the constant gauge this is the identity used to
discharge `product_normalized` without the pinning normalization.

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
    (hcov : FinalSelectedRelabelCovariance hhm) :
    FiniteSelectedPosteriorValueRelabelingFor hfaces where
  V_relabel_eq := by
    intro _hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    rw [hVeq (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)),
      hVeq q (experimentOfChannel P)]
    exact hcov.V_relabel_eq hax eA eO q P

/-- The trivial (constant `1`) positive face-scale gauge.  Choosing this gauge
makes the gauge-equivariance normalizations (`gauge_relabel`) hold by `rfl` and
reduces the gauged `scale_relabel`/`support_scale` obligations to their raw
(ungauged) forms. -/
noncomputable def constGaugeOne : PositiveFaceScaleGauge.{u} where
  gauge := fun _ => 1
  gauge_pos := fun _ => one_pos

/-- **The singleton-slice affine normalization is a theorem** (for every coherent
face-scale representative).

On a subsingleton first factor `A`, the product left-slice value
`faceScaleProductLeftSliceValue q r R P = V (q⊗r) (P⊗R)` is `P`-invariant: the
first-factor observation is uninformative, so `P⊗R` and `U_A⊗R` induce the same
posterior law (`samePosteriorLawExp_prodChannel_singleton_fst`), and `V` respects
posterior-law equivalence.  Since also `V q (exp P) = 0` on a subsingleton
(`V_channel_eq_zero_of_subsingleton`), the affine relation holds with slope `a = 1`
and intercept the (`P`-independent) value at `U_A`.  This discharges the
`singleton_slice` normalization with no assumption. -/
theorem finiteFaceScaleSingletonSliceAffine_of_faces
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces where
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
finite action relabellings for a relabel-natural selected value. Atomic tangent
realization transports the linear parts without imposing any naturality on an
arbitrary representing test function. -/
theorem branchPathCoeff_relabel_of_atomic_eval
    {F : PrefFamily.{u}}
    (hint : FinitePosteriorIntegralRepresentationAssumptions.{u})
    (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hrelab :
      ∀ {A B O Y : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        [Fintype O] [DecidableEq O]
        [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y)
        (q : Dist A) (P : Channel A O),
        hV.V (Relabeling.relabelDist eA q)
            (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hV.V q (experimentOfChannel P))
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
  set ηA : PosteriorLawSigned A :=
    posteriorLawDifferenceExp r (experimentOfChannel idA) (experimentOfChannel UA) with hηA_def
  set ηB : PosteriorLawSigned B :=
    relabelPosteriorLawSigned eA ηA with hηB_def
  have hηA_atomic : PosteriorLawSigned.AtomicLinear ηA :=
    posteriorLawDifferenceExp_atomicLinear _ _ _
  have hηA_tan : PosteriorLawTangent ηA := posteriorLawDifferenceExp_tangent _ _ _
  have hηB_atomic : PosteriorLawSigned.AtomicLinear ηB :=
    hηA_atomic.relabel eA
  have hηB_tan : PosteriorLawTangent ηB := hηA_tan.relabel eA
  have hLA_r :
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV r ηA =
        hV.V r (experimentOfChannel idA) - hV.V r (experimentOfChannel UA) := by
    simpa [hηA_def] using
      ((finiteAffineLinearPartAssumptions_of_integralRepresentation hint).value_difference
        F hV r (experimentOfChannel idA) (experimentOfChannel UA)).symm
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
    affineLinearPart_relabel_atomicTangent
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint)
      hV hrelab eA q hq ηA hηA_atomic hηA_tan
  have hT2 :
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV
          (Relabeling.relabelDist eA r) ηB =
        (finiteAffineLinearPartAssumptions_of_integralRepresentation hint).linearPart F hV r ηA :=
    affineLinearPart_relabel_atomicTangent
      (finiteAffineLinearPartAssumptions_of_integralRepresentation hint)
      hV hrelab eA r hr ηA hηA_atomic hηA_tan
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_interactionCollapse
    (InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax)

/-- Cross-prior block representation produced by the minimal full
pre-entropy closure route and the product-quasi-additive blockbridge. -/
noncomputable def crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_preUniversalBridge
    (finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod)
    hax
    (entropyReduction_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax)
    rfl

/-- Entropy regularity for the minimal full pre-entropy closure route. -/
theorem entropyRegularity_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    EntropyRegularity F
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction :=
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (k : K) (q : Dist (Act k)) (hq : q.FullSupport) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
        (blockEmbedDist Act k q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun q := by
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
  rw [hnorm.block_value.block_face_value hax Act k q hq]
  rw [hnorm.block_scale.block_face_scale hax Act k q hq]
  rfl

/-- Full-support relabeling invariance for the concrete entropy candidate
constructed by the minimal full pre-entropy closure route. -/
theorem Hfun_relabel_fullSupport_of_fullPreEntropyClosure_minimal
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
        (Relabeling.relabelDist e q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun q := by
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
          hfaces hhm huniq hprod haff hnorm hax).scale_coherence.scale_universal
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    ∀ (t : Dist (supportSubtype q)),
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)) =
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun t := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  intro t
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hreg : EntropyRegularity F hcross.entropy_reduction :=
    entropyRegularity_of_fullPreEntropyClosure_minimal
      hcard hfaces hhm huniq hprod haff hnorm hax
  let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
    hfunSupportRestriction_of_boundaryIdentity hsupport hid
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
      hhm huniq haff hnorm hax
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (k : K) (q : Dist (Act k)) :
    (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun
        (blockEmbedDist Act k q) =
      (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun q := by
  by_cases hq : q.FullSupport
  · exact Hfun_blockEmbed_fullSupport_of_fullPreEntropyClosure_minimal
      hhm huniq haff hnorm hax Act k q hq
  · let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
      normalizedValueSupportBoundary_of_cardinalBoundary hcard
    let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
      hfunBoundaryIdentity_of_cardinalBoundary hcard
    let hreg : EntropyRegularity F hcross.entropy_reduction :=
      entropyRegularity_of_fullPreEntropyClosure_minimal
        hcard hfaces hhm huniq hprod haff hnorm hax
    let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
      hfunSupportRestriction_of_boundaryIdentity hsupport hid
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
        hhm huniq haff hnorm hax
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O]
    (P : Channel A O) (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    posteriorLawIntegral q P
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun =
      posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
        (crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
          hfaces hhm huniq hprod haff hnorm hax).entropy_reduction.Hfun := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
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
      hcard hhm huniq haff hnorm hax q
      (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)

/-- Coarse-reveal entropy reduction for the concrete entropy candidate of the
minimal full pre-entropy closure route. -/
theorem coarseReveal_entropyReduction_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (p : Dist K) (q : ∀ k, Dist (Act k)) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    hcross.entropy_reduction.Hfun (sigmaDist p q) =
      normalizedValue hcross.entropy_reduction.scale_coherence (sigmaDist p q)
        (coarseRevealChannel Act) +
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
        hcross.entropy_reduction.Hfun := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
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
  · let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
      normalizedValueSupportBoundary_of_cardinalBoundary hcard
    let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
      hfunBoundaryIdentity_of_cardinalBoundary hcard
    let hreg : EntropyRegularity F hcross.entropy_reduction :=
      entropyRegularity_of_fullPreEntropyClosure_minimal
        hcard hfaces hhm huniq hprod haff hnorm hax
    let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
      hfunSupportRestriction_of_boundaryIdentity hsupport hid
    haveI : Nonempty (supportSubtype s) := supportSubtype_nonempty s
    have hH :
        hcross.entropy_reduction.Hfun s =
          hcross.entropy_reduction.Hfun s.restrictToSupport :=
      hhfun.Hfun_support_restrict F hax hcross hreg s
    have hV :
      normalizedValue hcross.entropy_reduction.scale_coherence s C =
          normalizedValue hcross.entropy_reduction.scale_coherence
            s.restrictToSupport (Channel.restrictToSupport C s) :=
      normalizedValue_support_restrict_of_boundary hsupport F hax hcross C s
    have hI :
        posteriorLawIntegral s C hcross.entropy_reduction.Hfun =
          posteriorLawIntegral s.restrictToSupport (Channel.restrictToSupport C s)
            hcross.entropy_reduction.Hfun :=
      posteriorLawIntegral_supportRestrict_Hfun_of_fullPreEntropyClosure_minimal
        hcard hhm huniq haff hnorm hax C s
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  let hsupport : FiniteNormalizedValueSupportBoundaryAssumptions.{u} :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid : FiniteHfunBoundaryIdentityAssumptions.{u} :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hrestricted : FiniteRestrictedCoarseRevealValueAssumptions.{u} :=
    restrictedCoarseRevealValue_of_cardinalBoundary hcard
  let hreg : EntropyRegularity F hcross.entropy_reduction :=
    entropyRegularity_of_fullPreEntropyClosure_minimal
      hcard hfaces hhm huniq hprod haff hnorm hax
  let hhfun : FiniteHfunSupportRestrictionAssumptions.{u} :=
    hfunSupportRestriction_of_boundaryIdentity hsupport hid
  change SatisfiesFiniteFaddeevRecursion hcross.entropy_reduction.Hfun
  intro K _ _ _ Act _ _ _ _ p q
  have hER :=
    coarseReveal_entropyReduction_of_fullPreEntropyClosure_minimal
      (hcard := hcard) (hhm := hhm) (huniq := huniq)
      (haff := haff) (hnorm := hnorm) (hax := hax)
      (Act := Act) (p := p) (q := q)
  have hV :=
    coarseReveal_value_eq_Hfun_of_axioms
      hsupport hhfun hrestricted F hax hcross hreg Act p q
  have hInt :
      posteriorLawIntegral (sigmaDist p q) (coarseRevealChannel Act)
          hcross.entropy_reduction.Hfun =
        ∑ k, p k * hcross.entropy_reduction.Hfun (q k) := by
    exact posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
      hcross.entropy_reduction.Hfun Act p q
      (fun k =>
        Hfun_blockEmbed_of_fullPreEntropyClosure_minimal
          (hcard := hcard) (hhm := hhm) (huniq := huniq)
          (haff := haff) (hnorm := hnorm) (hax := hax)
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    let hcross :=
      crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
        hfaces hhm huniq hprod haff hnorm hax
    FaddeevRecursionForm F hcross.entropy_reduction := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  exact
    { regularity :=
        entropyRegularity_of_fullPreEntropyClosure_minimal
          hcard hfaces hhm huniq hprod haff hnorm hax
      grouping_recursion :=
        satisfiesFiniteFaddeevRecursion_of_fullPreEntropyClosure_minimal
          (hcard := hcard) (hhm := hhm) (huniq := huniq)
          (haff := haff) (hnorm := hnorm) (hax := hax) }

/-- `FaddeevEntropyForm` for the concrete entropy candidate produced by the
minimal full pre-entropy closure route.  The only Faddeev/Shannon input is the
classical finite Faddeev theorem interface. -/
noncomputable def FaddeevEntropyForm_of_fullPreEntropyClosure_minimal
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    FaddeevEntropyForm F := by
  let hcross :=
    crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal
      hfaces hhm huniq hprod haff hnorm hax
  let hrecForm : FaddeevRecursionForm F hcross.entropy_reduction :=
    faddeevRecursionForm_of_fullPreEntropyClosure_minimal
      (hcard := hcard) (hhm := hhm) (huniq := huniq)
      (haff := haff) (hnorm := hnorm) (hax := hax)
  let hsupport :=
    normalizedValueSupportBoundary_of_cardinalBoundary hcard
  let hid :=
    hfunBoundaryIdentity_of_cardinalBoundary hcard
  let hhfun :=
    hfunSupportRestriction_of_boundaryIdentity hsupport hid
  let hstandard :
      FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun :=
    finiteFaddeevStandardHypotheses_of_axioms hax hcross hrecForm
      (fun q =>
        hhfun.Hfun_support_restrict F hax hcross hrecForm.regularity q)
  let hex :=
    hfad.of_standard_hypotheses
      hcross.entropy_reduction.Hfun hstandard
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    FaddeevEntropyForm F :=
  FaddeevEntropyForm_of_fullPreEntropyClosure_minimal
    (hcard := hcard) (hfad := hfad) (hhm := hhm)
    (huniq := classicalFiniteAffineUtilityUniquenessAssumptions)
    (haff := haff) (hnorm := hnorm) (hax := hax)

/-- Full-support MI representation package obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem fullSupportSufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    FullSupportSufficiencyMIPackage F :=
  FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F
    (FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Full-support block MI representation package obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem fullSupportBlockMI_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    FullSupportBlockMI F :=
  FullSupportBlockMI_of_FaddeevEntropyForm F
    (FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Boundary extension for MI representation obtained internally from the
support-restriction theorem and the full-support block MI package. -/
theorem fullSupportMIRepExtendsToBoundary_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    FullSupportMIRepExtendsToBoundary F :=
  FullSupportMIRepExtendsToBoundary_of_supportRestriction F
    (fullSupportBlockMI_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Final sufficiency package obtained from the closed pre-entropy spine,
internal boundary extension, and the classical finite Faddeev theorem
interface. -/
theorem sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    SufficiencyMIPackage F :=
  (fullSupportMIRepExtendsToBoundary_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard := hcard) (hfad := hfad) (hhm := hhm)
    (haff := haff) (hnorm := hnorm) (hax := hax))
    hax
    (fullSupportSufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Final mutual-information representation obtained from the closed
pre-entropy spine and the classical finite Faddeev theorem interface. -/
theorem MIRep_of_fullPreEntropyClosure_minimal_internalUniqueness
    (hcard : FiniteCardinalSupportBoundaryAssumptions.{u})
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hnorm : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
    (hax : TraceAxioms F) :
    MIRep F :=
  MIRep_of_SufficiencyMIPackage F
    (sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
      (hcard := hcard) (hfad := hfad) (hhm := hhm)
      (haff := haff) (hnorm := hnorm) (hax := hax))

/-- Left-slice affine transform for the selected face-scale representative
from HM public-mixture affinity, A7 same-order transport, internal finite
affine-utility uniqueness, and the singleton slice normalization. -/
theorem finiteFaceScaleProductLeftSliceAffineTransform_of_HM
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces :=
  faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
    (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
    (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
    (faceScaleProductLeftSliceSameOrder_of_A7 hfaces)
    hsingle
    classicalFiniteAffineUtilityUniquenessAssumptions

/-- Exact boundary-to-positive-support transport for the single value
representative carried by a coherent face-scale structure.  This deliberately
contains no universal quantification over alternative representatives. -/
structure FiniteBoundaryValueSupportReadFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  boundary_value_support :
    ∀ {A O : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (q : Dist A) [Nonempty (supportSubtype q)] (P : Channel A O),
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) =
        hfaces.branch_result.branch_agg.value_rep.V q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q))

/-- Block support-face value transport for the pre-entropy route, stated as a
theorem-style transport input rather than a representative normalization. -/
structure FiniteBlockSupportFaceValueTransportFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_value :
    ∀ (_hax : TraceAxioms F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.branch_agg.value_rep.V
        (blockEmbedDist Act k q)
        (experimentOfChannel
          (Channel.idChannel : Channel ((k : K) × Act k) ((k : K) × Act k))) =
      fullRevelationValueForFaceScales hfaces q

/-- Block support-face scale transport for the pre-entropy route. -/
structure FiniteBlockSupportFaceScaleTransportFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_scale :
    ∀ (_hax : TraceAxioms F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.scale_factorization.scale
        (blockEmbedDist Act k q) =
      hfaces.branch_result.scale_factorization.scale q

/-- Block value read on the support face of the embedded block posterior.

The full-revelation continuation is evaluated after restricting the embedded
prior to its positive support and using the identity channel on that support
face.  This is the support-read counterpart of the ambient
`FiniteBlockSupportFaceValueTransportFor`. -/
structure FiniteBlockSupportFaceValueSupportReadFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_value_support :
    ∀ (_hax : TraceAxioms F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.branch_agg.value_rep.V
        (blockEmbedDist Act k q).restrictToSupport
        (experimentOfChannel
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q)))) =
      fullRevelationValueForFaceScales hfaces q

/-- Block scale read on the support face of the embedded block posterior. -/
structure FiniteBlockSupportFaceScaleSupportReadFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  block_face_scale_support :
    ∀ (_hax : TraceAxioms F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (k : K) (q : Dist (Act k)) (_hq : q.FullSupport),
      hfaces.branch_result.scale_factorization.scale
        (blockEmbedDist Act k q).restrictToSupport =
      hfaces.branch_result.scale_factorization.scale q

/-- The pre-entropy representative/gauge facts needed by the final constructor,
with normalization terminology removed from the public-facing route. -/
structure PreEntropyRepresentativeGaugeKnownResults
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  coordinate_value :
    FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces
  coordinate_scale :
    FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces
  block_value :
    FiniteBlockSupportFaceValueTransportFor hfaces
  block_scale :
    FiniteBlockSupportFaceScaleTransportFor hfaces
  reference_z :
    FiniteProductReferenceZNormalizationFor hfaces hprod
  universal_singleton :
    FiniteUniversalScaleSingletonNormalizationFor hfaces

theorem coordinateSupportFaceValueIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces) :
    FiniteCoordinateSupportFaceValueIdentificationFor hfaces where
  first_coordinate_face_value := h.first_coordinate_face_value
  second_coordinate_face_value := h.second_coordinate_face_value

theorem coordinateSupportFaceScaleIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces) :
    FiniteCoordinateSupportFaceScaleIdentificationFor hfaces where
  first_coordinate_face_scale := h.first_coordinate_face_scale
  second_coordinate_face_scale := h.second_coordinate_face_scale

theorem blockSupportFaceValueIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteBlockSupportFaceValueTransportFor hfaces) :
    FiniteBlockSupportFaceValueIdentificationFor hfaces where
  block_face_value := h.block_face_value

theorem blockSupportFaceScaleIdentification_of_transport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteBlockSupportFaceScaleTransportFor hfaces) :
    FiniteBlockSupportFaceScaleIdentificationFor hfaces where
  block_face_scale := h.block_face_scale

theorem universalScaleSingleton_of_normalization
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (h : FiniteUniversalScaleSingletonNormalizationFor hfaces) :
    FiniteUniversalScaleSingletonNormalizationFor hfaces where
  scale_eq_of_subsingleton := h.scale_eq_of_subsingleton

theorem preEntropyRepresentativeGaugeNormalizations_of_knownResults
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (h : PreEntropyRepresentativeGaugeKnownResults hfaces hprod) :
    PreEntropyRepresentativeGaugeNormalizations hfaces hprod where
  coordinate_value :=
    coordinateSupportFaceValueIdentification_of_transport h.coordinate_value
  coordinate_scale :=
    coordinateSupportFaceScaleIdentification_of_transport h.coordinate_scale
  block_value :=
    blockSupportFaceValueIdentification_of_transport h.block_value
  block_scale :=
    blockSupportFaceScaleIdentification_of_transport h.block_scale
  reference_z := h.reference_z
  universal_singleton :=
    universalScaleSingleton_of_normalization h.universal_singleton

/-- Harmless final inputs stated as known transport/normalization results. -/
structure FinalHarmlessKnownResults
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  pre_entropy :
    PreEntropyRepresentativeGaugeKnownResults hfaces hprod

/-- Posterior integral representation supplied by the HM component of the
final interface. -/
noncomputable def posteriorIntegralRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u}) :
    FinitePosteriorIntegralRepresentationAssumptions.{u} :=
  finitePosteriorIntegralRepresentation_of_HM
    (integralRepresentationData_of_FinalHMInterface hhm)

/-- Affine linear-part package supplied by the internally proved posterior
integral representation.  Defining it from the named posterior package keeps
the two downstream views definitionally synchronized without unfolding the
finite construction itself. -/
noncomputable def affineLinearPart_of_FinalHMInterface
    (hhm : FinalHMInterface.{u}) :
    FiniteAffineLinearPartAssumptions.{u} :=
  finiteAffineLinearPartAssumptions_of_integralRepresentation
    (posteriorIntegralRepresentation_of_FinalHMInterface hhm)

/-- Hax-specific singleton branch package whose arbitrary singleton coefficient
is chosen to be the selected branch path scale `β(q,u_A)`.

The value-zero field is still proved from the HM/integral support-face theorem.
The coefficient choice is scale-aware, so it is the right package for removing
the old singleton scale-factorization normalization on the selected branch route. -/
noncomputable def finalHMSingletonScaleNormalizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) :
    FiniteBranchSingletonScaleNormalizationFor F
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  refine
    { singletonCoeff := fun {A} _ _ _ q _ =>
        hpath.branchPathCoeff q (Dist.uniform (A := A))
      singletonCoeff_pos := ?_
      singleton_branch_value_zero := ?_ }
  · intro A _ _ _ q _r hq _hr_singleton
    by_cases hnd :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b
    · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
        hq Dist.uniform_fullSupport hnd
    · have hpath_eq :
          hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hnd]
      rw [hpath_eq]
      exact one_pos
  · intro A O _ _ _ _ _ r hr_singleton P
    change canonicalPosteriorValue
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      r (experimentOfChannel P) = 0
    by_cases hr : r.FullSupport
    · rcases hr_singleton with ⟨a, _ha, huniq⟩
      have hsub : Subsingleton A :=
        ⟨fun x y => (huniq x (hr x)).trans (huniq y (hr y)).symm⟩
      simp [canonicalPosteriorValue, hr, hsub]
    · have hsub : Subsingleton (supportSubtype r) :=
        supportSubtype_subsingleton_of_singleton_support r hr_singleton
      simp [canonicalPosteriorValue, hr, hsub]

/-- The selected singleton coefficient is definitionally the selected branch
path scale to the uniform prior. -/
theorem finalHMSingletonScaleNormalizationFor_coeff
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) :
    (finalHMSingletonScaleNormalizationFor hhm hax).singletonCoeff q r =
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q (Dist.uniform (A := A)) := by
  rfl

/-- Canonical full-revelation normalization makes the selected value
functional exactly covariant under finite action/outcome relabellings. -/
theorem finalSelectedRelabelCovariance_of_canonicalNormalization
    (hhm : FinalHMInterface.{u}) :
    FinalSelectedRelabelCovariance hhm where
  V_relabel_eq := by
    intro F hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    classical
    change canonicalPosteriorValue
        (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
        (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      canonicalPosteriorValue
        (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
        q (experimentOfChannel P)
    exact canonicalPosteriorValue_relabel hax
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      eA eO q P

/-- Relabelling covariance in the only form needed by branch aggregation:
equality after applying an atomic tangent signed posterior law.  This is
representation-independent; in particular it does not assert that an
arbitrarily chosen integral test function is pointwise natural. -/
theorem finalHM_affineLinearPart_relabel_atomic_eval
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (s : Dist A) (hs : s.FullSupport)
    (η : PosteriorLawSigned A)
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    relabelPosteriorLawSigned e η
        ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue
          F (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (Relabeling.relabelDist e s)) =
      η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue
        F (posteriorValueRepresentation_of_FinalHMInterface hhm hax) s) := by
  have h :=
    affineLinearPart_relabel_atomicTangent
      (affineLinearPart_of_FinalHMInterface hhm)
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ((finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq hax)
      e s hs η hηatomic hηtan
  exact h

/-- The selected value representative is coherent with restriction to the
positive support face.  This is the selected-representative version of the old
support-face value normalization. -/
theorem finalHM_supportFaceValueTransport
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O) :
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
        (experimentOfChannel P) =
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
        r.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P r)) := by
  change canonicalPosteriorValue
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      r (experimentOfChannel P) =
    canonicalPosteriorValue
      (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax)
      r.restrictToSupport
      (experimentOfChannel (Channel.restrictToSupport P r))
  exact canonicalPosteriorValue_supportFace hax
    (rawPosteriorValueRepresentation_of_FinalHMInterface hhm hax) r P

/-- Selected boundary-value transport for the constructed representative,
packaged in
the branch-aggregation interface that only fixes the representative actually
used downstream. -/
theorem finalHM_boundaryValueTransportFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) :
    FiniteBranchBoundaryValueTransportFor
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax) where
  boundary_value_transport := by
    intro A O _ _ _ _ _ r _ P
    exact finalHM_supportFaceValueTransport hhm hax r P

/-- Boundary linear-part transport from the selected integral representation plus the
support-face marginal-value transport normalization. -/
theorem boundaryLinearPartTransport_of_FinalHM_marginalTransport
    (hhm : FinalHMInterface.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAssumptions
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        hboundary) :
    FiniteBoundaryLinearPartTransportAssumptions
      (affineLinearPart_of_FinalHMInterface hhm)
      hboundary :=
  boundaryLinearPartTransport_of_integralRepresentation
    (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
    hboundary hmarginal

/-- The hax-specific singleton coefficient `β(q,u_A)` satisfies the singleton
scale-factorization clause.  This is the theorem that removes the old selected
singleton scale-factorization normalization once the final route is switched to the
`...For` branch package. -/
theorem finalHMSingletonScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions
        (affineLinearPart_of_FinalHMInterface hhm) hboundary) :
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    let hvalue := finalHM_boundaryValueTransportFor hhm hax
    FiniteBranchScaleFactorizationSingletonNormalization
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  change FiniteBranchScaleFactorizationSingletonNormalization
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
  refine
    { scale_pos_singleton := ?_
      branchCoeff_factorization_singleton := ?_ }
  · intro A _ _ _ q hq _hr_singleton
    show 0 <
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q (Dist.uniform (A := A))
    rw [show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q (Dist.uniform (A := A)) =
        branchCoeffFromTangentRepParts hpath hboundary hsingle q
          (Dist.uniform (A := A)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
    by_cases hnd :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b
    · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
        hq Dist.uniform_fullSupport hnd
    · have hpath_eq :
          hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hnd]
      rw [hpath_eq]
      exact one_pos
  · intro A O₁ _ _ _ _ _ q hq P₁ o₁ hpos hsingle_support
    let r : Dist A := Channel.posterior P₁ q o₁
    have hnotnd :
        ¬ ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      exact not_nondegenerate_of_singleton_support r
        (by simpa [r] using hsingle_support)
    have hscale_eq : ∀ s : Dist A,
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).scale s =
          hpath.branchPathCoeff s (Dist.uniform (A := A)) := by
      intro s
      show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff s (Dist.uniform (A := A)) =
          hpath.branchPathCoeff s (Dist.uniform (A := A))
      rw [show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff s (Dist.uniform (A := A)) =
          branchCoeffFromTangentRepParts hpath hboundary hsingle s
            (Dist.uniform (A := A)) from rfl]
      simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
    by_cases hrfull : r.FullSupport
    · have hsub : Subsingleton A := by
        rcases hsingle_support with ⟨c, _hc, huniq⟩
        refine ⟨?_⟩
        intro a b
        exact (huniq a (hrfull a)).trans (huniq b (hrfull b)).symm
      have hU_notnd :
          ¬ ∃ a b : A, a ≠ b ∧
            0 < (Dist.uniform (A := A)) a ∧
            0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hne, _ha, _hb⟩
        exact hne (Subsingleton.elim a b)
      have hpath_qr_one : hpath.branchPathCoeff q r = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, hrfull, dif_pos]
        rw [dif_neg hnotnd]
      have hscale_q_one :
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale q = 1 := by
        rw [hscale_eq q]
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      have hscale_r_one :
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale r = 1 := by
        rw [hscale_eq r]
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hrfull, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff q (Channel.posterior P₁ q o₁) =
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale q /
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale (Channel.posterior P₁ q o₁)
      rw [show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff q r =
          branchCoeffFromTangentRepParts hpath hboundary hsingle q r from rfl]
      simp only [r, branchCoeffFromTangentRepParts, hrfull, dif_pos]
      rw [hpath_qr_one, hscale_q_one, hscale_r_one]
      norm_num
    · have hpath_r_one :
          hpath.branchPathCoeff r (Dist.uniform (A := A)) = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
        rw [dif_neg hrfull]
      have hbranch_qr :
          (faithfulBranchAggregationStructure_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).branchCoeff q r =
            hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
          rw [show
            (faithfulBranchAggregationStructure_of_componentsFor
              F hax hV hlin hpath hboundary hsingle hvalue hcoeff
            ).branchCoeff q r =
              branchCoeffFromTangentRepParts hpath hboundary hsingle q r from rfl]
          unfold branchCoeffFromTangentRepParts
          rw [dif_neg hrfull]
          rw [dif_neg hnotnd]
          simpa [hsingle] using
            finalHMSingletonScaleNormalizationFor_coeff hhm hax q r
      show
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff
        ).branchCoeff q (Channel.posterior P₁ q o₁) =
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale q /
          (faithfulBranchFullSupportScale_of_componentsFor
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff
          ).scale (Channel.posterior P₁ q o₁)
      rw [show (Channel.posterior P₁ q o₁) = r from rfl]
      rw [hbranch_qr, hscale_eq q, hscale_eq r, hpath_r_one]
      rw [div_one]

/-- Canonical selected boundary coefficient for the final HM route.

For a nondegenerate boundary posterior, the coefficient is fixed to be the
selected tangent path coefficient from the ambient prior to the uniform
basepoint.  This is the normalization under which boundary scale factorization
becomes a theorem rather than a separate normalization field. -/
noncomputable def finalHMBoundaryCoefficientScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) :
    FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u} := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  refine
    { boundaryCoeff := fun {A} _ _ _ q _ =>
        hpath.branchPathCoeff q (Dist.uniform (A := A))
      boundaryCoeff_pos := ?_ }
  intro A _ _ _ q r hq _hr_nonempty hrnd _hr_boundary
  have hU_nd :
      ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
    obtain ⟨a, b, hab, _ha, _hb⟩ := hrnd
    exact ⟨a, b, hab, Dist.uniform_fullSupport a,
      Dist.uniform_fullSupport b⟩
  exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
    hq Dist.uniform_fullSupport hU_nd

/-- Boundary coefficient normalization obtained from the proved atomic
support-face tangent scalar, rather than from the older uniform-path gauge
choice. -/
noncomputable def finalHMBoundaryAtomicCoefficientScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) :
    FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u} :=
  boundaryCoefficientScaleNormalization_of_A1_atomicLinearTangentSpanning
    (affineLinearPart_of_FinalHMInterface hhm)
    (atomicLinearTangentSpanning_of_atomic
      finiteAtomicPosteriorTangentSpanning)
    F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)

/-- Corrected support-face marginal transport for the selected final HM route.

This is the theorem-strength boundary actually proved from A1/A6 and atomic
tangent spanning: the support-face scalar relation is required only for
atomic-linear feasible tangents, which is exactly the domain generated by
continuation experiment differences in the branch formula. -/
structure FinalSupportFaceMarginalValueTransportAtomicFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) : Prop where
  support_face_marginalValue_scalar_atomic :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport)
      (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawSigned.AtomicLinear η →
      PosteriorLawTangent η →
      η (fun d =>
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax) q
          (Channel.actionPushforward d (supportIncludeKernel r))) =
        (boundaryFaceScale_of_coefficientScaleNormalization
          (finalHMBoundaryAtomicCoefficientScaleFor hhm hax)
        ).boundaryCoeff q r *
          η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
            (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
            r.restrictToSupport)

/-- The corrected atomic support-face marginal transport is internal to the
final HM route and the paper axioms. -/
theorem finalSupportFaceMarginalValueTransportAtomic_of_FinalHM_TraceAxioms
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) :
    FinalSupportFaceMarginalValueTransportAtomicFor hhm hax where
  support_face_marginalValue_scalar_atomic := by
    intro A _ _ _ q r hq _ hr_nonempty hr_nondegenerate _hr_boundary η hηatomic hηtan
    classical
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let htangent :=
      atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning
    have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
        0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
      obtain ⟨a, b, hab, ha, hb⟩ := hr_nondegenerate
      refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
      · intro h
        exact hab (congrArg Subtype.val h)
      · rw [Dist.restrictToSupport_apply]
        exact ha
      · rw [Dist.restrictToSupport_apply]
        exact hb
    have hrel :=
      boundaryAtomicLinearTangentCoeffOfA1Spanning_relation
        hlin htangent F hax hV q r hq hrs_nd η hηatomic hηtan
    simpa [hlin, hV, htangent, finalHMBoundaryAtomicCoefficientScaleFor,
      affineLinearPart_of_FinalHMInterface,
      boundaryFaceScale_of_coefficientScaleNormalization,
      boundaryCoefficientScaleNormalization_of_A1_atomicLinearTangentSpanning,
      finiteAffineLinearPartAssumptions_of_integralRepresentation]
      using hrel

/-- Repackage the selected atomic transport theorem under the lower-level
fixed-representative interface. -/
theorem supportFaceMarginalValueTransportAtomic_of_FinalHMFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (htransport : FinalSupportFaceMarginalValueTransportAtomicFor hhm hax) :
    FiniteSupportFaceMarginalValueTransportAtomicFor
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization
        (finalHMBoundaryAtomicCoefficientScaleFor hhm hax)) where
  support_face_marginalValue_scalar_atomic := by
    intro A _ _ _ q r hq _ hrn hrnd hrb η hηatomic hηtan
    exact htransport.support_face_marginalValue_scalar_atomic
      q r hq hrn hrnd hrb η hηatomic hηtan

/-- The theorem-strength support-face marginal transport required by the
canonical selected branch route.

Unlike the old normalization bundle, this fixes the boundary coefficient
internally to `finalHMBoundaryCoefficientScaleFor`.  The remaining content is
the actual support-face scalar theorem for the HM marginal test function. -/
structure FinalSupportFaceMarginalValueTransportFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) : Prop where
  support_face_marginalValue_scalar :
    ∀ (F' : PrefFamily.{u}) (hax' : TraceAxioms F')
      (hV' : PosteriorValueRepresentation F')
      {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport)
      [Nonempty (supportSubtype r)]
      (_hr_nonempty : ∃ a : A, 0 < r a)
      (_hr_nondegenerate : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hr_boundary : ¬ r.FullSupport)
      (η : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawTangent η →
      η (fun d =>
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F'
          hV' q
          (Channel.actionPushforward d (supportIncludeKernel r))) =
        (boundaryFaceScale_of_coefficientScaleNormalization
          (finalHMBoundaryCoefficientScaleFor hhm hax)
        ).boundaryCoeff q r *
          η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F'
            hV' r.restrictToSupport)

/-- Repackage the canonical selected marginal-transport theorem under the
historical interface consumed by the lower-level branch constructors. -/
theorem supportFaceMarginalValueTransport_of_FinalHMFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (htransport : FinalSupportFaceMarginalValueTransportFor hhm hax) :
    FiniteSupportFaceMarginalValueTransportAssumptions
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization
        (finalHMBoundaryCoefficientScaleFor hhm hax)) where
  support_face_marginalValue_scalar := by
    intro F' hax' hV' A _ _ _ q r hq _ hrn hrnd hrb η hη
    exact htransport.support_face_marginalValue_scalar
      F' hax' hV' q r hq hrn hrnd hrb η hη

/-- Boundary scale factorization for the canonical selected boundary
coefficient.

Once the boundary coefficient is fixed as the tangent coefficient to the
uniform basepoint, the boundary case of branch scale factorization is just the
definition of the full-support base scale; no separate boundary-scale
normalization is needed. -/
theorem finalHMBoundaryScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (htransport : FinalSupportFaceMarginalValueTransportFor hhm hax) :
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        (finalHMBoundaryCoefficientScaleFor hhm hax)
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    let hvalue := finalHM_boundaryValueTransportFor hhm hax
    let hmarginal :=
      supportFaceMarginalValueTransport_of_FinalHMFor
        hhm hax htransport
    let hcoeff :=
      boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
        (boundaryLinearPartTransport_of_FinalHM_marginalTransport
          hhm hboundary hmarginal)
    FiniteBranchScaleFactorizationBoundaryTransportAssumptions
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization
      (finalHMBoundaryCoefficientScaleFor hhm hax)
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  let hmarginal :=
    supportFaceMarginalValueTransport_of_FinalHMFor
      hhm hax htransport
  let hcoeff :=
    boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
      (boundaryLinearPartTransport_of_FinalHM_marginalTransport
        hhm hboundary hmarginal)
  change FiniteBranchScaleFactorizationBoundaryTransportAssumptions
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
  refine ⟨?_⟩
  intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hrnd hrb
  let r : Dist A := Channel.posterior P₁ q o₁
  have hscale_eq : ∀ s : Dist A,
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).scale s =
        hpath.branchPathCoeff s (Dist.uniform (A := A)) := by
    intro s
    show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff s (Dist.uniform (A := A)) =
        hpath.branchPathCoeff s (Dist.uniform (A := A))
    rw [show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff s (Dist.uniform (A := A)) =
        branchCoeffFromTangentRepParts hpath hboundary hsingle s
          (Dist.uniform (A := A)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  have hpath_r_one :
      hpath.branchPathCoeff r (Dist.uniform (A := A)) = 1 := by
    simp only [hpath,
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
    rw [dif_neg (by simpa [r] using hrb)]
  have hbranch_qr :
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q r =
        hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
    rw [show
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).branchCoeff q r =
        branchCoeffFromTangentRepParts hpath hboundary hsingle q r from rfl]
    unfold branchCoeffFromTangentRepParts
    rw [dif_neg (by simpa [r] using hrb)]
    rw [dif_pos (by simpa [r] using hrnd)]
    rfl
  show
    (faithfulBranchAggregationStructure_of_componentsFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
    ).branchCoeff q (Channel.posterior P₁ q o₁) =
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).scale q /
      (faithfulBranchFullSupportScale_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff
      ).scale (Channel.posterior P₁ q o₁)
  rw [show (Channel.posterior P₁ q o₁) = r from rfl]
  rw [hbranch_qr, hscale_eq q, hscale_eq r, hpath_r_one, div_one]

/-- Faithful branch package with the internal HM/finite-linear-algebra fields
filled automatically.

The remaining inputs are exactly the boundary/support representative choices
and the boundary/singleton scale-factorization transports.  This exposes more
of the proof order than passing an opaque `FiniteFaithfulBranchAggregationAssumptions`
bundle. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_components
    (hhm : FinalHMInterface.{u})
    (hatomic : FiniteAtomicPosteriorTangentSpanningAssumptions.{u})
    (hsupportFace : FiniteSupportFaceRepresentativeTransportAssumptions.{u})
    (hboundaryCoeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAssumptions
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        (boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff))
    (hboundaryScale :
      ∀ (F : PrefFamily.{u}) (hax : TraceAxioms F)
        (hV : PosteriorValueRepresentation F),
        let hlin := affineLinearPart_of_FinalHMInterface hhm
        let hpath :=
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
            hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
            (atomicLinearTangentSpanning_of_atomic hatomic) F hax hV
        let hboundary :=
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
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
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationSingletonNormalization
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
    boundaryLinearPartTransport_of_FinalHM_marginalTransport
      hhm (boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff)
      hmarginal
  boundary_scale_factorization := hboundaryScale
  singleton_scale_factorization := hsingleScale

/-- Faithful branch package from the final construction interface and explicit
support/boundary normalizations, with finite atomic tangent spanning discharged by
the internal theorem `finiteAtomicPosteriorTangentSpanning`. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_normalizations
    (hhm : FinalHMInterface.{u})
    (hsupportFace : FiniteSupportFaceRepresentativeTransportAssumptions.{u})
    (hboundaryCoeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hmarginal :
      FiniteSupportFaceMarginalValueTransportAssumptions
        (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
        (boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff))
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
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
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
          boundaryFaceScale_of_coefficientScaleNormalization hboundaryCoeff
        let hvalue :=
          boundaryValueTransport_of_supportFaceRepresentativeTransport
            hsupportFace
        let hcoeff :=
          boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
            (boundaryLinearPartTransport_of_FinalHM_marginalTransport
              hhm hboundary hmarginal)
        FiniteBranchScaleFactorizationSingletonNormalization
          (faithfulBranchAggregationStructure_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
          (faithfulBranchFullSupportScale_of_components
            F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    FiniteFaithfulBranchAggregationAssumptions.{u} :=
  faithfulBranchAggregationAssumptions_of_FinalHM_components
    hhm finiteAtomicPosteriorTangentSpanning
    hsupportFace hboundaryCoeff hsingle hmarginal
    hboundaryScale hsingleScale

/-- Legacy explicit boundary/scale data used by the pre-canonical route.

Unlike the final route, this structure asks for representative transport and
scale choices explicitly.  It is retained only for intermediate compatibility
and is not an assumption of `MIRep_of_TraceAxioms_FinalHM_Faddeev` or the public
main theorem. -/
structure FinalFaithfulBranchData
    (hhm : FinalHMInterface.{u}) where
  support_face : FiniteSupportFaceRepresentativeTransportAssumptions.{u}
  singleton_scale : FiniteBranchSingletonScaleNormalizationAssumptions.{u}
  boundary_coeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u}
  marginal_value :
    FiniteSupportFaceMarginalValueTransportAssumptions
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff)
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
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport
          support_face
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalTransport
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)
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
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport
          support_face
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalTransport
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationSingletonNormalization
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary
            singleton_scale hvalue hcoeff)

/-- Producer from the explicit faithful-branch normalization bundle. -/
noncomputable def faithfulBranchAggregationAssumptions_of_FinalHM_data
    (hhm : FinalHMInterface.{u})
    (hnorm : FinalFaithfulBranchData hhm) :
    FiniteFaithfulBranchAggregationAssumptions.{u} :=
  faithfulBranchAggregationAssumptions_of_FinalHM_normalizations
    hhm
    hnorm.support_face
    hnorm.boundary_coeff hnorm.singleton_scale
    hnorm.marginal_value hnorm.boundary_scale
    hnorm.singleton_scale_factorization

/-- HM-specific faithful branch normalizations with support-face value transport
internalised.

This is the selected-representative counterpart of
`FinalFaithfulBranchData`: it fixes the boundary value transport only for
the HM representative being assembled, via `finalHM_boundaryValueTransportFor`. -/
structure FinalFaithfulBranchDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) where
  boundary_coeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u}
  marginal_value :
    FiniteSupportFaceMarginalValueTransportAssumptions
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff)
  boundary_scale :
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff
    let hvalue := finalHM_boundaryValueTransportFor hhm hax
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
          (boundaryLinearPartTransport_of_FinalHM_marginalTransport
            hhm hboundary marginal_value)
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary
            (finalHMSingletonScaleNormalizationFor hhm hax) hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary
            (finalHMSingletonScaleNormalizationFor hhm hax) hvalue hcoeff)

/-- Selected faithful branch data with the corrected atomic support-face
marginal theorem.

This is the branch datum that is actually constructed from A1/A6 and the HM
interface.  It does not contain the old arbitrary-`PosteriorLawTangent`
support-face transport convention. -/
structure FinalFaithfulBranchAtomicDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) where
  boundary_coeff : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{u}
  marginal_value :
    FiniteSupportFaceMarginalValueTransportAtomicFor
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm)
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff)

/-- Internal constructor for the selected atomic branch datum. -/
noncomputable def finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) :
    FinalFaithfulBranchAtomicDataFor hhm hax where
  boundary_coeff := finalHMBoundaryAtomicCoefficientScaleFor hhm hax
  marginal_value :=
    supportFaceMarginalValueTransportAtomic_of_FinalHMFor
      hhm hax
      (finalSupportFaceMarginalValueTransportAtomic_of_FinalHM_TraceAxioms
        hhm hax)

/-- Selected branch aggregation structure assembled directly from the atomic
support-face theorem.  This bypasses the historical boundary-coefficient
transport route, whose support-face input quantified over arbitrary extensional
tangents. -/
noncomputable def faithfulBranchAggregationStructure_of_atomicDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    BranchAggregationStructure F :=
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransportAtomicFor
      F hax hV hint hpath hboundary hsingle hvalue
      hbranchData.marginal_value
  branchAggregationStructure_of_tangentFormulaFor
    F hax hV hlin hpath hboundary hsingle hformula

/-- Known-result boundary input for the selected faithful branch route.

The boundary coefficient and boundary scale factorization are now constructed
internally.  The only remaining branch input is the support-face scalar theorem
for the HM marginal-value test function, expressed relative to the canonical
coefficient `finalHMBoundaryCoefficientScaleFor`. -/
structure FinalFaithfulBranchKnownResultsFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F) : Prop where
  marginal_transport : FinalSupportFaceMarginalValueTransportFor hhm hax

/-- Convert the known-result branch input into the legacy internal bundle
consumed by existing constructors. -/
noncomputable def finalFaithfulBranchDataFor_of_knownResults
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hknown : FinalFaithfulBranchKnownResultsFor hhm hax) :
    FinalFaithfulBranchDataFor hhm hax where
  boundary_coeff := finalHMBoundaryCoefficientScaleFor hhm hax
  marginal_value :=
    supportFaceMarginalValueTransport_of_FinalHMFor
      hhm hax hknown.marginal_transport
  boundary_scale :=
    finalHMBoundaryScaleFactorizationFor hhm hax
      hknown.marginal_transport

/-- Selected faithful branch/cocycle/chain result from the HM-specific branch
bundle. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hnorm : FinalFaithfulBranchDataFor hhm hax) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hnorm.boundary_coeff
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
    let hcoeff :=
      boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
        (boundaryLinearPartTransport_of_FinalHM_marginalTransport
          hhm hboundary hnorm.marginal_value)
    BranchAggregationCocycleNormalizedChainRule_of_componentsFor
      F hax hV hlin hpath hboundary
        (finalHMSingletonScaleNormalizationFor hhm hax) hvalue hcoeff
      hnorm.boundary_scale
      (finalHMSingletonScaleFactorizationFor
        hhm hax hboundary hcoeff)

/-- Selected-branch scale relabelling from selected-representative covariance.

This is the hax-specific counterpart of `scaleRelabel_of_FinalHM_covariance`.
It uses the selected singleton scale and the theorem-produced singleton
factorization, so no hax-free singleton normalization is needed. -/
theorem scaleRelabel_of_FinalHM_covarianceFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).scale_factorization.scale (Relabeling.relabelDist e q) =
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).scale_factorization.scale q := by
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
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  let hcoeff :=
    boundaryCoefficientTransport_of_linearPartTransport hlin hboundary
      (boundaryLinearPartTransport_of_FinalHM_marginalTransport
        hhm hboundary hbranchData.marginal_value)
  have hscale_eq :
      ∀ (C : Type u) [Fintype C] [DecidableEq C] [Nonempty C] (s : Dist C),
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
          hhm hax hbranchData
        ).scale_factorization.scale s =
          hpath.branchPathCoeff s (Dist.uniform (A := C)) := by
    intro C _ _ _ s
    show
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
        hhm hax hbranchData
      ).branch_agg.branchCoeff s (Dist.uniform (A := C)) =
        hpath.branchPathCoeff s (Dist.uniform (A := C))
    rw [show
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
        hhm hax hbranchData
      ).branch_agg.branchCoeff s (Dist.uniform (A := C)) =
        branchCoeffFromTangentRepParts hpath hboundary hsingle s
          (Dist.uniform (A := C)) from rfl]
    simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  rw [hscale_eq B (Relabeling.relabelDist e q), hscale_eq A q]
  have huni :
      Relabeling.relabelDist e (Dist.uniform (A := A)) =
        Dist.uniform (A := B) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply,
      Dist.uniform_apply, Fintype.card_congr e]
  by_cases hA : Subsingleton A
  · have hqfsB : (Relabeling.relabelDist e q).FullSupport :=
      Relabeling.relabelDist_fullSupport e q hq
    have h1A : hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      have hnn :
          ¬ ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
            0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hab, _, _⟩
        exact hab (Subsingleton.elim a b)
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hq, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    have h1B :
        hpath.branchPathCoeff
          (Relabeling.relabelDist e q) (Dist.uniform (A := B)) = 1 := by
      haveI : Subsingleton B := Equiv.subsingleton e.symm
      have hnn :
          ¬ ∃ a b : B, a ≠ b ∧ 0 < (Dist.uniform (A := B)) a ∧
            0 < (Dist.uniform (A := B)) b := by
        rintro ⟨a, b, hab, _, _⟩
        exact hab (Subsingleton.elim a b)
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hqfsB, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    rw [h1B, h1A]
  · have hndU :
        ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
      rw [not_subsingleton_iff_nontrivial] at hA
      obtain ⟨a, b, hab⟩ := hA
      exact ⟨a, b, hab, Dist.uniform_fullSupport a,
        Dist.uniform_fullSupport b⟩
    rw [← huni]
    exact branchPathCoeff_relabel_of_atomic_eval
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm) hax hV
      (by
        intro A' B' O' Y' _ _ _ _ _ _ _ _ _ _ eA eO s P
        change
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              (Relabeling.relabelDist eA s)
              (experimentOfChannel
                (Relabeling.relabelChannel eA eO P)) =
            (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              s (experimentOfChannel P)
        exact
          (finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq
            hax eA eO s P)
      hpath
      e q (Dist.uniform (A := A)) hq Dist.uniform_fullSupport hndU

/-- Positivity of the selected faithful chain scale for every finite prior. -/
theorem faithful_scale_posFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 < (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).scale_factorization.scale q := by
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
  show 0 <
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff q (Dist.uniform (A := A))
  rw [show
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff q (Dist.uniform (A := A)) =
      branchCoeffFromTangentRepParts hpath hboundary hsingle q
        (Dist.uniform (A := A)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  by_cases hqfs : q.FullSupport
  · by_cases hnd :
        ∃ a b : A, a ≠ b ∧ 0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b
    · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
        hqfs Dist.uniform_fullSupport hnd
    · have hpath_eq :
          hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hqfs, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hnd]
      rw [hpath_eq]
      exact one_pos
  · have hpath_eq :
        hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning]
      rw [dif_neg hqfs]
    rw [hpath_eq]
    exact one_pos

/-- The selected faithful chain scale of a nondegenerate uniform prior is `1`. -/
theorem scale_uniform_eq_oneFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (hnd : ∃ a b : A, a ≠ b) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).scale_factorization.scale (Dist.uniform (A := A)) = 1 := by
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
  show
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) = 1
  rw [show
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_dataFor
      hhm hax hbranchData
    ).branch_agg.branchCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) =
      branchCoeffFromTangentRepParts hpath hboundary hsingle
        (Dist.uniform (A := A)) (Dist.uniform (A := A)) from rfl]
  simp only [branchCoeffFromTangentRepParts, Dist.uniform_fullSupport, dif_pos]
  have hcoc := branchCoeffTangentScalar_cocycle_fullSupport
    hlin F hax hV hpath
    (Dist.uniform (A := A)) (Dist.uniform (A := A))
    (Dist.uniform (A := A))
    Dist.uniform_fullSupport Dist.uniform_fullSupport Dist.uniform_fullSupport
    hnd
  have hpos :
      0 < hpath.branchPathCoeff
        (Dist.uniform (A := A)) (Dist.uniform (A := A)) := by
    obtain ⟨a, b, hab⟩ := hnd
    exact hpath.branchPathCoeff_pos _ _
      Dist.uniform_fullSupport Dist.uniform_fullSupport
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  nlinarith [hcoc, hpos]

/-- **R1: raw chain-scale relabelling invariance from selected covariance.**

The faithful branch chain scale is `scale q = branchCoeff q u_A` (the branch
coefficient to the uniform prior).  Relabelling carries `u_A` to `u_B`
(`Fintype.card_congr`), the full-support branch coefficient equals the tangent
scalar `branchPathCoeff`, and `branchPathCoeff` is relabel-invariant
(`branchPathCoeff_relabel_of_atomic_eval`).  On a subsingleton action
type both coefficients are the degenerate value `1`.  This discharges the raw
form of the `scale_relabel` gauge normalization (under the constant gauge). -/
theorem scaleRelabel_of_FinalHM_covariance
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Relabeling.relabelDist e q) =
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale q := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
    exact branchPathCoeff_relabel_of_atomic_eval
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm) hax hV
      (by
        intro A' B' O' Y' _ _ _ _ _ _ _ _ _ _ eA eO s P
        change
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              (Relabeling.relabelDist eA s)
              (experimentOfChannel
                (Relabeling.relabelChannel eA eO P)) =
            (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              s (experimentOfChannel P)
        exact
          (finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq
            hax eA eO s P)
      hpath e q
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
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      ).boundaryCoeff q r *
      (branchPathTangentScalarStructure_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q' q =
    (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      ).boundaryCoeff q' r := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
  have htrans := hbranchData.marginal_value.support_face_marginalValue_scalar
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

/-- Selected prior-independence of the boundary embedding defect. -/
theorem boundaryCoeff_qIndep_of_FinalHMFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q r *
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q' q =
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q' r := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  change hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q =
    hboundary.boundaryCoeff q' r
  have hrs_fs : (r.restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h
      exact hab (congrArg Subtype.val h)
    · rw [Dist.restrictToSupport_apply]
      exact ha
    · rw [Dist.restrictToSupport_apply]
      exact hb
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have htrans := hbranchData.marginal_value.support_face_marginalValue_scalar
  have hTq := htrans F hax hV q r hq hrn hrnd hrb η hηtan
  have hTq' := htrans F hax hV q' r hq' hrn hrnd hrb η hηtan
  have hpush_atomic := atomicLinear_pushSignedIncl r hηatomic
  have hpush_tan := pushSignedIncl_tangent r hηatomic hηtan
  have hrel := hpath.linear_part_scalar_relation_on_tangent q' q hq' hq
    (by obtain ⟨a, b, hab, _, _⟩ := hrnd; exact ⟨a, b, hab, hq a, hq b⟩)
    (pushSignedIncl r η) hpush_atomic hpush_tan
  have hLq : hlin.linearPart F hV q (pushSignedIncl r η) =
      hboundary.boundaryCoeff q r * η (hint.marginalValue F hV r.restrictToSupport) := hTq
  have hLq' : hlin.linearPart F hV q' (pushSignedIncl r η) =
      hboundary.boundaryCoeff q' r * η (hint.marginalValue F hV r.restrictToSupport) := hTq'
  rw [hLq, hLq'] at hrel
  have hLnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  have hstep :
      hboundary.boundaryCoeff q' r *
          η (hint.marginalValue F hV r.restrictToSupport) =
        (hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q) *
          η (hint.marginalValue F hV r.restrictToSupport) := by
    rw [hrel]
    ring
  have hcancel := mul_right_cancel₀ hLnz hstep
  linarith [hcancel]

/-- Selected prior-independence of the boundary embedding defect, using only
the atomic support-face marginal transport theorem. -/
theorem boundaryCoeff_qIndep_of_FinalHMAtomicFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q r *
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q' q =
    (boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
      ).boundaryCoeff q' r := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization hbranchData.boundary_coeff
  change hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q =
    hboundary.boundaryCoeff q' r
  have hrs_fs : (r.restrictToSupport).FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hrs_nd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_, ?_, ?_⟩
    · intro h
      exact hab (congrArg Subtype.val h)
    · rw [Dist.restrictToSupport_apply]
      exact ha
    · rw [Dist.restrictToSupport_apply]
      exact hb
  obtain ⟨η, hηatomic, hηtan, hηnz⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1 hlin F hax hV
      r.restrictToSupport r.restrictToSupport hrs_fs hrs_fs hrs_nd
  have hTq :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := A) q r hq hrn hrnd hrb η hηatomic hηtan
  have hTq' :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
      (A := A) q' r hq' hrn hrnd hrb η hηatomic hηtan
  have hpush_atomic := atomicLinear_pushSignedIncl r hηatomic
  have hpush_tan := pushSignedIncl_tangent r hηatomic hηtan
  have hrel := hpath.linear_part_scalar_relation_on_tangent q' q hq' hq
    (by obtain ⟨a, b, hab, _, _⟩ := hrnd; exact ⟨a, b, hab, hq a, hq b⟩)
    (pushSignedIncl r η) hpush_atomic hpush_tan
  have hLq : hlin.linearPart F hV q (pushSignedIncl r η) =
      hboundary.boundaryCoeff q r *
        η (hint.marginalValue F hV r.restrictToSupport) := hTq
  have hLq' : hlin.linearPart F hV q' (pushSignedIncl r η) =
      hboundary.boundaryCoeff q' r *
        η (hint.marginalValue F hV r.restrictToSupport) := hTq'
  rw [hLq, hLq'] at hrel
  have hLnz : η (hint.marginalValue F hV r.restrictToSupport) ≠ 0 := hηnz
  have hstep :
      hboundary.boundaryCoeff q' r *
          η (hint.marginalValue F hV r.restrictToSupport) =
        (hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q) *
          η (hint.marginalValue F hV r.restrictToSupport) := by
    rw [hrel]
    ring
  have hcancel := mul_right_cancel₀ hLnz hstep
  linarith [hcancel]

/-- Selected branch scale for the atomic boundary coefficient.

For full-support priors it agrees with the usual path-to-uniform scale.  For
nondegenerate boundary priors it is the inverse of the internally constructed
uniform-to-face boundary coefficient; singleton/degenerate priors retain the
harmless normalization `1`. -/
noncomputable def selectedAtomicBranchScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hb :=
    boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
  exact
    if hq : q.FullSupport then
      hpath.branchPathCoeff q (Dist.uniform (A := A))
    else if hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b then
      1 / hb.boundaryCoeff (Dist.uniform (A := A)) q
    else
      1

theorem selectedAtomicBranchScaleFor_fullSupport
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    selectedAtomicBranchScaleFor hhm hax hbranchData q =
      (branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        (affineLinearPart_of_FinalHMInterface hhm)
        finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).branchPathCoeff q (Dist.uniform (A := A)) := by
  classical
  simp [selectedAtomicBranchScaleFor, hq]

theorem selectedAtomicBranchScaleFor_boundary
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    selectedAtomicBranchScaleFor hhm hax hbranchData r =
      1 /
        (boundaryFaceScale_of_coefficientScaleNormalization
          hbranchData.boundary_coeff
        ).boundaryCoeff (Dist.uniform (A := A)) r := by
  classical
  simp [selectedAtomicBranchScaleFor, hrb, hrnd]

/-- Full-support positivity of the selected atomic branch scale. -/
theorem selectedAtomicBranchScaleFor_pos
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    0 < selectedAtomicBranchScaleFor hhm hax hbranchData q := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq]
  by_cases hnd :
      ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b
  · exact hpath.branchPathCoeff_pos q (Dist.uniform (A := A))
      hq Dist.uniform_fullSupport hnd
  · have hpath_eq :
        hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hq, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnd]
    rw [hpath_eq]
    exact one_pos

/-- Full-support scale factorization for the selected atomic branch scale. -/
noncomputable def atomicFullSupportScaleFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (faithfulBranchAggregationStructure_of_atomicDataFor
        hhm hax hbranchData) where
  scale := fun q => selectedAtomicBranchScaleFor hhm hax hbranchData q
  scale_pos := by
    intro A _ _ _ q hq _hnd
    exact selectedAtomicBranchScaleFor_pos hhm hax hbranchData q hq
  branchCoeff_factorization_fullSupport := by
    intro A _ _ _ q r hq hr hnd
    classical
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      selectedAtomicBranchScaleFor hhm hax hbranchData q /
        selectedAtomicBranchScaleFor hhm hax hbranchData r
    rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq,
      selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData r hr]
    rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
        hpath.branchPathCoeff q r by
      simp [branchCoeffFromTangentRepParts, hr]]
    have hU_nd :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
      obtain ⟨a, b, hab⟩ := hnd
      exact ⟨a, b, hab, Dist.uniform_fullSupport a,
        Dist.uniform_fullSupport b⟩
    have hpos :
        0 < hpath.branchPathCoeff r (Dist.uniform (A := A)) :=
      hpath.branchPathCoeff_pos r (Dist.uniform (A := A))
        hr Dist.uniform_fullSupport hU_nd
    have hcoc :=
      branchCoeffTangentScalar_cocycle_fullSupport
        hlin F hax hV hpath q r (Dist.uniform (A := A))
        hq hr Dist.uniform_fullSupport hnd
    rw [hcoc]
    change hpath.branchPathCoeff q r =
      hpath.branchPathCoeff q r * hpath.branchPathCoeff r (Dist.uniform (A := A)) /
        hpath.branchPathCoeff r (Dist.uniform (A := A))
    field_simp [ne_of_gt hpos]

/-- Boundary scale factorization for the selected atomic branch scale.

The boundary scale is not an extra normalization: for a nondegenerate boundary
posterior `r` it is fixed as the inverse of the internally constructed
uniform-to-face boundary coefficient, and the q-independence theorem identifies
the `q`-boundary coefficient with the full-support path scale. -/
noncomputable def atomicBoundaryScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBranchScaleFactorizationBoundaryTransportAssumptions
      (faithfulBranchAggregationStructure_of_atomicDataFor
        hhm hax hbranchData)
      (atomicFullSupportScaleFor hhm hax hbranchData) where
  branchCoeff_factorization_boundary := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hrnd hrb
    classical
    let r : Dist A := Channel.posterior P₁ q o₁
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    have hrnd_r :
        ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      simpa [r] using hrnd
    have hrb_r : ¬ r.FullSupport := by
      simpa [r] using hrb
    have hrn : ∃ a : A, 0 < r a := by
      rcases hrnd_r with ⟨a, _b, _hab, ha, _hb⟩
      exact ⟨a, ha⟩
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      selectedAtomicBranchScaleFor hhm hax hbranchData q /
        selectedAtomicBranchScaleFor hhm hax hbranchData r
    rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
        hboundary.boundaryCoeff q r by
      unfold branchCoeffFromTangentRepParts
      rw [dif_neg hrb_r]
      rw [dif_pos hrnd_r]]
    rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq,
      selectedAtomicBranchScaleFor_boundary
        hhm hax hbranchData r hrnd_r hrb_r]
    have hbc_pos :
        0 < hboundary.boundaryCoeff (Dist.uniform (A := A)) r :=
      hboundary.boundaryCoeff_pos (Dist.uniform (A := A)) r
        Dist.uniform_fullSupport hrn hrnd_r hrb_r
    have hqi :=
      boundaryCoeff_qIndep_of_FinalHMAtomicFor
        hhm hax hbranchData (Dist.uniform (A := A)) q r
        Dist.uniform_fullSupport hq hrn hrnd_r hrb_r
    rw [← hqi]
    field_simp [ne_of_gt hbc_pos]

/-- Singleton/degenerate scale factorization for the selected atomic branch
scale.

Singleton-support posteriors carry no identified value variation.  The HM
singleton coefficient is therefore fixed to the same full-support path scale,
while the selected atomic scale assigns value `1` to degenerate boundary
posteriors. -/
noncomputable def atomicSingletonScaleFactorizationFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBranchScaleFactorizationSingletonNormalization
      (faithfulBranchAggregationStructure_of_atomicDataFor
        hhm hax hbranchData)
      (atomicFullSupportScaleFor hhm hax hbranchData) where
  scale_pos_singleton := by
    intro A _ _ _ q hq _hr_singleton
    change 0 < selectedAtomicBranchScaleFor hhm hax hbranchData q
    exact selectedAtomicBranchScaleFor_pos hhm hax hbranchData q hq
  branchCoeff_factorization_singleton := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ _hpos hsingle_support
    classical
    let r : Dist A := Channel.posterior P₁ q o₁
    let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
    let hlin := affineLinearPart_of_FinalHMInterface hhm
    let hpath :=
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
        hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning) F hax hV
    let hboundary :=
      boundaryFaceScale_of_coefficientScaleNormalization
        hbranchData.boundary_coeff
    let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
    have hnotnd :
        ¬ ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b := by
      exact not_nondegenerate_of_singleton_support r
        (by simpa [r] using hsingle_support)
    change branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
      selectedAtomicBranchScaleFor hhm hax hbranchData q /
        selectedAtomicBranchScaleFor hhm hax hbranchData r
    by_cases hrfull : r.FullSupport
    · have hsub : Subsingleton A := by
        rcases hsingle_support with ⟨c, _hc, huniq⟩
        refine ⟨?_⟩
        intro a b
        exact (huniq a (hrfull a)).trans
          (huniq b (hrfull b)).symm
      have hU_notnd :
          ¬ ∃ a b : A, a ≠ b ∧
            0 < (Dist.uniform (A := A)) a ∧
            0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hne, _ha, _hb⟩
        exact hne (Subsingleton.elim a b)
      have hpath_qr_one : hpath.branchPathCoeff q r = 1 := by
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, hrfull, dif_pos]
        rw [dif_neg hnotnd]
      have hscale_q_one :
          selectedAtomicBranchScaleFor hhm hax hbranchData q = 1 := by
        rw [selectedAtomicBranchScaleFor_fullSupport
          hhm hax hbranchData q hq]
        change hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hq, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      have hscale_r_one :
          selectedAtomicBranchScaleFor hhm hax hbranchData r = 1 := by
        rw [selectedAtomicBranchScaleFor_fullSupport
          hhm hax hbranchData r hrfull]
        change hpath.branchPathCoeff r (Dist.uniform (A := A)) = 1
        simp only [hpath,
          branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
          hrfull, Dist.uniform_fullSupport, dif_pos]
        rw [dif_neg hU_notnd]
      rw [show branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
          hpath.branchPathCoeff q r by
        simp [branchCoeffFromTangentRepParts, hrfull]]
      rw [hpath_qr_one, hscale_q_one, hscale_r_one]
      norm_num
    · have hbranch_qr :
          branchCoeffFromTangentRepParts hpath hboundary hsingle q r =
            hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
        unfold branchCoeffFromTangentRepParts
        rw [dif_neg hrfull]
        rw [dif_neg hnotnd]
        simpa [hsingle] using
          finalHMSingletonScaleNormalizationFor_coeff hhm hax q r
      have hscale_r_one :
          selectedAtomicBranchScaleFor hhm hax hbranchData r = 1 := by
        simp [selectedAtomicBranchScaleFor, hrfull, hnotnd]
      rw [hbranch_qr]
      rw [selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq]
      change hpath.branchPathCoeff q (Dist.uniform (A := A)) =
        hpath.branchPathCoeff q (Dist.uniform (A := A)) /
          selectedAtomicBranchScaleFor hhm hax hbranchData r
      rw [hscale_r_one]
      rw [div_one]

/-- Selected faithful branch/cocycle/chain result assembled from the corrected
atomic support-face theorem.

This is the convention-free branch-chain route: its boundary coefficient,
support-face marginal transport, and boundary/singleton scale extensions are all
constructed from `TraceAxioms` and the HM interface. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hboundary :=
    boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  let hvalue := finalHM_boundaryValueTransportFor hhm hax
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransportAtomicFor
      F hax hV hint hpath hboundary hsingle hvalue
      hbranchData.marginal_value
  let hbranch :=
    branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula
  let hcocycle :=
    branchCoeffCocycleFor_of_tangentScalar
      F hax hV hlin hpath hboundary hsingle hformula
  let hfull := atomicFullSupportScaleFor hhm hax hbranchData
  {
    branch_agg := hbranch
    coeff_cocycle := hcocycle
    full_support_scale := hfull
    scale_factorization :=
      branchScaleFactorization_of_fullSupport_boundary_singleton
        hbranch hfull
        (atomicBoundaryScaleFactorizationFor hhm hax hbranchData)
        (atomicSingletonScaleFactorizationFor hhm hax hbranchData)
  }

/-- Relabelling invariance of the selected atomic branch scale on full-support
priors. -/
theorem scaleRelabel_of_FinalHM_covarianceAtomicFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale (Relabeling.relabelDist e q) =
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale q := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  have hscale_eq :
      ∀ (C : Type u) [Fintype C] [DecidableEq C] [Nonempty C]
        (s : Dist C), s.FullSupport →
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
          hhm hax hbranchData
        ).scale_factorization.scale s =
          hpath.branchPathCoeff s (Dist.uniform (A := C)) := by
    intro C _ _ _ s hs
    change selectedAtomicBranchScaleFor hhm hax hbranchData s =
      hpath.branchPathCoeff s (Dist.uniform (A := C))
    exact selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData s hs
  have hqfsB : (Relabeling.relabelDist e q).FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  rw [hscale_eq B (Relabeling.relabelDist e q) hqfsB,
    hscale_eq A q hq]
  have huni :
      Relabeling.relabelDist e (Dist.uniform (A := A)) =
        Dist.uniform (A := B) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply,
      Dist.uniform_apply, Fintype.card_congr e]
  by_cases hA : Subsingleton A
  · have h1A : hpath.branchPathCoeff q (Dist.uniform (A := A)) = 1 := by
      have hnn :
          ¬ ∃ a b : A, a ≠ b ∧
            0 < (Dist.uniform (A := A)) a ∧
            0 < (Dist.uniform (A := A)) b := by
        rintro ⟨a, b, hab, _, _⟩
        exact hab (Subsingleton.elim a b)
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hq, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    have h1B :
        hpath.branchPathCoeff
          (Relabeling.relabelDist e q) (Dist.uniform (A := B)) = 1 := by
      haveI : Subsingleton B := Equiv.subsingleton e.symm
      have hnn :
          ¬ ∃ a b : B, a ≠ b ∧
            0 < (Dist.uniform (A := B)) a ∧
            0 < (Dist.uniform (A := B)) b := by
        rintro ⟨a, b, hab, _, _⟩
        exact hab (Subsingleton.elim a b)
      simp only [hpath,
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
        hqfsB, Dist.uniform_fullSupport, dif_pos]
      rw [dif_neg hnn]
    rw [h1B, h1A]
  · have hndU :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b := by
      rw [not_subsingleton_iff_nontrivial] at hA
      obtain ⟨a, b, hab⟩ := hA
      exact ⟨a, b, hab, Dist.uniform_fullSupport a,
        Dist.uniform_fullSupport b⟩
    rw [← huni]
    exact branchPathCoeff_relabel_of_atomic_eval
      (posteriorIntegralRepresentation_of_FinalHMInterface hhm) hax hV
      (by
        intro A' B' O' Y' _ _ _ _ _ _ _ _ _ _ eA eO s P
        change
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              (Relabeling.relabelDist eA s)
              (experimentOfChannel
                (Relabeling.relabelChannel eA eO P)) =
            (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
              s (experimentOfChannel P)
        exact
          (finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq
            hax eA eO s P)
      hpath
      e q (Dist.uniform (A := A)) hq Dist.uniform_fullSupport hndU

/-- Positivity of the selected atomic chain scale for every finite prior. -/
theorem faithful_atomic_scale_posFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A) :
    0 < (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale q := by
  classical
  change 0 < selectedAtomicBranchScaleFor hhm hax hbranchData q
  by_cases hq : q.FullSupport
  · exact selectedAtomicBranchScaleFor_pos hhm hax hbranchData q hq
  · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
    · rw [selectedAtomicBranchScaleFor_boundary hhm hax hbranchData q hnd hq]
      have hnonempty : ∃ a : A, 0 < q a := by
        rcases hnd with ⟨a, _b, _hab, ha, _hb⟩
        exact ⟨a, ha⟩
      have hbpos :
          0 <
            (boundaryFaceScale_of_coefficientScaleNormalization
              hbranchData.boundary_coeff
            ).boundaryCoeff (Dist.uniform (A := A)) q :=
        (boundaryFaceScale_of_coefficientScaleNormalization
          hbranchData.boundary_coeff).boundaryCoeff_pos
          (Dist.uniform (A := A)) q Dist.uniform_fullSupport
          hnonempty hnd hq
      exact one_div_pos.mpr hbpos
    · simp [selectedAtomicBranchScaleFor, hq, hnd]

/-- The selected atomic chain scale of a nondegenerate uniform prior is `1`. -/
theorem scale_uniform_eq_oneAtomicFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (hnd : ∃ a b : A, a ≠ b) :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale (Dist.uniform (A := A)) = 1 := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  change selectedAtomicBranchScaleFor hhm hax hbranchData
      (Dist.uniform (A := A)) = 1
  rw [selectedAtomicBranchScaleFor_fullSupport
    hhm hax hbranchData (Dist.uniform (A := A))
    Dist.uniform_fullSupport]
  change hpath.branchPathCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) = 1
  have hcoc := branchCoeffTangentScalar_cocycle_fullSupport
    hlin F hax hV hpath
    (Dist.uniform (A := A)) (Dist.uniform (A := A))
    (Dist.uniform (A := A))
    Dist.uniform_fullSupport Dist.uniform_fullSupport Dist.uniform_fullSupport
    hnd
  have hpos :
      0 < hpath.branchPathCoeff
        (Dist.uniform (A := A)) (Dist.uniform (A := A)) := by
    obtain ⟨a, b, hab⟩ := hnd
    exact hpath.branchPathCoeff_pos _ _
      Dist.uniform_fullSupport Dist.uniform_fullSupport
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  nlinarith [hcoc, hpos]

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
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (n : ℕ) : ℝ :=
  if h : n = 0 then 1
  else
    haveI : NeZero n := ⟨h⟩
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := canonType.{u} n))

/-- The chain scale of the uniform prior depends only on the cardinality: it
equals `cardScale (card A)`.  Immediate from R1 via the equivalence
`A ≃ canonType (card A)`, which carries the uniform prior to the uniform prior. -/
theorem scale_uniform_eq_cardScale
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := A)) =
      cardScale hhm hbranchData hax (Fintype.card A) := by
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
  exact (scaleRelabel_of_FinalHM_covariance hhm hbranchData hax e
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
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (hnd : ∃ a b : A, a ≠ b) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (Dist.uniform (A := A)) = 1 := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m)
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (canonBoundary.{u} n m hmn).restrictToSupport = 1 := by
  rw [canonBoundary_face_uniform n m hmn]
  have hnd : ∃ a b : supportSubtype (canonBoundary.{u} n m hmn), a ≠ b := by
    have hcard : Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) = m := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]; simp [canonType]
    have : 1 < Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) := by omega
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    exact ⟨a, b, hab⟩
  exact scale_uniform_eq_one hhm hbranchData hax hnd

/-- **The embedding defect `K_{n,m}`** (`2 ≤ m ≤ n`): the boundary coefficient
from the uniform prior on the `n`-point action set to the canonical `m`-point
face.  Since both `scale (u_n)` and the face scale are `1`
(`scale_uniform_eq_one`, `canonBoundary_face_scale_eq_one`), this boundary
coefficient *is* the paper's embedding defect for the canonical inclusion.  The
cardinal gauge `t_n` is `cardDefect n 2`. -/
noncomputable def cardDefect
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (n m : ℕ) : ℝ :=
  if h : 2 ≤ m ∧ m ≤ n then
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m h.2)
  else 1

/-- The embedding defect is positive for `2 ≤ m < n`. -/
theorem cardDefect_pos
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (n m : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    0 < cardDefect hhm hbranchData hax n m := by
  classical
  have hle : m ≤ n := le_of_lt hmn
  rw [cardDefect, dif_pos ⟨hm2, hle⟩]
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
  apply (branchBoundaryFaceScale_of_faithfulAssumptions
    (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)).boundaryCoeff_pos
  · exact Dist.uniform_fullSupport
  · exact canonBoundary_support_nonempty n m hle (by omega)
  · exact canonBoundary_nondeg n m hle hm2
  · exact canonBoundary_boundary n m hle hmn

/-- Selected-chain scale of the canonical boundary support face is `1`. -/
theorem canonBoundary_face_scale_eq_oneFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m)
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale (canonBoundary.{u} n m hmn).restrictToSupport = 1 := by
  rw [canonBoundary_face_uniform n m hmn]
  have hnd :
      ∃ a b : supportSubtype (canonBoundary.{u} n m hmn), a ≠ b := by
    have hcard :
        Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) = m := by
      rw [Fintype.card_congr (canonBoundarySupportEquiv n m hmn)]
      simp [canonType]
    have : 1 < Fintype.card (supportSubtype (canonBoundary.{u} n m hmn)) := by
      omega
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card this
    exact ⟨a, b, hab⟩
  exact scale_uniform_eq_oneAtomicFor hhm hax hbranchData hnd

/-- Selected embedding defect `K_{n,m}` read from the selected boundary
coefficient package. -/
noncomputable def cardDefectFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) : ℝ :=
  if h : 2 ≤ m ∧ m ≤ n then
    haveI : NeZero m := ⟨by omega⟩
    haveI : NeZero n := ⟨by omega⟩
    haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
    (boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
    ).boundaryCoeff (Dist.uniform (A := canonType.{u} n))
      (canonBoundary.{u} n m h.2)
  else 1

/-- Positivity of the selected embedding defect for strict boundary faces. -/
theorem cardDefect_posFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    0 < cardDefectFor hhm hax hbranchData n m := by
  classical
  have hle : m ≤ n := le_of_lt hmn
  rw [cardDefectFor, dif_pos ⟨hm2, hle⟩]
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  haveI : Nonempty (canonType.{u} n) := ⟨ULift.up ⟨0, by omega⟩⟩
  apply (boundaryFaceScale_of_coefficientScaleNormalization
    hbranchData.boundary_coeff).boundaryCoeff_pos
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

/-- Pull a signed posterior law through a deterministic pushforward map. -/
noncomputable def pushSignedDet
    {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (K : S → T) (η : PosteriorLawSigned S) :
    PosteriorLawSigned T :=
  fun ψ => η (fun d => ψ (Channel.actionPushforward d
    (fun s => Dist.pure (K s))))

/-- Deterministic pushforward preserves atomic-linearity of signed posterior
laws. -/
noncomputable def atomicLinear_pushSignedDet
    {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (K : S → T) {η : PosteriorLawSigned S}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (pushSignedDet K η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact {
      I := hη.witness.I
      instFintypeI := inferInstance
      instDecidableEqI := inferInstance
      weight := hη.witness.weight
      point := fun i =>
        Channel.actionPushforward (hη.witness.point i)
          (fun s => Dist.pure (K s))
    }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext ψ
    show (∑ i : hη.witness.I, hη.witness.weight i *
        ψ (Channel.actionPushforward (hη.witness.point i)
          (fun s => Dist.pure (K s)))) =
      η (fun d => ψ (Channel.actionPushforward d
        (fun s => Dist.pure (K s))))
    have h := congrFun hη.eval_eq
      (fun d => ψ (Channel.actionPushforward d
        (fun s => Dist.pure (K s))))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- Relabelling pullback along an arbitrary finite equivalence preserves
atomic-linearity. -/
noncomputable def atomicLinear_relabelPullbackDirect
    {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (E : S ≃ T) {η : PosteriorLawSigned S}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear
      (fun ψ : Dist T → ℝ => η (fun d => ψ (Relabeling.relabelDist E d))) where
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
    have h := congrFun hη.eval_eq
      (fun d => ψ (Relabeling.relabelDist E d))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- **Transport equation for the embedding defect.**  For `2 ≤ m < n` and a
tangent `η` on the `m`-face support, the ambient marginal value of the uniform
prior, restricted along the face inclusion, equals `cardDefect n m` times the
intrinsic face marginal value.  (This is the support-face marginal-value
transport, with `boundaryCoeff` identified as `cardDefect`.) -/
theorem cardDefect_transport
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n)
    (η : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m (le_of_lt hmn))))
    (hηtan : PosteriorLawTangent η) :
    η (fun d => (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (Dist.uniform (A := canonType.{u} n))
          (Channel.actionPushforward d
            (supportIncludeKernel (canonBoundary.{u} n m (le_of_lt hmn))))) =
      cardDefect hhm hbranchData hax n m *
        η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (canonBoundary.{u} n m (le_of_lt hmn)).restrictToSupport) := by
  classical
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm
  have htr := hbranchData.marginal_value.support_face_marginalValue_scalar
    F hax hV (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m (le_of_lt hmn))
    Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n m (le_of_lt hmn) (by omega))
    (canonBoundary_nondeg n m (le_of_lt hmn) hm2)
    (canonBoundary_boundary n m (le_of_lt hmn) hmn) η hηtan
  have hcd : cardDefect hhm hbranchData hax n m =
      (branchBoundaryFaceScale_of_faithfulAssumptions
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      ).boundaryCoeff (Dist.uniform (A := canonType.{u} n)) (canonBoundary.{u} n m (le_of_lt hmn)) := by
    rw [cardDefect, dif_pos ⟨hm2, le_of_lt hmn⟩]
  rw [hcd]
  exact htr

/-- Selected transport equation for the embedding defect. -/
theorem cardDefect_transportFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n m : ℕ) [NeZero m] [NeZero n] (hm2 : 2 ≤ m) (hmn : m < n)
    (η : PosteriorLawSigned (supportSubtype (canonBoundary.{u} n m (le_of_lt hmn))))
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    η (fun d => (posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (Dist.uniform (A := canonType.{u} n))
          (Channel.actionPushforward d
            (supportIncludeKernel (canonBoundary.{u} n m (le_of_lt hmn))))) =
      cardDefectFor hhm hax hbranchData n m *
        η ((posteriorIntegralRepresentation_of_FinalHMInterface hhm).marginalValue F
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          (canonBoundary.{u} n m (le_of_lt hmn)).restrictToSupport) := by
  classical
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  have htr :=
    hbranchData.marginal_value.support_face_marginalValue_scalar_atomic
    (A := canonType.{u} n) (Dist.uniform (A := canonType.{u} n))
    (canonBoundary.{u} n m (le_of_lt hmn))
    Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n m (le_of_lt hmn) (by omega))
    (canonBoundary_nondeg n m (le_of_lt hmn) hm2)
    (canonBoundary_boundary n m (le_of_lt hmn) hmn) η hηatomic hηtan
  have hcd :
      cardDefectFor hhm hax hbranchData n m =
        (boundaryFaceScale_of_coefficientScaleNormalization
          hbranchData.boundary_coeff
        ).boundaryCoeff (Dist.uniform (A := canonType.{u} n))
          (canonBoundary.{u} n m (le_of_lt hmn)) := by
    rw [cardDefectFor, dif_pos ⟨hm2, le_of_lt hmn⟩]
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
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    (n m l : ℕ) [NeZero l] [NeZero m] [NeZero n]
    (hl2 : 2 ≤ l) (hlm : l < m) (hmn : m < n) :
    cardDefect hhm hbranchData hax n m * cardDefect hhm hbranchData hax m l =
      cardDefect hhm hbranchData hax n l := by
  classical
  have hle_ml : l ≤ m := le_of_lt hlm
  have hle_mn : m ≤ n := le_of_lt hmn
  have hle_ln : l ≤ n := hle_ml.trans hle_mn
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set hint := posteriorIntegralRepresentation_of_FinalHMInterface hhm with hintdef
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
  have hT_nl := cardDefect_transport hhm hbranchData hax n l hl2 (lt_of_lt_of_le hlm hle_mn) η hηtan
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
  have hη''atomic : PosteriorLawSigned.AtomicLinear η'' := by
    rw [hη''def]
    exact atomicLinear_pushSignedDet
      (nestSupportMap n m l hle_mn hle_ml) hηatomic
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
  have hT_nm := cardDefect_transport hhm hbranchData hax n m h2m hmn η'' hη''tan
  -- Combine hT_nl, hLHS_link, hT_nm:
  --   cardDefect n l · η(mV faceNL) = LHS_nl = LHS_nm(via link) = cardDefect n m · η''(mV faceNM)
  have hchain1 : cardDefect hhm hbranchData hax n l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      cardDefect hhm hbranchData hax n m *
      η'' (hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport) := by
    rw [← hT_nl, hLHS_link, hT_nm]
  -- Bridge: η''(mV faceNM) = cardDefect m l · η(mV faceNL)
-- Bridge: η''(mV faceNM) = cardDefect m l · η(mV faceNL)
  have hbridge :
      η'' (hint.marginalValue F hV (canonBoundary.{u} n m hle_mn).restrictToSupport) =
      cardDefect hhm hbranchData hax m l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
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
    have hT_ml := cardDefect_transport hhm hbranchData hax m l hl2 hlm ζ hζtan
    -- LHS of hT_ml IS our expression (ζ unfolded)
    have hLHS_eq : η (fun d => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward (relabelDist φ d)
            (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) =
        ζ (fun d' => hint.marginalValue F hV (Dist.uniform (A := canonType.{u} m))
          (Channel.actionPushforward d' (supportIncludeKernel (canonBoundary.{u} m l hle_ml)))) := rfl
    rw [hLHS_eq, hT_ml]
    -- goal: cardDefect m l · ζ(mV faceML) = cardDefect m l · η(mV faceNL). Need ζ(mV faceML)=η(mV faceNL).
    congr 1
    change relabelPosteriorLawSigned φ η
        (hint.marginalValue F hV
          (canonBoundary.{u} m l hle_ml).restrictToSupport) =
      η (hint.marginalValue F hV
        (canonBoundary.{u} n l hle_ln).restrictToSupport)
    have hfaceML_rel : (canonBoundary.{u} m l hle_ml).restrictToSupport =
        relabelDist φ (canonBoundary.{u} n l hle_ln).restrictToSupport := by
      rw [canonBoundary_face_uniform m l hle_ml, canonBoundary_face_uniform n l hle_ln]
      ext a
      rw [Dist.uniform_apply, relabelDist_apply, Dist.uniform_apply]
      congr 1
      rw [Fintype.card_congr (canonBoundarySupportEquiv m l hle_ml),
        Fintype.card_congr (canonBoundarySupportEquiv n l hle_ln)]
    rw [hfaceML_rel]
    exact finalHM_affineLinearPart_relabel_atomic_eval hhm hax φ
      (canonBoundary.{u} n l hle_ln).restrictToSupport
      hfaceNL_fs η hηatomic hηtan
  -- final cancellation
  have hfin : cardDefect hhm hbranchData hax n l *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefect hhm hbranchData hax n m * cardDefect hhm hbranchData hax m l) *
      η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) := by
    rw [hchain1, hbridge]; ring
  have := mul_right_cancel₀ hηnz' (by linarith [hfin] : _ )
  linarith [hfin, mul_right_cancel₀ hηnz'
    (show cardDefect hhm hbranchData hax n l *
        η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) =
      (cardDefect hhm hbranchData hax n m * cardDefect hhm hbranchData hax m l) *
        η (hint.marginalValue F hV (canonBoundary.{u} n l hle_ln).restrictToSupport) from hfin)]

/-- Selected embedding-defect cocycle. -/
theorem cardDefect_cocycleFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
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
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    (n : ℕ) : ℝ :=
  if n = 2 then 1
  else if 3 ≤ n then cardDefectFor hhm hax hbranchData n 2
  else 1

/-- Selected embedding defect factors through the selected cardinal scale. -/
theorem cardDefect_eq_ratioFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
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
    (hax : TraceAxioms F)
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
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax) :
    PositiveFaceScaleGauge.{u} where
  gauge := fun {A} _ _ _ _ =>
    cardScaleTFor hhm hax hbranchData (Fintype.card A)
  gauge_pos := fun {A} _ _ _ _ =>
    cardScaleT_posFor hhm hax hbranchData (Fintype.card A)

/-- The selected cardinal gauge is relabelling-invariant. -/
theorem cardinalGauge_gaugeRelFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
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
    (hax : TraceAxioms F)
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
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F) (n : ℕ) : ℝ :=
  if n = 2 then 1
  else if 3 ≤ n then cardDefect hhm hbranchData hax n 2
  else 1

/-- The embedding defect factors as `cardDefect n m = t_n / t_m` (the cocycle,
setting `ℓ = 2`). -/
theorem cardDefect_eq_ratio
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F)
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
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F)
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
    (hax : TraceAxioms F)
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
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
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
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
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
    (hax : TraceAxioms F)
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
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
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
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport)
    (hm2 : 2 ≤ Fintype.card (supportSubtype r))
    (hmn : Fintype.card (supportSubtype r) < Fintype.card A) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff (Dist.uniform (A := A)) r *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport =
    cardDefect hhm hbranchData hax (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  classical
  set n := Fintype.card A with hndef
  set m := Fintype.card (supportSubtype r) with hmdef
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
    exact (boundaryCoeff_relabel_of_FinalHM hhm hbranchData hax e (Dist.uniform (A := A)) r
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
    exact (scaleRelabel_of_FinalHM_covariance hhm hbranchData hax (relabelSupportEquiv e r).symm
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
  have hwf := boundaryCoeff_scale_within_face hhm hbranchData hax
    (Dist.uniform (A := canonType.{u} n)) r' (canonBoundary.{u} n m hmn')
    Dist.uniform_fullSupport hsupp hr'n hr'nd hr'b
  rw [hwf]
  -- scale(cB n m|supp) = 1, and bc(u_n, cB n m) = cardDefect n m
  rw [canonBoundary_face_scale_eq_one hhm hbranchData hax n m hmn' hm2, mul_one]
  rw [cardDefect, dif_pos ⟨hm2, hmn'⟩]

/-- **General embedding-defect reduction.**  For any full-support ambient prior
`q` and boundary posterior `r` (with `2 ≤ card supp r < card A`), the scaled
boundary coefficient is `scale q · cardDefect(card A, card supp r)`. -/
theorem general_defect
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport)
    (hm2 : 2 ≤ Fintype.card (supportSubtype r))
    (hmn : Fintype.card (supportSubtype r) < Fintype.card A) :
    (branchBoundaryFaceScale_of_faithfulAssumptions
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
    ).boundaryCoeff q r *
      (BranchAggregationCocycleNormalizedChainRule_of_faithful
        (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
        F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport =
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale q *
      cardDefect hhm hbranchData hax (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
  have hqi := boundaryCoeff_qIndep_of_FinalHM hhm hbranchData hax
    (Dist.uniform (A := A)) q r Dist.uniform_fullSupport hq hrn hrnd hrb
  -- hqi : hb.boundaryCoeff u_A r * hpath.branchPathCoeff q u_A = hb.boundaryCoeff q r
  have hbcq : hb.boundaryCoeff q r =
      hb.boundaryCoeff (Dist.uniform (A := A)) r *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
        ).scale_factorization.scale q := by
    rw [hscale_q]; exact hqi.symm
  rw [hbcq]
  -- now  bc(u_A,r)·scale q · scale(r|supp) = scale q · cardDefect
  have hgu := general_defect_uniform hhm hbranchData hax r hrn hrnd hrb hm2 hmn
  -- hgu : bc(u_A,r)·scale(r|supp) = cardDefect
  set s := hb.boundaryCoeff (Dist.uniform (A := A)) r
  set sq := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).scale_factorization.scale q
  set srs := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax hV
      ).scale_factorization.scale r.restrictToSupport
  -- goal: s * sq * srs = sq * cardDefect ; hgu : s * srs = cardDefect
  have : s * sq * srs = sq * (s * srs) := by ring
  rw [this, hgu]

/-- Selected embedding-defect reduction at the uniform ambient prior. -/
theorem general_defect_uniformFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport)
    (hm2 : 2 ≤ Fintype.card (supportSubtype r))
    (hmn : Fintype.card (supportSubtype r) < Fintype.card A) :
    (boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
    ).boundaryCoeff (Dist.uniform (A := A)) r *
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale r.restrictToSupport =
    cardDefectFor hhm hax hbranchData
      (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  classical
  set n := Fintype.card A with hndef
  set m := Fintype.card (supportSubtype r) with hmdef
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  set hb := boundaryFaceScale_of_coefficientScaleNormalization
    hbranchData.boundary_coeff with hbdef
  set e := alignEquiv r with hedef
  set r' := Relabeling.relabelDist e r with hr'def
  have huni :
      Relabeling.relabelDist e (Dist.uniform (A := A)) =
        Dist.uniform (A := canonType.{u} n) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply]
    congr 1
    exact congrArg (Nat.cast) (Fintype.card_congr e)
  have hbc_rel :
      hb.boundaryCoeff (Dist.uniform (A := A)) r =
        hb.boundaryCoeff (Dist.uniform (A := canonType.{u} n)) r' := by
    rw [← huni]
    exact (boundaryCoeff_relabel_of_FinalHMFor hhm hax hbranchData e
      (Dist.uniform (A := A)) r Dist.uniform_fullSupport hrn hrnd hrb).symm
  have hscale_rel :
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale r.restrictToSupport =
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale r'.restrictToSupport := by
    have hface : r'.restrictToSupport =
        Relabeling.relabelDist (relabelSupportEquiv e r).symm
          r.restrictToSupport :=
      restrictToSupport_relabelDist e r
    rw [hface]
    exact (scaleRelabel_of_FinalHM_covarianceAtomicFor hhm hax hbranchData
      (relabelSupportEquiv e r).symm r.restrictToSupport
      (Dist.restrictToSupport_fullSupport r)).symm
  rw [hbc_rel, hscale_rel]
  have hmn' : m ≤ n := le_of_lt hmn
  have hsupp : ∀ c, r' c > 0 ↔ (canonBoundary.{u} n m hmn') c > 0 :=
    alignEquiv_relabel_support_eq r m hmdef hmn'
  have hr'n : ∃ b : canonType.{u} n, 0 < r' b := by
    obtain ⟨a, ha⟩ := hrn
    exact ⟨e a, by
      rw [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply]
      exact ha⟩
  have hr'nd : ∃ a b : canonType.{u} n, a ≠ b ∧ 0 < r' a ∧ 0 < r' b := by
    obtain ⟨a, b, hab, ha, hb'⟩ := hrnd
    exact ⟨e a, e b, fun h => hab (e.injective h),
      by rw [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact ha,
      by rw [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply]; exact hb'⟩
  have hr'b : ¬ r'.FullSupport := by
    intro hfs
    apply hrb
    intro a
    have := hfs (e a)
    rwa [hr'def, Relabeling.relabelDist_apply, Equiv.symm_apply_apply] at this
  have hwf := boundaryCoeff_scale_within_faceFor hhm hax hbranchData
    (Dist.uniform (A := canonType.{u} n)) r' (canonBoundary.{u} n m hmn')
    Dist.uniform_fullSupport hsupp hr'n hr'nd hr'b
  rw [hwf]
  rw [canonBoundary_face_scale_eq_oneFor hhm hax hbranchData n m hmn' hm2,
    mul_one]
  rw [cardDefectFor, dif_pos ⟨hm2, hmn'⟩]

/-- Selected general embedding-defect reduction. -/
theorem general_defectFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport)
    (hm2 : 2 ≤ Fintype.card (supportSubtype r))
    (hmn : Fintype.card (supportSubtype r) < Fintype.card A) :
    (boundaryFaceScale_of_coefficientScaleNormalization
      hbranchData.boundary_coeff
    ).boundaryCoeff q r *
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale r.restrictToSupport =
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale q *
      cardDefectFor hhm hax hbranchData
        (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hb := boundaryFaceScale_of_coefficientScaleNormalization
    hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  have hscale_q :
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).scale_factorization.scale q =
        hpath.branchPathCoeff q (Dist.uniform (A := A)) := by
    change selectedAtomicBranchScaleFor hhm hax hbranchData q =
      hpath.branchPathCoeff q (Dist.uniform (A := A))
    exact selectedAtomicBranchScaleFor_fullSupport hhm hax hbranchData q hq
  have hqi := boundaryCoeff_qIndep_of_FinalHMAtomicFor hhm hax hbranchData
    (Dist.uniform (A := A)) q r Dist.uniform_fullSupport hq hrn hrnd hrb
  have hbcq : hb.boundaryCoeff q r =
      hb.boundaryCoeff (Dist.uniform (A := A)) r *
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
          hhm hax hbranchData
        ).scale_factorization.scale q := by
    rw [hscale_q]
    exact hqi.symm
  rw [hbcq]
  have hgu := general_defect_uniformFor hhm hax hbranchData
    r hrn hrnd hrb hm2 hmn
  set s := hb.boundaryCoeff (Dist.uniform (A := A)) r
  set sq :=
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale q
  set srs :=
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale r.restrictToSupport
  have : s * sq * srs = sq * (s * srs) := by
    ring
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
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F) (n : ℕ) :
    0 < cardScaleT hhm hbranchData hax n := by
  rw [cardScaleT]
  by_cases h2 : n = 2
  · rw [if_pos h2]; exact one_pos
  · rw [if_neg h2]
    by_cases h3 : 3 ≤ n
    · rw [if_pos h3]
      exact cardDefect_pos hhm hbranchData hax n 2 (le_refl 2) (by omega)
    · rw [if_neg h3]; exact one_pos

/-- **The cardinal gauge.**  `g(q) := cardScaleT (card A) = t_{card A}` — a positive
constant depending only on the cardinality of the action set.  It is internally
defined from the embedding defect (`cardDefect n 2`), not an external normalization.
With this gauge the raw face-scale equation `support_scale` becomes provable from
the general embedding-defect reduction and the cocycle `cardDefect n m = t_n/t_m`. -/
noncomputable def cardinalGauge
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F) :
    PositiveFaceScaleGauge.{u} where
  gauge := fun {A} _ _ _ _ => cardScaleT hhm hbranchData hax (Fintype.card A)
  gauge_pos := fun {A} _ _ _ _ => cardScaleT_pos hhm hbranchData hax (Fintype.card A)

/-- The cardinal gauge is relabelling-invariant (depends only on cardinality). -/
theorem cardinalGauge_gaugeRel
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (e : A ≃ B) (q : Dist A) :
    (cardinalGauge hhm hbranchData hax).gauge (Relabeling.relabelDist e q) =
      (cardinalGauge hhm hbranchData hax).gauge q := by
  show cardScaleT hhm hbranchData hax (Fintype.card B) =
    cardScaleT hhm hbranchData hax (Fintype.card A)
  rw [Fintype.card_congr e.symm]

/-- The cardinal-gauge scale-relabelling equation (`hrel`): the gauged scale is
relabelling-invariant.  `g` is cardinality-only and the raw chain scale is
relabel-invariant (R1). -/
theorem cardinalGauge_hrel
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (cardinalGauge hhm hbranchData hax).gauge (Relabeling.relabelDist e q) *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
          F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        ).scale_factorization.scale (Relabeling.relabelDist e q) =
      (cardinalGauge hhm hbranchData hax).gauge q *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
          F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        ).scale_factorization.scale q := by
  rw [cardinalGauge_gaugeRel hhm hbranchData hax e q,
    scaleRelabel_of_FinalHM_covariance hhm hbranchData hax e q hq]

/-- **The cardinal-gauge support-face equation (`hsupport`).**  With the cardinal
gauge, the raw face-scale equation holds: `(g q / g r)·branchCoeff q r =
(g q·scale q)/(g(r|supp)·scale(r|supp))`.  Proof: `g q = g r = t_n` cancel on the
left; `branchCoeff q r = boundaryCoeff q r`; the general embedding-defect reduction
gives `boundaryCoeff q r·scale(r|supp) = scale q·cardDefect n m`; and the cocycle
`cardDefect n m = t_n / t_m` with `t_m = g(r|supp)` closes it. -/
theorem cardinalGauge_hsupport
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    ((cardinalGauge hhm hbranchData hax).gauge q /
        (cardinalGauge hhm hbranchData hax).gauge r) *
        (BranchAggregationCocycleNormalizedChainRule_of_faithful
          (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
          F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
        ).branch_agg.branchCoeff q r =
      ((cardinalGauge hhm hbranchData hax).gauge q *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale q) /
        ((cardinalGauge hhm hbranchData hax).gauge r.restrictToSupport *
          (BranchAggregationCocycleNormalizedChainRule_of_faithful
            (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
            F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
          ).scale_factorization.scale r.restrictToSupport) := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
  have hgd := general_defect hhm hbranchData hax q r hq hrn hrnd hrb hm2 hmn
  have hratio := cardDefect_eq_ratio hhm hbranchData hax n m hm2 hmn
  have htn := cardScaleT_pos hhm hbranchData hax n
  have htm := cardScaleT_pos hhm hbranchData hax m
  have hscq := faithful_scale_pos hhm hbranchData hax q
  have hscrs := faithful_scale_pos hhm hbranchData hax r.restrictToSupport
  set bc := hb.boundaryCoeff q r
  set sq := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax)).scale_factorization.scale q
  set srs := (BranchAggregationCocycleNormalizedChainRule_of_faithful hfaith F hax
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
      ).scale_factorization.scale r.restrictToSupport
  set tn := cardScaleT hhm hbranchData hax n
  set tm := cardScaleT hhm hbranchData hax m
  rw [hratio] at hgd
  rw [div_self (ne_of_gt htn), one_mul]
  rw [eq_div_iff (by positivity)]
  have hcalc : bc * (tm * srs) = tm * (bc * srs) := by ring
  rw [hcalc, hgd]
  field_simp

/-- Selected cardinal-gauge support-face equation.  This is the hax-specific
counterpart of `cardinalGauge_hsupport`: the support-scale equation follows
from the selected embedding-defect reduction and the selected cardinal cocycle,
with the singleton branch scale already internalized by
`finalHMSingletonScaleNormalizationFor`. -/
theorem cardinalGauge_hsupportFor
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hbranchData : FinalFaithfulBranchAtomicDataFor hhm hax)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    ((cardinalGaugeFor hhm hax hbranchData).gauge q /
        (cardinalGaugeFor hhm hax hbranchData).gauge r) *
        (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
          hhm hax hbranchData
        ).branch_agg.branchCoeff q r =
      ((cardinalGaugeFor hhm hax hbranchData).gauge q *
          (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
            hhm hax hbranchData
          ).scale_factorization.scale q) /
        ((cardinalGaugeFor hhm hax hbranchData).gauge r.restrictToSupport *
          (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
            hhm hax hbranchData
          ).scale_factorization.scale r.restrictToSupport) := by
  classical
  let hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax
  let hlin := affineLinearPart_of_FinalHMInterface hhm
  let hpath :=
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
      hlin finiteLinearFunctionalSameSignScalarOnTangent_of_direct
      (atomicLinearTangentSpanning_of_atomic
        finiteAtomicPosteriorTangentSpanning) F hax hV
  let hb := boundaryFaceScale_of_coefficientScaleNormalization
    hbranchData.boundary_coeff
  let hsingle := finalHMSingletonScaleNormalizationFor hhm hax
  set n := Fintype.card A with hndef
  set m := Fintype.card (supportSubtype r) with hmdef
  haveI : NeZero m := ⟨by have := two_le_card_supp r hrnd; omega⟩
  haveI : NeZero n := ⟨Fintype.card_ne_zero⟩
  have hm2 : 2 ≤ m := two_le_card_supp r hrnd
  have hmn : m < n := card_supp_lt r hrb
  simp only [cardinalGaugeFor, card_supp_restrict r]
  have hbcq :
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).branch_agg.branchCoeff q r = hb.boundaryCoeff q r := by
    rw [show
      (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
        hhm hax hbranchData
      ).branch_agg.branchCoeff q r =
        branchCoeffFromTangentRepParts hpath hb hsingle q r from rfl]
    unfold branchCoeffFromTangentRepParts
    rw [dif_neg hrb, dif_pos hrnd]
  rw [hbcq]
  have hgd := general_defectFor hhm hax hbranchData
    q r hq hrn hrnd hrb hm2 hmn
  have hratio := cardDefect_eq_ratioFor hhm hax hbranchData n m hm2 hmn
  have htn := cardScaleT_posFor hhm hax hbranchData n
  have htm := cardScaleT_posFor hhm hax hbranchData m
  have hscq := faithful_atomic_scale_posFor hhm hax hbranchData q
  have hscrs :=
    faithful_atomic_scale_posFor hhm hax hbranchData r.restrictToSupport
  set bc := hb.boundaryCoeff q r
  set sq :=
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale q
  set srs :=
    (BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax hbranchData
    ).scale_factorization.scale r.restrictToSupport
  set tn := cardScaleTFor hhm hax hbranchData n
  set tm := cardScaleTFor hhm hax hbranchData m
  rw [hratio] at hgd
  rw [div_self (ne_of_gt htn), one_mul]
  rw [eq_div_iff (by positivity)]
  have hcalc : bc * (tm * srs) = tm * (bc * srs) := by
    ring
  rw [hcalc, hgd]
  field_simp

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
from explicit selected covariance and gauge relabelling-equivariance.**

The positive-gauge value functional is `gauge q · V_HM q E`.  Under a finite
relabelling `eA`, `V_HM` is invariant (`FinalSelectedRelabelCovariance`) and the chosen
gauge is invariant (`hgaugeRel`, a harmless equivariance normalization on the
gauge — the same status as the `scale_relabel` field it strengthens), so the
gauged value is invariant.  This produces the selected relabelling package
*without* the `product_normalized` pinning normalization (which is in fact false at
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
    (hcov : FinalSelectedRelabelCovariance hhm)
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
      FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair) :
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
      FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair) :
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
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)
          hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
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
        (integralRepresentationData_of_FinalHMInterface
          hhm)
        hsingleSlice)
      hintercept hslope)
    hcurrentGauge htriple hsingleInteraction

/-- Intercept positive-linearity for the constructed positive-gauge
representative, derived from the HM left-slice theorem, A7 intercept
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
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport)) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          hsingleSlice)) :=
  faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
    (faceScaleProductInterceptSameOrder_of_A7
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          hsingleSlice)))
    (faceScaleProductInterceptPublicMixAffinity_of_HM
      (integralRepresentationData_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          hsingleSlice)))
    (classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
      (integralRepresentationData_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
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
`faceScaleProductSlopeAffine_of_HM_A7_relabeling`, but it uses the selected
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
  have hsame := (faceScaleProductLeftSliceSameOrder_of_A7 hfaces).left_slice_same_order
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
coherent gauge choice `productLiftScale ≡ 1`, a normalization of a value that A5/A7 +
HM-uniqueness *prove* exists and is positive; it is not an opaque assumption. -/
theorem leftCoeff_eq_productLiftScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
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
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (a : A) (r : Dist B) (hAnd : ∃ x y : A, x ≠ y) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (prodDist (Dist.pure a) r) = 1 := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
-- Instantiate first_coordinate_face_value_of_HM with the selected HM value
-- transport theorem plus HM relabel covariance.
theorem faithful_first_coord_face_value
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (hcov : FinalSelectedRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (a : A) (r : Dist B) :
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
        (prodDist (Dist.pure a) r) (experimentOfChannel (productSecondRevealChannel (A := A) (B := B))) =
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  apply first_coordinate_face_value_of_HM
    (hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax)
  · -- support_face_value_transport from the integral representation
    intro F' hax' hV' A' O' _ _ _ _ _ r' _ P'
    exact hbranchData.support_face.support_face_value_transport
      F' hax' hV' r' P'
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
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (hcov : FinalSelectedRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ∃ x y : A, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
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
      rw [faithful_first_coord_face_value hhm hbranchData hax hcov a r]
      rw [show hcnr.chain.scale (prodDist (Dist.pure a) r) = 1 from
        scale_pure_prod_eq_one hhm hbranchData hax a r hAnd]
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
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] (q : Dist A) (b : B) (hBnd : ∃ x y : B, x ≠ y) :
    (BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    ).scale_factorization.scale (prodDist q (Dist.pure b)) = 1 := by
  classical
  set hfaith := faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData
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
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (hcov : FinalSelectedRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hBnd : ∃ x y : B, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
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
          hbranchData.support_face.support_face_value_transport
            F' hax' hV' r' P')
        (fun {A' B' O' Y'} _ _ _ _ _ _ _ _ _ _ eA eO q' P' => hcov.V_relabel_eq hax eA eO q' P')
        hax q b]
      rw [show hcnr.chain.scale (prodDist q (Dist.pure b)) = 1 from
        scale_prod_pure_eq_one hhm hbranchData hax q b hBnd, div_one]
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
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (hcov : FinalSelectedRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ∃ x y : A, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
        (experimentOfChannel (Channel.idChannel : Channel (A × B) (A × B))) =
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
          (experimentOfChannel (productFirstRevealChannel (A := A) (B := B))) +
        hcnr.scale_factorization.scale (prodDist q r) *
          (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  intro hcnr
  have hgov := product_scale_governing_left hhm hbranchData hax hcov q r hq hr hAnd
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set s := hcnr.scale_factorization.scale (prodDist q r) with hsdef
  have hspos : 0 < s := faithful_scale_pos hhm hbranchData hax (prodDist q r)
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
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (hcov : FinalSelectedRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hBnd : ∃ x y : B, x ≠ y) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
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
  have hgov := product_scale_governing_right hhm hbranchData hax hcov q r hq hr hBnd
  set hV := posteriorValueRepresentation_of_FinalHMInterface hhm hax with hVdef
  set s := hcnr.scale_factorization.scale (prodDist q r) with hsdef
  have hspos : 0 < s := faithful_scale_pos hhm hbranchData hax (prodDist q r)
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
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hbranchData : FinalFaithfulBranchData hhm)
    (hax : TraceAxioms F) (hcov : FinalSelectedRelabelCovariance hhm)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ∃ x y : A, x ≠ y)
    (hVr : (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
      (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0) :
    let hcnr := BranchAggregationCocycleNormalizedChainRule_of_faithful
      (faithfulBranchAggregationAssumptions_of_FinalHM_data hhm hbranchData)
      F hax (posteriorValueRepresentation_of_FinalHMInterface hhm hax)
    hcnr.scale_factorization.scale (prodDist q r) =
      ((posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
          (experimentOfChannel (Channel.idChannel : Channel (A × B) (A × B))) -
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V (prodDist q r)
          (experimentOfChannel (productFirstRevealChannel (A := A) (B := B)))) /
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) := by
  intro hcnr
  have hcl := product_scale_cleared_left hhm hbranchData hax hcov q r hq hr hAnd
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
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hAnd : ¬ Subsingleton A) :
    hpair.leftCoeff hax q r = hpair.rightCoeff hax r q := by
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hAnd
  have hval := faceScaleProduct_value_swap_eq_of_value_relabeling hrelV hax hfaces
    q r (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)
  rw [fs_bilinear_right_uninf hpair hax q r hq hr (Channel.idChannel : Channel A A)] at hval
  rw [fs_bilinear_left_uninf hpair hax r q hr hq (Channel.idChannel : Channel A A)] at hval
  exact mul_right_cancel₀ hVnz (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Face-scale swap: `B_{q,r} = A_{r,q}` (nondegenerate second coordinate). -/
theorem fs_rightCoeff_eq_swapped_leftCoeff
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hBnd : ¬ Subsingleton B) :
    hpair.rightCoeff hax q r = hpair.leftCoeff hax r q := by
  have hVnz : hfaces.branch_result.branch_agg.value_rep.V r
      (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hBnd
  have hval := faceScaleProduct_value_swap_eq_of_value_relabeling hrelV hax hfaces
    q r (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B)
  rw [fs_bilinear_left_uninf hpair hax q r hq hr (Channel.idChannel : Channel B B)] at hval
  rw [fs_bilinear_right_uninf hpair hax r q hr hq (Channel.idChannel : Channel B B)] at hval
  exact mul_right_cancel₀ hVnz (by simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Selected face-scale swap: `A_{q,r} = B_{r,q}`. -/
theorem fs_leftCoeff_eq_swapped_rightCoeff_selected
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

/-- Selected face-scale swap: `B_{q,r} = A_{r,q}`. -/
theorem fs_rightCoeff_eq_swapped_leftCoeff_selected
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
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
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
    have hc := hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
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
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
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
    have hc := hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep e e r
      (Channel.idChannel : Channel B B)
    rw [relabelChannel_id_eq e] at hc
    exact hc
  -- LHS values equal via (refl_A × e) covariance
  have hcov : hfaces.branch_result.branch_agg.value_rep.V (prodDist q (Relabeling.relabelDist e r))
        (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B' B'))) =
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B))) := by
    have hc := hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
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

/-- Selected relabel-invariance of `leftCoeff` in the second argument. -/
theorem fs_leftCoeff_relabel_right_selected
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
  have hrq : (Relabeling.relabelDist e r).FullSupport :=
    Relabeling.relabelDist_fullSupport e r hr
  have h1 := fs_bilinear_right_uninf hpair hax q (Relabeling.relabelDist e r) hq hrq
    (Channel.idChannel : Channel A A)
  have h2 := fs_bilinear_right_uninf hpair hax q r hq hr (Channel.idChannel : Channel A A)
  have hcov : hfaces.branch_result.branch_agg.value_rep.V (prodDist q (Relabeling.relabelDist e r))
        (experimentOfChannel (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B'))) =
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B))) := by
    have hc := hsel.V_relabel_eq hax
      ((Equiv.refl A).prodCongr e) ((Equiv.refl A).prodCongr (Equiv.refl PUnit.{u+1}))
      (prodDist q r) (prodChannel (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B))
    rw [Relabeling.relabelDist_prodCongr, Relabeling.relabelChannel_prodCongr] at hc
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

/-- Selected relabel-invariance of `rightCoeff` in the second argument. -/
theorem fs_rightCoeff_relabel_right_selected
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
  have hrq : (Relabeling.relabelDist e r).FullSupport :=
    Relabeling.relabelDist_fullSupport e r hr
  have h1 := fs_bilinear_left_uninf hpair hax q (Relabeling.relabelDist e r) hq hrq
    (Channel.idChannel : Channel B' B')
  have h2 := fs_bilinear_left_uninf hpair hax q r hq hr (Channel.idChannel : Channel B B)
  have hVe : hfaces.branch_result.branch_agg.value_rep.V (Relabeling.relabelDist e r)
        (experimentOfChannel (Channel.idChannel : Channel B' B')) =
      hfaces.branch_result.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) := by
    have hc := hsel.V_relabel_eq hax e e r (Channel.idChannel : Channel B B)
    rw [relabelChannel_id_eq e] at hc
    exact hc
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

/-- Selected value relabeling is preserved by coherent prior-gauge transforms. -/
theorem finiteSelectedPosteriorValueRelabeling_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteSelectedPosteriorValueRelabelingFor
      (hfaces.gaugeTransform hgauge) where
  V_relabel_eq := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    dsimp [CoherentRelabelingFaceScalesStructure.gaugeTransform,
      branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      branchAggregationStructure_gaugeTransform,
      posteriorValueRepresentation_gaugeTransform]
    rw [hgauge.gauge_relabel_eq eA q]
    rw [hsel.V_relabel_eq hax eA eO q P]

/-- Exact selected boundary-value transport is preserved by a coherent gauge.
For nondegenerate boundary priors this is the gauge support axiom; for
full-support priors it is relabelling coherence; singleton faces have zero
value on both sides. -/
theorem finiteBoundaryValueSupportRead_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hboundary : FiniteBoundaryValueSupportReadFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteBoundaryValueSupportReadFor
      (hfaces.gaugeTransform hgauge) where
  boundary_value_support := by
    intro A O _ _ _ _ _ q _ P
    classical
    have hbase := hboundary.boundary_value_support q P
    dsimp [CoherentRelabelingFaceScalesStructure.gaugeTransform,
      branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      branchAggregationStructure_gaugeTransform,
      posteriorValueRepresentation_gaugeTransform]
    by_cases hqf : q.FullSupport
    · have hdist :=
        restrictToSupport_fullSupport_eq_relabel q hqf
      have hg :
          hgauge.gauge q.restrictToSupport = hgauge.gauge q := by
        rw [hdist]
        exact hgauge.gauge_relabel_eq
          (fullSupportRestrictEquiv q hqf).symm q
      rw [hg, hbase]
    · by_cases hnd :
          ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
      · let a0 : supportSubtype q :=
          Classical.choice (supportSubtype_nonempty q)
        have hn : ∃ a : A, 0 < q a := ⟨a0.1, a0.2⟩
        have hg :=
          hgauge.gauge_support_restrict_eq q hn hnd hqf
        rw [hg, hbase]
      · have hss : Subsingleton (supportSubtype q) := by
          rw [subsingleton_iff]
          rintro ⟨a, ha⟩ ⟨b, hb⟩
          by_contra hab
          exact hnd
            ⟨a, b, fun h => hab (Subtype.ext h), ha, hb⟩
        letI : Subsingleton (supportSubtype q) := hss
        have hz :
            hfaces.branch_result.branch_agg.value_rep.V
                q.restrictToSupport
                (experimentOfChannel
                  (Channel.restrictToSupport P q)) = 0 :=
          branchValue_channel_eq_zero_of_subsingleton
            F hfaces.branch_result.branch_agg.value_rep
            q.restrictToSupport
            (Dist.restrictToSupport_fullSupport q)
            (Channel.restrictToSupport P q)
        have hzq :
            hfaces.branch_result.branch_agg.value_rep.V q
                (experimentOfChannel P) = 0 :=
          hbase.trans hz
        rw [hzq, hz, mul_zero, mul_zero]

/-- Full-revelation value is unchanged when a full-support prior is read on its
support face. -/
theorem fullRevelationValueForFaceScales_restrictToSupport_fullSupport_eq_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) :
    hfaces.branch_result.branch_agg.value_rep.V
        r.restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport (Channel.idChannel : Channel A A) r)) =
      fullRevelationValueForFaceScales hfaces r := by
  classical
  let e : A ≃ supportSubtype r := (fullSupportRestrictEquiv r hr).symm
  have hdist :
      r.restrictToSupport = Relabeling.relabelDist e r := by
    simpa [e] using restrictToSupport_fullSupport_eq_relabel r hr
  have hchan :
      Channel.restrictToSupport (Channel.idChannel : Channel A A) r =
        Relabeling.relabelChannel e (Equiv.refl A)
          (Channel.idChannel : Channel A A) := by
    ext x y
    simp [e, fullSupportRestrictEquiv, Channel.restrictToSupport,
      Relabeling.relabelChannel, Channel.idChannel]
  have hrel :=
    hsel.V_relabel_eq hax e (Equiv.refl A) r
      (Channel.idChannel : Channel A A)
  rw [← hdist, ← hchan] at hrel
  simpa [fullRevelationValueForFaceScales] using hrel

/-- Full-revelation value is unchanged when a full-support prior is read on its
support face with the identity channel on that support face. -/
theorem fullRevelationValueForFaceScales_restrictToSupport_idSupport_fullSupport_eq_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) :
    hfaces.branch_result.branch_agg.value_rep.V
        r.restrictToSupport
        (experimentOfChannel
          (Channel.idChannel :
            Channel (supportSubtype r) (supportSubtype r))) =
      fullRevelationValueForFaceScales hfaces r := by
  classical
  let e : A ≃ supportSubtype r := (fullSupportRestrictEquiv r hr).symm
  have hdist :
      r.restrictToSupport = Relabeling.relabelDist e r := by
    simpa [e] using restrictToSupport_fullSupport_eq_relabel r hr
  have hrel :=
    hsel.V_relabel_eq hax e e r (Channel.idChannel : Channel A A)
  rw [relabelChannel_id_eq e] at hrel
  rw [← hdist] at hrel
  simpa [fullRevelationValueForFaceScales] using hrel

/-- Chain scale is unchanged when a full-support prior is read on its support
face. -/
theorem faceScale_scale_restrictToSupport_fullSupport_eq
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) (hr : r.FullSupport) :
    hfaces.branch_result.scale_factorization.scale r.restrictToSupport =
      hfaces.branch_result.scale_factorization.scale r := by
  rw [restrictToSupport_fullSupport_eq_relabel r hr]
  exact
    CoherentRelabelingFaceScalesStructure.scale_relabel_eq hfaces
      (fullSupportRestrictEquiv r hr).symm r hr

/-- Support-read coordinate continuation value transport from selected
relabeling invariance. -/
theorem coordinateSupportFaceValueSupportRead_of_selectedRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces) :
    FiniteCoordinateSupportFaceValueSupportReadFor hfaces where
  first_coordinate_face_value_support := by
    intro hax A B _ _ _ _ _ _ q r hq hr _hA _hB a
    have ha : 0 < q a := hq a
    rw [posterior_productFirstRevealChannel_prodDist_of_pos q r a ha]
    rw [restrict_pureProd a r, restrictChannel_pureProd_secondReveal a r]
    have hrel :=
      hsel.V_relabel_eq hax (pureProdSupportEquiv a r).symm (Equiv.refl B)
        r.restrictToSupport
        (Channel.restrictToSupport (Channel.idChannel : Channel B B) r)
    rw [hrel]
    exact
      fullRevelationValueForFaceScales_restrictToSupport_fullSupport_eq_selected
        hsel hax r hr
  second_coordinate_face_value_support := by
    intro hax A B _ _ _ _ _ _ q r hq hr _hA _hB b
    have hb : 0 < r b := hr b
    rw [posterior_productSecondRevealChannel_prodDist_of_pos q r b hb]
    rw [restrict_prodPure q b, restrictChannel_prodPure_firstReveal q b]
    have hrel :=
      hsel.V_relabel_eq hax (prodPureSupportEquiv q b).symm (Equiv.refl A)
        q.restrictToSupport
        (Channel.restrictToSupport (Channel.idChannel : Channel A A) q)
    rw [hrel]
    exact
      fullRevelationValueForFaceScales_restrictToSupport_fullSupport_eq_selected
        hsel hax q hq

/-- Support-read coordinate continuation scale transport from coherent scale
relabeling. -/
theorem coordinateSupportFaceScaleSupportRead_of_relabeling
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteCoordinateSupportFaceScaleSupportReadFor hfaces where
  first_coordinate_face_scale_support := by
    intro _hax A B _ _ _ _ _ _ q r hq hr _hA _hB a
    have ha : 0 < q a := hq a
    rw [posterior_productFirstRevealChannel_prodDist_of_pos q r a ha]
    rw [restrict_pureProd a r]
    rw [CoherentRelabelingFaceScalesStructure.scale_relabel_eq hfaces
      (pureProdSupportEquiv a r).symm r.restrictToSupport
      (Dist.restrictToSupport_fullSupport r)]
    exact faceScale_scale_restrictToSupport_fullSupport_eq hfaces r hr
  second_coordinate_face_scale_support := by
    intro _hax A B _ _ _ _ _ _ q r hq hr _hA _hB b
    have hb : 0 < r b := hr b
    rw [posterior_productSecondRevealChannel_prodDist_of_pos q r b hb]
    rw [restrict_prodPure q b]
    rw [CoherentRelabelingFaceScalesStructure.scale_relabel_eq hfaces
      (prodPureSupportEquiv q b).symm q.restrictToSupport
      (Dist.restrictToSupport_fullSupport q)]
    exact faceScale_scale_restrictToSupport_fullSupport_eq hfaces q hq

/-- Support-read block value transport from selected relabeling invariance. -/
theorem blockSupportFaceValueSupportRead_of_selectedRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces) :
    FiniteBlockSupportFaceValueSupportReadFor hfaces where
  block_face_value_support := by
    intro hax K _ _ _ Act _ _ _ _ k q hq
    rw [restrict_blockEmbed_eq_relabel_support Act k q]
    have hrel :=
      hsel.V_relabel_eq hax
        (blockEmbedSupportEquiv Act k q).symm
        (blockEmbedSupportEquiv Act k q).symm
        q.restrictToSupport
        (Channel.idChannel : Channel (supportSubtype q) (supportSubtype q))
    rw [relabelChannel_id_eq (blockEmbedSupportEquiv Act k q).symm] at hrel
    rw [hrel]
    exact
      fullRevelationValueForFaceScales_restrictToSupport_idSupport_fullSupport_eq_selected
        hsel hax q hq

/-- Support-read block scale transport from coherent scale relabeling. -/
theorem blockSupportFaceScaleSupportRead_of_relabeling
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteBlockSupportFaceScaleSupportReadFor hfaces where
  block_face_scale_support := by
    intro _hax K _ _ _ Act _ _ _ _ k q hq
    rw [restrict_blockEmbed_eq_relabel_support Act k q]
    rw [CoherentRelabelingFaceScalesStructure.scale_relabel_eq hfaces
      (blockEmbedSupportEquiv Act k q).symm q.restrictToSupport
      (Dist.restrictToSupport_fullSupport q)]
    exact faceScale_scale_restrictToSupport_fullSupport_eq hfaces q hq

theorem cobGaugeSF_support_restrict
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
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
  rw [fs_leftCoeff_relabel_right hpair hrelV hax faceScaleInteractionReferencePrior rs
      (fullSupportRestrictEquiv rs hrsfs).symm faceScaleInteractionReferencePrior_fullSupport hrsfs
      faceScaleInteractionReference_not_subsingleton]
  rw [fs_rightCoeff_relabel_right hpair hrelV hax faceScaleInteractionReferencePrior rs
      (fullSupportRestrictEquiv rs hrsfs).symm faceScaleInteractionReferencePrior_fullSupport hrsfs hnd]


theorem cobGaugeSF_relabel
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
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
    rw [fs_leftCoeff_relabel_right hpair hrelV hax faceScaleInteractionReferencePrior
        q.restrictToSupport (relabelSupportEquiv e q).symm
        faceScaleInteractionReferencePrior_fullSupport hqsfs
        faceScaleInteractionReference_not_subsingleton]
    rw [fs_rightCoeff_relabel_right hpair hrelV hax faceScaleInteractionReferencePrior
        q.restrictToSupport (relabelSupportEquiv e q).symm
        faceScaleInteractionReferencePrior_fullSupport hqsfs hnd]


/-- On full-support (nondegenerate) priors, `cobGaugeSF` agrees with `cobGauge`. -/
theorem cobGaugeSF_eq_cobGauge_of_fullSupport
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
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
  rw [fs_leftCoeff_relabel_right hpair hrelV hax faceScaleInteractionReferencePrior r
      (fullSupportRestrictEquiv r hr).symm faceScaleInteractionReferencePrior_fullSupport hr
      faceScaleInteractionReference_not_subsingleton]
  rw [fs_rightCoeff_relabel_right hpair hrelV hax faceScaleInteractionReferencePrior r
      (fullSupportRestrictEquiv r hr).symm faceScaleInteractionReferencePrior_fullSupport hr hnd]

/-- Selected support-restriction invariance of the support-face coboundary gauge. -/
theorem cobGaugeSF_support_restrict_selected
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
  have hnd2 : ¬ Subsingleton (supportSubtype r.restrictToSupport) := by
    rw [not_subsingleton_iff_nontrivial] at hnd ⊢
    obtain ⟨a, b, hab⟩ := hnd
    refine ⟨⟨a, by rw [Dist.restrictToSupport_apply]; exact a.2⟩,
      ⟨b, by rw [Dist.restrictToSupport_apply]; exact b.2⟩, ?_⟩
    intro h; exact hab (congrArg Subtype.val h)
  unfold cobGaugeSF
  rw [if_neg hnd, if_neg hnd2]
  set rs := r.restrictToSupport with hrsdef
  rw [restrictToSupport_fullSupport_eq_relabel rs hrsfs]
  rw [fs_leftCoeff_relabel_right_selected hpair hsel hax faceScaleInteractionReferencePrior rs
      (fullSupportRestrictEquiv rs hrsfs).symm faceScaleInteractionReferencePrior_fullSupport hrsfs
      faceScaleInteractionReference_not_subsingleton]
  rw [fs_rightCoeff_relabel_right_selected hpair hsel hax faceScaleInteractionReferencePrior rs
      (fullSupportRestrictEquiv rs hrsfs).symm faceScaleInteractionReferencePrior_fullSupport hrsfs hnd]

/-- Selected relabel-invariance of the support-face coboundary gauge. -/
theorem cobGaugeSF_relabel_selected
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) :
    cobGaugeSF hpair hax (Relabeling.relabelDist e q) = cobGaugeSF hpair hax q := by
  classical
  have hequiv : Subsingleton (supportSubtype (Relabeling.relabelDist e q)) ↔
      Subsingleton (supportSubtype q) :=
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
    rw [fs_leftCoeff_relabel_right_selected hpair hsel hax faceScaleInteractionReferencePrior
        q.restrictToSupport (relabelSupportEquiv e q).symm
        faceScaleInteractionReferencePrior_fullSupport hqsfs
        faceScaleInteractionReference_not_subsingleton]
    rw [fs_rightCoeff_relabel_right_selected hpair hsel hax faceScaleInteractionReferencePrior
        q.restrictToSupport (relabelSupportEquiv e q).symm
        faceScaleInteractionReferencePrior_fullSupport hqsfs hnd]

/-- On full-support nondegenerate priors, selected `cobGaugeSF` agrees with
`cobGauge`. -/
theorem cobGaugeSF_eq_cobGauge_of_fullSupport_selected
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
  rw [restrictToSupport_fullSupport_eq_relabel r hr]
  rw [fs_leftCoeff_relabel_right_selected hpair hsel hax faceScaleInteractionReferencePrior r
      (fullSupportRestrictEquiv r hr).symm faceScaleInteractionReferencePrior_fullSupport hr
      faceScaleInteractionReference_not_subsingleton]
  rw [fs_rightCoeff_relabel_right_selected hpair hsel hax faceScaleInteractionReferencePrior r
      (fullSupportRestrictEquiv r hr).symm faceScaleInteractionReferencePrior_fullSupport hr hnd]

/-- The selected support-face coboundary is a coherent positive prior gauge. -/
noncomputable def cobGaugeSFGauge_selected
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) :
    CoherentFaceScaleGauge.{u} where
  gauge := fun {_} _ _ _ q => cobGaugeSF hpair hax q
  gauge_pos := by
    intro A _ _ _ q
    exact cobGaugeSF_pos hpair hax q
  gauge_relabel_eq := by
    intro A B _ _ _ _ _ _ e q
    exact cobGaugeSF_relabel_selected hpair hsel hax e q
  gauge_support_restrict_eq := by
    intro A _ _ _ r _ _hr_nonempty hr_nondegenerate _hr_boundary
    exact cobGaugeSF_support_restrict_selected hpair hsel hax r hr_nondegenerate

/-- The selected coboundary gauge normalizes the left product coefficient on
nondegenerate first factors for the active `hax`. -/
theorem cobGaugeSFGauge_leftCoeff_normalized_selected
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) :
    faceScaleGaugeTransformedLeftCoeff hpair
        (cobGaugeSFGauge_selected hpair hsel hax) hax q r = 1 := by
  classical
  have hprod : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  have hAB : ¬ Subsingleton (A × B) := by
    intro hsub
    apply hA
    refine ⟨?_⟩
    intro a a'
    have hp : (a, Classical.arbitrary B) = (a', Classical.arbitrary B) :=
      Subsingleton.elim _ _
    exact congrArg Prod.fst hp
  have hgq_ne : cobGauge hpair hax q ≠ 0 :=
    ne_of_gt (cobGauge_pos hpair hax q hq)
  have hgp_ne : cobGauge hpair hax (prodDist q r) ≠ 0 :=
    ne_of_gt (cobGauge_pos hpair hax (prodDist q r) hprod)
  dsimp [faceScaleGaugeTransformedLeftCoeff, cobGaugeSFGauge_selected]
  rw [cobGaugeSF_eq_cobGauge_of_fullSupport_selected hpair hsel hax q hq hA]
  rw [cobGaugeSF_eq_cobGauge_of_fullSupport_selected hpair hsel hax
    (prodDist q r) hprod hAB]
  rw [cobGauge_coboundary hpair htriple hax q r hq hr hA]
  field_simp [hgq_ne, hgp_ne]

/-- The selected coboundary gauge normalizes the right product coefficient on
nondegenerate second factors for the active `hax`. -/
theorem cobGaugeSFGauge_rightCoeff_normalized_selected
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hB : ¬ Subsingleton B) :
    faceScaleGaugeTransformedRightCoeff hpair
        (cobGaugeSFGauge_selected hpair hsel hax) hax q r = 1 := by
  classical
  have hprod_rq : (prodDist r q).FullSupport :=
    prodDist_fullSupport r q hr hq
  have hBA : ¬ Subsingleton (B × A) := by
    intro hsub
    apply hB
    refine ⟨?_⟩
    intro b b'
    have hp : (b, Classical.arbitrary A) = (b', Classical.arbitrary A) :=
      Subsingleton.elim _ _
    exact congrArg Prod.fst hp
  have hgprod :
      cobGaugeSF hpair hax (prodDist q r) =
        cobGaugeSF hpair hax (prodDist r q) := by
    have hrel :=
      cobGaugeSF_relabel_selected hpair hsel hax
        (Equiv.prodComm A B) (prodDist q r)
    simpa [relabelDist_prodComm q r] using hrel.symm
  have hgr_ne : cobGauge hpair hax r ≠ 0 :=
    ne_of_gt (cobGauge_pos hpair hax r hr)
  have hgp_ne : cobGauge hpair hax (prodDist r q) ≠ 0 :=
    ne_of_gt (cobGauge_pos hpair hax (prodDist r q) hprod_rq)
  dsimp [faceScaleGaugeTransformedRightCoeff, cobGaugeSFGauge_selected]
  rw [fs_rightCoeff_eq_swapped_leftCoeff_selected hpair hsel hax q r hq hr hB]
  rw [hgprod]
  rw [cobGaugeSF_eq_cobGauge_of_fullSupport_selected hpair hsel hax r hr hB]
  rw [cobGaugeSF_eq_cobGauge_of_fullSupport_selected hpair hsel hax
    (prodDist r q) hprod_rq hBA]
  rw [cobGauge_coboundary hpair htriple hax r q hr hq hB]
  field_simp [hgr_ne, hgp_ne]

end FaceScaleProductCocycle

/-- Current-representative nondegenerate product-gauge normalization. -/
structure FiniteFaceScaleProductGaugeNormalizationNondegenerateFor
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  leftCoeff_normalized_nd :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A),
      hpair.leftCoeff hax q r = 1
  rightCoeff_normalized_nd :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hB : ¬ Subsingleton B),
      hpair.rightCoeff hax q r = 1

/-- Nondegenerate product-gauge transform data.

Unlike `FiniteFaceScaleProductGaugeTransformFor`, this does not impose
normalization on behaviorally unidentified singleton-factor coefficients. -/
structure FiniteFaceScaleProductGaugeTransformNondegenerateFor
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    where
  gauge : CoherentFaceScaleGauge.{u}
  transformed_leftCoeff_normalized_nd :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A),
      faceScaleGaugeTransformedLeftCoeff hpair gauge hax q r = 1
  transformed_rightCoeff_normalized_nd :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hB : ¬ Subsingleton B),
      faceScaleGaugeTransformedRightCoeff hpair gauge hax q r = 1

/-- Normalized product bilinear form using only nondegenerate coefficient
normalization. -/
theorem faceScaleProductPairBilinear_normalized_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm :
      FiniteFaceScaleProductGaugeNormalizationNondegenerateFor hpair)
    (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (P : Channel A O) (R : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) +
      hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel R) +
      hpair.interactionCoeff hax q r *
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) *
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear hax q r hq hr P R]
  rw [hnorm.leftCoeff_normalized_nd hax q r hq hr hA]
  rw [hnorm.rightCoeff_normalized_nd hax q r hq hr hB]
  ring

/-- Coefficient extraction from triple-product value associativity and
nondegenerate product-gauge normalization. -/
theorem faceScaleTripleProductCoeffExtraction_of_valueAssociativity_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    {hnorm : FiniteFaceScaleProductGaugeNormalizationNondegenerateFor hpair}
    {htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces} :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair where
  interaction_assoc_xy := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
    have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
    have hxne :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hyne :
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
    have hxyne :
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel (Channel.idChannel : Channel A A)) *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      mul_ne_zero hxne hyne
    have hval :=
      htriple.triple_value_assoc hax q r s hq hr hs
        (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C)
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.idChannel : Channel B B))
        (Channel.uninformativeChannelU C)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.uninformativeChannelU C))] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q r hq hr hA hB
        (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        r s hr hs hB hC
        (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized s hs] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxyne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_xz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
    have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
    have hxne :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
    have hxzne :
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel (Channel.idChannel : Channel A A)) *
          hfaces.branch_result.branch_agg.value_rep.V s
            (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      mul_ne_zero hxne hzne
    have hval :=
      htriple.triple_value_assoc hax q r s hq hr hs
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C)
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.uninformativeChannelU B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q r hq hr hA hB
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        r s hr hs hB hC
        (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_yz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hAB : ¬ Subsingleton (A × B) := not_subsingleton_prod_left hA
    have hBC : ¬ Subsingleton (B × C) := not_subsingleton_prod_left hB
    have hyne :
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
    have hyzne :
        hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) *
          hfaces.branch_result.branch_agg.value_rep.V s
            (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
      mul_ne_zero hyne hzne
    have hval :=
      htriple.triple_value_assoc hax q r s hq hr hs
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C)
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        (prodDist q r) s hqr hs hAB hC
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q (prodDist r s) hq hrs hA hBC
        (Channel.uninformativeChannelU A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        q r hq hr hA hB
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized_nondegenerate hpair hnorm hax
        r s hr hs hB hC
        (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hyzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Product quasi-additivity from pairwise bilinearity, nondegenerate
normalization, and interaction associativity. Singleton factors are handled by
value-zero, not coefficient normalizations. -/
noncomputable def productQuasiAdditivityForFaceScales_of_components_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm :
      FiniteFaceScaleProductGaugeNormalizationNondegenerateFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces where
  kappa := faceScaleInteractionReferenceKappa hpair
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    by_cases hsubA : Subsingleton A
    · haveI : Subsingleton A := hsubA
      have hVq :
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep q hq P
      rw [hVq]
      by_cases hsubB : Subsingleton B
      · haveI : Subsingleton B := hsubB
        have hVr :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) = 0 :=
          branchValue_channel_eq_zero_of_subsingleton F
            hfaces.branch_result.branch_agg.value_rep r hr R
        rw [hVr]
        ring
      · rw [hnorm.rightCoeff_normalized_nd hax q r hq hr hsubB]
        ring
    · by_cases hsubB : Subsingleton B
      · haveI : Subsingleton B := hsubB
        have hVr :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) = 0 :=
          branchValue_channel_eq_zero_of_subsingleton F
            hfaces.branch_result.branch_agg.value_rep r hr R
        rw [hVr]
        rw [hnorm.leftCoeff_normalized_nd hax q r hq hr hsubA]
        ring
      · rw [hnorm.leftCoeff_normalized_nd hax q r hq hr hsubA]
        rw [hnorm.rightCoeff_normalized_nd hax q r hq hr hsubB]
        rw [faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc hax q r hq hr hsubA hsubB]
        ring

/-- Product quasi-additivity for a coherently transformed representative using
only nondegenerate product normalization. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge :
      FiniteFaceScaleProductGaugeTransformNondegenerateFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_components_nondegenerate
    (faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
    { leftCoeff_normalized_nd := by
        intro hax A B _ _ _ _ _ _ q r hq hr hA
        exact hgauge.transformed_leftCoeff_normalized_nd hax q r hq hr hA
      rightCoeff_normalized_nd := by
        intro hax A B _ _ _ _ _ _ q r hq hr hB
        exact hgauge.transformed_rightCoeff_normalized_nd hax q r hq hr hB }
    (faceScaleTripleProductCoeffExtraction_of_valueAssociativity_nondegenerate
      (hpair := faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
      (hnorm :=
        { leftCoeff_normalized_nd := by
            intro hax A B _ _ _ _ _ _ q r hq hr hA
            exact hgauge.transformed_leftCoeff_normalized_nd hax q r hq hr hA
          rightCoeff_normalized_nd := by
            intro hax A B _ _ _ _ _ _ q r hq hr hB
            exact hgauge.transformed_rightCoeff_normalized_nd hax q r hq hr hB })
      (htriple := faceScaleTripleProductValueAssociativity_gaugeTransform
        htriple hgauge.gauge))

/-- The selected coboundary gauge gives the nondegenerate product-normalization
transform for the selected `hax`. Universality over proof arguments follows
from proof irrelevance of `TraceAxioms F`. -/
noncomputable def cobGaugeSFProductTransform_selected
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (htriple : FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hax0 : TraceAxioms F) :
    FiniteFaceScaleProductGaugeTransformNondegenerateFor hpair where
  gauge := cobGaugeSFGauge_selected hpair hsel hax0
  transformed_leftCoeff_normalized_nd := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA
    have hp : hax = hax0 := Subsingleton.elim _ _
    cases hp
    exact cobGaugeSFGauge_leftCoeff_normalized_selected
      hpair hsel htriple hax0 q r hq hr hA
  transformed_rightCoeff_normalized_nd := by
    intro hax A B _ _ _ _ _ _ q r hq hr hB
    have hp : hax = hax0 := Subsingleton.elim _ _
    cases hp
    exact cobGaugeSFGauge_rightCoeff_normalized_selected
      hpair hsel htriple hax0 q r hq hr hB


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
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)))
    (hcurrentGauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
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
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
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
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hnorm :
      FiniteSelectedPosteriorValueRelabelingFor
        (coherentFaceScales_of_FinalHM_positiveGauge
          hhm hfaith hax hgauge hrel hsupport))
    (hcurrentGauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
              hhm)
            hsingleSlice)
          (productInterceptPositiveLinear_of_FinalHM_positiveGauge
            hhm hfaith hax hgauge hrel hsupport hsingleSlice)
          (faceScaleProductSlopeAffine_of_selectedRelabeling
            hnorm
            (productInterceptPositiveLinear_of_FinalHM_positiveGauge
              hhm hfaith hax hgauge hrel hsupport hsingleSlice))))
    (hsingleInteraction :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
            (integralRepresentationData_of_FinalHMInterface
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
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)) :
    FiniteProductQuasiAdditivityForFaceScales
      (productNormalizedFaceScales_of_FinalHM_gauge
        hhm hfaith hax hscaleRelabel hfaceScale hpair hgauge) :=
  productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData
    hpair hgauge htriple hsingle
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

/-- Boundary-completed normalized-value transport from exact transport of the
selected value representative.  No pointwise convention on an integral test
function is used. -/
theorem field1_boundaryComplete_of_selectedValue
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    (hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
      [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a)
      (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hs.branch_agg.branchCoeff q r =
        hs.scale q / hs.scale r.restrictToSupport)
    (hvalue :
      ∀ {A O : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype O] [DecidableEq O]
        (q : Dist A) [Nonempty (supportSubtype q)] (P : Channel A O),
        hs.branch_agg.value_rep.V q (experimentOfChannel P) =
          hs.branch_agg.value_rep.V q.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport P q)))
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (hqb : ¬ q.FullSupport) :
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    normalizedValue (boundaryCompleteScale hs hsf) q P =
      normalizedValue (boundaryCompleteScale hs hsf) q.restrictToSupport
        (Channel.restrictToSupport P q) := by
  classical
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hnum := hvalue q P
  change hs.branch_agg.value_rep.V q (experimentOfChannel P) /
      wrapScale hs q =
    hs.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) /
      wrapScale hs q.restrictToSupport
  rw [hnum]
  rw [wrapScale_fullSupport hs q.restrictToSupport
    (Dist.restrictToSupport_fullSupport q)]
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

open Classical in
/-- Boundary-completed chain scale for a coherent face-scale package, before
the final universal-scale field has been proved.  Full-support and singleton
priors keep the original chain scale; nondegenerate boundary priors are read on
their support face. -/
noncomputable def faceSupportReadScale
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  if (¬ q.FullSupport ∧ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) then
    hfaces.branch_result.scale_factorization.scale q.restrictToSupport
  else
    hfaces.branch_result.scale_factorization.scale q

theorem faceSupportReadScale_fullSupport
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    faceSupportReadScale hfaces q =
      hfaces.branch_result.scale_factorization.scale q := by
  classical
  simp only [faceSupportReadScale]
  rw [if_neg (by rintro ⟨hnf, _⟩; exact hnf hq)]

theorem faceSupportReadScale_boundary_nondeg
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnf : ¬ q.FullSupport)
    (hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    faceSupportReadScale hfaces q =
      hfaces.branch_result.scale_factorization.scale q.restrictToSupport := by
  classical
  simp only [faceSupportReadScale]
  rw [if_pos ⟨hnf, hnd⟩]

theorem faceSupportReadScale_singleton
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hnd : ¬ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b) :
    faceSupportReadScale hfaces q =
      hfaces.branch_result.scale_factorization.scale q := by
  classical
  simp only [faceSupportReadScale]
  rw [if_neg (by rintro ⟨_, hc⟩; exact hnd hc)]

/-- The support-read branch-chain package induced by coherent face scales.

This is not a new arbitrary gauge: it is the WLOG support-face reading of the
same branch aggregation, with the branch-coefficient factorization re-proved
from the already available support-face scale theorem. -/
noncomputable def supportReadBranchChain
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F) :
    BranchChainStructure F where
  branch_agg := hfaces.branch_result.branch_agg
  scale := fun {A} _ _ _ q => faceSupportReadScale hfaces q
  scale_pos := by
    intro A _ _ _ q hq
    rw [faceSupportReadScale_fullSupport hfaces q hq]
    exact hfaces.branch_result.scale_factorization.scale_pos q hq
  branchCoeff_factorization := by
    classical
    intro A O _ _ _ _ _ q hq P o hpos
    set r := Channel.posterior P q o with hrdef
    rw [faceSupportReadScale_fullSupport hfaces q hq]
    by_cases hrfull : r.FullSupport
    · rw [faceSupportReadScale_fullSupport hfaces r hrfull]
      exact hfaces.branch_result.scale_factorization.branchCoeff_factorization
        q hq P o hpos
    · by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b
      · haveI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
        obtain ⟨a0, b0, hab0, ha0, hb0⟩ := hnd
        rw [faceSupportReadScale_boundary_nondeg hfaces r hrfull
          ⟨a0, b0, hab0, ha0, hb0⟩]
        exact hfaces.support_face_scale_eq q hq r ⟨a0, ha0⟩
          ⟨a0, b0, hab0, ha0, hb0⟩ hrfull
      · rw [faceSupportReadScale_singleton hfaces r hnd]
        exact hfaces.branch_result.scale_factorization.branchCoeff_factorization
          q hq P o hpos

/-- Normalized values for the support-read branch chain are unchanged by
restricting a boundary prior to its positive support.  The numerator equality
is the HM/posterior-integral support-face theorem; the denominator equality is
the support-read scale definition. -/
theorem branchNormalizedValue_supportRead_restrictToSupport
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (hqb : ¬ q.FullSupport) :
    branchNormalizedValue (supportReadBranchChain hfaces) q P =
      branchNormalizedValue (supportReadBranchChain hfaces)
        q.restrictToSupport (Channel.restrictToSupport P q) := by
  classical
  haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hnum := hboundaryValue.boundary_value_support q P
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) /
        faceSupportReadScale hfaces q =
      hfaces.branch_result.branch_agg.value_rep.V q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q)) /
        faceSupportReadScale hfaces q.restrictToSupport
  rw [hnum]
  rw [faceSupportReadScale_fullSupport hfaces q.restrictToSupport
    (Dist.restrictToSupport_fullSupport q)]
  by_cases hnd : ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b
  · rw [faceSupportReadScale_boundary_nondeg hfaces q hqb hnd]
  · have hss : Subsingleton (supportSubtype q) := by
      rw [subsingleton_iff]
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      by_contra hne
      exact hnd ⟨a, b, fun h => hne (Subtype.ext h), ha, hb⟩
    haveI := hss
    have hz : hfaces.branch_result.branch_agg.value_rep.V q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) = 0 :=
      branchValue_channel_eq_zero_of_subsingleton F
        hfaces.branch_result.branch_agg.value_rep
        q.restrictToSupport (Dist.restrictToSupport_fullSupport q)
        (Channel.restrictToSupport P q)
    rw [hz, zero_div, zero_div]

/-- First-coordinate continuation value for the support-read branch chain.

The posterior after revealing `a` is ambient-boundary, but the normalized
continuation is evaluated by first restricting that posterior to its support
face. -/
theorem first_coordinate_supportRead_branchNormalizedValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (a : A) :
    branchNormalizedValue (supportReadBranchChain hfaces)
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (productSecondRevealChannel (A := A) (B := B)) =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r := by
  classical
  have ha : 0 < q a := hq a
  have hpost :
      Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a =
        prodDist (Dist.pure a) r :=
    posterior_productFirstRevealChannel_prodDist_of_pos q r a ha
  have hnotfull : ¬ (prodDist (Dist.pure a) r).FullSupport := by
    intro hfs
    haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    rcases exists_ne a with ⟨a', ha'⟩
    have hp := hfs (a', Classical.arbitrary B)
    rw [prodDist_apply_pair,
      Dist.pure_apply_ne a a' ha', zero_mul] at hp
    exact lt_irrefl 0 hp
  have hrestrict :=
    branchNormalizedValue_supportRead_restrictToSupport
      hfaces hboundaryValue (productSecondRevealChannel (A := A) (B := B))
      (prodDist (Dist.pure a) r) hnotfull
  have hv := hvalue.first_coordinate_face_value_support
    hax q r hq hr hA hB a
  have hs := hscale.first_coordinate_face_scale_support
    hax q r hq hr hA hB a
  rw [hpost] at hv
  rw [hpost] at hs
  rw [hpost]
  rw [hrestrict]
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (prodDist (Dist.pure a) r).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productSecondRevealChannel (A := A) (B := B))
            (prodDist (Dist.pure a) r))) /
        faceSupportReadScale hfaces (prodDist (Dist.pure a) r).restrictToSupport =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r
  rw [faceSupportReadScale_fullSupport hfaces
    (prodDist (Dist.pure a) r).restrictToSupport
    (Dist.restrictToSupport_fullSupport (prodDist (Dist.pure a) r))]
  rw [hv, hs]

/-- Second-coordinate continuation value for the support-read branch chain. -/
theorem second_coordinate_supportRead_branchNormalizedValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (b : B) :
    branchNormalizedValue (supportReadBranchChain hfaces)
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (productFirstRevealChannel (A := A) (B := B)) =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q := by
  classical
  have hb : 0 < r b := hr b
  have hpost :
      Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b =
        prodDist q (Dist.pure b) :=
    posterior_productSecondRevealChannel_prodDist_of_pos q r b hb
  have hnotfull : ¬ (prodDist q (Dist.pure b)).FullSupport := by
    intro hfs
    haveI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hB
    rcases exists_ne b with ⟨b', hb'⟩
    have hp := hfs (Classical.arbitrary A, b')
    rw [prodDist_apply_pair,
      Dist.pure_apply_ne b b' hb', mul_zero] at hp
    exact lt_irrefl 0 hp
  have hrestrict :=
    branchNormalizedValue_supportRead_restrictToSupport
      hfaces hboundaryValue (productFirstRevealChannel (A := A) (B := B))
      (prodDist q (Dist.pure b)) hnotfull
  have hv := hvalue.second_coordinate_face_value_support
    hax q r hq hr hA hB b
  have hs := hscale.second_coordinate_face_scale_support
    hax q r hq hr hA hB b
  rw [hpost] at hv
  rw [hpost] at hs
  rw [hpost]
  rw [hrestrict]
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (prodDist q (Dist.pure b)).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productFirstRevealChannel (A := A) (B := B))
            (prodDist q (Dist.pure b)))) /
        faceSupportReadScale hfaces (prodDist q (Dist.pure b)).restrictToSupport =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q
  rw [faceSupportReadScale_fullSupport hfaces
    (prodDist q (Dist.pure b)).restrictToSupport
    (Dist.restrictToSupport_fullSupport (prodDist q (Dist.pure b)))]
  rw [hv, hs]

/-- Sequential full-revelation normalized chain rule with coordinate
continuations read on support faces.

This is the corrected replacement for the old ambient coordinate-continuation
route: no equality of ambient boundary scales such as
`scale (pure a ⊗ r) = scale r` is used. -/
theorem sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hvalueSupport : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hscaleSupport : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces) :
    FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces where
  normalized_chain_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    classical
    let hchainSR := supportReadBranchChain hfaces
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hvalue :=
      coordinateRevealValueTransport_of_marginal_and_swap
        (coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
          hfaces hprod)
        (coordinateSwapFullRevelationValueTransport_of_posteriorLaw hfaces)
    have hchain :=
      branchNormalizedValue_seqCompose_of_chain hchainSR
        (prodDist q r) hprod_full
        (productFirstRevealChannel (A := A) (B := B))
        (fun _ => productSecondRevealChannel (A := A) (B := B))
    have hseq_left :
        branchNormalizedValue hchainSR (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              fun _ => productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productFirstThenSecondReveal_eq_idChannel]
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (Channel.idChannel : Channel (A × B) (A × B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rfl
    have hfirst :
        branchNormalizedValue hchainSR (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (productFirstRevealChannel (A := A) (B := B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rw [hvalue.first_reveal_value hax q r hq hr hA hB]
    have hcontsum :
        ∑ a : A,
            Channel.outcomeMarginal
                (productFirstRevealChannel (A := A) (B := B))
                (prodDist q r) a *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productFirstRevealChannel (A := A) (B := B))
                  (prodDist q r) a)
                (productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r := by
      calc
        ∑ a : A,
            Channel.outcomeMarginal
                (productFirstRevealChannel (A := A) (B := B))
                (prodDist q r) a *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productFirstRevealChannel (A := A) (B := B))
                  (prodDist q r) a)
                (productSecondRevealChannel (A := A) (B := B))
            =
          ∑ a : A, q a *
            (fullRevelationValueForFaceScales hfaces r /
              hfaces.branch_result.scale_factorization.scale r) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [outcomeMarginal_productFirstRevealChannel_prodDist]
            rw [first_coordinate_supportRead_branchNormalizedValue
              hboundaryValue hvalueSupport hscaleSupport hax
              q r hq hr hA hB a]
        _ =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r := by
            rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hchainSR (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              fun _ => productSecondRevealChannel (A := A) (B := B)) :=
            hseq_left.symm
      _ =
        branchNormalizedValue hchainSR (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) +
          ∑ a : A,
            Channel.outcomeMarginal
                (productFirstRevealChannel (A := A) (B := B))
                (prodDist q r) a *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productFirstRevealChannel (A := A) (B := B))
                  (prodDist q r) a)
                (productSecondRevealChannel (A := A) (B := B)) := hchain
      _ =
        fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r := by
            rw [hfirst, hcontsum]
  normalized_chain_right := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    classical
    let hchainSR := supportReadBranchChain hfaces
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hvalue :=
      coordinateRevealValueTransport_of_marginal_and_swap
        (coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
          hfaces hprod)
        (coordinateSwapFullRevelationValueTransport_of_posteriorLaw hfaces)
    have hchain :=
      branchNormalizedValue_seqCompose_of_chain hchainSR
        (prodDist q r) hprod_full
        (productSecondRevealChannel (A := A) (B := B))
        (fun _ => productFirstRevealChannel (A := A) (B := B))
    have hseq_right :
        branchNormalizedValue hchainSR (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              fun _ => productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productSecondThenFirstReveal_eq_swapReveal]
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (productSwapRevealChannel (A := A) (B := B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rw [hvalue.swap_full_revelation_value hax q r hq hr hA hB]
    have hsecond :
        branchNormalizedValue hchainSR (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      unfold branchNormalizedValue
      change
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (productSecondRevealChannel (A := A) (B := B))) /
            faceSupportReadScale hfaces (prodDist q r) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r)
      rw [faceSupportReadScale_fullSupport hfaces (prodDist q r) hprod_full]
      rw [hvalue.second_reveal_value hax q r hq hr hA hB]
    have hcontsum :
        ∑ b : B,
            Channel.outcomeMarginal
                (productSecondRevealChannel (A := A) (B := B))
                (prodDist q r) b *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productSecondRevealChannel (A := A) (B := B))
                  (prodDist q r) b)
                (productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q := by
      calc
        ∑ b : B,
            Channel.outcomeMarginal
                (productSecondRevealChannel (A := A) (B := B))
                (prodDist q r) b *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productSecondRevealChannel (A := A) (B := B))
                  (prodDist q r) b)
                (productFirstRevealChannel (A := A) (B := B))
            =
          ∑ b : B, r b *
            (fullRevelationValueForFaceScales hfaces q /
              hfaces.branch_result.scale_factorization.scale q) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [outcomeMarginal_productSecondRevealChannel_prodDist]
            rw [second_coordinate_supportRead_branchNormalizedValue
              hboundaryValue hvalueSupport hscaleSupport hax
              q r hq hr hA hB b]
        _ =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q := by
            rw [← Finset.sum_mul, r.sum_eq_one, one_mul]
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hchainSR (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              fun _ => productFirstRevealChannel (A := A) (B := B)) :=
            hseq_right.symm
      _ =
        branchNormalizedValue hchainSR (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) +
          ∑ b : B,
            Channel.outcomeMarginal
                (productSecondRevealChannel (A := A) (B := B))
                (prodDist q r) b *
              branchNormalizedValue hchainSR
                (Channel.posterior
                  (productSecondRevealChannel (A := A) (B := B))
                  (prodDist q r) b)
                (productFirstRevealChannel (A := A) (B := B)) := hchain
      _ =
        fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q := by
            rw [hsecond, hcontsum]

/-- Block-embedded continuation value for the support-read branch chain. -/
theorem block_supportRead_branchNormalizedValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hax : TraceAxioms F)
    {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
    (Act : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Nonempty (Act k)]
    [Nonempty ((k : K) × Act k)]
    (hK : ¬ Subsingleton K)
    (k : K) (q : Dist (Act k)) (hq : q.FullSupport) :
    branchNormalizedValue (supportReadBranchChain hfaces)
        (blockEmbedDist Act k q)
        (Channel.idChannel : Channel ((k : K) × Act k) ((k : K) × Act k)) =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q := by
  classical
  let SigmaAct : Type u := (k : K) × Act k
  have hnotfull : ¬ (blockEmbedDist Act k q).FullSupport := by
    intro hfs
    haveI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hK
    rcases exists_ne k with ⟨j, hj⟩
    let a : Act j := Classical.choice inferInstance
    have hp := hfs (⟨j, a⟩ : SigmaAct)
    have hzero : blockEmbedDist Act k q ⟨j, a⟩ = 0 :=
      blockEmbedDist_apply_ne Act hj q a
    rw [hzero] at hp
    exact lt_irrefl 0 hp
  have hrestrict :=
    branchNormalizedValue_supportRead_restrictToSupport
      hfaces hboundaryValue
      (Channel.idChannel : Channel SigmaAct SigmaAct)
      (blockEmbedDist Act k q) hnotfull
  have hcollapse :
      branchNormalizedValue (supportReadBranchChain hfaces)
          (blockEmbedDist Act k q).restrictToSupport
          (Channel.restrictToSupport
            (Channel.idChannel : Channel SigmaAct SigmaAct)
            (blockEmbedDist Act k q)) =
        branchNormalizedValue (supportReadBranchChain hfaces)
          (blockEmbedDist Act k q).restrictToSupport
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q))) := by
    have hV :=
      (supportReadBranchChain hfaces).branch_agg.value_rep.respects_same_posterior_law
        (blockEmbedDist Act k q).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (Channel.idChannel : Channel SigmaAct SigmaAct)
            (blockEmbedDist Act k q)))
        (experimentOfChannel
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q))))
        (samePosteriorLaw_restrict_idChannel_idSupport (blockEmbedDist Act k q))
    simpa [branchNormalizedValue] using congrArg
      (fun x => x /
        (supportReadBranchChain hfaces).scale
          (blockEmbedDist Act k q).restrictToSupport) hV
  have hv := hvalue.block_face_value_support hax Act k q hq
  have hs := hscale.block_face_scale_support hax Act k q hq
  rw [hrestrict, hcollapse]
  unfold branchNormalizedValue
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (blockEmbedDist Act k q).restrictToSupport
        (experimentOfChannel
          (Channel.idChannel :
            Channel (supportSubtype (blockEmbedDist Act k q))
              (supportSubtype (blockEmbedDist Act k q)))) /
        faceSupportReadScale hfaces (blockEmbedDist Act k q).restrictToSupport =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q
  rw [faceSupportReadScale_fullSupport hfaces
    (blockEmbedDist Act k q).restrictToSupport
    (Dist.restrictToSupport_fullSupport (blockEmbedDist Act k q))]
  rw [hv, hs]

/-- Pre-universal block-reveal chain rule with embedded block posteriors read
on their support faces. -/
theorem preUniversalBlockRevealChainRule_of_branchChain_supportRead_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalBlockRevealChainRuleFor hfaces hprod where
  block_reveal_chain := by
    intro hax K _ _ _ Act _ _ _ _ p f hp hf hsigma hKnd hAnd
    classical
    let SigmaAct : Type u := (k : K) × Act k
    let C : Channel SigmaAct K :=
      preUniversalCoarseRevealChannel (K := K) Act
    let hchainSR := supportReadBranchChain hfaces
    have hCeq : C = coarseRevealChannel Act := rfl
    have hsigma_nd : ¬ Subsingleton SigmaAct :=
      not_subsingleton_sigma_of_fiber_not_subsingleton Act hAnd
    have hchain :=
      branchNormalizedValue_seqCompose_of_chain hchainSR
        (sigmaDist p f) hsigma C
        (fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))
    have hseqV :
        hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
            (experimentOfChannel
              (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))) =
          fullRevelationValueForFaceScales hfaces (sigmaDist p f) := by
      have hsame :=
        preUniversal_samePosteriorLaw_seq_id_full_revelation
          (sigmaDist p f) C
      have hV :=
        hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
          (sigmaDist p f)
          (experimentOfChannel
            (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct)))
          (experimentOfChannel
            (Channel.idChannel : Channel SigmaAct SigmaAct))
          hsame
      simpa [fullRevelationValueForFaceScales] using hV
    have hbranchScale :
        fullRevelationValueForFaceScales hfaces (sigmaDist p f) =
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) +
            hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              ∑ k, p k *
                (fullRevelationValueForFaceScales hfaces (f k) /
                  hfaces.branch_result.scale_factorization.scale (f k)) := by
      have hsigma_scale_pos :
          0 < hfaces.branch_result.scale_factorization.scale (sigmaDist p f) :=
        hfaces.branch_result.scale_factorization.scale_pos (sigmaDist p f) hsigma
      have hsigma_scale_ne :
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) ≠ 0 :=
        ne_of_gt hsigma_scale_pos
      have hseqNV :
          branchNormalizedValue hchainSR (sigmaDist p f)
              (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct)) =
            fullRevelationValueForFaceScales hfaces (sigmaDist p f) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f) := by
        unfold branchNormalizedValue
        change
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel
                (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))) /
              faceSupportReadScale hfaces (sigmaDist p f) =
            fullRevelationValueForFaceScales hfaces (sigmaDist p f) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f)
        rw [faceSupportReadScale_fullSupport hfaces (sigmaDist p f) hsigma]
        rw [hseqV]
      have hcoarseNV :
          branchNormalizedValue hchainSR (sigmaDist p f) C =
            hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f) := by
        unfold branchNormalizedValue
        change
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              faceSupportReadScale hfaces (sigmaDist p f) =
            hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f)
        rw [faceSupportReadScale_fullSupport hfaces (sigmaDist p f) hsigma]
      have hmarg :
          Channel.outcomeMarginal C (sigmaDist p f) = p := by
        simpa [C, hCeq] using outcomeMarginal_coarseReveal_sigmaDist Act p f
      have hpost :
          ∀ k,
            Channel.posterior C (sigmaDist p f) k =
              blockEmbedDist Act k (f k) := by
        intro k
        simpa [C, hCeq] using
          posterior_coarseReveal_sigmaDist_of_pos Act p f k (hp k)
      have hterms :
          ∑ k, Channel.outcomeMarginal C (sigmaDist p f) k *
              branchNormalizedValue hchainSR
                (Channel.posterior C (sigmaDist p f) k)
                (Channel.idChannel : Channel SigmaAct SigmaAct) =
          ∑ k, p k *
            (fullRevelationValueForFaceScales hfaces (f k) /
              hfaces.branch_result.scale_factorization.scale (f k)) := by
        rw [hmarg]
        apply Finset.sum_congr rfl
        intro k _
        rw [hpost k]
        rw [block_supportRead_branchNormalizedValue
          hboundaryValue hvalue hscale hax Act hKnd k (f k) (hf k)]
      rw [hseqNV, hcoarseNV, hterms] at hchain
      have hmul := congrArg
        (fun x => x *
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f))
        hchain
      field_simp [hsigma_scale_ne] at hmul
      ring_nf at hmul ⊢
      linarith
    have hscaleToZ :
        hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)) =
          productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hratio :=
        faceScale_scale_div_eq_productScaleZ_div_of_productRevelation
          hlink hax (sigmaDist p f) (f k) hsigma (hf k)
          hsigma_nd (hAnd k)
      have hsf_pos :
          0 < hfaces.branch_result.scale_factorization.scale (f k) :=
        hfaces.branch_result.scale_factorization.scale_pos (f k) (hf k)
      have hsf_ne :
          hfaces.branch_result.scale_factorization.scale (f k) ≠ 0 :=
        ne_of_gt hsf_pos
      have hZf_ne :
          productScaleZForFaceScales hfaces hprod hax (f k) ≠ 0 :=
        productScaleZ_ne_zero_of_productRevelation
          hlink hax (sigmaDist p f) (f k) hsigma (hf k)
          hsigma_nd (hAnd k)
      have hterm :
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)) =
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
        calc
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k))
              =
            (hfaces.branch_result.scale_factorization.scale (sigmaDist p f) /
                hfaces.branch_result.scale_factorization.scale (f k)) *
              fullRevelationValueForFaceScales hfaces (f k) := by
                field_simp [hsf_ne]
          _ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) /
                productScaleZForFaceScales hfaces hprod hax (f k)) *
              fullRevelationValueForFaceScales hfaces (f k) := by
                rw [hratio]
          _ =
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
                field_simp [hZf_ne]
      calc
        hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
            (p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)))
            =
          p k *
            (hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k))) := by ring
        _ =
          p k *
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k))) := by
              rw [hterm]
        _ =
          productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            (p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k))) := by ring
    rw [hbranchScale, hscaleToZ]
  reference_Z_eq_one := href.reference_Z_eq_one

/-- Grouping recursion with block posteriors read on support faces. -/
theorem finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursion_of_blockReveal
    (finitePreUniversalBlockRevealValue_of_productQuasiAdditivity hprod)
    (preUniversalBlockRevealChainRule_of_branchChain_supportRead_productScale
      hboundaryValue hvalue hscale hlink href)
    (productScaleZpositive_of_sliceTransform hprod haff)

/-- Reference-free version of the pre-universal weight recursion.  The old
package also carried `Z(q_ref)=1`; the field below is the real recursion content
needed for the two-grouping calculation. -/
structure FinitePreUniversalGroupingWeightRecursionNoReferenceFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  weight_recursion :
    ∀ (hax : TraceAxioms F)
      {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (f : ∀ k, Dist (Act k))
      (_hp : p.FullSupport)
      (_hf : ∀ k, (f k).FullSupport)
      (_hsigma : (sigmaDist p f).FullSupport)
      (_hKnd : ¬ Subsingleton K)
      (_hAnd : ∀ k, ¬ Subsingleton (Act k)),
      (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f))⁻¹ =
        (productScaleZForFaceScales hfaces hprod hax p)⁻¹ *
          ∑ k, p k *
            (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹

private theorem weightRecursion_algebra_of_groupingGR_noReference
    {K : Type u} [Fintype K]
    (p : Dist K)
    (κ Hsigma Hp : ℝ) (Hf : K → ℝ)
    (hZsigma_pos : 0 < 1 + κ * Hsigma)
    (hZp_pos : 0 < 1 + κ * Hp)
    (hZf_pos : ∀ k, 0 < 1 + κ * Hf k)
    (hGR :
      Hsigma =
        Hp + (1 + κ * Hsigma) *
          ∑ k, p k * (Hf k / (1 + κ * Hf k))) :
    (1 + κ * Hsigma)⁻¹ =
      (1 + κ * Hp)⁻¹ * ∑ k, p k * (1 + κ * Hf k)⁻¹ := by
  classical
  by_cases hκ : κ = 0
  · simp [hκ, p.sum_eq_one]
  · let Zsigma : ℝ := 1 + κ * Hsigma
    let Zp : ℝ := 1 + κ * Hp
    let Zf : K → ℝ := fun k => 1 + κ * Hf k
    let S : ℝ := ∑ k, p k * (Zf k)⁻¹
    let T : ℝ := ∑ k, p k * (Hf k / Zf k)
    have hZsigma_ne : Zsigma ≠ 0 :=
      ne_of_gt (by simpa [Zsigma] using hZsigma_pos)
    have hZp_ne : Zp ≠ 0 :=
      ne_of_gt (by simpa [Zp] using hZp_pos)
    have hZf_ne : ∀ k, Zf k ≠ 0 := fun k =>
      ne_of_gt (by simpa [Zf] using hZf_pos k)
    have hGR' : Hsigma = Hp + Zsigma * T := by
      simpa [Zsigma, Zf, T] using hGR
    have hκT : κ * T = 1 - S := by
      have hsum :
          ∑ k, κ * (p k * (Hf k / Zf k)) =
            ∑ k, p k * (1 - (Zf k)⁻¹) := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        have hz_ne : Zf k ≠ 0 := hZf_ne k
        field_simp [hz_ne, hκ, Zf]
        ring
      calc
        κ * T = ∑ k, κ * (p k * (Hf k / Zf k)) := by
          simp [T, Finset.mul_sum]
        _ = ∑ k, p k * (1 - (Zf k)⁻¹) := hsum
        _ = ∑ k, (p k - p k * (Zf k)⁻¹) := by
          refine Finset.sum_congr rfl ?_
          intro k _hk
          ring
        _ = ∑ k, p k - ∑ k, p k * (Zf k)⁻¹ := by
          rw [Finset.sum_sub_distrib]
        _ = 1 - S := by
          simp [S, p.sum_eq_one]
    have hZeq : Zsigma = Zp + Zsigma * (1 - S) := by
      calc
        Zsigma = 1 + κ * Hsigma := rfl
        _ = 1 + κ * (Hp + Zsigma * T) := by rw [hGR']
        _ = Zp + Zsigma * (κ * T) := by ring
        _ = Zp + Zsigma * (1 - S) := by rw [hκT]
    have hZp_eq : Zp = Zsigma * S := by
      nlinarith [hZeq]
    have hS_ne : S ≠ 0 := by
      intro hS
      exact hZp_ne (by rw [hZp_eq, hS, mul_zero])
    have hmain : Zsigma⁻¹ = Zp⁻¹ * S := by
      rw [hZp_eq]
      field_simp [hZsigma_ne, hS_ne]
    simpa [Zsigma, Zp, Zf, S] using hmain

/-- Support-read grouping recursion without assuming the reference `Z`
normalization. -/
theorem finitePreUniversalGroupingWeightRecursionNoReference_of_blockReveal_supportRead_productScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hvalue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hscale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionNoReferenceFor hfaces hprod where
  weight_recursion := by
    intro hax K _ _ _ Act _ _ _ _ p f hp hf hsigma hKnd hAnd
    classical
    let SigmaAct : Type u := (k : K) × Act k
    let C : Channel SigmaAct K :=
      preUniversalCoarseRevealChannel (K := K) Act
    let hchainSR := supportReadBranchChain hfaces
    have hCeq : C = coarseRevealChannel Act := rfl
    have hsigma_nd : ¬ Subsingleton SigmaAct :=
      not_subsingleton_sigma_of_fiber_not_subsingleton Act hAnd
    have hchain :=
      branchNormalizedValue_seqCompose_of_chain hchainSR
        (sigmaDist p f) hsigma C
        (fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))
    have hseqV :
        hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
            (experimentOfChannel
              (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))) =
          fullRevelationValueForFaceScales hfaces (sigmaDist p f) := by
      have hsame :=
        preUniversal_samePosteriorLaw_seq_id_full_revelation
          (sigmaDist p f) C
      have hV :=
        hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
          (sigmaDist p f)
          (experimentOfChannel
            (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct)))
          (experimentOfChannel
            (Channel.idChannel : Channel SigmaAct SigmaAct))
          hsame
      simpa [fullRevelationValueForFaceScales] using hV
    have hbranchScale :
        fullRevelationValueForFaceScales hfaces (sigmaDist p f) =
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) +
            hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              ∑ k, p k *
                (fullRevelationValueForFaceScales hfaces (f k) /
                  hfaces.branch_result.scale_factorization.scale (f k)) := by
      have hsigma_scale_pos :
          0 < hfaces.branch_result.scale_factorization.scale (sigmaDist p f) :=
        hfaces.branch_result.scale_factorization.scale_pos (sigmaDist p f) hsigma
      have hsigma_scale_ne :
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) ≠ 0 :=
        ne_of_gt hsigma_scale_pos
      have hseqNV :
          branchNormalizedValue hchainSR (sigmaDist p f)
              (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct)) =
            fullRevelationValueForFaceScales hfaces (sigmaDist p f) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f) := by
        unfold branchNormalizedValue
        change
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel
                (C ▷ fun _ => (Channel.idChannel : Channel SigmaAct SigmaAct))) /
              faceSupportReadScale hfaces (sigmaDist p f) =
            fullRevelationValueForFaceScales hfaces (sigmaDist p f) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f)
        rw [faceSupportReadScale_fullSupport hfaces (sigmaDist p f) hsigma]
        rw [hseqV]
      have hcoarseNV :
          branchNormalizedValue hchainSR (sigmaDist p f) C =
            hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f) := by
        unfold branchNormalizedValue
        change
          hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              faceSupportReadScale hfaces (sigmaDist p f) =
            hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
              (experimentOfChannel C) /
              hfaces.branch_result.scale_factorization.scale (sigmaDist p f)
        rw [faceSupportReadScale_fullSupport hfaces (sigmaDist p f) hsigma]
      have hmarg :
          Channel.outcomeMarginal C (sigmaDist p f) = p := by
        simpa [C, hCeq] using outcomeMarginal_coarseReveal_sigmaDist Act p f
      have hpost :
          ∀ k,
            Channel.posterior C (sigmaDist p f) k =
              blockEmbedDist Act k (f k) := by
        intro k
        simpa [C, hCeq] using
          posterior_coarseReveal_sigmaDist_of_pos Act p f k (hp k)
      have hterms :
          ∑ k, Channel.outcomeMarginal C (sigmaDist p f) k *
              branchNormalizedValue hchainSR
                (Channel.posterior C (sigmaDist p f) k)
                (Channel.idChannel : Channel SigmaAct SigmaAct) =
          ∑ k, p k *
            (fullRevelationValueForFaceScales hfaces (f k) /
              hfaces.branch_result.scale_factorization.scale (f k)) := by
        rw [hmarg]
        apply Finset.sum_congr rfl
        intro k _
        rw [hpost k]
        rw [block_supportRead_branchNormalizedValue
          hboundaryValue hvalue hscale hax Act hKnd k (f k) (hf k)]
      rw [hseqNV, hcoarseNV, hterms] at hchain
      have hmul := congrArg
        (fun x => x *
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f))
        hchain
      field_simp [hsigma_scale_ne] at hmul
      ring_nf at hmul ⊢
      linarith
    have hscaleToZ :
        hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)) =
          productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hratio :=
        faceScale_scale_div_eq_productScaleZ_div_of_productRevelation
          hlink hax (sigmaDist p f) (f k) hsigma (hf k)
          hsigma_nd (hAnd k)
      have hsf_pos :
          0 < hfaces.branch_result.scale_factorization.scale (f k) :=
        hfaces.branch_result.scale_factorization.scale_pos (f k) (hf k)
      have hsf_ne :
          hfaces.branch_result.scale_factorization.scale (f k) ≠ 0 :=
        ne_of_gt hsf_pos
      have hZf_ne :
          productScaleZForFaceScales hfaces hprod hax (f k) ≠ 0 :=
        productScaleZ_ne_zero_of_productRevelation
          hlink hax (sigmaDist p f) (f k) hsigma (hf k)
          hsigma_nd (hAnd k)
      have hterm :
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)) =
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
        calc
          hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k))
              =
            (hfaces.branch_result.scale_factorization.scale (sigmaDist p f) /
                hfaces.branch_result.scale_factorization.scale (f k)) *
              fullRevelationValueForFaceScales hfaces (f k) := by
                field_simp [hsf_ne]
          _ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) /
                productScaleZForFaceScales hfaces hprod hax (f k)) *
              fullRevelationValueForFaceScales hfaces (f k) := by
                rw [hratio]
          _ =
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)) := by
                field_simp [hZf_ne]
      calc
        hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
            (p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k)))
            =
          p k *
            (hfaces.branch_result.scale_factorization.scale (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                hfaces.branch_result.scale_factorization.scale (f k))) := by ring
        _ =
          p k *
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k))) := by
              rw [hterm]
        _ =
          productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            (p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k))) := by ring
    have hblock :=
      finitePreUniversalBlockRevealValue_of_productQuasiAdditivity hprod
    have hcoarse :
        hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
            (experimentOfChannel
              (preUniversalCoarseRevealChannel (K := K) Act)) =
          fullRevelationValueForFaceScales hfaces p :=
      hblock.block_reveal_value_eq_fullRevelationValue
        hax Act p f hp hf hsigma
    have hGR :
        fullRevelationValueForFaceScales hfaces (sigmaDist p f) =
          fullRevelationValueForFaceScales hfaces p +
            productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
              ∑ k, p k *
                (fullRevelationValueForFaceScales hfaces (f k) /
                  productScaleZForFaceScales hfaces hprod hax (f k)) := by
      rw [hbranchScale, hscaleToZ]
      simpa [C] using congrArg
        (fun x =>
          x + productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
            ∑ k, p k *
              (fullRevelationValueForFaceScales hfaces (f k) /
                productScaleZForFaceScales hfaces hprod hax (f k)))
        hcoarse
    have hsigma_pos :=
      productScaleZpositive_of_sliceTransform hprod haff
        |>.Z_pos hax (sigmaDist p f) hsigma
    have hp_pos :=
      productScaleZpositive_of_sliceTransform hprod haff |>.Z_pos hax p hp
    have hf_pos :
        ∀ k, 0 < productScaleZForFaceScales hfaces hprod hax (f k) :=
      fun k => productScaleZpositive_of_sliceTransform hprod haff
        |>.Z_pos hax (f k) (hf k)
    simpa [productScaleZForFaceScales] using
      weightRecursion_algebra_of_groupingGR_noReference
        p (hprod.kappa hax)
        (fullRevelationValueForFaceScales hfaces (sigmaDist p f))
        (fullRevelationValueForFaceScales hfaces p)
        (fun k => fullRevelationValueForFaceScales hfaces (f k))
        (by simpa [productScaleZForFaceScales] using hsigma_pos)
        (by simpa [productScaleZForFaceScales] using hp_pos)
        (fun k => by simpa [productScaleZForFaceScales] using hf_pos k)
        (by simpa [productScaleZForFaceScales] using hGR)

/-- Reference-free two-grouping evaluations. -/
structure FiniteProductTwoGroupingWeightEquationNoReferenceFor
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  two_grouping_evaluations :
    ∀ (hax : TraceAxioms F)
      {U V : Type u}
      [Fintype U] [DecidableEq U] [Nonempty U]
      [Fintype V] [DecidableEq V] [Nonempty V]
      (u : Dist U) (v : Dist V) (_hu : u.FullSupport) (_hv : v.FullSupport)
      (_hU : ¬ Subsingleton U) (_hV : ¬ Subsingleton V),
      ∃ wT wp : ℝ, 0 < wp ∧
        wT = wp *
            (((productScaleZForFaceScales hfaces hprod hax u)⁻¹ ^ 2 +
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹ ^ 2) / 2) ∧
        wT = wp *
            ((((productScaleZForFaceScales hfaces hprod hax u)⁻¹ +
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹) / 2) ^ 2)

/-- Two-grouping theorem from reference-free weight recursion. -/
theorem finiteProductTwoGroupingWeightEquationNoReference_of_weightRecursion_fullSupportRelabeling
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hfull : FiniteFullSupportSelectedPosteriorValueRelabelingFor hfaces)
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hrec :
      FinitePreUniversalGroupingWeightRecursionNoReferenceFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod where
  two_grouping_evaluations := by
    intro hax U V _ _ _ _ _ _ u v hu hv hU hV
    classical
    set K := universalScaleReferenceType with hK
    set p₂ := universalScaleReferencePrior with hp₂
    have hp₂fs : p₂.FullSupport := universalScaleReferencePrior_fullSupport
    have hKnd : ¬ Subsingleton K := universalScaleReference_not_subsingleton
    set g := twoGroupingConditional u v with hg
    have hgfs : ∀ k, (g k).FullSupport := by
      intro k
      rcases k with ⟨b⟩
      cases b
      · exact hu
      · exact hv
    have hgnd : ∀ k, ¬ Subsingleton (twoGroupingFiber U V k) := by
      intro k
      rcases k with ⟨b⟩
      cases b
      · exact hU
      · exact hV
    set f := fun k => prodDist (g k) (g k) with hf
    have hffs : ∀ k, (f k).FullSupport := fun k =>
      prodDist_fullSupport (g k) (g k) (hgfs k) (hgfs k)
    have hfnd : ∀ k, ¬ Subsingleton (twoGroupingFiber U V k ×
        twoGroupingFiber U V k) := fun k =>
      not_subsingleton_prod_left (hgnd k)
    set T := sigmaDist p₂ f with hT
    set S := sigmaDist p₂ g with hS
    have hTfs : T.FullSupport := sigmaDist_fullSupport p₂ f hp₂fs hffs
    have hSfs : S.FullSupport := sigmaDist_fullSupport p₂ g hp₂fs hgfs
    haveI : Nonempty ((k : K) × (twoGroupingFiber U V k ×
        twoGroupingFiber U V k)) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    haveI : Nonempty ((k : K) × twoGroupingFiber U V k) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    set f' := fun (ka : (k : K) × twoGroupingFiber U V k) => g ka.1 with hf'
    have hf'fs : ∀ ka : (k : K) × twoGroupingFiber U V k,
        (f' ka).FullSupport := fun ka => hgfs ka.1
    have hf'nd : ∀ ka : (k : K) × twoGroupingFiber U V k,
        ¬ Subsingleton (twoGroupingFiber U V ka.1) := fun ka => hgnd ka.1
    set T' := sigmaDist S f' with hT'
    have hT'fs : T'.FullSupport := sigmaDist_fullSupport S f' hSfs hf'fs
    haveI :
        Nonempty ((ka : (k : K) × twoGroupingFiber U V k) ×
          twoGroupingFiber U V ka.1) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    have hSnd : ¬ Subsingleton ((k : K) × twoGroupingFiber U V k) :=
      not_subsingleton_sigma hKnd
    have hT'nd :
        ¬ Subsingleton
          ((ka : (k : K) × twoGroupingFiber U V k) ×
            twoGroupingFiber U V ka.1) :=
      not_subsingleton_sigma_of_fiber_not_subsingleton
        (fun ka : (k : K) × twoGroupingFiber U V k =>
          twoGroupingFiber U V ka.1) hf'nd
    have hHrel :
        fullRevelationValueForFaceScales hfaces
            (Relabeling.relabelDist (twoGroupingReassoc U V) T') =
          fullRevelationValueForFaceScales hfaces T' :=
      fullRevelationValueForFaceScales_relabel_eq_fullSupport hfull hax
        (twoGroupingReassoc U V) T' hT'fs hT'nd
    have hTeq : Relabeling.relabelDist (twoGroupingReassoc U V) T' = T :=
      relabelDist_twoGroupingReassoc u v
    have hZTT' :
        productScaleZForFaceScales hfaces hprod hax T =
          productScaleZForFaceScales hfaces hprod hax T' := by
      unfold productScaleZForFaceScales
      rw [← hTeq, hHrel]
    have hrecT :=
      hrec.weight_recursion hax
        (fun k : K => twoGroupingFiber U V k × twoGroupingFiber U V k)
        p₂ f hp₂fs hffs hTfs hKnd hfnd
    have hrecT' :=
      hrec.weight_recursion hax
        (fun ka : (k : K) × twoGroupingFiber U V k =>
          twoGroupingFiber U V ka.1)
        S f' hSfs hf'fs hT'fs hSnd hf'nd
    have hrecS :=
      hrec.weight_recursion hax (twoGroupingFiber U V)
        p₂ g hp₂fs hgfs hSfs hKnd hgnd
    set x := (productScaleZForFaceScales hfaces hprod hax u)⁻¹ with hx
    set y := (productScaleZForFaceScales hfaces hprod hax v)⁻¹ with hy
    have hsum_f :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹) =
          (x ^ 2 + y ^ 2) / 2 := by
      rw [sum_universalScaleReferenceType
        (fun k => p₂ k *
          (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹)]
      have hZff :
          productScaleZForFaceScales hfaces hprod hax (f (ULift.up false)) =
            productScaleZForFaceScales hfaces hprod hax u *
              productScaleZForFaceScales hfaces hprod hax u := by
        change productScaleZForFaceScales hfaces hprod hax (prodDist u u) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax u u hu hu
      have hZft :
          productScaleZForFaceScales hfaces hprod hax (f (ULift.up true)) =
            productScaleZForFaceScales hfaces hprod hax v *
              productScaleZForFaceScales hfaces hprod hax v := by
        change productScaleZForFaceScales hfaces hprod hax (prodDist v v) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax v v hv hv
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply,
        hZff, hZft, mul_inv, mul_inv]
      change 1 / 2 *
          ((productScaleZForFaceScales hfaces hprod hax u)⁻¹ *
            (productScaleZForFaceScales hfaces hprod hax u)⁻¹) +
          1 / 2 *
            ((productScaleZForFaceScales hfaces hprod hax v)⁻¹ *
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹) = _
      rw [← hx, ← hy]
      ring
    have hsum_g :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) =
          (x + y) / 2 := by
      rw [sum_universalScaleReferenceType
        (fun k => p₂ k *
          (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹)]
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply]
      change 1 / 2 * (productScaleZForFaceScales hfaces hprod hax u)⁻¹ +
          1 / 2 * (productScaleZForFaceScales hfaces hprod hax v)⁻¹ = _
      rw [← hx, ← hy]
      ring
    have hsum_f' :
        (∑ ka : (k : K) × twoGroupingFiber U V k,
          S ka * (productScaleZForFaceScales hfaces hprod hax (f' ka))⁻¹) =
          (x + y) / 2 := by
      rw [Fintype.sum_sigma]
      have hterm :
          ∀ k, (∑ a : twoGroupingFiber U V k,
              S ⟨k, a⟩ *
                (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹) =
            p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
        intro k
        have : ∀ a : twoGroupingFiber U V k,
            S ⟨k, a⟩ *
                (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹ =
              p₂ k * (g k) a *
                (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
          intro a
          change (sigmaDist p₂ g) ⟨k, a⟩ *
              (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ = _
          rw [sigmaDist_apply]
        rw [Finset.sum_congr rfl (fun a _ => this a)]
        have hfactor :
            (∑ a : twoGroupingFiber U V k,
              p₂ k * (g k) a *
                (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) =
              (p₂ k *
                (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) *
                (∑ a, (g k) a) := by
          rw [Finset.mul_sum]
          congr 1
          ext a
          ring
        rw [hfactor, (g k).sum_eq_one, mul_one]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      exact hsum_g
    have hZp₂pos : 0 < productScaleZForFaceScales hfaces hprod hax p₂ :=
      hpos.Z_pos hax p₂ hp₂fs
    refine ⟨(productScaleZForFaceScales hfaces hprod hax T)⁻¹,
      (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹,
      inv_pos.mpr hZp₂pos, ?_, ?_⟩
    · rw [show (productScaleZForFaceScales hfaces hprod hax T)⁻¹ =
          (productScaleZForFaceScales hfaces hprod hax (sigmaDist p₂ f))⁻¹
        from rfl]
      rw [hrecT, hsum_f]
    · have hE2' :
          (productScaleZForFaceScales hfaces hprod hax T')⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹ *
              (((x + y) / 2) ^ 2) := by
        rw [show (productScaleZForFaceScales hfaces hprod hax T')⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist S f'))⁻¹
          from rfl]
        rw [hrecT', hsum_f']
        rw [show (productScaleZForFaceScales hfaces hprod hax S)⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax S)⁻¹ from rfl]
        rw [show (productScaleZForFaceScales hfaces hprod hax S)⁻¹ =
            (productScaleZForFaceScales hfaces hprod hax (sigmaDist p₂ g))⁻¹
          from rfl]
        rw [hrecS, hsum_g]
        ring
      rw [hZTT']
      exact hE2'

theorem productScaleZ_inv_eq_of_twoGroupingNoReference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod)
    (hax : TraceAxioms F)
    {U V : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (u : Dist U) (v : Dist V) (hu : u.FullSupport) (hv : v.FullSupport)
    (hU : ¬ Subsingleton U) (hV : ¬ Subsingleton V) :
    (productScaleZForFaceScales hfaces hprod hax u)⁻¹ =
      (productScaleZForFaceScales hfaces hprod hax v)⁻¹ := by
  obtain ⟨wT, wp, hwp, hE1, hE2⟩ :=
    hgroup.two_grouping_evaluations hax u v hu hv hU hV
  exact twoGrouping_eq_of_evaluations hwp (hE1.symm.trans hE2)

theorem productScaleZ_eq_of_twoGroupingNoReference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hax : TraceAxioms F)
    {U V : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (u : Dist U) (v : Dist V) (hu : u.FullSupport) (hv : v.FullSupport)
    (hU : ¬ Subsingleton U) (hV : ¬ Subsingleton V) :
    productScaleZForFaceScales hfaces hprod hax u =
      productScaleZForFaceScales hfaces hprod hax v := by
  have hinv :=
    productScaleZ_inv_eq_of_twoGroupingNoReference
      hgroup hax u v hu hv hU hV
  have := congrArg (fun t => t⁻¹) hinv
  simpa [inv_inv] using this

/-- The reference normalization is a theorem from reference-free two-grouping:
two-grouping makes `Z` constant on nondegenerate full-support priors; applying
this to `q_ref × q_ref` and using multiplicativity forces the positive constant
to satisfy `c = c^2`, hence `c = 1`. -/
theorem finiteProductReferenceZNormalization_of_twoGroupingNoReference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationNoReferenceFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductReferenceZNormalizationFor hfaces hprod where
  reference_Z_eq_one := by
    intro hax
    set q0 : Dist universalScaleReferenceType := universalScaleReferencePrior with hq0
    have hq0fs : q0.FullSupport := universalScaleReferencePrior_fullSupport
    have hq0nd : ¬ Subsingleton universalScaleReferenceType :=
      universalScaleReference_not_subsingleton
    have hpfs : (prodDist q0 q0).FullSupport :=
      prodDist_fullSupport q0 q0 hq0fs hq0fs
    have hpnd : ¬ Subsingleton (universalScaleReferenceType × universalScaleReferenceType) :=
      not_subsingleton_prod_left hq0nd
    have hconst :
        productScaleZForFaceScales hfaces hprod hax (prodDist q0 q0) =
          productScaleZForFaceScales hfaces hprod hax q0 :=
      productScaleZ_eq_of_twoGroupingNoReference
        hgroup hpos hax (prodDist q0 q0) q0 hpfs hq0fs hpnd hq0nd
    have hmul :
        productScaleZForFaceScales hfaces hprod hax (prodDist q0 q0) =
          productScaleZForFaceScales hfaces hprod hax q0 *
            productScaleZForFaceScales hfaces hprod hax q0 :=
      productScaleZForFaceScales_prod_eq hfaces hprod hax q0 q0 hq0fs hq0fs
    have hposq : 0 < productScaleZForFaceScales hfaces hprod hax q0 :=
      hpos.Z_pos hax q0 hq0fs
    have hsquare :
        productScaleZForFaceScales hfaces hprod hax q0 *
            productScaleZForFaceScales hfaces hprod hax q0 =
          productScaleZForFaceScales hfaces hprod hax q0 := by
      exact hmul.symm.trans hconst
    have hone :
        productScaleZForFaceScales hfaces hprod hax q0 = 1 := by
      nlinarith [hposq, hsquare]
    simpa [q0, hq0] using hone

/-- Interaction collapse from support-read coordinate continuations.

This constructor is the support-face replacement for the coordinate part of
`InteractionCollapseUniversalScale_of_fullPreEntropyClosure`: the product scale
link is derived from `sequentialFullRevelationNormalizedChain_of_coordinateSupportRead`,
so it never asks for ambient coordinate boundary value/scale equalities.  The
  block input is also support-read; the remaining visible pre-entropy obligations
  are the product-reference and singleton normalizations. -/
noncomputable def InteractionCollapseUniversalScale_of_coordinateSupportRead
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  let hnorm :=
    sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
      hfaces hboundaryValue hprod hcoordValue hcoordScale
  let hlink :=
    productRevelationScaleLink_of_sequentialScale hfaces hprod
      (productRevelationSequentialScale_of_normalizedChain hfaces hnorm)
  let hpos := productScaleZpositive_of_sliceTransform hprod haff
  let hfull :=
    finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
      hhm huniq hpos
  let hrec :=
    finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale
      hboundaryValue haff hblockValue hblockScale hlink href
  let htwo :=
    finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  let hreference :=
    productGroupingReferenceWeight_of_twoGroupingWeightEquation htwo hpos
  let hweight :=
    productGroupingWeightConstant_of_reference hreference
  let hcollapse :=
    twoGroupingInteractionCollapse_of_weightConstant hfaces hprod hweight
  { face_scales := hfaces
    product_quasi_add := hprod
    scale_coherence :=
      scaleCoherence_of_faceScales_interactionCollapse
        hfaces hprod hlink hcollapse hsingle hax
    interaction_collapse := hcollapse.kappa_eq_zero }




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
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
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
  have hstandard :
      FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun :=
    finiteFaddeevStandardHypotheses_of_axioms hax hcross hrecForm hsupport
  have hex :=
    hfad.of_standard_hypotheses
      hcross.entropy_reduction.Hfun hstandard
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
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
    (hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hcross.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hcross.entropy_reduction.Hfun p) :
    MIRep F :=
  let hfe : FaddeevEntropyForm F :=
    FaddeevEntropyForm_forCross hblock hred hfad F hax hcross hreg hsupport hcoarse
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
  have hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hc.entropy_reduction.Hfun q =
        hc.entropy_reduction.Hfun q.restrictToSupport := by
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
      exact hhfunC
  apply MIRep_forCross hblock hred hfad F hax hc hreg hhfunC
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
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
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
  have hstandard :
      FiniteFaddeevStandardHypotheses hcross.entropy_reduction.Hfun :=
    finiteFaddeevStandardHypotheses_of_axioms hax hcross hrecForm hsupport
  have hex :=
    hfad.of_standard_hypotheses
      hcross.entropy_reduction.Hfun hstandard
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
    (hsupport : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hcross.entropy_reduction.Hfun q =
        hcross.entropy_reduction.Hfun q.restrictToSupport)
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
    FaddeevEntropyForm_ofCrossFacts
      hfad F hax hcross hreg hsupport hER hblockE hcoarse
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
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hpre : PreEntropyRepresentativeGaugeNormalizations hfaces hprod)
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
  exact MIRep_ofCrossFacts
    hfad F hax hc hreg hhfunC hER hblockE hcoarse P qq qq'

/-- Entropy reduction produced by the coordinate-support-read route. -/
noncomputable def entropyReduction_of_coordinateSupportRead
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_interactionCollapse
    (InteractionCollapseUniversalScale_of_coordinateSupportRead
      hfaces hboundaryValue hhm huniq hprod haff hcoordValue hcoordScale
      hblockValue hblockScale href hsingle hax)

/-- Cross-prior block representation produced by the coordinate-support-read
route. -/
noncomputable def crossPriorBlockRepresentation_of_coordinateSupportRead
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_preUniversalBridge
    (finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod)
    hax
    (entropyReduction_of_coordinateSupportRead
      hfaces hboundaryValue hhm huniq hprod haff hcoordValue hcoordScale
      hblockValue hblockScale href hsingle hax)
    rfl

/-- MI representation from the corrected coordinate support-read route.

Compared with `MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal`,
the coordinate hypotheses are the support-read facts and no ambient coordinate
transport/identification is assumed.  The remaining reference/singleton inputs
are deliberately left visible for the next grafting steps. -/
theorem MIRep_of_TraceAxioms_HM_Faddeev_withCoordinateSupportRead_noCardinal
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (haff : FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hcoordValue : FiniteCoordinateSupportFaceValueSupportReadFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleSupportReadFor hfaces)
    (hblockValue : FiniteBlockSupportFaceValueSupportReadFor hfaces)
    (hblockScale : FiniteBlockSupportFaceScaleSupportReadFor hfaces)
    (href : FiniteProductReferenceZNormalizationFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) :
    MIRep F := by
  set hcross := crossPriorBlockRepresentation_of_coordinateSupportRead
    hfaces hboundaryValue hhm huniq hprod haff hcoordValue hcoordScale
    hblockValue hblockScale href hsingle hax with hcrossdef
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
  have hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (q : Dist A),
      hc.entropy_reduction.Hfun q =
        normalizedValue hc.entropy_reduction.scale_coherence q Channel.idChannel :=
    fun q => rfl
  have hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A), ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hc.entropy_reduction.scale_coherence q P =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    intro A O _ _ _ _ _ P q hqb
    apply field1_boundaryComplete_of_selectedValue
      hcross.entropy_reduction.scale_coherence hsf
    · intro A' O' _ _ _ _ _ r _ R
      change
        hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) =
          hfaces.branch_result.branch_agg.value_rep.V r.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport R r))
      exact hboundaryValue.boundary_value_support r R
    · exact hqb
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
    unfold normalizedValue
    change
      hfaces.branch_result.branch_agg.value_rep.V
          (Relabeling.relabelDist e qA)
          (experimentOfChannel (Channel.idChannel : Channel B B)) /
        hfaces.branch_result.scale_factorization.scale
          (Relabeling.relabelDist e qA) =
      hfaces.branch_result.branch_agg.value_rep.V qA
          (experimentOfChannel (Channel.idChannel : Channel A A)) /
        hfaces.branch_result.scale_factorization.scale qA
    have hV := hsel.V_relabel_eq hax e e qA
      (Channel.idChannel : Channel A A)
    rw [relabelChannel_id_eq e] at hV
    have hs :=
      CoherentRelabelingFaceScalesStructure.scale_relabel_eq
        hfaces e qA hqA
    rw [hV, hs]
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
    fun {K} _ _ _ Act _ _ _ _ p q =>
      coarseReveal_entropyReduction_ofFacts F hax hc hnormC hhfunC hIntC Act p q
  have hblockE : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hc.entropy_reduction.Hfun (blockEmbedDist Act k qk) = hc.entropy_reduction.Hfun qk :=
    fun {K} _ _ _ Act _ _ _ _ k qk =>
      Hfun_blockEmbed_ofFacts F hc hhfunC hrelabC Act k qk
  have hcoarse : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u) [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) = hc.entropy_reduction.Hfun p :=
    fun {K} _ _ _ Act _ _ _ _ p q =>
      coarseVal_forCross F hax hc hreg hnormC
        (field3_restricted_coarse_reveal F hax hc hreg) hhfunC Act p q
  intro A O instA instDA instO instDO P qq qq'
  exact MIRep_ofCrossFacts
    hfad F hax hc hreg hhfunC hER hblockE hcoarse P qq qq'

/-- Scale-only cardinal alignment of the selected branch structure.

The cardinal factor changes the cross-alphabet choice of chain scale without
rescaling the selected posterior value.  Multiplying both would leave
normalized values unchanged, fail to remove the embedding defect, and destroy
the canonical boundary-to-support equality. -/
noncomputable def cardinalScaleBranchResultFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    BranchAggregationCocycleNormalizedChainRuleStructure F := by
  let hraw :=
    BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax branch
  let t : ℕ → ℝ := cardScaleTFor hhm hax branch
  exact
    { branch_agg := hraw.branch_agg
      coeff_cocycle := hraw.coeff_cocycle
      full_support_scale :=
        { scale := fun {A} _ _ _ q =>
            t (Fintype.card A) * hraw.full_support_scale.scale q
          scale_pos := by
            intro A _ _ _ q hq hnd
            exact mul_pos
              (cardScaleT_posFor hhm hax branch (Fintype.card A))
              (hraw.full_support_scale.scale_pos q hq hnd)
          branchCoeff_factorization_fullSupport := by
            intro A _ _ _ q r hq hr hnd
            rw [hraw.full_support_scale.branchCoeff_factorization_fullSupport
              q r hq hr hnd]
            have ht : t (Fintype.card A) ≠ 0 :=
              ne_of_gt
                (cardScaleT_posFor hhm hax branch (Fintype.card A))
            field_simp [ht] }
      scale_factorization :=
        { scale := fun {A} _ _ _ q =>
            t (Fintype.card A) * hraw.scale_factorization.scale q
          scale_pos := by
            intro A _ _ _ q hq
            exact mul_pos
              (cardScaleT_posFor hhm hax branch (Fintype.card A))
              (hraw.scale_factorization.scale_pos q hq)
          branchCoeff_factorization := by
            intro A O _ _ _ _ _ q hq P o hpos
            rw [hraw.scale_factorization.branchCoeff_factorization
              q hq P o hpos]
            have ht : t (Fintype.card A) ≠ 0 :=
              ne_of_gt
                (cardScaleT_posFor hhm hax branch (Fintype.card A))
            field_simp [ht] } }

/-- Coherent face scales after scale-only cardinal alignment. -/
noncomputable def cardinalGaugeFaceScalesFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    CoherentRelabelingFaceScalesStructure F := by
  let hraw :=
    BranchAggregationCocycleNormalizedChainRule_of_FinalHM_atomicDataFor
      hhm hax branch
  let hscaled := cardinalScaleBranchResultFor hhm hax branch
  exact
    { branch_result := hscaled
      scale_relabeling :=
        { scale_relabel_eq := by
            intro A B _ _ _ _ _ _ e q hq
            change
              cardScaleTFor hhm hax branch (Fintype.card B) *
                  hraw.scale_factorization.scale
                    (Relabeling.relabelDist e q) =
                cardScaleTFor hhm hax branch (Fintype.card A) *
                  hraw.scale_factorization.scale q
            rw [Fintype.card_congr e.symm]
            rw [scaleRelabel_of_FinalHM_covarianceAtomicFor
              hhm hax branch e q hq] }
      support_face_scale :=
        { support_face_scale := by
            intro A _ _ _ q hq r _ hrn hrnd hrb
            have hs :=
              cardinalGauge_hsupportFor hhm hax branch
                q hq r hrn hrnd hrb
            have ht :
                cardScaleTFor hhm hax branch (Fintype.card A) ≠ 0 :=
              ne_of_gt
                (cardScaleT_posFor hhm hax branch (Fintype.card A))
            simpa [hraw, hscaled, cardinalScaleBranchResultFor,
              cardinalGaugeFor, ht] using hs } }

/-- Singleton left-slice affine normalisation for the selected raw cardinal-gauge
face scales is internal. -/
theorem cardinalGaugeSingletonSliceFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleSingletonSliceAffineAssumptionsFor
      (cardinalGaugeFaceScalesFor hhm hax branch) :=
  finiteFaceScaleSingletonSliceAffine_of_faces
    (cardinalGaugeFaceScalesFor hhm hax branch)

/-- Selected relabelling for the scale-only cardinal alignment. -/
theorem cardinalGaugeSelectedRelabelingFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteSelectedPosteriorValueRelabelingFor
      (cardinalGaugeFaceScalesFor hhm hax branch) where
  V_relabel_eq := by
    intro _hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    change
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          (Relabeling.relabelDist eA q)
          (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P)
    exact
      (finalSelectedRelabelCovariance_of_canonicalNormalization hhm).V_relabel_eq
        hax eA eO q P

/-- Canonical boundary-value transport survives the scale-only cardinal
alignment because its value representative is unchanged. -/
theorem cardinalGaugeBoundaryValueSupportReadFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteBoundaryValueSupportReadFor
      (cardinalGaugeFaceScalesFor hhm hax branch) where
  boundary_value_support := by
    intro A O _ _ _ _ _ q _ P
    change
      (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V q
          (experimentOfChannel P) =
        (posteriorValueRepresentation_of_FinalHMInterface hhm hax).V
          q.restrictToSupport
          (experimentOfChannel (Channel.restrictToSupport P q))
    exact finalHM_supportFaceValueTransport hhm hax q P

/-- Product-intercept positive linearity for the selected raw cardinal-gauge face
scales. -/
theorem cardinalGaugeProductInterceptFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch))) :=
  faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
    (faceScaleProductInterceptSameOrder_of_A7
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch))))
    (faceScaleProductInterceptPublicMixAffinity_of_HM
      (integralRepresentationData_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch))))
    (classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
      (integralRepresentationData_of_FinalHMInterface hhm)
      (faceScaleProductLeftSliceAffine_of_transform
        (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
          (integralRepresentationData_of_FinalHMInterface
            hhm)
          (cardinalGaugeSingletonSliceFor hhm hax branch)))
      classicalFiniteAffineUtilityUniquenessAssumptions)

/-- Pairwise product bilinearity for the selected raw cardinal-gauge face scales. -/
noncomputable def cardinalGaugeProductPairFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
      (cardinalGaugeFaceScalesFor hhm hax branch) :=
  faceScaleProductPairwiseBilinearity_of_multiPieces
    (finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      (integralRepresentationData_of_FinalHMInterface
        hhm)
      (cardinalGaugeSingletonSliceFor hhm hax branch))
    (cardinalGaugeProductInterceptFor hhm hax branch)
    (faceScaleProductSlopeAffine_of_selectedRelabeling
      (cardinalGaugeSelectedRelabelingFor hhm hax branch)
      (cardinalGaugeProductInterceptFor hhm hax branch))

/-- Triple-product value associativity for the selected raw cardinal-gauge face
scales, derived from selected relabelling. -/
theorem cardinalGaugeTripleProductValueAssociativityFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
      (cardinalGaugeFaceScalesFor hhm hax branch) :=
  faceScaleTripleProductValueAssociativity_of_selectedRelabeling
    (cardinalGaugeFaceScalesFor hhm hax branch)
    (cardinalGaugeSelectedRelabelingFor hhm hax branch)

/-- The selected coboundary product transform for the cardinal-gauge face
scales.  This replaces the former product-gauge normalization by the explicit
coboundary constructed from product coefficient associativity. -/
noncomputable def cardinalGaugeProductCoboundaryTransformFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteFaceScaleProductGaugeTransformNondegenerateFor
      (cardinalGaugeProductPairFor hhm hax branch) :=
  cobGaugeSFProductTransform_selected
    (cardinalGaugeProductPairFor hhm hax branch)
    (cardinalGaugeSelectedRelabelingFor hhm hax branch)
    (cardinalGaugeTripleProductValueAssociativityFor hhm hax branch)
    hax

/-- Product quasi-additivity for the selected cardinal-gauge face scales after
the internally constructed coboundary product transform. -/
noncomputable def cardinalGaugeProductQuasiAdditivityFor
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (branch : FinalFaithfulBranchAtomicDataFor hhm hax) :
    FiniteProductQuasiAdditivityForFaceScales
      ((cardinalGaugeFaceScalesFor hhm hax branch).gaugeTransform
        (cardinalGaugeProductCoboundaryTransformFor
          hhm hax branch).gauge) :=
  productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData_nondegenerate
    (cardinalGaugeProductPairFor hhm hax branch)
    (cardinalGaugeProductCoboundaryTransformFor hhm hax branch)
    (cardinalGaugeTripleProductValueAssociativityFor hhm hax branch)

/-- The final constructed face-scale representative used by the paper-facing
cardinal-gauge route.  The branch data is constructed internally from the HM
interface and `TraceAxioms`, so this definition has no branch hypothesis. -/
noncomputable def finalConstructedCardinalGaugeFaceScales
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    CoherentRelabelingFaceScalesStructure F :=
  let branchData :=
    finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax
  (cardinalGaugeFaceScalesFor hhm hax branchData).gaugeTransform
    (cardinalGaugeProductCoboundaryTransformFor
      hhm hax branchData).gauge

/-- Product quasi-additivity for the final constructed face-scale
representative. -/
noncomputable def finalConstructedCardinalGaugeProductQuasiAdditivity
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteProductQuasiAdditivityForFaceScales
      (finalConstructedCardinalGaugeFaceScales hhm hax) := by
  dsimp [finalConstructedCardinalGaugeFaceScales]
  exact cardinalGaugeProductQuasiAdditivityFor hhm hax
    (finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax)

/-- Selected value relabeling for the final constructed cardinal/product-gauge
representative. -/
theorem finalConstructedCardinalGaugeSelectedRelabeling
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteSelectedPosteriorValueRelabelingFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) := by
  dsimp [finalConstructedCardinalGaugeFaceScales]
  exact
    finiteSelectedPosteriorValueRelabeling_gaugeTransform
      (cardinalGaugeSelectedRelabelingFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax))
      (cardinalGaugeProductCoboundaryTransformFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax)).gauge

/-- Boundary-value transport for the final scale-aligned/product-gauged
representative.  The cardinal alignment is scale-only, and the subsequent
coboundary gauge is support-coherent. -/
theorem finalConstructedBoundaryValueSupportRead_of_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteBoundaryValueSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) := by
  dsimp [finalConstructedCardinalGaugeFaceScales]
  exact
    finiteBoundaryValueSupportRead_gaugeTransform
      (cardinalGaugeBoundaryValueSupportReadFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax))
      (cardinalGaugeProductCoboundaryTransformFor hhm hax
        (finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax)).gauge

/-- Coordinate support-read value transport for the final constructed
representative.  This is the support-face theorem replacing the false ambient
coordinate-value convention. -/
theorem finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteCoordinateSupportFaceValueSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  coordinateSupportFaceValueSupportRead_of_selectedRelabeling
    (finalConstructedCardinalGaugeSelectedRelabeling hhm hax)

/-- Coordinate support-read scale transport for the final constructed
representative.  This is the support-face scale theorem replacing the false
ambient coordinate-scale convention. -/
theorem finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteCoordinateSupportFaceScaleSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  coordinateSupportFaceScaleSupportRead_of_relabeling
    (finalConstructedCardinalGaugeFaceScales hhm hax)

/-- Block support-read value transport for the final constructed
representative. -/
theorem finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteBlockSupportFaceValueSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  blockSupportFaceValueSupportRead_of_selectedRelabeling
    (finalConstructedCardinalGaugeSelectedRelabeling hhm hax)

/-- Block support-read scale transport for the final constructed
representative. -/
theorem finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteBlockSupportFaceScaleSupportReadFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  blockSupportFaceScaleSupportRead_of_relabeling
    (finalConstructedCardinalGaugeFaceScales hhm hax)

/-- The final constructed representative assigns scale `1` to full-support
subsingleton alphabets.  This is definitional from the support-face coboundary
gauge, the cardinal gauge value `t_1 = 1`, and the selected atomic singleton
scale. -/
theorem finalConstructedScale_eq_one_of_subsingleton
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : Subsingleton A) :
    (finalConstructedCardinalGaugeFaceScales hhm hax).branch_result.scale_factorization.scale q =
      1 := by
  classical
  letI : Subsingleton A := hA
  let branch := finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax
  change
    cobGaugeSF (cardinalGaugeProductPairFor hhm hax branch) hax q *
      ((cardinalGaugeFor hhm hax branch).gauge q *
        selectedAtomicBranchScaleFor hhm hax branch q) = 1
  have hsupport : Subsingleton (supportSubtype q) := by
    refine ⟨?_⟩
    intro x y
    exact Subtype.ext (Subsingleton.elim x.1 y.1)
  have hcob :
      cobGaugeSF (cardinalGaugeProductPairFor hhm hax branch) hax q = 1 := by
    unfold cobGaugeSF
    rw [if_pos hsupport]
  have hcard : Fintype.card A = 1 := by
    exact Fintype.card_eq_one_iff.mpr
      ⟨Classical.arbitrary A, fun y => Subsingleton.elim y (Classical.arbitrary A)⟩
  have hcgauge : (cardinalGaugeFor hhm hax branch).gauge q = 1 := by
    dsimp [cardinalGaugeFor, cardScaleTFor]
    rw [hcard]
    norm_num
  have hnotnd :
      ¬ ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
    rintro ⟨a, b, hne, _ha, _hb⟩
    exact hne (Subsingleton.elim a b)
  have hsel :
      selectedAtomicBranchScaleFor hhm hax branch q = 1 := by
    rw [selectedAtomicBranchScaleFor_fullSupport hhm hax branch q hq]
    simp only [branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
      hq, Dist.uniform_fullSupport, dif_pos]
    rw [dif_neg hnotnd]
  rw [hcob, hcgauge, hsel]
  ring

/-- The binary reference prior has final constructed scale `1`.  The only
coefficient calculation is product-swap symmetry at the binary reference, which
identifies the right and left product coefficients in the coboundary gauge. -/
theorem finalConstructedReferenceScale_eq_one
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    (finalConstructedCardinalGaugeFaceScales hhm hax).branch_result.scale_factorization.scale
      universalScaleReferencePrior = 1 := by
  classical
  let branch := finalFaithfulBranchAtomicDataFor_of_FinalHM_TraceAxioms hhm hax
  let hpair := cardinalGaugeProductPairFor hhm hax branch
  let hsel := cardinalGaugeSelectedRelabelingFor hhm hax branch
  change
    cobGaugeSF hpair hax universalScaleReferencePrior *
      ((cardinalGaugeFor hhm hax branch).gauge universalScaleReferencePrior *
        selectedAtomicBranchScaleFor hhm hax branch universalScaleReferencePrior) = 1
  have href_nd : ¬ Subsingleton universalScaleReferenceType :=
    universalScaleReference_not_subsingleton
  have hcob : cobGaugeSF hpair hax universalScaleReferencePrior = 1 := by
    rw [cobGaugeSF_eq_cobGauge_of_fullSupport_selected
      hpair hsel hax universalScaleReferencePrior
      universalScaleReferencePrior_fullSupport href_nd]
    unfold cobGauge
    change
      hpair.rightCoeff hax universalScaleReferencePrior universalScaleReferencePrior /
          hpair.leftCoeff hax universalScaleReferencePrior universalScaleReferencePrior =
        1
    have hswap :=
      fs_rightCoeff_eq_swapped_leftCoeff_selected
        hpair hsel hax universalScaleReferencePrior universalScaleReferencePrior
        universalScaleReferencePrior_fullSupport universalScaleReferencePrior_fullSupport
        href_nd
    have hleft_pos :
        0 < hpair.leftCoeff hax universalScaleReferencePrior universalScaleReferencePrior :=
      hpair.leftCoeff_pos hax universalScaleReferencePrior universalScaleReferencePrior
        universalScaleReferencePrior_fullSupport universalScaleReferencePrior_fullSupport
    rw [hswap]
    exact div_self (ne_of_gt hleft_pos)
  have hcard : Fintype.card universalScaleReferenceType.{u} = 2 := by
    simp [universalScaleReferenceType]
  have hcgauge :
      (cardinalGaugeFor hhm hax branch).gauge universalScaleReferencePrior = 1 := by
    simp [cardinalGaugeFor, cardScaleTFor, hcard]
  have hnd :
      ∃ a b : universalScaleReferenceType, a ≠ b :=
    ⟨ULift.up true, ULift.up false, by
      intro h
      cases congrArg ULift.down h⟩
  have hsel_scale :
      selectedAtomicBranchScaleFor hhm hax branch universalScaleReferencePrior = 1 := by
    have hraw :=
      scale_uniform_eq_oneAtomicFor hhm hax branch
        (A := universalScaleReferenceType) hnd
    change selectedAtomicBranchScaleFor hhm hax branch
        (Dist.uniform (A := universalScaleReferenceType)) = 1 at hraw
    simpa [universalScaleReferencePrior] using hraw
  rw [hcob, hcgauge, hsel_scale]
  ring

/-- The product-reference `Z` normalization for the final constructed
cardinal-gauge representative is internal.  The proof uses the reference-free
two-grouping calculation: `Z` is constant on nondegenerate full-support priors,
and multiplicativity at `q_ref × q_ref` plus positivity forces the constant to
be `1`. -/
theorem finalConstructedProductReferenceZNormalization_of_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteProductReferenceZNormalizationFor
      (finalConstructedCardinalGaugeFaceScales hhm hax)
      (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax) := by
  let hfacesKnown : CoherentRelabelingFaceScalesStructure F :=
    finalConstructedCardinalGaugeFaceScales hhm hax
  let hprodKnown :
      FiniteProductQuasiAdditivityForFaceScales hfacesKnown :=
    finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax
  let hhmClassical :
      FinitePosteriorIntegralRepresentationData.{u} :=
    integralRepresentationData_of_FinalHMInterface hhm
  let huniqKnown : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} :=
    classicalFiniteAffineUtilityUniquenessAssumptions
  let haffKnown :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor
        hfacesKnown :=
    finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      hhmClassical
      (finiteFaceScaleSingletonSliceAffine_of_faces hfacesKnown)
  let hboundaryValueKnown :
      FiniteBoundaryValueSupportReadFor hfacesKnown :=
    finalConstructedBoundaryValueSupportRead_of_FinalHM_TraceAxioms hhm hax
  let hcoordValueKnown :
      FiniteCoordinateSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hcoordScaleKnown :
      FiniteCoordinateSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hblockValueKnown :
      FiniteBlockSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hblockScaleKnown :
      FiniteBlockSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hnorm :=
    sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
      hfacesKnown hboundaryValueKnown hprodKnown
      hcoordValueKnown hcoordScaleKnown
  let hlink :=
    productRevelationScaleLink_of_sequentialScale hfacesKnown hprodKnown
      (productRevelationSequentialScale_of_normalizedChain hfacesKnown hnorm)
  let hpos := productScaleZpositive_of_sliceTransform hprodKnown haffKnown
  let hfull :=
    finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
      hhmClassical huniqKnown hpos
  let hrec :=
    finitePreUniversalGroupingWeightRecursionNoReference_of_blockReveal_supportRead_productScale
      hboundaryValueKnown haffKnown hblockValueKnown hblockScaleKnown hlink
  let htwo :=
    finiteProductTwoGroupingWeightEquationNoReference_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  exact finiteProductReferenceZNormalization_of_twoGroupingNoReference htwo hpos

/-- Given the remaining product-reference `Z` normalization, every nondegenerate
full-support prior has final constructed scale `1`.  This packages the already
proved product-revelation link, grouping-weight collapse, and the reference-scale
calculation above. -/
theorem finalConstructedNondegenerateScale_eq_one_of_referenceZ
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    (finalConstructedCardinalGaugeFaceScales hhm hax).branch_result.scale_factorization.scale q =
      1 := by
  classical
  let hfacesKnown : CoherentRelabelingFaceScalesStructure F :=
    finalConstructedCardinalGaugeFaceScales hhm hax
  let hprodKnown :
      FiniteProductQuasiAdditivityForFaceScales hfacesKnown :=
    finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax
  let hhmClassical :
      FinitePosteriorIntegralRepresentationData.{u} :=
    integralRepresentationData_of_FinalHMInterface hhm
  let huniqKnown : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} :=
    classicalFiniteAffineUtilityUniquenessAssumptions
  let haffKnown :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor
        hfacesKnown :=
    finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      hhmClassical
      (finiteFaceScaleSingletonSliceAffine_of_faces hfacesKnown)
  let hboundaryValueKnown :
      FiniteBoundaryValueSupportReadFor hfacesKnown :=
    finalConstructedBoundaryValueSupportRead_of_FinalHM_TraceAxioms hhm hax
  let hcoordValueKnown :
      FiniteCoordinateSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hcoordScaleKnown :
      FiniteCoordinateSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hblockValueKnown :
      FiniteBlockSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hblockScaleKnown :
      FiniteBlockSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hnorm :=
    sequentialFullRevelationNormalizedChain_of_coordinateSupportRead
      hfacesKnown hboundaryValueKnown hprodKnown
      hcoordValueKnown hcoordScaleKnown
  let hlink :=
    productRevelationScaleLink_of_sequentialScale hfacesKnown hprodKnown
      (productRevelationSequentialScale_of_normalizedChain hfacesKnown hnorm)
  let hpos := productScaleZpositive_of_sliceTransform hprodKnown haffKnown
  let hfull :=
    finiteFullSupportSelectedPosteriorValueRelabeling_of_HM_productNormalization
      hhmClassical huniqKnown hpos
  let hrec :=
    finitePreUniversalGroupingWeightRecursion_of_blockReveal_supportRead_productScale
      hboundaryValueKnown haffKnown hblockValueKnown hblockScaleKnown
      hlink reference_z
  let htwo :=
    finiteProductTwoGroupingWeightEquation_of_weightRecursion_fullSupportRelabeling
      hfull hrec hpos
  let hreference :=
    productGroupingReferenceWeight_of_twoGroupingWeightEquation htwo hpos
  let hweight :=
    productGroupingWeightConstant_of_reference hreference
  let hcollapse :=
    twoGroupingInteractionCollapse_of_weightConstant
      hfacesKnown hprodKnown hweight
  have hscale_eq :=
    scale_eq_of_productRevelation_and_interactionCollapse
      hfacesKnown hprodKnown hlink hcollapse hax q
      universalScaleReferencePrior hq universalScaleReferencePrior_fullSupport
      hA universalScaleReference_not_subsingleton
  exact hscale_eq.trans (finalConstructedReferenceScale_eq_one hhm hax)

/-- The remaining singleton universal-scale normalization follows from the final
constructed singleton/reference scale computations plus the product-reference `Z`
normalization.  Thus it is no longer an independent pre-entropy input once
`reference_z` is available. -/
theorem finalConstructedUniversalScaleSingleton_of_referenceZ_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax)) :
    FiniteUniversalScaleSingletonNormalizationFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) where
  scale_eq_of_subsingleton := by
    intro A B _ _ _ _ _ _ q r hq hr hsub
    rcases hsub with hA | hB
    · have hq1 :=
        finalConstructedScale_eq_one_of_subsingleton hhm hax q hq hA
      by_cases hB' : Subsingleton B
      · have hr1 :=
          finalConstructedScale_eq_one_of_subsingleton hhm hax r hr hB'
        rw [hq1, hr1]
      · have hr1 :=
          finalConstructedNondegenerateScale_eq_one_of_referenceZ
            hhm hax reference_z r hr hB'
        rw [hq1, hr1]
    · have hr1 :=
        finalConstructedScale_eq_one_of_subsingleton hhm hax r hr hB
      by_cases hA' : Subsingleton A
      · have hq1 :=
          finalConstructedScale_eq_one_of_subsingleton hhm hax q hq hA'
        rw [hq1, hr1]
      · have hq1 :=
          finalConstructedNondegenerateScale_eq_one_of_referenceZ
            hhm hax reference_z q hq hA'
        rw [hq1, hr1]

/-- Universal singleton scale normalization for the final constructed
representative, with the product-reference normalization now supplied
internally. -/
theorem finalConstructedUniversalScaleSingleton_of_FinalHM_TraceAxioms
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    FiniteUniversalScaleSingletonNormalizationFor
      (finalConstructedCardinalGaugeFaceScales hhm hax) :=
  finalConstructedUniversalScaleSingleton_of_referenceZ_FinalHM_TraceAxioms
    hhm hax
    (finalConstructedProductReferenceZNormalization_of_FinalHM_TraceAxioms
      hhm hax)

/-- MI route using the corrected coordinate support-read facts internally.

The coordinate value and scale facts are constructed from `FinalHMInterface`
  and `TraceAxioms`; only the still-unrepaired reference/singleton pre-entropy
  obligations remain explicit. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withCoordinateSupportReadPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax))
    (universal_singleton :
      FiniteUniversalScaleSingletonNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)) :
    MIRep F := by
  let hfacesKnown : CoherentRelabelingFaceScalesStructure F :=
    finalConstructedCardinalGaugeFaceScales hhm hax
  let hprodKnown :
      FiniteProductQuasiAdditivityForFaceScales hfacesKnown :=
    finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax
  let hhmClassical : FinitePosteriorIntegralRepresentationData.{u} :=
    integralRepresentationData_of_FinalHMInterface hhm
  let huniqKnown : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} :=
    classicalFiniteAffineUtilityUniquenessAssumptions
  let haffKnown :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor
        hfacesKnown :=
    finiteFaceScaleProductLeftSliceAffineTransform_of_HM
      hhmClassical
      (finiteFaceScaleSingletonSliceAffine_of_faces hfacesKnown)
  let hboundaryValueKnown :
      FiniteBoundaryValueSupportReadFor hfacesKnown :=
    finalConstructedBoundaryValueSupportRead_of_FinalHM_TraceAxioms hhm hax
  let hcoordValueKnown :
      FiniteCoordinateSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hcoordScaleKnown :
      FiniteCoordinateSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedCoordinateSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hblockValueKnown :
      FiniteBlockSupportFaceValueSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceValueSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hblockScaleKnown :
      FiniteBlockSupportFaceScaleSupportReadFor hfacesKnown :=
    finalConstructedBlockSupportFaceScaleSupportRead_of_FinalHM_TraceAxioms
      hhm hax
  let hselKnown :
      FiniteSelectedPosteriorValueRelabelingFor hfacesKnown :=
    finalConstructedCardinalGaugeSelectedRelabeling hhm hax
  exact
    @MIRep_of_TraceAxioms_HM_Faddeev_withCoordinateSupportRead_noCardinal
      hfad F hfacesKnown hboundaryValueKnown hhmClassical huniqKnown
      hprodKnown haffKnown hcoordValueKnown hcoordScaleKnown
      hblockValueKnown hblockScaleKnown reference_z universal_singleton
      hselKnown hax

/-- MI route after eliminating the universal-singleton pre-entropy input.

The only remaining pre-entropy normalization at this boundary is the
product-reference `Z` normalization; the universal singleton scale condition is
constructed from it and the final HM/trace-axiom representative. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_onlyReferenceZPreEntropy
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (reference_z :
      FiniteProductReferenceZNormalizationFor
        (finalConstructedCardinalGaugeFaceScales hhm hax)
        (finalConstructedCardinalGaugeProductQuasiAdditivity hhm hax)) :
    MIRep F := by
  exact
    MIRep_of_TraceAxioms_FinalHM_Faddeev_withCoordinateSupportReadPreEntropy
      hfad hhm hax reference_z
      (finalConstructedUniversalScaleSingleton_of_referenceZ_FinalHM_TraceAxioms
        hhm hax reference_z)

/-- Convention-free MI route.

All support restriction, relabelling covariance, cardinal scale alignment,
and pre-entropy normalizations for the selected canonical posterior value are
derived internally. -/
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F) :
    MIRep F := by
  exact
    MIRep_of_TraceAxioms_FinalHM_Faddeev_onlyReferenceZPreEntropy
      hfad hhm hax
      (finalConstructedProductReferenceZNormalization_of_FinalHM_TraceAxioms
        hhm hax)

end TraceableAgency
