/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.PreEntropyConstruction
import TraceableAgency.PureTrace.Support.CanonicalPosteriorValue
import TraceableAgency.PureTrace.Support.FiniteIntegralRepresentation
import TraceableAgency.PureTrace.Support.GenericHersteinMilnor

namespace TraceableAgency

universe u

/-- Assumption-free compatibility shell for the former Herstein--Milnor
boundary.

The selected posterior value is obtained from the preference-free
`genericHersteinMilnorMixtureTheorem`, now proved in Lean for the exact
sequentially-closed/interior-mixture schema, after Lean has derived all of its
ordinal hypotheses and constructed the posterior-law quotient as an abstract
convex mixture space.  Its private universe marker has a canonical default and
contributes no mathematical assumption. In particular, posterior-law continuity
is not an input:
`posteriorLawContinuity_of_axioms` proves it from primitive A2 and main-text
A1, A5, and A6.
Lean constructs the required continuous barycentric coordinates by explicit
finite vertex insertion and derives the spread/merge sandwich.

Finite Blackwell equivalence is not a field: the explicit
`posteriorMatchingKernel` construction proves it internally.  The
paper-specific block-comparison replacement package is then reconstructed
from that theorem plus the A6/A5/A1 replacement plumbing. -/
structure FinalHMInterface.{v} where
  private marker : ULift.{v} PUnit := ⟨PUnit.unit⟩

/-- Canonical inhabitant of the assumption-free HM compatibility shell. -/
def provedFinalHMInterface : FinalHMInterface.{u} := {}

/-- Posterior-law sufficiency from the auditable final HM interface.

The proved finite Blackwell equivalence theorem is upgraded to the
block-comparison replacement package by internal A6/A5/A1 plumbing, then fed
to `from_axioms_to_posterior_of_blackwell`. -/
theorem posteriorLawSufficiency_of_FinalHMInterface
    (_hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : PureTraceConditions F) :
    PosteriorLawSufficiency F :=
  posteriorLawSufficiency_of_axioms F hax

/-- Posterior-law continuity is derived from the primitive ordinal axioms,
not postulated by `FinalHMInterface`. -/
theorem posteriorLawContinuity_of_FinalHMInterface
    (_hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : PureTraceConditions F) :
    PosteriorLawContinuity F :=
  posteriorLawContinuity_of_axioms
    F finiteSamePosteriorLawBlackwellEquivalence hax

/-- Raw finite HM representative before the scale gauge is fixed. -/
noncomputable def rawPosteriorValueRepresentation_of_FinalHMInterface
    (_hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : PureTraceConditions F) :
    PosteriorValueRepresentation F :=
  posteriorValueRep_of_axioms_HMTheorem
    F finiteSamePosteriorLawBlackwellEquivalence
      genericHersteinMilnorMixtureTheorem hax

/-- Canonical posterior value representative.

At a boundary prior it first restricts to the positive-support simplex; on a
non-singleton full-support simplex it divides by the value of full revelation.
The normalization is derived from A1/A4 positivity and finite affine-utility
uniqueness, so exact support and relabelling covariance are theorems rather
than conventions. -/
noncomputable def posteriorValueRepresentation_of_FinalHMInterface
    (hhm : FinalHMInterface.{u})
    {F : PrefFamily.{u}}
    (hax : PureTraceConditions F) :
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
    ∀ {F : PrefFamily.{u}} (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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

Paper Lemma blockbridge, rescaled.  The
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F) :
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
    (hax : PureTraceConditions F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_preUniversalBridge
    hready.cross_prior_blockbridge hax
    (entropyReduction_of_preEntropyReady hready hhm huniq hax)
    rfl

end TraceableAgency
