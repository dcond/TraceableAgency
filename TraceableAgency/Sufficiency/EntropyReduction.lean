/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.EntropyReductionClosure
import TraceableAgency.External.GenericFaddeev

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
# Paper Stage 5: entropy reduction and Shannon identification

The input to this file is exactly the output of the product/branch compatibility
argument in Appendix A:

* a coherent face-scale representative;
* the universal chain scale obtained after interaction collapse;
* the unscaled cross-prior block bridge; and
* exact relabelling/support transport for the selected representative.

In particular, the theorem below does not reconstruct any of these objects
through the legacy posterior-integral Herstein--Milnor route.  Finite sums of
the entropy candidate over posterior laws still occur in the entropy-reduction
identity, as they do in the paper; no pointwise integrand representing the
original affine fibre utility is selected.
-/

/-- The paper's entropy-reduction/Faddeev endpoint from the outputs of Stages
3--5.  This is the minimal final consumer used by the refactored pure-trace
proof.

The equality `hagg` only records that the interaction-collapse object and the
cross-prior bridge carry the same selected branch representative.  It is
definitionally `rfl` for the intended paper-stage constructor. -/
theorem MIRep_of_paperInteractionCollapse
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces)
    (hcollapse : InteractionCollapseUniversalChainScaleStructure F)
    (hbridge : FinitePreUniversalCrossPriorBlockBridgeFor hfaces)
    (hagg :
      hcollapse.scale_coherence.branch_agg =
        hfaces.branch_result.branch_agg)
    (hscale :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        hcollapse.scale_coherence.scale q =
          hfaces.branch_result.scale_factorization.scale q)
    (hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces)
    (hax : TraceAxioms F) :
    MIRep F := by
  set hentropy : EntropyReductionRepresentation F :=
    EntropyReductionRepresentation_of_interactionCollapse hcollapse
      with hentropy_def
  have hentropy_scale_coherence :
      hentropy.scale_coherence = hcollapse.scale_coherence := by
    simp only [hentropy_def,
      EntropyReductionRepresentation_of_interactionCollapse,
      EntropyReductionRepresentation_of_scale]
  have hagg' :
      hentropy.scale_coherence.branch_agg =
        hfaces.branch_result.branch_agg := by
    rw [hentropy_scale_coherence]
    exact hagg
  set hcross : CrossPriorBlockRepresentation F :=
    crossPriorBlockRepresentation_of_preUniversalBridge
      hbridge hax hentropy hagg'
      with hcross_def
  have hcross_scale_coherence :
      hcross.entropy_reduction.scale_coherence =
        hcollapse.scale_coherence := by
    rw [hcross_def]
    change hentropy.scale_coherence = hcollapse.scale_coherence
    exact hentropy_scale_coherence
  have hsf : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (r : Dist A)
      [Nonempty (supportSubtype r)]
      (_hn : ∃ a : A, 0 < r a)
      (_hnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
      (_hb : ¬ r.FullSupport),
      hcross.entropy_reduction.scale_coherence.branch_agg.branchCoeff q r =
      hcross.entropy_reduction.scale_coherence.scale q /
          hcross.entropy_reduction.scale_coherence.scale
            r.restrictToSupport := by
    intro A _ _ _ q hq r _ hn hnd hb
    rw [hcross_scale_coherence, hagg, hscale q,
      hscale r.restrictToSupport]
    exact hfaces.support_face_scale_eq q hq r hn hnd hb
  let hc : CrossPriorBlockRepresentation F := wrapCross hcross hsf
  have hHfunId : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      hc.entropy_reduction.Hfun q =
        normalizedValue hc.entropy_reduction.scale_coherence q
          Channel.idChannel :=
    fun _q => rfl
  have hnormC : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] (P : Channel A O) (q : Dist A),
      ¬ q.FullSupport →
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      normalizedValue hc.entropy_reduction.scale_coherence q P =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport (Channel.restrictToSupport P q) := by
    intro A O _ _ _ _ _ P q hqb
    apply field1_boundaryComplete_of_selectedValue
      hcross.entropy_reduction.scale_coherence hsf
    · intro A' O' _ _ _ _ _ r _ R
      rw [hcross_scale_coherence, hagg]
      exact hboundaryValue.boundary_value_support r R
    · exact hqb
  have hhfunC : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      hc.entropy_reduction.Hfun q =
        hc.entropy_reduction.Hfun q.restrictToSupport := by
    intro A _ _ _ q
    haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    rw [hHfunId q, hHfunId q.restrictToSupport,
      show normalizedValue hc.entropy_reduction.scale_coherence q
          Channel.idChannel =
        normalizedValue hc.entropy_reduction.scale_coherence
          q.restrictToSupport
          (Channel.restrictToSupport Channel.idChannel q) from ?_,
      normalizedValue_restrict_idChannel_eq_idSupport
        hc.entropy_reduction q]
    by_cases hqf : q.FullSupport
    · exact normalizedValue_support_restrict_fullSupport_of_crossPrior
        F hax hc Channel.idChannel q hqf
    · exact hnormC Channel.idChannel q hqf
  have hrelabC : ∀ {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (qA : Dist A), qA.FullSupport →
      hc.entropy_reduction.Hfun (Relabeling.relabelDist e qA) =
        hc.entropy_reduction.Hfun qA := by
    intro A B _ _ _ _ _ _ e qA hqA
    have hqB : (Relabeling.relabelDist e qA).FullSupport :=
      Relabeling.relabelDist_fullSupport e qA hqA
    rw [wrapCross_Hfun_fullSupport hcross hsf
          (Relabeling.relabelDist e qA) hqB,
      wrapCross_Hfun_fullSupport hcross hsf qA hqA]
    unfold normalizedValue
    rw [hcross_scale_coherence, hagg,
      hscale (Relabeling.relabelDist e qA), hscale qA]
    have hV := hsel.V_relabel_eq hax e e qA
      (Channel.idChannel : Channel A A)
    rw [relabelChannel_id_eq e] at hV
    have hs :=
      CoherentRelabelingFaceScalesStructure.scale_relabel_eq
        hfaces e qA hqA
    rw [hV, hs]
  have hIntC : ∀ {A O : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q : Dist A),
      haveI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      posteriorLawIntegral q P hc.entropy_reduction.Hfun =
        posteriorLawIntegral q.restrictToSupport
          (Channel.restrictToSupport P q)
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
    set t := Channel.posterior
      (Channel.restrictToSupport P q) q.restrictToSupport o with htdef
    haveI : Nonempty
        (supportSubtype
          (Channel.actionPushforward t (supportIncludeKernel q))) :=
      supportSubtype_nonempty _
    haveI : Nonempty (supportSubtype t) := supportSubtype_nonempty t
    have hl := hhfunC
      (Channel.actionPushforward t (supportIncludeKernel q))
    have hr := hhfunC t
    have hrestrict :
        (Channel.actionPushforward t
          (supportIncludeKernel q)).restrictToSupport =
          Relabeling.relabelDist
            (supportIncludePushforwardSupportEquiv q t).symm
            t.restrictToSupport :=
      restrict_supportInclude_eq_relabel_support q t
    have hrel := hrelabC
      (supportIncludePushforwardSupportEquiv q t).symm
      t.restrictToSupport (Dist.restrictToSupport_fullSupport t)
    calc
      hc.entropy_reduction.Hfun
          (Channel.actionPushforward t (supportIncludeKernel q)) =
          hc.entropy_reduction.Hfun
            (Channel.actionPushforward t
              (supportIncludeKernel q)).restrictToSupport := hl
      _ = hc.entropy_reduction.Hfun
            (Relabeling.relabelDist
              (supportIncludePushforwardSupportEquiv q t).symm
              t.restrictToSupport) := by rw [hrestrict]
      _ = hc.entropy_reduction.Hfun t.restrictToSupport := hrel
      _ = hc.entropy_reduction.Hfun t := hr.symm
  have hreg : EntropyRegularity F hc.entropy_reduction :=
    entropyRegularity_forCross hax hc hHfunId hnormC
  have hER : ∀ {K : Type u} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      hc.entropy_reduction.Hfun (sigmaDist p q) =
        normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) +
        posteriorLawIntegral (sigmaDist p q)
          (coarseRevealChannel Act) hc.entropy_reduction.Hfun :=
    fun {K} _ _ _ Act _ _ _ _ p q =>
      coarseReveal_entropyReduction_ofFacts
        F hax hc hnormC hhfunC hIntC Act p q
  have hblockE : ∀ {K : Type u}
      [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (k : K) (qk : Dist (Act k)),
      hc.entropy_reduction.Hfun (blockEmbedDist Act k qk) =
        hc.entropy_reduction.Hfun qk :=
    fun {K} _ _ _ Act _ _ _ _ k qk =>
      Hfun_blockEmbed_ofFacts F hc hhfunC hrelabC Act k qk
  have hcoarse : ∀ {K : Type u}
      [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type u)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)] [Nonempty ((k : K) × Act k)]
      (p : Dist K) (q : ∀ k, Dist (Act k)),
      normalizedValue hc.entropy_reduction.scale_coherence
          (sigmaDist p q) (coarseRevealChannel Act) =
        hc.entropy_reduction.Hfun p :=
    fun {K} _ _ _ Act _ _ _ _ p q =>
      coarseVal_forCross F hax hc hreg hnormC
        (field3_restricted_coarse_reveal F hax hc hreg)
        hhfunC Act p q
  intro A O instA instDA instO instDO P qq qq'
  exact MIRep_ofCrossFacts
    hfad F hax hc hreg hhfunC hER hblockE hcoarse P qq qq'

end TraceableAgency
