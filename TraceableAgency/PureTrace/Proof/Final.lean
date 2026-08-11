/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Proof.Affine
import TraceableAgency.PureTrace.Proof.Spine
import TraceableAgency.PureTrace.Proof.ProductGauge
import TraceableAgency.PureTrace.Proof.FaceCoherence
import TraceableAgency.PureTrace.Proof.Scales
import TraceableAgency.PureTrace.Proof.EntropyReduction

namespace TraceableAgency

universe u

/-!
# Paper-faithful pure-trace assembly

This file connects the five direct stages of the paper reduction.  The
cardinal face-defect cocycle remains visible as an intermediate interface,
but the final theorem constructs it from the direct nested-face argument.
-/

/-! ## The selected representative entering the product argument -/

/-- The direct fixed-prior Herstein--Milnor utility, completed on boundary
priors by restriction to positive support. -/
noncomputable def paperDirectHMPosteriorValue
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    PosteriorValueRepresentation F :=
  posteriorValueRep_of_HersteinMilnorConclusion F
    (posteriorLawSufficiency_of_axioms F hax)
    (finiteHersteinMilnorConclusion_direct_of_axioms F hax)

/-- The canonical, full-revelation-normalized representative used by the
paper before product normalization. -/
noncomputable def paperCanonicalPosteriorValue
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    PosteriorValueRepresentation F :=
  canonicalPosteriorValueRepresentation hax
    (paperDirectHMPosteriorValue F hax)

/-- Exact relabelling of the canonical representative. -/
theorem paperCanonicalPosteriorValue_relabeling
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    PosteriorValueRelabeling (paperCanonicalPosteriorValue F hax) where
  V_relabel_eq := by
    intro A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    exact canonicalPosteriorValue_relabel hax
      (paperDirectHMPosteriorValue F hax) eA eO q P

/-- Exact transport of the canonical representative to the positive-support
face. -/
theorem paperCanonicalPosteriorValue_boundaryTransport
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    FiniteBranchBoundaryValueTransportFor F hax
      (paperCanonicalPosteriorValue F hax) where
  boundary_value_transport := by
    intro A O _ _ _ _ _ q _ P
    exact canonicalPosteriorValue_supportFace hax
      (paperDirectHMPosteriorValue F hax) q P

/-! ## Product gauge and the direct branch chain -/

/-- The normalized product gauge selected from the canonical value. -/
noncomputable def paperPosteriorProductGaugeData
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    PosteriorProductGaugeData (paperCanonicalPosteriorValue F hax) :=
  posteriorProductGaugeData_of_axioms
    (paperCanonicalPosteriorValue_relabeling F hax) hax
    (paperCanonicalPosteriorValue_boundaryTransport F hax)

/-- The gauged representative on which both product and branch comparisons
are performed. -/
noncomputable abbrev paperProductGaugedPosteriorValue
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    PosteriorValueRepresentation F :=
  (paperPosteriorProductGaugeData F hax).gaugedValue

/-- Boundary transport after the positive product gauge. -/
theorem paperProductGaugedBoundaryTransport
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    FiniteBranchBoundaryValueTransportFor F hax
      (paperProductGaugedPosteriorValue F hax) :=
  (paperPosteriorProductGaugeData F hax).boundaryValueTransport hax

/-- The direct tangent/branch/cocycle chain before cardinal face alignment. -/
noncomputable abbrev paperDirectBranchChain
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  directBranchChain_of_posteriorValue F hax
    (paperProductGaugedPosteriorValue F hax)
    (paperProductGaugedBoundaryTransport F hax)

/-- The one remaining face-geometric input to the current assembly. -/
abbrev PaperCardinalFaceDefectInput
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :=
  CardinalFaceDefectCocycleFor (paperDirectBranchChain F hax)

/-- The nested canonical-face cancellation supplies the remaining geometric
interface for the representative selected above. -/
noncomputable def paperCardinalFaceDefectCocycle
    (F : PrefFamily.{u}) (hax : PureTraceConditions F) :
    PaperCardinalFaceDefectInput F hax :=
  directCardinalFaceDefectCocycle F hax
    (paperProductGaugedPosteriorValue F hax)
    (paperProductGaugedBoundaryTransport F hax)
    (paperPosteriorProductGaugeData F hax).relabeling

/-! ## End-to-end reduction after the face defect cocycle -/

/-- Paper-route pure-trace reduction, conditional only on the direct cardinal
face-defect cocycle. -/
theorem pureTraceRepresentation_of_faceDefect
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hdef : PaperCardinalFaceDefectInput F hax) :
    PureTraceMIRepresentation F := by
  let hdata := paperPosteriorProductGaugeData F hax
  let hvalue := paperProductGaugedBoundaryTransport F hax
  let hfaces : CoherentRelabelingFaceScalesStructure F :=
    directCoherentRelabelingFaceScales_of_defect F hax
      (paperProductGaugedPosteriorValue F hax) hvalue hdef
  have hvalueEq :
      hfaces.branch_result.branch_agg.value_rep =
        paperProductGaugedPosteriorValue F hax := by
    rfl
  let hprod : FiniteProductQuasiAdditivityForFaceScales hfaces :=
    hdata.toProductQuasiAdditivityForFaceScales hfaces hvalueEq
  let hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod :=
    hdata.toProductScaleZPositiveForFaceScales hfaces hvalueEq
  have hboundaryValueFact :
      ∀ {A O : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype O] [DecidableEq O]
        (q : Dist A) [Nonempty (supportSubtype q)] (P : Channel A O),
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) =
          hfaces.branch_result.branch_agg.value_rep.V q.restrictToSupport
            (experimentOfChannel (Channel.restrictToSupport P q)) := by
    intro A O _ _ _ _ _ q _ P
    rw [hvalueEq]
    exact hvalue.boundary_value_transport q P
  let hboundaryValue : FiniteBoundaryValueSupportReadFor hfaces :=
    ⟨hboundaryValueFact⟩
  have hselFact :
      ∀ (_hax : PureTraceConditions F)
        {A B O Y : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        [Fintype O] [DecidableEq O]
        [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y)
        (q : Dist A) (P : Channel A O),
        hfaces.branch_result.branch_agg.value_rep.V
            (Relabeling.relabelDist eA q)
            (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) := by
    intro _hax A B O Y _ _ _ _ _ _ _ _ _ _ eA eO q P
    rw [hvalueEq]
    exact hdata.relabeling.V_relabel_eq eA eO q P
  let hsel : FiniteSelectedPosteriorValueRelabelingFor hfaces :=
    ⟨hselFact⟩
  let hcore : PaperScaleComparisonCore hfaces hprod :=
    paperScaleComparisonCore hfaces hboundaryValue hprod hpos hsel
  have hreference :
      hfaces.branch_result.scale_factorization.scale
        universalScaleReferencePrior = 1 := by
    exact directCoherentFaceScales_reference_scale_eq_one F hax
      (paperProductGaugedPosteriorValue F hax) hvalue hdef
  have hsingleOne :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A), q.FullSupport → Subsingleton A →
          hfaces.branch_result.scale_factorization.scale q = 1 := by
    intro A _ _ _ q hq hsub
    exact directCoherentFaceScales_subsingleton_scale_eq_one F hax
      (paperProductGaugedPosteriorValue F hax) hvalue hdef q hq hsub
  let hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces :=
    universalSingletonScale_of_paperCore hcore hreference hsingleOne hax
  let hcollapse : InteractionCollapseUniversalChainScaleStructure F :=
    interactionCollapse_of_paperScaleComparison
      hfaces hprod hcore hsingle hax
  let hbridge : FinitePreUniversalCrossPriorBlockBridgeFor hfaces :=
    finitePreUniversalCrossPriorBlockBridge_of_productQuasiAdditivity hprod
  apply MIRep_of_paperInteractionCollapse hfad hfaces hboundaryValue
    hcollapse hbridge
  · rfl
  · intro A _ _ _ q
    rfl
  · exact hsel
  · exact hax

/-- Unconditional paper-faithful pure-trace theorem.  Every input after the
classical Faddeev theorem is one of the primitive trace axioms. -/
theorem pureTraceRepresentation_of_conditions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F) :
    PureTraceMIRepresentation F :=
  pureTraceRepresentation_of_faceDefect hfad hax
    (paperCardinalFaceDefectCocycle F hax)

/-- Sufficiency packaged in the public statement used by the main theorem. -/
theorem pureTraceSufficiency_of_faddeev
    (hfad : ClassicalFaddeevTheoremAssumptions.{u}) :
    PureTraceSufficiency.{u} := by
  intro F hax
  exact pureTraceRepresentation_of_conditions hfad hax

end TraceableAgency
