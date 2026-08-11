/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation

namespace TraceableAgency

universe u

/-!
## Branch cocycle and normalised chain-rule layer

The named paper result `Branch-coefficient cocycle and normalised chain rule`
does not require the later universal-scale collapse.  The following structure
records the part needed for the normalised chain rule: branch aggregation plus
positive prior-dependent scales factoring the branch coefficients.
-/

/-- Branch aggregation with prior-dependent chain scales, before the later
universal-scale collapse. -/
structure BranchChainStructure (F : PrefFamily.{u}) where
  branch_agg : BranchAggregationStructure F
  scale :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → ℝ
  scale_pos :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      0 < scale q
  branchCoeff_factorization :
    ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (o₁ : O₁),
      BranchPositive P₁ q o₁ →
      branch_agg.branchCoeff q (Channel.posterior P₁ q o₁) =
        scale q / scale (Channel.posterior P₁ q o₁)

/-- Explicit finite branch coefficient cocycle interface for a fixed
`BranchAggregationStructure`.

The statement is restricted to one ambient finite action type and full-support
priors, matching the first part of the paper's cocycle proof. Boundary and
mixed-support extensions are kept separate. -/
structure FiniteBranchCoeffCocycleAssumptionsFor.{v}
    {F : PrefFamily.{v}} (hbranch : BranchAggregationStructure F) : Prop where
  coeff_cocycle_fullSupport :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r s : Dist A)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hnd : ∃ a b : A, a ≠ b),
      hbranch.branchCoeff q s =
        hbranch.branchCoeff q r * hbranch.branchCoeff r s

/-- Full-support cocycle for the faithful tangent-scalar branch coefficient.

This is the algebraic core of the paper's cocycle proof before it is transported
to the public `BranchAggregationStructure.branchCoeff`. -/
structure FiniteBranchCoeffCocycleTangentScalarFor.{v}
    (F : PrefFamily.{v}) (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{v})
    (hscalar : BranchPathTangentScalarStructure F hV hlin) : Prop where
  coeff_cocycle_fullSupport :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r s : Dist A)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hnd : ∃ a b : A, a ≠ b),
      hscalar.branchPathCoeff q s =
        hscalar.branchPathCoeff q r * hscalar.branchPathCoeff r s

/-- The faithful tangent-scalar coefficient satisfies the full-support cocycle.

The proof compares the three scalar relations
`L_q = beta(q,s)L_s`, `L_q = beta(q,r)L_r`, and
`L_r = beta(r,s)L_s`, then cancels a nonzero tangent direction supplied by A1.
It does not use the public branch aggregation formula, scale factorization, or
the later universal scale theorem. -/
theorem branchCoeffTangentScalar_cocycle_fullSupport
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hscalar : BranchPathTangentScalarStructure F hV hlin)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r s : Dist A)
    (hq : q.FullSupport) (hr : r.FullSupport) (hs : s.FullSupport)
    (hnd : ∃ a b : A, a ≠ b) :
    hscalar.branchPathCoeff q s =
      hscalar.branchPathCoeff q r * hscalar.branchPathCoeff r s := by
  classical
  rcases hnd with ⟨a, b, hab⟩
  have hs_nd : ∃ a b : A, a ≠ b ∧ 0 < s a ∧ 0 < s b :=
    ⟨a, b, hab, hs a, hs b⟩
  have hr_nd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b :=
    ⟨a, b, hab, hr a, hr b⟩
  rcases branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV q s hq hs hs_nd with
    ⟨η, hηatomic, hηtan, hηnz⟩
  -- η is a posterior-law difference; hηatomic witnesses its atomic-linear form
  have hqs :=
    hscalar.linear_part_scalar_relation_on_tangent q s hq hs hs_nd η hηatomic hηtan
  have hqr :=
    hscalar.linear_part_scalar_relation_on_tangent q r hq hr hr_nd η hηatomic hηtan
  have hrs :=
    hscalar.linear_part_scalar_relation_on_tangent r s hr hs hs_nd η hηatomic hηtan
  let Ls : ℝ := hlin.linearPart F hV s η
  have hcoeff_times :
      hscalar.branchPathCoeff q s * Ls =
        (hscalar.branchPathCoeff q r * hscalar.branchPathCoeff r s) * Ls := by
    calc
      hscalar.branchPathCoeff q s * Ls =
          hlin.linearPart F hV q η := by
            simpa [Ls] using hqs.symm
      _ = hscalar.branchPathCoeff q r * hlin.linearPart F hV r η := hqr
      _ = hscalar.branchPathCoeff q r *
            (hscalar.branchPathCoeff r s * Ls) := by
            rw [hrs]
      _ = (hscalar.branchPathCoeff q r *
            hscalar.branchPathCoeff r s) * Ls := by
            ring
  have hmul :
      (hscalar.branchPathCoeff q s -
          hscalar.branchPathCoeff q r * hscalar.branchPathCoeff r s) *
        Ls = 0 := by
    nlinarith [hcoeff_times]
  have hcoef :
      hscalar.branchPathCoeff q s -
          hscalar.branchPathCoeff q r * hscalar.branchPathCoeff r s = 0 :=
    (mul_eq_zero.mp hmul).resolve_right (by simpa [Ls] using hηnz)
  nlinarith

/-- Package form of `branchCoeffTangentScalar_cocycle_fullSupport`. -/
theorem branchCoeffCocycleTangentScalar_of_A1
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hscalar : BranchPathTangentScalarStructure F hV hlin) :
    FiniteBranchCoeffCocycleTangentScalarFor F hV hlin hscalar where
  coeff_cocycle_fullSupport := by
    intro A _ _ _ q r s hq hr hs hnd
    exact branchCoeffTangentScalar_cocycle_fullSupport
      hlin F hax hV hscalar q r s hq hr hs hnd

/-- Transport the faithful tangent-scalar cocycle to the public branch
coefficient of the `BranchAggregationStructure` reassembled through the
tangent-formula route.

The public cocycle interface is full-support only, so the assembled coefficient
definition always selects the tangent scalar branch. -/
theorem branchCoeffCocycleFor_of_tangentScalar
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hformula :
      FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle) :
    FiniteBranchCoeffCocycleAssumptionsFor
      (branchAggregationStructure_of_tangentFormulaFor
        F hax hV hlin hpath hboundary hsingle hformula) where
  coeff_cocycle_fullSupport := by
    intro A _ _ _ q r s hq hr hs hnd
    rw [branchAggregationStructure_of_tangentFormulaFor_branchCoeff_fullSupport_eq
      F hax hV hlin hpath hboundary hsingle hformula q s hs]
    rw [branchAggregationStructure_of_tangentFormulaFor_branchCoeff_fullSupport_eq
      F hax hV hlin hpath hboundary hsingle hformula q r hr]
    rw [branchAggregationStructure_of_tangentFormulaFor_branchCoeff_fullSupport_eq
      F hax hV hlin hpath hboundary hsingle hformula r s hs]
    exact branchCoeffTangentScalar_cocycle_fullSupport
      hlin F hax hV hpath q r s hq hr hs hnd

/-- Full-support scale factorization interface.

This is the basepoint factorization part of the branch-chain lemma restricted
to nondegenerate full-support priors in one ambient action simplex. Boundary
and singleton extensions are kept separate. -/
structure FiniteBranchScaleFactorizationFullSupportAssumptions.{v}
    {F : PrefFamily.{v}} (hbranch : BranchAggregationStructure F) where
  scale :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → ℝ
  scale_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hnd : ∃ a b : A, a ≠ b),
      0 < scale q
  branchCoeff_factorization_fullSupport :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hnd : ∃ a b : A, a ≠ b),
      hbranch.branchCoeff q r = scale q / scale r

/-- Basepoint scale for full-support factorization, using the uniform prior as
the basepoint on each finite action type. -/
noncomputable def branchFullSupportBaseScale
    {F : PrefFamily.{u}} (hbranch : BranchAggregationStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  hbranch.branchCoeff q (Dist.uniform (A := A))

/-- The full-support branch cocycle gives basepoint scale factorization on
nondegenerate ambient action types. -/
noncomputable def branchScaleFactorizationFullSupport_of_cocycle
    {F : PrefFamily.{u}} (hbranch : BranchAggregationStructure F)
    (hcocycle : FiniteBranchCoeffCocycleAssumptionsFor hbranch) :
    FiniteBranchScaleFactorizationFullSupportAssumptions hbranch where
  scale := fun q => branchFullSupportBaseScale hbranch q
  scale_pos := by
    intro A _ _ _ q hq hnd
    rcases hnd with ⟨a, b, hab⟩
    have huniform_nd :
        ∃ a b : A, a ≠ b ∧
          0 < (Dist.uniform (A := A)) a ∧
          0 < (Dist.uniform (A := A)) b :=
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
    exact hbranch.branchCoeff_pos q (Dist.uniform (A := A)) hq huniform_nd
  branchCoeff_factorization_fullSupport := by
    intro A _ _ _ q r hq hr hnd
    let q0 : Dist A := Dist.uniform (A := A)
    have hq0 : q0.FullSupport := Dist.uniform_fullSupport
    have hc :
        hbranch.branchCoeff q q0 =
          hbranch.branchCoeff q r * hbranch.branchCoeff r q0 :=
      hcocycle.coeff_cocycle_fullSupport q r q0 hq hr hq0 hnd
    rcases hnd with ⟨a, b, hab⟩
    have hq0_nd :
        ∃ a b : A, a ≠ b ∧ 0 < q0 a ∧ 0 < q0 b :=
      ⟨a, b, hab, hq0 a, hq0 b⟩
    have hscale_r_pos : 0 < hbranch.branchCoeff r q0 :=
      hbranch.branchCoeff_pos r q0 hr hq0_nd
    unfold branchFullSupportBaseScale
    change hbranch.branchCoeff q r =
      hbranch.branchCoeff q q0 / hbranch.branchCoeff r q0
    rw [hc]
    field_simp [ne_of_gt hscale_r_pos]

/-- Boundary part of branch scale factorization.

Full-support factorization is already internal from the cocycle.  This
interface isolates the remaining non-singleton boundary posterior case. -/
structure FiniteBranchScaleFactorizationBoundaryTransportAssumptions.{v}
    {F : PrefFamily.{v}} (hbranch : BranchAggregationStructure F)
    (hfull : FiniteBranchScaleFactorizationFullSupportAssumptions hbranch) : Prop where
  branchCoeff_factorization_boundary :
    ∀ {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (o₁ : O₁),
      BranchPositive P₁ q o₁ →
      (∃ a b : A, a ≠ b ∧
        0 < (Channel.posterior P₁ q o₁) a ∧
        0 < (Channel.posterior P₁ q o₁) b) →
      ¬ (Channel.posterior P₁ q o₁).FullSupport →
      hbranch.branchCoeff q (Channel.posterior P₁ q o₁) =
        hfull.scale q / hfull.scale (Channel.posterior P₁ q o₁)

/-- Singleton/degenerate part of branch scale factorization.

The scale at singleton-support priors is not fixed by value variation in the
branch formula.  This package isolates the needed normalization for reconstructing
the public scale-factorization interface. -/
structure FiniteBranchScaleFactorizationSingletonNormalization.{v}
    {F : PrefFamily.{v}} (hbranch : BranchAggregationStructure F)
    (hfull : FiniteBranchScaleFactorizationFullSupportAssumptions hbranch) : Prop where
  scale_pos_singleton :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (_hsingle_support :
        ∃ a : A, 0 < q a ∧ ∀ b : A, 0 < q b → b = a),
      0 < hfull.scale q
  branchCoeff_factorization_singleton :
    ∀ {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (o₁ : O₁),
      BranchPositive P₁ q o₁ →
      (∃ a : A,
        0 < (Channel.posterior P₁ q o₁) a ∧
        ∀ b : A, 0 < (Channel.posterior P₁ q o₁) b → b = a) →
      hbranch.branchCoeff q (Channel.posterior P₁ q o₁) =
        hfull.scale q / hfull.scale (Channel.posterior P₁ q o₁)

/-- Scale-factorization interface for branch coefficients.  This is the
factorisation part of `Branch-coefficient cocycle and normalised chain rule`,
without the later theorem that the scale is universal across priors. -/
structure FiniteBranchScaleFactorizationAssumptions.{v}
    {F : PrefFamily.{v}} (hbranch : BranchAggregationStructure F) where
  scale :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → ℝ
  scale_pos :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      0 < scale q
  branchCoeff_factorization :
    ∀ {A O₁ : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (o₁ : O₁),
      BranchPositive P₁ q o₁ →
      hbranch.branchCoeff q (Channel.posterior P₁ q o₁) =
        scale q / scale (Channel.posterior P₁ q o₁)

/-- Reassemble public branch scale factorization from the internal
full-support part plus explicit boundary and singleton extensions. -/
noncomputable def branchScaleFactorization_of_fullSupport_boundary_singleton
    {F : PrefFamily.{u}} (hbranch : BranchAggregationStructure F)
    (hfull : FiniteBranchScaleFactorizationFullSupportAssumptions hbranch)
    (hboundary :
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions hbranch hfull)
    (hsingle :
      FiniteBranchScaleFactorizationSingletonNormalization hbranch hfull) :
    FiniteBranchScaleFactorizationAssumptions hbranch where
  scale := hfull.scale
  scale_pos := by
    intro A _ _ _ q hq
    by_cases hndA : ∃ a b : A, a ≠ b
    · exact hfull.scale_pos q hq hndA
    · have hnot_support :
          ¬ ∃ a b : A, a ≠ b ∧ 0 < q a ∧ 0 < q b := by
        rintro ⟨a, b, hne, _ha, _hb⟩
        exact hndA ⟨a, b, hne⟩
      exact hsingle.scale_pos_singleton q hq
        (singleton_support_of_not_nondegenerate q hnot_support)
  branchCoeff_factorization := by
    intro A O₁ _ _ _ _ _ q hq P₁ o₁ hpos
    let r : Dist A := Channel.posterior P₁ q o₁
    by_cases hnd_support : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b
    · by_cases hfull_r : r.FullSupport
      · have hndA : ∃ a b : A, a ≠ b := by
          rcases hnd_support with ⟨a, b, hne, _ha, _hb⟩
          exact ⟨a, b, hne⟩
        simpa [r] using
          hfull.branchCoeff_factorization_fullSupport q r hq hfull_r hndA
      · exact hboundary.branchCoeff_factorization_boundary
          q hq P₁ o₁ hpos (by simpa [r] using hnd_support)
          (by simpa [r] using hfull_r)
    · have hsingle_support :
          ∃ a : A, 0 < r a ∧ ∀ b : A, 0 < r b → b = a :=
        singleton_support_of_not_nondegenerate r hnd_support
      exact hsingle.branchCoeff_factorization_singleton
        q hq P₁ o₁ hpos (by simpa [r] using hsingle_support)

/-- Faithful branch aggregation structure reassembled from the boundary
representative and coefficient transport components. -/
noncomputable def faithfulBranchAggregationStructure_of_components
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hvalue : FiniteBranchBoundaryValueTransportAssumptions.{u})
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary) :
    BranchAggregationStructure F :=
  branchAggregationStructure_of_tangentFormulaFor
    F hax hV hlin hpath hboundary hsingle
    (branchAggregationFormulaTangentFor_of_boundaryTransport
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff)

/-- Faithful branch aggregation structure reassembled from selected boundary
value transport and coefficient transport components. -/
noncomputable def faithfulBranchAggregationStructure_of_componentsFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary) :
    BranchAggregationStructure F :=
  branchAggregationStructure_of_tangentFormulaFor
    F hax hV hlin hpath hboundary hsingle
    (branchAggregationFormulaTangentFor_of_boundaryTransportFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff)

/-- Full-support factorization for the faithful branch structure reassembled
from the full-support cocycle. -/
noncomputable def faithfulBranchFullSupportScale_of_components
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hvalue : FiniteBranchBoundaryValueTransportAssumptions.{u})
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (faithfulBranchAggregationStructure_of_components
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff) :=
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransport
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  branchScaleFactorizationFullSupport_of_cocycle
    (branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula)
    (branchCoeffCocycleFor_of_tangentScalar
      F hax hV hlin hpath hboundary hsingle hformula)

/-- Full-support factorization for the selected faithful branch structure. -/
noncomputable def faithfulBranchFullSupportScale_of_componentsFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (faithfulBranchAggregationStructure_of_componentsFor
        F hax hV hlin hpath hboundary hsingle hvalue hcoeff) :=
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransportFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  branchScaleFactorizationFullSupport_of_cocycle
    (branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula)
    (branchCoeffCocycleFor_of_tangentScalar
      F hax hV hlin hpath hboundary hsingle hformula)

/-- Reassemble the pre-universal chain structure from scale factorization. -/
noncomputable def branchChainStructure_of_scaleFactorization
    {F : PrefFamily.{u}} (hbranch : BranchAggregationStructure F)
    (hfactor : FiniteBranchScaleFactorizationAssumptions.{u} hbranch) :
    BranchChainStructure F where
  branch_agg := hbranch
  scale := hfactor.scale
  scale_pos := hfactor.scale_pos
  branchCoeff_factorization := hfactor.branchCoeff_factorization

/-- Final faithful pre-universal branch-chain reassembly.

This is the Stage 22 faithful route for the named result "Branch aggregation,
cocycle, and normalised chain rule": once the accepted tangent geometry, the
support-face representative normalization, boundary coefficient/scale normalizations,
and singleton normalizations are supplied, the public `BranchChainStructure`
follows. -/
noncomputable def BranchAggregationChainRule_of_faithful_components
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
    (hvalue : FiniteBranchBoundaryValueTransportAssumptions.{u})
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary)
    (hboundaryScale :
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff))
    (hsingleScale :
      FiniteBranchScaleFactorizationSingletonNormalization
        (faithfulBranchAggregationStructure_of_components
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    BranchChainStructure F :=
  let hbranch :=
    faithfulBranchAggregationStructure_of_components
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  let hfull :=
    faithfulBranchFullSupportScale_of_components
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  branchChainStructure_of_scaleFactorization hbranch
    (branchScaleFactorization_of_fullSupport_boundary_singleton
      hbranch hfull hboundaryScale hsingleScale)

/-- Selected faithful branch-chain reassembly.

This is the same named-result constructor as
`BranchAggregationChainRule_of_faithful_components`, but its support-face value
input is fixed to the representative being assembled. -/
noncomputable def BranchAggregationChainRule_of_faithful_componentsFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hcoeff :
      FiniteBranchBoundaryCoefficientTransportAssumptions.{u} hlin hboundary)
    (hboundaryScale :
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff))
    (hsingleScale :
      FiniteBranchScaleFactorizationSingletonNormalization
        (faithfulBranchAggregationStructure_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_componentsFor
          F hax hV hlin hpath hboundary hsingle hvalue hcoeff)) :
    BranchChainStructure F :=
  let hbranch :=
    faithfulBranchAggregationStructure_of_componentsFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  let hfull :=
    faithfulBranchFullSupportScale_of_componentsFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  branchChainStructure_of_scaleFactorization hbranch
    (branchScaleFactorization_of_fullSupport_boundary_singleton
      hbranch hfull hboundaryScale hsingleScale)

/-- Reassemble the pre-universal branch-chain structure through the faithful
tangent-scalar branch aggregation route.

This does not prove scale factorization.  It records that once the
tangent-scalar formula bridge has produced the public
`BranchAggregationStructure`, the existing normalised chain-rule layer applies
without using the legacy hax-free branch path package. -/
noncomputable def branchChainStructure_of_tangentFormulaAndScaleFactorization
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationFor F hV)
    (hformula :
      FiniteBranchAggregationFormulaTangentFor F hax hV hlin hpath hboundary hsingle)
    (hfactor :
      FiniteBranchScaleFactorizationAssumptions
        (branchAggregationStructure_of_tangentFormulaFor
          F hax hV hlin hpath hboundary hsingle hformula)) :
    BranchChainStructure F :=
  branchChainStructure_of_scaleFactorization
    (branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula)
    hfactor

/-- Normalized value for the pre-universal branch-chain scale. -/
noncomputable def branchNormalizedValue {F : PrefFamily.{u}}
    (hchain : BranchChainStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) : ℝ :=
  hchain.branch_agg.value_rep.V q (experimentOfChannel P) / hchain.scale q

/-- Normalised chain rule from branch aggregation and branch-coefficient
factorization.  This is the formal core of the paper's normalised chain rule;
it does not use the later universal-scale theorem. -/
theorem branchNormalizedValue_seqCompose_of_chain
    {F : PrefFamily.{u}} (hchain : BranchChainStructure F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : O → Channel A Y) :
    branchNormalizedValue hchain q (P ▷ Q)
    =
    branchNormalizedValue hchain q P
      + ∑ o : O,
          (Channel.outcomeMarginal P q) o *
          branchNormalizedValue hchain (Channel.posterior P q o) (Q o) := by
  unfold branchNormalizedValue
  have hsq_pos : 0 < hchain.scale q := hchain.scale_pos q hq
  have hsq_ne : hchain.scale q ≠ 0 := ne_of_gt hsq_pos
  have hagg := hchain.branch_agg.branch_aggregation q hq P Q
  rw [hagg]
  rw [add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hpos : (Channel.outcomeMarginal P q) o > 0
  · rw [hchain.branchCoeff_factorization q hq P o hpos]
    field_simp [hsq_ne]
  · have hm0 : (Channel.outcomeMarginal P q) o = 0 :=
      le_antisymm (le_of_not_gt hpos) ((Channel.outcomeMarginal P q).nonneg o)
    rw [hm0]
    ring

end TraceableAgency
