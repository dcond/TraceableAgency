/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.BranchAggregation

/-!
# External Scale Coherence Assumptions

This file contains external assumptions for the scale coherence theorem,
which derives that the branch coefficients β(q,r) factor as a_q/a_r for
a universal scale a, independent of the prior q.

## Main definitions

* `FiniteScaleCoherenceAssumptions` - a structure bundling the scale coherence
  theorem as an external assumption.

## Status

These assumptions are:
1. Based on the paper's Lemmas chain, facescales, and scalecoherence (lines 2108-2500)
2. NOT proved in this Lean development
3. Used as explicit, auditable external assumptions
4. No anonymous `axiom` declarations are used

The scale coherence theorem derives:
1. **Cocycle property**: β(q,r) β(r,s) = β(q,s)
2. **Scale factorization**: β(q,r) = a_q/a_r for positive scales a_q
3. **Universal scale**: a_q = a is independent of q (via two-grouping argument)

## References

* empowerment_v5.tex, Lemma chain (lines 2108-2132)
* empowerment_v5.tex, Lemma facescales (lines 2269-2345)
* empowerment_v5.tex, Lemma scalecoherence (lines 2347-2500)

The proof uses:
- Branch aggregation (Lemma branchagg)
- Cocycle identity from tangent-space arguments
- A8 (independent background separability) for the two-grouping argument
- Product revelation and quasi-additivity
-/

set_option linter.style.header false

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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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

/-!
## Faithful Branch API

The old `FiniteBranchAggregationAssumptions` package returns a branch
aggregation structure from only A7 and a value representation.  The faithful
route developed in Stages 13--22 carries the extra classical finite-geometry
interfaces and the explicit boundary/singleton normalizations.  The following
bundle exposes that route without pretending to reconstruct the old hax-free
monolith.
-/

/-- Public faithful branch component bundle.

Later fields are dependent: boundary and singleton scale factorization are
typed for the branch structure and full-support scale constructed from the
earlier faithful components. -/
structure FiniteFaithfulBranchAggregationAssumptions.{v} where
  linear_part : FiniteAffineLinearPartAssumptions.{v}
  tangent_spanning : FiniteAtomicLinearPosteriorTangentSpanningAssumptions.{v}
  same_sign_scalar : FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{v}
  support_face_rep : FiniteSupportFaceRepresentativeTransportAssumptions.{v}
  boundary_coeff_scale : FiniteBoundaryCoefficientScaleNormalizationAssumptions.{v}
  singleton_scale : FiniteBranchSingletonScaleNormalizationAssumptions.{v}
  boundary_linear_transport :
    FiniteBoundaryLinearPartTransportAssumptions.{v}
      linear_part
      (boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff_scale)
  boundary_scale_factorization :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hV : PosteriorValueRepresentation F),
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          linear_part same_sign_scalar tangent_spanning F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff_scale
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport support_face_rep
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport
          linear_part hboundary boundary_linear_transport
      FiniteBranchScaleFactorizationBoundaryTransportAssumptions
        (faithfulBranchAggregationStructure_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)
  singleton_scale_factorization :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hV : PosteriorValueRepresentation F),
      let hpath :=
        branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
          linear_part same_sign_scalar tangent_spanning F hax hV
      let hboundary :=
        boundaryFaceScale_of_coefficientScaleNormalization boundary_coeff_scale
      let hvalue :=
        boundaryValueTransport_of_supportFaceRepresentativeTransport support_face_rep
      let hcoeff :=
        boundaryCoefficientTransport_of_linearPartTransport
          linear_part hboundary boundary_linear_transport
      FiniteBranchScaleFactorizationSingletonNormalization
        (faithfulBranchAggregationStructure_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)
        (faithfulBranchFullSupportScale_of_components
          F hax hV linear_part hpath hboundary singleton_scale hvalue hcoeff)

/-- Tangent scalar structure produced from a faithful branch bundle. -/
noncomputable def branchPathTangentScalarStructure_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchPathTangentScalarStructure F hV hfaith.linear_part :=
  branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning
    hfaith.linear_part hfaith.same_sign_scalar hfaith.tangent_spanning F hax hV

/-- Boundary face-scale structure produced from a faithful branch bundle. -/
def branchBoundaryFaceScale_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u}) :
    FiniteBranchBoundaryFaceScaleAssumptions.{u} :=
  boundaryFaceScale_of_coefficientScaleNormalization hfaith.boundary_coeff_scale

/-- Boundary value transport produced from a faithful branch bundle. -/
theorem branchBoundaryValueTransport_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u}) :
    FiniteBranchBoundaryValueTransportAssumptions.{u} :=
  boundaryValueTransport_of_supportFaceRepresentativeTransport
    hfaith.support_face_rep

/-- Boundary coefficient transport produced from a faithful branch bundle. -/
theorem branchBoundaryCoefficientTransport_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u}) :
    FiniteBranchBoundaryCoefficientTransportAssumptions.{u}
      hfaith.linear_part
      (branchBoundaryFaceScale_of_faithfulAssumptions hfaith) :=
  boundaryCoefficientTransport_of_linearPartTransport
    hfaith.linear_part
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.boundary_linear_transport

/-- Public branch aggregation structure produced from faithful branch
components. -/
noncomputable def branchAggregationStructure_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationStructure F :=
  faithfulBranchAggregationStructure_of_components
    F hax hV hfaith.linear_part
    (branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV)
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.singleton_scale
    (branchBoundaryValueTransport_of_faithfulAssumptions hfaith)
    (branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith)

/-- Full-support scale factorization produced from faithful branch
components. -/
noncomputable def branchFullSupportScale_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    FiniteBranchScaleFactorizationFullSupportAssumptions
      (branchAggregationStructure_of_faithfulAssumptions hfaith F hax hV) :=
  faithfulBranchFullSupportScale_of_components
    F hax hV hfaith.linear_part
    (branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV)
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.singleton_scale
    (branchBoundaryValueTransport_of_faithfulAssumptions hfaith)
    (branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith)

/-- Public branch-chain structure produced from faithful branch components. -/
noncomputable def branchChainStructure_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchChainStructure F :=
  BranchAggregationChainRule_of_faithful_components
    F hax hV hfaith.linear_part
    (branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV)
    (branchBoundaryFaceScale_of_faithfulAssumptions hfaith)
    hfaith.singleton_scale
    (branchBoundaryValueTransport_of_faithfulAssumptions hfaith)
    (branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith)
    (hfaith.boundary_scale_factorization F hax hV)
    (hfaith.singleton_scale_factorization F hax hV)

/-- Normalized chain rule exposed directly from faithful branch assumptions. -/
theorem normalizedChainRule_of_faithfulAssumptions
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : O → Channel A Y) :
    branchNormalizedValue
      (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
      q (P ▷ Q)
    =
    branchNormalizedValue
      (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
      q P
      + ∑ o : O,
          (Channel.outcomeMarginal P q) o *
          branchNormalizedValue
            (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
            (Channel.posterior P q o) (Q o) :=
  branchNormalizedValue_seqCompose_of_chain
    (branchChainStructure_of_faithfulAssumptions hfaith F hax hV)
    q hq P Q

/-!
## Faithful named result

The following package is the faithful Lean statement of the paper's named
result "Branch aggregation, cocycle, and normalised chain rule".  It exposes
the branch aggregation structure, the public full-support cocycle, the
full-support scale factorization, the boundary/singleton-extended scale
factorization, and the induced normalised chain rule.  It deliberately does not
use the old hax-free `FiniteBranchAggregationAssumptions` compatibility
monolith.
-/

/-- Faithful output package for branch aggregation, public cocycle,
scale factorization, and the normalised chain rule. -/
structure BranchAggregationCocycleNormalizedChainRuleStructure
    (F : PrefFamily.{u}) where
  branch_agg : BranchAggregationStructure F
  coeff_cocycle : FiniteBranchCoeffCocycleAssumptionsFor branch_agg
  full_support_scale :
    FiniteBranchScaleFactorizationFullSupportAssumptions branch_agg
  scale_factorization :
    FiniteBranchScaleFactorizationAssumptions branch_agg

namespace BranchAggregationCocycleNormalizedChainRuleStructure

/-- The branch-chain structure induced by the faithful named-result package. -/
noncomputable def chain
    {F : PrefFamily.{u}}
    (h : BranchAggregationCocycleNormalizedChainRuleStructure F) :
    BranchChainStructure F :=
  branchChainStructure_of_scaleFactorization h.branch_agg h.scale_factorization

/-- The normalised chain rule induced by the faithful named-result package. -/
theorem normalizedChainRule
    {F : PrefFamily.{u}}
    (h : BranchAggregationCocycleNormalizedChainRuleStructure F)
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
  branchNormalizedValue_seqCompose_of_chain h.chain q hq P Q

end BranchAggregationCocycleNormalizedChainRuleStructure

/-- Faithful theorem statement for the named result "Branch aggregation,
cocycle, and normalised chain rule".

All residual inputs are explicit in `FiniteFaithfulBranchAggregationAssumptions`:
finite tangent geometry, same-sign scalar linear algebra, support-face
representative normalization, boundary coefficient/scale transport, and
singleton normalizations. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_faithful
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F) :
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hpath :=
    branchPathTangentScalarStructure_of_faithfulAssumptions
      hfaith F hax hV
  let hboundary :=
    branchBoundaryFaceScale_of_faithfulAssumptions hfaith
  let hvalue :=
    branchBoundaryValueTransport_of_faithfulAssumptions hfaith
  let hcoeff :=
    branchBoundaryCoefficientTransport_of_faithfulAssumptions hfaith
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransport
      F hax hV hfaith.linear_part hpath hboundary hfaith.singleton_scale
      hvalue hcoeff
  let hbranch :=
    branchAggregationStructure_of_tangentFormulaFor
      F hax hV hfaith.linear_part hpath hboundary hfaith.singleton_scale
      hformula
  let hcocycle :=
    branchCoeffCocycleFor_of_tangentScalar
      F hax hV hfaith.linear_part hpath hboundary hfaith.singleton_scale
      hformula
  let hfull :=
    branchScaleFactorizationFullSupport_of_cocycle hbranch hcocycle
  {
    branch_agg := hbranch
    coeff_cocycle := hcocycle
    full_support_scale := hfull
    scale_factorization :=
      branchScaleFactorization_of_fullSupport_boundary_singleton
        hbranch hfull
        (hfaith.boundary_scale_factorization F hax hV)
        (hfaith.singleton_scale_factorization F hax hV)
  }

/-- Selected faithful theorem statement for branch aggregation, cocycle, and
normalised chain rule.

This is the same construction as `BranchAggregationCocycleNormalizedChainRule_of_faithful`,
but it consumes boundary value transport only for the representative `hV` being
assembled. -/
noncomputable def BranchAggregationCocycleNormalizedChainRule_of_componentsFor
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hsingle : FiniteBranchSingletonScaleNormalizationAssumptions.{u})
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
    BranchAggregationCocycleNormalizedChainRuleStructure F :=
  let hformula :=
    branchAggregationFormulaTangentFor_of_boundaryTransportFor
      F hax hV hlin hpath hboundary hsingle hvalue hcoeff
  let hbranch :=
    branchAggregationStructure_of_tangentFormulaFor
      F hax hV hlin hpath hboundary hsingle hformula
  let hcocycle :=
    branchCoeffCocycleFor_of_tangentScalar
      F hax hV hlin hpath hboundary hsingle hformula
  let hfull :=
    branchScaleFactorizationFullSupport_of_cocycle hbranch hcocycle
  {
    branch_agg := hbranch
    coeff_cocycle := hcocycle
    full_support_scale := hfull
    scale_factorization :=
      branchScaleFactorization_of_fullSupport_boundary_singleton
        hbranch hfull hboundaryScale hsingleScale
  }

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
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
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

/-!
## Interaction collapse and universal chain scale

The next named paper result starts from coherent face scales and proves two
things: the product interaction coefficient vanishes, and the prior-dependent
chain scale is actually universal.  This section gives a faithful pre-entropy
API for that result, split into the paper's product-revelation and two-grouping
subclaims rather than using the old all-in-one `FiniteScaleCoherenceAssumptions`
monolith.
-/

/-- Full-revelation value `H(q)` used in the scale-coherence proof, stated
against the faithful face-scale package. -/
noncomputable def fullRevelationValueForFaceScales
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  hfaces.branch_result.branch_agg.value_rep.V q
    (experimentOfChannel (Channel.idChannel : Channel A A))

/-- Coherent product quasi-additivity stated against the pre-universal
face-scale package.

This is the product formula from the earlier coherent-product result, but its
signature avoids requiring `ScaleCoherenceStructure` as an input. -/
structure FiniteProductQuasiAdditivityForFaceScales.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) where
  kappa : TraceAxioms F → ℝ
  product_quasi_add :
    ∀ (hax : TraceAxioms F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) +
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) +
        kappa hax *
          hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) *
          hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Face-scale-level first-coordinate slice affinity.

This is the pre-universal analogue of the Stage 10 left-slice affine package:
for fixed second-coordinate channel `R`, the product value is affine in the
first-coordinate value. -/
structure FiniteFaceScaleProductLeftSliceAffineAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) where
  leftSliceSlope :
    TraceAxioms F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftSliceIntercept :
    TraceAxioms F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  left_slice_affine :
    ∀ (hax : TraceAxioms F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftSliceSlope hax q r R *
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) +
        leftSliceIntercept hax q r R

/-- Face-scale-level intercept identification in the second-coordinate value.
-/
structure FiniteFaceScaleProductSliceInterceptAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) where
  rightCoeff :
    TraceAxioms F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff_pos :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff hax q r
  leftSliceIntercept_value :
    ∀ (hax : TraceAxioms F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      hslice.leftSliceIntercept hax q r R =
        rightCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R)

/-- Face-scale-level slope identification in the second-coordinate value. -/
structure FiniteFaceScaleProductSliceSlopeAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) where
  leftCoeff :
    TraceAxioms F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    TraceAxioms F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff hax q r
  leftSliceSlope_value :
    ∀ (hax : TraceAxioms F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A)
      (R : Channel B Y),
      hslice.leftSliceSlope hax q r R =
        leftCoeff hax q r +
          interactionCoeff hax q r *
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R)

/-- Product left-slice value in the pre-universal face-scale structure. -/
noncomputable def faceScaleProductLeftSliceValue
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B Y O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (R : Channel B Y) (P : Channel A O) : ℝ :=
  hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Face-scale product left-slice base-value public-mixture affinity. -/
structure FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  base_value_publicMix_affine :
    ∀ (_hax : TraceAxioms F)
      {A O Z : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
        t * hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P) +
        (1 - t) * hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel Q)

/-- Face-scale product left-slice public-mixture affinity in the first
coordinate. -/
structure FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  left_slice_publicMix_affine :
    ∀ (_hax : TraceAxioms F)
      {A B O Z Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      faceScaleProductLeftSliceValue hfaces q r R
          (publicMixChannel t ht0 ht1 P Q) =
        t * faceScaleProductLeftSliceValue hfaces q r R P +
        (1 - t) * faceScaleProductLeftSliceValue hfaces q r R Q

/-- Face-scale product left-slice order identification with the base
first-coordinate order. -/
structure FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  left_slice_same_order :
    ∀ (_hax : TraceAxioms F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y) (P Q : Channel A O),
      faceScaleProductLeftSliceValue hfaces q r R P ≥
          faceScaleProductLeftSliceValue hfaces q r R Q ↔
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) ≥
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel Q)

/-- Face-scale base-value nonconstancy for non-singleton full-support priors. -/
structure FiniteFaceScaleBaseValueNonconstancyAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  base_value_nonconstant :
    ∀ (_hax : TraceAxioms F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hA : ¬ Subsingleton A),
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))

/-- Singleton first-coordinate slice affine normalization.  This covers the
degenerate case where the first-coordinate value domain cannot identify a
positive slope from comparisons. -/
structure FiniteFaceScaleSingletonSliceAffineAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  singleton_left_slice_positive_affine_transform :
    ∀ (_hax : TraceAxioms F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : Subsingleton A) (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          faceScaleProductLeftSliceValue hfaces q r R P =
            a * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) + b

/-- Classical affine-utility uniqueness specialized to face-scale product
left slices. -/
structure ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  positive_affine_transform :
    ∀ (_hax : TraceAxioms F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (R : Channel B Y),
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
          t * hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) +
            (1 - t) * hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel Q)) →
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        faceScaleProductLeftSliceValue hfaces q r R
            (publicMixChannel t ht0 ht1 P Q) =
          t * faceScaleProductLeftSliceValue hfaces q r R P +
            (1 - t) * faceScaleProductLeftSliceValue hfaces q r R Q) →
      (hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))) →
      (∀ {O : Type v} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        faceScaleProductLeftSliceValue hfaces q r R P ≥
            faceScaleProductLeftSliceValue hfaces q r R Q ↔
          hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) ≥
            hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel Q)) →
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          faceScaleProductLeftSliceValue hfaces q r R P =
            a * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) + b

/-- The precise affine-transform output behind
`FiniteFaceScaleProductLeftSliceAffineAssumptionsFor`. -/
structure FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  left_slice_positive_affine_transform :
    ∀ (_hax : TraceAxioms F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          faceScaleProductLeftSliceValue hfaces q r R P =
            a * hfaces.branch_result.branch_agg.value_rep.V q
              (experimentOfChannel P) + b

/-- Reconstruct the face-scale affine-transform package from the product
mixture/order/nonconstancy pieces and the classical affine-utility theorem. -/
theorem faceScaleProductLeftSliceAffineTransform_of_parts
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hnonconst :
      FiniteFaceScaleBaseValueNonconstancyAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq :
      ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor hfaces) :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces where
  left_slice_positive_affine_transform := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    by_cases hsub : Subsingleton A
    · exact hsingle.singleton_left_slice_positive_affine_transform
        hax q r hq hr hsub R
    · exact
        huniq.positive_affine_transform hax q r hq hr hsub R
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact hbaseAff.base_value_publicMix_affine
              hax q hq t ht0 ht1 P Q)
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact hsliceAff.left_slice_publicMix_affine
              hax q r hq hr R t ht0 ht1 P Q)
          (hnonconst.base_value_nonconstant hax q hq hsub)
          (by
            intro O _ _ P Q
            exact hsameOrder.left_slice_same_order hax q r hq hr R P Q)

noncomputable def faceScaleAffineSliceTransformSlope
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (haff.left_slice_positive_affine_transform hax q r h.1 h.2 R)
    else 0

noncomputable def faceScaleAffineSliceTransformIntercept
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : TraceAxioms F)
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
          (haff.left_slice_positive_affine_transform hax q r h.1 h.2 R))
    else 0

/-- The chosen slice-transform slope is strictly positive at full-support
priors: it is the multiplier `a` of a positive affine transform.  This is the
Lean form of the paper's positive-slice-slope condition (Lemma coherentnorm,
`α(ν) > 0`), from which POS follows. -/
theorem faceScaleAffineSliceTransformSlope_pos
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    0 < faceScaleAffineSliceTransformSlope haff hax q r R := by
  classical
  have hcond : q.FullSupport ∧ r.FullSupport := ⟨hq, hr⟩
  have hpos :=
    (Classical.choose_spec
      (Classical.choose_spec
        (haff.left_slice_positive_affine_transform hax q r hq hr R))).1
  simpa [faceScaleAffineSliceTransformSlope, hcond] using hpos

/-- Reconstruct face-scale left-slice affinity from the exact
positive-affine-transform output. -/
noncomputable def faceScaleProductLeftSliceAffine_of_transform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces) :
    FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces where
  leftSliceSlope := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r R
    exact faceScaleAffineSliceTransformSlope haff hax q r R
  leftSliceIntercept := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r R
    exact faceScaleAffineSliceTransformIntercept haff hax q r R
  left_slice_affine := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    classical
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform
            hax q r hq hr R))).2 (P := P)
    simpa [faceScaleProductLeftSliceValue, faceScaleAffineSliceTransformSlope,
      faceScaleAffineSliceTransformIntercept, hq, hr] using hspec

/-- Face-scale second-coordinate intercept positive-linearity theorem. -/
structure FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_positive_linear :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceIntercept hax q r R =
            Bcoeff * hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R)

/-- Face-scale intercept same-order condition. -/
structure FiniteFaceScaleProductInterceptSameOrderAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_same_order :
    ∀ (hax : TraceAxioms F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R S : Channel B Y),
      hslice.leftSliceIntercept hax q r R ≥
          hslice.leftSliceIntercept hax q r S ↔
        hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) ≥
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel S)

/-- Face-scale intercept public-mixture affinity. -/
structure FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_publicMix_affine :
    ∀ (hax : TraceAxioms F)
      {A B Y Z : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      [Fintype Z] [DecidableEq Z]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (R : Channel B Y) (S : Channel B Z),
      hslice.leftSliceIntercept hax q r
          (publicMixChannel t ht0 ht1 R S) =
        t * hslice.leftSliceIntercept hax q r R +
        (1 - t) * hslice.leftSliceIntercept hax q r S

/-- The universe-polymorphic uninformative channel has zero value under the
chosen posterior-value representative. -/
theorem V_uninformativeChannelU_eq_zero
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
  hV.zero_normalized q hq

/-- If a channel has a subsingleton outcome type, its posterior law evaluates
as the prior itself. -/
theorem posteriorLawIntegralExp_subsingleton_outcome
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Nonempty O] [Subsingleton O]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (experimentOfChannel P) φ = φ q := by
  obtain ⟨o₀⟩ : Nonempty O := inferInstance
  have huniq : ∀ o : O, o = o₀ := fun o => Subsingleton.elim o o₀
  have hP_o₀ : ∀ a : A, (P a).prob o₀ = 1 := by
    intro a
    have hsum := (P a).sum_eq_one
    rw [show (∑ o : O, (P a).prob o) = (P a).prob o₀ from
      Finset.sum_eq_single o₀ (fun b _ hb => absurd (huniq b) hb)
        (fun h => absurd (Finset.mem_univ o₀) h)] at hsum
    exact hsum
  have hmarg : (Channel.outcomeMarginal P q).prob o₀ = 1 := by
    simp only [Channel.outcomeMarginal_apply, hP_o₀, mul_one]
    exact q.sum_eq_one
  have hmarg_pos : (0 : ℝ) < (Channel.outcomeMarginal P q).prob o₀ := by
    rw [hmarg]
    exact one_pos
  have hpost : Channel.posterior P q o₀ = q := by
    unfold Channel.posterior
    rw [dif_pos hmarg_pos]
    ext a
    simp only [Channel.outcomeMarginal_apply, hP_o₀, mul_one]
    simp [q.sum_eq_one]
  unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
  simp only [FiniteExperimentOn.outcomeMarginal, FiniteExperimentOn.posterior]
  rw [show (∑ o : O, (Channel.outcomeMarginal P q).prob o *
      φ (Channel.posterior P q o)) =
      (Channel.outcomeMarginal P q).prob o₀ *
        φ (Channel.posterior P q o₀) from
    Finset.sum_eq_single o₀ (fun b _ hb => absurd (huniq b) hb)
      (fun h => absurd (Finset.mem_univ o₀) h)]
  rw [hmarg, hpost, one_mul]

/-- A channel with a subsingleton outcome type has zero value under the
zero-normalised posterior-value representative. -/
theorem V_eq_zero_of_subsingleton_outcome
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Nonempty O] [Subsingleton O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    hV.V q (experimentOfChannel P) = 0 := by
  have hsameLaw : SamePosteriorLawExp q
      (experimentOfChannel P)
      (experimentOfChannel (Channel.uninformativeChannelU A)) := by
    intro φ _hcont
    rw [posteriorLawIntegralExp_subsingleton_outcome q P φ]
    have hU :
        posteriorLawIntegralExp q
          (experimentOfChannel (Channel.uninformativeChannelU A)) φ = φ q :=
      posteriorLawIntegralExp_subsingleton_outcome q
        (Channel.uninformativeChannelU A) φ
    rw [hU]
  rw [hV.respects_same_posterior_law q _ _ hsameLaw]
  exact hV.zero_normalized q hq

/-- Face-scale intercept zero-normalisation at the no-information channel. -/
structure FiniteFaceScaleProductInterceptZeroAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  intercept_uninformative_eq_zero :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hslice.leftSliceIntercept hax q r
        (Channel.uninformativeChannelU B) = 0

/-- The left-slice intercept is the product value at the first-coordinate
no-information channel. -/
theorem faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hslice.leftSliceIntercept hax q r R =
      faceScaleProductLeftSliceValue hfaces q r R
        (Channel.uninformativeChannelU A) := by
  have hslice_eq :=
    hslice.left_slice_affine hax q r hq hr
      (Channel.uninformativeChannelU A) R
  have hzero :
      hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  rw [hzero, mul_zero, zero_add] at hslice_eq
  exact hslice_eq.symm

/-- Intercept zero-normalisation follows internally from the slice-affine
identity and subsingleton-outcome zero-normalisation. -/
theorem faceScaleProductInterceptZero_of_sliceAffine
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptZeroAssumptionsFor hslice where
  intercept_uninformative_eq_zero := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr (Channel.uninformativeChannelU B)]
    exact V_eq_zero_of_subsingleton_outcome F
      hfaces.branch_result.branch_agg.value_rep
      (prodDist q r) (prodDist_fullSupport q r hq hr)
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B))

/-- Single source-ready finite affine-utility uniqueness theorem.

This is the generic classical statement used by both the first-coordinate
left-slice affine transform and the second-coordinate intercept normalization:
if two public-mixture affine real representatives on the same finite
experiment domain induce the same weak order and the base representative is
nonconstant, then the second representative is a positive affine transform of
the base. -/
structure ClassicalFiniteAffineUtilityUniquenessAssumptions.{v} : Prop where
  positive_affine_transform :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (base target :
        {O : Type v} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ),
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        base (publicMixChannel t ht0 ht1 P Q) =
          t * base P + (1 - t) * base Q) →
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        target (publicMixChannel t ht0 ht1 P Q) =
          t * target P + (1 - t) * target Q) →
      (base (Channel.idChannel : Channel A A) ≠
        base (Channel.uninformativeChannelU A)) →
      (∀ {O : Type v} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        target P ≥ target Q ↔ base P ≥ base Q) →
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O), target P = a * base P + b

private theorem affineUtility_value_eq_of_cross
    {bi bu ti tu x y : ℝ}
    (hden : bi - bu ≠ 0)
    (hcross : (bi - bu) * y + (bu - x) * ti + (x - bi) * tu = 0) :
    y = ((ti - tu) / (bi - bu)) * x +
      (tu - ((ti - tu) / (bi - bu)) * bu) := by
  field_simp [hden]
  nlinarith [hcross]

/-- Finite public-mixture affine utility uniqueness.

The proof uses only the hypotheses exposed in
`ClassicalFiniteAffineUtilityUniquenessAssumptions`: public-mixture affinity,
nonconstancy of the identity/no-information anchors, and same weak order on
each common outcome type.  Cross-outcome comparisons are obtained by embedding
any channel and the two anchors into a common three-arm public mixture. -/
theorem classicalFiniteAffineUtilityUniquenessAssumptions :
    ClassicalFiniteAffineUtilityUniquenessAssumptions.{u} where
  positive_affine_transform := by
    intro A _ _ _ base target hbaseAff htargetAff hnonconst horder
    classical
    let I : Channel A A := Channel.idChannel
    let U : Channel A PUnit.{u+1} := Channel.uninformativeChannelU A
    let bi : ℝ := base I
    let bu : ℝ := base U
    let ti : ℝ := target I
    let tu : ℝ := target U
    let Δ : ℝ := bi - bu
    have hΔ_ne : Δ ≠ 0 := by
      dsimp [Δ, bi, bu, I, U]
      exact sub_ne_zero.mpr hnonconst
    have two_thirds_pos : (0 : ℝ) < (2 / 3 : ℝ) := by norm_num
    have two_thirds_lt_one : (2 / 3 : ℝ) < 1 := by norm_num
    have one_third_pos : (0 : ℝ) < (1 / 3 : ℝ) := by norm_num
    have one_third_lt_one : (1 / 3 : ℝ) < 1 := by norm_num
    let Mhi : Channel A (A ⊕ PUnit.{u+1}) :=
      publicMixChannel (2 / 3 : ℝ) two_thirds_pos two_thirds_lt_one I U
    let Mlo : Channel A (A ⊕ PUnit.{u+1}) :=
      publicMixChannel (1 / 3 : ℝ) one_third_pos one_third_lt_one I U
    have hbase_hi :
        base Mhi = (2 / 3 : ℝ) * bi + (1 / 3 : ℝ) * bu := by
      change base (publicMixChannel (2 / 3 : ℝ)
          two_thirds_pos two_thirds_lt_one I U) =
        (2 / 3 : ℝ) * bi + (1 / 3 : ℝ) * bu
      rw [hbaseAff (O := A) (Z := PUnit.{u+1})
        (2 / 3 : ℝ) two_thirds_pos two_thirds_lt_one I U]
      dsimp [bi, bu]
      norm_num
    have hbase_lo :
        base Mlo = (1 / 3 : ℝ) * bi + (2 / 3 : ℝ) * bu := by
      change base (publicMixChannel (1 / 3 : ℝ)
          one_third_pos one_third_lt_one I U) =
        (1 / 3 : ℝ) * bi + (2 / 3 : ℝ) * bu
      rw [hbaseAff (O := A) (Z := PUnit.{u+1})
        (1 / 3 : ℝ) one_third_pos one_third_lt_one I U]
      dsimp [bi, bu]
      norm_num
    have htarget_hi :
        target Mhi = (2 / 3 : ℝ) * ti + (1 / 3 : ℝ) * tu := by
      change target (publicMixChannel (2 / 3 : ℝ)
          two_thirds_pos two_thirds_lt_one I U) =
        (2 / 3 : ℝ) * ti + (1 / 3 : ℝ) * tu
      rw [htargetAff (O := A) (Z := PUnit.{u+1})
        (2 / 3 : ℝ) two_thirds_pos two_thirds_lt_one I U]
      dsimp [ti, tu]
      norm_num
    have htarget_lo :
        target Mlo = (1 / 3 : ℝ) * ti + (2 / 3 : ℝ) * tu := by
      change target (publicMixChannel (1 / 3 : ℝ)
          one_third_pos one_third_lt_one I U) =
        (1 / 3 : ℝ) * ti + (2 / 3 : ℝ) * tu
      rw [htargetAff (O := A) (Z := PUnit.{u+1})
        (1 / 3 : ℝ) one_third_pos one_third_lt_one I U]
      dsimp [ti, tu]
      norm_num
    have hslope_pos : 0 < (ti - tu) / (bi - bu) := by
      rcases lt_or_gt_of_ne hΔ_ne with hΔ_neg | hΔ_pos
      · have hb_lt : base Mhi < base Mlo := by
          rw [hbase_hi, hbase_lo]
          dsimp [Δ, bi, bu] at hΔ_neg
          nlinarith
        have ht_not_ge : ¬ target Mhi ≥ target Mlo := by
          intro hge
          have hbase_ge : base Mhi ≥ base Mlo :=
            (horder Mhi Mlo).1 hge
          linarith
        have ht_lt : target Mhi < target Mlo := not_le.mp ht_not_ge
        have hti_lt : ti < tu := by
          rw [htarget_hi, htarget_lo] at ht_lt
          nlinarith
        have hnum_pos : 0 < -(ti - tu) := by linarith
        have hden_pos : 0 < -(bi - bu) := by
          dsimp [Δ, bi, bu] at hΔ_neg
          linarith
        exact div_pos_of_neg_of_neg (by linarith) (by linarith)
      · have hb_gt : base Mhi > base Mlo := by
          rw [hbase_hi, hbase_lo]
          dsimp [Δ, bi, bu] at hΔ_pos
          nlinarith
        have ht_not_ge : ¬ target Mlo ≥ target Mhi := by
          intro hge
          have hbase_ge : base Mlo ≥ base Mhi :=
            (horder Mlo Mhi).1 hge
          linarith
        have ht_gt : target Mhi > target Mlo := not_le.mp ht_not_ge
        have hti_gt : ti > tu := by
          rw [htarget_hi, htarget_lo] at ht_gt
          nlinarith
        exact div_pos (by linarith) (by
          dsimp [Δ, bi, bu] at hΔ_pos
          exact hΔ_pos)
    refine ⟨(ti - tu) / (bi - bu),
      tu - ((ti - tu) / (bi - bu)) * bu, hslope_pos, ?_⟩
    intro O _ _ P
    let x : ℝ := base P
    let y : ℝ := target P
    let cP : ℝ := bi - bu
    let cI : ℝ := bu - x
    let cU : ℝ := x - bi
    let K : ℝ := |cP| + |cI| + |cU| + 1
    let S : ℝ := 3 * K
    have hc_sum : cP + cI + cU = 0 := by
      dsimp [cP, cI, cU]
      ring
    have hK_pos : 0 < K := by
      have hnonneg : 0 ≤ |cP| + |cI| + |cU| := by positivity
      dsimp [K]
      linarith
    have hS_pos : 0 < S := by
      dsimp [S]
      positivity
    have hKcP_pos : 0 < K + cP := by
      have hlt : -cP < K := by
        dsimp [K]
        linarith [neg_le_abs cP, abs_nonneg cI, abs_nonneg cU]
      linarith
    have hKcI_pos : 0 < K + cI := by
      have hlt : -cI < K := by
        dsimp [K]
        linarith [neg_le_abs cI, abs_nonneg cP, abs_nonneg cU]
      linarith
    have hKcU_pos : 0 < K + cU := by
      have hlt : -cU < K := by
        dsimp [K]
        linarith [neg_le_abs cU, abs_nonneg cP, abs_nonneg cI]
      linarith
    let α : ℝ := (K + cP) / S
    let β : ℝ := (K + cI) / S
    let γ : ℝ := (K + cU) / S
    let α₀ : ℝ := K / S
    let β₀ : ℝ := K / S
    let γ₀ : ℝ := K / S
    have hα_pos : 0 < α := by
      dsimp [α]
      exact div_pos hKcP_pos hS_pos
    have hβ_pos : 0 < β := by
      dsimp [β]
      exact div_pos hKcI_pos hS_pos
    have hγ_pos : 0 < γ := by
      dsimp [γ]
      exact div_pos hKcU_pos hS_pos
    have hα₀_pos : 0 < α₀ := by
      dsimp [α₀]
      exact div_pos hK_pos hS_pos
    have hβ₀_pos : 0 < β₀ := by
      dsimp [β₀]
      exact div_pos hK_pos hS_pos
    have hγ₀_pos : 0 < γ₀ := by
      dsimp [γ₀]
      exact div_pos hK_pos hS_pos
    have hsum : α + β + γ = 1 := by
      dsimp [α, β, γ, S]
      field_simp [ne_of_gt hK_pos]
      nlinarith [hc_sum]
    have hsum₀ : α₀ + β₀ + γ₀ = 1 := by
      dsimp [α₀, β₀, γ₀, S]
      field_simp [ne_of_gt hK_pos]
      ring
    have three_base :
        ∀ {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
          (hsum : α + β + γ = 1),
          base
            (publicMixChannel α hα (by linarith)
              P
              (publicMixChannel (β / (β + γ))
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  exact div_pos hβ hden_pos)
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  have hlt : β < β + γ := by linarith
                  exact (div_lt_one hden_pos).2 hlt)
                I U)) =
            α * x + β * bi + γ * bu := by
      intro α β γ hα hβ hγ hsum
      have hα_lt : α < 1 := by linarith
      have hden_pos : 0 < β + γ := by positivity
      have hden_ne : β + γ ≠ 0 := ne_of_gt hden_pos
      have hone_sub : 1 - α = β + γ := by linarith
      rw [hbaseAff α hα hα_lt]
      rw [hbaseAff (β / (β + γ))
        (by exact div_pos hβ hden_pos)
        (by
          have hlt : β < β + γ := by linarith
          exact (div_lt_one hden_pos).2 hlt)]
      dsimp [x, bi, bu, I, U]
      rw [hone_sub]
      have hcoefβ : (β + γ) * (β / (β + γ)) = β := by
        field_simp [hden_ne]
      have hcoefγ : (β + γ) * (1 - β / (β + γ)) = γ := by
        field_simp [hden_ne]
        ring
      calc
        α * base P +
            (β + γ) *
              (β / (β + γ) * base Channel.idChannel +
                (1 - β / (β + γ)) * base (Channel.uninformativeChannelU A)) =
            α * base P +
              ((β + γ) * (β / (β + γ))) * base Channel.idChannel +
              ((β + γ) * (1 - β / (β + γ))) *
                base (Channel.uninformativeChannelU A) := by
          ring
        _ = α * base P + β * base Channel.idChannel +
              γ * base (Channel.uninformativeChannelU A) := by
          rw [hcoefβ, hcoefγ]
    have three_target :
        ∀ {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
          (hsum : α + β + γ = 1),
          target
            (publicMixChannel α hα (by linarith)
              P
              (publicMixChannel (β / (β + γ))
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  exact div_pos hβ hden_pos)
                (by
                  have hden_pos : 0 < β + γ := by linarith
                  have hlt : β < β + γ := by linarith
                  exact (div_lt_one hden_pos).2 hlt)
                I U)) =
            α * y + β * ti + γ * tu := by
      intro α β γ hα hβ hγ hsum
      have hα_lt : α < 1 := by linarith
      have hden_pos : 0 < β + γ := by positivity
      have hden_ne : β + γ ≠ 0 := ne_of_gt hden_pos
      have hone_sub : 1 - α = β + γ := by linarith
      rw [htargetAff α hα hα_lt]
      rw [htargetAff (β / (β + γ))
        (by exact div_pos hβ hden_pos)
        (by
          have hlt : β < β + γ := by linarith
          exact (div_lt_one hden_pos).2 hlt)]
      dsimp [y, ti, tu, I, U]
      rw [hone_sub]
      have hcoefβ : (β + γ) * (β / (β + γ)) = β := by
        field_simp [hden_ne]
      have hcoefγ : (β + γ) * (1 - β / (β + γ)) = γ := by
        field_simp [hden_ne]
        ring
      calc
        α * target P +
            (β + γ) *
              (β / (β + γ) * target Channel.idChannel +
                (1 - β / (β + γ)) * target (Channel.uninformativeChannelU A)) =
            α * target P +
              ((β + γ) * (β / (β + γ))) * target Channel.idChannel +
              ((β + γ) * (1 - β / (β + γ))) *
                target (Channel.uninformativeChannelU A) := by
          ring
        _ = α * target P + β * target Channel.idChannel +
              γ * target (Channel.uninformativeChannelU A) := by
          rw [hcoefβ, hcoefγ]
    have hbase_weight :
        α * x + β * bi + γ * bu =
          α₀ * x + β₀ * bi + γ₀ * bu := by
      dsimp [α, β, γ, α₀, β₀, γ₀, S]
      field_simp [ne_of_gt hK_pos]
      dsimp [cP, cI, cU]
      ring
    let T₁ : Channel A (O ⊕ (A ⊕ PUnit.{u+1})) :=
      publicMixChannel α hα_pos (by linarith)
        P
        (publicMixChannel (β / (β + γ))
          (by
            have hden_pos : 0 < β + γ := by linarith
            exact div_pos hβ_pos hden_pos)
          (by
            have hden_pos : 0 < β + γ := by linarith
            have hlt : β < β + γ := by linarith
            exact (div_lt_one hden_pos).2 hlt)
          I U)
    let T₀ : Channel A (O ⊕ (A ⊕ PUnit.{u+1})) :=
      publicMixChannel α₀ hα₀_pos (by linarith)
        P
        (publicMixChannel (β₀ / (β₀ + γ₀))
          (by
            have hden_pos : 0 < β₀ + γ₀ := by linarith
            exact div_pos hβ₀_pos hden_pos)
          (by
            have hden_pos : 0 < β₀ + γ₀ := by linarith
            have hlt : β₀ < β₀ + γ₀ := by linarith
            exact (div_lt_one hden_pos).2 hlt)
          I U)
    have hbase_T₁ : base T₁ = α * x + β * bi + γ * bu := by
      simpa [T₁] using three_base hα_pos hβ_pos hγ_pos hsum
    have hbase_T₀ : base T₀ = α₀ * x + β₀ * bi + γ₀ * bu := by
      simpa [T₀] using three_base hα₀_pos hβ₀_pos hγ₀_pos hsum₀
    have htarget_T₁ : target T₁ = α * y + β * ti + γ * tu := by
      simpa [T₁] using three_target hα_pos hβ_pos hγ_pos hsum
    have htarget_T₀ : target T₀ = α₀ * y + β₀ * ti + γ₀ * tu := by
      simpa [T₀] using three_target hα₀_pos hβ₀_pos hγ₀_pos hsum₀
    have hbase_T_eq : base T₁ = base T₀ := by
      rw [hbase_T₁, hbase_T₀]
      exact hbase_weight
    have htarget_T_eq : target T₁ = target T₀ := by
      apply le_antisymm
      · exact (horder T₀ T₁).2 (by rw [hbase_T_eq])
      · exact (horder T₁ T₀).2 (by rw [hbase_T_eq])
    have htarget_weight :
        α * y + β * ti + γ * tu =
          α₀ * y + β₀ * ti + γ₀ * tu := by
      rw [← htarget_T₁, ← htarget_T₀]
      exact htarget_T_eq
    have hlinear : cP * y + cI * ti + cU * tu = 0 := by
      have hscaled :
          (K + cP) * y + (K + cI) * ti + (K + cU) * tu =
            K * y + K * ti + K * tu := by
        have hmul := congrArg (fun z : ℝ => S * z) htarget_weight
        dsimp [α, β, γ, α₀, β₀, γ₀] at hmul
        field_simp [ne_of_gt hS_pos] at hmul
        calc
          (K + cP) * y + (K + cI) * ti + (K + cU) * tu =
              K * (y + ti + tu) := hmul
          _ = K * y + K * ti + K * tu := by ring
      calc
        cP * y + cI * ti + cU * tu =
            ((K + cP) * y + (K + cI) * ti + (K + cU) * tu) -
              (K * y + K * ti + K * tu) := by
          ring
        _ = 0 := by rw [hscaled]; ring
    have hcross :
        (bi - bu) * y + (bu - x) * ti + (x - bi) * tu = 0 := by
      simpa [cP, cI, cU] using hlinear
    have hden : bi - bu ≠ 0 := by
      dsimp [bi, bu, I, U]
      exact sub_ne_zero.mpr hnonconst
    have hy_eq :
        y = ((ti - tu) / (bi - bu)) * x +
          (tu - ((ti - tu) / (bi - bu)) * bu) := by
      exact affineUtility_value_eq_of_cross hden hcross
    simpa [x, y, bi, bu, ti, tu] using hy_eq

/-- The face-scale first-coordinate affine-utility uniqueness package is an
instance of the single classical finite affine-utility uniqueness theorem. -/
theorem classicalFaceScaleAffineUtilityUniqueness_of_finiteAffineUtility
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor hfaces where
  positive_affine_transform := by
    intro _hax A B Y _ _ _ _ _ _ _ _ q r _hq _hr _hA R
      hbaseAff htargetAff hnonconst horder
    let base :
        {O : Type u} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ :=
      fun {O} [Fintype O] [DecidableEq O] P =>
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel P)
    let target :
        {O : Type u} → [Fintype O] → [DecidableEq O] →
          Channel A O → ℝ :=
      fun {O} [Fintype O] [DecidableEq O] P =>
        faceScaleProductLeftSliceValue hfaces q r R P
    exact
      huniq.positive_affine_transform base target
        (by
          intro O Z _ _ _ _ t ht0 ht1 P Q
          exact hbaseAff t ht0 ht1 P Q)
        (by
          intro O Z _ _ _ _ t ht0 ht1 P Q
          exact htargetAff t ht0 ht1 P Q)
        hnonconst
        (by
          intro O _ _ P Q
          exact horder P Q)

/-- Classical second-coordinate affine uniqueness for the face-scale intercept
functional. -/
structure ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  positive_linear_of_same_order_affine_zero :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      (∀ {Y Z : Type v} [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (R : Channel B Y) (S : Channel B Z),
        hslice.leftSliceIntercept hax q r
            (publicMixChannel t ht0 ht1 R S) =
          t * hslice.leftSliceIntercept hax q r R +
          (1 - t) * hslice.leftSliceIntercept hax q r S) →
      (∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
        (R S : Channel B Y),
        hslice.leftSliceIntercept hax q r R ≥
            hslice.leftSliceIntercept hax q r S ↔
          hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) ≥
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel S)) →
      hslice.leftSliceIntercept hax q r
        (Channel.uninformativeChannelU B) = 0 →
      ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceIntercept hax q r R =
            Bcoeff * hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R)

/-- Reconstruct intercept positive-linearity from same-order, affinity,
zero-normalisation, and classical affine uniqueness. -/
theorem faceScaleProductInterceptPositiveLinear_of_parts
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (horder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor hslice)
    (haff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice)
    (hzero :
      FiniteFaceScaleProductInterceptZeroAssumptionsFor hslice)
    (huniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor hslice) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice where
  intercept_positive_linear := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact huniq.positive_linear_of_same_order_affine_zero
      hax q r hq hr
      (by
        intro Y Z _ _ _ _ t ht0 ht1 R S
        exact haff.intercept_publicMix_affine
          hax q r hq hr t ht0 ht1 R S)
      (by
        intro Y _ _ R S
        exact horder.intercept_same_order hax q r hq hr R S)
      (hzero.intercept_uninformative_eq_zero hax q r hq hr)

/-- Reconstruct intercept positive-linearity without an external intercept-zero
assumption.  The zero-normalisation is internal from `hslice`. -/
theorem faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (horder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor hslice)
    (haff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice)
    (huniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor hslice) :
    FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice :=
  faceScaleProductInterceptPositiveLinear_of_parts
    horder haff (faceScaleProductInterceptZero_of_sliceAffine hslice) huniq

noncomputable def faceScaleInterceptRightCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hlin :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose (hlin.intercept_positive_linear hax q r h.1 h.2)
    else 1

/-- Reconstruct the face-scale intercept package from the exact
positive-linearity output. -/
noncomputable def faceScaleProductSliceIntercept_of_positiveLinear
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hlin :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice) :
    FiniteFaceScaleProductSliceInterceptAssumptionsFor hslice where
  rightCoeff := by
    intro hax A B _ _ _ _ _ _ q r
    exact faceScaleInterceptRightCoeff hlin hax q r
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    classical
    have hpos :=
      (Classical.choose_spec
        (hlin.intercept_positive_linear hax q r hq hr)).1
    simpa [faceScaleInterceptRightCoeff, hq, hr] using hpos
  leftSliceIntercept_value := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hspec :=
      (Classical.choose_spec
        (hlin.intercept_positive_linear hax q r hq hr)).2 (R := R)
    simpa [faceScaleInterceptRightCoeff, hq, hr] using hspec

/-- Exact face-scale slope-affine output behind the slice-slope package. -/
structure FiniteFaceScaleProductSlopeAffineAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    Prop where
  slope_affine_in_second_value :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A),
      ∃ Acoeff Ccoeff : ℝ, 0 < Acoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceSlope hax q r R =
            Acoeff +
              Ccoeff * hfaces.branch_result.branch_agg.value_rep.V r
                (experimentOfChannel R)

noncomputable def faceScaleSlopeLeftCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (haff : FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A then
      Classical.choose
        (haff.slope_affine_in_second_value hax q r h.1 h.2.1 h.2.2)
    else 1

noncomputable def faceScaleSlopeInteractionCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (haff : FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A then
      Classical.choose
        (Classical.choose_spec
          (haff.slope_affine_in_second_value hax q r h.1 h.2.1 h.2.2))
    else 0

/-- Reconstruct the face-scale slice-slope package from the exact
slope-affine output. -/
noncomputable def faceScaleProductSliceSlope_of_slopeAffine
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (haff : FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice) :
    FiniteFaceScaleProductSliceSlopeAssumptionsFor hslice where
  leftCoeff := by
    intro hax A B _ _ _ _ _ _ q r
    exact faceScaleSlopeLeftCoeff haff hax q r
  interactionCoeff := by
    intro hax A B _ _ _ _ _ _ q r
    exact faceScaleSlopeInteractionCoeff haff hax q r
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    classical
    by_cases hA : Subsingleton A
    · -- degenerate first coordinate: the calibrated coefficient defaults to 1
      have hne : ¬ (q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A) := by
        rintro ⟨_, _, hnotA⟩; exact hnotA hA
      simp only [faceScaleSlopeLeftCoeff, dif_neg hne]
      exact one_pos
    · have hpos :=
        (Classical.choose_spec
          (Classical.choose_spec
            (haff.slope_affine_in_second_value hax q r hq hr hA))).1
      have hcond : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A :=
        ⟨hq, hr, hA⟩
      simpa [faceScaleSlopeLeftCoeff, hcond] using hpos
  leftSliceSlope_value := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr hA R
    classical
    have hcond : q.FullSupport ∧ r.FullSupport ∧ ¬ Subsingleton A :=
      ⟨hq, hr, hA⟩
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.slope_affine_in_second_value hax q r hq hr hA))).2 (R := R)
    simpa [faceScaleSlopeLeftCoeff, faceScaleSlopeInteractionCoeff, hcond]
      using hspec

/-- Face-scale-level pairwise product bilinear form.

This is the non-circular analogue of the old
`FinitePairwiseProductBilinearAssumptions`: it is stated against the
pre-universal `CoherentRelabelingFaceScalesStructure`, not against the
`ScaleCoherenceStructure` that the interaction-collapse theorem is trying to
construct. -/
structure FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) where
  leftCoeff :
    TraceAxioms F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff :
    TraceAxioms F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    TraceAxioms F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff hax q r
  rightCoeff_pos :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff hax q r
  product_pair_bilinear :
    ∀ (hax : TraceAxioms F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) +
        rightCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) +
        interactionCoeff hax q r *
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) *
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R)

/-- Left linear product coefficient after applying a coherent positive
prior-gauge transform to the selected face-scale representatives. -/
noncomputable def faceScaleGaugeTransformedLeftCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u})
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.leftCoeff hax q r *
    (hgauge.gauge (prodDist q r) / hgauge.gauge q)

/-- Right linear product coefficient after applying a coherent positive
prior-gauge transform to the selected face-scale representatives. -/
noncomputable def faceScaleGaugeTransformedRightCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u})
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.rightCoeff hax q r *
    (hgauge.gauge (prodDist q r) / hgauge.gauge r)

/-- Interaction product coefficient after applying a coherent positive
prior-gauge transform to the selected face-scale representatives. -/
noncomputable def faceScaleGaugeTransformedInteractionCoeff
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u})
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.interactionCoeff hax q r *
    (hgauge.gauge (prodDist q r) /
      (hgauge.gauge q * hgauge.gauge r))

/-- Pairwise product bilinearity is transported by coherent positive
prior-gauge rescaling, with the usual coefficient transformation laws from
Lemma `coherentnorm`. -/
noncomputable def faceScaleProductPairwiseBilinearity_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor
      (hfaces.gaugeTransform hgauge) where
  leftCoeff := fun hax {A B} _ _ _ _ _ _ q r =>
    faceScaleGaugeTransformedLeftCoeff hpair hgauge hax q r
  rightCoeff := fun hax {A B} _ _ _ _ _ _ q r =>
    faceScaleGaugeTransformedRightCoeff hpair hgauge hax q r
  interactionCoeff := fun hax {A B} _ _ _ _ _ _ q r =>
    faceScaleGaugeTransformedInteractionCoeff hpair hgauge hax q r
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact mul_pos (hpair.leftCoeff_pos hax q r hq hr)
      (div_pos (hgauge.gauge_pos (prodDist q r)) (hgauge.gauge_pos q))
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact mul_pos (hpair.rightCoeff_pos hax q r hq hr)
      (div_pos (hgauge.gauge_pos (prodDist q r)) (hgauge.gauge_pos r))
  product_pair_bilinear := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    dsimp [CoherentRelabelingFaceScalesStructure.gaugeTransform,
      branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      branchAggregationStructure_gaugeTransform,
      posteriorValueRepresentation_gaugeTransform,
      faceScaleGaugeTransformedLeftCoeff,
      faceScaleGaugeTransformedRightCoeff,
      faceScaleGaugeTransformedInteractionCoeff]
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    have hgq_ne : hgauge.gauge q ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos q)
    have hgr_ne : hgauge.gauge r ≠ 0 :=
      ne_of_gt (hgauge.gauge_pos r)
    field_simp [hgq_ne, hgr_ne]

/-- Explicit product-gauge transform data for a raw pairwise face-scale
bilinear package.  This records the positive coherent gauge selected in the
paper's product-normalisation step and the two transformed linear coefficient
normalisations. -/
structure FiniteFaceScaleProductGaugeTransformFor
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    where
  gauge : CoherentFaceScaleGauge.{u}
  transformed_leftCoeff_normalized :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      faceScaleGaugeTransformedLeftCoeff hpair gauge hax q r = 1
  transformed_rightCoeff_normalized :
    ∀ (hax : TraceAxioms F)
      {A B : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      faceScaleGaugeTransformedRightCoeff hpair gauge hax q r = 1

/-- Reconstruct face-scale pairwise product bilinearity from the same Step 2
slice-affine pieces used by the old Stage 10 coherent-product route. -/
def faceScaleProductPairwiseBilinearity_of_sliceAffine
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductSliceInterceptAssumptionsFor hslice)
    (hslope : FiniteFaceScaleProductSliceSlopeAssumptionsFor hslice) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces where
  leftCoeff := hslope.leftCoeff
  rightCoeff := hintercept.rightCoeff
  interactionCoeff := hslope.interactionCoeff
  leftCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hslope.leftCoeff_pos hax q r hq hr
  rightCoeff_pos := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hintercept.rightCoeff_pos hax q r hq hr
  product_pair_bilinear := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    classical
    by_cases hA : Subsingleton A
    · -- degenerate first coordinate: V_q(P) = 0, so both slope terms vanish
      haveI : Subsingleton A := hA
      have hVq :
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep q hq P
      rw [hslice.left_slice_affine hax q r hq hr P R]
      rw [hintercept.leftSliceIntercept_value hax q r hq hr R]
      rw [hVq]
      ring
    · rw [hslice.left_slice_affine hax q r hq hr P R]
      rw [hslope.leftSliceSlope_value hax q r hq hr hA R]
      rw [hintercept.leftSliceIntercept_value hax q r hq hr R]
      ring

/-- Face-scale-level Step 3 gauge normalization of product linear
coefficients. -/
structure FiniteFaceScaleProductGaugeNormalizationAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  leftCoeff_normalized :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff hax q r = 1
  rightCoeff_normalized :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff hax q r = 1

/-- Explicit current-representative product gauge normalization.

The paper chooses positive rescalings of the zero-normalised representatives
before stating coherent product quasi-additivity.  At this point of the Lean
development the representatives in `hfaces` are fixed, so this normalization says
they are already in the product gauge where the two linear coefficients are
normalised to one. -/
structure FiniteFaceScaleCurrentProductGaugeNormalizationFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  current_leftCoeff_normalized :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff hax q r = 1
  current_rightCoeff_normalized :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff hax q r = 1

/-- Reconstruct the gauge-normalization package from the explicit
current-representative gauge normalization. -/
theorem faceScaleProductGaugeNormalization_of_currentGauge
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair) :
    FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair where
  leftCoeff_normalized := hgauge.current_leftCoeff_normalized
  rightCoeff_normalized := hgauge.current_rightCoeff_normalized

/-- After applying the selected product gauge, the transformed representatives
are in the current product gauge by construction. -/
theorem faceScaleCurrentProductGaugeNormalization_of_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair) :
    FiniteFaceScaleCurrentProductGaugeNormalizationFor
      (faceScaleProductPairwiseBilinearity_gaugeTransform
        hpair hgauge.gauge) where
  current_leftCoeff_normalized := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hgauge.transformed_leftCoeff_normalized hax q r hq hr
  current_rightCoeff_normalized := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    exact hgauge.transformed_rightCoeff_normalized hax q r hq hr

/-- Normalized face-scale product bilinear form.  Once the current
representatives are in the product gauge, the two linear product coefficients
are both one and the only pair-dependent term is the interaction coefficient. -/
theorem faceScaleProductPairBilinear_normalized
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
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
  rw [hnorm.leftCoeff_normalized hax q r hq hr]
  rw [hnorm.rightCoeff_normalized hax q r hq hr]
  ring

/-- A1 nontriviality makes full revelation nonzero in the current face-scale
value representative.  This early helper is used by the normalized
triple-product coefficient algebra below. -/
theorem faceScale_idChannel_value_ne_zero_of_A1
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
  have hne :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) :=
    branch_value_ne_of_strict_experiment_pref
      F hfaces.branch_result.branch_agg.value_rep q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      hstrict.1 hstrict.2
  have hzero :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  intro hid
  exact hne (by rw [hid, hzero])

/-- Face-scale-level Steps 4--5 interaction universality: after gauge
normalization, the bilinear interaction coefficient is a common `kappa`
independent of the two product factors. -/
structure FiniteFaceScaleProductInteractionUniversalityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) where
  kappa : TraceAxioms F → ℝ
  interactionCoeff_common :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.interactionCoeff hax q r = kappa hax

/-- Fixed nondegenerate reference type for the face-scale common-κ extraction. -/
abbrev faceScaleInteractionReferenceType : Type u := ULift.{u, 0} Bool

/-- Fixed full-support reference prior for the face-scale common-κ extraction. -/
noncomputable def faceScaleInteractionReferencePrior :
    Dist faceScaleInteractionReferenceType :=
  Dist.uniform

theorem faceScaleInteractionReferencePrior_fullSupport :
    faceScaleInteractionReferencePrior.FullSupport :=
  Dist.uniform_fullSupport (A := faceScaleInteractionReferenceType)

theorem faceScaleInteractionReference_not_subsingleton :
    ¬ Subsingleton faceScaleInteractionReferenceType := by
  intro hsub
  have htf : (true : Bool) = false := by
    exact congrArg ULift.down
      (Subsingleton.elim
        (ULift.up true : faceScaleInteractionReferenceType)
        (ULift.up false : faceScaleInteractionReferenceType))
  cases htf

/-- The reference interaction coefficient used to name common `kappa`. -/
noncomputable def faceScaleInteractionReferenceKappa
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : TraceAxioms F) : ℝ :=
  hpair.interactionCoeff hax
    faceScaleInteractionReferencePrior faceScaleInteractionReferencePrior

/-- Face-scale-level K1--K3 interaction associativity equations.  These are
the exact source-ready coefficient equations needed to identify a common
interaction coefficient. -/
structure FiniteFaceScaleProductInteractionAssociativityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  interaction_assoc_xy :
    ∀ (hax : TraceAxioms F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax q r =
        hpair.interactionCoeff hax q (prodDist r s)
  interaction_assoc_xz :
    ∀ (hax : TraceAxioms F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax q (prodDist r s)
  interaction_assoc_yz :
    ∀ (hax : TraceAxioms F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax r s

/-- Singleton interaction coefficient normalization for face-scale product
bilinearity.  Singleton coordinate values vanish, so the interaction
coefficient is not value-identified in singleton factors. -/
structure FiniteFaceScaleSingletonInteractionNormalizationFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces) :
    Prop where
  interactionCoeff_eq_reference_of_subsingleton_left :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton A →
      hpair.interactionCoeff hax q r =
        faceScaleInteractionReferenceKappa hpair hax
  interactionCoeff_eq_reference_of_subsingleton_right :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton B →
      hpair.interactionCoeff hax q r =
        faceScaleInteractionReferenceKappa hpair hax

/-- Nondegenerate common-κ extraction from K1--K3. -/
theorem faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.interactionCoeff hax q r =
      faceScaleInteractionReferenceKappa hpair hax := by
  let q₀ : Dist faceScaleInteractionReferenceType :=
    faceScaleInteractionReferencePrior
  have hq₀ : q₀.FullSupport :=
    faceScaleInteractionReferencePrior_fullSupport
  have hRef : ¬ Subsingleton faceScaleInteractionReferenceType :=
    faceScaleInteractionReference_not_subsingleton
  have h_qr_to_r_ref :
      hpair.interactionCoeff hax q r =
        hpair.interactionCoeff hax r q₀ := by
    calc
      hpair.interactionCoeff hax q r
          = hpair.interactionCoeff hax q (prodDist r q₀) :=
            hassoc.interaction_assoc_xy hax q r q₀ hq hr hq₀ hA hB hRef
      _ = hpair.interactionCoeff hax (prodDist q r) q₀ :=
            (hassoc.interaction_assoc_xz hax q r q₀ hq hr hq₀ hA hB hRef).symm
      _ = hpair.interactionCoeff hax r q₀ :=
            hassoc.interaction_assoc_yz hax q r q₀ hq hr hq₀ hA hB hRef
  have h_r_ref_to_ref_ref :
      hpair.interactionCoeff hax r q₀ =
        hpair.interactionCoeff hax q₀ q₀ := by
    calc
      hpair.interactionCoeff hax r q₀
          = hpair.interactionCoeff hax r (prodDist q₀ q₀) :=
            hassoc.interaction_assoc_xy hax r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
      _ = hpair.interactionCoeff hax (prodDist r q₀) q₀ :=
            (hassoc.interaction_assoc_xz hax r q₀ q₀ hr hq₀ hq₀ hB hRef hRef).symm
      _ = hpair.interactionCoeff hax q₀ q₀ :=
            hassoc.interaction_assoc_yz hax r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
  calc
    hpair.interactionCoeff hax q r
        = hpair.interactionCoeff hax r q₀ := h_qr_to_r_ref
    _ = faceScaleInteractionReferenceKappa hpair hax := by
        simpa [faceScaleInteractionReferenceKappa, q₀]
          using h_r_ref_to_ref_ref

/-- Reconstruct face-scale interaction universality from K1--K3 and singleton
interaction normalizations. -/
noncomputable def faceScaleProductInteractionUniversality_of_parts
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair) :
    FiniteFaceScaleProductInteractionUniversalityAssumptionsFor hpair where
  kappa := faceScaleInteractionReferenceKappa hpair
  interactionCoeff_common := by
    intro hax A B _ _ _ _ _ _ q r hq hr
    by_cases hsubA : Subsingleton A
    · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_left
        hax q r hq hr hsubA
    · by_cases hsubB : Subsingleton B
      · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_right
          hax q r hq hr hsubB
      · exact faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc hax q r hq hr hsubA hsubB

/-- Product quasi-additivity from product gauge normalization and interaction
associativity, without a singleton interaction normalization.

The singleton coefficient is not value-identified: if either factor is a
subsingleton, the corresponding posterior value is zero, so the interaction term
vanishes for every coefficient.  The only coefficient identification needed for
the product formula is therefore the nondegenerate one, which follows from the
K1--K3 associativity equations. -/
noncomputable def productQuasiAdditivityForFaceScales_of_components_noSingleton
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces where
  kappa := faceScaleInteractionReferenceKappa hpair
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    rw [hnorm.leftCoeff_normalized hax q r hq hr]
    rw [hnorm.rightCoeff_normalized hax q r hq hr]
    by_cases hsubA : Subsingleton A
    · haveI : Subsingleton A := hsubA
      have hVq :
          hfaces.branch_result.branch_agg.value_rep.V q
            (experimentOfChannel P) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep q hq P
      rw [hVq]
      ring
    · by_cases hsubB : Subsingleton B
      · haveI : Subsingleton B := hsubB
        have hVr :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R) = 0 :=
          branchValue_channel_eq_zero_of_subsingleton F
            hfaces.branch_result.branch_agg.value_rep r hr R
        rw [hVr]
        ring
      · rw [faceScaleInteractionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc hax q r hq hr hsubA hsubB]
        ring

/-- Face-scale triple-product value associativity.  This is the
pre-universal, pre-entropy version of the product-parenthesization value
transport used in the old Stage 10 interaction-associativity proof. -/
structure FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  triple_value_assoc :
    ∀ (_hax : TraceAxioms F)
      {A B C O Y Z : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      [Fintype Z] [DecidableEq Z]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (P : Channel A O) (R : Channel B Y) (S : Channel C Z),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist (prodDist q r) s)
          (experimentOfChannel (prodChannel (prodChannel P R) S)) =
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q (prodDist r s))
          (experimentOfChannel (prodChannel P (prodChannel R S)))

/-- Face-scale triple-product value associativity follows from exact
relabeling coherence of the selected posterior-value representatives and the
structural product associator relabeling facts. -/
theorem faceScaleTripleProductValueAssociativity_of_valueRelabeling
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u}) :
    FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces where
  triple_value_assoc := by
    intro hax A B C O Y Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q r s _hq _hr _hs
      P R S
    have hrel :=
      hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
        (Equiv.prodAssoc A B C) (Equiv.prodAssoc O Y Z)
        (prodDist (prodDist q r) s) (prodChannel (prodChannel P R) S)
    have hrel' :
        hfaces.branch_result.branch_agg.value_rep.V
            (prodDist q (prodDist r s))
            (experimentOfChannel (prodChannel P (prodChannel R S))) =
          hfaces.branch_result.branch_agg.value_rep.V
            (prodDist (prodDist q r) s)
            (experimentOfChannel (prodChannel (prodChannel P R) S)) := by
      simpa [relabelDist_prodAssoc q r s, relabelChannel_prodAssoc P R S]
        using hrel
    exact hrel'.symm

/-- Triple-product value associativity is preserved by coherent positive
prior-gauge rescaling.  The two product-parenthesized priors are related by
the canonical product associator, and `CoherentFaceScaleGauge.gauge_relabel_eq`
aligns the two gauge factors. -/
theorem faceScaleTripleProductValueAssociativity_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hgauge : CoherentFaceScaleGauge.{u}) :
    FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor
      (hfaces.gaugeTransform hgauge) where
  triple_value_assoc := by
    intro hax A B C O Y Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q r s hq hr hs P R S
    dsimp [CoherentRelabelingFaceScalesStructure.gaugeTransform,
      branchAggregationCocycleNormalizedChainRuleStructure_gaugeTransform,
      branchAggregationStructure_gaugeTransform,
      posteriorValueRepresentation_gaugeTransform]
    have hraw :=
      htriple.triple_value_assoc hax q r s hq hr hs P R S
    have hg :
        hgauge.gauge (prodDist q (prodDist r s)) =
          hgauge.gauge (prodDist (prodDist q r) s) := by
      have h :=
        hgauge.gauge_relabel_eq
          (Equiv.prodAssoc A B C) (prodDist (prodDist q r) s)
      simpa [relabelDist_prodAssoc q r s] using h
    rw [hraw, hg]

/-- Coefficient extraction from triple-product value associativity and
normalized product coefficients.  This is the exact source-ready algebraic
bridge needed to turn value-level associativity into the K1--K3 interaction
coefficient equations. -/
structure FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (_hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (_htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    Prop where
  interaction_assoc_xy :
    ∀ (hax : TraceAxioms F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax q r =
        hpair.interactionCoeff hax q (prodDist r s)
  interaction_assoc_xz :
    ∀ (hax : TraceAxioms F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax q (prodDist r s)
  interaction_assoc_yz :
    ∀ (hax : TraceAxioms F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hs : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff hax (prodDist q r) s =
        hpair.interactionCoeff hax r s

/-- Face-scale K1--K3 coefficient extraction from value-level triple-product
associativity and normalized product bilinear form.

This is the pre-universal analogue of the old Stage 10 normalized
triple-product algebra, stated directly against
`CoherentRelabelingFaceScalesStructure`. -/
theorem faceScaleTripleProductCoeffExtraction_of_valueAssociativity
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    {hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair}
    {htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces} :
    FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
      hpair hnorm htriple where
  interaction_assoc_xy := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA hB _hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hxne :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hyne :
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
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
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.idChannel : Channel B B))
        (Channel.uninformativeChannelU C)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.uninformativeChannelU C))] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q r hq hr
        (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        r s hr hs
        (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized s hs] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxyne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_xz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs hA _hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hxne :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
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
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs
        (Channel.idChannel : Channel A A)
        (prodChannel (Channel.uninformativeChannelU B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q r hq hr
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        r s hr hs
        (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hxzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)
  interaction_assoc_yz := by
    intro hax A B C _ _ _ _ _ _ _ _ _ q r s hq hr hs _hA hB hC
    have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
    have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hs
    have hyne :
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax r hr hB
    have hzne :
        hfaces.branch_result.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 := by
      exact faceScale_idChannel_value_ne_zero_of_A1 hfaces hax s hs hC
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
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        (prodDist q r) s hqr hs
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (Channel.idChannel : Channel C C)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q (prodDist r s) hq hrs
        (Channel.uninformativeChannelU A)
        (prodChannel (Channel.idChannel : Channel B B)
          (Channel.idChannel : Channel C C))] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        q r hq hr
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)] at hval
    rw [faceScaleProductPairBilinear_normalized hpair hnorm hax
        r s hr hs
        (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C)] at hval
    rw [hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq] at hval
    ring_nf at hval
    exact mul_right_cancel₀ hyzne (by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Reconstruct K1--K3 interaction associativity from triple-product
coefficient extraction. -/
theorem faceScaleProductInteractionAssociativity_of_coeffExtraction
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    {hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair}
    {htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces}
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        hpair hnorm htriple) :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair where
  interaction_assoc_xy := hextract.interaction_assoc_xy
  interaction_assoc_xz := hextract.interaction_assoc_xz
  interaction_assoc_yz := hextract.interaction_assoc_yz

/-- Interaction associativity for the product-gauge transformed representative,
obtained by transporting pairwise bilinearity and triple-product value
associativity through the coherent gauge and then applying the existing
coefficient-extraction algebra. -/
theorem faceScaleProductInteractionAssociativity_gaugeTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor
      (faceScaleProductPairwiseBilinearity_gaugeTransform
        hpair hgauge.gauge) :=
  faceScaleProductInteractionAssociativity_of_coeffExtraction
    (faceScaleTripleProductCoeffExtraction_of_valueAssociativity
      (hpair :=
        faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)
      (hnorm :=
        faceScaleProductGaugeNormalization_of_currentGauge
          (faceScaleCurrentProductGaugeNormalization_of_gaugeTransform hgauge))
      (htriple :=
        faceScaleTripleProductValueAssociativity_gaugeTransform
          htriple hgauge.gauge))

/-- Interaction associativity for a representative already in the current
product gauge, obtained directly from value-level triple-product
associativity. -/
theorem faceScaleProductInteractionAssociativity_of_valueAssociativity_currentGauge
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces}
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair :=
  faceScaleProductInteractionAssociativity_of_coeffExtraction
    (faceScaleTripleProductCoeffExtraction_of_valueAssociativity
      (hpair := hpair)
      (hnorm := faceScaleProductGaugeNormalization_of_currentGauge hgauge)
      (htriple := htriple))

/-- Pairwise product bilinearity reconstructed from the multi-stage
left-slice affine, intercept, and slope outputs. -/
noncomputable def faceScaleProductPairwiseBilinearity_of_multiPieces
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff)) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces :=
  faceScaleProductPairwiseBilinearity_of_sliceAffine
    (faceScaleProductLeftSliceAffine_of_transform haff)
    (faceScaleProductSliceIntercept_of_positiveLinear hintercept)
    (faceScaleProductSliceSlope_of_slopeAffine hslope)

/-- Reassemble the face-scale product quasi-additivity theorem from the
non-circular face-scale analogues of the Stage 10 product components. -/
def productQuasiAdditivityForFaceScales_of_components
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm : FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (huniv :
      FiniteFaceScaleProductInteractionUniversalityAssumptionsFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces where
  kappa := huniv.kappa
  product_quasi_add := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear hax q r hq hr P R]
    rw [hnorm.leftCoeff_normalized hax q r hq hr]
    rw [hnorm.rightCoeff_normalized hax q r hq hr]
    rw [huniv.interactionCoeff_common hax q r hq hr]
    ring

/-- Product quasi-additivity from pairwise bilinearity, explicit current-gauge
normalization, and the K-associativity/singleton interaction-universality
pieces. -/
noncomputable def productQuasiAdditivityForFaceScales_of_finalProductComponents
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  productQuasiAdditivityForFaceScales_of_components hpair
    (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
    (faceScaleProductInteractionUniversality_of_parts hpair hassoc hsingle)

/-- Product quasi-additivity for the product-gauge transformed representative.

This is the Lean form of the paper move "rescale by the chosen positive product
gauge, then work with the normalized representatives": the raw pairwise
bilinear package is transported through the gauge, the transformed left/right
coefficients are normalized by `hgauge`, and the usual interaction
associativity/singleton pieces supply the common `κ`. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedComponents
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge))
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_finalProductComponents
    (faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
    (faceScaleCurrentProductGaugeNormalization_of_gaugeTransform hgauge)
    hassoc hsingle

/-- Product quasi-additivity for the product-gauge transformed representative,
with transformed interaction associativity derived internally from raw
triple-product value associativity. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_gaugeTransform
          hpair hgauge.gauge)) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_gaugeTransformedComponents
    hpair hgauge
    (faceScaleProductInteractionAssociativity_gaugeTransform hgauge htriple)
    hsingle

/-- Product quasi-additivity for the product-gauge transformed representative,
with singleton-factor cases handled by value-zero rather than by an arbitrary
singleton coefficient normalization. -/
noncomputable def productQuasiAdditivityForFaceScales_of_gaugeTransformedProductData_noSingleton
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleProductGaugeTransformFor hpair)
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces) :
    FiniteProductQuasiAdditivityForFaceScales
      (hfaces.gaugeTransform hgauge.gauge) :=
  productQuasiAdditivityForFaceScales_of_components_noSingleton
    (faceScaleProductPairwiseBilinearity_gaugeTransform hpair hgauge.gauge)
    (faceScaleProductGaugeNormalization_of_currentGauge
      (faceScaleCurrentProductGaugeNormalization_of_gaugeTransform hgauge))
    (faceScaleProductInteractionAssociativity_gaugeTransform hgauge htriple)

/-- Product quasi-additivity from the multi-stage source-ready components:
left-slice affine transform, intercept linearity, slope affinity, current
gauge, triple-product value/coefficient extraction, and singleton interaction
normalization. -/
noncomputable def productQuasiAdditivityForFaceScales_of_multiComponents
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        htriple)
    (hsingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope)) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  productQuasiAdditivityForFaceScales_of_finalProductComponents
    (faceScaleProductPairwiseBilinearity_of_multiPieces
      haff hintercept hslope)
    hgauge
    (faceScaleProductInteractionAssociativity_of_coeffExtraction hextract)
    hsingle

/-- Paper Step 1: product revelation links the chain scales to
`Z(q) = 1 + kappa * H(q)`.

The equations are written without division to keep the algebraic downstream
proof independent of denominator-normalization details. -/
structure FiniteProductRevelationScaleLinkAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  scale_product_left :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        (1 + hprod.kappa hax *
          fullRevelationValueForFaceScales hfaces q) *
        hfaces.branch_result.scale_factorization.scale r
  scale_product_right :
    ∀ (hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        (1 + hprod.kappa hax *
          fullRevelationValueForFaceScales hfaces r) *
        hfaces.branch_result.scale_factorization.scale q

/-- Paper Step 3: the two-grouping argument collapses the product interaction
coefficient to zero. -/
structure FiniteTwoGroupingInteractionCollapseAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  kappa_eq_zero :
    ∀ (hax : TraceAxioms F), hprod.kappa hax = 0

/-- Singleton/degenerate scale normalization for extending the nondegenerate
universal-scale conclusion to all full-support priors. -/
structure FiniteUniversalScaleSingletonNormalizationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  scale_eq_of_subsingleton :
    ∀ {A B : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      (Subsingleton A ∨ Subsingleton B) →
      hfaces.branch_result.scale_factorization.scale q =
        hfaces.branch_result.scale_factorization.scale r

/-!
### Stage 27 product-interaction cleanup

The product-revelation scale link and the final two-grouping collapse are
split below into smaller pieces.  The full-revelation product value identity
and the final cancellation from constant `Z` to `kappa = 0` are internal.  The
remaining external content is the sequential-revelation scale equation and the
paper's weight-constant conclusion from the grouping equation.
-/

/-- Product of two full-revelation channels is the full-revelation channel on
the product action type. -/
theorem prodChannel_idChannel_idChannel_eq_idChannel
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    prodChannel (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B) =
      (Channel.idChannel : Channel (A × B) (A × B)) := by
  funext a
  ext o
  rcases a with ⟨a, b⟩
  rcases o with ⟨a', b'⟩
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      simp [prodChannel, Channel.idChannel]
    · simp [prodChannel, Channel.idChannel, Dist.pure_apply, hb]
  · simp [prodChannel, Channel.idChannel, Dist.pure_apply, ha]

/-- Reveal the first coordinate of a product action. -/
noncomputable def productFirstRevealChannel
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] :
    Channel (A × B) A :=
  fun ab => Dist.pure ab.1

/-- Reveal the second coordinate of a product action. -/
noncomputable def productSecondRevealChannel
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B] :
    Channel (A × B) B :=
  fun ab => Dist.pure ab.2

/-- Full revelation of a product action with swapped outcome labels. -/
noncomputable def productSwapRevealChannel
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Channel (A × B) (B × A) :=
  fun ab => Dist.pure (ab.2, ab.1)

/-- Revealing the first coordinate and then the second coordinate is exactly
full revelation of the product action. -/
theorem productFirstThenSecondReveal_eq_idChannel
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    (productFirstRevealChannel (A := A) (B := B) ▷
        (fun _ => productSecondRevealChannel (A := A) (B := B))) =
      (Channel.idChannel : Channel (A × B) (A × B)) := by
  funext ab
  ext o
  rcases ab with ⟨a, b⟩
  rcases o with ⟨a', b'⟩
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, Channel.idChannel]
    · simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, Channel.idChannel, hb]
  · simp [seqCompose_apply, productFirstRevealChannel,
      productSecondRevealChannel, Channel.idChannel, Dist.pure_apply, ha]

/-- Revealing the second coordinate and then the first coordinate is full
revelation with the two outcome coordinates swapped. -/
theorem productSecondThenFirstReveal_eq_swapReveal
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    (productSecondRevealChannel (A := A) (B := B) ▷
        (fun _ => productFirstRevealChannel (A := A) (B := B))) =
      productSwapRevealChannel (A := A) (B := B) := by
  funext ab
  ext o
  rcases ab with ⟨a, b⟩
  rcases o with ⟨b', a'⟩
  by_cases hb : b' = b
  · subst hb
    by_cases ha : a' = a
    · subst ha
      simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, productSwapRevealChannel]
    · simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, productSwapRevealChannel,
        ha]
  · simp [seqCompose_apply, productFirstRevealChannel,
      productSecondRevealChannel, productSwapRevealChannel,
      Dist.pure_apply, hb]

/-- Positive posterior under the identity channel is the revealed pure action. -/
theorem posterior_idChannel_eq_pure_of_pos
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (a : A) (ha : 0 < q a) :
    Channel.posterior (Channel.idChannel : Channel A A) q a =
      Dist.pure a := by
  ext b
  have hm : (Channel.outcomeMarginal (Channel.idChannel : Channel A A) q) a = q a := by
    rw [outcomeMarginal_idChannel']
  unfold Channel.posterior
  rw [dif_pos (by rw [hm]; exact ha)]
  by_cases h : b = a
  · subst h
    simp only [Channel.idChannel, Dist.pure_apply_self, mul_one]
    rw [hm]
    field_simp [ne_of_gt ha]
  · have hsym : a ≠ b := fun h' => h h'.symm
    simp [Channel.idChannel, Dist.pure_apply_ne _ _ h,
      Dist.pure_apply_ne _ _ hsym]

/-- The swapped full-revelation marginal under a product prior is the swapped
product prior. -/
theorem outcomeMarginal_productSwapRevealChannel_prodDist
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B)) (prodDist q r) =
      prodDist r q := by
  ext ba
  rcases ba with ⟨b, a⟩
  calc
    Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B)) (prodDist q r) (b, a)
        =
      q a * r b := by
        rw [Channel.outcomeMarginal_apply]
        rw [Fintype.sum_eq_single (a, b)]
        · simp [productSwapRevealChannel, prodDist_apply_pair]
        · intro ab hab
          rcases ab with ⟨a', b'⟩
          have hpair : (b, a) ≠ (b', a') := by
            intro hba
            apply hab
            exact Prod.ext (Prod.ext_iff.mp hba |>.2.symm)
              (Prod.ext_iff.mp hba |>.1.symm)
          simp [productSwapRevealChannel, prodDist_apply_pair,
            Dist.pure_apply_ne _ _ hpair]
    _ = prodDist r q (b, a) := by
        rw [prodDist_apply_pair]
        ring

/-- Positive posterior under swapped product full revelation is the pure
product action with coordinates unswapped. -/
theorem posterior_productSwapRevealChannel_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) (b : B)
    (ha : 0 < q a) (hb : 0 < r b) :
    Channel.posterior
        (productSwapRevealChannel (A := A) (B := B))
        (prodDist q r) (b, a) =
      Dist.pure (a, b) := by
  ext ab
  rcases ab with ⟨a', b'⟩
  have hm :
      (Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B))
        (prodDist q r)) (b, a) = q a * r b := by
    rw [outcomeMarginal_productSwapRevealChannel_prodDist]
    rw [prodDist_apply_pair]
    ring
  have hmpos :
      (Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B))
        (prodDist q r)) (b, a) > 0 := by
    rw [hm]
    exact mul_pos ha hb
  unfold Channel.posterior
  rw [dif_pos hmpos]
  by_cases h : a' = a ∧ b' = b
  · rcases h with ⟨ha', hb'⟩
    subst ha'
    subst hb'
    simp only [prodDist_apply_pair, productSwapRevealChannel,
      Dist.pure_apply_self, mul_one]
    rw [hm]
    field_simp [ne_of_gt (mul_pos ha hb)]
  · have hswap : (b, a) ≠ (b', a') := by
      intro hba
      apply h
      exact ⟨Prod.ext_iff.mp hba |>.2.symm,
        Prod.ext_iff.mp hba |>.1.symm⟩
    have hpure : (a', b') ≠ (a, b) := by
      intro hp
      apply h
      exact ⟨Prod.ext_iff.mp hp |>.1, Prod.ext_iff.mp hp |>.2⟩
    simp [productSwapRevealChannel, prodDist_apply_pair, hswap,
      Dist.pure_apply_ne _ _ hpure]

/-- Swapped product full revelation and ordinary product full revelation induce
the same posterior law under a full-support product prior. -/
theorem samePosteriorLawExp_productSwapReveal_idChannel_of_fullSupport
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (productSwapRevealChannel (A := A) (B := B)))
      (experimentOfChannel (Channel.idChannel : Channel (A × B) (A × B))) := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  rw [outcomeMarginal_productSwapRevealChannel_prodDist,
    outcomeMarginal_idChannel']
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc
    ∑ b : B, ∑ a : A,
        (r b * q a) *
          φ (Channel.posterior
            (productSwapRevealChannel (A := A) (B := B))
            (prodDist q r) (b, a))
        =
      ∑ b : B, ∑ a : A,
        (q a * r b) * φ (Dist.pure (a, b)) := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro a _
          rw [posterior_productSwapRevealChannel_prodDist_of_pos
            q r a b (hq a) (hr b)]
          ring_nf
    _ =
      ∑ a : A, ∑ b : B,
        (q a * r b) * φ (Dist.pure (a, b)) := by
          rw [Finset.sum_comm]
    _ =
      ∑ a : A, ∑ b : B,
        (q a * r b) *
          φ (Channel.posterior
            (Channel.idChannel : Channel (A × B) (A × B))
            (prodDist q r) (a, b)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          have hp : 0 < prodDist q r (a, b) := by
            exact mul_pos (hq a) (hr b)
          rw [posterior_idChannel_eq_pure_of_pos (prodDist q r) (a, b) hp]

/-- The marginal of the first-coordinate reveal under a product prior is the
first prior. -/
theorem outcomeMarginal_productFirstRevealChannel_prodDist
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    Channel.outcomeMarginal
        (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) =
      q := by
  ext a
  rw [Channel.outcomeMarginal_apply]
  simp only [productFirstRevealChannel, prodDist_apply_pair,
    Fintype.sum_prod_type]
  calc
    ∑ x : A, ∑ y : B, q x * r y * (Dist.pure x) a
        = ∑ x : A, q x * (Dist.pure x) a * ∑ y : B, r y := by
          apply Finset.sum_congr rfl
          intro x _
          calc
            ∑ y : B, q x * r y * (Dist.pure x) a
                = ∑ y : B, (q x * (Dist.pure x) a) * r y := by
                  apply Finset.sum_congr rfl
                  intro y _
                  ring
            _ = q x * (Dist.pure x) a * ∑ y : B, r y := by
                  rw [Finset.mul_sum]
    _ = ∑ x : A, q x * (Dist.pure x) a := by
          rw [r.sum_eq_one]
          simp
    _ = q a := by
          simp [Dist.pure_apply]

/-- The marginal of the second-coordinate reveal under a product prior is the
second prior. -/
theorem outcomeMarginal_productSecondRevealChannel_prodDist
    {A B : Type u}
    [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    Channel.outcomeMarginal
        (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) =
      r := by
  ext b
  rw [Channel.outcomeMarginal_apply]
  simp only [productSecondRevealChannel, prodDist_apply_pair,
    Fintype.sum_prod_type]
  calc
    ∑ x : A, ∑ y : B, q x * r y * (Dist.pure y) b
        = ∑ y : B, (∑ x : A, q x) * r y * (Dist.pure y) b := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          calc
            ∑ x : A, q x * r y * (Dist.pure y) b
                = ∑ x : A, q x * (r y * (Dist.pure y) b) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
            _ = (∑ x : A, q x) * (r y * (Dist.pure y) b) := by
                  rw [Finset.sum_mul]
            _ = (∑ x : A, q x) * r y * (Dist.pure y) b := by
                  ring
    _ = ∑ y : B, r y * (Dist.pure y) b := by
          rw [q.sum_eq_one]
          simp
    _ = r b := by
          simp [Dist.pure_apply]

/-- Posterior after revealing the first coordinate of a product prior. -/
theorem posterior_productFirstRevealChannel_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) (ha : 0 < q a) :
    Channel.posterior
        (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) a =
      prodDist (Dist.pure a) r := by
  ext ab
  rcases ab with ⟨a', b⟩
  have hmarg_pos :
      (Channel.outcomeMarginal
        (productFirstRevealChannel (A := A) (B := B)) (prodDist q r)) a > 0 := by
    simpa [outcomeMarginal_productFirstRevealChannel_prodDist] using ha
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : a' = a
  · subst h
    simp [productFirstRevealChannel, prodDist_apply_pair,
      outcomeMarginal_productFirstRevealChannel_prodDist, ne_of_gt ha]
  · have hsym : a ≠ a' := fun h' => h h'.symm
    simp [productFirstRevealChannel, prodDist_apply_pair,
      Dist.pure_apply_ne _ _ h, Dist.pure_apply_ne _ _ hsym,
      outcomeMarginal_productFirstRevealChannel_prodDist]

/-- Posterior after revealing the second coordinate of a product prior. -/
theorem posterior_productSecondRevealChannel_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (b : B) (hb : 0 < r b) :
    Channel.posterior
        (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) b =
      prodDist q (Dist.pure b) := by
  ext ab
  rcases ab with ⟨a, b'⟩
  have hmarg_pos :
      (Channel.outcomeMarginal
        (productSecondRevealChannel (A := A) (B := B)) (prodDist q r)) b > 0 := by
    simpa [outcomeMarginal_productSecondRevealChannel_prodDist] using hb
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : b' = b
  · subst h
    simp [productSecondRevealChannel, prodDist_apply_pair,
      outcomeMarginal_productSecondRevealChannel_prodDist, ne_of_gt hb]
  · have hsym : b ≠ b' := fun h' => h h'.symm
    simp [productSecondRevealChannel, prodDist_apply_pair,
      Dist.pure_apply_ne _ _ h, Dist.pure_apply_ne _ _ hsym,
      outcomeMarginal_productSecondRevealChannel_prodDist]

/-- Product of first-coordinate full revelation with no information on the
second coordinate has first marginal `q`. -/
theorem outcomeMarginal_prod_id_uninformativeChannelU_prodDist
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) :
    Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r) (a, PUnit.unit) = q a := by
  have h := congrArg (fun d : Dist (A × PUnit.{u+1}) => d (a, PUnit.unit))
    (outcomeMarginal_prod q r
      (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU B))
  calc
    Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r) (a, PUnit.unit)
        =
      (Channel.outcomeMarginal (Channel.idChannel : Channel A A) q) a *
        (Channel.outcomeMarginal (Channel.uninformativeChannelU B) r) PUnit.unit := by
          simpa [prodDist_apply_pair] using h
    _ = q a * 1 := by
          rw [outcomeMarginal_idChannel']
          have hU :
              (Channel.outcomeMarginal (Channel.uninformativeChannelU B) r)
                  PUnit.unit = 1 := by
            simp [Channel.outcomeMarginal, Channel.uninformativeChannelU,
              r.sum_eq_one]
          rw [hU]
    _ = q a := by ring

/-- Product of no information on the first coordinate with second-coordinate
full revelation has second marginal `r`. -/
theorem outcomeMarginal_prod_uninformativeChannelU_id_prodDist
    {A B : Type u}
    [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (b : B) :
    Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r) (PUnit.unit, b) = r b := by
  have h := congrArg (fun d : Dist (PUnit.{u+1} × B) => d (PUnit.unit, b))
    (outcomeMarginal_prod q r
      (Channel.uninformativeChannelU A)
      (Channel.idChannel : Channel B B))
  calc
    Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r) (PUnit.unit, b)
        =
      (Channel.outcomeMarginal (Channel.uninformativeChannelU A) q) PUnit.unit *
        (Channel.outcomeMarginal (Channel.idChannel : Channel B B) r) b := by
          simpa [prodDist_apply_pair] using h
    _ = 1 * r b := by
          rw [outcomeMarginal_idChannel']
          have hU :
              (Channel.outcomeMarginal (Channel.uninformativeChannelU A) q)
                  PUnit.unit = 1 := by
            simp [Channel.outcomeMarginal, Channel.uninformativeChannelU,
              q.sum_eq_one]
          rw [hU]
    _ = r b := by ring

/-- Posterior for first-coordinate full revelation with no information on the
second coordinate. -/
theorem posterior_prod_id_uninformativeChannelU_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) (ha : 0 < q a) :
    Channel.posterior
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r) (a, PUnit.unit) =
      prodDist (Dist.pure a) r := by
  ext ab
  rcases ab with ⟨a', b⟩
  have hmarg_eq :
      (Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r)) (a, PUnit.unit) = q a :=
    outcomeMarginal_prod_id_uninformativeChannelU_prodDist q r a
  have hmarg_pos :
      (Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r)) (a, PUnit.unit) > 0 := by
    rw [hmarg_eq]
    exact ha
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : a' = a
  · subst a'
    simp only [prodDist_apply_pair, prodChannel_apply_pair, Channel.idChannel,
      Channel.uninformativeChannelU, Dist.pure_apply_self, mul_one, one_mul]
    change q a * r b /
        (Channel.outcomeMarginal
          (prodChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU B))
          (prodDist q r)) (a, PUnit.unit) = r b
    rw [hmarg_eq]
    field_simp [ne_of_gt ha]
  · have hsym : a ≠ a' := fun h' => h h'.symm
    simp [prodChannel_apply_pair, Channel.idChannel, Channel.uninformativeChannelU,
      prodDist_apply_pair, Dist.pure_apply_ne _ _ h,
      Dist.pure_apply_ne _ _ hsym]

/-- Posterior for no information on the first coordinate with second-coordinate
full revelation. -/
theorem posterior_prod_uninformativeChannelU_id_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (b : B) (hb : 0 < r b) :
    Channel.posterior
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r) (PUnit.unit, b) =
      prodDist q (Dist.pure b) := by
  ext ab
  rcases ab with ⟨a, b'⟩
  have hmarg_eq :
      (Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r)) (PUnit.unit, b) = r b :=
    outcomeMarginal_prod_uninformativeChannelU_id_prodDist q r b
  have hmarg_pos :
      (Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r)) (PUnit.unit, b) > 0 := by
    rw [hmarg_eq]
    exact hb
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : b' = b
  · subst b'
    simp only [prodDist_apply_pair, prodChannel_apply_pair, Channel.idChannel,
      Channel.uninformativeChannelU, Dist.pure_apply_self, mul_one]
    change q a * r b /
        (Channel.outcomeMarginal
          (prodChannel (Channel.uninformativeChannelU A)
            (Channel.idChannel : Channel B B))
          (prodDist q r)) (PUnit.unit, b) = q a
    rw [hmarg_eq]
    field_simp [ne_of_gt hb]
  · have hsym : b ≠ b' := fun h' => h h'.symm
    simp [prodChannel_apply_pair, Channel.idChannel, Channel.uninformativeChannelU,
      prodDist_apply_pair, Dist.pure_apply_ne _ _ h,
      Dist.pure_apply_ne _ _ hsym]

/-- Revealing the first coordinate has the same posterior law as full
revelation of the first coordinate together with no information on the second. -/
theorem samePosteriorLawExp_productFirstReveal_prod_id_uninformativeU
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel
        (productFirstRevealChannel (A := A) (B := B)))
      (experimentOfChannel
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))) := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro a _
  rw [outcomeMarginal_productFirstRevealChannel_prodDist,
    outcomeMarginal_prod_id_uninformativeChannelU_prodDist]
  by_cases ha : 0 < q a
  · rw [posterior_productFirstRevealChannel_prodDist_of_pos q r a ha,
      posterior_prod_id_uninformativeChannelU_prodDist_of_pos q r a ha]
  · have hzero : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
    simp [hzero]

/-- Revealing the second coordinate has the same posterior law as no
information on the first coordinate together with full revelation of the second. -/
theorem samePosteriorLawExp_productSecondReveal_prod_uninformativeU_id
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel
        (productSecondRevealChannel (A := A) (B := B)))
      (experimentOfChannel
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))) := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro b _
  rw [outcomeMarginal_productSecondRevealChannel_prodDist,
    outcomeMarginal_prod_uninformativeChannelU_id_prodDist]
  by_cases hb : 0 < r b
  · rw [posterior_productSecondRevealChannel_prodDist_of_pos q r b hb,
      posterior_prod_uninformativeChannelU_id_prodDist_of_pos q r b hb]
  · have hzero : r b = 0 := le_antisymm (le_of_not_gt hb) (r.nonneg b)
    simp [hzero]

/-- A1 gives nonzero full-revelation value for a full-support non-singleton
prior in the faithful face-scale representative. -/
theorem fullRevelationValueForFaceScales_ne_zero_of_A1
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    fullRevelationValueForFaceScales hfaces q ≠ 0 := by
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
  have hne :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) :=
    branch_value_ne_of_strict_experiment_pref
      F hfaces.branch_result.branch_agg.value_rep q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      hstrict.1 hstrict.2
  have hzero :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  intro hH
  exact hne (by
    unfold fullRevelationValueForFaceScales at hH
    rw [hH, hzero])

/-- Base-value nonconstancy for the face-scale product-slice affine
decomposition is internal from A1 and zero-normalisation. -/
theorem faceScaleBaseValueNonconstancy_of_A1
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleBaseValueNonconstancyAssumptionsFor hfaces where
  base_value_nonconstant := by
    intro hax A _ _ _ q hq hA
    have hstrict :=
      branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
    exact
      branch_value_ne_of_strict_experiment_pref
        F hfaces.branch_result.branch_agg.value_rep q hq
        (experimentOfChannel (Channel.idChannel : Channel A A))
        (experimentOfChannel (Channel.uninformativeChannelU A))
        hstrict.1 hstrict.2

/-- Product quasi-additivity internally gives the full-revelation value
identity `H(q ⊗ r) = H(q) + H(r) + kappa H(q)H(r)`. -/
theorem fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    fullRevelationValueForFaceScales hfaces (prodDist q r) =
      fullRevelationValueForFaceScales hfaces q +
      fullRevelationValueForFaceScales hfaces r +
      hprod.kappa hax *
        fullRevelationValueForFaceScales hfaces q *
        fullRevelationValueForFaceScales hfaces r := by
  have hqa :=
    hprod.product_quasi_add hax q r hq hr
      (Channel.idChannel : Channel A A)
      (Channel.idChannel : Channel B B)
  simpa [fullRevelationValueForFaceScales,
    prodChannel_idChannel_idChannel_eq_idChannel] using hqa

/-- Sharper product-revelation bridge: sequential full revelation gives the
scale-weighted value equation.  Product quasi-additivity supplies the other
side of the comparison internally. -/
structure FiniteProductRevelationSequentialScaleAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  sequential_reveal_left :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale r *
          (fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces q) =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces r
  sequential_reveal_right :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale q *
          (fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces r) =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces q

/-- Source-ready normalized-chain form of the sequential full-revelation
calculation in Step 1 of `Interaction collapse and universal chain scale`.

This is narrower than `FiniteProductRevelationSequentialScaleAssumptionsFor`:
it asserts exactly the normalized chain-rule specialization before clearing
denominators.  The remaining content is the channel/face transport identifying
the first-stage coordinate reveal and every continuation reveal with the
corresponding full-revelation values. -/
structure FiniteSequentialFullRevelationNormalizedChainAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  normalized_chain_left :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r
  normalized_chain_right :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q

/-- Coordinate-reveal value transport for the sequential full-revelation
calculation.

This isolates the value/relabeling part of Step 1: revealing only one
coordinate of a product prior has the same representative value as full
revelation of that coordinate, and swapped full revelation has the same value
as ordinary full revelation of the product. -/
structure FiniteCoordinateRevealValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productFirstRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces q
  second_reveal_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productSecondRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces r
  swap_full_revelation_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
          (productSwapRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces (prodDist q r)

/-- The first two coordinate-reveal value identities, separated from the
swapped full-revelation outcome-relabeling identity.

This is narrower than `FiniteCoordinateRevealValueTransportAssumptionsFor`:
the remaining content is exactly the product/no-information value transport for
revealing one coordinate of a product prior. -/
structure FiniteCoordinateRevealMarginalValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productFirstRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces q
  second_reveal_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productSecondRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces r

/-- Swapped product full revelation has the same value as ordinary product
full revelation.

This isolates the outcome-relabeling part of coordinate value transport. -/
structure FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  swap_full_revelation_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productSwapRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces (prodDist q r)

/-- Swapped product full revelation has the same value as ordinary product full
revelation because it induces the same posterior law under a full-support
product prior. -/
theorem coordinateSwapFullRevelationValueTransport_of_posteriorLaw
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces where
  swap_full_revelation_value := by
    intro _hax A B _ _ _ _ _ _ q r hq hr _hA _hB
    let hV := hfaces.branch_result.branch_agg.value_rep
    have hsame :=
      samePosteriorLawExp_productSwapReveal_idChannel_of_fullSupport
        q r hq hr
    have hval :
        hV.V (prodDist q r)
            (experimentOfChannel
              (productSwapRevealChannel (A := A) (B := B))) =
          hV.V (prodDist q r)
            (experimentOfChannel
              (Channel.idChannel : Channel (A × B) (A × B))) :=
      hV.respects_same_posterior_law (prodDist q r)
        (experimentOfChannel
          (productSwapRevealChannel (A := A) (B := B)))
        (experimentOfChannel
          (Channel.idChannel : Channel (A × B) (A × B)))
        hsame
    exact hval

/-- Reassemble the Stage 29 coordinate value-transport package from its two
sharper pieces. -/
theorem coordinateRevealValueTransport_of_marginal_and_swap
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hmarg :
      FiniteCoordinateRevealMarginalValueTransportAssumptionsFor hfaces)
    (hswap :
      FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces) :
    FiniteCoordinateRevealValueTransportAssumptionsFor hfaces where
  first_reveal_value := hmarg.first_reveal_value
  second_reveal_value := hmarg.second_reveal_value
  swap_full_revelation_value := hswap.swap_full_revelation_value

/-- Product quasi-additivity, together with zero normalization for the
uninformative channel and posterior-law transport, proves the marginal
coordinate-reveal value identities.  Thus the Stage 30 marginal-value transport
residual is not an independent product bridge. -/
theorem coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) :
    FiniteCoordinateRevealMarginalValueTransportAssumptionsFor hfaces where
  first_reveal_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr _hA _hB
    let hV := hfaces.branch_result.branch_agg.value_rep
    have hsameVal :
        hV.V (prodDist q r)
            (experimentOfChannel
              (productFirstRevealChannel (A := A) (B := B))) =
          hV.V (prodDist q r)
            (experimentOfChannel
              (prodChannel (Channel.idChannel : Channel A A)
                (Channel.uninformativeChannelU B))) :=
      hV.respects_same_posterior_law (prodDist q r)
        (experimentOfChannel
          (productFirstRevealChannel (A := A) (B := B)))
        (experimentOfChannel
          (prodChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU B)))
        (samePosteriorLawExp_productFirstReveal_prod_id_uninformativeU q r)
    have hqa :=
      hprod.product_quasi_add hax q r hq hr
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)
    have hzero :
        hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) = 0 :=
      hV.zero_normalized r hr
    calc
      hV.V (prodDist q r)
          (experimentOfChannel
            (productFirstRevealChannel (A := A) (B := B)))
          =
        hV.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel A A)
              (Channel.uninformativeChannelU B))) := hsameVal
      _ =
        hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) +
          hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) +
          hprod.kappa hax *
            hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) *
            hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) := hqa
      _ = fullRevelationValueForFaceScales hfaces q := by
        change
          hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) +
              hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) +
            hprod.kappa hax *
              hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) *
              hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) =
            hV.V q (experimentOfChannel (Channel.idChannel : Channel A A))
        rw [hzero]
        ring
  second_reveal_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr _hA _hB
    let hV := hfaces.branch_result.branch_agg.value_rep
    have hsameVal :
        hV.V (prodDist q r)
            (experimentOfChannel
              (productSecondRevealChannel (A := A) (B := B))) =
          hV.V (prodDist q r)
            (experimentOfChannel
              (prodChannel (Channel.uninformativeChannelU A)
                (Channel.idChannel : Channel B B))) :=
      hV.respects_same_posterior_law (prodDist q r)
        (experimentOfChannel
          (productSecondRevealChannel (A := A) (B := B)))
        (experimentOfChannel
          (prodChannel (Channel.uninformativeChannelU A)
            (Channel.idChannel : Channel B B)))
        (samePosteriorLawExp_productSecondReveal_prod_uninformativeU_id q r)
    have hqa :=
      hprod.product_quasi_add hax q r hq hr
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)
    have hzero :
        hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
      hV.zero_normalized q hq
    calc
      hV.V (prodDist q r)
          (experimentOfChannel
            (productSecondRevealChannel (A := A) (B := B)))
          =
        hV.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (Channel.idChannel : Channel B B))) := hsameVal
      _ =
        hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) +
          hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) +
          hprod.kappa hax *
            hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) *
            hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := hqa
      _ = fullRevelationValueForFaceScales hfaces r := by
        change
          hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) +
              hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) +
            hprod.kappa hax *
              hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) *
              hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) =
            hV.V r (experimentOfChannel (Channel.idChannel : Channel B B))
        rw [hzero]
        ring

/-- Continuation transport for the sequential full-revelation calculation.

After revealing one coordinate, every continuation branch lives on a coordinate
face such as `{a} × B`.  This interface isolates the support-face/relabeling
and scale transport needed to identify the weighted normalized continuation
sum with the full-revelation value of the other coordinate. -/
structure FiniteCoordinateRevealContinuationTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_continuation_sum :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      ∑ a : A,
          (Channel.outcomeMarginal
            (productFirstRevealChannel (A := A) (B := B))
            (prodDist q r)) a *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r) a)
            (productSecondRevealChannel (A := A) (B := B))
        =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r
  second_reveal_continuation_sum :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      ∑ b : B,
          (Channel.outcomeMarginal
            (productSecondRevealChannel (A := A) (B := B))
            (prodDist q r)) b *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r) b)
            (productFirstRevealChannel (A := A) (B := B))
        =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q

/-- Pointwise coordinate-face continuation transport.

This is narrower than the weighted-sum package: it asks for the normalized
continuation value on each coordinate face.  The weighted identities then
follow by the internally proved coordinate-reveal marginal identities and the
fact that the marginals sum to one. -/
structure FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_branch :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      branchNormalizedValue hfaces.chain
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (productSecondRevealChannel (A := A) (B := B))
      =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r
  second_reveal_branch :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      branchNormalizedValue hfaces.chain
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (productFirstRevealChannel (A := A) (B := B))
      =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q

/-- Coordinate support-face value transport.

After one coordinate of a product prior is revealed, the continuation problem
lives on the coordinate face `{a} × B` or `A × {b}`.  This interface isolates
the cardinal representative choice identifying that ambient boundary-face
continuation value with the intrinsic full-revelation value on the unrevealed
coordinate. -/
structure FiniteCoordinateSupportFaceValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (experimentOfChannel
          (productSecondRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces r
  second_coordinate_face_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (experimentOfChannel
          (productFirstRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces q

/-- Coordinate support-face scale transport.

This is the scale counterpart of
`FiniteCoordinateSupportFaceValueTransportAssumptionsFor`: it identifies the
chain scale selected on the ambient coordinate face with the intrinsic scale on
the unrevealed coordinate. -/
structure FiniteCoordinateSupportFaceScaleTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_scale :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a) =
      hfaces.branch_result.scale_factorization.scale r
  second_coordinate_face_scale :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b) =
      hfaces.branch_result.scale_factorization.scale q

/-- Coordinate continuation value read on the support face of the boundary
posterior.

This is the support-read version of
`FiniteCoordinateSupportFaceValueTransportAssumptionsFor`.  After revealing one
coordinate of a full-support product prior, the posterior is a boundary prior
on the ambient product type.  The paper reads the continuation on its positive
support face before identifying that face with the unrevealed coordinate. -/
structure FiniteCoordinateSupportFaceValueSupportReadFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_value_support :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productSecondRevealChannel (A := A) (B := B))
            (Channel.posterior
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r) a))) =
      fullRevelationValueForFaceScales hfaces r
  second_coordinate_face_value_support :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productFirstRevealChannel (A := A) (B := B))
            (Channel.posterior
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r) b))) =
      fullRevelationValueForFaceScales hfaces q

/-- Coordinate continuation scale read on the support face of the boundary
posterior.  This is the support-read counterpart of
`FiniteCoordinateSupportFaceScaleTransportAssumptionsFor`. -/
structure FiniteCoordinateSupportFaceScaleSupportReadFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_scale_support :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a).restrictToSupport =
      hfaces.branch_result.scale_factorization.scale r
  second_coordinate_face_scale_support :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b).restrictToSupport =
      hfaces.branch_result.scale_factorization.scale q

/-- Coordinate support-face value normalization.

This names the representative choice identifying the ambient product boundary
face after a coordinate reveal with the intrinsic unrevealed coordinate
problem. -/
structure FiniteCoordinateSupportFaceValueIdentificationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (experimentOfChannel
          (productSecondRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces r
  second_coordinate_face_value :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (experimentOfChannel
          (productFirstRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces q

/-- Coordinate support-face scale normalization. -/
structure FiniteCoordinateSupportFaceScaleIdentificationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_scale :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a) =
      hfaces.branch_result.scale_factorization.scale r
  second_coordinate_face_scale :
    ∀ (_hax : TraceAxioms F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b) =
      hfaces.branch_result.scale_factorization.scale q

/-- Reconstruct value transport from the explicit coordinate support-face
representative normalization. -/
theorem coordinateSupportFaceValueTransport_of_identification
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hident : FiniteCoordinateSupportFaceValueIdentificationFor hfaces) :
    FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces where
  first_coordinate_face_value :=
    hident.first_coordinate_face_value
  second_coordinate_face_value :=
    hident.second_coordinate_face_value

/-- Reconstruct scale transport from the explicit coordinate support-face
scale normalization. -/
theorem coordinateSupportFaceScaleTransport_of_identification
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hident : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces) :
    FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces where
  first_coordinate_face_scale :=
    hident.first_coordinate_face_scale
  second_coordinate_face_scale :=
    hident.second_coordinate_face_scale

/-- Reconstruct pointwise coordinate-branch continuation transport from the
two exact coordinate support-face transports: value representatives and chain
scales. -/
theorem coordinateRevealBranchContinuationTransport_of_coordinateSupportFaceTransports
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hvalue :
      FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces)
    (hscale :
      FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces) :
    FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces where
  first_reveal_branch := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB a
    have hv :=
      hvalue.first_coordinate_face_value hax q r hq hr hA hB a
    have hs :=
      hscale.first_coordinate_face_scale hax q r hq hr hA hB a
    simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
      BranchAggregationCocycleNormalizedChainRuleStructure.chain,
      branchChainStructure_of_scaleFactorization, hv, hs]
  second_reveal_branch := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB b
    have hv :=
      hvalue.second_coordinate_face_value hax q r hq hr hA hB b
    have hs :=
      hscale.second_coordinate_face_scale hax q r hq hr hA hB b
    simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
      BranchAggregationCocycleNormalizedChainRuleStructure.chain,
      branchChainStructure_of_scaleFactorization, hv, hs]

/-- Reassemble the Stage 29 continuation-sum transport package from pointwise
coordinate-face continuation transport. -/
theorem coordinateRevealContinuationTransport_of_branchTransport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces) :
    FiniteCoordinateRevealContinuationTransportAssumptionsFor hfaces where
  first_reveal_continuation_sum := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    calc
      ∑ a : A,
          (Channel.outcomeMarginal
            (productFirstRevealChannel (A := A) (B := B))
            (prodDist q r)) a *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r) a)
            (productSecondRevealChannel (A := A) (B := B))
          =
        ∑ a : A,
          q a *
          (fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [outcomeMarginal_productFirstRevealChannel_prodDist]
            rw [hbranch.first_reveal_branch hax q r hq hr hA hB a]
      _ =
        fullRevelationValueForFaceScales hfaces r /
          hfaces.branch_result.scale_factorization.scale r := by
            rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  second_reveal_continuation_sum := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    calc
      ∑ b : B,
          (Channel.outcomeMarginal
            (productSecondRevealChannel (A := A) (B := B))
            (prodDist q r)) b *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r) b)
            (productFirstRevealChannel (A := A) (B := B))
          =
        ∑ b : B,
          r b *
          (fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [outcomeMarginal_productSecondRevealChannel_prodDist]
            rw [hbranch.second_reveal_branch hax q r hq hr hA hB b]
      _ =
        fullRevelationValueForFaceScales hfaces q /
          hfaces.branch_result.scale_factorization.scale q := by
            rw [← Finset.sum_mul, r.sum_eq_one, one_mul]

/-- The normalized sequential full-revelation bridge follows from coordinate
reveal value transport, continuation support-face transport, and the already
proved normalized chain rule. -/
theorem sequentialFullRevelationNormalizedChain_of_coordinateTransports
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hvalue : FiniteCoordinateRevealValueTransportAssumptionsFor hfaces)
    (hcont :
      FiniteCoordinateRevealContinuationTransportAssumptionsFor hfaces) :
    FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces where
  normalized_chain_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hchain :=
      hfaces.normalizedChainRule (prodDist q r) hprod_full
        (productFirstRevealChannel (A := A) (B := B))
        (fun _ => productSecondRevealChannel (A := A) (B := B))
    have hseq_left :
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              (fun _ => productSecondRevealChannel (A := A) (B := B))) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productFirstThenSecondReveal_eq_idChannel]
      rfl
    have hfirst :
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
        BranchAggregationCocycleNormalizedChainRuleStructure.chain,
        branchChainStructure_of_scaleFactorization,
        fullRevelationValueForFaceScales,
        hvalue.first_reveal_value hax q r hq hr hA hB]
    have hcontsum :=
      hcont.first_reveal_continuation_sum hax q r hq hr hA hB
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              (fun _ => productSecondRevealChannel (A := A) (B := B))) :=
            hseq_left.symm
      _ =
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) +
          ∑ a : A,
            (Channel.outcomeMarginal
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r)) a *
            branchNormalizedValue hfaces.chain
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
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hchain :=
      hfaces.normalizedChainRule (prodDist q r) hprod_full
        (productSecondRevealChannel (A := A) (B := B))
        (fun _ => productFirstRevealChannel (A := A) (B := B))
    have hseq_right :
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              (fun _ => productFirstRevealChannel (A := A) (B := B))) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productSecondThenFirstReveal_eq_swapReveal]
      simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
        BranchAggregationCocycleNormalizedChainRuleStructure.chain,
        branchChainStructure_of_scaleFactorization,
        fullRevelationValueForFaceScales,
        hvalue.swap_full_revelation_value hax q r hq hr hA hB]
    have hsecond :
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
        BranchAggregationCocycleNormalizedChainRuleStructure.chain,
        branchChainStructure_of_scaleFactorization,
        fullRevelationValueForFaceScales,
        hvalue.second_reveal_value hax q r hq hr hA hB]
    have hcontsum :=
      hcont.second_reveal_continuation_sum hax q r hq hr hA hB
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              (fun _ => productFirstRevealChannel (A := A) (B := B))) :=
            hseq_right.symm
      _ =
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) +
          ∑ b : B,
            (Channel.outcomeMarginal
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r)) b *
            branchNormalizedValue hfaces.chain
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

/-- Clearing denominators in the normalized sequential full-revelation
equations gives the existing scale-weighted Step 1 package. -/
theorem productRevelationSequentialScale_of_normalizedChain
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hnorm :
      FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces) :
    FiniteProductRevelationSequentialScaleAssumptionsFor hfaces where
  sequential_reveal_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hnorm_left :=
      hnorm.normalized_chain_left hax q r hq hr hA hB
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hsp_pos :
        0 <
          hfaces.branch_result.scale_factorization.scale (prodDist q r) :=
      hfaces.branch_result.scale_factorization.scale_pos
        (prodDist q r) hprod_full
    have hsr_pos :
        0 < hfaces.branch_result.scale_factorization.scale r :=
      hfaces.branch_result.scale_factorization.scale_pos r hr
    have hsp_ne :
        hfaces.branch_result.scale_factorization.scale (prodDist q r) ≠ 0 :=
      ne_of_gt hsp_pos
    have hsr_ne :
        hfaces.branch_result.scale_factorization.scale r ≠ 0 :=
      ne_of_gt hsr_pos
    field_simp [hsp_ne, hsr_ne] at hnorm_left
    ring_nf at hnorm_left ⊢
    linarith
  sequential_reveal_right := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hnorm_right :=
      hnorm.normalized_chain_right hax q r hq hr hA hB
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hsp_pos :
        0 <
          hfaces.branch_result.scale_factorization.scale (prodDist q r) :=
      hfaces.branch_result.scale_factorization.scale_pos
        (prodDist q r) hprod_full
    have hsq_pos :
        0 < hfaces.branch_result.scale_factorization.scale q :=
      hfaces.branch_result.scale_factorization.scale_pos q hq
    have hsp_ne :
        hfaces.branch_result.scale_factorization.scale (prodDist q r) ≠ 0 :=
      ne_of_gt hsp_pos
    have hsq_ne :
        hfaces.branch_result.scale_factorization.scale q ≠ 0 :=
      ne_of_gt hsq_pos
    field_simp [hsp_ne, hsq_ne] at hnorm_right
    ring_nf at hnorm_right ⊢
    linarith

/-- Reconstruct the old product-revelation scale-link package from the
sequential-revelation scale equations plus the internal full-revelation product
identity and A1 nonzero full revelation. -/
theorem productRevelationScaleLink_of_sequentialScale
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hseq : FiniteProductRevelationSequentialScaleAssumptionsFor hfaces) :
    FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod where
  scale_product_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hprodH :=
      fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
        hfaces hprod hax q r hq hr
    have hseq_left :=
      hseq.sequential_reveal_left hax q r hq hr hA hB
    have hHr_ne :
        fullRevelationValueForFaceScales hfaces r ≠ 0 :=
      fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax r hr hB
    have hdiff :
        fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces q =
          (1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces q) *
            fullRevelationValueForFaceScales hfaces r := by
      rw [hprodH]
      ring
    rw [hdiff] at hseq_left
    have hmul :
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces q) *
            hfaces.branch_result.scale_factorization.scale r) *
          fullRevelationValueForFaceScales hfaces r =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces r := by
      calc
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces q) *
            hfaces.branch_result.scale_factorization.scale r) *
          fullRevelationValueForFaceScales hfaces r
            =
          hfaces.branch_result.scale_factorization.scale r *
            ((1 + hprod.kappa hax *
                fullRevelationValueForFaceScales hfaces q) *
              fullRevelationValueForFaceScales hfaces r) := by ring
        _ =
          hfaces.branch_result.scale_factorization.scale (prodDist q r) *
            fullRevelationValueForFaceScales hfaces r := hseq_left
    exact (mul_right_cancel₀ hHr_ne hmul).symm
  scale_product_right := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hprodH :=
      fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
        hfaces hprod hax q r hq hr
    have hseq_right :=
      hseq.sequential_reveal_right hax q r hq hr hA hB
    have hHq_ne :
        fullRevelationValueForFaceScales hfaces q ≠ 0 :=
      fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax q hq hA
    have hdiff :
        fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces r =
          (1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces r) *
            fullRevelationValueForFaceScales hfaces q := by
      rw [hprodH]
      ring
    rw [hdiff] at hseq_right
    have hmul :
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces r) *
            hfaces.branch_result.scale_factorization.scale q) *
          fullRevelationValueForFaceScales hfaces q =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces q := by
      calc
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces r) *
            hfaces.branch_result.scale_factorization.scale q) *
          fullRevelationValueForFaceScales hfaces q
            =
          hfaces.branch_result.scale_factorization.scale q *
            ((1 + hprod.kappa hax *
                fullRevelationValueForFaceScales hfaces r) *
              fullRevelationValueForFaceScales hfaces q) := by ring
        _ =
          hfaces.branch_result.scale_factorization.scale (prodDist q r) *
            fullRevelationValueForFaceScales hfaces q := hseq_right
    exact (mul_right_cancel₀ hHq_ne hmul).symm

/-- `Z(q) = 1 + kappa * H(q)` for the product-interaction proof. -/
noncomputable def productScaleZForFaceScales
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  1 + hprod.kappa hax * fullRevelationValueForFaceScales hfaces q

/-- The product `Z`-weight is multiplicative: `Z(q ⊗ r) = Z(q) · Z(r)`.

This is the Lean form of the paper's identity (M) `w(u⊗v)=w(u)w(v)` (Lemma
scalecoherence, Step 3, eq. wmult), obtained directly from the internal
full-revelation product identity `H(q⊗r)=H(q)+H(r)+κH(q)H(r)`.  It is proved
here with no extra assumptions — but note it holds for EVERY value of `κ`, so
multiplicativity alone does not force `κ = 0`; that requires the full
partition/disjoint-union grouping equation. -/
theorem productScaleZForFaceScales_prod_eq
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : TraceAxioms F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    productScaleZForFaceScales hfaces hprod hax (prodDist q r) =
      productScaleZForFaceScales hfaces hprod hax q *
        productScaleZForFaceScales hfaces hprod hax r := by
  have hH :=
    fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
      hfaces hprod hax q r hq hr
  unfold productScaleZForFaceScales
  rw [hH]
  ring

/-- The two-grouping algebra core (paper Lemma scalecoherence, Step 3).

Comparing the two evaluations (E1) `s·(x²+y²)/2` and (E2) `s·((x+y)/2)²` of the
same disjoint-union weight `w(T)` with `s = w(p) > 0` forces `(x−y)² = 0`, hence
`x = y`.  This is the pure real-analysis heart of the argument and is
independent of any representation detail. -/
theorem twoGrouping_eq_of_evaluations
    {s x y : ℝ} (hs : 0 < s)
    (hE : s * ((x ^ 2 + y ^ 2) / 2) = s * (((x + y) / 2) ^ 2)) :
    x = y := by
  have hsq : (x - y) ^ 2 = 0 := by
    have h := mul_left_cancel₀ (ne_of_gt hs) hE
    nlinarith [h]
  have : x - y = 0 := by nlinarith [sq_nonneg (x - y), hsq]
  linarith

/-- Full-revelation value `H` is invariant under action relabeling, from exact
posterior-value relabeling of the selected representatives.  This is the Lean
form of the paper's Corollary permutationinvariance restricted to full
revelation, and it is what lets the two-grouping regroup a disjoint union along
different partitions. -/
theorem fullRevelationValueForFaceScales_relabel_eq
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) :
    fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) =
      fullRevelationValueForFaceScales hfaces q := by
  have hrel :=
    hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
      e e q (Channel.idChannel : Channel A A)
  have hid :
      Relabeling.relabelChannel e e (Channel.idChannel : Channel A A) =
        (Channel.idChannel : Channel B B) := by
    funext b
    ext b'
    rw [Relabeling.relabelChannel_apply]
    simp only [Channel.idChannel]
    by_cases hbb : b' = b
    · subst hbb
      rw [Dist.pure_apply_self, Dist.pure_apply_self]
    · rw [Dist.pure_apply_ne (e.symm b) (e.symm b')
          (fun h => hbb (e.symm.injective h)),
        Dist.pure_apply_ne b b' hbb]
  rw [hid] at hrel
  simpa [fullRevelationValueForFaceScales] using hrel

/-- The fixed nondegenerate reference action type used to cancel the common
interaction coefficient. -/
abbrev universalScaleReferenceType : Type u := ULift.{u, 0} Bool

/-- The fixed full-support reference prior for the two-grouping cleanup. -/
noncomputable def universalScaleReferencePrior : Dist universalScaleReferenceType :=
  Dist.uniform

theorem universalScaleReferencePrior_fullSupport :
    universalScaleReferencePrior.FullSupport :=
  Dist.uniform_fullSupport (A := universalScaleReferenceType)

theorem universalScaleReference_not_subsingleton :
    ¬ Subsingleton universalScaleReferenceType := by
  intro hsub
  have htf : (true : Bool) = false := by
    exact congrArg ULift.down
      (Subsingleton.elim
        (ULift.up true : universalScaleReferenceType)
        (ULift.up false : universalScaleReferenceType))
  cases htf

/-- Sharper two-grouping bridge: the grouping equation forces the induced
`Z`-weight to be one at every nondegenerate full-support prior.  The remaining
cancellation from this fact to `kappa = 0` is internal. -/
structure FiniteProductGroupingWeightConstantAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  Z_eq_one_of_nondegenerate :
    ∀ (hax : TraceAxioms F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hA : ¬ Subsingleton A),
      productScaleZForFaceScales hfaces hprod hax q = 1

/-- Product `Z`-weight positivity (paper eq. POS `1 + κ F_r(ν) > 0`), phrased at
full revelation.  This is the positive-slice-slope consequence of coherent
product quasi-additivity, needed so that `w = 1/Z` is a well-defined positive
weight in the two-grouping argument. -/
structure FiniteProductScaleZPositiveAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  Z_pos :
    ∀ (hax : TraceAxioms F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      0 < productScaleZForFaceScales hfaces hprod hax q

/-- The `Z`-weight is the calibrated first-coordinate slice slope.

Comparing coherent product quasi-additivity with the slice-affine decomposition
at the two calibrated first-coordinate points `U` (no information) and `id`
(full revelation), over a nondegenerate reference first coordinate, identifies

`faceScaleAffineSliceTransformSlope haff hax q₀ q id = 1 + κ·H(q) = Z(q)`.

This is the cardinal identification behind the paper's POS condition. -/
theorem productScaleZForFaceScales_eq_sliceTransformSlope
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : TraceAxioms F)
    {A₀ A : Type u}
    [Fintype A₀] [DecidableEq A₀] [Nonempty A₀]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q₀ : Dist A₀) (q : Dist A)
    (hq₀ : q₀.FullSupport) (hq : q.FullSupport)
    (hA₀ : ¬ Subsingleton A₀) :
    productScaleZForFaceScales hfaces hprod hax q =
      faceScaleAffineSliceTransformSlope haff hax q₀ q
        (Channel.idChannel : Channel A A) := by
  classical
  set V := hfaces.branch_result.branch_agg.value_rep with hV
  set hslice := faceScaleProductLeftSliceAffine_of_transform haff with hhslice
  have hH₀_ne :
      fullRevelationValueForFaceScales hfaces q₀ ≠ 0 :=
    fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax q₀ hq₀ hA₀
  -- Slice-affine at the two calibrated first-coordinate points.
  have hU :=
    hslice.left_slice_affine hax q₀ q hq₀ hq
      (Channel.uninformativeChannelU A₀)
      (Channel.idChannel : Channel A A)
  have hId :=
    hslice.left_slice_affine hax q₀ q hq₀ hq
      (Channel.idChannel : Channel A₀ A₀)
      (Channel.idChannel : Channel A A)
  -- Product quasi-additivity at the same two points.
  have hqaU :=
    hprod.product_quasi_add hax q₀ q hq₀ hq
      (Channel.uninformativeChannelU A₀)
      (Channel.idChannel : Channel A A)
  have hqaId :=
    hprod.product_quasi_add hax q₀ q hq₀ hq
      (Channel.idChannel : Channel A₀ A₀)
      (Channel.idChannel : Channel A A)
  have hzero₀ :
      V.V q₀ (experimentOfChannel (Channel.uninformativeChannelU A₀)) = 0 :=
    V.zero_normalized q₀ hq₀
  -- Intercept identification: intercept = H(q).
  rw [hzero₀] at hU hqaU
  rw [mul_zero, zero_add] at hU
  rw [mul_zero, zero_mul, add_zero, zero_add] at hqaU
  have hintercept :
      hslice.leftSliceIntercept hax q₀ q (Channel.idChannel : Channel A A) =
        fullRevelationValueForFaceScales hfaces q := by
    have := hU.symm.trans hqaU
    simpa [fullRevelationValueForFaceScales] using this
  -- Slope identification: slope·H(q₀) = H(q₀)·(1 + κ·H(q)).
  have hkey :
      hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) *
          fullRevelationValueForFaceScales hfaces q₀ =
        (1 + hprod.kappa hax * fullRevelationValueForFaceScales hfaces q) *
          fullRevelationValueForFaceScales hfaces q₀ := by
    have hchain := hId.symm.trans hqaId
    rw [hintercept] at hchain
    have hchain' :
        hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) *
            fullRevelationValueForFaceScales hfaces q₀ =
          fullRevelationValueForFaceScales hfaces q₀ +
            hprod.kappa hax * fullRevelationValueForFaceScales hfaces q₀ *
              fullRevelationValueForFaceScales hfaces q := by
      have := hchain
      simp only [fullRevelationValueForFaceScales] at this ⊢
      linarith
    rw [hchain']
    ring
  have hslope_eq :
      hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) =
        1 + hprod.kappa hax * fullRevelationValueForFaceScales hfaces q :=
    mul_right_cancel₀ hH₀_ne hkey
  have hslope_def :
      hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) =
        faceScaleAffineSliceTransformSlope haff hax q₀ q
          (Channel.idChannel : Channel A A) := rfl
  rw [productScaleZForFaceScales, ← hslope_eq, hslope_def]

/-- **Concrete POS, proved.**  `Z(q) = 1 + κ·H(q) > 0` for every full-support
prior, for ANY coherent product quasi-additivity package, given the slice-affine
transform.  The abstract `κ` is pinned by the value function through
quasi-additivity: `Z(q)` IS the calibrated slice slope, which is the positive
multiplier of a positive affine transform
(`faceScaleAffineSliceTransformSlope_pos`).  This discharges the paper's POS
condition (eq. QAslope) with no extra assumption. -/
theorem productScaleZpositive_of_sliceTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces) :
    FiniteProductScaleZPositiveAssumptionsFor hfaces hprod where
  Z_pos := by
    intro hax A _ _ _ q hq
    rw [productScaleZForFaceScales_eq_sliceTransformSlope hprod haff hax
      universalScaleReferencePrior q
      universalScaleReferencePrior_fullSupport hq
      universalScaleReference_not_subsingleton]
    exact faceScaleAffineSliceTransformSlope_pos haff hax
      universalScaleReferencePrior q
      universalScaleReferencePrior_fullSupport hq
      (Channel.idChannel : Channel A A)

/-- **Pre-universal grouping weight recursion — the paper's weight equation (W).**

For a finite partition presented as a dependent sigma family (`sigmaDist p f`,
with block probabilities `p` and within-block conditionals `f`), the inverse
`Z`-weight `w = Z⁻¹` satisfies

`w(sigmaDist p f) = w(p) · Σₖ pₖ · w(fₖ)`.

This is paper eq. (W) (Lemma scalecoherence, Step 2, derived there from the
grouping recursion (GR), which in turn comes from the block bridge, the branch
formula, and undetectable-distinctions neutrality — all strictly BEFORE
universal scale, entropy reduction, or Faddeev).  It is stated at the
pre-universal face-scale layer, for the face-scale `Z(·) = 1 + κ·H(·)` only.

Nondegeneracy side conditions: the sigma total, the coarse prior, and every
positive-probability block conditional are nondegenerate full-support; blocks
with `pₖ = 0` do not constrain the equation (their `w` term is multiplied by
`pₖ = 0`), so the recursion is quantified over full-support `p`.

This is strictly earlier and strictly more primitive than the two-grouping
evaluations E1/E2, which are DERIVED from it below
(`finiteProductTwoGroupingWeightEquation_of_weightRecursion`). -/
structure FinitePreUniversalGroupingWeightRecursionAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  weight_recursion :
    ∀ (hax : TraceAxioms F)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
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
  reference_Z_eq_one :
    ∀ (hax : TraceAxioms F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- **Repaired grouping target — the paper's two-grouping equation (W)/(E1)/(E2).**

This replaces the opaque `FiniteProductGroupingReferenceWeightAssumptionsFor`
conclusion with the *cause* the paper actually uses: the labelled
disjoint-union `T = ½(u⊗u)⁰ ⊔ ½(v⊗v)¹` admits two groupings, whose weight
equation (paper eqs. (E1)/(E2), Lemma scalecoherence Step 3) evaluate `w(T)` two
ways.  Concretely, writing `w(·) = 1/Z(·)`, for every pair of nondegenerate
full-support priors there is a common positive top-block weight `wp > 0` with

* (E1) `w(T) = wp · (x² + y²)/2`, and
* (E2) `w(T) = wp · ((x + y)/2)²`,

where `x = w(u)`, `y = w(v)`.  A reference normalization fixes `Z` at the
reference prior to one.

This is faithful to the paper's named grouping equation and strictly more
primitive than the reference-weight conclusion: the entire nontrivial
cancellation `(x − y)² = 0 ⟹ Z(u) = Z(v) ⟹ Z ≡ 1 ⟹ κ = 0` is proved from it
below.  The remaining content is exactly the block-bridge grouping recursion
supplying the two evaluations, which is the genuine pre-universal input that is
not yet formalized at this layer. -/
structure FiniteProductTwoGroupingWeightEquationAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  two_grouping_evaluations :
    ∀ (hax : TraceAxioms F)
      {U V : Type v}
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
  reference_Z_eq_one :
    ∀ (hax : TraceAxioms F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- **Two-grouping cancellation.**  The paper's Step-3 conclusion `w(u) = w(v)`
for nondegenerate full-support priors, from the two evaluations of `w(T)`. -/
theorem productScaleZ_inv_eq_of_twoGrouping
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
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

/-- Product `Z` is constant across nondegenerate full-support priors, from the
two-grouping cancellation and `Z`-positivity. -/
theorem productScaleZ_eq_of_twoGrouping
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hax : TraceAxioms F)
    {U V : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (u : Dist U) (v : Dist V) (hu : u.FullSupport) (hv : v.FullSupport)
    (hU : ¬ Subsingleton U) (hV : ¬ Subsingleton V) :
    productScaleZForFaceScales hfaces hprod hax u =
      productScaleZForFaceScales hfaces hprod hax v := by
  have hinv := productScaleZ_inv_eq_of_twoGrouping hgroup hax u v hu hv hU hV
  have hZu := hpos.Z_pos hax u hu
  have hZv := hpos.Z_pos hax v hv
  -- x⁻¹ = y⁻¹ with x,y > 0 gives x = y.
  have := congrArg (fun t => t⁻¹) hinv
  simpa [inv_inv] using this

/-!
### Deriving the two-grouping evaluations E1/E2 from the weight recursion (W)

The labelled disjoint union `T = ½(u⊗u)⁰ ⊔ ½(v⊗v)¹` is presented as a
`sigmaDist` in two ways: grouped by the top label, and grouped by the pair
(label, first within-block coordinate).  The weight recursion evaluates both;
exact relabeling identifies the two presentations; multiplicativity of `Z`
turns `w(u⊗u)` into `w(u)²`.  Everything below is the paper's Lemma
scalecoherence Step 3 up to (E1)/(E2), with no entropy or universal scale.
-/

/-- `sigmaDist` of full-support pieces is full-support. -/
theorem sigmaDist_fullSupport
    {K : Type u} [Fintype K] {Act : K → Type u}
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    (p : Dist K) (f : ∀ k, Dist (Act k))
    (hp : p.FullSupport) (hf : ∀ k, (f k).FullSupport) :
    (sigmaDist p f).FullSupport := by
  intro ka
  rcases ka with ⟨k, a⟩
  rw [sigmaDist_apply]
  exact mul_pos (hp k) (hf k a)

/-- Sum over the two-point reference label type. -/
theorem sum_universalScaleReferenceType
    (g : universalScaleReferenceType → ℝ) :
    (∑ k : universalScaleReferenceType, g k) =
      g (ULift.up false) + g (ULift.up true) := by
  rw [← (Equiv.ulift (α := Bool)).symm.sum_comp g]
  simp [Fintype.sum_bool, Equiv.ulift]
  ring

/-- The uniform reference prior puts mass `1/2` on each label. -/
theorem universalScaleReferencePrior_apply
    (k : universalScaleReferenceType.{u}) :
    universalScaleReferencePrior k = 1 / 2 := by
  have hcard : Fintype.card universalScaleReferenceType.{u} = 2 := by
    simp [universalScaleReferenceType]
  simp [universalScaleReferencePrior, Dist.uniform_apply, hcard]

/-- A product with a nonsubsingleton factor is nonsubsingleton. -/
theorem not_subsingleton_prod_left
    {α β : Type u} [Nonempty β]
    (hα : ¬ Subsingleton α) : ¬ Subsingleton (α × β) := by
  intro hsub
  apply hα
  obtain ⟨b⟩ : Nonempty β := inferInstance
  constructor
  intro a a'
  have := Subsingleton.elim (α := α × β) (a, b) (a', b)
  exact congrArg Prod.fst this

/-- A sigma with a nonsubsingleton base and nonempty fibers is
nonsubsingleton. -/
theorem not_subsingleton_sigma
    {K : Type u} {Act : K → Type u} [∀ k, Nonempty (Act k)]
    (hK : ¬ Subsingleton K) : ¬ Subsingleton ((k : K) × Act k) := by
  intro hsub
  apply hK
  constructor
  intro k k'
  have := Subsingleton.elim (α := (k : K) × Act k)
    ⟨k, Classical.choice inferInstance⟩ ⟨k', Classical.choice inferInstance⟩
  exact congrArg Sigma.fst this

/-- Two-case fiber family over the two-point reference label type. -/
def twoGroupingFiber (U V : Type u) : universalScaleReferenceType → Type u
  | ⟨false⟩ => U
  | ⟨true⟩ => V

noncomputable instance twoGroupingFiberFintype
    {U V : Type u} [Fintype U] [Fintype V] :
    ∀ k, Fintype (twoGroupingFiber U V k)
  | ⟨false⟩ => show Fintype U from inferInstance
  | ⟨true⟩ => show Fintype V from inferInstance

instance twoGroupingFiberDecidableEq
    {U V : Type u} [DecidableEq U] [DecidableEq V] :
    ∀ k, DecidableEq (twoGroupingFiber U V k)
  | ⟨false⟩ => show DecidableEq U from inferInstance
  | ⟨true⟩ => show DecidableEq V from inferInstance

instance twoGroupingFiberNonempty
    {U V : Type u} [Nonempty U] [Nonempty V] :
    ∀ k, Nonempty (twoGroupingFiber U V k)
  | ⟨false⟩ => show Nonempty U from inferInstance
  | ⟨true⟩ => show Nonempty V from inferInstance

/-- The two block conditionals of the two-grouping disjoint union. -/
noncomputable def twoGroupingConditional
    {U V : Type u} [Fintype U] [Fintype V]
    (u : Dist U) (v : Dist V) :
    ∀ k, Dist (twoGroupingFiber U V k)
  | ⟨false⟩ => u
  | ⟨true⟩ => v

/-- Reassociation of the two sigma presentations of the two-grouping
disjoint union. -/
def twoGroupingReassoc (U V : Type u) :
    ((ka : (k : universalScaleReferenceType) × twoGroupingFiber U V k) ×
        twoGroupingFiber U V ka.1) ≃
      ((k : universalScaleReferenceType) ×
        (twoGroupingFiber U V k × twoGroupingFiber U V k)) where
  toFun := fun x => ⟨x.1.1, (x.1.2, x.2)⟩
  invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  left_inv := fun x => rfl
  right_inv := fun x => rfl

/-- The fine sigma presentation relabels onto the coarse one. -/
theorem relabelDist_twoGroupingReassoc
    {U V : Type u}
    [Fintype U] [DecidableEq U]
    [Fintype V] [DecidableEq V]
    (u : Dist U) (v : Dist V) :
    Relabeling.relabelDist (twoGroupingReassoc U V)
        (sigmaDist
          (sigmaDist universalScaleReferencePrior
            (twoGroupingConditional u v))
          (fun ka => twoGroupingConditional u v ka.1)) =
      sigmaDist universalScaleReferencePrior
        (fun k => prodDist (twoGroupingConditional u v k)
          (twoGroupingConditional u v k)) := by
  ext x
  rcases x with ⟨k, a, b⟩
  show (sigmaDist
      (sigmaDist universalScaleReferencePrior (twoGroupingConditional u v))
      (fun ka => twoGroupingConditional u v ka.1))
        ((twoGroupingReassoc U V).symm ⟨k, (a, b)⟩) =
    (sigmaDist universalScaleReferencePrior
      (fun k => prodDist (twoGroupingConditional u v k)
        (twoGroupingConditional u v k))) ⟨k, (a, b)⟩
  show (sigmaDist universalScaleReferencePrior (twoGroupingConditional u v))
        ⟨k, a⟩ * (twoGroupingConditional u v k) b =
    universalScaleReferencePrior k *
      (prodDist (twoGroupingConditional u v k)
        (twoGroupingConditional u v k)) (a, b)
  rw [sigmaDist_apply, prodDist_apply_pair]
  ring

/-- **E1/E2 derived from the pre-universal weight recursion.**

The two evaluations of `w(T)` for the labelled disjoint union
`T = ½(u⊗u)⁰ ⊔ ½(v⊗v)¹` follow from:

* the weight recursion (W) applied to the coarse grouping of `T` (E1),
* the weight recursion applied twice — to the fine grouping of `T` and to its
  coarse marginal `S = ½u⁰ ⊔ ½v¹` (E2),
* exact relabeling between the two sigma presentations of `T`
  (`hrelV` + `relabelDist_twoGroupingReassoc`),
* multiplicativity `Z(x ⊗ x) = Z(x)²`
  (`productScaleZForFaceScales_prod_eq`), and
* `Z`-positivity for the reference weight `wp = w(p₂) > 0`.

This upgrades the two-grouping target: its remaining source is exactly the
weight recursion (W). -/
theorem finiteProductTwoGroupingWeightEquation_of_weightRecursion
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hrec :
      FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod where
  reference_Z_eq_one := hrec.reference_Z_eq_one
  two_grouping_evaluations := by
    intro hax U V _ _ _ _ _ _ u v hu hv hU hV
    classical
    -- Setup: label type, fibers, conditionals.
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
    -- Coarse presentation T and fine marginal S.
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
    -- Fine presentation T' over the coarse marginal S.
    set f' := fun (ka : (k : K) × twoGroupingFiber U V k) => g ka.1 with hf'
    have hf'fs : ∀ ka : (k : K) × twoGroupingFiber U V k,
        (f' ka).FullSupport :=
      fun ka => hgfs ka.1
    have hf'nd : ∀ ka : (k : K) × twoGroupingFiber U V k,
        ¬ Subsingleton (twoGroupingFiber U V ka.1) :=
      fun ka => hgnd ka.1
    set T' := sigmaDist S f' with hT'
    have hT'fs : T'.FullSupport := sigmaDist_fullSupport S f' hSfs hf'fs
    haveI :
        Nonempty ((ka : (k : K) × twoGroupingFiber U V k) ×
          twoGroupingFiber U V ka.1) :=
      ⟨⟨Classical.choice inferInstance, Classical.choice inferInstance⟩⟩
    have hSnd : ¬ Subsingleton ((k : K) × twoGroupingFiber U V k) :=
      not_subsingleton_sigma hKnd
    -- Exact relabeling identifies the two presentations: Z(T') = Z(T).
    have hHrel :
        fullRevelationValueForFaceScales hfaces
            (Relabeling.relabelDist (twoGroupingReassoc U V) T') =
          fullRevelationValueForFaceScales hfaces T' :=
      fullRevelationValueForFaceScales_relabel_eq hrelV hax hfaces
        (twoGroupingReassoc U V) T'
    have hTeq : Relabeling.relabelDist (twoGroupingReassoc U V) T' = T :=
      relabelDist_twoGroupingReassoc u v
    have hZTT' : productScaleZForFaceScales hfaces hprod hax T = productScaleZForFaceScales hfaces hprod hax T' := by
      unfold productScaleZForFaceScales
      rw [← hTeq, hHrel]
    -- Weight recursion, coarse grouping: E1 before multiplicativity.
    have hrecT :=
      hrec.weight_recursion hax
        (fun k : K => twoGroupingFiber U V k × twoGroupingFiber U V k)
        p₂ f hp₂fs hffs hTfs hKnd hfnd
    -- Weight recursion, fine grouping and its coarse marginal.
    have hrecT' :=
      hrec.weight_recursion hax
        (fun ka : (k : K) × twoGroupingFiber U V k =>
          twoGroupingFiber U V ka.1)
        S f' hSfs hf'fs hT'fs hSnd hf'nd
    have hrecS :=
      hrec.weight_recursion hax (twoGroupingFiber U V)
        p₂ g hp₂fs hgfs hSfs hKnd hgnd
    -- Abbreviations for the two weights.
    set x := (productScaleZForFaceScales hfaces hprod hax u)⁻¹ with hx
    set y := (productScaleZForFaceScales hfaces hprod hax v)⁻¹ with hy
    -- The coarse sum: Σ p₂ k · w(f k) = (x² + y²)/2, via multiplicativity.
    have hsum_f :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹) = (x ^ 2 + y ^ 2) / 2 := by
      rw [sum_universalScaleReferenceType
        (fun k => p₂ k * (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹)]
      have hZff : productScaleZForFaceScales hfaces hprod hax (f (ULift.up false)) = productScaleZForFaceScales hfaces hprod hax u * productScaleZForFaceScales hfaces hprod hax u := by
        show productScaleZForFaceScales hfaces hprod hax
            (prodDist u u) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax u u hu hu
      have hZft : productScaleZForFaceScales hfaces hprod hax (f (ULift.up true)) = productScaleZForFaceScales hfaces hprod hax v * productScaleZForFaceScales hfaces hprod hax v := by
        show productScaleZForFaceScales hfaces hprod hax
            (prodDist v v) = _
        exact productScaleZForFaceScales_prod_eq hfaces hprod hax v v hv hv
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply,
        hZff, hZft, mul_inv, mul_inv]
      show 1 / 2 * ((productScaleZForFaceScales hfaces hprod hax u)⁻¹ * (productScaleZForFaceScales hfaces hprod hax u)⁻¹) + 1 / 2 * ((productScaleZForFaceScales hfaces hprod hax v)⁻¹ * (productScaleZForFaceScales hfaces hprod hax v)⁻¹) = _
      rw [← hx, ← hy]
      ring
    -- The fine sums: both marginal sums are (x + y)/2.
    have hsum_g :
        (∑ k, p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) = (x + y) / 2 := by
      rw [sum_universalScaleReferenceType (fun k => p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹)]
      rw [universalScaleReferencePrior_apply, universalScaleReferencePrior_apply]
      show 1 / 2 * (productScaleZForFaceScales hfaces hprod hax u)⁻¹ + 1 / 2 * (productScaleZForFaceScales hfaces hprod hax v)⁻¹ = _
      rw [← hx, ← hy]
      ring
    have hsum_f' :
        (∑ ka : (k : K) × twoGroupingFiber U V k,
          S ka * (productScaleZForFaceScales hfaces hprod hax (f' ka))⁻¹) = (x + y) / 2 := by
      rw [Fintype.sum_sigma]
      have hterm :
          ∀ k, (∑ a : twoGroupingFiber U V k,
              S ⟨k, a⟩ * (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹) =
            p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
        intro k
        have : ∀ a : twoGroupingFiber U V k,
            S ⟨k, a⟩ * (productScaleZForFaceScales hfaces hprod hax (f' ⟨k, a⟩))⁻¹ =
              p₂ k * (g k) a * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ := by
          intro a
          show (sigmaDist p₂ g) ⟨k, a⟩ * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹ = _
          rw [sigmaDist_apply]
        rw [Finset.sum_congr rfl (fun a _ => this a)]
        have hfactor :
            (∑ a : twoGroupingFiber U V k,
              p₂ k * (g k) a * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) =
              (p₂ k * (productScaleZForFaceScales hfaces hprod hax (g k))⁻¹) * (∑ a, (g k) a) := by
          rw [Finset.mul_sum]
          congr 1
          ext a
          ring
        rw [hfactor, (g k).sum_eq_one, mul_one]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      exact hsum_g
    -- Reference weight is positive.
    have hZp₂pos : 0 < productScaleZForFaceScales hfaces hprod hax p₂ := hpos.Z_pos hax p₂ hp₂fs
    -- Assemble E1 and E2 with wT := w(T), wp := w(p₂).
    refine ⟨(productScaleZForFaceScales hfaces hprod hax T)⁻¹, (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹, inv_pos.mpr hZp₂pos, ?_, ?_⟩
    · -- E1: coarse grouping.
      rw [show (productScaleZForFaceScales hfaces hprod hax T)⁻¹ =
          (productScaleZForFaceScales hfaces hprod hax (sigmaDist p₂ f))⁻¹
        from rfl]
      rw [hrecT, hsum_f]
    · -- E2: fine grouping + coarse marginal, transported by relabeling.
      have hE2' :
          (productScaleZForFaceScales hfaces hprod hax T')⁻¹ = (productScaleZForFaceScales hfaces hprod hax p₂)⁻¹ * (((x + y) / 2) ^ 2) := by
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

/-- Sharper source-ready grouping bridge.

The paper's finite partition/disjoint-union grouping argument first makes the
`Z` weight independent of the nondegenerate full-support prior, and then fixes
that common value by a reference normalization.  This structure records those
two pieces separately from the downstream cancellation to `kappa = 0`. -/
structure FiniteProductGroupingReferenceWeightAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  Z_eq_reference_of_grouping :
    ∀ (hax : TraceAxioms F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hA : ¬ Subsingleton A),
      productScaleZForFaceScales hfaces hprod hax q =
        productScaleZForFaceScales hfaces hprod hax
          universalScaleReferencePrior
  reference_Z_eq_one :
    ∀ (hax : TraceAxioms F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- Reconstruct the old weight-constant package from the sharper grouping
reference-weight bridge. -/
theorem productGroupingWeightConstant_of_reference
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod) :
    FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod where
  Z_eq_one_of_nondegenerate := by
    intro hax A _ _ _ q hq hA
    calc
      productScaleZForFaceScales hfaces hprod hax q =
          productScaleZForFaceScales hfaces hprod hax
            universalScaleReferencePrior :=
        hgroup.Z_eq_reference_of_grouping hax q hq hA
      _ = 1 := hgroup.reference_Z_eq_one hax

/-- **Repaired grouping equation ⟹ reference-weight package.**

The paper's two-grouping evaluations plus `Z`-positivity reconstruct the
reference-weight package that the interaction-collapse constructor consumes.
The `Z`-equal-to-reference field is the two-grouping cancellation
(`productScaleZ_eq_of_twoGrouping`); the reference normalization is supplied
directly.  This is the faithful reduction of the grouping equation: everything
downstream of the paper's two evaluations is now proved in Lean. -/
theorem productGroupingReferenceWeight_of_twoGroupingWeightEquation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod where
  Z_eq_reference_of_grouping := by
    intro hax A _ _ _ q hq hA
    exact productScaleZ_eq_of_twoGrouping hgroup hpos hax q
      universalScaleReferencePrior hq universalScaleReferencePrior_fullSupport
      hA universalScaleReference_not_subsingleton
  reference_Z_eq_one := hgroup.reference_Z_eq_one

/-- The final algebraic cancellation in Step 3: if the grouping argument makes
`Z` identically one on nondegenerate full-support priors, then `kappa = 0`. -/
theorem twoGroupingInteractionCollapse_of_weightConstant
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod) :
    FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod where
  kappa_eq_zero := by
    intro hax
    let q0 : Dist universalScaleReferenceType := universalScaleReferencePrior
    have hq0 : q0.FullSupport := universalScaleReferencePrior_fullSupport
    have hRef : ¬ Subsingleton universalScaleReferenceType :=
      universalScaleReference_not_subsingleton
    have hZ :=
      hweight.Z_eq_one_of_nondegenerate hax q0 hq0 hRef
    have hH_ne :
        fullRevelationValueForFaceScales hfaces q0 ≠ 0 :=
      fullRevelationValueForFaceScales_ne_zero_of_A1
        hfaces hax q0 hq0 hRef
    have hkH :
        hprod.kappa hax * fullRevelationValueForFaceScales hfaces q0 = 0 := by
      unfold productScaleZForFaceScales at hZ
      linarith
    exact (mul_eq_zero.mp hkH).resolve_right hH_ne

/-- Product-revelation scale links plus `kappa = 0` imply universal scale on
nondegenerate full-support priors. -/
theorem scale_eq_of_productRevelation_and_interactionCollapse
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hfaces.branch_result.scale_factorization.scale q =
      hfaces.branch_result.scale_factorization.scale r := by
  have hleft :=
    hlink.scale_product_left hax q r hq hr hA hB
  have hright :=
    hlink.scale_product_right hax q r hq hr hA hB
  have hleft' :
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        hfaces.branch_result.scale_factorization.scale r := by
    simpa [hcollapse.kappa_eq_zero hax] using hleft
  have hright' :
      hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        hfaces.branch_result.scale_factorization.scale q := by
    simpa [hcollapse.kappa_eq_zero hax] using hright
  exact hright'.symm.trans hleft'

/-- Universal scale for all full-support priors from the nondegenerate product
argument plus the singleton/degenerate normalization. -/
theorem scale_universal_of_productRevelation_and_interactionCollapse
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hfaces.branch_result.scale_factorization.scale q =
      hfaces.branch_result.scale_factorization.scale r := by
  by_cases hA : Subsingleton A
  · exact hsingle.scale_eq_of_subsingleton q r hq hr (Or.inl hA)
  · by_cases hB : Subsingleton B
    · exact hsingle.scale_eq_of_subsingleton q r hq hr (Or.inr hB)
    · exact scale_eq_of_productRevelation_and_interactionCollapse
        hfaces hprod hlink hcollapse hax q r hq hr hA hB

/-- Reassemble the public `ScaleCoherenceStructure` from faithful face scales
and the sharp interaction-collapse components. -/
noncomputable def scaleCoherence_of_faceScales_interactionCollapse
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    ScaleCoherenceStructure F where
  branch_agg := hfaces.branch_result.branch_agg
  scale := hfaces.branch_result.scale_factorization.scale
  scale_pos := hfaces.branch_result.scale_factorization.scale_pos
  branchCoeff_factorization :=
    hfaces.branch_result.scale_factorization.branchCoeff_factorization
  scale_universal := by
    intro A B _ _ _ _ _ _ q r hq hr
    exact scale_universal_of_productRevelation_and_interactionCollapse
      hfaces hprod hlink hcollapse hsingle hax q r hq hr

/-- Faithful output package for "Interaction collapse and universal chain
scale". -/
structure InteractionCollapseUniversalChainScaleStructure
    (F : PrefFamily.{u}) where
  face_scales : CoherentRelabelingFaceScalesStructure F
  product_quasi_add :
    FiniteProductQuasiAdditivityForFaceScales face_scales
  scale_coherence : ScaleCoherenceStructure F
  interaction_collapse :
    ∀ (hax : TraceAxioms F), product_quasi_add.kappa hax = 0

namespace InteractionCollapseUniversalChainScaleStructure

/-- The universal chain-scale output. -/
theorem scale_universal
    {F : PrefFamily.{u}}
    (h : InteractionCollapseUniversalChainScaleStructure F)
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    h.scale_coherence.scale q = h.scale_coherence.scale r :=
  h.scale_coherence.scale_universal q r hq hr

/-- Product additivity after the interaction coefficient collapses. -/
theorem product_additivity
    {F : PrefFamily.{u}}
    (h : InteractionCollapseUniversalChainScaleStructure F)
    (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    h.face_scales.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      h.face_scales.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel P) +
      h.face_scales.branch_result.branch_agg.value_rep.V r
        (experimentOfChannel R) := by
  have hqa :=
    h.product_quasi_add.product_quasi_add hax q r hq hr P R
  simpa [h.interaction_collapse hax] using hqa

end InteractionCollapseUniversalChainScaleStructure

/-- Faithful theorem statement for "Interaction collapse and universal chain
scale". -/
noncomputable def InteractionCollapseUniversalScale_of_faithfulFaceScales
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hlink : FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod)
    (hcollapse : FiniteTwoGroupingInteractionCollapseAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F where
  face_scales := hfaces
  product_quasi_add := hprod
  scale_coherence :=
    scaleCoherence_of_faceScales_interactionCollapse
      hfaces hprod hlink hcollapse hsingle hax
  interaction_collapse := hcollapse.kappa_eq_zero

/-- Stage 27 reassembler for "Interaction collapse and universal chain
scale" using the sharper product-revelation and two-grouping inputs. -/
noncomputable def InteractionCollapseUniversalScale_of_decomposedProductBridges
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hseq : FiniteProductRevelationSequentialScaleAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_faithfulFaceScales
    hfaces hprod
    (productRevelationScaleLink_of_sequentialScale hfaces hprod hseq)
    (twoGroupingInteractionCollapse_of_weightConstant hfaces hprod hweight)
    hsingle hax

/-- Stage 28 reassembler using the normalized-chain full-revelation form of
the product-revelation Step 1 bridge. -/
noncomputable def InteractionCollapseUniversalScale_of_normalizedSequentialProduct
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hnorm :
      FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_decomposedProductBridges
    hfaces hprod
    (productRevelationSequentialScale_of_normalizedChain hfaces hnorm)
    hweight hsingle hax

/-- Stage 29 reassembler using the coordinate-reveal value and continuation
transport pieces directly. -/
noncomputable def InteractionCollapseUniversalScale_of_coordinateRevealTransports
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hvalue : FiniteCoordinateRevealValueTransportAssumptionsFor hfaces)
    (hcont :
      FiniteCoordinateRevealContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_normalizedSequentialProduct
    hfaces hprod
    (sequentialFullRevelationNormalizedChain_of_coordinateTransports
      hfaces hvalue hcont)
    hweight hsingle hax

/-- Stage 30 reassembler using the sharper coordinate transport pieces. -/
noncomputable def InteractionCollapseUniversalScale_of_coordinateTransportPieces
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hmarg :
      FiniteCoordinateRevealMarginalValueTransportAssumptionsFor hfaces)
    (hswap :
      FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces)
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_coordinateRevealTransports
    hfaces hprod
    (coordinateRevealValueTransport_of_marginal_and_swap hmarg hswap)
    (coordinateRevealContinuationTransport_of_branchTransport hbranch)
    hweight hsingle hax

/-- Stage IC cleanup reassembler: the marginal coordinate-reveal value
transport is derived internally from product quasi-additivity, so this
constructor takes only the swap and coordinate-face continuation transports as
coordinate residuals. -/
noncomputable def InteractionCollapseUniversalScale_of_productQuasiAndCoordinatePieces
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hswap :
      FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces)
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_coordinateTransportPieces
    hfaces hprod
    (coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
      hfaces hprod)
    hswap hbranch hweight hsingle hax

/-- Stage IC all-residual cleanup reassembler: both coordinate-reveal marginal
value transport and swapped full-revelation transport are internal, so the only
coordinate residual left is pointwise coordinate-face continuation transport. -/
noncomputable def InteractionCollapseUniversalScale_of_productQuasiAndBranchContinuation
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_productQuasiAndCoordinatePieces
    hfaces hprod
    (coordinateSwapFullRevelationValueTransport_of_posteriorLaw hfaces)
    hbranch hweight hsingle hax

/-- Minimal current faithful reassembler for the interaction-collapse route
after the coordinate-reveal cleanup.

The swap full-revelation and marginal coordinate-reveal value transports are
internal.  The coordinate continuation residual is reduced to the two exact
support-face transports: value representatives and chain scales. -/
noncomputable def InteractionCollapseUniversalScale_of_minimalResiduals
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hcoordValue :
      FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces)
    (hweight : FiniteProductGroupingWeightConstantAssumptionsFor hfaces hprod)
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_productQuasiAndBranchContinuation
    hfaces hprod
    (coordinateRevealBranchContinuationTransport_of_coordinateSupportFaceTransports
      hcoordValue hcoordScale)
    hweight hsingle hax

/-- Interaction-collapse reassembler using the non-circular face-scale product
components instead of the already assembled product quasi-additivity package. -/
noncomputable def InteractionCollapseUniversalScale_of_productComponents
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hnorm :
      FiniteFaceScaleProductGaugeNormalizationAssumptionsFor hpair)
    (huniv :
      FiniteFaceScaleProductInteractionUniversalityAssumptionsFor hpair)
    (hcoordValue :
      FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces)
    (hweight :
      FiniteProductGroupingWeightConstantAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_components
          hpair hnorm huniv))
    (hsingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_components hpair hnorm huniv)
    hcoordValue hcoordScale hweight hsingle hax

/-- Final current interaction-collapse constructor.

This uses the smallest named product and coordinate components currently
available in this file: explicit product current-gauge normalization,
interaction K-associativity plus singleton normalization, and coordinate
support-face representative/scale normalizations. -/
noncomputable def InteractionCollapseUniversalScale_of_finalComponents
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hpair :
      FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hgauge : FiniteFaceScaleCurrentProductGaugeNormalizationFor hpair)
    (hassoc :
      FiniteFaceScaleProductInteractionAssociativityAssumptionsFor hpair)
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor hpair)
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hweight :
      FiniteProductGroupingWeightConstantAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_finalProductComponents
          hpair hgauge hassoc hinterSingle))
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_finalProductComponents
      hpair hgauge hassoc hinterSingle)
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    hweight hunivSingle hax

/-- Interaction-collapse constructor using the multi-stage source-ready
components instead of the broader pairwise, interaction-associativity, and
weight-constant packages. -/
noncomputable def InteractionCollapseUniversalScale_of_multiClosedComponents
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hintercept :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform haff))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope))
    (htriple :
      FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor hfaces)
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        htriple)
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_multiPieces
          haff hintercept hslope))
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hweight :
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_multiComponents
          haff hintercept hslope hgauge htriple hextract hinterSingle))
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_multiComponents
      haff hintercept hslope hgauge htriple hextract hinterSingle)
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    (productGroupingWeightConstant_of_reference hweight)
    hunivSingle hax

/-- Closed-local left-slice affine transform constructor.

This removes the old face-scale-specific affine-utility uniqueness package from
the interaction-collapse API: the non-singleton case is supplied by the single
classical finite affine-utility uniqueness theorem, and nonconstancy is internal
from A1. -/
theorem faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces :=
  faceScaleProductLeftSliceAffineTransform_of_parts
    hbaseAff hsliceAff hsameOrder
    (faceScaleBaseValueNonconstancy_of_A1 hfaces)
    hsingle
    (classicalFaceScaleAffineUtilityUniqueness_of_finiteAffineUtility huniq)

/-- Closed-local pairwise bilinearity constructor.

This keeps the second-coordinate intercept uniqueness and slope-affinity theorem
pieces explicit, but no longer requires an intercept-zero interface: zero is
proved internally from subsingleton no-information value normalization. -/
noncomputable def faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hinterceptOrder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptAff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptUniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq))) :
    FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces :=
  let haff :=
    faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
      hbaseAff hsliceAff hsameOrder hsingle huniq
  let hlin :=
    faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
      hinterceptOrder hinterceptAff hinterceptUniq
  faceScaleProductPairwiseBilinearity_of_multiPieces haff hlin hslope

/-- Product quasi-additivity from the closed-local IC theorem pieces.

The triple-product value associativity package is no longer an explicit input;
it is reconstructed from exact relabeling of posterior-value representatives. -/
noncomputable def productQuasiAdditivityForFaceScales_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hinterceptOrder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptAff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptUniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        (faceScaleTripleProductValueAssociativity_of_valueRelabeling
          hfaces hrelV))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope)) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  let haff :=
    faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
      hbaseAff hsliceAff hsameOrder hsingle huniq
  let hlin :=
    faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
      hinterceptOrder hinterceptAff hinterceptUniq
  productQuasiAdditivityForFaceScales_of_multiComponents
    haff hlin hslope hgauge
    (faceScaleTripleProductValueAssociativity_of_valueRelabeling hfaces hrelV)
    hextract hinterSingle

/-- Family-level product representation theorem for the pre-universal
face-scale layer.

This is deliberately not another local interface for one residual.  It groups
the remaining HM/product-coordinate content behind coherent product
quasi-additivity: public-mix affinity, product-coordinate order transport,
intercept/slope affine uniqueness, and triple-product coefficient extraction.
It replaces seven local theorem externals plus the coefficient-extraction
external in the public interaction-collapse constructor. -/
structure FiniteFaceScaleProductRepresentationTheoremAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  base_publicMix :
    FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces
  coordinate_publicMix :
    FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces
  left_slice_same_order :
    FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces
  intercept_same_order :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  intercept_publicMix :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  second_coordinate_uniqueness :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  slope_affine :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v}),
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq))
  triple_coeff_extraction :
    ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
      (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{v})
      (hgauge :
        FiniteFaceScaleCurrentProductGaugeNormalizationFor
          (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
            base_publicMix coordinate_publicMix left_slice_same_order
            hsingle huniq
            (intercept_same_order hsingle huniq)
            (intercept_publicMix hsingle huniq)
            (second_coordinate_uniqueness hsingle huniq)
            (slope_affine hsingle huniq)))
      (hrelV : FinitePosteriorValueRelabelingAssumptions.{v}),
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          base_publicMix coordinate_publicMix left_slice_same_order
          hsingle huniq
          (intercept_same_order hsingle huniq)
          (intercept_publicMix hsingle huniq)
          (second_coordinate_uniqueness hsingle huniq)
          (slope_affine hsingle huniq))
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        (faceScaleTripleProductValueAssociativity_of_valueRelabeling
          hfaces hrelV)

/-- Product quasi-additivity reconstructed from the family-level product
representation theorem. -/
noncomputable def productQuasiAdditivityForFaceScales_of_productRepresentation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprodRep :
      FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq)))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq))) :
    FiniteProductQuasiAdditivityForFaceScales hfaces :=
  productQuasiAdditivityForFaceScales_of_closedLocalTheorems
    hprodRep.base_publicMix
    hprodRep.coordinate_publicMix
    hprodRep.left_slice_same_order
    hsingle huniq
    (hprodRep.intercept_same_order hsingle huniq)
    (hprodRep.intercept_publicMix hsingle huniq)
    (hprodRep.second_coordinate_uniqueness hsingle huniq)
    (hprodRep.slope_affine hsingle huniq)
    hgauge hrelV
    (hprodRep.triple_coeff_extraction hsingle huniq hgauge hrelV)
    hinterSingle

/-- Family-level grouping equation theorem.

This replaces the local `FiniteProductGroupingReferenceWeightAssumptionsFor`
for each product-quasi-additivity package.  The intended proof is the paper's
finite partition/disjoint-union grouping equation, followed by the already
internal reference-weight algebra. -/
structure FiniteProductGroupingEquationAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  reference_weight :
    ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod

/-- Reference-weight package reconstructed from the family-level grouping
equation theorem. -/
theorem productGroupingReferenceWeight_of_groupingEquation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hgroup :
      FiniteProductGroupingEquationAssumptionsFor hfaces)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) :
    FiniteProductGroupingReferenceWeightAssumptionsFor hfaces hprod :=
  hgroup.reference_weight hprod

/-- Cleanest current interaction-collapse constructor after local closure.

Compared with `InteractionCollapseUniversalScale_of_multiClosedComponents`, this
does not expose the old intercept-zero, face-scale-specific affine-uniqueness,
or triple-product value-associativity packages.  Remaining theorem inputs are
the public-mix/order/slope/coefficient/grouping statements that have not been
proved locally, plus explicit gauge/support-face/singleton normalizations. -/
noncomputable def InteractionCollapseUniversalScale_of_closedLocalTheorems
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hbaseAff :
      FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces)
    (hsliceAff :
      FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces)
    (hsameOrder :
      FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hinterceptOrder :
      FiniteFaceScaleProductInterceptSameOrderAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptAff :
      FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hinterceptUniq :
      ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hslope :
      FiniteFaceScaleProductSlopeAffineAssumptionsFor
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            hbaseAff hsliceAff hsameOrder hsingle huniq)))
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hextract :
      FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope)
        (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
        (faceScaleTripleProductValueAssociativity_of_valueRelabeling
          hfaces hrelV))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope))
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hweight :
      FiniteProductGroupingReferenceWeightAssumptionsFor hfaces
        (productQuasiAdditivityForFaceScales_of_closedLocalTheorems
          hbaseAff hsliceAff hsameOrder hsingle huniq
          hinterceptOrder hinterceptAff hinterceptUniq hslope
          hgauge hrelV hextract hinterSingle))
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces
    (productQuasiAdditivityForFaceScales_of_closedLocalTheorems
      hbaseAff hsliceAff hsameOrder hsingle huniq
      hinterceptOrder hinterceptAff hinterceptUniq hslope
      hgauge hrelV hextract hinterSingle)
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    (productGroupingWeightConstant_of_reference hweight)
    hunivSingle hax

/-- Total-closure interaction-collapse constructor.

This is the strictest current API: the nine remaining local theorem externals
are not exposed.  They are replaced by two family-level theorem assumptions:
one coherent product-representation theorem and one finite grouping-equation
theorem.  Existing global classical/relabeling inputs remain explicit. -/
noncomputable def InteractionCollapseUniversalScale_of_totalClosure
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprodRep :
      FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces)
    (hsingle :
      FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq)))
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          hprodRep.base_publicMix
          hprodRep.coordinate_publicMix
          hprodRep.left_slice_same_order
          hsingle huniq
          (hprodRep.intercept_same_order hsingle huniq)
          (hprodRep.intercept_publicMix hsingle huniq)
          (hprodRep.second_coordinate_uniqueness hsingle huniq)
          (hprodRep.slope_affine hsingle huniq)))
    (hcoordValue :
      FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale :
      FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hgroup :
      FiniteProductGroupingEquationAssumptionsFor hfaces)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  let hprod :=
    productQuasiAdditivityForFaceScales_of_productRepresentation
      hprodRep hsingle huniq hgauge hrelV hinterSingle
  InteractionCollapseUniversalScale_of_minimalResiduals
    hfaces hprod
    (coordinateSupportFaceValueTransport_of_identification hcoordValue)
    (coordinateSupportFaceScaleTransport_of_identification hcoordScale)
    (productGroupingWeightConstant_of_reference
      (productGroupingReferenceWeight_of_groupingEquation hgroup hprod))
    hunivSingle hax

/-- Family-level grouping equation reconstructed from the repaired two-grouping
weight equation plus `Z`-positivity.

This exposes the honest remaining product-grouping content — the paper's
two-grouping evaluations (E1)/(E2) and the positive-slice-slope condition
(POS) — instead of the opaque reference-weight package.  Everything downstream
(the `(x−y)²=0` cancellation, `Z ≡ 1`, `κ = 0`) is now proved in Lean. -/
theorem finiteProductGroupingEquation_of_twoGroupingWeightEquation
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hgroup :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FiniteProductGroupingEquationAssumptionsFor hfaces where
  reference_weight := fun hprod =>
    productGroupingReferenceWeight_of_twoGroupingWeightEquation
      (hgroup hprod) (hpos hprod)

/-- **Family-level grouping equation from the pre-universal weight recursion.**

POS is discharged internally (`productScaleZpositive_of_sliceTransform`), and
the two-grouping evaluations E1/E2 are derived from the weight recursion (W)
(`finiteProductTwoGroupingWeightEquation_of_weightRecursion`).  The remaining
product-grouping input is exactly the paper's weight equation (W). -/
theorem finiteProductGroupingEquation_of_weightRecursion
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hrec :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod) :
    FiniteProductGroupingEquationAssumptionsFor hfaces :=
  finiteProductGroupingEquation_of_twoGroupingWeightEquation
    (fun hprod =>
      finiteProductTwoGroupingWeightEquation_of_weightRecursion hrelV
        (hrec hprod)
        (productScaleZpositive_of_sliceTransform hprod haff))
    (fun hprod => productScaleZpositive_of_sliceTransform hprod haff)

/-!
## Scale Coherence External Assumption

The scale coherence theorem states that given branch aggregation coefficients β(q,r):

1. **Cocycle**: β(q,s) = β(q,r) β(r,s) for nested supports
2. **Factorization**: β(q,r) = a_q/a_r where a_q := 1/β(q₀, q) for fixed basepoint q₀
3. **Universal scale**: The two-grouping argument (using A8) shows a_q = a is
   independent of q across all full-support priors on all finite action sets

Paper proof sketch (Lemma scalecoherence, lines 2347-2500):
1. Define H(q) := F_q(χ_q) (full revelation value) and Z(q) := 1 + κH(q)
2. Product revelation: reveal A first, then B in each branch
3. Compare with quasi-additivity to get a_{q⊗r}/a_r = Z(q)
4. Symmetry gives a_q = C·Z(q) for universal C > 0
5. Two-grouping argument via A8 forces κ = 0, hence Z ≡ 1
6. Therefore a_q = C is universal
-/

/--
**Finite Scale Coherence Assumptions**

External assumption that branch aggregation coefficients satisfy cocycle/factorization
properties and that the scale is universal across all full-support priors.

Paper: Lemmas chain, facescales, scalecoherence (lines 2108-2500).

**Key mathematical content:**
- Cocycle: β(q,s) = β(q,r) β(r,s)
- Factorization: β(q,r) = a_q/a_r
- Universal scale: a_q = a for all full-support q (via two-grouping + A8)

This is a data-carrying structure because it provides the scale function.
-/
structure FiniteScaleCoherenceAssumptions.{v} where
  /-- Given branch aggregation structure, construct scale coherence structure.
      This packages Lemmas chain + facescales + scalecoherence. -/
  of_branch_aggregation :
    ∀ (F : PrefFamily.{v}),
      BranchAggregationStructure F →
      ScaleCoherenceStructure F

/-!
## Bridge Theorems

These theorems show how to use the scale coherence assumption in the
sufficiency spine.
-/

/--
**Scale Coherence from Assumption**

Given the external scale coherence assumption and a branch aggregation structure,
derive a scale coherence structure.
-/
noncomputable def scaleCoherence_of_assumption
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (F : PrefFamily.{u})
    (hbranch : BranchAggregationStructure F) :
    ScaleCoherenceStructure F :=
  hscale.of_branch_aggregation F hbranch

/--
**Scale Coherence from All External Assumptions**

Given all four external assumptions (Blackwell, Herstein-Milnor, Branch Aggregation,
Scale Coherence) and TraceAxioms, derive a scale coherence structure.

This composes the first four sufficiency bridges:
1. TraceAxioms → PosteriorLawSufficiency (via Blackwell)
2. PosteriorLawSufficiency → PosteriorValueRepresentation (via Herstein-Milnor)
3. PosteriorValueRepresentation → BranchAggregationStructure (via Branch Aggregation)
4. BranchAggregationStructure → ScaleCoherenceStructure (via Scale Coherence)

Paper: Lemmas blockcoh--blackwell + postsep + branchagg + chain + scalecoherence
(lines 810-2500).
-/
noncomputable def scaleCoherence_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hax : TraceAxioms F) :
    ScaleCoherenceStructure F :=
  let hbranchStruct := branchAggregation_of_axioms F hblackwell hhm hbranch hax
  hscale.of_branch_aggregation F hbranchStruct

/-!
## Spine Integration Helper

Shows how to fill the `branch_to_scale` field of `SufficiencySpineAssumptions`.
-/

/--
**Branch to Scale Bridge**

Given the scale coherence external assumption, provides the bridge
from BranchAggregationStructure to ScaleCoherenceStructure.

This can be used to fill the `branch_to_scale` field when constructing
`SufficiencySpineAssumptions`.
-/
noncomputable def branch_to_scale_of_assumption
    (hscale : FiniteScaleCoherenceAssumptions.{u}) :
    ∀ F : PrefFamily.{u}, BranchAggregationStructure F → ScaleCoherenceStructure F :=
  fun F hbranch => hscale.of_branch_aggregation F hbranch

end TraceableAgency
