/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Proof.Branch
import TraceableAgency.PureTrace.Proof.ProductGauge
import TraceableAgency.PureTrace.Support.EntropyReductionClosure

namespace TraceableAgency

universe u

/-!
# Coherent face scales from the direct branch construction

This file performs only scale selection.  In particular, the cardinal
alignment below leaves the selected posterior-value representative and the
branch coefficients unchanged.
-/

/-! ## Tangents carried by a support inclusion -/

/-- Pointwise formula for the deterministic inclusion of a support-face
distribution into its ambient simplex. -/
theorem directActionPushforward_supportInclude_apply
    {A : Type u} [Fintype A] [DecidableEq A]
    (r : Dist A) (d : Dist (supportSubtype r)) (a : A) :
    Channel.actionPushforward d (supportIncludeKernel r) a =
      if h : r a > 0 then d ⟨a, h⟩ else 0 := by
  classical
  unfold Channel.actionPushforward supportIncludeKernel
  change (∑ c : supportSubtype r, d c * (Dist.pure c.1) a) =
    if h : r a > 0 then d ⟨a, h⟩ else 0
  by_cases hra : r a > 0
  · rw [dif_pos hra]
    let b : supportSubtype r := ⟨a, hra⟩
    rw [Finset.sum_eq_single b]
    · simp [b]
    · intro c _ hcb
      have hne : c.1 ≠ a := by
        intro hca
        exact hcb (Subtype.ext hca)
      rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ b) hb
  · rw [dif_neg hra]
    apply Finset.sum_eq_zero
    intro c _
    have hne : c.1 ≠ a := by
      intro hca
      exact hra (hca ▸ c.2)
    rw [Dist.pure_apply_ne c.1 a (fun h => hne h.symm), mul_zero]

/-- Inclusion pushforward preserves atomic linearity. -/
noncomputable def directAtomicLinear_pushSignedIncl
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A) [Nonempty (supportSubtype r)]
    {eta : PosteriorLawSigned (supportSubtype r)}
    (heta : PosteriorLawSigned.AtomicLinear eta) :
    PosteriorLawSigned.AtomicLinear (directPushSignedIncl r eta) where
  witness := by
    letI : Fintype heta.witness.I := heta.witness.instFintypeI
    letI : DecidableEq heta.witness.I := heta.witness.instDecidableEqI
    exact
      { I := heta.witness.I
        instFintypeI := inferInstance
        instDecidableEqI := inferInstance
        weight := heta.witness.weight
        point := fun i => Channel.actionPushforward
          (heta.witness.point i) (supportIncludeKernel r) }
  eval_eq := by
    letI : Fintype heta.witness.I := heta.witness.instFintypeI
    letI : DecidableEq heta.witness.I := heta.witness.instDecidableEqI
    funext phi
    show (∑ i : heta.witness.I, heta.witness.weight i *
        phi (Channel.actionPushforward
          (heta.witness.point i) (supportIncludeKernel r))) =
      eta (fun d => phi
        (Channel.actionPushforward d (supportIncludeKernel r)))
    have h := congrFun heta.eval_eq (fun d =>
      phi (Channel.actionPushforward d (supportIncludeKernel r)))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- Atomic form of the ambient-to-face scalar relation used below. -/
structure AtomicBoundaryLinearPartRelationFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u}) : Prop where
  relation :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A), q.FullSupport →
      [Nonempty (supportSubtype r)] →
      (∃ a : A, 0 < r a) →
      (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) →
      ¬ r.FullSupport →
      ∀ (eta : PosteriorLawSigned (supportSubtype r)),
      PosteriorLawSigned.AtomicLinear eta →
      PosteriorLawTangent eta →
      hlin.linearPart F hV q (directPushSignedIncl r eta) =
        hboundary.boundaryCoeff q r *
          hlin.linearPart F hV r.restrictToSupport eta

/-- The direct affine linear part satisfies the atomic boundary relation. -/
noncomputable def directAtomicBoundaryLinearPartRelation
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    AtomicBoundaryLinearPartRelationFor F hax hV
      finiteAffineLinearPartAssumptions_of_posteriorValue
      (directBoundaryFaceScale F hax hV) where
  relation := by
    intro A _ _ _ q r hq _ _hrn hrnd _hrb eta hetaAtomic hetaTan
    have hrsnd : ∃ a b : supportSubtype r, a ≠ b ∧
        0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
      obtain ⟨a, b, hab, ha, hb⟩ := hrnd
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩,
        by intro h; exact hab (congrArg Subtype.val h),
        by simpa [Dist.restrictToSupport_apply] using ha,
        by simpa [Dist.restrictToSupport_apply] using hb⟩
    exact boundaryAtomicLinearTangentCoeffOfA1Spanning_relation
      finiteAffineLinearPartAssumptions_of_posteriorValue
      directAtomicLinearTangentSpanning F hax hV
      q r hq hrsnd eta hetaAtomic hetaTan

/-- The direct full-support path coefficient is invariant under a finite
action relabelling when the selected value is exactly relabelling-covariant. -/
theorem directBranchPathCoeff_relabel
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hVrel :
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
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    (directBranchPathTangentScalar F hax hV).branchPathCoeff
        (Relabeling.relabelDist e q) (Dist.uniform (A := B)) =
      (directBranchPathTangentScalar F hax hV).branchPathCoeff
        q (Dist.uniform (A := A)) := by
  classical
  let hlin := finiteAffineLinearPartAssumptions_of_posteriorValue
  let hpath := directBranchPathTangentScalar F hax hV
  have hqB : (Relabeling.relabelDist e q).FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  have huni : Relabeling.relabelDist e (Dist.uniform (A := A)) =
      Dist.uniform (A := B) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply,
      Dist.uniform_apply, Fintype.card_congr e]
  by_cases hsub : Subsingleton A
  · haveI : Subsingleton B := Equiv.subsingleton e.symm
    have hnotA : ¬ ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b := by
      rintro ⟨a, b, hab, _, _⟩
      exact hab (Subsingleton.elim a b)
    have hnotB : ¬ ∃ a b : B, a ≠ b ∧
        0 < (Dist.uniform (A := B)) a ∧
        0 < (Dist.uniform (A := B)) b := by
      rintro ⟨a, b, hab, _, _⟩
      exact hab (Subsingleton.elim a b)
    simp only [hpath, directBranchPathTangentScalar,
      branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
      hq, hqB, Dist.uniform_fullSupport, dif_pos]
    rw [dif_neg hnotB, dif_neg hnotA]
  · rw [not_subsingleton_iff_nontrivial] at hsub
    obtain ⟨a, b, hab⟩ := hsub
    have hndA : ∃ a b : A, a ≠ b ∧
        0 < (Dist.uniform (A := A)) a ∧
        0 < (Dist.uniform (A := A)) b :=
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
    have hndB : ∃ a b : B, a ≠ b ∧
        0 < (Dist.uniform (A := B)) a ∧
        0 < (Dist.uniform (A := B)) b :=
      ⟨e a, e b, fun h => hab (e.injective h),
        Dist.uniform_fullSupport _, Dist.uniform_fullSupport _⟩
    obtain ⟨eta, hetaAtomic, hetaTan, hetaNe⟩ :=
      branch_linear_part_nonzero_atomicLinear_tangent_of_A1
        hlin F hax hV (Dist.uniform (A := A)) (Dist.uniform (A := A))
        Dist.uniform_fullSupport Dist.uniform_fullSupport hndA
    let etaB := relabelPosteriorLawSigned e eta
    have hetaBAtomic : PosteriorLawSigned.AtomicLinear etaB :=
      hetaAtomic.relabel e
    have hetaBTan : PosteriorLawTangent etaB := hetaTan.relabel e
    have hA := hpath.linear_part_scalar_relation_on_tangent
      q (Dist.uniform (A := A)) hq Dist.uniform_fullSupport
      hndA eta hetaAtomic hetaTan
    have hB := hpath.linear_part_scalar_relation_on_tangent
      (Relabeling.relabelDist e q) (Dist.uniform (A := B))
      hqB Dist.uniform_fullSupport hndB etaB hetaBAtomic hetaBTan
    have hnatQ := directPosteriorLawLinearMap_relabel_atomicTangent
      hV hVrel e q hq eta hetaAtomic hetaTan
    have hnatU := directPosteriorLawLinearMap_relabel_atomicTangent
      hV hVrel e (Dist.uniform (A := A)) Dist.uniform_fullSupport
      eta hetaAtomic hetaTan
    change directPosteriorLawLinearMap hV q eta =
      hpath.branchPathCoeff q (Dist.uniform (A := A)) *
        directPosteriorLawLinearMap hV (Dist.uniform (A := A)) eta at hA
    change directPosteriorLawLinearMap hV (Dist.uniform (A := A)) eta ≠ 0 at hetaNe
    rw [← huni] at hB
    change directPosteriorLawLinearMap hV (Relabeling.relabelDist e q) etaB =
      hpath.branchPathCoeff (Relabeling.relabelDist e q)
          (Relabeling.relabelDist e (Dist.uniform (A := A))) *
        directPosteriorLawLinearMap hV
          (Relabeling.relabelDist e (Dist.uniform (A := A))) etaB at hB
    dsimp [etaB] at hB
    rw [hnatQ, hnatU] at hB
    rw [huni] at hB
    exact mul_right_cancel₀ hetaNe (hB.symm.trans hA)

/-- Relabelling invariance of the selected raw direct scale. -/
theorem directSelectedBranchScale_relabel
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hVrel :
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
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport) :
    directSelectedBranchScale F hax hV (Relabeling.relabelDist e q) =
      directSelectedBranchScale F hax hV q := by
  rw [directSelectedBranchScale_fullSupport F hax hV _
      (Relabeling.relabelDist_fullSupport e q hq),
    directSelectedBranchScale_fullSupport F hax hV q hq]
  exact directBranchPathCoeff_relabel hax hV hVrel e q hq

/-- The face coefficient, divided by the within-simplex chain scale, is
independent of the full-support ambient prior.  This is the first cocycle
cancellation in the paper proof. -/
theorem boundaryCoeff_priorIndependent_of_atomicRelation
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hrel : AtomicBoundaryLinearPartRelationFor
      F hax hV hlin hboundary)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q q' r : Dist A) (hq : q.FullSupport) (hq' : q'.FullSupport)
    [Nonempty (supportSubtype r)]
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    hboundary.boundaryCoeff q r * hpath.branchPathCoeff q' q =
      hboundary.boundaryCoeff q' r := by
  classical
  have hrsnd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩,
      by intro h; exact hab (congrArg Subtype.val h),
      by simpa [Dist.restrictToSupport_apply] using ha,
      by simpa [Dist.restrictToSupport_apply] using hb⟩
  obtain ⟨eta, hetaAtomic, hetaTan, hetaNe⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV r.restrictToSupport r.restrictToSupport
      (Dist.restrictToSupport_fullSupport r)
      (Dist.restrictToSupport_fullSupport r) hrsnd
  have hqrel := hrel.relation q r hq hrn hrnd hrb
    eta hetaAtomic hetaTan
  have hq'rel := hrel.relation q' r hq' hrn hrnd hrb
    eta hetaAtomic hetaTan
  have hpushAtomic := directAtomicLinear_pushSignedIncl r hetaAtomic
  have hpushTan := directPushSignedIncl_tangent r hetaAtomic hetaTan
  have hpathrel := hpath.linear_part_scalar_relation_on_tangent
    q' q hq' hq
    (by
      obtain ⟨a, b, hab, _, _⟩ := hrnd
      exact ⟨a, b, hab, hq a, hq b⟩)
    (directPushSignedIncl r eta) hpushAtomic hpushTan
  rw [hqrel, hq'rel] at hpathrel
  have hcancel := mul_right_cancel₀ hetaNe (by
    calc
      hboundary.boundaryCoeff q' r *
          hlin.linearPart F hV r.restrictToSupport eta =
        hpath.branchPathCoeff q' q *
          (hboundary.boundaryCoeff q r *
            hlin.linearPart F hV r.restrictToSupport eta) := hpathrel
      _ = (hboundary.boundaryCoeff q r *
          hpath.branchPathCoeff q' q) *
            hlin.linearPart F hV r.restrictToSupport eta := by ring)
  linarith

/-! ## Relabelling the support square -/

/-- The positive support of a relabelled prior, with the orientation convenient
for transporting its restricted prior back to the original support. -/
noncomputable def directRelabelSupportEquiv
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (e : A ≃ B) (r : Dist A) :
    supportSubtype (Relabeling.relabelDist e r) ≃ supportSubtype r where
  toFun b := ⟨e.symm b.1, by
    simpa [Relabeling.relabelDist_apply] using b.2⟩
  invFun a := ⟨e a.1, by
    simpa [Relabeling.relabelDist_apply] using a.2⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

/-- Restriction to positive support commutes with a finite relabelling. -/
theorem directRestrictToSupport_relabelDist
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (e : A ≃ B) (r : Dist A) :
    (Relabeling.relabelDist e r).restrictToSupport =
      Relabeling.relabelDist (directRelabelSupportEquiv e r).symm
        r.restrictToSupport := by
  ext b
  rw [Dist.restrictToSupport_apply, Relabeling.relabelDist_apply,
    Relabeling.relabelDist_apply, Dist.restrictToSupport_apply]
  simp [directRelabelSupportEquiv]

/-- The deterministic support inclusion square commutes with relabelling. -/
theorem directPush_relabel_comm
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (r : Dist A)
    [Nonempty (supportSubtype r)]
    [Nonempty (supportSubtype (Relabeling.relabelDist e r))]
    (d : Dist (supportSubtype r)) :
    Channel.actionPushforward
        (Relabeling.relabelDist (directRelabelSupportEquiv e r).symm d)
        (supportIncludeKernel (Relabeling.relabelDist e r)) =
      Relabeling.relabelDist e
        (Channel.actionPushforward d (supportIncludeKernel r)) := by
  classical
  ext b
  have hL :
      (Channel.actionPushforward
        (Relabeling.relabelDist (directRelabelSupportEquiv e r).symm d)
        (supportIncludeKernel (Relabeling.relabelDist e r))) b =
      if h : (Relabeling.relabelDist e r) b > 0 then
        (Relabeling.relabelDist (directRelabelSupportEquiv e r).symm d)
          ⟨b, h⟩
      else 0 :=
    directActionPushforward_supportInclude_apply
      (Relabeling.relabelDist e r) _ b
  have hR :
      (Channel.actionPushforward d (supportIncludeKernel r)) (e.symm b) =
      if h : r (e.symm b) > 0 then d ⟨e.symm b, h⟩ else 0 :=
    directActionPushforward_supportInclude_apply r d (e.symm b)
  rw [Relabeling.relabelDist_apply, hL, hR]
  by_cases hb : (Relabeling.relabelDist e r) b > 0
  · have ha : r (e.symm b) > 0 := by
      simpa [Relabeling.relabelDist_apply] using hb
    rw [dif_pos hb, dif_pos ha, Relabeling.relabelDist_apply]
    congr 1
  · have ha : ¬ r (e.symm b) > 0 := by
      simpa [Relabeling.relabelDist_apply] using hb
    rw [dif_neg hb, dif_neg ha]

/-- Pushing a signed face tangent and relabelling it is the same as first
relabelling the face tangent and then pushing it. -/
theorem directPushSignedIncl_relabel
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (r : Dist A)
    [Nonempty (supportSubtype r)]
    [Nonempty (supportSubtype (Relabeling.relabelDist e r))]
    (eta : PosteriorLawSigned (supportSubtype r)) :
    directPushSignedIncl (Relabeling.relabelDist e r)
        (relabelPosteriorLawSigned
          (directRelabelSupportEquiv e r).symm eta) =
      relabelPosteriorLawSigned e (directPushSignedIncl r eta) := by
  funext phi
  change
    eta (fun d => phi (Channel.actionPushforward
      (Relabeling.relabelDist (directRelabelSupportEquiv e r).symm d)
      (supportIncludeKernel (Relabeling.relabelDist e r)))) =
    eta (fun d => phi (Relabeling.relabelDist e
      (Channel.actionPushforward d (supportIncludeKernel r))))
  congr 1
  funext d
  rw [directPush_relabel_comm]

/-- Exact covariance of the selected value forces covariance of the positive
ambient-to-face coefficient. -/
theorem boundaryCoeff_relabel_of_atomicRelation
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hrel : AtomicBoundaryLinearPartRelationFor
      F hax hV hlin hboundary)
    (hVrel :
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
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q r : Dist A) (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    hboundary.boundaryCoeff (Relabeling.relabelDist e q)
        (Relabeling.relabelDist e r) =
      hboundary.boundaryCoeff q r := by
  classical
  let rq := Relabeling.relabelDist e q
  let rr := Relabeling.relabelDist e r
  have hrq : rq.FullSupport :=
    Relabeling.relabelDist_fullSupport e q hq
  have hrrn : ∃ b : B, 0 < rr b := by
    obtain ⟨a, ha⟩ := hrn
    exact ⟨e a, by simpa [rq, rr, Relabeling.relabelDist_apply] using ha⟩
  have hrrnd : ∃ a b : B, a ≠ b ∧ 0 < rr a ∧ 0 < rr b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    exact ⟨e a, e b, fun h => hab (e.injective h),
      by simpa [rr, Relabeling.relabelDist_apply] using ha,
      by simpa [rr, Relabeling.relabelDist_apply] using hb⟩
  have hrrb : ¬ rr.FullSupport := by
    intro hfs
    apply hrb
    intro a
    have := hfs (e a)
    simpa [rr, Relabeling.relabelDist_apply] using this
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  letI : Nonempty (supportSubtype rr) := supportSubtype_nonempty rr
  have hrsnd : ∃ a b : supportSubtype r, a ≠ b ∧
      0 < r.restrictToSupport a ∧ 0 < r.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩,
      by intro h; exact hab (congrArg Subtype.val h),
      by simpa [Dist.restrictToSupport_apply] using ha,
      by simpa [Dist.restrictToSupport_apply] using hb⟩
  obtain ⟨eta, hetaAtomic, hetaTan, hetaNe⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV r.restrictToSupport r.restrictToSupport
      (Dist.restrictToSupport_fullSupport r)
      (Dist.restrictToSupport_fullSupport r) hrsnd
  let es := (directRelabelSupportEquiv e r).symm
  let eta' : PosteriorLawSigned (supportSubtype rr) :=
    relabelPosteriorLawSigned es eta
  have heta'Atomic : PosteriorLawSigned.AtomicLinear eta' :=
    hetaAtomic.relabel es
  have heta'Tan : PosteriorLawTangent eta' := hetaTan.relabel es
  have hqr := hrel.relation q r hq hrn hrnd hrb
    eta hetaAtomic hetaTan
  have hqr' := hrel.relation rq rr hrq hrrn hrrnd hrrb
    eta' heta'Atomic heta'Tan
  have hpushEq : directPushSignedIncl rr eta' =
      relabelPosteriorLawSigned e (directPushSignedIncl r eta) := by
    simpa [rr, eta', es] using directPushSignedIncl_relabel e r eta
  have hambient := affineLinearPart_relabel_atomicTangent
    hlin hV hVrel e q hq (directPushSignedIncl r eta)
    (directAtomicLinear_pushSignedIncl r hetaAtomic)
    (directPushSignedIncl_tangent r hetaAtomic hetaTan)
  have hfacePrior : rr.restrictToSupport =
      Relabeling.relabelDist es r.restrictToSupport := by
    simpa [rr, es] using directRestrictToSupport_relabelDist e r
  have hface := affineLinearPart_relabel_atomicTangent
    hlin hV hVrel es r.restrictToSupport
    (Dist.restrictToSupport_fullSupport r) eta hetaAtomic hetaTan
  rw [hpushEq] at hqr'
  rw [hfacePrior] at hqr'
  rw [hambient, hface] at hqr'
  have hcancel := mul_right_cancel₀ hetaNe (hqr'.symm.trans hqr)
  exact hcancel

/-! ## The embedding defect does not depend on weights within a face -/

/-- The canonical equivalence between the positive supports of two priors
having the same support set. -/
def directSameSupportEquiv
    {A : Type u} [Fintype A] [DecidableEq A]
    (rho sigma : Dist A) (hsupp : ∀ a, rho a > 0 ↔ sigma a > 0) :
    supportSubtype rho ≃ supportSubtype sigma where
  toFun a := ⟨a.1, (hsupp a.1).mp a.2⟩
  invFun b := ⟨b.1, (hsupp b.1).mpr b.2⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv b := by apply Subtype.ext; rfl

/-- Support inclusion is insensitive to the positive weights placed on a
fixed support set. -/
theorem directPush_sameSupport_comm
    {A : Type u} [Fintype A] [DecidableEq A]
    (rho sigma : Dist A) (hsupp : ∀ a, rho a > 0 ↔ sigma a > 0)
    (d : Dist (supportSubtype rho)) :
    Channel.actionPushforward d (supportIncludeKernel rho) =
      Channel.actionPushforward
        (Relabeling.relabelDist (directSameSupportEquiv rho sigma hsupp) d)
        (supportIncludeKernel sigma) := by
  classical
  ext a
  rw [directActionPushforward_supportInclude_apply,
    directActionPushforward_supportInclude_apply]
  by_cases ha : rho a > 0
  · have ha' : sigma a > 0 := (hsupp a).mp ha
    rw [dif_pos ha, dif_pos ha', Relabeling.relabelDist_apply]
    congr 1
  · have ha' : ¬ sigma a > 0 := fun h => ha ((hsupp a).mpr h)
    rw [dif_neg ha, dif_neg ha']

/-- Signed-law form of `directPush_sameSupport_comm`. -/
theorem directPushSignedIncl_sameSupport
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (rho sigma : Dist A) (hsupp : ∀ a, rho a > 0 ↔ sigma a > 0)
    [Nonempty (supportSubtype rho)] [Nonempty (supportSubtype sigma)]
    (eta : PosteriorLawSigned (supportSubtype rho)) :
    directPushSignedIncl sigma
        (relabelPosteriorLawSigned
          (directSameSupportEquiv rho sigma hsupp) eta) =
      directPushSignedIncl rho eta := by
  funext phi
  change eta (fun d => phi (Channel.actionPushforward
      (Relabeling.relabelDist (directSameSupportEquiv rho sigma hsupp) d)
      (supportIncludeKernel sigma))) =
    eta (fun d => phi
      (Channel.actionPushforward d (supportIncludeKernel rho)))
  congr 1
  funext d
  rw [← directPush_sameSupport_comm rho sigma hsupp d]

/-- Within a fixed support inclusion, the product
`boundaryCoeff(q,r) * scale(r|supp)` is independent of the positive weights of
`r`.  This is the second cancellation in the face-cocycle argument. -/
theorem boundaryCoeff_mul_scale_sameSupport_of_atomicRelation
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hpath : BranchPathTangentScalarStructure F hV hlin)
    (hboundary : FiniteBranchBoundaryFaceScaleAssumptions.{u})
    (hrel : AtomicBoundaryLinearPartRelationFor
      F hax hV hlin hboundary)
    (hVrel :
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
    {hbranch : BranchAggregationStructure F}
    (hfull : FiniteBranchScaleFactorizationFullSupportAssumptions hbranch)
    (hbranchPath :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q r : Dist A), q.FullSupport → r.FullSupport →
        (∃ a b : A, a ≠ b) →
        hbranch.branchCoeff q r = hpath.branchPathCoeff q r)
    (hscaleRelabel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A), q.FullSupport →
        hfull.scale (Relabeling.relabelDist e q) = hfull.scale q)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q rho sigma : Dist A) (hq : q.FullSupport)
    (hsupp : ∀ a, rho a > 0 ↔ sigma a > 0)
    (hrn : ∃ a : A, 0 < rho a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < rho a ∧ 0 < rho b)
    (hrb : ¬ rho.FullSupport) :
    hboundary.boundaryCoeff q rho * hfull.scale rho.restrictToSupport =
      hboundary.boundaryCoeff q sigma *
        hfull.scale sigma.restrictToSupport := by
  classical
  have hsn : ∃ a : A, 0 < sigma a := by
    obtain ⟨a, ha⟩ := hrn
    exact ⟨a, (hsupp a).mp ha⟩
  have hsnd : ∃ a b : A, a ≠ b ∧ 0 < sigma a ∧ 0 < sigma b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    exact ⟨a, b, hab, (hsupp a).mp ha, (hsupp b).mp hb⟩
  have hsb : ¬ sigma.FullSupport := by
    intro hfs
    apply hrb
    intro a
    exact (hsupp a).mpr (hfs a)
  letI : Nonempty (supportSubtype rho) := supportSubtype_nonempty rho
  letI : Nonempty (supportSubtype sigma) := supportSubtype_nonempty sigma
  have hrsnd : ∃ a b : supportSubtype rho, a ≠ b ∧
      0 < rho.restrictToSupport a ∧ 0 < rho.restrictToSupport b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩,
      by intro h; exact hab (congrArg Subtype.val h),
      by simpa [Dist.restrictToSupport_apply] using ha,
      by simpa [Dist.restrictToSupport_apply] using hb⟩
  obtain ⟨eta, hetaAtomic, hetaTan, hetaNe⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV rho.restrictToSupport rho.restrictToSupport
      (Dist.restrictToSupport_fullSupport rho)
      (Dist.restrictToSupport_fullSupport rho) hrsnd
  let e := directSameSupportEquiv rho sigma hsupp
  let rho' : Dist (supportSubtype sigma) :=
    Relabeling.relabelDist e rho.restrictToSupport
  let eta' : PosteriorLawSigned (supportSubtype sigma) :=
    relabelPosteriorLawSigned e eta
  have heta'Atomic : PosteriorLawSigned.AtomicLinear eta' :=
    hetaAtomic.relabel e
  have heta'Tan : PosteriorLawTangent eta' := hetaTan.relabel e
  have hrho := hrel.relation q rho hq hrn hrnd hrb
    eta hetaAtomic hetaTan
  have hsigma := hrel.relation q sigma hq hsn hsnd hsb
    eta' heta'Atomic heta'Tan
  have hpush : directPushSignedIncl sigma eta' =
      directPushSignedIncl rho eta := by
    simpa [eta', e] using
      directPushSignedIncl_sameSupport rho sigma hsupp eta
  rw [hpush, hrho] at hsigma
  have hrho'fs : rho'.FullSupport :=
    Relabeling.relabelDist_fullSupport e rho.restrictToSupport
      (Dist.restrictToSupport_fullSupport rho)
  have hsigmafs : sigma.restrictToSupport.FullSupport :=
    Dist.restrictToSupport_fullSupport sigma
  have hnd : ∃ a b : supportSubtype sigma, a ≠ b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    exact ⟨e ⟨a, ha⟩, e ⟨b, hb⟩,
      fun h => hab (congrArg (fun x => x.1) (e.injective h))⟩
  have hpathrel := hpath.linear_part_scalar_relation_on_tangent
    sigma.restrictToSupport rho' hsigmafs hrho'fs
    (by
      obtain ⟨a, b, hab⟩ := hnd
      exact ⟨a, b, hab, hrho'fs a, hrho'fs b⟩)
    eta' heta'Atomic heta'Tan
  have hnat := affineLinearPart_relabel_atomicTangent
    hlin hV hVrel e rho.restrictToSupport
    (Dist.restrictToSupport_fullSupport rho) eta hetaAtomic hetaTan
  have hcoeff : hpath.branchPathCoeff sigma.restrictToSupport rho' =
      hfull.scale sigma.restrictToSupport / hfull.scale rho' := by
    rw [← hbranchPath sigma.restrictToSupport rho'
      hsigmafs hrho'fs hnd]
    exact hfull.branchCoeff_factorization_fullSupport
      sigma.restrictToSupport rho' hsigmafs hrho'fs hnd
  have hscaleRho' : hfull.scale rho' =
      hfull.scale rho.restrictToSupport :=
    hscaleRelabel e rho.restrictToSupport
      (Dist.restrictToSupport_fullSupport rho)
  have hlinearSigma :
      hlin.linearPart F hV sigma.restrictToSupport eta' =
        (hfull.scale sigma.restrictToSupport /
          hfull.scale rho.restrictToSupport) *
          hlin.linearPart F hV rho.restrictToSupport eta := by
    rw [hpathrel, hcoeff, hscaleRho', hnat]
  rw [hlinearSigma] at hsigma
  have hsRhoPos := hfull.scale_pos rho.restrictToSupport
    (Dist.restrictToSupport_fullSupport rho)
    (by
      obtain ⟨a, b, hab⟩ := hnd
      exact ⟨e.symm a, e.symm b, fun h => hab (e.symm.injective h)⟩)
  have hsRhoNe : hfull.scale rho.restrictToSupport ≠ 0 :=
    ne_of_gt hsRhoPos
  have hcancel := mul_right_cancel₀ hetaNe (by
    calc
      (hboundary.boundaryCoeff q rho *
          hfull.scale rho.restrictToSupport) *
          hlin.linearPart F hV rho.restrictToSupport eta =
        hfull.scale rho.restrictToSupport *
          (hboundary.boundaryCoeff q rho *
            hlin.linearPart F hV rho.restrictToSupport eta) := by ring
      _ = hfull.scale rho.restrictToSupport *
          (hboundary.boundaryCoeff q sigma *
            ((hfull.scale sigma.restrictToSupport /
              hfull.scale rho.restrictToSupport) *
              hlin.linearPart F hV rho.restrictToSupport eta)) := by rw [hsigma]
      _ = (hboundary.boundaryCoeff q sigma *
          hfull.scale sigma.restrictToSupport) *
          hlin.linearPart F hV rho.restrictToSupport eta := by
            field_simp [hsRhoNe])
  exact hcancel

/-- Direct boundary coefficients are invariant under simultaneous action
relabeling. -/
theorem directBoundaryCoeff_relabel
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hVrel :
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
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q r : Dist A) (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (directBoundaryFaceScale F hax hV).boundaryCoeff
        (Relabeling.relabelDist e q) (Relabeling.relabelDist e r) =
      (directBoundaryFaceScale F hax hV).boundaryCoeff q r :=
  boundaryCoeff_relabel_of_atomicRelation hax hV
    finiteAffineLinearPartAssumptions_of_posteriorValue
    (directBoundaryFaceScale F hax hV)
    (directAtomicBoundaryLinearPartRelation F hax hV)
    hVrel e q r hq hrn hrnd hrb

/-- For the direct selected scale, the scaled boundary defect depends only on
the underlying support subset, not on weights inside that subset. -/
theorem directBoundaryCoeff_mul_scale_sameSupport
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hVrel :
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
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q rho sigma : Dist A) (hq : q.FullSupport)
    (hsupp : ∀ a, rho a > 0 ↔ sigma a > 0)
    (hrn : ∃ a : A, 0 < rho a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < rho a ∧ 0 < rho b)
    (hrb : ¬ rho.FullSupport) :
    (directBoundaryFaceScale F hax hV).boundaryCoeff q rho *
        directSelectedBranchScale F hax hV rho.restrictToSupport =
      (directBoundaryFaceScale F hax hV).boundaryCoeff q sigma *
        directSelectedBranchScale F hax hV sigma.restrictToSupport := by
  apply boundaryCoeff_mul_scale_sameSupport_of_atomicRelation
    hax hV finiteAffineLinearPartAssumptions_of_posteriorValue
    (directBranchPathTangentScalar F hax hV)
    (directBoundaryFaceScale F hax hV)
    (directAtomicBoundaryLinearPartRelation F hax hV) hVrel
    (directSelectedFullSupportScale F hax hV hvalue)
  · intro A _ _ _ s t hs ht hnd
    change branchCoeffFromTangentRepParts
        (directBranchPathTangentScalar F hax hV)
        (directBoundaryFaceScale F hax hV)
        (directBranchSingletonScaleNormalization F hax hV hvalue) s t =
      (directBranchPathTangentScalar F hax hV).branchPathCoeff s t
    simp [branchCoeffFromTangentRepParts, ht]
  · intro A B _ _ _ _ _ _ e s hs
    exact directSelectedBranchScale_relabel hax hV hVrel e s hs
  · exact hq
  · exact hsupp
  · exact hrn
  · exact hrnd
  · exact hrb

/-! ## Canonical finite faces -/

private theorem directSelectedBranchScale_uniform_eq_one_aux
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (hnd : ∃ a b : A, a ≠ b) :
    directSelectedBranchScale F hax hV (Dist.uniform (A := A)) = 1 := by
  classical
  let hpath := directBranchPathTangentScalar F hax hV
  rw [directSelectedBranchScale_fullSupport F hax hV
    (Dist.uniform (A := A)) Dist.uniform_fullSupport]
  change hpath.branchPathCoeff (Dist.uniform (A := A))
    (Dist.uniform (A := A)) = 1
  have hcoc := branchCoeffTangentScalar_cocycle_fullSupport
    finiteAffineLinearPartAssumptions_of_posteriorValue F hax hV hpath
    (Dist.uniform (A := A)) (Dist.uniform (A := A))
    (Dist.uniform (A := A)) Dist.uniform_fullSupport
    Dist.uniform_fullSupport Dist.uniform_fullSupport hnd
  obtain ⟨a, b, hab⟩ := hnd
  have hpos : 0 < hpath.branchPathCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) :=
    hpath.branchPathCoeff_pos _ _ Dist.uniform_fullSupport
      Dist.uniform_fullSupport
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  nlinarith

/-- Direct embedding defect for the canonical `m`-point face of the canonical
`n`-point simplex.  Outside the nondegenerate proper-face range its value is
irrelevant and is set to one. -/
noncomputable def directCardinalFaceDefect
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) (n m : ℕ) : ℝ :=
  if h : 2 ≤ m ∧ m < n then
    haveI : NeZero m := ⟨by omega⟩
    haveI : Nonempty (canonType.{u} n) :=
      ⟨ULift.up ⟨0, by omega⟩⟩
    (directBoundaryFaceScale F hax hV).boundaryCoeff
      (Dist.uniform (A := canonType.{u} n))
      (canonBoundary.{u} n m (le_of_lt h.2))
  else 1

theorem directCardinalFaceDefect_pos
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (n m : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    0 < directCardinalFaceDefect F hax hV n m := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  haveI : Nonempty (canonType.{u} n) :=
    ⟨ULift.up ⟨0, by omega⟩⟩
  rw [directCardinalFaceDefect, dif_pos ⟨hm2, hmn⟩]
  exact (directBoundaryFaceScale F hax hV).boundaryCoeff_pos
    (Dist.uniform (A := canonType.{u} n))
    (canonBoundary.{u} n m (le_of_lt hmn))
    Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n m (le_of_lt hmn) (by omega))
    (canonBoundary_nondeg n m (le_of_lt hmn) hm2)
    (canonBoundary_boundary n m (le_of_lt hmn) hmn)

/-- The selected scale on the intrinsic support of a canonical face is one. -/
theorem directCanonicalBoundary_face_scale_eq_one
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hVrel :
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
    (n m : ℕ) (hmn : m ≤ n) [NeZero m] (hm2 : 2 ≤ m)
    [Nonempty (supportSubtype (canonBoundary.{u} n m hmn))] :
    directSelectedBranchScale F hax hV
      (canonBoundary.{u} n m hmn).restrictToSupport = 1 := by
  rw [cBface_eq_relabel_uniform n m hmn]
  change directSelectedBranchScale F hax hV
      (Relabeling.relabelDist (canonBoundarySupportEquiv n m hmn).symm
        (Dist.uniform (A := canonType.{u} m))) = 1
  rw [directSelectedBranchScale_relabel hax hV hVrel
    (canonBoundarySupportEquiv n m hmn).symm
    (Dist.uniform (A := canonType.{u} m)) Dist.uniform_fullSupport]
  apply directSelectedBranchScale_uniform_eq_one_aux
  have hcard : Fintype.card (canonType.{u} m) = m := by
    simp [canonType]
  have : 1 < Fintype.card (canonType.{u} m) := by omega
  exact Fintype.one_lt_card_iff.mp this

/-- Reduction of an arbitrary boundary face to its canonical cardinal defect
at the uniform ambient prior. -/
theorem directGeneralFaceDefect_uniform
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hVrel :
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
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (r : Dist A)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (directBoundaryFaceScale F hax hV).boundaryCoeff
        (Dist.uniform (A := A)) r *
      directSelectedBranchScale F hax hV r.restrictToSupport =
    directCardinalFaceDefect F hax hV
      (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  classical
  let n := Fintype.card A
  let m := Fintype.card (supportSubtype r)
  have hm2 : 2 ≤ m := two_le_card_supp r hrnd
  have hmn : m < n := card_supp_lt r hrb
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  let e := alignEquiv r
  let r' := Relabeling.relabelDist e r
  have huni : Relabeling.relabelDist e (Dist.uniform (A := A)) =
      Dist.uniform (A := canonType.{u} n) := by
    ext b
    rw [Relabeling.relabelDist_apply, Dist.uniform_apply, Dist.uniform_apply]
    congr 1
    exact congrArg (fun k : ℕ => (k : ℝ)) (Fintype.card_congr e)
  have hbc :
      (directBoundaryFaceScale F hax hV).boundaryCoeff
          (Dist.uniform (A := A)) r =
        (directBoundaryFaceScale F hax hV).boundaryCoeff
          (Dist.uniform (A := canonType.{u} n)) r' := by
    rw [← huni]
    exact (directBoundaryCoeff_relabel hax hV hVrel e
      (Dist.uniform (A := A)) r Dist.uniform_fullSupport hrn hrnd hrb).symm
  have hscale : directSelectedBranchScale F hax hV r.restrictToSupport =
      directSelectedBranchScale F hax hV r'.restrictToSupport := by
    have hface : r'.restrictToSupport =
        Relabeling.relabelDist (directRelabelSupportEquiv e r).symm
          r.restrictToSupport := by
      simpa [r', e] using directRestrictToSupport_relabelDist e r
    rw [hface]
    exact (directSelectedBranchScale_relabel hax hV hVrel
      (directRelabelSupportEquiv e r).symm r.restrictToSupport
      (Dist.restrictToSupport_fullSupport r)).symm
  rw [hbc, hscale]
  have hle : m ≤ n := le_of_lt hmn
  have hsupp : ∀ c, r' c > 0 ↔ (canonBoundary.{u} n m hle) c > 0 := by
    intro c
    exact alignEquiv_relabel_support_eq r m rfl hle c
  have hr'n : ∃ a : canonType.{u} n, 0 < r' a := by
    obtain ⟨a, ha⟩ := hrn
    exact ⟨e a, by simpa [r', Relabeling.relabelDist_apply] using ha⟩
  have hr'nd : ∃ a b : canonType.{u} n,
      a ≠ b ∧ 0 < r' a ∧ 0 < r' b := by
    obtain ⟨a, b, hab, ha, hb⟩ := hrnd
    exact ⟨e a, e b, fun h => hab (e.injective h),
      by simpa [r', Relabeling.relabelDist_apply] using ha,
      by simpa [r', Relabeling.relabelDist_apply] using hb⟩
  have hr'b : ¬ r'.FullSupport := by
    intro hfs
    apply hrb
    intro a
    have := hfs (e a)
    simpa [r', Relabeling.relabelDist_apply] using this
  have hwf := directBoundaryCoeff_mul_scale_sameSupport
    hax hV hvalue hVrel (Dist.uniform (A := canonType.{u} n))
    r' (canonBoundary.{u} n m hle) Dist.uniform_fullSupport
    hsupp hr'n hr'nd hr'b
  rw [hwf]
  haveI : Nonempty (supportSubtype (canonBoundary.{u} n m hle)) :=
    supportSubtype_nonempty _
  rw [directCanonicalBoundary_face_scale_eq_one
    hax hV hVrel n m hle hm2, mul_one]
  rw [directCardinalFaceDefect, dif_pos ⟨hm2, hmn⟩]

/-- General ambient-prior form of the direct face-defect reduction. -/
theorem directGeneralFaceDefect
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hVrel :
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
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport)
    (hrn : ∃ a : A, 0 < r a)
    (hrnd : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b)
    (hrb : ¬ r.FullSupport) :
    (directBoundaryFaceScale F hax hV).boundaryCoeff q r *
        directSelectedBranchScale F hax hV r.restrictToSupport =
      directSelectedBranchScale F hax hV q *
        directCardinalFaceDefect F hax hV
          (Fintype.card A) (Fintype.card (supportSubtype r)) := by
  have hqi := directBoundaryCoeff_qIndep F hax hV
    (Dist.uniform (A := A)) q r Dist.uniform_fullSupport hq hrnd
  rw [directSelectedBranchScale_fullSupport F hax hV q hq]
  have huni := directGeneralFaceDefect_uniform
    hax hV hvalue hVrel r hrn hrnd hrb
  calc
    (directBoundaryFaceScale F hax hV).boundaryCoeff q r *
        directSelectedBranchScale F hax hV r.restrictToSupport =
      ((directBoundaryFaceScale F hax hV).boundaryCoeff
          (Dist.uniform (A := A)) r *
        (directBranchPathTangentScalar F hax hV).branchPathCoeff q
          (Dist.uniform (A := A))) *
        directSelectedBranchScale F hax hV r.restrictToSupport := by rw [hqi]
    _ = (directBranchPathTangentScalar F hax hV).branchPathCoeff q
          (Dist.uniform (A := A)) *
        ((directBoundaryFaceScale F hax hV).boundaryCoeff
          (Dist.uniform (A := A)) r *
          directSelectedBranchScale F hax hV r.restrictToSupport) := by ring
    _ = (directBranchPathTangentScalar F hax hV).branchPathCoeff q
          (Dist.uniform (A := A)) *
        directCardinalFaceDefect F hax hV
          (Fintype.card A) (Fintype.card (supportSubtype r)) := by rw [huni]

/-- An injective deterministic pushforward preserves posterior-law
tangency. -/
theorem pushSignedDet_tangent_of_injective
    {S T : Type u} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (K : S → T) (hK : Function.Injective K)
    {eta : PosteriorLawSigned S}
    (hetaAtomic : PosteriorLawSigned.AtomicLinear eta)
    (hetaTan : PosteriorLawTangent eta) :
    PosteriorLawTangent (pushSignedDet K eta) := by
  refine ⟨hetaTan.1, ?_⟩
  intro t
  change eta (fun d => (Channel.actionPushforward d
    (fun x => Dist.pure (K x))) t) = 0
  by_cases hex : ∃ x : S, K x = t
  · obtain ⟨x, hx⟩ := hex
    have hfun : (fun d : Dist S =>
        (Channel.actionPushforward d (fun y => Dist.pure (K y))) t) =
        (fun d => d x) := by
      funext d
      show (∑ y : S, d y * (Dist.pure (K y) : Dist T) t) = d x
      rw [Finset.sum_eq_single x]
      · rw [hx, Dist.pure_apply_self, mul_one]
      · intro y _ hy
        rw [Dist.pure_apply_ne, mul_zero]
        intro hyt
        exact hy (hK (hyt.symm.trans hx.symm))
      · intro hxmem
        exact absurd (Finset.mem_univ x) hxmem
    rw [hfun]
    exact hetaTan.2 x
  · have hfun : (fun d : Dist S =>
        (Channel.actionPushforward d (fun y => Dist.pure (K y))) t) =
        (fun _ => (0 : ℝ)) := by
      funext d
      show (∑ y : S, d y * (Dist.pure (K y) : Dist T) t) = 0
      apply Finset.sum_eq_zero
      intro y _
      rw [Dist.pure_apply_ne, mul_zero]
      intro hyt
      exact hex ⟨y, hyt.symm⟩
    rw [hfun]
    have hz := congrFun hetaAtomic.eval_eq (fun _ => (0 : ℝ))
    rw [AtomicPosteriorSignedLaw.eval_apply] at hz
    rw [← hz]
    simp

/-- Multiplicativity of the direct canonical embedding defect over nested
finite faces.  The proof is the paper's three-level cancellation, performed
on one nonzero atomic tangent of the smallest face. -/
theorem directCardinalFaceDefect_cocycle
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hVrel :
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
    (n m l : ℕ) (hl2 : 2 ≤ l) (hlm : l < m) (hmn : m < n) :
    directCardinalFaceDefect F hax hV n l =
      directCardinalFaceDefect F hax hV n m *
        directCardinalFaceDefect F hax hV m l := by
  classical
  haveI : NeZero l := ⟨by omega⟩
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  have hleML : l ≤ m := le_of_lt hlm
  have hleMN : m ≤ n := le_of_lt hmn
  have hleLN : l ≤ n := hleML.trans hleMN
  let rNL := canonBoundary.{u} n l hleLN
  let rNM := canonBoundary.{u} n m hleMN
  let rML := canonBoundary.{u} m l hleML
  let hlin := finiteAffineLinearPartAssumptions_of_posteriorValue
  let hb := directBoundaryFaceScale F hax hV
  let hrel := directAtomicBoundaryLinearPartRelation F hax hV
  letI : Nonempty (supportSubtype rNL) := supportSubtype_nonempty _
  letI : Nonempty (supportSubtype rNM) := supportSubtype_nonempty _
  letI : Nonempty (supportSubtype rML) := supportSubtype_nonempty _
  have hNLfs : rNL.restrictToSupport.FullSupport :=
    Dist.restrictToSupport_fullSupport _
  have hNLnd : ∃ a b : supportSubtype rNL, a ≠ b ∧
      0 < rNL.restrictToSupport a ∧ 0 < rNL.restrictToSupport b := by
    have hcard : Fintype.card (supportSubtype rNL) = l := by
      change Fintype.card (supportSubtype (canonBoundary.{u} n l hleLN)) = l
      rw [Fintype.card_congr (canonBoundarySupportEquiv n l hleLN)]
      simp [canonType]
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega :
      1 < Fintype.card (supportSubtype rNL))
    exact ⟨a, b, hab, hNLfs a, hNLfs b⟩
  obtain ⟨eta, hetaAtomic, hetaTan, hetaNe⟩ :=
    branch_linear_part_nonzero_atomicLinear_tangent_of_A1
      hlin F hax hV rNL.restrictToSupport rNL.restrictToSupport
      hNLfs hNLfs hNLnd
  have hTNL := hrel.relation
    (Dist.uniform (A := canonType.{u} n)) rNL Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n l hleLN (by omega))
    (canonBoundary_nondeg n l hleLN hl2)
    (canonBoundary_boundary n l hleLN (by omega)) eta hetaAtomic hetaTan
  let K := nestSupportMap n m l hleMN hleML
  let etaNM : PosteriorLawSigned (supportSubtype rNM) := pushSignedDet K eta
  have hetaNMAtomic : PosteriorLawSigned.AtomicLinear etaNM :=
    atomicLinear_pushSignedDet K hetaAtomic
  have hK : Function.Injective K := by
    intro a b hab
    apply Subtype.ext
    have hv := congrArg Subtype.val hab
    simpa [K, nestSupportMap] using hv
  have hetaNMTan : PosteriorLawTangent etaNM :=
    pushSignedDet_tangent_of_injective K hK hetaAtomic hetaTan
  have hpushOuter : directPushSignedIncl rNL eta =
      directPushSignedIncl rNM etaNM := by
    funext psi
    change eta (fun d => psi (Channel.actionPushforward d
        (supportIncludeKernel rNL))) =
      eta (fun d => psi (Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (K a)))
        (supportIncludeKernel rNM)))
    congr 1
    funext d
    exact congrArg psi (supportInclude_nest n m l hleMN hleML d)
  have hm2 : 2 ≤ m := by omega
  have hTNM := hrel.relation
    (Dist.uniform (A := canonType.{u} n)) rNM Dist.uniform_fullSupport
    (canonBoundary_support_nonempty n m hleMN (by omega))
    (canonBoundary_nondeg n m hleMN hm2)
    (canonBoundary_boundary n m hleMN hmn)
    etaNM hetaNMAtomic hetaNMTan
  rw [hpushOuter] at hTNL
  have hchain : hb.boundaryCoeff
        (Dist.uniform (A := canonType.{u} n)) rNL *
        hlin.linearPart F hV rNL.restrictToSupport eta =
      hb.boundaryCoeff (Dist.uniform (A := canonType.{u} n)) rNM *
        hlin.linearPart F hV rNM.restrictToSupport etaNM := by
    rw [← hTNL, ← hTNM]
  let eNM := canonBoundarySupportEquiv n m hleMN
  have hfaceNM : Relabeling.relabelDist eNM rNM.restrictToSupport =
      Dist.uniform (A := canonType.{u} m) := by
    change Relabeling.relabelDist eNM
        (canonBoundary.{u} n m hleMN).restrictToSupport = _
    rw [cBface_eq_relabel_uniform n m hleMN]
    ext a
    simp [Relabeling.relabelDist_apply]
  have hnatNM := affineLinearPart_relabel_atomicTangent
    hlin hV hVrel eNM rNM.restrictToSupport
    (Dist.restrictToSupport_fullSupport rNM) etaNM hetaNMAtomic hetaNMTan
  rw [hfaceNM] at hnatNM
  let phi : supportSubtype rNL ≃ supportSubtype rML :=
    (canonBoundarySupportEquiv n l hleLN).trans
      (canonBoundarySupportEquiv m l hleML).symm
  let zeta : PosteriorLawSigned (supportSubtype rML) :=
    relabelPosteriorLawSigned phi eta
  have hzetaAtomic : PosteriorLawSigned.AtomicLinear zeta :=
    hetaAtomic.relabel phi
  have hzetaTan : PosteriorLawTangent zeta := hetaTan.relabel phi
  have hpushMiddle : relabelPosteriorLawSigned eNM etaNM =
      directPushSignedIncl rML zeta := by
    funext psi
    change eta (fun d => psi (Relabeling.relabelDist eNM
      (Channel.actionPushforward d (fun a => Dist.pure (K a))))) =
      eta (fun d => psi (Channel.actionPushforward
        (Relabeling.relabelDist phi d) (supportIncludeKernel rML)))
    congr 1
    funext d
    apply congrArg psi
    have hnest := push_nest_eq_relabel n m l hleMN hleML d
    have hleft : Relabeling.relabelDist eNM
        (Channel.actionPushforward d (fun a => Dist.pure (K a))) =
      Channel.actionPushforward
        (Channel.actionPushforward d
          (fun a => Dist.pure (canonBoundarySupportEquiv n l hleLN a)))
        (canonInclKernel m l hleML) := by
      calc
        Relabeling.relabelDist eNM
            (Channel.actionPushforward d (fun a => Dist.pure (K a))) =
          Relabeling.relabelDist eNM
            (Relabeling.relabelDist eNM.symm
              (Channel.actionPushforward
                (Channel.actionPushforward d
                  (fun a => Dist.pure
                    (canonBoundarySupportEquiv n l hleLN a)))
                (canonInclKernel m l hleML))) := congrArg _ hnest
        _ = _ := by ext a; simp [Relabeling.relabelDist_apply]
    rw [hleft]
    rw [canonIncl_eq_supportInclude m l hleML
      (Channel.actionPushforward d
        (fun a => Dist.pure (canonBoundarySupportEquiv n l hleLN a)))]
    congr 1
    rw [show Relabeling.relabelDist phi d = relabelDist phi d by rfl]
    rw [relabelDist_eq_actionPushforward]
    rw [actionPushforward_pure_comp d
      (fun a => canonBoundarySupportEquiv n l hleLN a)
      (fun b => (canonBoundarySupportEquiv m l hleML).symm b)]
    apply congrArg (Channel.actionPushforward d)
    funext a
    rfl
  have hTML := hrel.relation
    (Dist.uniform (A := canonType.{u} m)) rML Dist.uniform_fullSupport
    (canonBoundary_support_nonempty m l hleML (by omega))
    (canonBoundary_nondeg m l hleML hl2)
    (canonBoundary_boundary m l hleML hlm)
    zeta hzetaAtomic hzetaTan
  have hfaceML : rML.restrictToSupport =
      Relabeling.relabelDist phi rNL.restrictToSupport := by
    change (canonBoundary.{u} m l hleML).restrictToSupport =
      Relabeling.relabelDist phi
        (canonBoundary.{u} n l hleLN).restrictToSupport
    rw [canonBoundary_face_uniform m l hleML,
      canonBoundary_face_uniform n l hleLN]
    ext a
    rw [Dist.uniform_apply, Relabeling.relabelDist_apply, Dist.uniform_apply]
    congr 1
    rw [Fintype.card_congr (canonBoundarySupportEquiv m l hleML),
      Fintype.card_congr (canonBoundarySupportEquiv n l hleLN)]
  have hnatML := affineLinearPart_relabel_atomicTangent
    hlin hV hVrel phi rNL.restrictToSupport hNLfs
    eta hetaAtomic hetaTan
  rw [← hfaceML] at hnatML
  have hbridge : hlin.linearPart F hV rNM.restrictToSupport etaNM =
      hb.boundaryCoeff (Dist.uniform (A := canonType.{u} m)) rML *
        hlin.linearPart F hV rNL.restrictToSupport eta := by
    rw [← hnatNM, hpushMiddle, hTML, hnatML]
  rw [hbridge] at hchain
  have hcancel := mul_right_cancel₀ hetaNe (by
    calc
      hb.boundaryCoeff (Dist.uniform (A := canonType.{u} n)) rNL *
          hlin.linearPart F hV rNL.restrictToSupport eta =
        hb.boundaryCoeff (Dist.uniform (A := canonType.{u} n)) rNM *
          (hb.boundaryCoeff (Dist.uniform (A := canonType.{u} m)) rML *
            hlin.linearPart F hV rNL.restrictToSupport eta) := hchain
      _ = (hb.boundaryCoeff (Dist.uniform (A := canonType.{u} n)) rNM *
          hb.boundaryCoeff (Dist.uniform (A := canonType.{u} m)) rML) *
          hlin.linearPart F hV rNL.restrictToSupport eta := by ring)
  change directCardinalFaceDefect F hax hV n l =
    directCardinalFaceDefect F hax hV n m *
      directCardinalFaceDefect F hax hV m l
  rw [directCardinalFaceDefect, dif_pos ⟨hl2, by omega⟩,
    directCardinalFaceDefect, dif_pos ⟨hm2, hmn⟩,
    directCardinalFaceDefect, dif_pos ⟨hl2, hlm⟩]
  exact hcancel

/-! ## The finite-cardinal face cocycle and its coboundary -/

/-- The exact output of the geometric face argument, separated from the
purely algebraic choice of cardinal gauge.

`defect n m` is the positive scalar attached to an `m`-point face in an
`n`-point simplex.  The last field is the arbitrary-face reduction; the
preceding cocycle field is what makes the gauge `t n := defect n 2` work. -/
structure CardinalFaceDefectCocycleFor
    {F : PrefFamily.{u}}
    (hraw : BranchAggregationCocycleNormalizedChainRuleStructure F) where
  defect : ℕ → ℕ → ℝ
  defect_pos :
    ∀ n m, 2 ≤ m → m < n → 0 < defect n m
  defect_cocycle :
    ∀ n m l, 2 ≤ l → l < m → m < n →
      defect n l = defect n m * defect m l
  raw_scale_relabel :
    ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (e : A ≃ B) (q : Dist A), q.FullSupport →
      hraw.scale_factorization.scale (Relabeling.relabelDist e q) =
        hraw.scale_factorization.scale q
  arbitrary_face_defect :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A), q.FullSupport →
      ∀ (r : Dist A), [Nonempty (supportSubtype r)] →
      (∃ a : A, 0 < r a) →
      (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) →
      ¬ r.FullSupport →
      hraw.branch_agg.branchCoeff q r *
          hraw.scale_factorization.scale r.restrictToSupport =
        hraw.scale_factorization.scale q *
          defect (Fintype.card A) (Fintype.card (supportSubtype r))

/-- Cardinal coboundary selected from the face cocycle. -/
noncomputable def cardinalFaceScaleT
    {F : PrefFamily.{u}}
    {hraw : BranchAggregationCocycleNormalizedChainRuleStructure F}
    (hdef : CardinalFaceDefectCocycleFor hraw) (n : ℕ) : ℝ :=
  if n = 2 then 1 else if 3 ≤ n then hdef.defect n 2 else 1

theorem cardinalFaceScaleT_pos
    {F : PrefFamily.{u}}
    {hraw : BranchAggregationCocycleNormalizedChainRuleStructure F}
    (hdef : CardinalFaceDefectCocycleFor hraw) (n : ℕ) :
    0 < cardinalFaceScaleT hdef n := by
  rw [cardinalFaceScaleT]
  by_cases h2 : n = 2
  · rw [if_pos h2]
    exact one_pos
  · rw [if_neg h2]
    by_cases h3 : 3 ≤ n
    · rw [if_pos h3]
      exact hdef.defect_pos n 2 (by omega) (by omega)
    · rw [if_neg h3]
      exact one_pos

/-- A positive multiplicative face cocycle on finite cardinalities is the
coboundary `defect n m = t n / t m`. -/
theorem cardinalFaceDefect_eq_ratio
    {F : PrefFamily.{u}}
    {hraw : BranchAggregationCocycleNormalizedChainRuleStructure F}
    (hdef : CardinalFaceDefectCocycleFor hraw)
    (n m : ℕ) (hm2 : 2 ≤ m) (hmn : m < n) :
    hdef.defect n m =
      cardinalFaceScaleT hdef n / cardinalFaceScaleT hdef m := by
  have hn3 : 3 ≤ n := by omega
  have htn : cardinalFaceScaleT hdef n = hdef.defect n 2 := by
    rw [cardinalFaceScaleT, if_neg (by omega), if_pos hn3]
  rcases eq_or_lt_of_le hm2 with rfl | hm3
  · rw [htn, cardinalFaceScaleT, if_pos rfl, div_one]
  · have htm3 : 3 ≤ m := by omega
    have htm : cardinalFaceScaleT hdef m = hdef.defect m 2 := by
      rw [cardinalFaceScaleT, if_neg (by omega), if_pos htm3]
    have hcoc := hdef.defect_cocycle n m 2 (by omega) hm3 hmn
    have hpos : 0 < hdef.defect m 2 :=
      hdef.defect_pos m 2 (by omega) hm3
    rw [htn, htm]
    rw [hcoc]
    field_simp [ne_of_gt hpos]

/-- Multiply the two scale fields of a branch-chain package by a positive
constant depending on the cardinality of the ambient finite type.  The branch
aggregation structure, hence its selected value representative, is unchanged.
-/
noncomputable def scaleOnlyCardinalTransform
    {F : PrefFamily.{u}}
    (hraw : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) :
    BranchAggregationCocycleNormalizedChainRuleStructure F where
  branch_agg := hraw.branch_agg
  coeff_cocycle := hraw.coeff_cocycle
  full_support_scale :=
    { scale := fun {A} _ _ _ q =>
        t (Fintype.card A) * hraw.full_support_scale.scale q
      scale_pos := by
        intro A _ _ _ q hq hnd
        exact mul_pos (ht (Fintype.card A))
          (hraw.full_support_scale.scale_pos q hq hnd)
      branchCoeff_factorization_fullSupport := by
        intro A _ _ _ q r hq hr hnd
        rw [hraw.full_support_scale.branchCoeff_factorization_fullSupport
          q r hq hr hnd]
        have hn : t (Fintype.card A) ≠ 0 := ne_of_gt (ht _)
        field_simp [hn] }
  scale_factorization :=
    { scale := fun {A} _ _ _ q =>
        t (Fintype.card A) * hraw.scale_factorization.scale q
      scale_pos := by
        intro A _ _ _ q hq
        exact mul_pos (ht (Fintype.card A))
          (hraw.scale_factorization.scale_pos q hq)
      branchCoeff_factorization := by
        intro A O _ _ _ _ _ q hq P o hpos
        rw [hraw.scale_factorization.branchCoeff_factorization
          q hq P o hpos]
        have hn : t (Fintype.card A) ≠ 0 := ne_of_gt (ht _)
        field_simp [hn] }

@[simp] theorem scaleOnlyCardinalTransform_value_rep
    {F : PrefFamily.{u}}
    (hraw : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n) :
    (scaleOnlyCardinalTransform hraw t ht).branch_agg.value_rep =
      hraw.branch_agg.value_rep :=
  rfl

/-- Assemble coherent face scales after a scale-only cardinal alignment.

The two hypotheses are precisely the two numerical conclusions of the face
cocycle argument: raw scale covariance under bijections, and the aligned
boundary-to-support equation.  Keeping this assembly separate makes explicit
that no value representative is rescaled here. -/
noncomputable def coherentFaceScales_of_scaleOnlyCardinalTransform
    {F : PrefFamily.{u}}
    (hraw : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (hrel :
      ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        (e : A ≃ B) (q : Dist A), q.FullSupport →
        hraw.scale_factorization.scale (Relabeling.relabelDist e q) =
          hraw.scale_factorization.scale q)
    (hface :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A), q.FullSupport →
        ∀ (r : Dist A), [Nonempty (supportSubtype r)] →
        (∃ a : A, 0 < r a) →
        (∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b) →
        ¬ r.FullSupport →
        hraw.branch_agg.branchCoeff q r =
          (t (Fintype.card A) * hraw.scale_factorization.scale q) /
            (t (Fintype.card (supportSubtype r)) *
              hraw.scale_factorization.scale r.restrictToSupport)) :
    CoherentRelabelingFaceScalesStructure F := by
  let hscaled := scaleOnlyCardinalTransform hraw t ht
  exact
    { branch_result := hscaled
      scale_relabeling :=
        { scale_relabel_eq := by
            intro A B _ _ _ _ _ _ e q hq
            change
              t (Fintype.card B) *
                  hraw.scale_factorization.scale
                    (Relabeling.relabelDist e q) =
                t (Fintype.card A) * hraw.scale_factorization.scale q
            rw [Fintype.card_congr e.symm, hrel e q hq] }
      support_face_scale :=
        { support_face_scale := by
            intro A _ _ _ q hq r _ hrn hrnd hrb
            exact hface q hq r hrn hrnd hrb } }

@[simp] theorem coherentFaceScales_of_scaleOnlyCardinalTransform_value_rep
    {F : PrefFamily.{u}}
    (hraw : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (t : ℕ → ℝ) (ht : ∀ n, 0 < t n)
    (hrel hface) :
    (coherentFaceScales_of_scaleOnlyCardinalTransform
      hraw t ht hrel hface).branch_result.branch_agg.value_rep =
      hraw.branch_agg.value_rep :=
  rfl

/-- The face cocycle produces coherent scales by a scale-only cardinal
alignment.  Consequently the selected value representative is unchanged. -/
noncomputable def coherentFaceScales_of_cardinalFaceDefect
    {F : PrefFamily.{u}}
    (hraw : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hdef : CardinalFaceDefectCocycleFor hraw) :
    CoherentRelabelingFaceScalesStructure F := by
  let t : ℕ → ℝ := cardinalFaceScaleT hdef
  apply coherentFaceScales_of_scaleOnlyCardinalTransform
    hraw t (cardinalFaceScaleT_pos hdef)
  · exact hdef.raw_scale_relabel
  · intro A _ _ _ q hq r _ hrn hrnd hrb
    have hm2 : 2 ≤ Fintype.card (supportSubtype r) := by
      obtain ⟨a, b, hab, ha, hb⟩ := hrnd
      have hlt : 1 < Fintype.card (supportSubtype r) :=
        Fintype.one_lt_card_iff.mpr
          ⟨⟨a, ha⟩, ⟨b, hb⟩,
            by intro h; exact hab (congrArg Subtype.val h)⟩
      omega
    have hmn : Fintype.card (supportSubtype r) < Fintype.card A := by
      have hex : ∃ a : A, ¬ r a > 0 := by
        by_contra hall
        apply hrb
        intro a
        exact not_not.mp (fun h => hall ⟨a, h⟩)
      obtain ⟨a, ha⟩ := hex
      exact Fintype.card_subtype_lt (p := fun x => r x > 0) ha
    have hratio := cardinalFaceDefect_eq_ratio hdef
      (Fintype.card A) (Fintype.card (supportSubtype r)) hm2 hmn
    have hrawEq := hdef.arbitrary_face_defect q hq r hrn hrnd hrb
    have htM : t (Fintype.card (supportSubtype r)) ≠ 0 :=
      ne_of_gt (cardinalFaceScaleT_pos hdef _)
    have hsFace :
        hraw.scale_factorization.scale r.restrictToSupport ≠ 0 :=
      ne_of_gt (hraw.scale_factorization.scale_pos r.restrictToSupport
        (Dist.restrictToSupport_fullSupport r))
    rw [hratio] at hrawEq
    rw [eq_div_iff (mul_ne_zero htM hsFace)]
    calc
      hraw.branch_agg.branchCoeff q r *
          (t (Fintype.card (supportSubtype r)) *
            hraw.scale_factorization.scale r.restrictToSupport) =
        t (Fintype.card (supportSubtype r)) *
          (hraw.branch_agg.branchCoeff q r *
            hraw.scale_factorization.scale r.restrictToSupport) := by ring
      _ = t (Fintype.card (supportSubtype r)) *
          (hraw.scale_factorization.scale q *
            (t (Fintype.card A) /
              t (Fintype.card (supportSubtype r)))) := by rw [hrawEq]
      _ = t (Fintype.card A) * hraw.scale_factorization.scale q := by
        field_simp [htM]

@[simp] theorem coherentFaceScales_of_cardinalFaceDefect_value_rep
    {F : PrefFamily.{u}}
    (hraw : BranchAggregationCocycleNormalizedChainRuleStructure F)
    (hdef : CardinalFaceDefectCocycleFor hraw) :
    (coherentFaceScales_of_cardinalFaceDefect hraw hdef).branch_result.branch_agg.value_rep =
      hraw.branch_agg.value_rep :=
  rfl

/-- Final scale-only assembly specialized to the direct branch chain.  The
remaining argument is exactly the cardinal face-defect cocycle proved by the
nested-face cancellation below/at the call site. -/
noncomputable def directCoherentRelabelingFaceScales_of_defect
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hdef : CardinalFaceDefectCocycleFor
      (directBranchChain_of_posteriorValue F hax hV hvalue)) :
    CoherentRelabelingFaceScalesStructure F :=
  coherentFaceScales_of_cardinalFaceDefect
    (directBranchChain_of_posteriorValue F hax hV hvalue) hdef

@[simp] theorem directCoherentRelabelingFaceScales_of_defect_value_rep
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hdef : CardinalFaceDefectCocycleFor
      (directBranchChain_of_posteriorValue F hax hV hvalue)) :
    (directCoherentRelabelingFaceScales_of_defect
      F hax hV hvalue hdef).branch_result.branch_agg.value_rep = hV :=
  rfl

/-- The direct nested-face argument supplies the complete cardinal defect
cocycle, with no geometric input left to choose. -/
noncomputable def directCardinalFaceDefectCocycle
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hrelV : PosteriorValueRelabeling hV) :
    CardinalFaceDefectCocycleFor
      (directBranchChain_of_posteriorValue F hax hV hvalue) where
  defect := directCardinalFaceDefect F hax hV
  defect_pos := by
    intro n m hm2 hmn
    exact directCardinalFaceDefect_pos F hax hV n m hm2 hmn
  defect_cocycle := by
    intro n m l hl2 hlm hmn
    exact directCardinalFaceDefect_cocycle
      hax hV hrelV.V_relabel_eq n m l hl2 hlm hmn
  raw_scale_relabel := by
    intro A B _ _ _ _ _ _ e q hq
    change directSelectedBranchScale F hax hV
        (Relabeling.relabelDist e q) =
      directSelectedBranchScale F hax hV q
    exact directSelectedBranchScale_relabel
      hax hV hrelV.V_relabel_eq e q hq
  arbitrary_face_defect := by
    intro A _ _ _ q hq r _ hrn hrnd hrb
    change branchCoeffFromTangentRepParts
          (directBranchPathTangentScalar F hax hV)
          (directBoundaryFaceScale F hax hV)
          (directBranchSingletonScaleNormalization F hax hV hvalue) q r *
        directSelectedBranchScale F hax hV r.restrictToSupport =
      directSelectedBranchScale F hax hV q *
        directCardinalFaceDefect F hax hV
          (Fintype.card A) (Fintype.card (supportSubtype r))
    rw [show branchCoeffFromTangentRepParts
          (directBranchPathTangentScalar F hax hV)
          (directBoundaryFaceScale F hax hV)
          (directBranchSingletonScaleNormalization F hax hV hvalue) q r =
        (directBoundaryFaceScale F hax hV).boundaryCoeff q r by
      simp [branchCoeffFromTangentRepParts, hrb, hrnd]]
    exact directGeneralFaceDefect
      hax hV hvalue hrelV.V_relabel_eq q r hq hrn hrnd hrb

/-- End-to-end coherent relabeling and support-face scales from the selected
posterior value.  The cardinal alignment changes only the scale fields. -/
noncomputable def directCoherentRelabelingFaceScales
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hrelV : PosteriorValueRelabeling hV) :
    CoherentRelabelingFaceScalesStructure F :=
  directCoherentRelabelingFaceScales_of_defect F hax hV hvalue
    (directCardinalFaceDefectCocycle F hax hV hvalue hrelV)

@[simp] theorem directCoherentRelabelingFaceScales_value_rep
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hrelV : PosteriorValueRelabeling hV) :
    (directCoherentRelabelingFaceScales F hax hV hvalue hrelV
      ).branch_result.branch_agg.value_rep = hV :=
  rfl

/-- The selected direct scale is one at a uniform prior on every
nondegenerate finite alphabet. -/
theorem directSelectedBranchScale_uniform_eq_one
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (hnd : ∃ a b : A, a ≠ b) :
    directSelectedBranchScale F hax hV (Dist.uniform (A := A)) = 1 := by
  classical
  let hpath := directBranchPathTangentScalar F hax hV
  rw [directSelectedBranchScale_fullSupport F hax hV
    (Dist.uniform (A := A)) Dist.uniform_fullSupport]
  change hpath.branchPathCoeff (Dist.uniform (A := A))
    (Dist.uniform (A := A)) = 1
  have hcoc := branchCoeffTangentScalar_cocycle_fullSupport
    finiteAffineLinearPartAssumptions_of_posteriorValue F hax hV hpath
    (Dist.uniform (A := A)) (Dist.uniform (A := A))
    (Dist.uniform (A := A)) Dist.uniform_fullSupport
    Dist.uniform_fullSupport Dist.uniform_fullSupport hnd
  obtain ⟨a, b, hab⟩ := hnd
  have hpos : 0 < hpath.branchPathCoeff
      (Dist.uniform (A := A)) (Dist.uniform (A := A)) :=
    hpath.branchPathCoeff_pos _ _ Dist.uniform_fullSupport
      Dist.uniform_fullSupport
      ⟨a, b, hab, Dist.uniform_fullSupport a, Dist.uniform_fullSupport b⟩
  nlinarith

/-- The selected direct scale is one on a full-support subsingleton
alphabet. -/
theorem directSelectedBranchScale_subsingleton_eq_one
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hsub : Subsingleton A) :
    directSelectedBranchScale F hax hV q = 1 := by
  classical
  letI : Subsingleton A := hsub
  rw [directSelectedBranchScale_fullSupport F hax hV q hq]
  have hnotnd : ¬ ∃ a b : A, a ≠ b ∧
      0 < (Dist.uniform (A := A)) a ∧
      0 < (Dist.uniform (A := A)) b := by
    rintro ⟨a, b, hab, _, _⟩
    exact hab (Subsingleton.elim a b)
  simp only [directBranchPathTangentScalar,
    branchPathTangentScalarStructure_of_A1_atomicLinearTangentSpanning,
    hq, Dist.uniform_fullSupport, dif_pos]
  rw [dif_neg hnotnd]

/-- The scale-only aligned direct face package retains the binary reference
normalization. -/
theorem directCoherentFaceScales_reference_scale_eq_one
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hdef : CardinalFaceDefectCocycleFor
      (directBranchChain_of_posteriorValue F hax hV hvalue)) :
    (directCoherentRelabelingFaceScales_of_defect F hax hV hvalue hdef
      ).branch_result.scale_factorization.scale
        universalScaleReferencePrior = 1 := by
  change cardinalFaceScaleT hdef (Fintype.card universalScaleReferenceType) *
      directSelectedBranchScale F hax hV universalScaleReferencePrior = 1
  have hcard : Fintype.card universalScaleReferenceType = 2 := by
    simp [universalScaleReferenceType]
  rw [hcard]
  have ht : cardinalFaceScaleT hdef 2 = 1 := by
    simp [cardinalFaceScaleT]
  rw [ht, one_mul]
  apply directSelectedBranchScale_uniform_eq_one
  exact ⟨ULift.up false, ULift.up true, by simp⟩

/-- The scale-only aligned direct face package has scale one at every
full-support subsingleton prior. -/
theorem directCoherentFaceScales_subsingleton_scale_eq_one
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hdef : CardinalFaceDefectCocycleFor
      (directBranchChain_of_posteriorValue F hax hV hvalue))
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hsub : Subsingleton A) :
    (directCoherentRelabelingFaceScales_of_defect F hax hV hvalue hdef
      ).branch_result.scale_factorization.scale q = 1 := by
  change cardinalFaceScaleT hdef (Fintype.card A) *
      directSelectedBranchScale F hax hV q = 1
  have hcard : Fintype.card A = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let a : A := Classical.choice (inferInstance : Nonempty A)
    exact ⟨a, fun b => hsub.elim b a⟩
  rw [hcard]
  have ht : cardinalFaceScaleT hdef 1 = 1 := by
    simp [cardinalFaceScaleT]
  rw [ht, one_mul]
  exact directSelectedBranchScale_subsingleton_eq_one
    F hax hV q hq hsub

/-- Binary-reference normalization for the unconditional direct coherent
face-scale package. -/
theorem directCoherentRelabelingFaceScales_reference_scale_eq_one
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hrelV : PosteriorValueRelabeling hV) :
    (directCoherentRelabelingFaceScales F hax hV hvalue hrelV
      ).branch_result.scale_factorization.scale
        universalScaleReferencePrior = 1 :=
  directCoherentFaceScales_reference_scale_eq_one F hax hV hvalue
    (directCardinalFaceDefectCocycle F hax hV hvalue hrelV)

/-- Subsingleton normalization for the unconditional direct coherent
face-scale package. -/
theorem directCoherentRelabelingFaceScales_subsingleton_scale_eq_one
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    (hvalue : FiniteBranchBoundaryValueTransportFor F hax hV)
    (hrelV : PosteriorValueRelabeling hV)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hsub : Subsingleton A) :
    (directCoherentRelabelingFaceScales F hax hV hvalue hrelV
      ).branch_result.scale_factorization.scale q = 1 :=
  directCoherentFaceScales_subsingleton_scale_eq_one F hax hV hvalue
    (directCardinalFaceDefectCocycle F hax hV hvalue hrelV) q hq hsub

end TraceableAgency
