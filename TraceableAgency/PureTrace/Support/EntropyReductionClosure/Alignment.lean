/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.DefectCocycle

namespace TraceableAgency

universe u

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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
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
    (hhm : FinalHMInterface.{u}) (hax : PureTraceConditions F)
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
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F) (n : ℕ) :
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
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F) :
    PositiveFaceScaleGauge.{u} where
  gauge := fun {A} _ _ _ _ => cardScaleT hhm hbranchData hax (Fintype.card A)
  gauge_pos := fun {A} _ _ _ _ => cardScaleT_pos hhm hbranchData hax (Fintype.card A)

/-- The cardinal gauge is relabelling-invariant (depends only on cardinality). -/
theorem cardinalGauge_gaugeRel
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u})
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F)
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
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F)
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
    (hbranchData : FinalFaithfulBranchData hhm) (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
representative, derived from the HM left-slice theorem, derived-background intercept
same-order, HM public-mix affinity, and internal finite affine-utility
uniqueness. -/
theorem productInterceptPositiveLinear_of_FinalHM_positiveGauge
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hfaith : FiniteFaithfulBranchAggregationAssumptions.{u})
    (hax : PureTraceConditions F)
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
    (faceScaleProductInterceptSameOrder_of_backgroundInertness
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
    (hax : PureTraceConditions F)
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
`faceScaleProductSlopeAffine_of_HM_backgroundInertness_relabeling`, but it uses the selected
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
    (hax : PureTraceConditions F)
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
  have hsame := (faceScaleProductLeftSliceSameOrder_of_backgroundInertness hfaces).left_slice_same_order
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
`productLiftScale q r` (`> 0`).  Hence `current_product_gauge` is transparently
the coherent gauge choice `productLiftScale ≡ 1`, a normalization of a value
that A5, derived background inertness, and HM uniqueness *prove* exists and is
positive; it is not an opaque assumption. -/
theorem leftCoeff_eq_productLiftScale
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hhm : FinitePosteriorIntegralRepresentationData.{u})
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hslope : FiniteFaceScaleProductSliceSlopeAssumptionsFor hslice)
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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

end TraceableAgency
