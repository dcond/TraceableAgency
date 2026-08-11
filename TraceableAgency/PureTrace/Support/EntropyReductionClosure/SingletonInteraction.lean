/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReductionClosure.Alignment

namespace TraceableAgency

universe u

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
    (hsupp : ∀ (F' : PrefFamily.{u}) (hax : PureTraceConditions F') (hV' : PosteriorValueRepresentation F')
      {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV'.V r (experimentOfChannel P) =
        hV'.V r.restrictToSupport (experimentOfChannel (Channel.restrictToSupport P r)))
    (hcov : ∀ {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B] [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O),
        hV.V (Relabeling.relabelDist eA q) (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hV.V q (experimentOfChannel P))
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F) {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F) (hcov : FinalSelectedRelabelCovariance hhm)
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
    (hax : PureTraceConditions F) (hcov : FinalSelectedRelabelCovariance hhm)
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
    (hsupp : ∀ (F' : PrefFamily.{u}) (hax : PureTraceConditions F') (hV' : PosteriorValueRepresentation F')
      {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
      (r : Dist A) [Nonempty (supportSubtype r)] (P : Channel A O),
      hV'.V r (experimentOfChannel P) =
        hV'.V r.restrictToSupport (experimentOfChannel (Channel.restrictToSupport P r)))
    (hcov : ∀ {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B] [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O),
        hV.V (Relabeling.relabelDist eA q) (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hV.V q (experimentOfChannel P))
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F) {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F) (hcov : FinalSelectedRelabelCovariance hhm)
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
    (hax : PureTraceConditions F) (hcov : FinalSelectedRelabelCovariance hhm)
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
    (hax : PureTraceConditions F) (hcov : FinalSelectedRelabelCovariance hhm)
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
    (hax : PureTraceConditions F) (hcov : FinalSelectedRelabelCovariance hhm)
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
    (hax : PureTraceConditions F) {A B O : Type u}
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
    (hax : PureTraceConditions F) {A B Y : Type u}
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
    (hax : PureTraceConditions F) {A B C : Type u}
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
    (hax : PureTraceConditions F) {A B C : Type u}
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
    (hax : PureTraceConditions F) {A B C : Type u}
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
    (hax : PureTraceConditions F) {A B : Type u}
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
    (hax : PureTraceConditions F) {A B : Type u}
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
    (hax : PureTraceConditions F) {A B : Type u}
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
    (hax : PureTraceConditions F) {A B : Type u}
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
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : ℝ :=
  hpair.rightCoeff hax faceScaleInteractionReferencePrior x /
    hpair.leftCoeff hax faceScaleInteractionReferencePrior x

theorem cobGauge_pos
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F) {B C : Type u}
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
    (hax : PureTraceConditions F) {A B B' : Type u}
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
    (hax : PureTraceConditions F) {A B B' : Type u}
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
    (hax : PureTraceConditions F) {A B B' : Type u}
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
    (hax : PureTraceConditions F) {A B B' : Type u}
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
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (x : Dist A) : ℝ := by
  classical
  exact
    if Subsingleton (supportSubtype x) then 1
    else
      hpair.rightCoeff hax faceScaleInteractionReferencePrior x.restrictToSupport /
        hpair.leftCoeff hax faceScaleInteractionReferencePrior x.restrictToSupport

theorem cobGaugeSF_pos
    (hpair : FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor hfaces)
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F) {A B : Type u}
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
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F) {A B : Type u}
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
    (hax : PureTraceConditions F) {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
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
    (hax : PureTraceConditions F) :
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
    (hax : PureTraceConditions F)
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
    (hax : PureTraceConditions F)
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

end TraceableAgency
