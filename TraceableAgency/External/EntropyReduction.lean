/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.ScaleCoherence
import TraceableAgency.External.SupportRestriction
import TraceableAgency.External.Relabeling
import TraceableAgency.Info.Identities

/-!
# External Entropy Reduction Assumptions

This file contains external assumptions for two paper-specific bridges:
the entropy reduction theorem, which derives
V̂_q(P) = H(q) - Σ m(o) H(r_o) from scale coherence, and the separate
unscaled cross-prior blockbridge, which universal scale converts to the
normalized bridge used downstream.

## Main definitions

* `FiniteCrossPriorBlockAssumptions` - the remaining coherent product content,
  now split down to law-level posterior value affinity, singleton handling,
  classical affine uniqueness, the product-slice
  intercept/slope identifications, and coherent gauge/κ normalization. Lean
  derives channel-level value public-mix affinity, base-value nonconstancy,
  product-slice public-mix affinity, coherent product quasi-additivity, the
  product-lift value identities, and assembles them with the internally proved
  product-block transfer before conversion to the scaled cross-prior block
  representation.

## Status

The entropy-reduction formula is now proved from `ScaleCoherenceStructure`.
No entropy-side external assumption is used for this bridge.  Regularity facts
such as nonnegativity and singleton-zero are part of the later Faddeev bridge,
where they are mathematically needed.

The entropy reduction theorem derives:
1. **Entropy definition**: H(q) := V̂_q(χ_q) where χ_q is full revelation
2. **Entropy reduction formula**: V̂_q(μ_{q,P}) = H(q) - Σ m(o) H(r_o)

The cross-prior bridge is exposed separately because the paper proves
Lemma blockbridge before entropy reduction and only later rescales it.

## References

* empowerment_v5.tex, Lemma faddeevsketch (lines 2504-2559)
* empowerment_v5.tex, Lemma blockbridge (lines 1776-1827)

The proof uses:
- Scale coherence (universal scale a)
- Chain rule: V̂_q(P▷{Q}) = V̂_q(P) + Σ m(o) V̂_{r_o}(Q^o)
- Full revelation refinement: P▷{Id} has posterior law χ_q
- Block bridge (Lemma blockbridge) for cross-prior representation
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
## Normalized Value and Entropy Candidate

Helpers for working with the rescaled value functional V̂ = V/a.
-/

/-- Normalized value V̂_q(P) = V_q(P) / a_q.
    Paper notation: V̂_q(μ_{q,P}) or F̂_q(μ_{q,P}) (line 2507). -/
noncomputable def normalizedValue
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) : ℝ :=
  hs.branch_agg.value_rep.V q (experimentOfChannel P) / hs.scale q

/-- Simp lemma for normalized value. -/
@[simp]
theorem normalizedValue_def
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    normalizedValue hs q P =
      hs.branch_agg.value_rep.V q (experimentOfChannel P) / hs.scale q := rfl

/-- Candidate entropy function H(q) := V̂_q(Id_A).
    Paper definition (line 2509): H(q) := F̂_q(χ_q) where χ_q is full-revelation.
    Since Id_A : A → Δ(A) induces χ_q as its posterior law, we use Id_A directly. -/
noncomputable def Hcandidate
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  normalizedValue hs q Channel.idChannel

/-- Simp lemma for entropy candidate. -/
@[simp]
theorem Hcandidate_def
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    Hcandidate hs q =
      hs.branch_agg.value_rep.V q (experimentOfChannel Channel.idChannel) / hs.scale q := rfl

/-!
## Entropy Reduction External Assumption

The entropy reduction theorem states that given scale coherence with universal scale:

1. **Entropy reduction formula**: V̂_q(μ_{q,P}) = H(q) - Σ m(o) H(r_o)

   Paper proof sketch (lines 2528-2545):
   - Append full revelation Id_A after P: the compound P▷{Id_A}
   - The overall posterior law of P▷{Id_A} is χ_q (full revelation)
   - Apply chain rule: V̂_q(χ_q) = V̂_q(P) + Σ m(o) V̂_{r_o}(χ_{r_o})
   - Rearrange: V̂_q(P) = H(q) - Σ m(o) H(r_o)

The normalized chain rule and full-revelation posterior-law refinement are
proved below.
-/

-- `posterior_idChannel_eq_pure_of_pos` is already proved in ScaleCoherence.lean
-- (with explicit `(a : A)` argument); we use it directly below via the import.

/-- Outcome marginal of `P` followed by full revelation. -/
theorem outcomeMarginal_seq_id_apply
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) (o : O) (a : A) :
    Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) =
      q a * P a o := by
  simp only [Channel.outcomeMarginal_apply, seqCompose_apply, Channel.idChannel,
    Dist.pure_apply]
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hba
    have hao : a ≠ b := fun h => hba h.symm
    simp [if_neg hao]

/-- Posterior of `P` followed by full revelation at a positive composite
outcome is the revealed point mass. -/
theorem posterior_seq_id_eq_pure_of_pos
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) {o : O} {a : A}
    (hpos : Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) > 0) :
    Channel.posterior (P ▷ fun _ => Channel.idChannel) q (o, a) = Dist.pure a := by
  ext b
  unfold Channel.posterior
  rw [dif_pos hpos]
  have hm :
      Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) =
        q a * P a o :=
    outcomeMarginal_seq_id_apply q P o a
  change q b * ((P ▷ fun _ => Channel.idChannel) b) (o, a) /
      Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) =
    (Dist.pure a) b
  rw [hm]
  by_cases hba : b = a
  · subst b
    simp [seqCompose_apply, Channel.idChannel, Dist.pure_apply_self,
      div_self (ne_of_gt (by rwa [hm] at hpos))]
  · have hab : a ≠ b := fun h => hba h.symm
    simp [seqCompose_apply, Channel.idChannel, Dist.pure_apply_ne _ _ hab,
      Dist.pure_apply_ne _ _ hba]

/-- Posterior-law integral of full revelation is the expectation over point
masses. -/
theorem posteriorLawIntegral_idChannel_eq_sum_pure
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (φ : Dist A → ℝ) :
    posteriorLawIntegral q Channel.idChannel φ =
      ∑ a : A, q a * φ (Dist.pure a) := by
  unfold posteriorLawIntegral
  apply Finset.sum_congr rfl
  intro a _
  rw [outcomeMarginal_idChannel']
  by_cases ha : q a > 0
  · rw [posterior_idChannel_eq_pure_of_pos q a ha]
  · have hzero : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
    simp [hzero]

/-- Posterior-law integral of `P` followed by full revelation is also the
expectation over point masses. -/
theorem posteriorLawIntegral_seq_id_eq_sum_pure
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (P ▷ fun _ => Channel.idChannel) φ =
      ∑ a : A, q a * φ (Dist.pure a) := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  have hterm :
      (∑ x : O, ∑ y : A,
        Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (x, y) *
          φ (Channel.posterior (P ▷ fun _ => Channel.idChannel) q (x, y))) =
      ∑ x : O, ∑ y : A, q y * P y x * φ (Dist.pure y) := by
    apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro a _
    by_cases hpos :
        Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) > 0
    · rw [posterior_seq_id_eq_pure_of_pos q P hpos,
        outcomeMarginal_seq_id_apply q P o a]
    · have hm0 :
        Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q (o, a) = 0 :=
        le_antisymm (le_of_not_gt hpos)
          ((Channel.outcomeMarginal (P ▷ fun _ => Channel.idChannel) q).nonneg (o, a))
      have hqa : q a * P a o = 0 := by
        rw [← outcomeMarginal_seq_id_apply q P o a, hm0]
      rw [hm0, hqa]
      ring
  rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ x : O, q a * P a x * φ (Dist.pure a))
        = q a * φ (Dist.pure a) * ∑ x : O, P a x := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro o _
          ring
    _ = q a * φ (Dist.pure a) := by
          rw [(P a).sum_eq_one, mul_one]

/-- `P` followed by full revelation has the same posterior law as full
revelation itself. -/
theorem posteriorLawIntegral_seq_id_eq_identity
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) :
    posteriorLawIntegral q (P ▷ fun _ => Channel.idChannel) φ =
      posteriorLawIntegral q Channel.idChannel φ := by
  rw [posteriorLawIntegral_seq_id_eq_sum_pure,
    posteriorLawIntegral_idChannel_eq_sum_pure]

/-- Experiment-level posterior-law equivalence for full revelation refinement. -/
theorem samePosteriorLaw_seq_id_full_revelation
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    SamePosteriorLawExp q
      (experimentOfChannel (P ▷ fun _ => Channel.idChannel))
      (experimentOfChannel Channel.idChannel) := by
  intro φ _hφ
  unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
  exact posteriorLawIntegral_seq_id_eq_identity q P φ

/-- Posterior-law invariance turns the full-revelation refinement into equality
of normalized values. -/
theorem normalizedValue_seq_id_eq_full_revelation
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    normalizedValue hs q (P ▷ fun _ => Channel.idChannel) =
      Hcandidate hs q := by
  unfold normalizedValue Hcandidate
  have hV :=
    hs.branch_agg.value_rep.respects_same_posterior_law q
      (experimentOfChannel (P ▷ fun _ => Channel.idChannel))
      (experimentOfChannel Channel.idChannel)
      (samePosteriorLaw_seq_id_full_revelation q P)
  rw [hV]
  rfl

/--
Normalized chain rule from branch aggregation and scale coherence.

The proof splits each branch on whether its first-stage probability is positive.
Positive branches use `branchCoeff_factorization`; zero branches vanish before
any coefficient or posterior-scale fact is needed.
-/
theorem normalizedValue_seqCompose_of_branchAggregation
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (hq : q.FullSupport)
    (P : Channel A O) (Q : O → Channel A Y) :
    normalizedValue hs q (P ▷ Q)
    =
    normalizedValue hs q P
      + ∑ o : O,
          (Channel.outcomeMarginal P q) o *
          normalizedValue hs (Channel.posterior P q o) (Q o) := by
  unfold normalizedValue
  have hsq_pos : 0 < hs.scale q := hs.scale_pos q hq
  have hsq_ne : hs.scale q ≠ 0 := ne_of_gt hsq_pos
  have hagg := hs.branch_agg.branch_aggregation q hq P Q
  rw [hagg]
  rw [add_div]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro o _
  by_cases hpos : (Channel.outcomeMarginal P q) o > 0
  · rw [hs.branchCoeff_factorization q hq P o hpos]
    field_simp [hsq_ne]
  · have hm0 : (Channel.outcomeMarginal P q) o = 0 :=
      le_antisymm (le_of_not_gt hpos) ((Channel.outcomeMarginal P q).nonneg o)
    rw [hm0]
    ring

/-- Full-revelation specialization of the normalized chain rule. -/
theorem normalized_chain_id_of_scale
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    normalizedValue hs q (P ▷ fun _ => Channel.idChannel)
    =
    normalizedValue hs q P + posteriorLawIntegral q P (Hcandidate hs) := by
  rw [normalizedValue_seqCompose_of_branchAggregation hs q hq P
    (fun _ => Channel.idChannel)]
  unfold posteriorLawIntegral Hcandidate
  rfl

/-- Entropy-reduction formula from normalized chain rule and full-revelation
posterior-law refinement. -/
theorem value_entropy_reduction_of_scale
    {F : PrefFamily.{u}} (hs : ScaleCoherenceStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    normalizedValue hs q P =
      Hcandidate hs q - posteriorLawIntegral q P (Hcandidate hs) := by
  have hrefine := normalizedValue_seq_id_eq_full_revelation hs q P
  have hchain_id := normalized_chain_id_of_scale hs q hq P
  linarith

/-- Construct entropy reduction from scale coherence. -/
noncomputable def EntropyReductionRepresentation_of_scale
    (F : PrefFamily.{u})
    (hs : ScaleCoherenceStructure F) :
    EntropyReductionRepresentation F where
  scale_coherence := hs
  Hfun := fun {A} [Fintype A] [DecidableEq A] [Nonempty A] q =>
    Hcandidate hs q
  value_entropy_reduction := fun {A O} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O] q hq P => by
    exact value_entropy_reduction_of_scale hs q hq P

/-- **Boundary Hfun identity, proved (not assumed) for the constructed entropy
representation.**

For the canonical entropy representation `EntropyReductionRepresentation_of_scale`,
the entropy candidate is *defined* as `Hfun q := Hcandidate hs q =
normalizedValue hs q Channel.idChannel`.  Hence the identity
`Hfun q = normalizedValue q (Id)` holds by `rfl` at *every* prior `q` — with no
full-support guard, no regularity hypothesis, and no boundary assumption.

This is the content that `FiniteCardinalSupportBoundaryAssumptions.Hfun_boundary_identity`
(and `FiniteHfunBoundaryIdentityAssumptions`) asserts as an external boundary
normalization.  For the representation actually built and used by the final theorem
it is definitional, so that boundary field carries no information here. -/
theorem hfun_eq_normalizedValue_idChannel_of_scale
    (F : PrefFamily.{u}) (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    (EntropyReductionRepresentation_of_scale F hs).Hfun q =
      normalizedValue (EntropyReductionRepresentation_of_scale F hs).scale_coherence q
        Channel.idChannel :=
  rfl

/-!
**Product lifts for the unscaled cross-prior blockbridge**

Paper Lemma blockbridge first compares `(q, P)` and `(r, Q)` after lifting both
to the product prior `q ⊗ r`, using `P ⊗ U_B` and `U_A ⊗ Q`.  These definitions
name that product-lifted comparison.
-/

/-- Product lift of a left-side channel: `P ⊗ U_B`. -/
noncomputable def leftProductLiftChannel
    {A B O : Type u} [Fintype A] [Fintype B] [Fintype O]
    (P : Channel A O) : Channel (A × B) (O × PUnit.{u + 1}) :=
  prodChannel P (Channel.uninformativeChannelU B)

/-- Product lift of a right-side channel: `U_A ⊗ Q`. -/
noncomputable def rightProductLiftChannel
    {A B Y : Type u} [Fintype A] [Fintype B] [Fintype Y]
    (Q : Channel B Y) : Channel (A × B) (PUnit.{u + 1} × Y) :=
  prodChannel (Channel.uninformativeChannelU A) Q

/-- Same-prior product-lifted block comparison at the product prior `q ⊗ r`. -/
def ProductLiftedComparison
    (F : PrefFamily.{u})
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (Q : Channel B Y) : Prop :=
  ExperimentPairPref F
    (experimentOfChannel (leftProductLiftChannel (B := B) P))
    (experimentOfChannel (rightProductLiftChannel (A := A) Q))
    (prodDist q r) (prodDist q r)

/-!
## Product projection and embedding kernels
-/

/-- Projection kernel `(a, b) ↦ a`. -/
noncomputable def fstProjectionKernel
    {A B : Type u} [Fintype A] [DecidableEq A] :
    Channel.ActionKernel (A × B) A :=
  fun ab => Dist.pure ab.1

/-- Projection kernel `(a, b) ↦ b`. -/
noncomputable def sndProjectionKernel
    {A B : Type u} [Fintype B] [DecidableEq B] :
    Channel.ActionKernel (A × B) B :=
  fun ab => Dist.pure ab.2

/-- Embedding kernel `a ↦ (a, b)` with background draw `b ~ r`. -/
noncomputable def leftEmbedKernel
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    (r : Dist B) : Channel.ActionKernel A (A × B) :=
  fun a => prodDist (Dist.pure a) r

/-- Embedding kernel `b ↦ (a, b)` with background draw `a ~ q`. -/
noncomputable def rightEmbedKernel
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (q : Dist A) : Channel.ActionKernel B (A × B) :=
  fun b => prodDist q (Dist.pure b)

/-- Outcome relabeling kernel `o ↦ (o, *)`. -/
noncomputable def outcomeRightUnitKernel
    {O : Type u} [Fintype O] [DecidableEq O] :
    Channel O (O × PUnit.{u + 1}) :=
  fun o => Dist.pure (o, PUnit.unit)

/-- Outcome projection kernel `(o, *) ↦ o`. -/
noncomputable def outcomeRightUnitProjectKernel
    {O : Type u} [Fintype O] [DecidableEq O] :
    Channel (O × PUnit.{u + 1}) O :=
  fun ou => Dist.pure ou.1

/-- Outcome relabeling kernel `y ↦ (*, y)`. -/
noncomputable def outcomeLeftUnitKernel
    {Y : Type u} [Fintype Y] [DecidableEq Y] :
    Channel Y (PUnit.{u + 1} × Y) :=
  fun y => Dist.pure (PUnit.unit, y)

/-- Outcome projection kernel `(*, y) ↦ y`. -/
noncomputable def outcomeLeftUnitProjectKernel
    {Y : Type u} [Fintype Y] [DecidableEq Y] :
    Channel (PUnit.{u + 1} × Y) Y :=
  fun uy => Dist.pure uy.2

/-- Copy a channel into the outcome type `O × PUnit`. -/
noncomputable def leftUnitOutcomeChannel
    {A O : Type u} [Fintype O] [DecidableEq O]
    (P : Channel A O) : Channel A (O × PUnit.{u + 1}) :=
  fun a => prodDist (P a) (Dist.pure PUnit.unit)

/-- Copy a channel into the outcome type `PUnit × Y`. -/
noncomputable def rightUnitOutcomeChannel
    {B Y : Type u} [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) : Channel B (PUnit.{u + 1} × Y) :=
  fun b => prodDist (Dist.pure PUnit.unit) (Q b)

@[simp]
theorem leftUnitOutcomeChannel_apply
    {A O : Type u} [Fintype O] [DecidableEq O]
    (P : Channel A O) (a : A) (o : O) :
    leftUnitOutcomeChannel P a (o, PUnit.unit) = P a o := by
  simp [leftUnitOutcomeChannel]

@[simp]
theorem rightUnitOutcomeChannel_apply
    {B Y : Type u} [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (b : B) (y : Y) :
    rightUnitOutcomeChannel Q b (PUnit.unit, y) = Q b y := by
  simp [rightUnitOutcomeChannel]

theorem postprocess_outcomeRightUnit_eq_leftUnitOutcome
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) :
    Channel.postprocess P outcomeRightUnitKernel =
      leftUnitOutcomeChannel P := by
  ext a ou
  rcases ou with ⟨o, u⟩
  cases u
  unfold Channel.postprocess outcomeRightUnitKernel leftUnitOutcomeChannel
  change (∑ o' : O, P a o' * Dist.pure (o', PUnit.unit) (o, PUnit.unit)) =
    (prodDist (P a) (Dist.pure PUnit.unit)) (o, PUnit.unit)
  rw [Fintype.sum_eq_single o]
  · simp
  · intro o' ho'ne
    have hne :
        (o', (PUnit.unit : PUnit.{u + 1})) ≠
          (o, (PUnit.unit : PUnit.{u + 1})) := by
      intro h
      exact ho'ne (Prod.ext_iff.mp h).1
    have hpure :
        (Dist.pure (o', (PUnit.unit : PUnit.{u + 1})) :
          Dist (O × PUnit.{u + 1})) (o, PUnit.unit) = 0 :=
      Dist.pure_apply_ne _ _ hne.symm
    rw [hpure]
    ring

theorem postprocess_leftUnitOutcome_project_eq
    {A O : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) :
    Channel.postprocess (leftUnitOutcomeChannel P) outcomeRightUnitProjectKernel =
      P := by
  ext a o
  unfold Channel.postprocess outcomeRightUnitProjectKernel
  change (∑ ou : O × PUnit.{u + 1},
      leftUnitOutcomeChannel P a ou * Dist.pure ou.1 o) = P a o
  rw [Fintype.sum_prod_type]
  simp [leftUnitOutcomeChannel, prodDist_apply_pair]
  rw [Fintype.sum_eq_single o]
  · simp
  · intro x hxne
    have hne : o ≠ x := fun h => hxne h.symm
    simp [Dist.pure_apply_ne _ _ hne]

theorem postprocess_outcomeLeftUnit_eq_rightUnitOutcome
    {B Y : Type u} [Fintype B] [DecidableEq B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) :
    Channel.postprocess Q outcomeLeftUnitKernel =
      rightUnitOutcomeChannel Q := by
  ext b uy
  rcases uy with ⟨u, y⟩
  cases u
  unfold Channel.postprocess outcomeLeftUnitKernel rightUnitOutcomeChannel
  change (∑ y' : Y, Q b y' * Dist.pure (PUnit.unit, y') (PUnit.unit, y)) =
    (prodDist (Dist.pure PUnit.unit) (Q b)) (PUnit.unit, y)
  rw [Fintype.sum_eq_single y]
  · simp
  · intro y' hy'ne
    have hne :
        ((PUnit.unit : PUnit.{u + 1}), y') ≠
          ((PUnit.unit : PUnit.{u + 1}), y) := by
      intro h
      exact hy'ne (Prod.ext_iff.mp h).2
    have hpure :
        (Dist.pure ((PUnit.unit : PUnit.{u + 1}), y') :
          Dist (PUnit.{u + 1} × Y)) (PUnit.unit, y) = 0 :=
      Dist.pure_apply_ne _ _ hne.symm
    rw [hpure]
    ring

theorem postprocess_rightUnitOutcome_project_eq
    {B Y : Type u} [Fintype B] [DecidableEq B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) :
    Channel.postprocess (rightUnitOutcomeChannel Q) outcomeLeftUnitProjectKernel =
      Q := by
  ext b y
  unfold Channel.postprocess outcomeLeftUnitProjectKernel
  change (∑ uy : PUnit.{u + 1} × Y,
      rightUnitOutcomeChannel Q b uy * Dist.pure uy.2 y) = Q b y
  rw [Fintype.sum_prod_type]
  simp [rightUnitOutcomeChannel, prodDist_apply_pair]
  rw [Fintype.sum_eq_single y]
  · simp
  · intro x hxne
    have hne : y ≠ x := fun h => hxne h.symm
    simp [Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_prod_fst
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward (prodDist q r) (fstProjectionKernel (A := A) (B := B)) = q := by
  ext a
  change (∑ ab : A × B, (prodDist q r) ab * Dist.pure ab.1 a) = q a
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single a]
  · simp [prodDist_apply_pair, ← Finset.mul_sum, r.sum_eq_one]
  · intro a' ha'ne
    apply Finset.sum_eq_zero
    intro b _
    have hne : a ≠ a' := fun h => ha'ne h.symm
    simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_prod_snd
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward (prodDist q r) (sndProjectionKernel (A := A) (B := B)) = r := by
  ext b
  change (∑ ab : A × B, (prodDist q r) ab * Dist.pure ab.2 b) = r b
  rw [Fintype.sum_prod_type]
  simp_rw [prodDist_apply_pair]
  rw [Finset.sum_comm]
  rw [Fintype.sum_eq_single b]
  · simp only [Dist.pure_apply_self, mul_one]
    calc
      (∑ i : A, q i * r b) = (∑ i : A, q i) * r b := by
        rw [Finset.sum_mul]
      _ = r b := by
        rw [q.sum_eq_one, one_mul]
  · intro b' hb'ne
    apply Finset.sum_eq_zero
    intro a _
    have hne : b ≠ b' := fun h => hb'ne h.symm
    simp [Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_leftEmbed
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward q (leftEmbedKernel (A := A) r) = prodDist q r := by
  ext ab
  rcases ab with ⟨a, b⟩
  change (∑ a' : A, q a' * prodDist (Dist.pure a') r (a, b)) =
    prodDist q r (a, b)
  rw [Fintype.sum_eq_single a]
  · simp [prodDist_apply_pair]
  · intro a' ha'ne
    have hne : a ≠ a' := fun h => ha'ne h.symm
    simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]

theorem actionPushforward_rightEmbed
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (q : Dist A) (r : Dist B) :
    Channel.actionPushforward r (rightEmbedKernel (B := B) q) = prodDist q r := by
  ext ab
  rcases ab with ⟨a, b⟩
  change (∑ b' : B, r b' * prodDist q (Dist.pure b') (a, b)) =
    prodDist q r (a, b)
  rw [Fintype.sum_eq_single b]
  · simp [prodDist_apply_pair, mul_comm]
  · intro b' hb'ne
    have hne : b ≠ b' := fun h => hb'ne h.symm
    simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]

theorem leftProductLift_isBayesPushforwardCompletion_fst
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (leftProductLiftChannel (B := B) P)
      (prodDist q r)
      (fstProjectionKernel (A := A) (B := B))
      (leftUnitOutcomeChannel P) := by
  intro a ha ou
  rcases ou with ⟨o, u⟩
  cases u
  have hpush := congrArg (fun d : Dist A => d a) (actionPushforward_prod_fst q r)
  have hqa : q a > 0 := by simpa [hpush] using ha
  have hnum :
      (∑ ab : A × B,
          prodDist q r ab * Dist.pure ab.1 a *
            leftProductLiftChannel (B := B) P ab (o, PUnit.unit)) =
        q a * P a o := by
    rw [Fintype.sum_prod_type]
    rw [Fintype.sum_eq_single a]
    · simp only [leftProductLiftChannel, prodDist_apply_pair, prodChannel_apply_pair,
        Channel.uninformativeChannelU, Dist.pure_apply_self, mul_one]
      have hsum :
          (∑ x : B, q a * r x * P a o) =
          (q a * P a o) * (∑ x : B, r x) := by
        simp_rw [show ∀ x : B, q a * r x * P a o = r x * (q a * P a o) by
          intro x
          ring]
        calc
          (∑ x : B, r x * (q a * P a o)) =
              (∑ x : B, r x) * (q a * P a o) := by
            rw [Finset.sum_mul]
          _ = (q a * P a o) * (∑ x : B, r x) := by
            ring
      rw [hsum, r.sum_eq_one]
      ring
    · intro a' ha'ne
      apply Finset.sum_eq_zero
      intro b _
      have hne : a ≠ a' := fun h => ha'ne h.symm
      simp [leftProductLiftChannel, prodDist_apply_pair, prodChannel_apply_pair,
        Dist.pure_apply_ne _ _ hne]
  change leftUnitOutcomeChannel P a (o, PUnit.unit) =
    (∑ ab : A × B,
        prodDist q r ab * Dist.pure ab.1 a *
          leftProductLiftChannel (B := B) P ab (o, PUnit.unit)) /
      (Channel.actionPushforward (prodDist q r) (fstProjectionKernel (A := A) (B := B))) a
  rw [hnum, hpush]
  simp [hqa.ne']

theorem rightProductLift_isBayesPushforwardCompletion_snd
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (rightProductLiftChannel (A := A) Q)
      (prodDist q r)
      (sndProjectionKernel (A := A) (B := B))
      (rightUnitOutcomeChannel Q) := by
  intro b hb uy
  rcases uy with ⟨u, y⟩
  cases u
  have hpush := congrArg (fun d : Dist B => d b) (actionPushforward_prod_snd q r)
  have hrb : r b > 0 := by simpa [hpush] using hb
  have hnum :
      (∑ ab : A × B,
          prodDist q r ab * Dist.pure ab.2 b *
            rightProductLiftChannel (A := A) Q ab (PUnit.unit, y)) =
        r b * Q b y := by
    rw [Fintype.sum_prod_type]
    simp_rw [prodDist_apply_pair]
    rw [Finset.sum_comm]
    rw [Fintype.sum_eq_single b]
    · simp only [rightProductLiftChannel, prodChannel_apply_pair,
        Channel.uninformativeChannelU, Dist.pure_apply_self, one_mul, mul_one]
      calc
        (∑ i : A, q i * r b * Q b y) =
            (∑ i : A, q i) * (r b * Q b y) := by
          simp_rw [show ∀ i : A, q i * r b * Q b y = q i * (r b * Q b y) by
            intro i
            ring]
          rw [Finset.sum_mul]
        _ = r b * Q b y := by
          rw [q.sum_eq_one, one_mul]
    · intro b' hb'ne
      apply Finset.sum_eq_zero
      intro a _
      have hne : b ≠ b' := fun h => hb'ne h.symm
      simp [rightProductLiftChannel, prodChannel_apply_pair,
        Dist.pure_apply_ne _ _ hne]
  change rightUnitOutcomeChannel Q b (PUnit.unit, y) =
    (∑ ab : A × B,
        prodDist q r ab * Dist.pure ab.2 b *
          rightProductLiftChannel (A := A) Q ab (PUnit.unit, y)) /
      (Channel.actionPushforward (prodDist q r) (sndProjectionKernel (A := A) (B := B))) b
  rw [hnum, hpush]
  simp [hrb.ne']

theorem leftUnitOutcome_isBayesPushforwardCompletion_leftEmbed
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (leftUnitOutcomeChannel P)
      q
      (leftEmbedKernel (A := A) r)
      (leftProductLiftChannel (B := B) P) := by
  intro ab hab ou
  rcases ab with ⟨a, b⟩
  rcases ou with ⟨o, u⟩
  cases u
  have hpush := congrArg (fun d : Dist (A × B) => d (a, b))
    (actionPushforward_leftEmbed q r)
  have hprod : q a * r b > 0 := by simpa [hpush, prodDist_apply_pair] using hab
  have hnum :
      (∑ a' : A,
          q a' * prodDist (Dist.pure a') r (a, b) *
            leftUnitOutcomeChannel P a' (o, PUnit.unit)) =
        q a * r b * P a o := by
    rw [Fintype.sum_eq_single a]
    · simp [prodDist_apply_pair, mul_assoc]
    · intro a' ha'ne
      have hne : a ≠ a' := fun h => ha'ne h.symm
      simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]
  change leftProductLiftChannel (B := B) P (a, b) (o, PUnit.unit) =
    (∑ a' : A,
        q a' * prodDist (Dist.pure a') r (a, b) *
          leftUnitOutcomeChannel P a' (o, PUnit.unit)) /
      (Channel.actionPushforward q (leftEmbedKernel (A := A) r)) (a, b)
  rw [hnum, hpush]
  simp [leftProductLiftChannel, prodChannel_apply_pair, Channel.uninformativeChannelU,
    prodDist_apply_pair, hprod.ne']

theorem rightUnitOutcome_isBayesPushforwardCompletion_rightEmbed
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    Channel.IsBayesPushforwardCompletion
      (rightUnitOutcomeChannel Q)
      r
      (rightEmbedKernel (B := B) q)
      (rightProductLiftChannel (A := A) Q) := by
  intro ab hab uy
  rcases ab with ⟨a, b⟩
  rcases uy with ⟨u, y⟩
  cases u
  have hpush := congrArg (fun d : Dist (A × B) => d (a, b))
    (actionPushforward_rightEmbed q r)
  have hprod : q a * r b > 0 := by simpa [hpush, prodDist_apply_pair] using hab
  have hnum :
      (∑ b' : B,
          r b' * prodDist q (Dist.pure b') (a, b) *
            rightUnitOutcomeChannel Q b' (PUnit.unit, y)) =
        q a * r b * Q b y := by
    rw [Fintype.sum_eq_single b]
    · simp [prodDist_apply_pair, mul_comm, mul_assoc]
    · intro b' hb'ne
      have hne : b ≠ b' := fun h => hb'ne h.symm
      simp [prodDist_apply_pair, Dist.pure_apply_ne _ _ hne]
  change rightProductLiftChannel (A := A) Q (a, b) (PUnit.unit, y) =
    (∑ b' : B,
        r b' * prodDist q (Dist.pure b') (a, b) *
          rightUnitOutcomeChannel Q b' (PUnit.unit, y)) /
      (Channel.actionPushforward r (rightEmbedKernel (B := B) q)) (a, b)
  rw [hnum, hpush]
  simp only [rightProductLiftChannel, prodChannel_apply_pair, Channel.uninformativeChannelU,
    one_mul]
  field_simp [hprod.ne']
  rw [prodDist_apply_pair]
  ring

/-!
## Product-block transfer from A3/A4/A5
-/

/-- Four labels for a common finite-block replacement environment. -/
inductive ProductBlockReplacementBlock : Type u
  | originalLeft
  | replacementLeft
  | originalRight
  | replacementRight
  deriving DecidableEq, Fintype

open ProductBlockReplacementBlock

/-- Action alphabets for the common product-block replacement environment. -/
def productBlockReplacementAct
    (A A' B B' : Type u) : ProductBlockReplacementBlock → Type u
  | originalLeft => A
  | replacementLeft => A'
  | originalRight => B
  | replacementRight => B'

noncomputable instance productBlockReplacementActFintype
    {A A' B B' : Type u} [Fintype A] [Fintype A'] [Fintype B] [Fintype B'] :
    ∀ k : ProductBlockReplacementBlock, Fintype (productBlockReplacementAct A A' B B' k)
  | originalLeft => show Fintype A from inferInstance
  | replacementLeft => show Fintype A' from inferInstance
  | originalRight => show Fintype B from inferInstance
  | replacementRight => show Fintype B' from inferInstance

instance productBlockReplacementActDecidableEq
    {A A' B B' : Type u} [DecidableEq A] [DecidableEq A'] [DecidableEq B]
    [DecidableEq B'] :
    ∀ k : ProductBlockReplacementBlock,
      DecidableEq (productBlockReplacementAct A A' B B' k)
  | originalLeft => show DecidableEq A from inferInstance
  | replacementLeft => show DecidableEq A' from inferInstance
  | originalRight => show DecidableEq B from inferInstance
  | replacementRight => show DecidableEq B' from inferInstance

/-- Outcome alphabets for the common product-block replacement environment. -/
def productBlockReplacementOut
    (O O' Y Y' : Type u) : ProductBlockReplacementBlock → Type u
  | originalLeft => O
  | replacementLeft => O'
  | originalRight => Y
  | replacementRight => Y'

noncomputable instance productBlockReplacementOutFintype
    {O O' Y Y' : Type u} [Fintype O] [Fintype O'] [Fintype Y] [Fintype Y'] :
    ∀ k : ProductBlockReplacementBlock, Fintype (productBlockReplacementOut O O' Y Y' k)
  | originalLeft => show Fintype O from inferInstance
  | replacementLeft => show Fintype O' from inferInstance
  | originalRight => show Fintype Y from inferInstance
  | replacementRight => show Fintype Y' from inferInstance

instance productBlockReplacementOutDecidableEq
    {O O' Y Y' : Type u} [DecidableEq O] [DecidableEq O'] [DecidableEq Y]
    [DecidableEq Y'] :
    ∀ k : ProductBlockReplacementBlock,
      DecidableEq (productBlockReplacementOut O O' Y Y' k)
  | originalLeft => show DecidableEq O from inferInstance
  | replacementLeft => show DecidableEq O' from inferInstance
  | originalRight => show DecidableEq Y from inferInstance
  | replacementRight => show DecidableEq Y' from inferInstance

/-- Channels for the common product-block replacement environment. -/
noncomputable def productBlockReplacementChannel
    {A A' B B' O O' Y Y' : Type u}
    [Fintype O] [Fintype O'] [Fintype Y] [Fintype Y']
    (P : Channel A O) (P' : Channel A' O')
    (Q : Channel B Y) (Q' : Channel B' Y') :
    ∀ k : ProductBlockReplacementBlock,
      Channel (productBlockReplacementAct A A' B B' k)
        (productBlockReplacementOut O O' Y Y' k)
  | originalLeft => show Channel A O from P
  | replacementLeft => show Channel A' O' from P'
  | originalRight => show Channel B Y from Q
  | replacementRight => show Channel B' Y' from Q'

/--
Common-block transfer: if each side of a two-block comparison is weakly
equivalent to a replacement side, then A3 and transitivity preserve the
pairwise comparison.
-/
theorem pairwise_product_block_replacement_from_weak_equiv
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A A' B B' O O' Y Y' : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype A'] [DecidableEq A']
    [Fintype B] [DecidableEq B]
    [Fintype B'] [DecidableEq B']
    [Fintype O] [DecidableEq O]
    [Fintype O'] [DecidableEq O']
    [Fintype Y] [DecidableEq Y]
    [Fintype Y'] [DecidableEq Y']
    (P : Channel A O) (P' : Channel A' O')
    (Q : Channel B Y) (Q' : Channel B' Y')
    (q : Dist A) (q' : Dist A') (r : Dist B) (r' : Dist B')
    (hleft_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q'))
    (hleft_to_old :
      F.rel (blockChannel P' P) (inlDist q') (inrDist q))
    (hright_to_new :
      F.rel (blockChannel Q Q') (inlDist r) (inrDist r'))
    (hright_to_old :
      F.rel (blockChannel Q' Q) (inlDist r') (inrDist r)) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      F.rel (blockChannel P' Q') (inlDist q') (inrDist r') := by
  classical
  let k0 : ProductBlockReplacementBlock.{u} := originalLeft
  let k1 : ProductBlockReplacementBlock.{u} := replacementLeft
  let k2 : ProductBlockReplacementBlock.{u} := originalRight
  let k3 : ProductBlockReplacementBlock.{u} := replacementRight
  let Act := productBlockReplacementAct A A' B B'
  let Out := productBlockReplacementOut O O' Y Y'
  let C := productBlockReplacementChannel P P' Q Q'
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act k0 q
  let x' := blockEmbedDist Act k1 q'
  let y := blockEmbedDist Act k2 r
  let y' := blockEmbedDist Act k3 r'
  have htrans :
      ∀ a b c : Dist ((k : ProductBlockReplacementBlock) × Act k),
        F.rel commonP a b → F.rel commonP b c → F.rel commonP a c :=
    (hax.a1.1 commonP).2
  have h02_ne : k0 ≠ k2 := by decide
  have h01_ne : k0 ≠ k1 := by decide
  have h10_ne : k1 ≠ k0 := by decide
  have h23_ne : k2 ≠ k3 := by decide
  have h32_ne : k3 ≠ k2 := by decide
  have h13_ne : k1 ≠ k3 := by decide
  have hcommon_02 :
      F.rel commonP x y ↔
        F.rel (blockChannel P Q) (inlDist q) (inrDist r) := by
    simpa [commonP, x, y, k0, k2, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using
      (hax.a3.2 (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k2) h02_ne
        (qᵢ := q) (qⱼ := r))
  have hcommon_01 : F.rel commonP x x' := by
    have h :=
      (hax.a3.2 (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k0) (j := k1) h01_ne
        (qᵢ := q) (qⱼ := q')).mpr hleft_to_new
    simpa [commonP, x, x', k0, k1, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hcommon_10 : F.rel commonP x' x := by
    have h :=
      (hax.a3.2 (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k0) h10_ne
        (qᵢ := q') (qⱼ := q)).mpr hleft_to_old
    simpa [commonP, x, x', k0, k1, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hcommon_23 : F.rel commonP y y' := by
    have h :=
      (hax.a3.2 (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k2) (j := k3) h23_ne
        (qᵢ := r) (qⱼ := r')).mpr hright_to_new
    simpa [commonP, y, y', k2, k3, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hcommon_32 : F.rel commonP y' y := by
    have h :=
      (hax.a3.2 (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k3) (j := k2) h32_ne
        (qᵢ := r') (qⱼ := r)).mpr hright_to_old
    simpa [commonP, y, y', k2, k3, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using h
  have hreplace : F.rel commonP x y ↔ F.rel commonP x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonP a b) htrans
      hcommon_01 hcommon_10 hcommon_23 hcommon_32
  have hcommon_13 :
      F.rel commonP x' y' ↔
        F.rel (blockChannel P' Q') (inlDist q') (inrDist r') := by
    simpa [commonP, x', y', k1, k3, Act, Out, C, productBlockReplacementAct,
      productBlockReplacementOut, productBlockReplacementChannel] using
      (hax.a3.2 (K := ProductBlockReplacementBlock) (Act := Act) (Out := Out) (P := C)
        (i := k1) (j := k3) h13_ne
        (qᵢ := q') (qⱼ := r'))
  exact hcommon_02.symm.trans (hreplace.trans hcommon_13)

theorem original_rel_leftUnitOutcome
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel (blockChannel P (leftUnitOutcomeChannel P)) (inlDist q) (inrDist q) := by
  have h := hax.a4 P outcomeRightUnitKernel q
  simpa [postprocess_outcomeRightUnit_eq_leftUnitOutcome P] using h

theorem leftUnitOutcome_rel_original
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) :
    F.rel (blockChannel (leftUnitOutcomeChannel P) P) (inlDist q) (inrDist q) := by
  have h := hax.a4 (leftUnitOutcomeChannel P) outcomeRightUnitProjectKernel q
  simpa [postprocess_leftUnitOutcome_project_eq P] using h

theorem original_rel_rightUnitOutcome
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {B Y : Type u} [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (r : Dist B) :
    F.rel (blockChannel Q (rightUnitOutcomeChannel Q)) (inlDist r) (inrDist r) := by
  have h := hax.a4 Q outcomeLeftUnitKernel r
  simpa [postprocess_outcomeLeftUnit_eq_rightUnitOutcome Q] using h

theorem rightUnitOutcome_rel_original
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {B Y : Type u} [Fintype B] [DecidableEq B] [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (r : Dist B) :
    F.rel (blockChannel (rightUnitOutcomeChannel Q) Q) (inlDist r) (inrDist r) := by
  have h := hax.a4 (rightUnitOutcomeChannel Q) outcomeLeftUnitProjectKernel r
  simpa [postprocess_rightUnitOutcome_project_eq Q] using h

theorem leftProductLift_rel_leftUnitOutcome
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (leftProductLiftChannel (B := B) P) (leftUnitOutcomeChannel P))
      (inlDist (prodDist q r)) (inrDist q) := by
  have h :=
    hax.a5 (leftProductLiftChannel (B := B) P) (prodDist q r)
      (fstProjectionKernel (A := A) (B := B)) (leftUnitOutcomeChannel P)
      (leftProductLift_isBayesPushforwardCompletion_fst P q r)
  simpa [actionPushforward_prod_fst q r] using h

theorem leftUnitOutcome_rel_leftProductLift
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (leftUnitOutcomeChannel P) (leftProductLiftChannel (B := B) P))
      (inlDist q) (inrDist (prodDist q r)) := by
  have h :=
    hax.a5 (leftUnitOutcomeChannel P) q (leftEmbedKernel (A := A) r)
      (leftProductLiftChannel (B := B) P)
      (leftUnitOutcome_isBayesPushforwardCompletion_leftEmbed P q r)
  simpa [actionPushforward_leftEmbed q r] using h

theorem rightProductLift_rel_rightUnitOutcome
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (rightProductLiftChannel (A := A) Q) (rightUnitOutcomeChannel Q))
      (inlDist (prodDist q r)) (inrDist r) := by
  have h :=
    hax.a5 (rightProductLiftChannel (A := A) Q) (prodDist q r)
      (sndProjectionKernel (A := A) (B := B)) (rightUnitOutcomeChannel Q)
      (rightProductLift_isBayesPushforwardCompletion_snd Q q r)
  simpa [actionPushforward_prod_snd q r] using h

theorem rightUnitOutcome_rel_rightProductLift
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (Q : Channel B Y) (q : Dist A) (r : Dist B) :
    F.rel (blockChannel (rightUnitOutcomeChannel Q) (rightProductLiftChannel (A := A) Q))
      (inlDist r) (inrDist (prodDist q r)) := by
  have h :=
    hax.a5 (rightUnitOutcomeChannel Q) r (rightEmbedKernel (B := B) q)
      (rightProductLiftChannel (A := A) Q)
      (rightUnitOutcome_isBayesPushforwardCompletion_rightEmbed Q q r)
  simpa [actionPushforward_rightEmbed q r] using h

theorem product_block_transfer_of_A5_A3
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      ProductLiftedComparison F q r P Q := by
  have horig_to_unit :
      F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
        F.rel (blockChannel (leftUnitOutcomeChannel P) (rightUnitOutcomeChannel Q))
          (inlDist q) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax P
      (leftUnitOutcomeChannel P) Q (rightUnitOutcomeChannel Q) q q r r
      (original_rel_leftUnitOutcome F hax P q)
      (leftUnitOutcome_rel_original F hax P q)
      (original_rel_rightUnitOutcome F hax Q r)
      (rightUnitOutcome_rel_original F hax Q r)
  have hunit_to_product :
      F.rel (blockChannel (leftUnitOutcomeChannel P) (rightUnitOutcomeChannel Q))
          (inlDist q) (inrDist r) ↔
        F.rel (blockChannel (leftProductLiftChannel (B := B) P)
            (rightProductLiftChannel (A := A) Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftUnitOutcomeChannel P) (leftProductLiftChannel (B := B) P)
      (rightUnitOutcomeChannel Q) (rightProductLiftChannel (A := A) Q)
      q (prodDist q r) r (prodDist q r)
      (leftUnitOutcome_rel_leftProductLift F hax P q r)
      (leftProductLift_rel_leftUnitOutcome F hax P q r)
      (rightUnitOutcome_rel_rightProductLift F hax Q q r)
      (rightProductLift_rel_rightUnitOutcome F hax Q q r)
  have hproduct :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (rightProductLiftChannel (A := A) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        ProductLiftedComparison F q r P Q := by
    rfl
  exact horig_to_unit.trans (hunit_to_product.trans hproduct)

/-- The same-prior product-lifted comparison is represented by the product-prior
value functional. This is internal: it is exactly
`PosteriorValueRepresentation.represents_block_comparisons` plus
`prodDist_fullSupport`. -/
theorem productLiftedComparison_represents
    (F : PrefFamily.{u})
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    ProductLiftedComparison F q r P Q ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) Q)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r _hq _hr
  exact
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (rightProductLiftChannel (A := A) Q))

/-- A8, transported through the same-prior value representation, says that the
value order between first-coordinate product experiments is independent of the
second-coordinate background. This is the ordinal product-coordinate
independence step of paper Lemma `coherentnorm`; the later cardinal bilinear
form is kept separate. -/
theorem product_left_coordinate_value_order_independent
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B O O₂R O₂S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype O₂R] [DecidableEq O₂R]
    [Fintype O₂S] [DecidableEq O₂S]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) (R : Channel B O₂R) (S : Channel B O₂S) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q R)) ↔
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P S)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q S)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel Q R))
  have hS :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P S))
      (experimentOfChannel (prodChannel Q S))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q R)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel P S) (prodChannel Q S))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P S)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q S)) at hS'
  exact hR'.symm.trans ((hax.a8.1 q r hq hr P Q R S).trans hS')

/-- Symmetric A8 value-order independence for second-coordinate product
experiments. -/
theorem product_right_coordinate_value_order_independent
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B O₁R O₁S O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O₁R] [DecidableEq O₁R]
    [Fintype O₁S] [DecidableEq O₁S]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel A O₁R) (S : Channel A O₁S) (P Q : Channel B O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R P)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R Q)) ↔
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S P)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S Q)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel R P))
      (experimentOfChannel (prodChannel R Q))
  have hS :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel S P))
      (experimentOfChannel (prodChannel S Q))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel R P) (prodChannel R Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R Q)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel S P) (prodChannel S Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S Q)) at hS'
  exact hR'.symm.trans ((hax.a8.2 q r hq hr R S P Q).trans hS')

/-- Product left-slice value functional:
`P ↦ V_{q⊗r}(P⊗R)` for fixed full-support product prior and fixed
second-coordinate background. -/
noncomputable def productLeftSliceValue
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y)
    (P : Channel A O) : ℝ :=
  hs.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Product left-slice order with no-information background is the original
first-coordinate order. This is the projection/embedding part of Step 1 of
paper Lemma `coherentnorm`, proved from the A3/A4/A5 weak-equivalence
machinery internalized in Stage 10C. -/
theorem product_left_noInfo_value_order_iff_base
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) Q)) ↔
    hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
  have hprod_rel :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) := by
    change
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftProductLiftChannel (B := B) P) (leftUnitOutcomeChannel P)
      (leftProductLiftChannel (B := B) Q) (leftUnitOutcomeChannel Q)
      (prodDist q r) q (prodDist q r) q
      (leftProductLift_rel_leftUnitOutcome F hax P q r)
      (leftUnitOutcome_rel_leftProductLift F hax P q r)
      (leftProductLift_rel_leftUnitOutcome F hax Q q r)
      (leftUnitOutcome_rel_leftProductLift F hax Q q r)
  have hunit_to_base :
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) ↔
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftUnitOutcomeChannel P) P
      (leftUnitOutcomeChannel Q) Q
      q q q q
      (leftUnitOutcome_rel_original F hax P q)
      (original_rel_leftUnitOutcome F hax P q)
      (leftUnitOutcome_rel_original F hax Q q)
      (original_rel_leftUnitOutcome F hax Q q)
  have hbase_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      q hq (experimentOfChannel P) (experimentOfChannel Q)
  have hbase_rel :
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
    change
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- For a fixed second-coordinate background, the product left-slice value and
the original first-coordinate value represent the same weak order. This is the
Lean version of Step 1 of paper Lemma `coherentnorm` for first-coordinate
slices. -/
theorem product_left_slice_same_order
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) (R : Channel B Y) :
    productLeftSliceValue hs q r R P ≥ productLeftSliceValue hs q r R Q ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
  have hbackground :=
    product_left_coordinate_value_order_independent F hax hs
      q r hq hr P Q R (Channel.uninformativeChannelU B)
  have hbase :=
    product_left_noInfo_value_order_iff_base F hax hs q r hq hr P Q
  exact (by
    simpa [productLeftSliceValue, leftProductLiftChannel] using
      hbackground.trans hbase)

/-- Product right-slice value functional:
`R ↦ V_{q⊗r}(P⊗R)` for fixed full-support product prior and fixed
first-coordinate background. -/
noncomputable def productRightSliceValue
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O)
    (R : Channel B Y) : ℝ :=
  hs.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Product right-slice with no-information first-coordinate background recovers
the base second-coordinate order. Proved from A3/A4/A5 projection/embedding
machinery (right-side analogue of `product_left_noInfo_value_order_iff_base`). -/
theorem product_right_noInfo_value_order_iff_base
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R S : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) S)) ↔
    hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (rightProductLiftChannel (A := A) R))
      (experimentOfChannel (rightProductLiftChannel (A := A) S))
  have hprod_rel :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) := by
    change
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightProductLiftChannel (A := A) R) (rightUnitOutcomeChannel R)
      (rightProductLiftChannel (A := A) S) (rightUnitOutcomeChannel S)
      (prodDist q r) r (prodDist q r) r
      (rightProductLift_rel_rightUnitOutcome F hax R q r)
      (rightUnitOutcome_rel_rightProductLift F hax R q r)
      (rightProductLift_rel_rightUnitOutcome F hax S q r)
      (rightUnitOutcome_rel_rightProductLift F hax S q r)
  have hunit_to_base :
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) ↔
      F.rel (blockChannel R S) (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightUnitOutcomeChannel R) R
      (rightUnitOutcomeChannel S) S
      r r r r
      (rightUnitOutcome_rel_original F hax R r)
      (original_rel_rightUnitOutcome F hax R r)
      (rightUnitOutcome_rel_original F hax S r)
      (original_rel_rightUnitOutcome F hax S r)
  have hbase_rep :=
    hs.branch_agg.value_rep.represents_block_comparisons
      r hr (experimentOfChannel R) (experimentOfChannel S)
  have hbase_rel :
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
    change
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- For a fixed first-coordinate background, the product right-slice value and
the original second-coordinate value represent the same weak order. Right-side
analogue of `product_left_slice_same_order`. -/
theorem product_right_slice_same_order
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R S : Channel B Y) :
    productRightSliceValue hs q r P R ≥ productRightSliceValue hs q r P S ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
  have hbackground :=
    product_right_coordinate_value_order_independent F hax hs
      q r hq hr (Channel.uninformativeChannelU A) P R S
  have hbase :=
    product_right_noInfo_value_order_iff_base F hax hs q r hq hr R S
  exact (by
    simpa [productRightSliceValue, rightProductLiftChannel] using
      hbackground.symm.trans hbase)

/--
**Product Left-Slice Affine Assumptions**

Paper-specific cardinal content from the first half of Step 2 of Lemma
`coherentnorm`. After product-coordinate order independence, affine-utility
uniqueness makes each first-coordinate slice a positive affine transform of the
first-coordinate representative:

`L_{q,r}(P,R) = α_R V_q(P) + γ_R`.
-/
structure FiniteProductLeftSliceAffineAssumptions.{v} where
  leftSliceSlope :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftSliceIntercept :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B Y : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      [Fintype Y] → [DecidableEq Y] →
      Dist A → Dist B → Channel B Y → ℝ
  leftSliceSlope_pos :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      0 < leftSliceSlope F hax hs q r R
  left_slice_affine :
    ∀ (F : PrefFamily.{v})
      (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftSliceSlope F hax hs q r R *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        leftSliceIntercept F hax hs q r R

/--
**Affine Slice Uniqueness Assumptions**

Paper-specific affine/HM uniqueness content behind Step 2 of Lemma
`coherentnorm`. The same-order fact for product left-slices is proved above;
what remains external here is the cardinal theorem that two nonconstant affine
representatives of that order differ by a positive affine transform.
-/
structure FiniteAffineSliceUniquenessAssumptions.{v} where
  left_slice_positive_affine_transform :
    ∀ (F : PrefFamily.{v})
      (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          productLeftSliceValue hs q r R P =
            a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b

/-- Left outcome marginal of a public-coin mixture. -/
theorem outcomeMarginal_publicMixChannel_inl
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (o : O) :
    Channel.outcomeMarginal (publicMixChannel t ht0 ht1 P Q) q (Sum.inl o) =
      t * Channel.outcomeMarginal P q o := by
  simp only [Channel.outcomeMarginal_apply, publicMixChannel]
  rw [Finset.mul_sum]
  congr 1
  ext a
  ring

/-- Right outcome marginal of a public-coin mixture. -/
theorem outcomeMarginal_publicMixChannel_inr
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (y : Y) :
    Channel.outcomeMarginal (publicMixChannel t ht0 ht1 P Q) q (Sum.inr y) =
      (1 - t) * Channel.outcomeMarginal Q q y := by
  simp only [Channel.outcomeMarginal_apply, publicMixChannel]
  rw [Finset.mul_sum]
  congr 1
  ext a
  ring

/-- Left branch posterior of a public-coin mixture. -/
theorem posterior_publicMixChannel_inl
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (o : O) :
    Channel.posterior (publicMixChannel t ht0 ht1 P Q) q (Sum.inl o) =
      Channel.posterior P q o := by
  ext a
  unfold Channel.posterior
  simp only [outcomeMarginal_publicMixChannel_inl]
  by_cases hm : Channel.outcomeMarginal P q o > 0
  · have hm_sum : 0 < ∑ x, q x * P x o := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have htm_sum : 0 < t * ∑ x, q x * P x o := mul_pos ht0 hm_sum
    simp [hm_sum, htm_sum, publicMixChannel]
    field_simp [ne_of_gt ht0]
  · have hm0 : Channel.outcomeMarginal P q o = 0 := by
      exact le_antisymm (not_lt.mp hm) ((Channel.outcomeMarginal P q).nonneg o)
    have hm_sum_nonpos : ¬ 0 < ∑ x, q x * P x o := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have hm_sum_eq : (∑ x, q x * P x o) = 0 := by
      simpa [Channel.outcomeMarginal_apply] using hm0
    have htm_sum_nonpos : ¬ 0 < t * ∑ x, q x * P x o := by
      simp [hm_sum_eq]
    simp [hm_sum_nonpos, htm_sum_nonpos]

/-- Right branch posterior of a public-coin mixture. -/
theorem posterior_publicMixChannel_inr
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (y : Y) :
    Channel.posterior (publicMixChannel t ht0 ht1 P Q) q (Sum.inr y) =
      Channel.posterior Q q y := by
  ext a
  unfold Channel.posterior
  simp only [outcomeMarginal_publicMixChannel_inr]
  have h1t_pos : 0 < 1 - t := by linarith
  by_cases hm : Channel.outcomeMarginal Q q y > 0
  · have hm_sum : 0 < ∑ x, q x * Q x y := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have htm_sum : 0 < (1 - t) * ∑ x, q x * Q x y :=
      mul_pos h1t_pos hm_sum
    simp [hm_sum, htm_sum, publicMixChannel]
    field_simp [ne_of_gt h1t_pos]
  · have hm0 : Channel.outcomeMarginal Q q y = 0 := by
      exact le_antisymm (not_lt.mp hm) ((Channel.outcomeMarginal Q q).nonneg y)
    have hm_sum_nonpos : ¬ 0 < ∑ x, q x * Q x y := by
      simpa [Channel.outcomeMarginal_apply] using hm
    have hm_sum_eq : (∑ x, q x * Q x y) = 0 := by
      simpa [Channel.outcomeMarginal_apply] using hm0
    have htm_sum_nonpos : ¬ 0 < (1 - t) * ∑ x, q x * Q x y := by
      simp [hm_sum_eq]
    simp [hm_sum_nonpos, htm_sum_nonpos]

/--
Public-coin mixtures of implementing channels induce convex mixtures of
posterior laws, stated extensionally through posterior-law integrals.
-/
theorem posteriorLawIntegral_publicMixChannel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y)
    (φ : Dist A → ℝ) :
    posteriorLawIntegral q (publicMixChannel t ht0 ht1 P Q) φ =
      t * posteriorLawIntegral q P φ +
        (1 - t) * posteriorLawIntegral q Q φ := by
  unfold posteriorLawIntegral
  rw [Fintype.sum_sum_type]
  simp only [outcomeMarginal_publicMixChannel_inl,
    outcomeMarginal_publicMixChannel_inr,
    posterior_publicMixChannel_inl,
    posterior_publicMixChannel_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring_nf

/--
**Posterior-Law Value Affinity**

Herstein--Milnor/value-representation interface content: the chosen posterior
value representative is affine over convex mixtures of posterior laws.  The
posterior laws are represented extensionally by their posterior-law integrals.
-/
structure FinitePosteriorLawValueAffineAssumptions.{v} where
  V_affine_of_posteriorLawIntegral_mix :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hV : PosteriorValueRepresentation F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (_ht0 : 0 < t) (_ht1 : t < 1)
      (E_mix E₁ E₂ : FiniteExperimentOn A),
      (∀ φ : Dist A → ℝ, Continuous φ →
        posteriorLawIntegralExp q E_mix φ =
          t * posteriorLawIntegralExp q E₁ φ +
            (1 - t) * posteriorLawIntegralExp q E₂ φ) →
      hV.V q E_mix = t * hV.V q E₁ + (1 - t) * hV.V q E₂

/--
**Posterior Value Public-Mix Affinity**

Compatibility package for public-coin mixtures of implementing channels.  Stage
10K derives this from the structural posterior-law mixture identity plus the
law-level Herstein--Milnor value-affinity interface.
-/
structure FinitePosteriorValueAffineAssumptions.{v} where
  V_publicMix_affine :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hV : PosteriorValueRepresentation F)
      {A O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Y),
      hV.V q (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
        t * hV.V q (experimentOfChannel P) +
          (1 - t) * hV.V q (experimentOfChannel Q)

theorem posteriorValueAffine_of_lawAffine_and_publicMixLaw
    (hlaw : FinitePosteriorLawValueAffineAssumptions.{u}) :
    FinitePosteriorValueAffineAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hV A O Y _ _ _ _ _ _ _ q hq t ht0 ht1 P Q
  exact
    hlaw.V_affine_of_posteriorLawIntegral_mix
      F hax hV q hq t ht0 ht1
      (experimentOfChannel (publicMixChannel t ht0 ht1 P Q))
      (experimentOfChannel P)
      (experimentOfChannel Q)
      (by
        intro φ _hφ
        unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
        exact posteriorLawIntegral_publicMixChannel q t ht0 ht1 P Q φ)

/-- Global finite Herstein--Milnor mixture-space representation consequences.

This is the single global fallback interface for the known finite
Herstein--Milnor theorem.  It is not branch-specific or interaction-collapse
specific: it supplies the two posterior-law consequences used downstream,
namely public-mixture affinity of the selected posterior-value representative
and its finite posterior-integral form. -/
structure ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{v} where
  posterior_law_value_affine :
    FinitePosteriorLawValueAffineAssumptions.{v}
  posterior_integral_representation :
    FinitePosteriorIntegralRepresentationAssumptions.{v}

/-- Posterior-law value affinity extracted from the global finite
Herstein--Milnor mixture-space representation theorem. -/
theorem finitePosteriorLawValueAffine_of_HM
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u}) :
    FinitePosteriorLawValueAffineAssumptions.{u} :=
  hhm.posterior_law_value_affine

/-- Posterior integral representation extracted from the global finite
Herstein--Milnor mixture-space representation theorem. -/
noncomputable def finitePosteriorIntegralRepresentation_of_HM
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u}) :
    FinitePosteriorIntegralRepresentationAssumptions.{u} :=
  hhm.posterior_integral_representation

/-- The branch affine-linear-part package follows from the posterior integral
representation supplied by the global finite Herstein--Milnor theorem. -/
noncomputable def finiteAffineLinearPartAssumptions_of_HM
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u}) :
    FiniteAffineLinearPartAssumptions.{u} :=
  finiteAffineLinearPartAssumptions_of_integralRepresentation
    hhm.posterior_integral_representation

/-- Canonical outcome equivalence distributing product over a public-mix sum:
`((O ⊕ Z) × Y) ≃ ((O × Y) ⊕ (Z × Y))`. -/
def prodSumDistribEquiv (O Z Y : Type u) :
    ((O ⊕ Z) × Y) ≃ ((O × Y) ⊕ (Z × Y)) where
  toFun oy :=
    match oy.1 with
    | Sum.inl o => Sum.inl (o, oy.2)
    | Sum.inr z => Sum.inr (z, oy.2)
  invFun s :=
    match s with
    | Sum.inl oy => (Sum.inl oy.1, oy.2)
    | Sum.inr zy => (Sum.inr zy.1, zy.2)
  left_inv := by
    intro oy
    cases oy with
    | mk oz y =>
      cases oz <;> rfl
  right_inv := by
    intro s
    cases s with
    | inl oy =>
      cases oy
      rfl
    | inr zy =>
      cases zy
      rfl

@[simp]
theorem prodSumDistribEquiv_inl (o : O) (y : Y) :
    prodSumDistribEquiv O Z Y (Sum.inl o, y) = Sum.inl (o, y) := rfl

@[simp]
theorem prodSumDistribEquiv_inr (z : Z) (y : Y) :
    prodSumDistribEquiv O Z Y (Sum.inr z, y) = Sum.inr (z, y) := rfl

/-- Deterministic outcome kernel induced by an outcome equivalence.  This local
copy avoids importing the later Faddeev relabeling file into the upstream
entropy/cross-prior layer. -/
noncomputable def posteriorLawEquivKernel
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) : Channel O Y :=
  fun o => Dist.pure (e o)

@[simp]
theorem posteriorLawEquivKernel_apply
    {O Y : Type u} [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (o : O) (y : Y) :
    posteriorLawEquivKernel e o y = if y = e o then 1 else 0 := rfl

/-- Postprocessing by a deterministic outcome equivalence simply relabels the
row probabilities. -/
theorem postprocess_posteriorLawEquivKernel_apply
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (P : Channel A O) (a : A) (y : Y) :
    Channel.postprocess P (posteriorLawEquivKernel e) a y = P a (e.symm y) := by
  change (∑ o : O, P a o * Dist.pure (e o) y) = P a (e.symm y)
  rw [Fintype.sum_eq_single (e.symm y)]
  · simp
  · intro o hone
    have hne : y ≠ e o := by
      intro hy
      apply hone
      exact e.injective (by simpa using hy.symm)
    simp [Dist.pure_apply_ne _ _ hne]

/-- Outcome marginals relabel under deterministic bijective postprocessing. -/
theorem outcomeMarginal_postprocess_posteriorLawEquivKernel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) (y : Y) :
    Channel.outcomeMarginal (Channel.postprocess P (posteriorLawEquivKernel e)) q y =
      Channel.outcomeMarginal P q (e.symm y) := by
  simp [Channel.outcomeMarginal_apply, postprocess_posteriorLawEquivKernel_apply]

/-- Posteriors relabel under deterministic bijective postprocessing. -/
theorem posterior_postprocess_posteriorLawEquivKernel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) (y : Y) :
    Channel.posterior (Channel.postprocess P (posteriorLawEquivKernel e)) q y =
      Channel.posterior P q (e.symm y) := by
  ext a
  unfold Channel.posterior
  simp [postprocess_posteriorLawEquivKernel_apply]

/-- Posterior-law integrals are invariant under deterministic bijective
postprocessing of outcomes. -/
theorem posteriorLawIntegral_postprocess_posteriorLawEquivKernel
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) (φ : Dist A → ℝ) :
    posteriorLawIntegral q P φ =
      posteriorLawIntegral q (Channel.postprocess P (posteriorLawEquivKernel e)) φ := by
  unfold posteriorLawIntegral
  let f : O → ℝ := fun o =>
    Channel.outcomeMarginal P q o * φ (Channel.posterior P q o)
  let g : Y → ℝ := fun y =>
    Channel.outcomeMarginal (Channel.postprocess P (posteriorLawEquivKernel e)) q y *
      φ (Channel.posterior (Channel.postprocess P (posteriorLawEquivKernel e)) q y)
  change (∑ o : O, f o) = ∑ y : Y, g y
  exact Fintype.sum_equiv e f g (by
    intro o
    dsimp [f, g]
    simp [postprocess_posteriorLawEquivKernel_apply,
      posterior_postprocess_posteriorLawEquivKernel])

/-- Experiments have the same posterior law after deterministic bijective
postprocessing of outcomes. -/
theorem samePosteriorLawExp_of_bijective_postprocess
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (e : O ≃ Y) :
    SamePosteriorLawExp q
      (experimentOfChannel P)
      (experimentOfChannel (Channel.postprocess P (posteriorLawEquivKernel e))) := by
  intro φ _hφ
  unfold posteriorLawIntegralExp experimentOfChannel FiniteExperimentOn.ofChannel
  exact posteriorLawIntegral_postprocess_posteriorLawEquivKernel q P e φ

/-- Deterministic outcome kernel induced by `prodSumDistribEquiv`. -/
noncomputable def prodSumDistribKernel
    {O Z Y : Type u} [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] :
    Channel ((O ⊕ Z) × Y) ((O × Y) ⊕ (Z × Y)) :=
  posteriorLawEquivKernel (prodSumDistribEquiv O Z Y)

theorem prodSumDistribKernel_eq_posteriorLawEquivKernel
    {O Z Y : Type u} [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y] :
    prodSumDistribKernel (O := O) (Z := Z) (Y := Y) =
      posteriorLawEquivKernel (prodSumDistribEquiv O Z Y) := rfl

/--
At the channel level, taking a product with a fixed background channel commutes
with public mixing in the first coordinate, up to the canonical outcome
relabeling `prodSumDistribEquiv`.
-/
theorem prodChannel_publicMix_left_postprocess
    {A B O Z Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    [Fintype Y] [DecidableEq Y]
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Z) (R : Channel B Y) :
    Channel.postprocess
        (prodChannel (publicMixChannel t ht0 ht1 P Q) R)
        (prodSumDistribKernel (O := O) (Z := Z) (Y := Y)) =
      publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R) := by
  ext ab s
  rcases ab with ⟨a, b⟩
  cases s with
  | inl oy =>
    rcases oy with ⟨o, y⟩
    change
      (∑ oy' : (O ⊕ Z) × Y,
          (publicMixChannel t ht0 ht1 P Q a oy'.1 * R b oy'.2) *
            Dist.pure (prodSumDistribEquiv O Z Y oy') (Sum.inl (o, y))) =
        t * (P a o * R b y)
    rw [Fintype.sum_eq_single ((Sum.inl o : O ⊕ Z), y)]
    · simp [prodSumDistribEquiv, publicMixChannel]
      ring
    · intro oy' hoy'
      rcases oy' with ⟨oz, y'⟩
      by_cases hmap : prodSumDistribEquiv O Z Y (oz, y') = Sum.inl (o, y)
      · have hsource : (oz, y') = ((Sum.inl o : O ⊕ Z), y) := by
          cases oz with
          | inl o' =>
            simp only [prodSumDistribEquiv_inl, Sum.inl.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨ho, hy⟩
            subst ho
            subst hy
            rfl
          | inr z =>
            simp [prodSumDistribEquiv_inr] at hmap
        exact (hoy' hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquiv O Z Y (oz, y')) (Sum.inl (o, y)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]
  | inr zy =>
    rcases zy with ⟨z, y⟩
    change
      (∑ oy' : (O ⊕ Z) × Y,
          (publicMixChannel t ht0 ht1 P Q a oy'.1 * R b oy'.2) *
            Dist.pure (prodSumDistribEquiv O Z Y oy') (Sum.inr (z, y))) =
        (1 - t) * (Q a z * R b y)
    rw [Fintype.sum_eq_single ((Sum.inr z : O ⊕ Z), y)]
    · simp [prodSumDistribEquiv, publicMixChannel]
      ring
    · intro oy' hoy'
      rcases oy' with ⟨oz, y'⟩
      by_cases hmap : prodSumDistribEquiv O Z Y (oz, y') = Sum.inr (z, y)
      · have hsource : (oz, y') = ((Sum.inr z : O ⊕ Z), y) := by
          cases oz with
          | inl o =>
            simp [prodSumDistribEquiv_inl] at hmap
          | inr z' =>
            simp only [prodSumDistribEquiv_inr, Sum.inr.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨hz, hy⟩
            subst hz
            subst hy
            rfl
        exact (hoy' hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquiv O Z Y (oz, y')) (Sum.inr (z, y)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]

/--
Narrow posterior-law compatibility left after the channel-level equality:
posterior laws are unchanged by the canonical finite outcome relabeling that
identifies `prodChannel (publicMix P Q) R` with the public mixture of product
channels. This is structural channel/posterior-law content, not an economic
axiom.
-/
structure FiniteProductPublicMixPosteriorLawAssumptions.{v} where
  samePosteriorLaw_prod_publicMix_left :
    ∀ {A B O Z Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B)
      (R : Channel B Y)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R)))

theorem samePosteriorLaw_prod_publicMix_left_of_postprocess
    {A B O Z Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (R : Channel B Y)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Z) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) := by
  let PmixProd := prodChannel (publicMixChannel t ht0 ht1 P Q) R
  have hsame :
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel PmixProd)
        (experimentOfChannel
          (Channel.postprocess PmixProd
            (posteriorLawEquivKernel (prodSumDistribEquiv O Z Y)))) :=
    samePosteriorLawExp_of_bijective_postprocess
      (prodDist q r) PmixProd (prodSumDistribEquiv O Z Y)
  have hchan :
      Channel.postprocess PmixProd
          (posteriorLawEquivKernel (prodSumDistribEquiv O Z Y)) =
        publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R) := by
    simpa [PmixProd, prodSumDistribKernel_eq_posteriorLawEquivKernel] using
      (prodChannel_publicMix_left_postprocess
        (t := t) (ht0 := ht0) (ht1 := ht1) (P := P) (Q := Q) (R := R))
  simpa [PmixProd, hchan] using hsame

theorem productPublicMixPosteriorLaw_of_structural :
    FiniteProductPublicMixPosteriorLawAssumptions.{u} where
  samePosteriorLaw_prod_publicMix_left := by
    intro A B O Z Y _ _ _ _ _ _ _ _ _ _ _ _ q r R t ht0 ht1 P Q
    exact samePosteriorLaw_prod_publicMix_left_of_postprocess q r R t ht0 ht1 P Q

/-!
## Right-Side Product/Public-Mix Posterior-Law Compatibility

Mirror of the left-side machinery: shows that mixing in the second coordinate
inside a product channel is equivalent (up to outcome relabeling) to the public
mixture of the two product channels. This is Stage 10P structural content.
-/

/-- Right-side product/sum distributivity: `O × (Y ⊕ Z) ≃ (O × Y) ⊕ (O × Z)`. -/
def prodSumDistribEquivRight (O Y Z : Type u) :
    (O × (Y ⊕ Z)) ≃ ((O × Y) ⊕ (O × Z)) where
  toFun oys :=
    match oys.2 with
    | Sum.inl y => Sum.inl (oys.1, y)
    | Sum.inr z => Sum.inr (oys.1, z)
  invFun s :=
    match s with
    | Sum.inl oy => (oy.1, Sum.inl oy.2)
    | Sum.inr oz => (oz.1, Sum.inr oz.2)
  left_inv := by
    intro ⟨o, yz⟩
    cases yz <;> rfl
  right_inv := by
    intro s
    cases s with
    | inl oy => cases oy; rfl
    | inr oz => cases oz; rfl

@[simp]
theorem prodSumDistribEquivRight_inl (o : O) (y : Y) :
    prodSumDistribEquivRight O Y Z (o, Sum.inl y) = Sum.inl (o, y) := rfl

@[simp]
theorem prodSumDistribEquivRight_inr (o : O) (z : Z) :
    prodSumDistribEquivRight O Y Z (o, Sum.inr z) = Sum.inr (o, z) := rfl

/-- Right-side product/public-mix channel postprocessing: mixing in the second
coordinate of a product channel, then relabeling outcomes, equals the public
mixture of the two product channels. -/
theorem prodChannel_publicMix_right_postprocess
    {A B O Y Z : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (R : Channel B Y) (S : Channel B Z) :
    Channel.postprocess
        (prodChannel P (publicMixChannel t ht0 ht1 R S))
        (posteriorLawEquivKernel (prodSumDistribEquivRight O Y Z)) =
      publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S) := by
  ext ⟨a, b⟩ s
  cases s with
  | inl oy =>
    rcases oy with ⟨o, y⟩
    change
      (∑ oy' : O × (Y ⊕ Z),
          (P a oy'.1 * publicMixChannel t ht0 ht1 R S b oy'.2) *
            Dist.pure (prodSumDistribEquivRight O Y Z oy') (Sum.inl (o, y))) =
        t * (P a o * R b y)
    rw [Fintype.sum_eq_single (o, (Sum.inl y : Y ⊕ Z))]
    · simp [prodSumDistribEquivRight, publicMixChannel]
      ring
    · intro ⟨o', yz'⟩ hne
      by_cases hmap : prodSumDistribEquivRight O Y Z (o', yz') = Sum.inl (o, y)
      · have hsource : (o', yz') = (o, Sum.inl y) := by
          cases yz' with
          | inl y' =>
            simp only [prodSumDistribEquivRight_inl, Sum.inl.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨ho, hy⟩
            subst ho; subst hy; rfl
          | inr z =>
            simp [prodSumDistribEquivRight_inr] at hmap
        exact (hne hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquivRight O Y Z (o', yz')) (Sum.inl (o, y)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]
  | inr oz =>
    rcases oz with ⟨o, z⟩
    change
      (∑ oy' : O × (Y ⊕ Z),
          (P a oy'.1 * publicMixChannel t ht0 ht1 R S b oy'.2) *
            Dist.pure (prodSumDistribEquivRight O Y Z oy') (Sum.inr (o, z))) =
        (1 - t) * (P a o * S b z)
    rw [Fintype.sum_eq_single (o, (Sum.inr z : Y ⊕ Z))]
    · simp [prodSumDistribEquivRight, publicMixChannel]
      ring
    · intro ⟨o', yz'⟩ hne
      by_cases hmap : prodSumDistribEquivRight O Y Z (o', yz') = Sum.inr (o, z)
      · have hsource : (o', yz') = (o, Sum.inr z) := by
          cases yz' with
          | inl y =>
            simp [prodSumDistribEquivRight_inl] at hmap
          | inr z' =>
            simp only [prodSumDistribEquivRight_inr, Sum.inr.injEq, Prod.mk.injEq] at hmap
            rcases hmap with ⟨ho, hz⟩
            subst ho; subst hz; rfl
        exact (hne hsource).elim
      · have hpure :
            Dist.pure (prodSumDistribEquivRight O Y Z (o', yz')) (Sum.inr (o, z)) = 0 := by
          apply Dist.pure_apply_ne
          intro htarget
          exact hmap htarget.symm
        rw [hpure, mul_zero]

/-- Right-side product/public-mix posterior-law theorem: mixing in the second
coordinate inside a product channel gives the same posterior law as the public
mixture of the two product channels. Mirror of
`samePosteriorLaw_prod_publicMix_left_of_postprocess`. -/
theorem samePosteriorLaw_prod_publicMix_right_of_postprocess
    {A B O Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B)
    (P : Channel A O)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel P (publicMixChannel t ht0 ht1 R S)))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S))) := by
  let PmixProd := prodChannel P (publicMixChannel t ht0 ht1 R S)
  have hsame :
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel PmixProd)
        (experimentOfChannel
          (Channel.postprocess PmixProd
            (posteriorLawEquivKernel (prodSumDistribEquivRight O Y Z)))) :=
    samePosteriorLawExp_of_bijective_postprocess
      (prodDist q r) PmixProd (prodSumDistribEquivRight O Y Z)
  have hchan :
      Channel.postprocess PmixProd
          (posteriorLawEquivKernel (prodSumDistribEquivRight O Y Z)) =
        publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S) :=
    prodChannel_publicMix_right_postprocess t ht0 ht1 P R S
  simpa [PmixProd, hchan] using hsame

/-- Right-slice public-mix affinity: for a fixed first-coordinate background,
the product value is public-mix affine in the second-coordinate channel.
Derived from the right-side posterior-law theorem plus posterior-value
public-mix affinity. -/
theorem product_right_slice_publicMix_affine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    productRightSliceValue hs q r P (publicMixChannel t ht0 ht1 R S) =
      t * productRightSliceValue hs q r P R +
        (1 - t) * productRightSliceValue hs q r P S := by
  have hsame :=
    samePosteriorLaw_prod_publicMix_right_of_postprocess q r P t ht0 ht1 R S
  have hVeq :=
    hs.branch_agg.value_rep.respects_same_posterior_law
      (prodDist q r)
      (experimentOfChannel (prodChannel P (publicMixChannel t ht0 ht1 R S)))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S)))
      hsame
  have hprod : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  calc
    productRightSliceValue hs q r P (publicMixChannel t ht0 ht1 R S)
        = hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel P S))) := by
          simpa [productRightSliceValue] using hVeq
    _ = t * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel P R)) +
          (1 - t) * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel P S)) := by
          exact
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
              F hax hs.branch_agg.value_rep
              (prodDist q r) hprod t ht0 ht1
              (prodChannel P R) (prodChannel P S)
    _ = t * productRightSliceValue hs q r P R +
          (1 - t) * productRightSliceValue hs q r P S := by
          rfl

/--
**Product Left-Slice Public-Mix Affinity**

Paper-specific product-affinity content for the first-coordinate slice:
`P ↦ V_{q⊗r}(P⊗R)` is affine under public mixtures of the first-coordinate
experiment. In the paper this follows because `L_{q,r}` is separately affine.
Stage 10I derives this from channel-level value public-mix affinity plus the
narrow posterior-law compatibility between `prodChannel (publicMix P Q) R` and
the public mixture of `prodChannel P R` and `prodChannel Q R`. Stage 10K
derives the channel-level value public-mix affinity from law-level posterior
value affinity and the structural public-mix posterior-law mixture theorem.
-/
structure FiniteProductLeftSlicePublicMixAffineAssumptions.{v} where
  product_left_slice_publicMix_affine :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B O Z Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Z] [DecidableEq Z]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (P : Channel A O) (Q : Channel A Z),
      productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q) =
        t * productLeftSliceValue hs q r R P +
          (1 - t) * productLeftSliceValue hs q r R Q

theorem product_left_slice_publicMix_affine_of_posterior_affinity
    (hVaff : FinitePosteriorValueAffineAssumptions.{u})
    (hmixlaw : FiniteProductPublicMixPosteriorLawAssumptions.{u}) :
    FiniteProductLeftSlicePublicMixAffineAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hs A B O Z Y _ _ _ _ _ _ _ _ _ _ _ _ q r hq hr R t ht0 ht1 P Q
  have hsame :
      SamePosteriorLawExp (prodDist q r)
        (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) :=
    hmixlaw.samePosteriorLaw_prod_publicMix_left q r R t ht0 ht1 P Q
  have hVeq :=
    hs.branch_agg.value_rep.respects_same_posterior_law
      (prodDist q r)
      (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
      (experimentOfChannel
        (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R)))
      hsame
  have hprod : (prodDist q r).FullSupport :=
    prodDist_fullSupport q r hq hr
  calc
    productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q)
        = hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel
              (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) := by
          simpa [productLeftSliceValue] using hVeq
    _ = t * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel P R)) +
          (1 - t) * hs.branch_agg.value_rep.V (prodDist q r)
            (experimentOfChannel (prodChannel Q R)) := by
          exact
            hVaff.V_publicMix_affine F hax hs.branch_agg.value_rep
              (prodDist q r) hprod t ht0 ht1
              (prodChannel P R) (prodChannel Q R)
    _ = t * productLeftSliceValue hs q r R P +
          (1 - t) * productLeftSliceValue hs q r R Q := by
          rfl

/-- Face-scale base-value public-mixture affinity follows from the global
posterior-law value-affinity package. -/
theorem faceScaleBaseValuePublicMixAffinity_of_posteriorLawValueAffine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces where
  base_value_publicMix_affine := by
    intro hax A O Z _ _ _ _ _ _ _ q hq t ht0 ht1 P Q
    exact
      (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
        F hax hfaces.branch_result.branch_agg.value_rep
        q hq t ht0 ht1 P Q

/-- Face-scale first-coordinate product-slice public-mixture affinity follows
from posterior-law value affinity plus the structural product/public-mix
posterior-law transport. -/
theorem faceScaleProductCoordinateMixtureAffinity_of_posteriorLawValueAffine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces where
  left_slice_publicMix_affine := by
    intro hax A B O Z Y _ _ _ _ _ _ _ _ _ _ _ _ q r hq hr R t ht0 ht1 P Q
    have hsame :
        SamePosteriorLawExp (prodDist q r)
          (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
          (experimentOfChannel
            (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) :=
      samePosteriorLaw_prod_publicMix_left_of_postprocess q r R t ht0 ht1 P Q
    have hVeq :=
      hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
        (prodDist q r)
        (experimentOfChannel (prodChannel (publicMixChannel t ht0 ht1 P Q) R))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R)))
        hsame
    have hprod : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    calc
      faceScaleProductLeftSliceValue hfaces q r R
          (publicMixChannel t ht0 ht1 P Q)
          = hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (publicMixChannel t ht0 ht1 (prodChannel P R) (prodChannel Q R))) := by
            simpa [faceScaleProductLeftSliceValue] using hVeq
      _ = t * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel (prodChannel P R)) +
            (1 - t) * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel (prodChannel Q R)) := by
            exact
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
                F hax hfaces.branch_result.branch_agg.value_rep
                (prodDist q r) hprod t ht0 ht1
                (prodChannel P R) (prodChannel Q R)
      _ = t * faceScaleProductLeftSliceValue hfaces q r R P +
            (1 - t) * faceScaleProductLeftSliceValue hfaces q r R Q := by
            rfl

/-- Face-scale intercept public-mixture affinity follows from posterior-law
value affinity and product/public-mix posterior-law transport in the second
coordinate. -/
theorem faceScaleProductInterceptPublicMixAffinity_of_posteriorLawValueAffine
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice where
  intercept_publicMix_affine := by
    intro hax A B Y Z _ _ _ _ _ _ _ _ _ _ q r hq hr t ht0 ht1 R S
    have hsame :
        SamePosteriorLawExp (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (publicMixChannel t ht0 ht1 R S)))
          (experimentOfChannel
            (publicMixChannel t ht0 ht1
              (prodChannel (Channel.uninformativeChannelU A) R)
              (prodChannel (Channel.uninformativeChannelU A) S))) :=
      samePosteriorLaw_prod_publicMix_right_of_postprocess
        q r (Channel.uninformativeChannelU A) t ht0 ht1 R S
    have hVeq :=
      hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
        (prodDist q r)
        (experimentOfChannel
          (prodChannel (Channel.uninformativeChannelU A)
            (publicMixChannel t ht0 ht1 R S)))
        (experimentOfChannel
          (publicMixChannel t ht0 ht1
            (prodChannel (Channel.uninformativeChannelU A) R)
            (prodChannel (Channel.uninformativeChannelU A) S)))
        hsame
    have hprod : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr (publicMixChannel t ht0 ht1 R S)]
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr R]
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr S]
    calc
      faceScaleProductLeftSliceValue hfaces q r
          (publicMixChannel t ht0 ht1 R S)
          (Channel.uninformativeChannelU A)
          = hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (publicMixChannel t ht0 ht1
                  (prodChannel (Channel.uninformativeChannelU A) R)
                  (prodChannel (Channel.uninformativeChannelU A) S))) := by
            simpa [faceScaleProductLeftSliceValue] using hVeq
      _ = t * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (prodChannel (Channel.uninformativeChannelU A) R)) +
            (1 - t) * hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
              (experimentOfChannel
                (prodChannel (Channel.uninformativeChannelU A) S)) := by
            exact
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw hVaff).V_publicMix_affine
                F hax hfaces.branch_result.branch_agg.value_rep
                (prodDist q r) hprod t ht0 ht1
                (prodChannel (Channel.uninformativeChannelU A) R)
                (prodChannel (Channel.uninformativeChannelU A) S)
      _ = t * faceScaleProductLeftSliceValue hfaces q r R
              (Channel.uninformativeChannelU A) +
            (1 - t) * faceScaleProductLeftSliceValue hfaces q r S
              (Channel.uninformativeChannelU A) := by
            rfl

/-- HM-specialized wrapper for the face-scale base public-mix field. -/
theorem faceScaleBaseValuePublicMixAffinity_of_HM
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor hfaces :=
  faceScaleBaseValuePublicMixAffinity_of_posteriorLawValueAffine
    (finitePosteriorLawValueAffine_of_HM hhm) hfaces

/-- HM-specialized wrapper for the face-scale product-coordinate public-mix
field. -/
theorem faceScaleProductCoordinateMixtureAffinity_of_HM
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor hfaces :=
  faceScaleProductCoordinateMixtureAffinity_of_posteriorLawValueAffine
    (finitePosteriorLawValueAffine_of_HM hhm) hfaces

/-- HM-specialized wrapper for the face-scale intercept public-mix field. -/
theorem faceScaleProductInterceptPublicMixAffinity_of_HM
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor hslice :=
  faceScaleProductInterceptPublicMixAffinity_of_posteriorLawValueAffine
    (finitePosteriorLawValueAffine_of_HM hhm) hslice

/-- Face-scale version of the A8 product-coordinate order independence
theorem for first-coordinate product experiments.  Unlike the older
`product_left_coordinate_value_order_independent`, this is stated before
universal scale coherence and uses only the value representative already
contained in `CoherentRelabelingFaceScalesStructure`. -/
theorem faceScaleProduct_left_coordinate_value_order_independent
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : TraceAxioms F)
    {A B O O₂R O₂S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype O₂R] [DecidableEq O₂R]
    [Fintype O₂S] [DecidableEq O₂S]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) (R : Channel B O₂R) (S : Channel B O₂S) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q R)) ↔
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P S)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q S)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel Q R))
  have hS :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel P S))
      (experimentOfChannel (prodChannel Q S))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel P R) (prodChannel Q R))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q R)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel P S) (prodChannel Q S))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P S)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q S)) at hS'
  exact hR'.symm.trans ((hax.a8.1 q r hq hr P Q R S).trans hS')

/-- Face-scale product left-slice with no-information background recovers the
base first-coordinate order. -/
theorem faceScaleProduct_left_noInfo_value_order_iff_base
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : TraceAxioms F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P Q : Channel A O) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) Q)) ↔
    hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Q) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
  have hprod_rel :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) := by
    change
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) Q)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (leftProductLiftChannel (B := B) P)
          (leftProductLiftChannel (B := B) Q))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftProductLiftChannel (B := B) P) (leftUnitOutcomeChannel P)
      (leftProductLiftChannel (B := B) Q) (leftUnitOutcomeChannel Q)
      (prodDist q r) q (prodDist q r) q
      (leftProductLift_rel_leftUnitOutcome F hax P q r)
      (leftUnitOutcome_rel_leftProductLift F hax P q r)
      (leftProductLift_rel_leftUnitOutcome F hax Q q r)
      (leftUnitOutcome_rel_leftProductLift F hax Q q r)
  have hunit_to_base :
      F.rel (blockChannel (leftUnitOutcomeChannel P) (leftUnitOutcomeChannel Q))
        (inlDist q) (inrDist q) ↔
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (leftUnitOutcomeChannel P) P
      (leftUnitOutcomeChannel Q) Q
      q q q q
      (leftUnitOutcome_rel_original F hax P q)
      (original_rel_leftUnitOutcome F hax P q)
      (leftUnitOutcome_rel_original F hax Q q)
      (original_rel_leftUnitOutcome F hax Q q)
  have hbase_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      q hq (experimentOfChannel P) (experimentOfChannel Q)
  have hbase_rel :
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Q) := by
    change
      F.rel (blockChannel P Q) (inlDist q) (inrDist q) ↔
      hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hfaces.branch_result.branch_agg.value_rep.V q (experimentOfChannel Q) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- A8 gives the face-scale first-coordinate slice order before universal
scale coherence. -/
theorem faceScaleProductLeftSliceSameOrder_of_A8
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor hfaces where
  left_slice_same_order := by
    intro hax A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr R P Q
    have hbackground :=
      faceScaleProduct_left_coordinate_value_order_independent
        hfaces hax q r hq hr P Q R (Channel.uninformativeChannelU B)
    have hbase :=
      faceScaleProduct_left_noInfo_value_order_iff_base
        hfaces hax q r hq hr P Q
    simpa [faceScaleProductLeftSliceValue, leftProductLiftChannel] using
      hbackground.trans hbase

/-- Face-scale product right-slice value in the pre-universal structure. -/
noncomputable def faceScaleProductRightSliceValue
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O)
    (R : Channel B Y) : ℝ :=
  hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
    (experimentOfChannel (prodChannel P R))

/-- Face-scale A8 product-coordinate order independence for second-coordinate
product experiments. -/
theorem faceScaleProduct_right_coordinate_value_order_independent
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : TraceAxioms F)
    {A B O₁R O₁S O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O₁R] [DecidableEq O₁R]
    [Fintype O₁S] [DecidableEq O₁S]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel A O₁R) (S : Channel A O₁S) (P Q : Channel B O) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R P)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel R Q)) ↔
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S P)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel S Q)) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hR :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel R P))
      (experimentOfChannel (prodChannel R Q))
  have hS :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (prodChannel S P))
      (experimentOfChannel (prodChannel S Q))
  have hR' := hR
  change
      F.rel (blockChannel (prodChannel R P) (prodChannel R Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel R Q)) at hR'
  have hS' := hS
  change
      F.rel (blockChannel (prodChannel S P) (prodChannel S Q))
          (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S P)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel S Q)) at hS'
  exact hR'.symm.trans ((hax.a8.2 q r hq hr R S P Q).trans hS')

/-- Face-scale product right-slice with no-information first-coordinate
background recovers the base second-coordinate order. -/
theorem faceScaleProduct_right_noInfo_value_order_iff_base
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R S : Channel B Y) :
    hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) S)) ↔
    hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) ≥
      hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel S) := by
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hprod_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      (prodDist q r) hprod
      (experimentOfChannel (rightProductLiftChannel (A := A) R))
      (experimentOfChannel (rightProductLiftChannel (A := A) S))
  have hprod_rel :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) := by
    change
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) R)) ≥
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) S)) at hprod_rep
    exact hprod_rep
  have hproduct_to_unit :
      F.rel (blockChannel (rightProductLiftChannel (A := A) R)
          (rightProductLiftChannel (A := A) S))
        (inlDist (prodDist q r)) (inrDist (prodDist q r)) ↔
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightProductLiftChannel (A := A) R) (rightUnitOutcomeChannel R)
      (rightProductLiftChannel (A := A) S) (rightUnitOutcomeChannel S)
      (prodDist q r) r (prodDist q r) r
      (rightProductLift_rel_rightUnitOutcome F hax R q r)
      (rightUnitOutcome_rel_rightProductLift F hax R q r)
      (rightProductLift_rel_rightUnitOutcome F hax S q r)
      (rightUnitOutcome_rel_rightProductLift F hax S q r)
  have hunit_to_base :
      F.rel (blockChannel (rightUnitOutcomeChannel R) (rightUnitOutcomeChannel S))
        (inlDist r) (inrDist r) ↔
      F.rel (blockChannel R S) (inlDist r) (inrDist r) :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      (rightUnitOutcomeChannel R) R
      (rightUnitOutcomeChannel S) S
      r r r r
      (rightUnitOutcome_rel_original F hax R r)
      (original_rel_rightUnitOutcome F hax R r)
      (rightUnitOutcome_rel_original F hax S r)
      (original_rel_rightUnitOutcome F hax S r)
  have hbase_rep :=
    hfaces.branch_result.branch_agg.value_rep.represents_block_comparisons
      r hr (experimentOfChannel R) (experimentOfChannel S)
  have hbase_rel :
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel S) := by
    change
      F.rel (blockChannel R S) (inlDist r) (inrDist r) ↔
      hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hfaces.branch_result.branch_agg.value_rep.V r (experimentOfChannel S) at hbase_rep
    exact hbase_rep
  exact hprod_rel.symm.trans (hproduct_to_unit.trans (hunit_to_base.trans hbase_rel))

/-- A8 gives the face-scale second-coordinate slice order before universal
scale coherence. -/
theorem faceScaleProductRightSliceSameOrder_of_A8
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : TraceAxioms F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R S : Channel B Y) :
    faceScaleProductRightSliceValue hfaces q r P R ≥
        faceScaleProductRightSliceValue hfaces q r P S ↔
      hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel R) ≥
        hfaces.branch_result.branch_agg.value_rep.V r
          (experimentOfChannel S) := by
  have hbackground :=
    faceScaleProduct_right_coordinate_value_order_independent
      hfaces hax q r hq hr (Channel.uninformativeChannelU A) P R S
  have hbase :=
    faceScaleProduct_right_noInfo_value_order_iff_base
      hfaces hax q r hq hr R S
  simpa [faceScaleProductRightSliceValue, rightProductLiftChannel] using
    hbackground.symm.trans hbase

/-- Face-scale intercept same-order reconstructed from A8 right-slice order
and the internal intercept/no-information identity. -/
theorem faceScaleProductInterceptSameOrder_of_A8
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces) :
    FiniteFaceScaleProductInterceptSameOrderAssumptionsFor hslice where
  intercept_same_order := by
    intro hax A B Y _ _ _ _ _ _ _ _ q r hq hr R S
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr R]
    rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
      hslice hax q r hq hr S]
    simpa [faceScaleProductRightSliceValue, faceScaleProductLeftSliceValue]
      using
        faceScaleProductRightSliceSameOrder_of_A8
          hfaces hax q r hq hr (Channel.uninformativeChannelU A) R S

/-- Post-HM product representation reassembler.

HM supplies all public-mixture fields, and A8 supplies the product-coordinate
same-order fields.  The remaining inputs are exactly the non-HM product
representation pieces: second-coordinate affine uniqueness, slope affine
identification, and triple-product coefficient extraction. -/
theorem finiteFaceScaleProductRepresentationTheorem_of_HM
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hsecond :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
              hsingle huniq)))
    (hslope :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        FiniteFaceScaleProductSlopeAffineAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
              hsingle huniq)))
    (hextract :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
        (hgauge :
          FiniteFaceScaleCurrentProductGaugeNormalizationFor
            (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
              hsingle huniq
              (faceScaleProductInterceptSameOrder_of_A8
                (faceScaleProductLeftSliceAffine_of_transform
                  (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                    (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                    (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                    (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
                    hsingle huniq)))
              (faceScaleProductInterceptPublicMixAffinity_of_HM hhm
                (faceScaleProductLeftSliceAffine_of_transform
                  (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                    (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                    (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                    (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
                    hsingle huniq)))
              (hsecond hsingle huniq)
              (hslope hsingle huniq)))
        (hrelV : FinitePosteriorValueRelabelingAssumptions.{u}),
        FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor
          (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
            (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
            (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
            (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
            hsingle huniq
            (faceScaleProductInterceptSameOrder_of_A8
              (faceScaleProductLeftSliceAffine_of_transform
                (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                  (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                  (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                  (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
                  hsingle huniq)))
            (faceScaleProductInterceptPublicMixAffinity_of_HM hhm
              (faceScaleProductLeftSliceAffine_of_transform
                (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                  (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                  (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                  (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
                  hsingle huniq)))
            (hsecond hsingle huniq)
            (hslope hsingle huniq))
          (faceScaleProductGaugeNormalization_of_currentGauge hgauge)
          (faceScaleTripleProductValueAssociativity_of_valueRelabeling
            hfaces hrelV)) :
    FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces where
  base_publicMix := faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces
  coordinate_publicMix :=
    faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces
  left_slice_same_order := faceScaleProductLeftSliceSameOrder_of_A8 hfaces
  intercept_same_order := by
    intro hsingle huniq
    exact faceScaleProductInterceptSameOrder_of_A8
      (faceScaleProductLeftSliceAffine_of_transform
        (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
          (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
          (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
          (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
          hsingle huniq))
  intercept_publicMix := by
    intro hsingle huniq
    exact faceScaleProductInterceptPublicMixAffinity_of_HM hhm
      (faceScaleProductLeftSliceAffine_of_transform
        (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
          (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
          (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
          (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
          hsingle huniq))
  second_coordinate_uniqueness := hsecond
  slope_affine := hslope
  triple_coeff_extraction := hextract

/-- Post-HM product representation reassembler with triple-product coefficient
extraction discharged internally.

The remaining product-representation inputs are the genuinely coherent
second-coordinate/slope identifications.  Public mixtures come from HM,
same-order comes from A8, and triple coefficient extraction is now pure
face-scale algebra from product value associativity. -/
theorem finiteFaceScaleProductRepresentationTheorem_of_HM_and_coeffExtraction
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hsecond :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
              hsingle huniq)))
    (hslope :
      ∀ (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
        (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}),
        FiniteFaceScaleProductSlopeAffineAssumptionsFor
          (faceScaleProductLeftSliceAffine_of_transform
            (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
              (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
              (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
              (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
              hsingle huniq))) :
    FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces :=
  finiteFaceScaleProductRepresentationTheorem_of_HM hhm hfaces hsecond hslope
    (by
      intro hsingle huniq hgauge hrelV
      exact
        faceScaleTripleProductCoeffExtraction_of_valueAssociativity)

/-!
## Singleton Posterior-Law Collapse

When the action set A is a singleton, every distribution on A is the same
(the unique point mass), hence every experiment induces the same posterior law.
This is a purely structural / domain-collapse fact requiring no behavioral axiom.

Paper: Step 5 of Lemma coherentnorm (line 1663–1676 of empowerment_v5(1).tex):
"Let q_* = δ_* be the prior on a singleton. Its zero-normalised representative
is identically zero."
-/

/-- On a singleton type, any two distributions are equal. -/
theorem Dist.eq_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Subsingleton A]
    (q q' : Dist A) : q = q' := by
  ext a
  have huniq : ∀ b : A, b = a := fun b => Subsingleton.elim b a
  have hq : q a = ∑ b : A, q b :=
    (Finset.sum_eq_single a (fun b _ hba => absurd (huniq b) hba)
      (fun h => absurd (Finset.mem_univ a) h)).symm
  have hq' : q' a = ∑ b : A, q' b :=
    (Finset.sum_eq_single a (fun b _ hba => absurd (huniq b) hba)
      (fun h => absurd (Finset.mem_univ a) h)).symm
  linarith [q.sum_eq_one, q'.sum_eq_one]

/-- On a singleton type, the posterior of any experiment at any outcome equals q. -/
theorem posterior_eq_prior_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E : FiniteExperimentOn A) (o : E.OutcomeType) :
    @FiniteExperimentOn.posterior A _ _ _ E q o = q :=
  Dist.eq_of_subsingleton _ _

/-- On a singleton type, posteriorLawIntegralExp evaluates to φ(q) for any
experiment, because all posteriors collapse to q. -/
theorem posteriorLawIntegralExp_singleton
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E : FiniteExperimentOn A) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q E φ = φ q := by
  unfold posteriorLawIntegralExp
  have hpost : ∀ o : E.OutcomeType,
      @FiniteExperimentOn.posterior A _ _ _ E q o = q :=
    posterior_eq_prior_of_subsingleton q E
  simp_rw [hpost]
  letI := E.outFintype
  have hmarg_sum : (∑ o : E.OutcomeType, (E.outcomeMarginal q) o) = 1 :=
    (E.outcomeMarginal q).sum_eq_one
  rw [← Finset.sum_mul, hmarg_sum, one_mul]

/-- On a singleton action set, all experiments induce the same posterior law. -/
theorem samePosteriorLawExp_of_subsingleton
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    SamePosteriorLawExp q E E' := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_singleton q E φ, posteriorLawIntegralExp_singleton q E' φ]

/-- On a singleton action set, V q E = 0 for any experiment E. -/
theorem V_eq_zero_of_subsingleton
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A) :
    hV.V q E = 0 := by
  have heq : hV.V q E =
      hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) :=
    hV.respects_same_posterior_law q E
      (experimentOfChannel (Channel.uninformativeChannelU A))
      (samePosteriorLawExp_of_subsingleton q E _)
  rw [heq, hV.zero_normalized q hq]

/-- On a singleton action set, V q (experimentOfChannel P) = 0 for any channel P. -/
theorem V_channel_eq_zero_of_subsingleton
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    hV.V q (experimentOfChannel P) = 0 :=
  V_eq_zero_of_subsingleton F hV q hq (experimentOfChannel P)

/-- On a singleton first-coordinate, the product-left-slice value is constant
in P. This uses A8 (background separability) with same-type channels. -/
theorem productLeftSliceValue_singleton_const_sameType
    {F : PrefFamily.{u}} (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y)
    (P Q : Channel A O) :
    productLeftSliceValue hs q r R P =
      productLeftSliceValue hs q r R Q := by
  unfold productLeftSliceValue
  have hprod : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hVP : hs.branch_agg.value_rep.V q (experimentOfChannel P) = 0 :=
    V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P
  have hVQ : hs.branch_agg.value_rep.V q (experimentOfChannel Q) = 0 :=
    V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq Q
  have hlift_eq : hs.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (leftProductLiftChannel (B := B) P)) =
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) Q)) := by
    have hord_fwd := (product_left_noInfo_value_order_iff_base F hax hs q r hq hr P Q).mpr
    have hord_bwd := (product_left_noInfo_value_order_iff_base F hax hs q r hq hr Q P).mpr
    linarith [hord_fwd (by linarith : hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel Q)),
      hord_bwd (by linarith : hs.branch_agg.value_rep.V q (experimentOfChannel Q) ≥
        hs.branch_agg.value_rep.V q (experimentOfChannel P))]
  have hrepr_fwd := hs.branch_agg.value_rep.represents_block_comparisons
    (prodDist q r) hprod
    (experimentOfChannel (prodChannel P R))
    (experimentOfChannel (prodChannel Q R))
  have hrepr_bwd := hs.branch_agg.value_rep.represents_block_comparisons
    (prodDist q r) hprod
    (experimentOfChannel (prodChannel Q R))
    (experimentOfChannel (prodChannel P R))
  have hA8_fwd := (hax.a8.1 q r hq hr P Q R (Channel.uninformativeChannelU B)).mpr
  have hA8_bwd := (hax.a8.1 q r hq hr Q P R (Channel.uninformativeChannelU B)).mpr
  have hlift_pref : ExperimentPairPref F
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
      (prodDist q r) (prodDist q r) := by
    rw [hs.branch_agg.value_rep.represents_block_comparisons (prodDist q r) hprod]
    linarith [hlift_eq]
  have hlift_pref' : ExperimentPairPref F
      (experimentOfChannel (leftProductLiftChannel (B := B) Q))
      (experimentOfChannel (leftProductLiftChannel (B := B) P))
      (prodDist q r) (prodDist q r) := by
    rw [hs.branch_agg.value_rep.represents_block_comparisons (prodDist q r) hprod]
    linarith [hlift_eq]
  have hge_fwd : hs.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (prodChannel P R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel Q R)) := by
    rw [← hrepr_fwd]
    exact hA8_fwd hlift_pref
  have hge_bwd : hs.branch_agg.value_rep.V (prodDist q r)
      (experimentOfChannel (prodChannel Q R)) ≥
      hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) := by
    rw [← hrepr_bwd]
    exact hA8_bwd hlift_pref'
  linarith

/-- On a singleton first-coordinate, any experiment `prodChannel P R` has the same
posterior law at `prodDist q r` as `prodChannel (uninformativeChannelU A) R`,
because the posterior only depends on the R-outcome (not on P or its outcome). -/
theorem samePosteriorLawExp_prodChannel_singleton_fst
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (P : Channel A O) (R : Channel B Y) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R)) := by
  obtain ⟨a₀⟩ : Nonempty A := inferInstance
  have huniq : ∀ a : A, a = a₀ := fun a => Subsingleton.elim a a₀
  have hq_eq : q a₀ = 1 := by
    have hsum := q.sum_eq_one
    rw [show (∑ a : A, q a) = q a₀ from
      Finset.sum_eq_single a₀ (fun b _ hb => absurd (huniq b) hb)
        (fun h => absurd (Finset.mem_univ a₀) h)] at hsum
    exact hsum
  have hU_val : ∀ (u : PUnit.{u+1}),
      (Channel.uninformativeChannelU A a₀ : Dist PUnit.{u+1}) u = 1 := by
    intro u; cases u; simp [Channel.uninformativeChannelU]
  have hP_sum : (∑ o : O, (P a₀).prob o) = 1 := (P a₀).sum_eq_one
  intro φ _hcont
  show posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel P R)) φ =
    posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R)) φ
  simp only [posteriorLawIntegralExp, experimentOfChannel, FiniteExperimentOn.ofChannel,
    FiniteExperimentOn.outcomeMarginal, FiniteExperimentOn.posterior]
  -- Both sides are sums of marginal * φ(posterior). Key: marginal(o,y) = P(a₀)(o) * mR(y).
  -- When P(a₀)(o) = 0, the term is 0. When P(a₀)(o) > 0, the posteriors agree.
  -- So the integral factors as (Σ_o P(a₀)(o)) * Σ_y mR(y) * φ(postR(y)) = RHS.
  have hmarg_factored : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
      (P a₀).prob o * Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) (PUnit.unit, y) := by
    intro o y
    simp only [Channel.outcomeMarginal_apply]
    have hstep_P : ∀ x : A × B, (prodDist q r) x * (prodChannel P R) x (o, y) =
        (P a₀).prob o * (r x.2 * R x.2 y) := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq a, hq_eq, one_mul]; ring
    have hstep_U : ∀ x : A × B, (prodDist q r) x *
        (prodChannel (Channel.uninformativeChannelU A) R) x (PUnit.unit, y) =
        r x.2 * R x.2 y := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq a, hq_eq, one_mul,
        hU_val, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => hstep_P x), ← Finset.mul_sum,
      Finset.sum_congr rfl (fun x _ => hstep_U x)]
  -- Key: when P(a₀)(o) > 0 and marginal_U > 0, posteriors are equal
  have hpost_when_pos : ∀ (o : O) (y : Y),
      (P a₀).prob o > 0 →
      Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) (PUnit.unit, y) > 0 →
      Channel.posterior (prodChannel P R) (prodDist q r) (o, y) =
        Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) := by
    intro o y hPo hUy
    have hmarg_P_pos : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) > 0 := by
      rw [hmarg_factored o y]; exact mul_pos hPo hUy
    unfold Channel.posterior
    rw [dif_pos hmarg_P_pos, dif_pos hUy]
    ext ⟨a, b⟩
    simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq a, hq_eq, one_mul,
      hU_val, mul_one]
    rw [show Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
        (P a₀).prob o * Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) from hmarg_factored o y]
    have hPo_ne : (P a₀).prob o ≠ 0 := ne_of_gt hPo
    have hUy_ne : (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) : Dist (PUnit.{u+1} × Y)).prob (PUnit.unit, y) ≠ 0 := ne_of_gt hUy
    field_simp
  -- Now prove the integral equality by factoring
  suffices h : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
      (P a₀).prob o *
        (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y))) by
    have hlhs : (∑ o : O × Y,
        Channel.outcomeMarginal (prodChannel P R) (prodDist q r) o *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) o)) =
      ∑ y : Y, Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [h]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul, hP_sum, one_mul]
    have hrhs : (∑ o : PUnit.{u+1} × Y,
        Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) o *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) o)) =
      ∑ y : Y, Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) *
        φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y)) := by
      rw [Fintype.sum_prod_type]
      simp [Finset.univ_unique]
    exact hlhs.trans hrhs.symm
  intro o y
  rcases eq_or_lt_of_le ((P a₀).nonneg o) with hPo | hPo
  · -- P(a₀)(o) = 0: marginal is 0, whole product is 0
    have hmarg0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
      rw [hmarg_factored o y]; simp [hPo.symm]
    simp only [Channel.outcomeMarginal_apply] at hmarg0
    simp [hmarg0, hPo.symm]
  · -- P(a₀)(o) > 0: need marginal_U positivity
    have hUy_nn : (0 : ℝ) ≤ Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r) (PUnit.unit, y) :=
      (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
        (prodDist q r)).nonneg (PUnit.unit, y)
    rcases eq_or_lt_of_le hUy_nn with hUy | hUy
    · -- marginal_U = 0: both sides are 0
      have hmU0 : Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
          (prodDist q r) (PUnit.unit, y) = 0 := hUy.symm
      have hmP0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
        rw [hmarg_factored o y, hmU0, mul_zero]
      change Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
          φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
        (P a₀).prob o *
          (Channel.outcomeMarginal (prodChannel (Channel.uninformativeChannelU A) R)
            (prodDist q r) (PUnit.unit, y) *
          φ (Channel.posterior (prodChannel (Channel.uninformativeChannelU A) R)
            (prodDist q r) (PUnit.unit, y)))
      rw [hmP0, hmU0]; ring
    · -- Both positive: posteriors agree
      rw [hmarg_factored o y, hpost_when_pos o y hPo hUy, mul_assoc]

/-- On a singleton first-coordinate, productLeftSliceValue is constant across
all outcome types. -/
theorem productLeftSliceValue_singleton_const
    {F : PrefFamily.{u}} (_hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (R : Channel B Y)
    (P : Channel A O) :
    productLeftSliceValue hs q r R P =
      productLeftSliceValue hs q r R (Channel.uninformativeChannelU A) := by
  unfold productLeftSliceValue
  exact hs.branch_agg.value_rep.respects_same_posterior_law (prodDist q r) _ _
    (samePosteriorLawExp_prodChannel_singleton_fst q r P R)

/--
**Singleton Product Slice Affinity**

The paper handles singleton factors separately after the nondegenerate
coherent-product argument. The affine-uniqueness theorem needs a nonconstant
base representative, so singleton first-coordinate action sets are isolated
instead of hidden in the classical uniqueness statement.

NOTE: This assumption is now proved internally via
`singletonSliceAffine_of_singletonCollapse` and is retained only for
backwards-compatibility of the structure definition until the cross-prior
bundle is updated.
-/
structure FiniteSingletonSliceAffineAssumptions.{v} where
  singleton_left_slice_positive_affine_transform :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          productLeftSliceValue hs q r R P =
            a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b

/-- The singleton slice affine assumption is provable internally:
take a = 1, b = productLeftSliceValue for the canonical uninformative channel.
Since V q (experimentOfChannel P) = 0 on singletons and the product-left-slice
value is constant in P (by A8 + value zero), the identity holds trivially.

Paper: Step 5 of Lemma coherentnorm (line 1663–1676 of empowerment_v5(1).tex). -/
private theorem singletonSliceAffine_proof
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    ∃ a b : ℝ, 0 < a ∧
      ∀ {O : Type u} [Fintype O] [DecidableEq O]
        (P : Channel A O),
        productLeftSliceValue hs q r R P =
          a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b := by
  refine ⟨1, productLeftSliceValue hs q r R (Channel.uninformativeChannelU _), one_pos, ?_⟩
  intro O _ _ P
  have hVzero : hs.branch_agg.value_rep.V q (experimentOfChannel P) = 0 :=
    V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P
  have hconst : productLeftSliceValue hs q r R P =
      productLeftSliceValue hs q r R (Channel.uninformativeChannelU _) :=
    productLeftSliceValue_singleton_const hax hs q r hq hr R P
  linarith

theorem singletonSliceAffine_of_singletonCollapse :
    FiniteSingletonSliceAffineAssumptions.{u} :=
  ⟨singletonSliceAffine_proof⟩

/--
**Base Value Nonconstancy**

Value consequence of local nontriviality: at full-support non-singleton priors,
full revelation and no information have different posterior values. Stage 10L
reduced this to strict experiment-pair preference, and Stage 10M derives that
strictness from A1 plus structural Unit/PUnit relabeling and block-swap
plumbing. This compatibility structure is no longer a live external field.
-/
structure FiniteValueNonconstancyAssumptions.{v} where
  base_value_nonconstant :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hnot_subsingleton : ¬ Subsingleton A),
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))

/-- Strict experiment-pair preference at a full-support prior forces the value
representative to assign different values. -/
theorem value_ne_of_strict_experiment_pref
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (E₁ E₂ : FiniteExperimentOn A)
    (hpref : ExperimentPairPref F E₁ E₂ q q)
    (hnrev : ¬ ExperimentPairPref F E₂ E₁ q q) :
    hV.V q E₁ ≠ hV.V q E₂ := by
  intro heq
  have hge₂₁ : hV.V q E₂ ≥ hV.V q E₁ := by
    simp [heq]
  have _hge₁₂ : hV.V q E₁ ≥ hV.V q E₂ :=
    (hV.represents_block_comparisons q hq E₁ E₂).mp hpref
  exact hnrev ((hV.represents_block_comparisons q hq E₂ E₁).mpr hge₂₁)

/-- Reversing deterministic bijective outcome postprocessing recovers the
original channel. -/
theorem postprocess_posteriorLawEquivKernel_symm_eq_original
    {A O Y : Type u} [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (e : O ≃ Y) (P : Channel A O) :
    Channel.postprocess
        (Channel.postprocess P (posteriorLawEquivKernel e))
        (posteriorLawEquivKernel e.symm) =
      P := by
  ext a o
  simp [postprocess_posteriorLawEquivKernel_apply]

/-- Outcome relabeling by a deterministic equivalence preserves the preference
relation. This local version uses only A4, A3, and A1 transitivity. -/
theorem rel_postprocess_posteriorLawEquivKernel_of_A4
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A O Y : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (e : O ≃ Y) (q r : Dist A) :
    F.rel P q r ↔
      F.rel (Channel.postprocess P (posteriorLawEquivKernel e)) q r := by
  let P' := Channel.postprocess P (posteriorLawEquivKernel e)
  have hq_to_new :
      F.rel (blockChannel P P') (inlDist q) (inrDist q) := by
    simpa [P'] using hax.a4 P (posteriorLawEquivKernel e) q
  have hq_to_old :
      F.rel (blockChannel P' P) (inlDist q) (inrDist q) := by
    have h := hax.a4 P' (posteriorLawEquivKernel e.symm) q
    simpa [P', postprocess_posteriorLawEquivKernel_symm_eq_original] using h
  have hr_to_new :
      F.rel (blockChannel P P') (inlDist r) (inrDist r) := by
    simpa [P'] using hax.a4 P (posteriorLawEquivKernel e) r
  have hr_to_old :
      F.rel (blockChannel P' P) (inlDist r) (inrDist r) := by
    have h := hax.a4 P' (posteriorLawEquivKernel e.symm) r
    simpa [P', postprocess_posteriorLawEquivKernel_symm_eq_original] using h
  have hblock :=
    pairwise_product_block_replacement_from_weak_equiv F hax
      P P' P P' q q r r
      hq_to_new hq_to_old hr_to_new hr_to_old
  exact (hax.a3.1 P q r).trans (hblock.trans (hax.a3.1 P' q r).symm)

/--
**A1 Experiment-Pair Strictness Bridge**

Narrow ordinal compatibility bridge isolated in Stage 10L and proved in
Stage 10M. A1 gives strictness for the ordinary
`Unit` no-information channel as a reverse-lottery failure in the same block
environment. The value representation needs strictness as an experiment-pair
comparison against `Channel.uninformativeChannelU`, whose reverse comparison is
encoded in the swapped two-block environment. The proof below uses the
upstream structural Unit/PUnit lift and block-swap/relabeling transfer; this is
not a cardinal value or product assumption.
-/
structure FiniteA1ExperimentPairStrictnessAssumptions.{v} where
  id_uninformativeU_strict :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hnot_subsingleton : ¬ Subsingleton A),
      ExperimentPairPref F
        (experimentOfChannel (Channel.idChannel : Channel A A))
        (experimentOfChannel (Channel.uninformativeChannelU A))
        q q
      ∧
      ¬ ExperimentPairPref F
        (experimentOfChannel (Channel.uninformativeChannelU A))
        (experimentOfChannel (Channel.idChannel : Channel A A))
        q q

/-- A1's ordinary Unit no-information strictness, after the structural
Unit/PUnit relabeling and block-swap transfers, gives exactly the
ExperimentPairPref strictness needed by the value nonconstancy witness. -/
theorem id_uninformativeU_experiment_strict_of_A1
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hnot_subsingleton : ¬ Subsingleton A) :
    ExperimentPairPref F
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      q q
    ∧
    ¬ ExperimentPairPref F
      (experimentOfChannel (Channel.uninformativeChannelU A))
      (experimentOfChannel (Channel.idChannel : Channel A A))
      q q := by
  classical
  haveI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hnot_subsingleton
  have hstrict :=
    Relabeling.lifted_uninformative_strict_of_A1 F hax q hq
  constructor
  · change
      F.rel
        (blockChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A))
        (inlDist q) (inrDist q)
    exact hstrict.1
  · intro hrev
    change
      F.rel
        (blockChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel A A))
        (inlDist q) (inrDist q) at hrev
    have hrev_same :
        F.rel
          (blockChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU A))
          (inrDist q) (inlDist q) := by
      exact
        (Relabeling.block_swap_rel_of_axioms F hax
          (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU A) q q).mpr hrev
    exact hstrict.2 hrev_same

/-- Package the A1-to-experiment strictness transfer as a derived structure. -/
theorem a1ExperimentPairStrictness_of_axioms :
    FiniteA1ExperimentPairStrictnessAssumptions.{u} where
  id_uninformativeU_strict := by
    intro F hax A _ _ _ q hq hnot_subsingleton
    exact id_uninformativeU_experiment_strict_of_A1 F hax q hq hnot_subsingleton

/-- Base value nonconstancy follows from A1 and the posterior value
representation. -/
theorem valueNonconstancy_of_A1_experiment_strictness
    (hstrictness : FiniteA1ExperimentPairStrictnessAssumptions.{u}) :
    FiniteValueNonconstancyAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hs A _ _ _ q hq hnot_subsingleton
  have hstrict :=
    hstrictness.id_uninformativeU_strict F hax q hq hnot_subsingleton
  exact
    value_ne_of_strict_experiment_pref F hs.branch_agg.value_rep q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      hstrict.1 hstrict.2

/--
**Classical Affine Utility Uniqueness**

Classical affine-geometry theorem specialized to the finite experiment channel
domain used here. If the base representative and product slice are affine under
public mixtures, the base representative is nonconstant, and the two
functionals represent the same weak order, then the product slice is a positive
affine transform of the base representative.
-/
structure ClassicalAffineUtilityUniquenessAssumptions.{v} where
  positive_affine_transform :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hnot_subsingleton : ¬ Subsingleton A)
      (R : Channel B Y),
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        hs.branch_agg.value_rep.V q
            (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
          t * hs.branch_agg.value_rep.V q (experimentOfChannel P) +
            (1 - t) * hs.branch_agg.value_rep.V q (experimentOfChannel Q)) →
      (∀ {O Z : Type v} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q) =
          t * productLeftSliceValue hs q r R P +
            (1 - t) * productLeftSliceValue hs q r R Q) →
      (hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A))) →
      (∀ {O : Type v} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        productLeftSliceValue hs q r R P ≥ productLeftSliceValue hs q r R Q ↔
          hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
            hs.branch_agg.value_rep.V q (experimentOfChannel Q)) →
      ∃ a b : ℝ, 0 < a ∧
        ∀ {O : Type v} [Fintype O] [DecidableEq O]
          (P : Channel A O),
          productLeftSliceValue hs q r R P =
            a * hs.branch_agg.value_rep.V q (experimentOfChannel P) + b

/-- Assemble the Stage 10G affine-slice uniqueness package from the sharper
affinity, nonconstancy/singleton, and classical affine-utility uniqueness
components. -/
theorem affineSliceUniqueness_of_parts
    (hVaff : FinitePosteriorValueAffineAssumptions.{u})
    (hsliceAff : FiniteProductLeftSlicePublicMixAffineAssumptions.{u})
    (hnonconst : FiniteValueNonconstancyAssumptions.{u})
    (hsingle : FiniteSingletonSliceAffineAssumptions.{u})
    (huniq : ClassicalAffineUtilityUniquenessAssumptions.{u}) :
    FiniteAffineSliceUniquenessAssumptions.{u} := by
  refine ⟨?_⟩
  intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
  classical
  by_cases hsub : Subsingleton A
  · letI : Subsingleton A := hsub
    exact
      hsingle.singleton_left_slice_positive_affine_transform
        F hax hs q r hq hr R
  · have hbase_aff :
      ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        hs.branch_agg.value_rep.V q
            (experimentOfChannel (publicMixChannel t ht0 ht1 P Q)) =
          t * hs.branch_agg.value_rep.V q (experimentOfChannel P) +
            (1 - t) * hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
      intro O Z _ _ _ _ t ht0 ht1 P Q
      exact
        hVaff.V_publicMix_affine F hax hs.branch_agg.value_rep
          q hq t ht0 ht1 P Q
    have hslice_aff :
      ∀ {O Z : Type u} [Fintype O] [DecidableEq O]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (P : Channel A O) (Q : Channel A Z),
        productLeftSliceValue hs q r R (publicMixChannel t ht0 ht1 P Q) =
          t * productLeftSliceValue hs q r R P +
            (1 - t) * productLeftSliceValue hs q r R Q := by
      intro O Z _ _ _ _ t ht0 ht1 P Q
      exact
        hsliceAff.product_left_slice_publicMix_affine
          F hax hs q r hq hr R t ht0 ht1 P Q
    have hnonconstant :=
      hnonconst.base_value_nonconstant F hax hs q hq hsub
    have hsame_order :
      ∀ {O : Type u} [Fintype O] [DecidableEq O]
        (P Q : Channel A O),
        productLeftSliceValue hs q r R P ≥ productLeftSliceValue hs q r R Q ↔
          hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
            hs.branch_agg.value_rep.V q (experimentOfChannel Q) := by
      intro O _ _ P Q
      exact product_left_slice_same_order F hax hs q r hq hr P Q R
    exact
      huniq.positive_affine_transform
        F hax hs q r hq hr hsub R
        hbase_aff hslice_aff hnonconstant hsame_order

noncomputable def affineSliceUniquenessSlope
    (haff : FiniteAffineSliceUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (R : Channel B Y) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (haff.left_slice_positive_affine_transform F hax hs q r h.1 h.2 R)
    else 0

noncomputable def affineSliceUniquenessIntercept
    (haff : FiniteAffineSliceUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
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
          (haff.left_slice_positive_affine_transform F hax hs q r h.1 h.2 R))
    else 0

/-- Recover the previous Stage 10F compatibility package from the narrower
affine-slice uniqueness assumption. -/
noncomputable def productLeftSliceAffine_of_affineUniqueness
    (haff : FiniteAffineSliceUniquenessAssumptions.{u}) :
    FiniteProductLeftSliceAffineAssumptions.{u} where
  leftSliceSlope := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r R
    exact affineSliceUniquenessSlope haff F hax hs q r R
  leftSliceIntercept := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r R
    exact affineSliceUniquenessIntercept haff F hax hs q r R
  leftSliceSlope_pos := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hpos :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform F hax hs q r hq hr R))).1
    simpa [affineSliceUniquenessSlope, hq, hr] using hpos
  left_slice_affine := by
    intro F hax hs A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    classical
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (haff.left_slice_positive_affine_transform F hax hs q r hq hr R))).2
        (P := P)
    simpa [productLeftSliceValue, affineSliceUniquenessSlope,
      affineSliceUniquenessIntercept, hq, hr] using hspec

/-- The left-slice intercept equals the product-left-slice value at the
uninformative first-coordinate channel. This is immediate from the affine
identity `V(P⊗R) = α_R V_q(P) + γ_R` at P = U_A where V_q(U_A) = 0.

Paper: Step 2 of Lemma coherentnorm (line 1525): Taking μ = δ_p shows
γ(ν) = L_{p,r}(δ_p,ν). -/
theorem leftSliceIntercept_eq_noInfo_productLeftSliceValue
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hslice.leftSliceIntercept F hax hs q r R =
      productLeftSliceValue hs q r R (Channel.uninformativeChannelU A) := by
  have haffine := hslice.left_slice_affine F hax hs q r hq hr
    (Channel.uninformativeChannelU A) R
  have hVzero : hs.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hs.branch_agg.value_rep.zero_normalized q hq
  unfold productLeftSliceValue
  rw [hVzero, mul_zero, zero_add] at haffine
  exact haffine.symm

/-- The left-slice intercept at the uninformative second-coordinate background
R = U_B is zero. From the intercept = no-info identity, this equals
V_{q⊗r}(U_A ⊗ U_B) = 0 since PUnit × PUnit is subsingleton. -/
theorem leftSliceIntercept_uninformative_eq_zero
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hslice.leftSliceIntercept F hax hs q r
      (Channel.uninformativeChannelU B) = 0 := by
  rw [leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr]
  simp only [productLeftSliceValue]
  exact V_eq_zero_of_subsingleton_outcome F hs.branch_agg.value_rep
    (prodDist q r) (prodDist_fullSupport q r hq hr)
    (prodChannel (Channel.uninformativeChannelU A) (Channel.uninformativeChannelU B))

/-- The left-slice intercept function R ↦ γ_R represents the same weak order as
V_r. That is, γ_R ≥ γ_S iff V_r(R) ≥ V_r(S). This follows from:
1. γ_R = productLeftSliceValue at U_A = V_{q⊗r}(U_A ⊗ R)
2. The product right-slice same-order theorem. -/
theorem leftSliceIntercept_same_order_as_Vr
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R S : Channel B Y) :
    hslice.leftSliceIntercept F hax hs q r R ≥
      hslice.leftSliceIntercept F hax hs q r S ↔
    hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
  rw [leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr R,
      leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr S]
  exact product_right_slice_same_order F hax hs q r hq hr
    (Channel.uninformativeChannelU A) R S

/-- The left-slice intercept is public-mix affine in R. This is the missing
"γ is affine" premise from the paper's Step 2.
Derived from: intercept = no-info product value + right-slice public-mix affinity. -/
theorem leftSliceIntercept_publicMix_affine
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (R : Channel B Y) (S : Channel B Z) :
    hslice.leftSliceIntercept F hax hs q r (publicMixChannel t ht0 ht1 R S) =
      t * hslice.leftSliceIntercept F hax hs q r R +
        (1 - t) * hslice.leftSliceIntercept F hax hs q r S := by
  rw [leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr,
      leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr R,
      leftSliceIntercept_eq_noInfo_productLeftSliceValue hslice F hax hs q r hq hr S]
  simp only [productLeftSliceValue]
  exact product_right_slice_publicMix_affine hVaff hax hs q r hq hr
    (Channel.uninformativeChannelU A) t ht0 ht1 R S

/--
**Second-Coordinate Affine Utility Uniqueness**

Narrow classical/HM uniqueness interface for the intercept step in Step 2 of
Lemma `coherentnorm`. If a second-coordinate functional γ is public-mix affine,
represents the same weak order as the posterior value representative `V_r`, and
vanishes at the no-information experiment, then γ is a positive linear multiple
of `V_r`.

This is deliberately separated from the first-coordinate
`ClassicalAffineUtilityUniquenessAssumptions`, whose conclusion is hard-coded to
`productLeftSliceValue`.
-/
structure ClassicalSecondCoordinateAffineUniquenessAssumptions.{v} where
  positive_linear_of_same_order_affine_zero :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (γ : {Y : Type v} → [Fintype Y] → [DecidableEq Y] → Channel B Y → ℝ),
      (∀ {Y Z : Type v} [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (R : Channel B Y) (S : Channel B Z),
        γ (publicMixChannel t ht0 ht1 R S) =
          t * γ R + (1 - t) * γ S) →
      (∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
        (R S : Channel B Y),
        γ R ≥ γ S ↔
          hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
            hs.branch_agg.value_rep.V r (experimentOfChannel S)) →
      γ (Channel.uninformativeChannelU B) = 0 →
      ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          γ R =
            Bcoeff * hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Apply second-coordinate affine uniqueness to the left-slice intercept
function γ_R. The same-order, zero, and public-mix affine hypotheses are exactly
the Stage 10O/10P internal theorems. -/
theorem leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateAffineUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    ∃ Bcoeff : ℝ, 0 < Bcoeff ∧
      ∀ {Y : Type u} [Fintype Y] [DecidableEq Y]
        (R : Channel B Y),
        hslice.leftSliceIntercept F hax hs q r R =
          Bcoeff * hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  let γ : {Y : Type u} → [Fintype Y] → [DecidableEq Y] → Channel B Y → ℝ :=
    fun {Y} [Fintype Y] [DecidableEq Y] R =>
      hslice.leftSliceIntercept F hax hs q r R
  have haff :
      ∀ {Y Z : Type u} [Fintype Y] [DecidableEq Y]
        [Fintype Z] [DecidableEq Z]
        (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (R : Channel B Y) (S : Channel B Z),
        γ (publicMixChannel t ht0 ht1 R S) =
          t * γ R + (1 - t) * γ S := by
    intro Y Z _ _ _ _ t ht0 ht1 R S
    change
      hslice.leftSliceIntercept F hax hs q r
          (publicMixChannel t ht0 ht1 R S) =
        t * hslice.leftSliceIntercept F hax hs q r R +
          (1 - t) * hslice.leftSliceIntercept F hax hs q r S
    exact leftSliceIntercept_publicMix_affine hslice hVaff hax hs
      q r hq hr t ht0 ht1 R S
  have horder :
      ∀ {Y : Type u} [Fintype Y] [DecidableEq Y]
        (R S : Channel B Y),
        γ R ≥ γ S ↔
          hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
            hs.branch_agg.value_rep.V r (experimentOfChannel S) := by
    intro Y _ _ R S
    change
      hslice.leftSliceIntercept F hax hs q r R ≥
        hslice.leftSliceIntercept F hax hs q r S ↔
      hs.branch_agg.value_rep.V r (experimentOfChannel R) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel S)
    exact leftSliceIntercept_same_order_as_Vr hslice F hax hs q r hq hr R S
  have hzero : γ (Channel.uninformativeChannelU B) = 0 := by
    change
      hslice.leftSliceIntercept F hax hs q r
        (Channel.uninformativeChannelU B) = 0
    exact leftSliceIntercept_uninformative_eq_zero hslice F hax hs q r hq hr
  exact
    huniq.positive_linear_of_same_order_affine_zero
      F hax hs q r hq hr γ haff horder hzero

/--
**Product Slice Intercept Assumptions**

Paper-specific content identifying the first-coordinate slice intercept
`γ_R = L(δ_q,R)` as a positive multiple of the second-coordinate value:

`γ_R = B_{q,r} V_r(R)`.
-/
structure FiniteProductSliceInterceptAssumptions.{v}
    (hslice : FiniteProductLeftSliceAffineAssumptions.{v}) where
  rightCoeff :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff F hax hs q r
  leftSliceIntercept_value :
    ∀ (F : PrefFamily.{v})
      (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      hslice.leftSliceIntercept F hax hs q r R =
        rightCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- The positive coefficient in the intercept theorem supplied by
second-coordinate affine uniqueness. It is only read at full-support priors; the
fallback value is irrelevant and keeps the total function well-defined. -/
noncomputable def leftSliceInterceptRightCoeff
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateAffineUniquenessAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
          hslice hVaff huniq F hax hs q r h.1 h.2)
    else 1

/-- Recover the previous intercept compatibility package from the narrower
second-coordinate affine-uniqueness interface plus the internal Stage 10O/10P
same-order, zero, and public-mix affine facts. -/
noncomputable def productSliceIntercept_of_secondCoordinateAffineUniqueness
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hVaff : FinitePosteriorLawValueAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateAffineUniquenessAssumptions.{u}) :
    FiniteProductSliceInterceptAssumptions.{u} hslice where
  rightCoeff := by
    intro F hax hs A B _ _ _ _ _ _ q r
    exact leftSliceInterceptRightCoeff hslice hVaff huniq F hax hs q r
  rightCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    classical
    have hpos :=
      (Classical.choose_spec
        (leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
          hslice hVaff huniq F hax hs q r hq hr)).1
    simpa [leftSliceInterceptRightCoeff, hq, hr] using hpos
  leftSliceIntercept_value := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hspec :=
      (Classical.choose_spec
        (leftSliceIntercept_positive_linear_of_secondCoordinateAffineUniqueness
          hslice hVaff huniq F hax hs q r hq hr)).2 (R := R)
    simpa [leftSliceInterceptRightCoeff, hq, hr] using hspec

/--
**Product Slice Slope Assumptions**

Paper-specific content identifying the first-coordinate slice slope as affine
in the second-coordinate value:

`α_R = A_{q,r} + C_{q,r} V_r(R)`.
-/
structure FiniteProductSliceSlopeAssumptions.{v}
    (hslice : FiniteProductLeftSliceAffineAssumptions.{v}) where
  leftCoeff :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff F hax hs q r
  leftSliceSlope_value :
    ∀ (F : PrefFamily.{v})
      (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (R : Channel B Y),
      hslice.leftSliceSlope F hax hs q r R =
        leftCoeff F hax hs q r +
        interactionCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Difference-quotient identity for a first-coordinate affine slice. This is
the formal version of the paper's comparison of the slice value at two
first-coordinate experiments: the product-value gap is the slice slope times
the base-value gap. -/
theorem leftSliceSlope_mul_value_gap_eq_product_value_gap
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Z Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Z] [DecidableEq Z]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel A Z) (R : Channel B Y) :
    hslice.leftSliceSlope F hax hs q r R *
        (hs.branch_agg.value_rep.V q (experimentOfChannel P) -
          hs.branch_agg.value_rep.V q (experimentOfChannel Q)) =
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) -
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel Q R)) := by
  rw [hslice.left_slice_affine F hax hs q r hq hr P R,
      hslice.left_slice_affine F hax hs q r hq hr Q R]
  ring

/--
**Second-Coordinate Slope Affine Uniqueness**

Paper-specific affine-utility uniqueness conclusion for the slope function in
Step 2 of Lemma `coherentnorm`. After the paper compares a nonconstant
first-coordinate witness with the intercept identity, the first-coordinate
slice slope has the form

`α_R = A_{q,r} + C_{q,r} V_r(R)`, with `A_{q,r} > 0`.

Stage 10R keeps this as the live narrow slope obligation and derives the
previous `FiniteProductSliceSlopeAssumptions` compatibility package from it.
-/
structure ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{v}
    (hslice : FiniteProductLeftSliceAffineAssumptions.{v}) where
  slope_affine_in_second_value :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      ∃ Acoeff Ccoeff : ℝ, 0 < Acoeff ∧
        ∀ {Y : Type v} [Fintype Y] [DecidableEq Y]
          (R : Channel B Y),
          hslice.leftSliceSlope F hax hs q r R =
            Acoeff +
              Ccoeff * hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- The positive constant term in the slope-affine theorem. It is only used
under full-support guards; the fallback value is irrelevant. -/
noncomputable def leftSliceSlopeLeftCoeff
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{u} hslice)
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (huniq.slope_affine_in_second_value F hax hs q r h.1 h.2)
    else 1

/-- The interaction coefficient in the slope-affine theorem. It is only used
under full-support guards; the fallback value is irrelevant. -/
noncomputable def leftSliceSlopeInteractionCoeff
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{u} hslice)
    (F : PrefFamily.{u}) (hax : TraceAxioms F) (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ := by
  classical
  exact
    if h : q.FullSupport ∧ r.FullSupport then
      Classical.choose
        (Classical.choose_spec
          (huniq.slope_affine_in_second_value F hax hs q r h.1 h.2))
    else 0

/-- Recover the previous slope compatibility package from the narrower
second-coordinate slope-affine uniqueness interface. -/
noncomputable def productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (huniq : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{u} hslice) :
    FiniteProductSliceSlopeAssumptions.{u} hslice where
  leftCoeff := by
    intro F hax hs A B _ _ _ _ _ _ q r
    exact leftSliceSlopeLeftCoeff hslice huniq F hax hs q r
  interactionCoeff := by
    intro F hax hs A B _ _ _ _ _ _ q r
    exact leftSliceSlopeInteractionCoeff hslice huniq F hax hs q r
  leftCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    classical
    have hpos :=
      (Classical.choose_spec
        (Classical.choose_spec
          (huniq.slope_affine_in_second_value F hax hs q r hq hr))).1
    simpa [leftSliceSlopeLeftCoeff, hq, hr] using hpos
  leftSliceSlope_value := by
    intro F hax hs A B Y _ _ _ _ _ _ _ _ q r hq hr R
    classical
    have hspec :=
      (Classical.choose_spec
        (Classical.choose_spec
          (huniq.slope_affine_in_second_value F hax hs q r hq hr))).2 (R := R)
    simpa [leftSliceSlopeLeftCoeff, leftSliceSlopeInteractionCoeff, hq, hr]
      using hspec

/--
**Pairwise Product Bilinear Assumptions**

Compatibility package for the conclusion of Step 2 of Lemma `coherentnorm`.
Stage 10F no longer keeps this as the live external assumption; it is derived
from left-slice affinity plus the intercept and slope identifications.
-/
structure FinitePairwiseProductBilinearAssumptions.{v} where
  leftCoeff :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  rightCoeff :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  interactionCoeff :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A B : Type v} →
      [Fintype A] → [DecidableEq A] → [Nonempty A] →
      [Fintype B] → [DecidableEq B] → [Nonempty B] →
      Dist A → Dist B → ℝ
  leftCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < leftCoeff F hax hs q r
  rightCoeff_pos :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      0 < rightCoeff F hax hs q r
  product_pair_bilinear :
    ∀ (F : PrefFamily.{v})
      (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        leftCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        rightCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r (experimentOfChannel R) +
        interactionCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Assemble pairwise bilinear product form from the three Step 2 slice-affine
components isolated in Stage 10F. -/
def pairwiseProductBilinear_of_sliceAffine
    (hslice : FiniteProductLeftSliceAffineAssumptions.{u})
    (hintercept : FiniteProductSliceInterceptAssumptions.{u} hslice)
    (hslope : FiniteProductSliceSlopeAssumptions.{u} hslice) :
    FinitePairwiseProductBilinearAssumptions.{u} where
  leftCoeff := hslope.leftCoeff
  rightCoeff := hintercept.rightCoeff
  interactionCoeff := hslope.interactionCoeff
  leftCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hslope.leftCoeff_pos F hax hs q r hq hr
  rightCoeff_pos := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hintercept.rightCoeff_pos F hax hs q r hq hr
  product_pair_bilinear := by
    intro F hax hs A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hslice.left_slice_affine F hax hs q r hq hr P R]
    rw [hslope.leftSliceSlope_value F hax hs q r hq hr R]
    rw [hintercept.leftSliceIntercept_value F hax hs q r hq hr R]
    ring

/-- The product of two no-information channels has zero value. Its outcome
space is a product of two `PUnit` spaces, hence subsingleton. -/
theorem V_prod_uninformative_uninformative_eq_zero
    (F : PrefFamily.{u}) (hV : PosteriorValueRepresentation F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hV.V (prodDist q r)
      (experimentOfChannel
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.uninformativeChannelU B))) = 0 := by
  exact V_eq_zero_of_subsingleton_outcome F hV
    (prodDist q r) (prodDist_fullSupport q r hq hr)
    (prodChannel (Channel.uninformativeChannelU A)
      (Channel.uninformativeChannelU B))

/-- Full revelation has nonzero value at full-support non-singleton priors. -/
theorem V_idChannel_ne_zero_of_A1
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hnot_subsingleton : ¬ Subsingleton A) :
    hs.branch_agg.value_rep.V q
      (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 := by
  have hne :=
    (valueNonconstancy_of_A1_experiment_strictness
      a1ExperimentPairStrictness_of_axioms).base_value_nonconstant
      F hax hs q hq hnot_subsingleton
  have hzero :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hs.branch_agg.value_rep.zero_normalized q hq
  intro hid_zero
  exact hne (hid_zero.trans hzero.symm)

/-- Pairwise bilinear form with no information in the right coordinate. -/
theorem product_pair_bilinear_right_uninformative
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel
          (prodChannel P (Channel.uninformativeChannelU B))) =
      hpair.leftCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P
    (Channel.uninformativeChannelU B)]
  rw [hs.branch_agg.value_rep.zero_normalized r hr]
  ring

/-- Pairwise bilinear form with no information in the left coordinate. -/
theorem product_pair_bilinear_left_uninformative
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel
          (prodChannel (Channel.uninformativeChannelU A) R)) =
      hpair.rightCoeff F hax hs q r *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr
    (Channel.uninformativeChannelU A) R]
  rw [hs.branch_agg.value_rep.zero_normalized q hq]
  ring

/-- If the left action set is singleton, the pairwise bilinear identity cannot
read the left or interaction coefficients: all left-coordinate values are zero. -/
theorem product_pair_bilinear_subsingleton_left
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hpair.rightCoeff F hax hs q r *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P]
  ring

/-- If the right action set is singleton, the pairwise bilinear identity cannot
read the right or interaction coefficients: all right-coordinate values are zero. -/
theorem product_pair_bilinear_subsingleton_right
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hpair.leftCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep r hr R]
  ring

/-- If the left action set is singleton, the interaction term in the pairwise
bilinear formula is identically zero. Thus product values cannot identify the
interaction coefficient in this degenerate coordinate. -/
theorem product_pair_bilinear_subsingleton_left_interaction_drops_out
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Subsingleton A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hpair.interactionCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) = 0 := by
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep q hq P]
  ring

/-- If the right action set is singleton, the interaction term in the pairwise
bilinear formula is identically zero. Thus product values cannot identify the
interaction coefficient in this degenerate coordinate. -/
theorem product_pair_bilinear_subsingleton_right_interaction_drops_out
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hpair.interactionCoeff F hax hs q r *
        hs.branch_agg.value_rep.V q (experimentOfChannel P) *
        hs.branch_agg.value_rep.V r (experimentOfChannel R) = 0 := by
  rw [V_channel_eq_zero_of_subsingleton F hs.branch_agg.value_rep r hr R]
  ring

/-- Product priors are symmetric up to the canonical product-label swap. -/
theorem relabelDist_prodComm
    {A B : Type u} [Fintype A] [Fintype B]
    (q : Dist A) (r : Dist B) :
    Relabeling.relabelDist (Equiv.prodComm A B) (prodDist q r) =
      prodDist r q := by
  ext x
  rcases x with ⟨b, a⟩
  simp [Relabeling.relabelDist, prodDist_apply_pair, mul_comm]

/-- Product channels are symmetric up to the canonical product-label swap on
actions and outcomes. -/
theorem relabelChannel_prodComm
    {A B O Y : Type u}
    [Fintype A] [Fintype B] [Fintype O] [Fintype Y]
    (P : Channel A O) (R : Channel B Y) :
    Relabeling.relabelChannel (Equiv.prodComm A B) (Equiv.prodComm O Y)
        (prodChannel P R) =
      prodChannel R P := by
  ext x o
  rcases x with ⟨b, a⟩
  rcases o with ⟨y, o⟩
  simp [Relabeling.relabelChannel, prodChannel_apply_pair, mul_comm]

/-- Outcome marginals are transported by simultaneous action/outcome relabeling. -/
theorem outcomeMarginal_relabelChannel
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) (y : Y) :
    Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y =
      Channel.outcomeMarginal P q (eO.symm y) := by
  simp only [Channel.outcomeMarginal_apply, Relabeling.relabelDist_apply,
    Relabeling.relabelChannel_apply]
  rw [Equiv.sum_comp eA.symm (fun a : A => q a * P a (eO.symm y))]

/-- At positive outcomes, posteriors are transported by simultaneous
action/outcome relabeling. Zero-marginal outcomes are irrelevant to posterior
laws and are therefore left out of this statement. -/
theorem posterior_relabelChannel_of_pos
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) (y : Y)
    (hpos : Channel.outcomeMarginal P q (eO.symm y) > 0) :
    Channel.posterior (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y =
      Relabeling.relabelDist eA (Channel.posterior P q (eO.symm y)) := by
  have hpos' : Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y > 0 := by
    rw [outcomeMarginal_relabelChannel eA eO q P y]
    exact hpos
  ext b
  unfold Channel.posterior
  rw [dif_pos hpos', dif_pos hpos]
  change (Relabeling.relabelDist eA q b *
        Relabeling.relabelChannel eA eO P b y) /
        Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
          (Relabeling.relabelDist eA q) y =
      q (eA.symm b) * P (eA.symm b) (eO.symm y) /
        Channel.outcomeMarginal P q (eO.symm y)
  rw [outcomeMarginal_relabelChannel eA eO q P y]
  rfl

/-- Posterior-law integrals are transported by simultaneous action/outcome
relabeling. This is the structural posterior-law form of exact relabeling:
test functions on the relabeled action simplex are pulled back by the action
relabeling. -/
theorem posteriorLawIntegral_relabelChannel
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) (φ : Dist B → ℝ) :
    posteriorLawIntegral (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel eA eO P) φ =
      posteriorLawIntegral q P (fun d => φ (Relabeling.relabelDist eA d)) := by
  unfold posteriorLawIntegral
  let f : O → ℝ := fun o =>
    Channel.outcomeMarginal P q o *
      φ (Relabeling.relabelDist eA (Channel.posterior P q o))
  let g : Y → ℝ := fun y =>
    Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y *
      φ (Channel.posterior (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) y)
  change (∑ y : Y, g y) = ∑ o : O, f o
  exact (Fintype.sum_equiv eO f g (by
    intro o
    dsimp [f, g]
    change Channel.outcomeMarginal P q o *
        φ (Relabeling.relabelDist eA (Channel.posterior P q o)) =
      Channel.outcomeMarginal (Relabeling.relabelChannel eA eO P)
          (Relabeling.relabelDist eA q) (eO o) *
        φ (Channel.posterior (Relabeling.relabelChannel eA eO P)
          (Relabeling.relabelDist eA q) (eO o))
    rw [outcomeMarginal_relabelChannel eA eO q P (eO o)]
    simp only [Equiv.symm_apply_apply]
    by_cases hpos : Channel.outcomeMarginal P q o > 0
    · rw [posterior_relabelChannel_of_pos eA eO q P (eO o)]
      · simp
      · simpa
    · have hmarg_nonneg : 0 ≤ Channel.outcomeMarginal P q o :=
        (Channel.outcomeMarginal P q).nonneg o
      have hmarg_zero : Channel.outcomeMarginal P q o = 0 := by
        exact le_antisymm (le_of_not_gt hpos) hmarg_nonneg
      rw [hmarg_zero]
      simp)).symm

/-- Posterior-law integrals for the two product parenthesizations agree after
pulling test functions back along the canonical product associativity
relabeling. This is structural posterior-law plumbing; it is not yet the
cardinal value equality needed for coefficient comparison. -/
theorem posteriorLawIntegral_prodAssoc
    {A B C O Y Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (P : Channel A O) (R : Channel B Y) (S : Channel C Z)
    (φ : Dist (A × (B × C)) → ℝ) :
    posteriorLawIntegral (prodDist q (prodDist r s))
        (prodChannel P (prodChannel R S)) φ =
      posteriorLawIntegral (prodDist (prodDist q r) s)
        (prodChannel (prodChannel P R) S)
        (fun d => φ (Relabeling.relabelDist (Equiv.prodAssoc A B C) d)) := by
  have h := posteriorLawIntegral_relabelChannel
    (eA := Equiv.prodAssoc A B C)
    (eO := Equiv.prodAssoc O Y Z)
    (q := prodDist (prodDist q r) s)
    (P := prodChannel (prodChannel P R) S)
    (φ := φ)
  simpa [relabelDist_prodAssoc q r s, relabelChannel_prodAssoc P R S] using h

/-- Normalized branch values are exactly invariant under relabelling once the
chosen value representatives and the chosen chain scales are both coherent
under relabelling. -/
theorem branchNormalizedValue_relabel_eq_of_valueRelabeling_and_faceScales
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    branchNormalizedValue hfaces.chain
        (Relabeling.relabelDist eA q)
        (Relabeling.relabelChannel eA eO P) =
      branchNormalizedValue hfaces.chain q P := by
  unfold branchNormalizedValue
  unfold CoherentRelabelingFaceScalesStructure.chain
  unfold BranchAggregationCocycleNormalizedChainRuleStructure.chain
  unfold branchChainStructure_of_scaleFactorization
  have hVeq :=
    exactRelabelingInvariance_of_valueRelabeling
      hrelV F hax hfaces.branch_result.branch_agg.value_rep
      eA eO q P
  have hscale :=
    CoherentRelabelingFaceScalesStructure.scale_relabel_eq
      hfaces eA q hq
  change
    hfaces.branch_result.branch_agg.value_rep.V
        (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) /
      hfaces.branch_result.scale_factorization.scale
        (Relabeling.relabelDist eA q)
    =
    hfaces.branch_result.branch_agg.value_rep.V q
        (experimentOfChannel P) /
      hfaces.branch_result.scale_factorization.scale q
  rw [hVeq, hscale]

/-- The cardinal value-level triple-product associativity statement needed by
paper Step 3. It says that the two parenthesizations of a product experiment
have the same value after canonical product associativity is accounted for. -/
def TripleProductValueAssociates
    (F : PrefFamily.{u}) (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C) : Prop :=
  ∀ {O Y Z : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    [Fintype Z] [DecidableEq Z]
    (P : Channel A O) (R : Channel B Y) (S : Channel C Z),
      hs.branch_agg.value_rep.V (prodDist (prodDist q r) s)
          (experimentOfChannel (prodChannel (prodChannel P R) S)) =
        hs.branch_agg.value_rep.V (prodDist q (prodDist r s))
          (experimentOfChannel (prodChannel P (prodChannel R S)))

/--
Value-level triple-product associativity. This isolates the exact cardinal
upgrade from the structural posterior-law transport theorem
`posteriorLawIntegral_prodAssoc` to equality of the chosen value
representatives across the two product action types.
-/
structure FiniteTripleProductValueAssociativityAssumptions.{v} where
  triple_value_assoc :
    ∀ (F : PrefFamily.{v}) (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s

/-- Product-parenthesization value associativity follows from the coherent
value-relabeling interface and the structural product associativity relabeling
facts. -/
theorem tripleProductValueAssociates_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport) :
    TripleProductValueAssociates F hs q r s := by
  intro O Y Z _ _ _ _ _ _ P R S
  have hrel :=
    hrelV.V_relabel_eq F hax hs.branch_agg.value_rep
      (Equiv.prodAssoc A B C) (Equiv.prodAssoc O Y Z)
      (prodDist (prodDist q r) s) (prodChannel (prodChannel P R) S)
  have hrel' :
      hs.branch_agg.value_rep.V (prodDist q (prodDist r s))
          (experimentOfChannel (prodChannel P (prodChannel R S))) =
        hs.branch_agg.value_rep.V (prodDist (prodDist q r) s)
          (experimentOfChannel (prodChannel (prodChannel P R) S)) := by
    simpa [relabelDist_prodAssoc q r s, relabelChannel_prodAssoc P R S] using hrel
  exact hrel'.symm

/-- Reconstruct value-level triple-product associativity from coherent
value-relabeling of the chosen posterior representatives. -/
theorem tripleProductValueAssociativity_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u}) :
    FiniteTripleProductValueAssociativityAssumptions.{u} where
  triple_value_assoc := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact tripleProductValueAssociates_of_value_relabeling
      hrelV F hax hs q r s hq hr hsupp

/--
**Product Gauge Coherence Assumptions**

Paper-specific content from Steps 3-5 of Lemma `coherentnorm`: after coherent
positive rescaling of the zero-normalized representatives, the pair-specific
linear coefficients are both one and the interaction coefficient is a common
scalar `κ`, including singleton compatibility.
-/
structure FiniteProductGaugeCoherenceAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  kappa : ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F → ℝ
  leftCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff F hax hs q r = 1
  rightCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff F hax hs q r = 1
  interactionCoeff_common :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.interactionCoeff F hax hs q r = kappa F hax hs

/-- Ratio of the two linear coefficients before Step 3 gauge normalization:
`rho(p,r) = B_{p,r}/A_{p,r}` in the paper. -/
noncomputable def linearCoeffRho
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.rightCoeff F hax hs q r / hpair.leftCoeff F hax hs q r

/-- The coefficient ratio is positive at full-support priors. -/
theorem linearCoeffRho_pos
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    0 < linearCoeffRho hpair F hax hs q r := by
  unfold linearCoeffRho
  exact div_pos (hpair.rightCoeff_pos F hax hs q r hq hr)
    (hpair.leftCoeff_pos F hax hs q r hq hr)

/-- Product-swap value equality from coherent value relabeling and the
structural product-swap relabeling facts. -/
theorem product_value_swap_eq_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hs.branch_agg.value_rep.V (prodDist r q)
        (experimentOfChannel (prodChannel R P)) := by
  have hrel :=
    hrelV.V_relabel_eq F hax hs.branch_agg.value_rep
      (Equiv.prodComm A B) (Equiv.prodComm O Y)
      (prodDist q r) (prodChannel P R)
  have hrel' :
      hs.branch_agg.value_rep.V (prodDist r q)
          (experimentOfChannel (prodChannel R P)) =
        hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) := by
    simpa [relabelDist_prodComm q r, relabelChannel_prodComm P R] using hrel
  exact hrel'.symm

/--
Paper Step 3 coefficient associativity equations C1-C3, obtained by comparing
the two parenthesizations of a triple product after identifying product types by
the canonical associativity relabeling.
-/
structure FiniteProductLinearCoeffAssociativityAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/-- Nondegenerate C1 coefficient extraction. Vary the first coordinate and set
the second and third coordinates to no information. -/
theorem coeff_assoc_A_from_triple_of_nontrivial_left
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton A)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.leftCoeff F hax hs (prodDist q r) s *
        hpair.leftCoeff F hax hs q r =
      hpair.leftCoeff F hax hs q (prodDist r s) := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hVnonzero :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hnot_subsingleton
  have hleft_inner :
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel A A)
              (Channel.uninformativeChannelU B))) =
        hpair.leftCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q
            (experimentOfChannel (Channel.idChannel : Channel A A)) :=
    product_pair_bilinear_right_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel A A)
  have hright_inner_zero :
      hs.branch_agg.value_rep.V (prodDist r s)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU B)
              (Channel.uninformativeChannelU C))) = 0 :=
    V_prod_uninformative_uninformative_eq_zero F hs.branch_agg.value_rep
      r s hr hsupp
  have hval := htriple
    (P := (Channel.idChannel : Channel A A))
    (R := (Channel.uninformativeChannelU B))
    (S := (Channel.uninformativeChannelU C))
  rw [hpair.product_pair_bilinear F hax hs (prodDist q r) s hqr hsupp
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear F hax hs q (prodDist r s) hq hrs
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.uninformativeChannelU B)
        (Channel.uninformativeChannelU C))] at hval
  rw [hleft_inner, hs.branch_agg.value_rep.zero_normalized s hsupp,
      hright_inner_zero] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate C2 coefficient extraction. Vary the middle coordinate and
set the first and third coordinates to no information. -/
theorem coeff_assoc_mixed_from_triple_of_nontrivial_middle
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton B)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.leftCoeff F hax hs (prodDist q r) s *
        hpair.rightCoeff F hax hs q r =
      hpair.rightCoeff F hax hs q (prodDist r s) *
        hpair.leftCoeff F hax hs r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hVnonzero :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hnot_subsingleton
  have hleft_inner :
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (Channel.idChannel : Channel B B))) =
        hpair.rightCoeff F hax hs q r *
          hs.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) :=
    product_pair_bilinear_left_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel B B)
  have hright_inner :
      hs.branch_agg.value_rep.V (prodDist r s)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel B B)
              (Channel.uninformativeChannelU C))) =
        hpair.leftCoeff F hax hs r s *
          hs.branch_agg.value_rep.V r
            (experimentOfChannel (Channel.idChannel : Channel B B)) :=
    product_pair_bilinear_right_uninformative hpair F hax hs r s hr hsupp
      (Channel.idChannel : Channel B B)
  have hval := htriple
    (P := (Channel.uninformativeChannelU A))
    (R := (Channel.idChannel : Channel B B))
    (S := (Channel.uninformativeChannelU C))
  rw [hpair.product_pair_bilinear F hax hs (prodDist q r) s hqr hsupp
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B))
      (Channel.uninformativeChannelU C)] at hval
  rw [hpair.product_pair_bilinear F hax hs q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C))] at hval
  rw [hleft_inner, hright_inner, hs.branch_agg.value_rep.zero_normalized s hsupp,
      hs.branch_agg.value_rep.zero_normalized q hq] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate C3 coefficient extraction. Vary the third coordinate and set
the first and second coordinates to no information. -/
theorem coeff_assoc_B_from_triple_of_nontrivial_right
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.rightCoeff F hax hs (prodDist q r) s =
      hpair.rightCoeff F hax hs q (prodDist r s) *
        hpair.rightCoeff F hax hs r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hVnonzero :
      hs.branch_agg.value_rep.V s
        (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs s hsupp hnot_subsingleton
  have hleft_inner_zero :
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (Channel.uninformativeChannelU B))) = 0 :=
    V_prod_uninformative_uninformative_eq_zero F hs.branch_agg.value_rep
      q r hq hr
  have hright_inner :
      hs.branch_agg.value_rep.V (prodDist r s)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU B)
              (Channel.idChannel : Channel C C))) =
        hpair.rightCoeff F hax hs r s *
          hs.branch_agg.value_rep.V s
            (experimentOfChannel (Channel.idChannel : Channel C C)) :=
    product_pair_bilinear_left_uninformative hpair F hax hs r s hr hsupp
      (Channel.idChannel : Channel C C)
  have hval := htriple
    (P := (Channel.uninformativeChannelU A))
    (R := (Channel.uninformativeChannelU B))
    (S := (Channel.idChannel : Channel C C))
  rw [hpair.product_pair_bilinear F hax hs (prodDist q r) s hqr hsupp
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B))
      (Channel.idChannel : Channel C C)] at hval
  rw [hpair.product_pair_bilinear F hax hs q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C))] at hval
  rw [hleft_inner_zero, hright_inner,
      hs.branch_agg.value_rep.zero_normalized q hq] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/--
Coefficient extraction from value-level triple-product associativity. This is
the remaining elementary algebra/uniqueness step in paper Step 3: once the two
triple-product parenthesizations have the same value, comparing the
pair-specific bilinear expansions yields C1-C3.
-/
structure FiniteTripleProductCoeffExtractionAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A_from_triple :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed_from_triple :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B_from_triple :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      TripleProductValueAssociates F hs q r s →
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/--
The remaining degenerate branches for coefficient extraction. Stage 10V proves
C1, C2, and C3 whenever the coordinate whose value is varied is
non-subsingleton. These fields isolate exactly the singleton cases where the
paper's nondegenerate interval argument cannot be reproduced by cancellation.
-/
structure FiniteTripleProductCoeffExtractionSingletonAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A_of_subsingleton :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton A →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed_of_subsingleton :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton B →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B_of_subsingleton :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton C →
      TripleProductValueAssociates F hs q r s →
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/--
Singleton coefficient gauge normalization. On singleton fibres the relevant
coordinate value is identically zero, so the corresponding linear coefficient
is not identified by product values. These equations are therefore classified
as a singleton/gauge normalization, not as an extracted coefficient comparison.
-/
structure FiniteSingletonCoefficientGaugeNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_assoc_A_singleton_normalization :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton A →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.leftCoeff F hax hs q r =
        hpair.leftCoeff F hax hs q (prodDist r s)
  coeff_assoc_mixed_singleton_normalization :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton B →
      TripleProductValueAssociates F hs q r s →
      hpair.leftCoeff F hax hs (prodDist q r) s *
          hpair.rightCoeff F hax hs q r =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.leftCoeff F hax hs r s
  coeff_assoc_B_singleton_normalization :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport),
      Subsingleton C →
      TripleProductValueAssociates F hs q r s →
      hpair.rightCoeff F hax hs (prodDist q r) s =
        hpair.rightCoeff F hax hs q (prodDist r s) *
          hpair.rightCoeff F hax hs r s

/-- Convert the singleton gauge normalization into the old singleton coefficient
extraction compatibility package. -/
theorem tripleProductCoeffExtractionSingleton_of_gaugeNormalization
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hgauge :
      FiniteSingletonCoefficientGaugeNormalizationAssumptions.{u} hpair) :
    FiniteTripleProductCoeffExtractionSingletonAssumptions.{u} hpair where
  coeff_assoc_A_of_subsingleton := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hsub htriple
    exact hgauge.coeff_assoc_A_singleton_normalization
      F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_mixed_of_subsingleton := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hsub htriple
    exact hgauge.coeff_assoc_mixed_singleton_normalization
      F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_B_of_subsingleton := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hsub htriple
    exact hgauge.coeff_assoc_B_singleton_normalization
      F hax hs q r s hq hr hsupp hsub htriple

/-- Reconstruct full coefficient extraction from the internally proved
nondegenerate C1-C3 cases and the remaining singleton branches. -/
theorem tripleProductCoeffExtraction_of_nondegenerate_and_singleton
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hsingle :
      FiniteTripleProductCoeffExtractionSingletonAssumptions.{u} hpair) :
    FiniteTripleProductCoeffExtractionAssumptions.{u} hpair where
  coeff_assoc_A_from_triple := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp htriple
    by_cases hsub : Subsingleton A
    · exact hsingle.coeff_assoc_A_of_subsingleton
        F hax hs q r s hq hr hsupp hsub htriple
    · exact coeff_assoc_A_from_triple_of_nontrivial_left
        hpair F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_mixed_from_triple := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp htriple
    by_cases hsub : Subsingleton B
    · exact hsingle.coeff_assoc_mixed_of_subsingleton
        F hax hs q r s hq hr hsupp hsub htriple
    · exact coeff_assoc_mixed_from_triple_of_nontrivial_middle
        hpair F hax hs q r s hq hr hsupp hsub htriple
  coeff_assoc_B_from_triple := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp htriple
    by_cases hsub : Subsingleton C
    · exact hsingle.coeff_assoc_B_of_subsingleton
        F hax hs q r s hq hr hsupp hsub htriple
    · exact coeff_assoc_B_from_triple_of_nontrivial_right
        hpair F hax hs q r s hq hr hsupp hsub htriple

/-- Reassemble the paper Step 3 C1-C3 coefficient associativity package from
value-level triple associativity plus coefficient extraction. -/
theorem linearCoeffAssociativity_of_triple_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (htriple : FiniteTripleProductValueAssociativityAssumptions.{u})
    (hextract : FiniteTripleProductCoeffExtractionAssumptions.{u} hpair) :
    FiniteProductLinearCoeffAssociativityAssumptions.{u} hpair where
  coeff_assoc_A := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact hextract.coeff_assoc_A_from_triple F hax hs q r s hq hr hsupp
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  coeff_assoc_mixed := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact hextract.coeff_assoc_mixed_from_triple F hax hs q r s hq hr hsupp
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  coeff_assoc_B := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp
    exact hextract.coeff_assoc_B_from_triple F hax hs q r s hq hr hsupp
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)

/--
Paper Step 3 coordinate-swap consequence for the linear coefficient ratio:
`rho(r,p) = rho(p,r)^{-1}`, stated without division by writing the product as
one. This is the coefficient-level part forced by product swap before choosing
the normalized gauge.
-/
structure FiniteProductLinearCoeffSwapAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  rho_reciprocity :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      linearCoeffRho hpair F hax hs q r *
          linearCoeffRho hpair F hax hs r q =
        1

/-- Nondegenerate swap extraction for the first linear coefficient:
`A_{q,r} = B_{r,q}`. -/
theorem leftCoeff_eq_swapped_rightCoeff_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton A) :
    hpair.leftCoeff F hax hs q r =
      hpair.rightCoeff F hax hs r q := by
  have hVnonzero :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hnot_subsingleton
  have hval :=
    product_value_swap_eq_of_value_relabeling hrelV F hax hs q r
      (Channel.idChannel : Channel A A) (Channel.uninformativeChannelU B)
  rw [product_pair_bilinear_right_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel A A)] at hval
  rw [product_pair_bilinear_left_uninformative hpair F hax hs r q hr hq
      (Channel.idChannel : Channel A A)] at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate swap extraction for the second linear coefficient:
`B_{q,r} = A_{r,q}`. -/
theorem rightCoeff_eq_swapped_leftCoeff_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hnot_subsingleton : ¬ Subsingleton B) :
    hpair.rightCoeff F hax hs q r =
      hpair.leftCoeff F hax hs r q := by
  have hVnonzero :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hnot_subsingleton
  have hval :=
    product_value_swap_eq_of_value_relabeling hrelV F hax hs q r
      (Channel.uninformativeChannelU A) (Channel.idChannel : Channel B B)
  rw [product_pair_bilinear_left_uninformative hpair F hax hs q r hq hr
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_right_uninformative hpair F hax hs r q hr hq
      (Channel.idChannel : Channel B B)] at hval
  exact mul_right_cancel₀ hVnonzero (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Nondegenerate rho reciprocity extracted from product swap. -/
theorem linearCoeffRho_reciprocity_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hnot_subsingleton_A : ¬ Subsingleton A)
    (hnot_subsingleton_B : ¬ Subsingleton B) :
    linearCoeffRho hpair F hax hs q r *
        linearCoeffRho hpair F hax hs r q =
      1 := by
  have hA :=
    leftCoeff_eq_swapped_rightCoeff_of_value_swap_nondegenerate
      hrelV hpair F hax hs q r hq hr hnot_subsingleton_A
  have hB :=
    rightCoeff_eq_swapped_leftCoeff_of_value_swap_nondegenerate
      hrelV hpair F hax hs q r hq hr hnot_subsingleton_B
  unfold linearCoeffRho
  rw [hB, hA]
  have hleft_ne :
      hpair.leftCoeff F hax hs q r ≠ 0 :=
    ne_of_gt (hpair.leftCoeff_pos F hax hs q r hq hr)
  have hright_ne :
      hpair.leftCoeff F hax hs r q ≠ 0 :=
    ne_of_gt (hpair.leftCoeff_pos F hax hs r q hr hq)
  have hswapped_right_ne :
      hpair.rightCoeff F hax hs r q ≠ 0 :=
    ne_of_gt (hpair.rightCoeff_pos F hax hs r q hr hq)
  field_simp [hleft_ne, hright_ne, hswapped_right_ne]

/--
Singleton coefficient swap normalization. When one coordinate is singleton, the
corresponding value representative is identically zero, so the swap coefficient
comparison cannot be extracted from value variation. These equations are
therefore classified with the singleton/gauge normalizations rather than as
nondegenerate coefficient extraction.
-/
structure FiniteProductLinearCoeffSwapSingletonNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  rho_reciprocity_of_subsingleton_left :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton A →
      linearCoeffRho hpair F hax hs q r *
          linearCoeffRho hpair F hax hs r q =
        1
  rho_reciprocity_of_subsingleton_right :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton B →
      linearCoeffRho hpair F hax hs q r *
          linearCoeffRho hpair F hax hs r q =
        1

/-- Reconstruct the old swap/rho reciprocity package from the internally
proved nondegenerate swap extraction and the remaining singleton normalization. -/
theorem productLinearCoeffSwap_of_valueSwap_and_singletonNormalization
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hsingle :
      FiniteProductLinearCoeffSwapSingletonNormalizationAssumptions.{u} hpair) :
    FiniteProductLinearCoeffSwapAssumptions.{u} hpair where
  rho_reciprocity := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    by_cases hsubA : Subsingleton A
    · exact hsingle.rho_reciprocity_of_subsingleton_left
        F hax hs q r hq hr hsubA
    · by_cases hsubB : Subsingleton B
      · exact hsingle.rho_reciprocity_of_subsingleton_right
          F hax hs q r hq hr hsubB
      · exact linearCoeffRho_reciprocity_of_value_swap_nondegenerate
          hrelV hpair F hax hs q r hq hr hsubA hsubB

/--
The remaining Step 3 gauge-choice bridge. The paper proves that after choosing
a positive reference-prior gauge and rescaling the zero-normalized
representatives, the current representatives may be taken to satisfy
`A_{p,r}=B_{p,r}=1`. Lean currently has no operation that replaces the
`PosteriorValueRepresentation` inside `ScaleCoherenceStructure` by a positively
rescaled coherent representative, so this record isolates exactly that
chosen-normal-gauge statement.
-/
structure FiniteProductPositiveGaugeChoiceAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  current_leftCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff F hax hs q r = 1
  current_rightCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff F hax hs q r = 1

/-- The paper's coefficient transformation law for the left linear coefficient
under a positive prior-dependent rescaling `F_q^* = φ(q) F_q`. -/
noncomputable def gaugeTransformedLeftCoeff
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (gauge : ∀ (F : PrefFamily.{u}), TraceAxioms F → ScaleCoherenceStructure F →
      {A : Type u} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.leftCoeff F hax hs q r *
    (gauge F hax hs (prodDist q r) / gauge F hax hs q)

/-- The paper's coefficient transformation law for the right linear coefficient
under a positive prior-dependent rescaling `F_q^* = φ(q) F_q`. -/
noncomputable def gaugeTransformedRightCoeff
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (gauge : ∀ (F : PrefFamily.{u}), TraceAxioms F → ScaleCoherenceStructure F →
      {A : Type u} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) : ℝ :=
  hpair.rightCoeff F hax hs q r *
    (gauge F hax hs (prodDist q r) / gauge F hax hs r)

/--
Reference-gauge transform package for paper Step 3. This records the positive
gauge `φ` and the fact that the coefficients obtained after applying the
paper's transform law are normalized. It does not by itself replace the
`PosteriorValueRepresentation` stored inside `ScaleCoherenceStructure`.
-/
structure FiniteProductReferenceGaugeTransformAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  gauge :
    ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F →
      {A : Type v} → [Fintype A] → [DecidableEq A] → [Nonempty A] →
      Dist A → ℝ
  gauge_pos :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      0 < gauge F hax hs q
  transformed_leftCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      gaugeTransformedLeftCoeff hpair gauge F hax hs q r = 1
  transformed_rightCoeff_normalized :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      gaugeTransformedRightCoeff hpair gauge F hax hs q r = 1

/--
Representative-choice normalization connecting the paper's transformed
coefficients to the current Lean representatives. Since the current code does
not implement a new `ScaleCoherenceStructure` with rescaled `V`, this says the
currently selected representatives are the post-gauge representatives.
-/
structure FiniteCurrentRepresentativesGaugeNormalizedAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v})
    (hgauge : FiniteProductReferenceGaugeTransformAssumptions.{v} hpair) where
  current_leftCoeff_eq_transformed :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.leftCoeff F hax hs q r =
        gaugeTransformedLeftCoeff hpair hgauge.gauge F hax hs q r
  current_rightCoeff_eq_transformed :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.rightCoeff F hax hs q r =
        gaugeTransformedRightCoeff hpair hgauge.gauge F hax hs q r

/-- Reconstruct the old normalized-current-coefficients package from the
reference-gauge transform law plus the normalization that the current
representatives are already the post-gauge representatives. -/
theorem positiveGaugeChoice_of_representativeGaugeNormalization
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hgauge : FiniteProductReferenceGaugeTransformAssumptions.{u} hpair)
    (hcurrent :
      FiniteCurrentRepresentativesGaugeNormalizedAssumptions.{u} hpair hgauge) :
    FiniteProductPositiveGaugeChoiceAssumptions.{u} hpair where
  current_leftCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    rw [hcurrent.current_leftCoeff_eq_transformed F hax hs q r hq hr]
    exact hgauge.transformed_leftCoeff_normalized F hax hs q r hq hr
  current_rightCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    rw [hcurrent.current_rightCoeff_eq_transformed F hax hs q r hq hr]
    exact hgauge.transformed_rightCoeff_normalized F hax hs q r hq hr

/--
**Product Gauge Normalization Assumptions**

Compatibility package for paper Step 3 of Lemma `coherentnorm`. Stage 10T no
longer keeps this as the live external assumption; it is derived from the
coefficient associativity equations, the swap/rho reciprocity equation, and the
remaining gauge-choice bridge saying the current representatives have already
been put in the normalized positive gauge.
-/
structure FiniteProductGaugeNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  coeff_associativity : FiniteProductLinearCoeffAssociativityAssumptions.{v} hpair
  coeff_swap : FiniteProductLinearCoeffSwapAssumptions.{v} hpair
  gauge_choice : FiniteProductPositiveGaugeChoiceAssumptions.{v} hpair

/-- Reassemble the Step 3 normalization compatibility package from the
coefficient associativity, swap/rho, and normalized-gauge-choice components. -/
theorem productGaugeNormalization_of_step3_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hassoc : FiniteProductLinearCoeffAssociativityAssumptions.{u} hpair)
    (hswap : FiniteProductLinearCoeffSwapAssumptions.{u} hpair)
    (hgauge : FiniteProductPositiveGaugeChoiceAssumptions.{u} hpair) :
    FiniteProductGaugeNormalizationAssumptions.{u} hpair where
  coeff_associativity := hassoc
  coeff_swap := hswap
  gauge_choice := hgauge

/-- Compatibility accessor for the old normalized-left-coefficient field. -/
theorem FiniteProductGaugeNormalizationAssumptions.leftCoeff_normalized
    {hpair : FinitePairwiseProductBilinearAssumptions.{u}}
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hpair.leftCoeff F hax hs q r = 1 :=
  hnorm.gauge_choice.current_leftCoeff_normalized F hax hs q r hq hr

/-- Compatibility accessor for the old normalized-right-coefficient field. -/
theorem FiniteProductGaugeNormalizationAssumptions.rightCoeff_normalized
    {hpair : FinitePairwiseProductBilinearAssumptions.{u}}
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    hpair.rightCoeff F hax hs q r = 1 :=
  hnorm.gauge_choice.current_rightCoeff_normalized F hax hs q r hq hr

/-- Pairwise product bilinear formula after the Step 3 gauge normalization,
with both linear coefficients rewritten to one. -/
theorem product_pair_bilinear_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (R : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (prodChannel P R)) =
      hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        hs.branch_agg.value_rep.V r (experimentOfChannel R) +
        hpair.interactionCoeff F hax hs q r *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) *
          hs.branch_agg.value_rep.V r (experimentOfChannel R) := by
  rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
  rw [hnorm.leftCoeff_normalized F hax hs q r hq hr]
  rw [hnorm.rightCoeff_normalized F hax hs q r hq hr]
  ring

/--
**Product Interaction Universality Assumptions**

Paper Steps 4-5 of Lemma `coherentnorm`: after the linear coefficients have
been normalized, the remaining interaction coefficient is independent of the
two finite factors, with singleton factors included by compatibility.
-/
structure FiniteProductInteractionUniversalityAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  kappa : ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F → ℝ
  interactionCoeff_common :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      hpair.interactionCoeff F hax hs q r = kappa F hax hs

/-- A fixed nondegenerate reference action type for Step 4 common-κ
arguments. -/
abbrev interactionReferenceType : Type u := ULift.{u, 0} Bool

/-- The fixed full-support reference prior used to name the common interaction
coefficient. -/
noncomputable def interactionReferencePrior : Dist interactionReferenceType :=
  Dist.uniform

theorem interactionReferencePrior_fullSupport :
    interactionReferencePrior.FullSupport :=
  Dist.uniform_fullSupport (A := interactionReferenceType)

theorem interactionReference_not_subsingleton :
    ¬ Subsingleton interactionReferenceType := by
  intro hsub
  have htf : (true : Bool) = false := by
    exact congrArg ULift.down
      (Subsingleton.elim
        (ULift.up true : interactionReferenceType)
        (ULift.up false : interactionReferenceType))
  cases htf

/-- The interaction coefficient at the fixed reference prior. -/
noncomputable def interactionReferenceKappa
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F) : ℝ :=
  hpair.interactionCoeff F hax hs
    interactionReferencePrior interactionReferencePrior

/--
Paper Step 4 interaction associativity equations K1-K4 for nondegenerate
factors after the Step 3 gauge normalization. K4 is recorded for faithfulness
even though the common-κ extraction below only needs K1-K3.
-/
structure FiniteProductInteractionAssociativityAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  interaction_assoc_xy :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs q (prodDist r s)
  interaction_assoc_xz :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs q (prodDist r s)
  interaction_assoc_yz :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs r s
  interaction_assoc_xyz :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B C : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype C] [DecidableEq C] [Nonempty C]
      (q : Dist A) (r : Dist B) (s : Dist C)
      (_hq : q.FullSupport) (_hr : r.FullSupport) (_hsupp : s.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (_hC : ¬ Subsingleton C),
      hpair.interactionCoeff F hax hs (prodDist q r) s *
          hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs q (prodDist r s) *
          hpair.interactionCoeff F hax hs r s

/-- K1 from normalized triple-product expansions. Set the third coordinate to
no information, vary the first two coordinates, and cancel the nonzero A1
witness values. -/
theorem interaction_assoc_xy_from_triple_of_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (_hC : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.interactionCoeff F hax hs q r =
      hpair.interactionCoeff F hax hs q (prodDist r s) := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hxne :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hA
  have hyne :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hB
  have hxyne :
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) *
        hs.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    mul_ne_zero hxne hyne
  have hval := htriple
    (P := (Channel.idChannel : Channel A A))
    (R := (Channel.idChannel : Channel B B))
    (S := (Channel.uninformativeChannelU C))
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      (prodDist q r) s hqr hsupp
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B))
      (Channel.uninformativeChannelU C)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q (prodDist r s) hq hrs
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.idChannel : Channel B B)
        (Channel.uninformativeChannelU C))] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q r hq hr (Channel.idChannel : Channel A A)
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      r s hr hsupp (Channel.idChannel : Channel B B)
      (Channel.uninformativeChannelU C)] at hval
  rw [hs.branch_agg.value_rep.zero_normalized s hsupp] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hxyne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- K2 from normalized triple-product expansions. Set the middle coordinate to
no information, vary the first and third coordinates, and cancel the nonzero
A1 witness values. -/
theorem interaction_assoc_xz_from_triple_of_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
    (hC : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.interactionCoeff F hax hs (prodDist q r) s =
      hpair.interactionCoeff F hax hs q (prodDist r s) := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hxne :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hA
  have hzne :
      hs.branch_agg.value_rep.V s
        (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs s hsupp hC
  have hxzne :
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) *
        hs.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    mul_ne_zero hxne hzne
  have hval := htriple
    (P := (Channel.idChannel : Channel A A))
    (R := (Channel.uninformativeChannelU B))
    (S := (Channel.idChannel : Channel C C))
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      (prodDist q r) s hqr hsupp
      (prodChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B))
      (Channel.idChannel : Channel C C)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q (prodDist r s) hq hrs
      (Channel.idChannel : Channel A A)
      (prodChannel (Channel.uninformativeChannelU B)
        (Channel.idChannel : Channel C C))] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q r hq hr (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      r s hr hsupp (Channel.uninformativeChannelU B)
      (Channel.idChannel : Channel C C)] at hval
  rw [hs.branch_agg.value_rep.zero_normalized r hr] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hxzne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- K3 from normalized triple-product expansions. Set the first coordinate to
no information, vary the last two coordinates, and cancel the nonzero A1
witness values. -/
theorem interaction_assoc_yz_from_triple_of_normalized
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hq : q.FullSupport) (hr : r.FullSupport) (hsupp : s.FullSupport)
    (_hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B)
    (hC : ¬ Subsingleton C)
    (htriple : TripleProductValueAssociates F hs q r s) :
    hpair.interactionCoeff F hax hs (prodDist q r) s =
      hpair.interactionCoeff F hax hs r s := by
  have hqr : (prodDist q r).FullSupport := prodDist_fullSupport q r hq hr
  have hrs : (prodDist r s).FullSupport := prodDist_fullSupport r s hr hsupp
  have hyne :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hB
  have hzne :
      hs.branch_agg.value_rep.V s
        (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs s hsupp hC
  have hyzne :
      hs.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) *
        hs.branch_agg.value_rep.V s
          (experimentOfChannel (Channel.idChannel : Channel C C)) ≠ 0 :=
    mul_ne_zero hyne hzne
  have hval := htriple
    (P := (Channel.uninformativeChannelU A))
    (R := (Channel.idChannel : Channel B B))
    (S := (Channel.idChannel : Channel C C))
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      (prodDist q r) s hqr hsupp
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B))
      (Channel.idChannel : Channel C C)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q (prodDist r s) hq hrs
      (Channel.uninformativeChannelU A)
      (prodChannel (Channel.idChannel : Channel B B)
        (Channel.idChannel : Channel C C))] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      q r hq hr (Channel.uninformativeChannelU A)
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs
      r s hr hsupp (Channel.idChannel : Channel B B)
      (Channel.idChannel : Channel C C)] at hval
  rw [hs.branch_agg.value_rep.zero_normalized q hq] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hyzne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- K4 follows algebraically from K1-K3. -/
theorem interaction_assoc_xyz_from_interaction_assoc_xyz_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    (q : Dist A) (r : Dist B) (s : Dist C)
    (hxy :
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs q (prodDist r s))
    (hxz :
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs q (prodDist r s))
    (hyz :
      hpair.interactionCoeff F hax hs (prodDist q r) s =
        hpair.interactionCoeff F hax hs r s) :
    hpair.interactionCoeff F hax hs (prodDist q r) s *
        hpair.interactionCoeff F hax hs q r =
      hpair.interactionCoeff F hax hs q (prodDist r s) *
        hpair.interactionCoeff F hax hs r s := by
  rw [hxz, hxy, ← hyz, hxz]

/-- Derive the full nondegenerate K1-K4 interaction associativity package from
value-level triple-product associativity and the Step 3 normalized product
gauge. -/
theorem productInteractionAssociativity_of_tripleValue_and_gaugeNormalization
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (htriple : FiniteTripleProductValueAssociativityAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair) :
    FiniteProductInteractionAssociativityAssumptions.{u} hpair where
  interaction_assoc_xy := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_xy_from_triple_of_normalized hpair hnorm
      F hax hs q r s hq hr hsupp hA hB hC
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  interaction_assoc_xz := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_xz_from_triple_of_normalized hpair hnorm
      F hax hs q r s hq hr hsupp hA hB hC
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  interaction_assoc_yz := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_yz_from_triple_of_normalized hpair hnorm
      F hax hs q r s hq hr hsupp hA hB hC
      (htriple.triple_value_assoc F hax hs q r s hq hr hsupp)
  interaction_assoc_xyz := by
    intro F hax hs A B C _ _ _ _ _ _ _ _ _ q r s hq hr hsupp hA hB hC
    exact interaction_assoc_xyz_from_interaction_assoc_xyz_parts
      hpair F hax hs q r s
      (interaction_assoc_xy_from_triple_of_normalized hpair hnorm
        F hax hs q r s hq hr hsupp hA hB hC
        (htriple.triple_value_assoc F hax hs q r s hq hr hsupp))
      (interaction_assoc_xz_from_triple_of_normalized hpair hnorm
        F hax hs q r s hq hr hsupp hA hB hC
        (htriple.triple_value_assoc F hax hs q r s hq hr hsupp))
      (interaction_assoc_yz_from_triple_of_normalized hpair hnorm
        F hax hs q r s hq hr hsupp hA hB hC
        (htriple.triple_value_assoc F hax hs q r s hq hr hsupp))

/-- Paper Step 4 coordinate-swap symmetry for the interaction coefficient in
nondegenerate factors after Step 3 normalization. -/
structure FiniteProductInteractionSwapAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  interaction_swap :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs r q

/-- Nondegenerate interaction coefficient symmetry from product swap after the
Step 3 gauge normalization. Evaluate both coordinates at full revelation, use
product-swap value equality, expand both sides with the normalized pairwise
formula, and cancel the nonzero A1 witness values. -/
theorem interactionCoeff_eq_swapped_of_value_swap_nondegenerate
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.interactionCoeff F hax hs q r =
      hpair.interactionCoeff F hax hs r q := by
  have hxne :
      hs.branch_agg.value_rep.V q
        (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs q hq hA
  have hyne :
      hs.branch_agg.value_rep.V r
        (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    V_idChannel_ne_zero_of_A1 F hax hs r hr hB
  have hxyne :
      hs.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) *
        hs.branch_agg.value_rep.V r
          (experimentOfChannel (Channel.idChannel : Channel B B)) ≠ 0 :=
    mul_ne_zero hxne hyne
  have hval :=
    product_value_swap_eq_of_value_relabeling hrelV F hax hs q r
      (Channel.idChannel : Channel A A) (Channel.idChannel : Channel B B)
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs q r hq hr
      (Channel.idChannel : Channel A A)
      (Channel.idChannel : Channel B B)] at hval
  rw [product_pair_bilinear_normalized hpair hnorm F hax hs r q hr hq
      (Channel.idChannel : Channel B B)
      (Channel.idChannel : Channel A A)] at hval
  ring_nf at hval
  exact mul_right_cancel₀ hxyne (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hval)

/-- Derive the nondegenerate interaction-swap package from coherent product
value relabeling and the Step 3 gauge-normalized product formula. -/
theorem productInteractionSwap_of_valueSwap_and_gaugeNormalization
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair) :
    FiniteProductInteractionSwapAssumptions.{u} hpair where
  interaction_swap := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr hA hB
    exact interactionCoeff_eq_swapped_of_value_swap_nondegenerate
      hrelV hpair hnorm F hax hs q r hq hr hA hB

/--
Singleton interaction normalization. If one factor is singleton, the product
interaction term is multiplied by a zero coordinate value, so the coefficient
is not identified by value variation. The paper handles singleton factors in
Step 5 using extra product-bijection/gauge reasoning; Lean isolates the
remaining normalization directly against the reference common coefficient.
-/
structure FiniteSingletonInteractionCoefficientNormalizationAssumptions.{v}
    (hpair : FinitePairwiseProductBilinearAssumptions.{v}) where
  interactionCoeff_eq_reference_of_subsingleton_left :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton A →
      hpair.interactionCoeff F hax hs q r =
        interactionReferenceKappa hpair F hax hs
  interactionCoeff_eq_reference_of_subsingleton_right :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      Subsingleton B →
      hpair.interactionCoeff F hax hs q r =
        interactionReferenceKappa hpair F hax hs

/-- Nondegenerate common-κ extraction from the K1-K3 associativity equations.
The swap symmetry is part of the paper Step 4 split and is carried by the
reassembly theorem, but K1-K3 already suffice for this algebraic extraction
once the lifted-Bool reference prior is fixed. -/
theorem interactionCoeff_eq_reference_of_assoc_nondegenerate
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hassoc : FiniteProductInteractionAssociativityAssumptions.{u} hpair)
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (hA : ¬ Subsingleton A) (hB : ¬ Subsingleton B) :
    hpair.interactionCoeff F hax hs q r =
      interactionReferenceKappa hpair F hax hs := by
  let q₀ : Dist interactionReferenceType := interactionReferencePrior
  have hq₀ : q₀.FullSupport := interactionReferencePrior_fullSupport
  have hRef : ¬ Subsingleton interactionReferenceType :=
    interactionReference_not_subsingleton
  have h_qr_to_r_ref :
      hpair.interactionCoeff F hax hs q r =
        hpair.interactionCoeff F hax hs r q₀ := by
    calc
      hpair.interactionCoeff F hax hs q r
          = hpair.interactionCoeff F hax hs q (prodDist r q₀) :=
            hassoc.interaction_assoc_xy F hax hs q r q₀ hq hr hq₀ hA hB hRef
      _ = hpair.interactionCoeff F hax hs (prodDist q r) q₀ :=
            (hassoc.interaction_assoc_xz F hax hs q r q₀ hq hr hq₀ hA hB hRef).symm
      _ = hpair.interactionCoeff F hax hs r q₀ :=
            hassoc.interaction_assoc_yz F hax hs q r q₀ hq hr hq₀ hA hB hRef
  have h_r_ref_to_ref_ref :
      hpair.interactionCoeff F hax hs r q₀ =
        hpair.interactionCoeff F hax hs q₀ q₀ := by
    calc
      hpair.interactionCoeff F hax hs r q₀
          = hpair.interactionCoeff F hax hs r (prodDist q₀ q₀) :=
            hassoc.interaction_assoc_xy F hax hs r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
      _ = hpair.interactionCoeff F hax hs (prodDist r q₀) q₀ :=
            (hassoc.interaction_assoc_xz F hax hs r q₀ q₀ hr hq₀ hq₀ hB hRef hRef).symm
      _ = hpair.interactionCoeff F hax hs q₀ q₀ :=
            hassoc.interaction_assoc_yz F hax hs r q₀ q₀ hr hq₀ hq₀ hB hRef hRef
  calc
    hpair.interactionCoeff F hax hs q r
        = hpair.interactionCoeff F hax hs r q₀ := h_qr_to_r_ref
    _ = interactionReferenceKappa hpair F hax hs := by
        simpa [interactionReferenceKappa, q₀] using h_r_ref_to_ref_ref

/-- Reconstruct the old common-κ package from nondegenerate Step 4
associativity, nondegenerate swap symmetry, and the singleton interaction
normalization. -/
noncomputable def interactionUniversality_of_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hassoc : FiniteProductInteractionAssociativityAssumptions.{u} hpair)
    (_hswap : FiniteProductInteractionSwapAssumptions.{u} hpair)
    (hsingle :
      FiniteSingletonInteractionCoefficientNormalizationAssumptions.{u} hpair) :
    FiniteProductInteractionUniversalityAssumptions.{u} hpair where
  kappa := interactionReferenceKappa hpair
  interactionCoeff_common := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    by_cases hsubA : Subsingleton A
    · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_left
        F hax hs q r hq hr hsubA
    · by_cases hsubB : Subsingleton B
      · exact hsingle.interactionCoeff_eq_reference_of_subsingleton_right
          F hax hs q r hq hr hsubB
      · exact interactionCoeff_eq_reference_of_assoc_nondegenerate
          hpair hassoc F hax hs q r hq hr hsubA hsubB

/-- Reassemble the old gauge coherence package from the Step 3 normalization
and Steps 4-5 interaction-universality components. -/
def productGaugeCoherence_of_parts
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (huniv : FiniteProductInteractionUniversalityAssumptions.{u} hpair) :
    FiniteProductGaugeCoherenceAssumptions.{u} hpair where
  kappa := huniv.kappa
  leftCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hnorm.leftCoeff_normalized F hax hs q r hq hr
  rightCoeff_normalized := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact hnorm.rightCoeff_normalized F hax hs q r hq hr
  interactionCoeff_common := by
    intro F hax hs A B _ _ _ _ _ _ q r hq hr
    exact huniv.interactionCoeff_common F hax hs q r hq hr

/--
**Coherent Product Quasi-Additivity Assumptions**

Compatibility package for the conclusion of paper Lemma `coherentnorm`.
Stage 10E no longer keeps this as the live external assumption; it is derived
from pairwise bilinear product form plus coherent gauge/κ normalization.

`V_{q⊗r}(P⊗R) = V_q(P) + V_r(R) + κ V_q(P)V_r(R)`.

Stage 10D uses only the `δ`-factor consequences of this formula, where one
factor is no-information and hence has value zero.
-/
structure FiniteCoherentProductQuasiAdditivityAssumptions.{v} where
  kappa : ∀ (F : PrefFamily.{v}), TraceAxioms F → ScaleCoherenceStructure F → ℝ
  product_quasi_add :
    ∀ (F : PrefFamily.{v})
      (hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B O Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (R : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) =
        hs.branch_agg.value_rep.V q (experimentOfChannel P) +
        hs.branch_agg.value_rep.V r (experimentOfChannel R) +
        kappa F hax hs *
          hs.branch_agg.value_rep.V q (experimentOfChannel P) *
          hs.branch_agg.value_rep.V r (experimentOfChannel R)

/-- Assemble the coherent product quasi-additivity conclusion from the two
paper-level cardinal components isolated in Stage 10E. -/
def coherentProductQuasiAdditivity_of_pairwiseBilinear_and_gauge
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hgauge : FiniteProductGaugeCoherenceAssumptions.{u} hpair) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} where
  kappa := hgauge.kappa
  product_quasi_add := by
    intro F hax hs A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P R
    rw [hpair.product_pair_bilinear F hax hs q r hq hr P R]
    rw [hgauge.leftCoeff_normalized F hax hs q r hq hr]
    rw [hgauge.rightCoeff_normalized F hax hs q r hq hr]
    rw [hgauge.interactionCoeff_common F hax hs q r hq hr]
    ring

/-- Direct coherentnorm reassembly from the decomposed Step 3 normalization
and Steps 4-5 interaction-universality components. This is the same
quasi-additivity package as `coherentProductQuasiAdditivity_of_pairwiseBilinear_and_gauge`,
but exposes that the monolithic gauge package is no longer a live assumption. -/
def coherentProductQuasiAdditivity_of_gaugeNormalization_and_interaction
    (hpair : FinitePairwiseProductBilinearAssumptions.{u})
    (hnorm : FiniteProductGaugeNormalizationAssumptions.{u} hpair)
    (huniv : FiniteProductInteractionUniversalityAssumptions.{u} hpair) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} :=
  coherentProductQuasiAdditivity_of_pairwiseBilinear_and_gauge hpair
    (productGaugeCoherence_of_parts hpair hnorm huniv)

/--
**Product-Lift Value Assumptions**

Paper-specific value identities from Lemma blockbridge, lines 1789-1794:
`F_{q⊗r}(μ_{q,P} ⊗ δ_r) = F_q(μ_{q,P})` and
`F_{q⊗r}(δ_q ⊗ μ_{r,Q}) = F_r(μ_{r,Q})`.

These are the special `δ`-factor consequences of coherent product
quasi-additivity and zero normalization.
-/
structure FiniteProductLiftValueAssumptions.{v} where
  left_lift_value :
    ∀ (F : PrefFamily.{v})
      (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B O : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (leftProductLiftChannel (B := B) P)) =
        hs.branch_agg.value_rep.V q (experimentOfChannel P)
  right_lift_value :
    ∀ (F : PrefFamily.{v})
      (_hax : TraceAxioms F)
      (hs : ScaleCoherenceStructure F)
      {A B Y : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (Q : Channel B Y),
      hs.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (rightProductLiftChannel (A := A) Q)) =
        hs.branch_agg.value_rep.V r (experimentOfChannel Q)

/-- Left product-lift value identity from coherent product quasi-additivity
and zero normalization of the no-information background. -/
theorem left_lift_value_of_coherentProductQuasiAdditivity
    (hcoh : FiniteCoherentProductQuasiAdditivityAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (leftProductLiftChannel (B := B) P)) =
      hs.branch_agg.value_rep.V q (experimentOfChannel P) := by
  rw [leftProductLiftChannel]
  rw [hcoh.product_quasi_add F hax hs q r hq hr P (Channel.uninformativeChannelU B)]
  rw [hs.branch_agg.value_rep.zero_normalized r hr]
  ring

/-- Right product-lift value identity from coherent product quasi-additivity
and zero normalization of the no-information background. -/
theorem right_lift_value_of_coherentProductQuasiAdditivity
    (hcoh : FiniteCoherentProductQuasiAdditivityAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (Q : Channel B Y) :
    hs.branch_agg.value_rep.V (prodDist q r)
        (experimentOfChannel (rightProductLiftChannel (A := A) Q)) =
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) := by
  rw [rightProductLiftChannel]
  rw [hcoh.product_quasi_add F hax hs q r hq hr (Channel.uninformativeChannelU A) Q]
  rw [hs.branch_agg.value_rep.zero_normalized q hq]
  ring

/-- Package the two product-lift value identities derived from coherent
product quasi-additivity. -/
theorem productLiftValue_of_coherentProductQuasiAdditivity
    (hcoh : FiniteCoherentProductQuasiAdditivityAssumptions.{u}) :
    FiniteProductLiftValueAssumptions.{u} where
  left_lift_value := by
    intro F hax hs
    exact left_lift_value_of_coherentProductQuasiAdditivity hcoh F hax hs
  right_lift_value := by
    intro F hax hs
    exact right_lift_value_of_coherentProductQuasiAdditivity hcoh F hax hs

/--
Assemble the unscaled full-support blockbridge from product-lift value
identification, same-prior value representation, and the product-block transfer
proved from A3/A4/A5.
-/
theorem unscaled_cross_prior_block_rep_of_product_parts
    (hvalue : FiniteProductLiftValueAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) := by
  have htransfer' :=
    product_block_transfer_of_A5_A3 F hax q r hq hr P Q
  have hrep :=
    productLiftedComparison_represents F hs q r hq hr P Q
  have hleft :=
    hvalue.left_lift_value F hax hs q r hq hr P
  have hright :=
    hvalue.right_lift_value F hax hs q r hq hr Q
  have hrep' :
      ProductLiftedComparison F q r P Q ↔
        hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
        hs.branch_agg.value_rep.V r (experimentOfChannel Q) := by
    simpa [hleft, hright] using hrep
  exact htransfer'.trans hrep'

/--
**Finite Cross-Prior Block Assumptions**

External assumptions for the paper's unscaled full-support cross-prior
blockbridge, after internalizing the product-to-block transfer from A3/A4/A5
and the A8 value-order coordinate-independence consequence. What remains
external is split into the paper's cardinal coherent-product pieces and the
remaining HM/affine/product bridges: posterior-law value affinity, first-slice
classical affine-utility uniqueness, second-coordinate intercept affine
uniqueness, slope identification, and coherent
gauge/κ normalization. Public-mix posterior-law mixture, product-public-mix
posterior-law compatibility, product-slice public-mix affinity, and cardinal
base-value nonconstancy are now derived/internal; the A1 experiment-pair
strictness bridge is now derived from structural relabeling/block-swap
plumbing; singleton first-slice handling and product-slice intercept
identification are also derived internally. The left-slice affine package,
pairwise bilinear form, coherent product formula, and product-lift value
identities are derived from these parts by setting one factor to the
zero-normalized no-information experiment:

1. `V_{q⊗r}(P ⊗ U_B) = V_q(P)`;
2. `V_{q⊗r}(U_A ⊗ Q) = V_r(Q)`.

The same-prior product comparison itself is proved internally from
`PosteriorValueRepresentation.represents_block_comparisons`.
-/
structure FiniteCrossPriorBlockAssumptions.{v} where
  posterior_law_affinity : FinitePosteriorLawValueAffineAssumptions.{v}
  classical_affine_uniqueness : ClassicalAffineUtilityUniquenessAssumptions.{v}
  intercept_uniqueness : ClassicalSecondCoordinateAffineUniquenessAssumptions.{v}
  slope_uniqueness : ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions.{v}
    (productLeftSliceAffine_of_affineUniqueness
      (affineSliceUniqueness_of_parts
        (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
        (product_left_slice_publicMix_affine_of_posterior_affinity
          (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
          productPublicMixPosteriorLaw_of_structural)
        (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
        singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
  posterior_value_relabeling : FinitePosteriorValueRelabelingAssumptions.{v}
  singleton_coeff_gauge :
    FiniteSingletonCoefficientGaugeNormalizationAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
  gauge_coeff_swap_singleton :
    FiniteProductLinearCoeffSwapSingletonNormalizationAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
  reference_gauge :
    FiniteProductReferenceGaugeTransformAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
  current_gauge_normalized :
    FiniteCurrentRepresentativesGaugeNormalizedAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))
      reference_gauge
  singleton_interaction :
    FiniteSingletonInteractionCoefficientNormalizationAssumptions.{v}
      (pairwiseProductBilinear_of_sliceAffine
        (productLeftSliceAffine_of_affineUniqueness
          (affineSliceUniqueness_of_parts
            (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
            (product_left_slice_publicMix_affine_of_posterior_affinity
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              productPublicMixPosteriorLaw_of_structural)
            (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
            singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
        (productSliceIntercept_of_secondCoordinateAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          posterior_law_affinity intercept_uniqueness)
        (productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
          (productLeftSliceAffine_of_affineUniqueness
            (affineSliceUniqueness_of_parts
              (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
              (product_left_slice_publicMix_affine_of_posterior_affinity
                (posteriorValueAffine_of_lawAffine_and_publicMixLaw posterior_law_affinity)
                productPublicMixPosteriorLaw_of_structural)
              (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
              singletonSliceAffine_of_singletonCollapse classical_affine_uniqueness))
          slope_uniqueness))

/-- The old Stage 10F left-slice affine compatibility package, derived from
the narrower affine-slice uniqueness assumption. -/
theorem FiniteCrossPriorBlockAssumptions.affine_slice
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteAffineSliceUniquenessAssumptions.{u} :=
  affineSliceUniqueness_of_parts
    (posteriorValueAffine_of_lawAffine_and_publicMixLaw hcross.posterior_law_affinity)
    (product_left_slice_publicMix_affine_of_posterior_affinity
      (posteriorValueAffine_of_lawAffine_and_publicMixLaw hcross.posterior_law_affinity)
      productPublicMixPosteriorLaw_of_structural)
    (valueNonconstancy_of_A1_experiment_strictness a1ExperimentPairStrictness_of_axioms)
    singletonSliceAffine_of_singletonCollapse
    hcross.classical_affine_uniqueness

/-- The old Stage 10F left-slice affine compatibility package, derived from the
sharper Stage 10H affine-uniqueness decomposition. -/
noncomputable def FiniteCrossPriorBlockAssumptions.slice_affine
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductLeftSliceAffineAssumptions.{u} :=
  productLeftSliceAffine_of_affineUniqueness hcross.affine_slice

/-- The old Stage 10F intercept package, now derived from second-coordinate
affine uniqueness plus the internal intercept same-order/zero/affinity facts. -/
noncomputable def FiniteCrossPriorBlockAssumptions.slice_intercept
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductSliceInterceptAssumptions.{u} hcross.slice_affine :=
  productSliceIntercept_of_secondCoordinateAffineUniqueness
    hcross.slice_affine hcross.posterior_law_affinity hcross.intercept_uniqueness

/-- The old Stage 10F slope package, now derived from second-coordinate
slope-affine uniqueness. -/
noncomputable def FiniteCrossPriorBlockAssumptions.slice_slope
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductSliceSlopeAssumptions.{u} hcross.slice_affine :=
  productSliceSlope_of_secondCoordinateSlopeAffineUniqueness
    hcross.slice_affine hcross.slope_uniqueness

/-- The pairwise bilinear compatibility package derived from the Stage 10F
slice-affine split assumptions. -/
noncomputable def FiniteCrossPriorBlockAssumptions.pairwise_bilinear
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FinitePairwiseProductBilinearAssumptions.{u} :=
  pairwiseProductBilinear_of_sliceAffine
    hcross.slice_affine hcross.slice_intercept hcross.slice_slope

/-- The singleton coefficient-extraction compatibility package, reconstructed
from the live singleton coefficient gauge normalization. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_singleton
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteTripleProductCoeffExtractionSingletonAssumptions.{u} hcross.pairwise_bilinear :=
  tripleProductCoeffExtractionSingleton_of_gaugeNormalization
    hcross.pairwise_bilinear hcross.singleton_coeff_gauge

/-- The old Stage 10U full coefficient-extraction package, now derived from
the proved nondegenerate C1-C3 extraction lemmas plus the remaining singleton
branches. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_extraction
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteTripleProductCoeffExtractionAssumptions.{u} hcross.pairwise_bilinear :=
  tripleProductCoeffExtraction_of_nondegenerate_and_singleton
    hcross.pairwise_bilinear hcross.gauge_coeff_singleton

/-- The old value-level triple-product associativity package, reconstructed
from coherent value relabeling of the selected posterior representatives. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_triple_value_assoc
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteTripleProductValueAssociativityAssumptions.{u} :=
  tripleProductValueAssociativity_of_value_relabeling
    hcross.posterior_value_relabeling

/-- The old Stage 10T C1-C3 coefficient associativity package, now derived
from value-level triple associativity plus coefficient extraction. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_associativity
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductLinearCoeffAssociativityAssumptions.{u} hcross.pairwise_bilinear :=
  linearCoeffAssociativity_of_triple_parts hcross.pairwise_bilinear
    hcross.gauge_triple_value_assoc hcross.gauge_coeff_extraction

/-- The old Stage 10T coordinate-swap/rho package, now reconstructed from
coherent value relabeling plus the remaining singleton swap normalization. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_coeff_swap
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductLinearCoeffSwapAssumptions.{u} hcross.pairwise_bilinear :=
  productLinearCoeffSwap_of_valueSwap_and_singletonNormalization
    hcross.posterior_value_relabeling hcross.pairwise_bilinear
    hcross.gauge_coeff_swap_singleton

/-- The old Stage 10T positive gauge-choice package, now reconstructed from
the reference-gauge transform law plus the normalization that the current
representatives are already the post-gauge representatives. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_choice
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductPositiveGaugeChoiceAssumptions.{u} hcross.pairwise_bilinear :=
  positiveGaugeChoice_of_representativeGaugeNormalization hcross.pairwise_bilinear
    hcross.reference_gauge hcross.current_gauge_normalized

/-- The old Stage 10S Step 3 normalization package, now derived from
coefficient associativity, swap/rho reciprocity, and the normalized gauge
choice. -/
theorem FiniteCrossPriorBlockAssumptions.gauge_normalization
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductGaugeNormalizationAssumptions.{u} hcross.pairwise_bilinear :=
  productGaugeNormalization_of_step3_parts hcross.pairwise_bilinear
    hcross.gauge_coeff_associativity hcross.gauge_coeff_swap hcross.gauge_choice

/-- The Stage 10AB interaction associativity package, derived from
value-level triple associativity and the Step 3 gauge-normalized product
formula. -/
theorem FiniteCrossPriorBlockAssumptions.interaction_assoc
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductInteractionAssociativityAssumptions.{u} hcross.pairwise_bilinear :=
  productInteractionAssociativity_of_tripleValue_and_gaugeNormalization
    hcross.pairwise_bilinear hcross.gauge_triple_value_assoc hcross.gauge_normalization

/-- The Stage 10AC interaction-swap package, derived from coherent product
value relabeling and the Step 3 gauge-normalized product formula. -/
theorem FiniteCrossPriorBlockAssumptions.interaction_swap
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductInteractionSwapAssumptions.{u} hcross.pairwise_bilinear :=
  productInteractionSwap_of_valueSwap_and_gaugeNormalization
    hcross.posterior_value_relabeling hcross.pairwise_bilinear hcross.gauge_normalization

/-- The old Stage 10S interaction-universality package, reconstructed from
the Step 4 nondegenerate interaction associativity equations, interaction swap
symmetry, and the Step 5 singleton interaction normalization. -/
noncomputable def FiniteCrossPriorBlockAssumptions.interaction_universality
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductInteractionUniversalityAssumptions.{u} hcross.pairwise_bilinear :=
  interactionUniversality_of_parts hcross.pairwise_bilinear
    hcross.interaction_assoc hcross.interaction_swap hcross.singleton_interaction

/-- The old Stage 10E gauge package, now derived from the Step 3 linear
normalization and Steps 4-5 interaction-universality components. -/
noncomputable def FiniteCrossPriorBlockAssumptions.coherent_gauge
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteProductGaugeCoherenceAssumptions.{u} hcross.pairwise_bilinear :=
  productGaugeCoherence_of_parts hcross.pairwise_bilinear
    hcross.gauge_normalization hcross.interaction_universality

/-- The coherent product quasi-additivity compatibility package derived from
the Stage 10E/10F split assumptions. -/
noncomputable def FiniteCrossPriorBlockAssumptions.coherent_product
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} :=
  coherentProductQuasiAdditivity_of_gaugeNormalization_and_interaction
    hcross.pairwise_bilinear hcross.gauge_normalization hcross.interaction_universality

/-- Named Stage 10AE reassembly of paper Lemma `coherentnorm` from the
decomposed HM/coherent-representative interfaces and gauge/singleton
normalizations carried by `FiniteCrossPriorBlockAssumptions`. -/
noncomputable def coherentnorm_of_decomposed_components
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    FiniteCoherentProductQuasiAdditivityAssumptions.{u} :=
  hcross.coherent_product

/-- Compatibility theorem exposing the Stage 10A unscaled bridge from the Stage
10C product decomposition. -/
theorem FiniteCrossPriorBlockAssumptions.unscaled_cross_prior_block_rep
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) :=
  unscaled_cross_prior_block_rep_of_product_parts
    (productLiftValue_of_coherentProductQuasiAdditivity hcross.coherent_product)
    F hax hs q r hq hr P Q

/-!
## Cross-prior blockbridge reassembly

Paper Lemma `blockbridge` is full-support at the formal
`CrossPriorBlockRepresentation` level; arbitrary-prior boundary uses are routed
through the separate support-restriction/boundary-extension layer.
-/

/-- Named full-support unscaled reassembly of paper Lemma `blockbridge`.

It combines coherent product quasi-additivity, zero normalization,
same-prior value representation, and the A3/A4/A5 product-to-block transfer. -/
theorem blockbridge_fullSupport_of_decomposed_components
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hs : ScaleCoherenceStructure F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (P : Channel A O) (Q : Channel B Y) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      hs.branch_agg.value_rep.V q (experimentOfChannel P) ≥
      hs.branch_agg.value_rep.V r (experimentOfChannel Q) :=
  hcross.unscaled_cross_prior_block_rep F hax hs q r hq hr P Q

/-!
## Bridge Theorems

These theorems show how to use entropy reduction in the sufficiency spine.
-/

/--
**Entropy Reduction from Scale Coherence**

Given a scale coherence structure, derive an entropy reduction representation.
-/
noncomputable def entropyReduction_of_assumption
    (F : PrefFamily.{u})
    (hscale : ScaleCoherenceStructure F) :
    EntropyReductionRepresentation F :=
  EntropyReductionRepresentation_of_scale F hscale

/--
**Cross-Prior Block Representation from Unscaled Blockbridge**

Given the external unscaled paper blockbridge and an entropy-reduction
representation, derive the scaled cross-prior block representation by dividing
by the universal positive scale.
-/
noncomputable def crossPriorBlockRepresentation_of_unscaled
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hentropy : EntropyReductionRepresentation F) :
    CrossPriorBlockRepresentation F where
  entropy_reduction := hentropy
  cross_prior_block_rep := by
    intro A B O Y _ _ _ _ _ _ _ _ _ _ q r hq hr P Q
    have hraw :=
      hcross.unscaled_cross_prior_block_rep F hax hentropy.scale_coherence
        q r hq hr P Q
    rw [hraw]
    have hscale :
        hentropy.scale_coherence.scale q = hentropy.scale_coherence.scale r :=
      hentropy.scale_coherence.scale_universal q r hq hr
    have hpos : 0 < hentropy.scale_coherence.scale q :=
      hentropy.scale_coherence.scale_pos q hq
    rw [← hscale]
    exact (div_le_div_iff_of_pos_right hpos).symm

/--
**Cross-Prior Block Representation from Assumption**

Compatibility name for the scaled representation derived from the unscaled
paper blockbridge.
-/
noncomputable def crossPriorBlock_of_assumption
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hentropy : EntropyReductionRepresentation F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_unscaled hcross F hax hentropy

/-- Named Stage 12B scaled reassembly of paper Lemma `blockbridge`.

The unscaled full-support bridge is `blockbridge_fullSupport_of_decomposed_components`;
this wrapper applies the universal positive scale carried by
`EntropyReductionRepresentation`. -/
noncomputable def crossPriorBlockRepresentation_of_decomposed_components
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (F : PrefFamily.{u})
    (hax : TraceAxioms F)
    (hentropy : EntropyReductionRepresentation F) :
    CrossPriorBlockRepresentation F :=
  crossPriorBlockRepresentation_of_unscaled hcross F hax hentropy

/--
**Entropy Reduction from All External Assumptions**

Given the first external assumptions through scale coherence, derive an entropy
reduction representation.

This composes the first five sufficiency bridges:
1. TraceAxioms → PosteriorLawSufficiency (via Blackwell)
2. PosteriorLawSufficiency → PosteriorValueRepresentation (via Herstein-Milnor)
3. PosteriorValueRepresentation → BranchAggregationStructure (via Branch Aggregation)
4. BranchAggregationStructure → ScaleCoherenceStructure (via Scale Coherence)
5. ScaleCoherenceStructure → EntropyReductionRepresentation
   (via internal normalized chain rule)

Paper: Lemmas blockcoh--blackwell + postsep + branchagg + chain + scalecoherence +
faddeevsketch (lines 810-2559).
-/
noncomputable def entropyReduction_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hax : TraceAxioms F) :
    EntropyReductionRepresentation F :=
  let hscaleStruct := scaleCoherence_of_axioms F hblackwell hhm hbranch hscale hax
  EntropyReductionRepresentation_of_scale F hscaleStruct

/--
**Cross-Prior Block Representation from All External Assumptions**

Given the external assumptions through entropy reduction plus the separate
unscaled cross-prior block assumption, derive a scaled cross-prior block
representation.
-/
noncomputable def crossPriorBlock_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hbranch : FiniteBranchAggregationAssumptions.{u})
    (hscale : FiniteScaleCoherenceAssumptions.{u})
    (hcross : FiniteCrossPriorBlockAssumptions.{u})
    (hax : TraceAxioms F) :
    CrossPriorBlockRepresentation F :=
  let hentropyStruct :=
    entropyReduction_of_axioms F hblackwell hhm hbranch hscale hax
  crossPriorBlockRepresentation_of_unscaled hcross F hax hentropyStruct

/-!
## Spine Integration Helper

Shows how to fill the `scale_to_entropy_reduction` field of `SufficiencySpineAssumptions`.
-/

/--
**Scale to Entropy Reduction Bridge**

Provides the bridge from ScaleCoherenceStructure to EntropyReductionRepresentation.

This can be used to fill the `scale_to_entropy_reduction` field when constructing
`SufficiencySpineAssumptions`.
-/
noncomputable def scale_to_entropy_reduction_of_scale :
    ∀ F : PrefFamily.{u}, ScaleCoherenceStructure F → EntropyReductionRepresentation F :=
  fun F hscale => EntropyReductionRepresentation_of_scale F hscale

/--
**Entropy Reduction to Cross-Prior Bridge**

Given the cross-prior block external assumption, provides the bridge from
`EntropyReductionRepresentation` to `CrossPriorBlockRepresentation` by way of
the unscaled paper blockbridge and universal scale.
-/
noncomputable def entropy_reduction_to_cross_prior_of_assumption
    (hcross : FiniteCrossPriorBlockAssumptions.{u}) :
    ∀ F : PrefFamily.{u}, TraceAxioms F →
      EntropyReductionRepresentation F → CrossPriorBlockRepresentation F :=
  fun F hax hentropy => crossPriorBlockRepresentation_of_unscaled hcross F hax hentropy

/-!
## Fable Stage: Selected right-slice coefficient / slope identification

This section discharges the two remaining opaque inputs of the product
representation theorem:

* `ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor` — the
  right-slice intercept `B_{p,r}` identification, and
* `FiniteFaceScaleProductSlopeAffineAssumptionsFor` — the slice-slope affinity
  `α(ν)=A_{p,r}+C_{p,r}y(ν)`.

Both are proved from the single global classical finite affine-utility
uniqueness theorem, A8 same-order, HM public mixtures, and — crucially for the
slope — exact posterior-value relabeling invariance under the product swap
(`Equiv.prodComm`).  This is the Lean form of the paper's coordinate-swap
scalar `d(p,r)` (empowerment_v5(1).tex, Lemma coherentnorm, Step 2).

The slope target is repaired to nondegenerate first coordinate
(`¬ Subsingleton A`): in a singleton first coordinate the base value
`V_q(P) = 0` for every channel, so the slice slope is not value-identified and
the paper's Step 2 explicitly restricts to nondegenerate action sets.  The
degenerate first coordinate is handled downstream in
`faceScaleProductPairwiseBilinearity_of_sliceAffine`, where `V_q(P)=0` makes
both slope terms vanish, so no interaction-collapse content is lost.
-/

/-- On a singleton second coordinate, the product experiment `P ⊗ R` induces the
same posterior law as `P ⊗ U_B`: the singleton `B`-coordinate carries no
information. Mirror of `samePosteriorLawExp_prodChannel_singleton_fst`. -/
theorem samePosteriorLawExp_prodChannel_singleton_snd
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B)
    (P : Channel A O) (R : Channel B Y) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (prodChannel P R))
      (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU B))) := by
  obtain ⟨b₀⟩ : Nonempty B := inferInstance
  have huniq : ∀ b : B, b = b₀ := fun b => Subsingleton.elim b b₀
  have hr_eq : r b₀ = 1 := by
    have hsum := r.sum_eq_one
    rw [show (∑ b : B, r b) = r b₀ from
      Finset.sum_eq_single b₀ (fun b _ hb => absurd (huniq b) hb)
        (fun h => absurd (Finset.mem_univ b₀) h)] at hsum
    exact hsum
  have hU_val : ∀ (u : PUnit.{u+1}),
      (Channel.uninformativeChannelU B b₀ : Dist PUnit.{u+1}) u = 1 := by
    intro u; cases u; simp [Channel.uninformativeChannelU]
  have hR_sum : (∑ y : Y, (R b₀).prob y) = 1 := (R b₀).sum_eq_one
  intro φ _hcont
  show posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel P R)) φ =
    posteriorLawIntegralExp (prodDist q r) (experimentOfChannel (prodChannel P (Channel.uninformativeChannelU B))) φ
  simp only [posteriorLawIntegralExp, experimentOfChannel, FiniteExperimentOn.ofChannel,
    FiniteExperimentOn.outcomeMarginal, FiniteExperimentOn.posterior]
  have hmarg_factored : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
      (R b₀).prob y * Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) (o, PUnit.unit) := by
    intro o y
    simp only [Channel.outcomeMarginal_apply]
    have hstep_R : ∀ x : A × B, (prodDist q r) x * (prodChannel P R) x (o, y) =
        (R b₀).prob y * (q x.1 * P x.1 o) := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq b, hr_eq, one_mul]; ring
    have hstep_U : ∀ x : A × B, (prodDist q r) x *
        (prodChannel P (Channel.uninformativeChannelU B)) x (o, PUnit.unit) =
        q x.1 * P x.1 o := by
      intro ⟨a, b⟩
      simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq b, hr_eq, one_mul,
        hU_val, mul_one]
    rw [Finset.sum_congr rfl (fun x _ => hstep_R x), ← Finset.mul_sum,
      Finset.sum_congr rfl (fun x _ => hstep_U x)]
  have hpost_when_pos : ∀ (o : O) (y : Y),
      (R b₀).prob y > 0 →
      Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) (o, PUnit.unit) > 0 →
      Channel.posterior (prodChannel P R) (prodDist q r) (o, y) =
        Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) := by
    intro o y hRy hUo
    have hmarg_P_pos : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) > 0 := by
      rw [hmarg_factored o y]; exact mul_pos hRy hUo
    unfold Channel.posterior
    rw [dif_pos hmarg_P_pos, dif_pos hUo]
    ext ⟨a, b⟩
    simp only [prodDist_apply_pair, prodChannel_apply_pair, huniq b, hr_eq, one_mul,
      hU_val, mul_one]
    rw [show Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) =
        (R b₀).prob y * Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) from hmarg_factored o y]
    have hRy_ne : (R b₀).prob y ≠ 0 := ne_of_gt hRy
    have hUo_ne : (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) : Dist (O × PUnit.{u+1})).prob (o, PUnit.unit) ≠ 0 := ne_of_gt hUo
    field_simp
  suffices h : ∀ (o : O) (y : Y),
      Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
      (R b₀).prob y *
        (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit))) by
    have hlhs : (∑ oy : O × Y,
        Channel.outcomeMarginal (prodChannel P R) (prodDist q r) oy *
        φ (Channel.posterior (prodChannel P R) (prodDist q r) oy)) =
      ∑ o : O, Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit)) := by
      rw [Fintype.sum_prod_type]
      simp_rw [h]
      simp_rw [← Finset.sum_mul, hR_sum, one_mul]
    have hrhs : (∑ oy : O × PUnit.{u+1},
        Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) oy *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) oy)) =
      ∑ o : O, Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) *
        φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [Finset.univ_unique]
    exact hlhs.trans hrhs.symm
  intro o y
  rcases eq_or_lt_of_le ((R b₀).nonneg y) with hRy | hRy
  · have hmarg0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
      rw [hmarg_factored o y]; simp [hRy.symm]
    simp only [Channel.outcomeMarginal_apply] at hmarg0
    simp [hmarg0, hRy.symm]
  · have hUo_nn : (0 : ℝ) ≤ Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r) (o, PUnit.unit) :=
      (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
        (prodDist q r)).nonneg (o, PUnit.unit)
    rcases eq_or_lt_of_le hUo_nn with hUo | hUo
    · have hmU0 : Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
          (prodDist q r) (o, PUnit.unit) = 0 := hUo.symm
      have hmP0 : Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) = 0 := by
        rw [hmarg_factored o y, hmU0, mul_zero]
      change Channel.outcomeMarginal (prodChannel P R) (prodDist q r) (o, y) *
          φ (Channel.posterior (prodChannel P R) (prodDist q r) (o, y)) =
        (R b₀).prob y *
          (Channel.outcomeMarginal (prodChannel P (Channel.uninformativeChannelU B))
            (prodDist q r) (o, PUnit.unit) *
          φ (Channel.posterior (prodChannel P (Channel.uninformativeChannelU B))
            (prodDist q r) (o, PUnit.unit)))
      rw [hmP0, hmU0]; ring
    · rw [hmarg_factored o y, hpost_when_pos o y hRy hUo, mul_assoc]

/-- On a singleton second coordinate, the left-slice intercept vanishes:
`P ⊗ R ∼ P ⊗ U_B ∼ U_A ⊗ U_B`, and the latter has a subsingleton outcome, hence
value zero. -/
theorem faceScaleLeftSliceIntercept_eq_zero_of_subsingleton_snd
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (hax : TraceAxioms F)
    {A B Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] [Subsingleton B]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport)
    (R : Channel B Y) :
    hslice.leftSliceIntercept hax q r R = 0 := by
  rw [faceScaleLeftSliceIntercept_eq_noInfo_productLeftSliceValue
    hslice hax q r hq hr R]
  unfold faceScaleProductLeftSliceValue
  -- V_{q⊗r}(U_A ⊗ R) = V_{q⊗r}(U_A ⊗ U_B) = 0 (subsingleton outcome).
  have hsame :=
    samePosteriorLawExp_prodChannel_singleton_snd q r
      (Channel.uninformativeChannelU A) R
  rw [hfaces.branch_result.branch_agg.value_rep.respects_same_posterior_law
    (prodDist q r)
    (experimentOfChannel (prodChannel (Channel.uninformativeChannelU A) R))
    (experimentOfChannel
      (prodChannel (Channel.uninformativeChannelU A)
        (Channel.uninformativeChannelU B)))
    hsame]
  exact V_eq_zero_of_subsingleton_outcome F
    hfaces.branch_result.branch_agg.value_rep
    (prodDist q r) (prodDist_fullSupport q r hq hr)
    (prodChannel (Channel.uninformativeChannelU A)
      (Channel.uninformativeChannelU B))

/-- Face-scale product-swap value equality from coherent value relabeling.

This is the pre-universal analogue of `product_value_swap_eq_of_value_relabeling`,
stated directly against `CoherentRelabelingFaceScalesStructure`. -/
theorem faceScaleProduct_value_swap_eq_of_value_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}} (hax : TraceAxioms F)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
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
    hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
      (Equiv.prodComm A B) (Equiv.prodComm O Y)
      (prodDist q r) (prodChannel P R)
  have hrel' :
      hfaces.branch_result.branch_agg.value_rep.V (prodDist r q)
          (experimentOfChannel (prodChannel R P)) =
        hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel (prodChannel P R)) := by
    simpa [relabelDist_prodComm q r, relabelChannel_prodComm P R] using hrel
  exact hrel'.symm

/-- **Target 1a.** Second-coordinate right-slice intercept identification.

Mirrors `classicalFaceScaleAffineUtilityUniqueness_of_finiteAffineUtility` with
base representative `V_r` and target representative `leftSliceIntercept`.  The
nondegenerate second coordinate uses the single global classical
affine-utility uniqueness theorem; the intercept vanishes at the no-information
channel, so the additive constant is zero.  The singleton second coordinate is
handled by the value-zero collapse: `V_r ≡ 0`, and the supplied same-order
hypothesis forces the intercept constant, equal to its zero value at `U_B`. -/
theorem classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u}) :
    ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor hslice where
  positive_linear_of_same_order_affine_zero := by
    intro hax A B _ _ _ _ _ _ q r hq hr haffine horder hzero
    classical
    have hbaseAff :=
      (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces).base_value_publicMix_affine
    by_cases hB : Subsingleton B
    · -- Degenerate second coordinate: V_r ≡ 0 and the intercept vanishes.
      haveI : Subsingleton B := hB
      refine ⟨1, one_pos, ?_⟩
      intro Y _ _ R
      have hVzero :
          hfaces.branch_result.branch_agg.value_rep.V r
            (experimentOfChannel R) = 0 :=
        branchValue_channel_eq_zero_of_subsingleton F
          hfaces.branch_result.branch_agg.value_rep r hr R
      rw [faceScaleLeftSliceIntercept_eq_zero_of_subsingleton_snd
        hslice hax q r hq hr R, hVzero, mul_zero]
    · -- Nondegenerate second coordinate: classical affine-utility uniqueness.
      obtain ⟨a, b, ha_pos, htransform⟩ :=
        huniq.positive_affine_transform (A := B)
          (fun {Y} [Fintype Y] [DecidableEq Y] R =>
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel R))
          (fun {Y} [Fintype Y] [DecidableEq Y] R =>
            hslice.leftSliceIntercept hax q r R)
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact hbaseAff hax r hr t ht0 ht1 P Q)
          (by
            intro O Z _ _ _ _ t ht0 ht1 P Q
            exact haffine t ht0 ht1 P Q)
          (faceScaleBaseValueNonconstancy_of_A1 hfaces
            |>.base_value_nonconstant hax r hr hB)
          (by
            intro O _ _ P Q
            exact horder P Q)
      have hb : b = 0 := by
        have h0 := htransform (Channel.uninformativeChannelU B)
        have hbase0 :
            hfaces.branch_result.branch_agg.value_rep.V r
              (experimentOfChannel (Channel.uninformativeChannelU B)) = 0 :=
          hfaces.branch_result.branch_agg.value_rep.zero_normalized r hr
        rw [hbase0, mul_zero, zero_add] at h0
        rw [hzero] at h0
        exact h0.symm
      refine ⟨a, ha_pos, ?_⟩
      intro Y _ _ R
      have := htransform R
      rw [hb, add_zero] at this
      exact this

/-- **Target 1b.** Slice-slope affinity in the second-coordinate value.

This is the Lean form of the paper's `α(ν)=A_{p,r}+C_{p,r}y(ν)` (Lemma
coherentnorm, Step 2), proved via the coordinate swap.  For nondegenerate first
coordinate, evaluate the slice-affine identity at full first-coordinate
revelation `id_A`, transport it across `Equiv.prodComm` to the swapped product,
expand the swapped slice, and use intercept positive-linearity on both slices.
Dividing by `H(q) ≠ 0` gives an affine dependence of the slope on `V_r(R)`, with
positive constant coefficient `B_{r,q}`. -/
theorem faceScaleProductSlopeAffine_of_HM_A8_relabeling
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hslice : FiniteFaceScaleProductLeftSliceAffineAssumptionsFor hfaces}
    (hlin :
      FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor hslice) :
    FiniteFaceScaleProductSlopeAffineAssumptionsFor hslice where
  slope_affine_in_second_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA
    classical
    -- H(q) = V_q(id_A) ≠ 0 for nondegenerate first coordinate.
    have hHq :
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠ 0 :=
      faceScale_idChannel_value_ne_zero_of_A1 hfaces hax q hq hA
    -- Intercept positive-linearity at (q,r) and (r,q).
    obtain ⟨Bqr, _hBqr_pos, hBqr⟩ := hlin.intercept_positive_linear hax q r hq hr
    obtain ⟨Brq, hBrq_pos, hBrq⟩ := hlin.intercept_positive_linear hax r q hr hq
    refine ⟨Brq,
      (hslice.leftSliceSlope hax r q (Channel.idChannel : Channel A A) - Bqr) /
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)),
      hBrq_pos, ?_⟩
    intro Y _ _ R
    -- (1) slice-affine at (q,r) with first channel id_A:
    have h1 :=
      hslice.left_slice_affine hax q r hq hr
        (Channel.idChannel : Channel A A) R
    -- (2) swap value equality: V_{q⊗r}(id_A ⊗ R) = V_{r⊗q}(R ⊗ id_A).
    have h2 :=
      faceScaleProduct_value_swap_eq_of_value_relabeling hrelV hax hfaces
        q r (Channel.idChannel : Channel A A) R
    -- (3) slice-affine at (r,q) with first channel R:
    have h3 :=
      hslice.left_slice_affine hax r q hr hq R
        (Channel.idChannel : Channel A A)
    -- Intercept identifications.
    have hIqr := hBqr R
    have hIrq := hBrq (Channel.idChannel : Channel A A)
    -- Master equation: slope(q,r,R) * H(q) = slope(r,q,id_A) * V_r(R)
    --   + B_{r,q} * H(q) - B_{q,r} * V_r(R).
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
      -- hchain : slope(q,r,R)*H(q) + intercept(q,r,R)
      --          = slope(r,q,id_A)*V_r(R) + intercept(r,q,id_A)
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

/-- Fully-closed product representation theorem.

All second-coordinate/slope inputs of `finiteFaceScaleProductRepresentationTheorem_of_HM`
are now discharged internally:

* second-coordinate intercept uniqueness by
  `classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility`
  (HM public mixtures + the single global classical affine-utility theorem);
* slope affinity by `faceScaleProductSlopeAffine_of_HM_A8_relabeling`
  (intercept positive-linearity + exact posterior-value relabeling under the
  product swap).

The remaining inputs are the accepted global classical/relabeling assumptions
(`hhm`, `hrelV`), which are the same inputs already used throughout the product
layer. -/
theorem finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleProductRepresentationTheoremAssumptionsFor hfaces :=
  finiteFaceScaleProductRepresentationTheorem_of_HM_and_coeffExtraction hhm hfaces
    (fun hsingle huniq =>
      classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
        hhm
        (faceScaleProductLeftSliceAffine_of_transform
          (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
            (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
            (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
            (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
            hsingle huniq))
        huniq)
    (fun hsingle huniq =>
      faceScaleProductSlopeAffine_of_HM_A8_relabeling hrelV
        (faceScaleProductInterceptPositiveLinear_of_order_affinity_uniqueness
          (faceScaleProductInterceptSameOrder_of_A8
            (faceScaleProductLeftSliceAffine_of_transform
              (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
                hsingle huniq)))
          (faceScaleProductInterceptPublicMixAffinity_of_HM hhm
            (faceScaleProductLeftSliceAffine_of_transform
              (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
                hsingle huniq)))
          (classicalFaceScaleSecondCoordinateAffineUniqueness_of_finiteAffineUtility
            hhm
            (faceScaleProductLeftSliceAffine_of_transform
              (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
                (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
                (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
                (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
                hsingle huniq))
            huniq)))

/-- **Fable product-closure interaction-collapse constructor.**

This is the reassembled clean constructor after the Fable stage.  Compared with
`InteractionCollapseUniversalScale_of_totalClosure`:

* the product-representation input is discharged internally by
  `finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling`
  (the slope/second-coordinate content is now proved, not assumed);
* the opaque grouping-equation input is replaced by the repaired, faithful
  two-grouping weight equation `hgroup` plus the positive-slice-slope condition
  `hpos` (paper eqs. (E1)/(E2)/POS), from which the full `κ = 0` cancellation is
  proved by `finiteProductGroupingEquation_of_twoGroupingWeightEquation`.

The remaining inputs are the accepted global classical/relabeling assumptions
(`hhm`, `huniq`, `hrelV`), the accepted normalizations, and the two honest paper
product-grouping primitives (`hgroup`, `hpos`). -/
noncomputable def InteractionCollapseUniversalScale_of_fableProductClosure
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hcoordValue : FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hgroup :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_totalClosure
    hfaces
    (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
      hhm hrelV hfaces)
    hsingle huniq hgauge hrelV hinterSingle hcoordValue hcoordScale
    (finiteProductGroupingEquation_of_twoGroupingWeightEquation hgroup hpos)
    hunivSingle hax

/-- **Targeted final interaction-collapse constructor.**

Compared with `InteractionCollapseUniversalScale_of_fableProductClosure`:

* POS (`FiniteProductScaleZPositiveAssumptionsFor`) is NO LONGER an input — it
  is proved (`productScaleZpositive_of_sliceTransform`): `Z(q)` is identified
  with the calibrated slice-transform slope, which is the positive multiplier of
  a positive affine transform;
* the two-grouping evaluations E1/E2 are NO LONGER an input — they are derived
  (`finiteProductTwoGroupingWeightEquation_of_weightRecursion`) from the sharper
  pre-universal weight recursion (W)
  (`FinitePreUniversalGroupingWeightRecursionAssumptionsFor`), which is now the
  exact remaining product-grouping primitive.

Remaining inputs: the global classical assumptions (`hhm`, `huniq`), the global
cardinal relabeling coherence (`hrelV`), the accepted normalizations, and the
weight recursion (W). -/
noncomputable def InteractionCollapseUniversalScale_of_targetedFinalClosure
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hhm : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions.{u})
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    (hsingle : FiniteFaceScaleSingletonSliceAffineAssumptionsFor hfaces)
    (huniq : ClassicalFiniteAffineUtilityUniquenessAssumptions.{u})
    (hgauge :
      FiniteFaceScaleCurrentProductGaugeNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hinterSingle :
      FiniteFaceScaleSingletonInteractionNormalizationFor
        (faceScaleProductPairwiseBilinearity_of_closedLocalTheorems
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).base_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).coordinate_publicMix
          (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).left_slice_same_order
          hsingle huniq
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_same_order hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).intercept_publicMix hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).second_coordinate_uniqueness hsingle huniq)
          ((finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
            hhm hrelV hfaces).slope_affine hsingle huniq)))
    (hcoordValue : FiniteCoordinateSupportFaceValueIdentificationFor hfaces)
    (hcoordScale : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces)
    (hrec :
      ∀ (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces),
        FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod)
    (hunivSingle : FiniteUniversalScaleSingletonNormalizationFor hfaces)
    (hax : TraceAxioms F) :
    InteractionCollapseUniversalChainScaleStructure F :=
  InteractionCollapseUniversalScale_of_totalClosure
    hfaces
    (finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling
      hhm hrelV hfaces)
    hsingle huniq hgauge hrelV hinterSingle hcoordValue hcoordScale
    (finiteProductGroupingEquation_of_weightRecursion hrelV
      (faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems
        (faceScaleBaseValuePublicMixAffinity_of_HM hhm hfaces)
        (faceScaleProductCoordinateMixtureAffinity_of_HM hhm hfaces)
        (faceScaleProductLeftSliceSameOrder_of_A8 hfaces)
        hsingle huniq)
      hrec)
    hunivSingle hax

end TraceableAgency
