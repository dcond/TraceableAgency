/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.NormalizedValue

namespace TraceableAgency

universe u

/-!
## Entropy Reduction External Assumption

The entropy reduction theorem states that given scale coherence with universal scale:

1. **Entropy reduction formula**: V̂_q(μ_{q,P}) = H(q) - Σ m(o) H(r_o)

   Paper proof sketch:
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

end TraceableAgency
