/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import Mathlib
import TraceableAgency.External.Blackwell

/-!
# External Herstein--Milnor Posterior Value Assumptions

This file owns the Herstein--Milnor interface used by the sufficiency spine.
Blackwell-specific posterior-law replacement remains in `External/Blackwell.lean`;
this file starts from `PosteriorLawSufficiency` and packages the value
representation obtained from the posterior-law quotient.

The assumption is intentionally named and data-carrying. It is not a proof of
Herstein--Milnor or of the paper-specific quotient construction.
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
## Herstein-Milnor / Posterior Value Representation Assumptions

These are external assumptions for the Herstein-Milnor mixture-space theorem,
which establishes that preferences on a mixture space satisfying completeness,
transitivity, independence, and continuity are represented by an affine functional.

Paper reference: Lemma postsep (lines 1000-1196).

The paper uses:
1. PosteriorLawSufficiency to define a quotient comparison on M_q
2. A6 (public-coin independence) for mixture independence
3. A2 (continuity) for closed contour sets
4. Herstein-Milnor to get an affine representative F_q

We package this as an external assumption that directly provides the value functional.

**Note**: Unlike `FiniteBlackwellPosteriorAssumptions` which is a pure `Prop`,
`FiniteHersteinMilnorAssumptions` carries data (the value functional V).
It is therefore a `Type`, not a `Prop`.
-/

/-- Package the uninformative channel as an experiment.
    Uses the canonical `Channel.uninformativeChannelU` from Basic/Channel.lean. -/
def uninformativeExperiment (A : Type u) [Fintype A] [DecidableEq A] [Nonempty A] :
    FiniteExperimentOn A :=
  { OutcomeType := PUnit.{u+1}
    outFintype := inferInstance
    outDecEq := inferInstance
    channel := Channel.uninformativeChannelU A }

/-!
## Herstein--Milnor hypotheses proved from the paper axioms

The representation theorem itself remains external below.  The declarations in
this section prove the input side of the theorem for the posterior-law quotient:
the induced comparison is a well-defined continuous mixture-space weak order,
with the public-mixture operation implementing convex combinations of posterior
laws.
-/

/-- Package a channel as a finite experiment.  This local name avoids importing
the later sufficiency spine, where the same construction is also exposed. -/
def hmExperimentOfChannel {A O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) : FiniteExperimentOn A :=
  FiniteExperimentOn.ofChannel P

/-- Public-coin mixture of two finite experiments on the same action space. -/
noncomputable def hmPublicMixExperiment {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : FiniteExperimentOn A) : FiniteExperimentOn A :=
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype R.OutcomeType := R.outFintype
  letI : DecidableEq R.OutcomeType := R.outDecEq
  hmExperimentOfChannel (publicMixChannel t ht0 ht1 E.P R.P)

/-- The posterior-law quotient comparison used as the input relation for
Herstein--Milnor at fixed full-support prior `q`. -/
def posteriorLawHMRel (F : PrefFamily.{u})
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E G : FiniteExperimentOn A) : Prop :=
  ExperimentPairPref F E G q q

/-- Two labels for the common block environment used to prove completeness of
the experiment-pair comparison. -/
inductive HMTwoBlock : Type u
  | left
  | right
  deriving DecidableEq, Fintype

/-- Three labels for the common block environment used to prove transitivity of
the experiment-pair comparison. -/
inductive HMTripleBlock : Type u
  | left
  | middle
  | right
  deriving DecidableEq, Fintype

/-- Left outcome marginal of a public-coin mixture.  This is low-level channel
algebra, duplicated here so the HM input proof does not depend on later entropy
or Faddeev files. -/
theorem hm_outcomeMarginal_publicMixChannel_inl
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
theorem hm_outcomeMarginal_publicMixChannel_inr
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
theorem hm_posterior_publicMixChannel_inl
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (o : O) :
    Channel.posterior (publicMixChannel t ht0 ht1 P Q) q (Sum.inl o) =
      Channel.posterior P q o := by
  ext a
  unfold Channel.posterior
  simp only [hm_outcomeMarginal_publicMixChannel_inl]
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
theorem hm_posterior_publicMixChannel_inr
    {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (P : Channel A O) (Q : Channel A Y) (y : Y) :
    Channel.posterior (publicMixChannel t ht0 ht1 P Q) q (Sum.inr y) =
      Channel.posterior Q q y := by
  ext a
  unfold Channel.posterior
  simp only [hm_outcomeMarginal_publicMixChannel_inr]
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

/-- Public-coin mixtures of implementing channels induce convex mixtures of
posterior laws, stated extensionally through posterior-law integrals. -/
theorem hm_posteriorLawIntegral_publicMixChannel
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
  simp only [hm_outcomeMarginal_publicMixChannel_inl,
    hm_outcomeMarginal_publicMixChannel_inr,
    hm_posterior_publicMixChannel_inl,
    hm_posterior_publicMixChannel_inr]
  rw [Finset.mul_sum, Finset.mul_sum]
  ring_nf

/-- Experiment-level posterior-law convexity for public mixtures. -/
theorem hm_posteriorLawIntegral_publicMixExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : FiniteExperimentOn A)
    (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (hmPublicMixExperiment t ht0 ht1 E R) φ =
      t * posteriorLawIntegralExp q E φ +
        (1 - t) * posteriorLawIntegralExp q R φ := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype R.OutcomeType := R.outFintype
  letI : DecidableEq R.OutcomeType := R.outDecEq
  unfold hmPublicMixExperiment hmExperimentOfChannel FiniteExperimentOn.ofChannel
  change posteriorLawIntegral q (publicMixChannel t ht0 ht1 E.P R.P) φ =
    t * posteriorLawIntegral q E.P φ + (1 - t) * posteriorLawIntegral q R.P φ
  exact hm_posteriorLawIntegral_publicMixChannel q t ht0 ht1 E.P R.P φ

/-- The input-side hypotheses needed to apply Herstein--Milnor to the
posterior-law quotient at a fixed full-support prior. -/
structure FinitePosteriorLawHMHypothesesFor
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) : Prop where
  same_refl :
    ∀ E : FiniteExperimentOn A, SamePosteriorLawExp q E E
  same_symm :
    ∀ E G : FiniteExperimentOn A,
      SamePosteriorLawExp q E G → SamePosteriorLawExp q G E
  same_trans :
    ∀ E G H : FiniteExperimentOn A,
      SamePosteriorLawExp q E G →
      SamePosteriorLawExp q G H →
      SamePosteriorLawExp q E H
  quotient_well_defined :
    ∀ E G E' G' : FiniteExperimentOn A,
      SamePosteriorLawExp q E E' →
      SamePosteriorLawExp q G G' →
      (posteriorLawHMRel F q E G ↔ posteriorLawHMRel F q E' G')
  complete :
    ∀ E G : FiniteExperimentOn A,
      posteriorLawHMRel F q E G ∨ posteriorLawHMRel F q G E
  transitive :
    ∀ E G H : FiniteExperimentOn A,
      posteriorLawHMRel F q E G →
      posteriorLawHMRel F q G H →
      posteriorLawHMRel F q E H
  public_mix_independence :
    ∀ (E G R : FiniteExperimentOn A)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1),
      posteriorLawHMRel F q E G ↔
        posteriorLawHMRel F q
          (hmPublicMixExperiment t ht0 ht1 E R)
          (hmPublicMixExperiment t ht0 ht1 G R)
  public_mix_posterior_law :
    ∀ (E R : FiniteExperimentOn A)
      (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
      (φ : Dist A → ℝ),
      posteriorLawIntegralExp q (hmPublicMixExperiment t ht0 ht1 E R) φ =
        t * posteriorLawIntegralExp q E φ +
          (1 - t) * posteriorLawIntegralExp q R φ
  closed_upper_contour :
    ∀ (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A)
      (Gₙ : ℕ → FiniteExperimentOn A) (G : FiniteExperimentOn A),
      PosteriorLawConvergesAtExp q Eₙ E →
      PosteriorLawConvergesAtExp q Gₙ G →
      (∀ n, posteriorLawHMRel F q (Eₙ n) (Gₙ n)) →
      posteriorLawHMRel F q E G
  nontrivial_full_revelation :
    ∀ [Nontrivial A],
      F.strictRel
        (blockChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannel A))
        (inlDist q) (inrDist q)

/-- Completeness of the posterior-law HM comparison, proved by placing both
experiments in one common block environment and applying A1/A3. -/
theorem posteriorLawHMRel_complete_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E G : FiniteExperimentOn A) :
    posteriorLawHMRel F q E G ∨ posteriorLawHMRel F q G E := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype G.OutcomeType := G.outFintype
  letI : DecidableEq G.OutcomeType := G.outDecEq
  let Act : HMTwoBlock → Type u := fun _ => A
  let Out : HMTwoBlock → Type u
    | HMTwoBlock.left => E.OutcomeType
    | HMTwoBlock.right => G.OutcomeType
  letI : ∀ b, Fintype (Act b) := fun _ => inferInstance
  letI : ∀ b, DecidableEq (Act b) := fun _ => inferInstance
  let outFintype : ∀ b, Fintype (Out b)
    | HMTwoBlock.left => E.outFintype
    | HMTwoBlock.right => G.outFintype
  let outDecEq : ∀ b, DecidableEq (Out b)
    | HMTwoBlock.left => E.outDecEq
    | HMTwoBlock.right => G.outDecEq
  letI : ∀ b, Fintype (Out b) := outFintype
  letI : ∀ b, DecidableEq (Out b) := outDecEq
  let C : ∀ b, Channel (Act b) (Out b)
    | HMTwoBlock.left => E.P
    | HMTwoBlock.right => G.P
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act HMTwoBlock.left q
  let y := blockEmbedDist Act HMTwoBlock.right q
  rcases (hax.a1.1 commonP).1 x y with hxy | hyx
  · left
    have hblock :=
      (hax.a3.2 (K := HMTwoBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTwoBlock.left) (j := HMTwoBlock.right) (by decide)
        (qᵢ := q) (qⱼ := q)).mp hxy
    simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
      Act, Out, C] using hblock
  · right
    have hblock :=
      (hax.a3.2 (K := HMTwoBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTwoBlock.right) (j := HMTwoBlock.left) (by decide)
        (qᵢ := q) (qⱼ := q)).mp hyx
    simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
      Act, Out, C] using hblock

/-- Transitivity of the posterior-law HM comparison, proved in a common
three-block environment and transported back with A3. -/
theorem posteriorLawHMRel_transitive_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E G H : FiniteExperimentOn A) :
    posteriorLawHMRel F q E G →
    posteriorLawHMRel F q G H →
    posteriorLawHMRel F q E H := by
  intro hEG hGH
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype G.OutcomeType := G.outFintype
  letI : DecidableEq G.OutcomeType := G.outDecEq
  letI : Fintype H.OutcomeType := H.outFintype
  letI : DecidableEq H.OutcomeType := H.outDecEq
  let Act : HMTripleBlock → Type u := fun _ => A
  let Out : HMTripleBlock → Type u
    | HMTripleBlock.left => E.OutcomeType
    | HMTripleBlock.middle => G.OutcomeType
    | HMTripleBlock.right => H.OutcomeType
  letI : ∀ k, Fintype (Act k) := fun _ => inferInstance
  letI : ∀ k, DecidableEq (Act k) := fun _ => inferInstance
  let outFintype : ∀ k, Fintype (Out k)
    | HMTripleBlock.left => E.outFintype
    | HMTripleBlock.middle => G.outFintype
    | HMTripleBlock.right => H.outFintype
  let outDecEq : ∀ k, DecidableEq (Out k)
    | HMTripleBlock.left => E.outDecEq
    | HMTripleBlock.middle => G.outDecEq
    | HMTripleBlock.right => H.outDecEq
  letI : ∀ k, Fintype (Out k) := outFintype
  letI : ∀ k, DecidableEq (Out k) := outDecEq
  let C : ∀ k, Channel (Act k) (Out k)
    | HMTripleBlock.left => E.P
    | HMTripleBlock.middle => G.P
    | HMTripleBlock.right => H.P
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act HMTripleBlock.left q
  let y := blockEmbedDist Act HMTripleBlock.middle q
  let z := blockEmbedDist Act HMTripleBlock.right q
  have hxy : F.rel commonP x y := by
    have hcommon :=
      (hax.a3.2 (K := HMTripleBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTripleBlock.left) (j := HMTripleBlock.middle) (by decide)
        (qᵢ := q) (qⱼ := q)).mpr (by
          simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
            Act, Out, C] using hEG)
    simpa [commonP, x, y] using hcommon
  have hyz : F.rel commonP y z := by
    have hcommon :=
      (hax.a3.2 (K := HMTripleBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTripleBlock.middle) (j := HMTripleBlock.right) (by decide)
        (qᵢ := q) (qⱼ := q)).mpr (by
          simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
            Act, Out, C] using hGH)
    simpa [commonP, y, z] using hcommon
  have hxz : F.rel commonP x z := (hax.a1.1 commonP).2 x y z hxy hyz
  have hblock :=
    (hax.a3.2 (K := HMTripleBlock) (Act := Act) (Out := Out) (P := C)
      (i := HMTripleBlock.left) (j := HMTripleBlock.right) (by decide)
      (qᵢ := q) (qⱼ := q)).mp hxz
  simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
    Act, Out, C] using hblock

/-- Public-coin independence for the posterior-law HM comparison is exactly A6,
lifted from channels to finite experiments. -/
theorem posteriorLawHMRel_public_mix_independence_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E G R : FiniteExperimentOn A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    posteriorLawHMRel F q E G ↔
      posteriorLawHMRel F q
        (hmPublicMixExperiment t ht0 ht1 E R)
        (hmPublicMixExperiment t ht0 ht1 G R) := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype G.OutcomeType := G.outFintype
  letI : DecidableEq G.OutcomeType := G.outDecEq
  letI : Fintype R.OutcomeType := R.outFintype
  letI : DecidableEq R.OutcomeType := R.outDecEq
  unfold posteriorLawHMRel ExperimentPairPref blockExperimentChannel
    hmPublicMixExperiment hmExperimentOfChannel FiniteExperimentOn.ofChannel
  change
    (F.rel (blockChannel E.P G.P) (inlDist q) (inrDist q) ↔
      F.rel
        (blockChannel (publicMixChannel t ht0 ht1 E.P R.P)
          (publicMixChannel t ht0 ht1 G.P R.P))
        (inlDist q) (inrDist q))
  exact hax.a6 q E.P G.P R.P t ht0 ht1

/-- The A1 local nontriviality witness, transported to the HM experiment
comparison. -/
theorem posteriorLawHMRel_nontrivial_full_revelation_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    (q : Dist A) (hq : q.FullSupport) :
    F.strictRel
      (blockChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannel A))
      (inlDist q) (inrDist q) := by
  exact hax.a1.2 q hq

/-- The Herstein--Milnor input hypotheses for the posterior-law quotient are
proved from `TraceAxioms` plus posterior-law sufficiency and posterior-law
continuity.

In v6, posterior-law continuity is no longer a clause of Axiom A2; it is the
derived lemma `lem:plcont`, supplied here as the explicit hypothesis `hplc`.
Previously this field was discharged by `hax.a2.2`. -/
theorem finitePosteriorLawHMHypotheses_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    (hpls : PosteriorLawSufficiency F)
    (hplc : PosteriorLawContinuity F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    FinitePosteriorLawHMHypothesesFor F hax hpls q hq where
  same_refl := by
    intro E φ _hφ
    rfl
  same_symm := by
    intro E G h φ hφ
    exact (h φ hφ).symm
  same_trans := by
    intro E G H hEG hGH φ hφ
    exact (hEG φ hφ).trans (hGH φ hφ)
  quotient_well_defined := by
    intro E G E' G' hE hG
    exact hpls q hq E G E' G' hE hG
  complete := by
    intro E G
    exact posteriorLawHMRel_complete_of_axioms F hax q E G
  transitive := by
    intro E G H hEG hGH
    exact posteriorLawHMRel_transitive_of_axioms F hax q E G H hEG hGH
  public_mix_independence := by
    intro E G R t ht0 ht1
    exact posteriorLawHMRel_public_mix_independence_of_axioms F hax q E G R t ht0 ht1
  public_mix_posterior_law := by
    intro E R t ht0 ht1 φ
    exact hm_posteriorLawIntegral_publicMixExperiment q t ht0 ht1 E R φ
  closed_upper_contour := by
    intro Eₙ E Gₙ G hE hG hrel
    exact hplc q hq Eₙ E Gₙ G hE hG hrel
  nontrivial_full_revelation := by
    intro _hnt
    exact posteriorLawHMRel_nontrivial_full_revelation_of_axioms F hax q hq

/-- Version using the existing finite Blackwell bridge to produce
posterior-law sufficiency from the axioms. -/
theorem finitePosteriorLawHMHypotheses_of_blackwell_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hax : TraceAxioms F)
    (hplc : PosteriorLawContinuity F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    FinitePosteriorLawHMHypothesesFor F hax
      (from_axioms_to_posterior_of_blackwell F hblackwell hax) q hq :=
  finitePosteriorLawHMHypotheses_of_axioms F hax
    (from_axioms_to_posterior_of_blackwell F hblackwell hax) hplc q hq

/-!
## Theorem-shaped external Herstein--Milnor interface

This is the cleaner audit boundary: Lean proves the input package
`FinitePosteriorLawHMHypothesesFor`; the classical Herstein--Milnor theorem is
then assumed as an implication from those hypotheses to the value
representation conclusion.
-/

/-- The posterior-value conclusion supplied by Herstein--Milnor for a fixed
preference family and posterior-law sufficiency proof. -/
structure FiniteHersteinMilnorConclusionFor
    (F : PrefFamily.{u}) (hpls : PosteriorLawSufficiency F) where
  /-- Value functional V : prior and finite experiment ↦ real value. -/
  V :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → FiniteExperimentOn A → ℝ
  /-- The value depends only on the induced posterior law. -/
  V_respects_same_posterior_law :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' → V q E = V q E'
  /-- The value represents full-support block comparisons. -/
  V_represents_block_comparisons :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (E₁ E₂ : FiniteExperimentOn A),
      ExperimentPairPref F E₁ E₂ q q ↔ V q E₁ ≥ V q E₂
  /-- Normalization at the no-information experiment. -/
  V_zero_normalized :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      V q (uninformativeExperiment A) = 0

/-- External classical Herstein--Milnor theorem, stated as an implication from
the Lean-proved posterior-law quotient hypotheses to the value conclusion. -/
structure ClassicalFiniteHersteinMilnorTheoremAssumptions.{v} where
  posterior_value_conclusion :
    ∀ (F : PrefFamily.{v}) (hax : TraceAxioms F)
      (hpls : PosteriorLawSufficiency F),
      (∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A) (hq : q.FullSupport),
        FinitePosteriorLawHMHypothesesFor F hax hpls q hq) →
      FiniteHersteinMilnorConclusionFor F hpls

/-- Apply the theorem-shaped HM assumption after the already-formalized
Blackwell/posterior-law-sufficiency bridge. -/
noncomputable def finiteHersteinMilnorConclusion_of_blackwell_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : ClassicalFiniteHersteinMilnorTheoremAssumptions.{u})
    (hax : TraceAxioms F)
    (hplc : PosteriorLawContinuity F) :
    FiniteHersteinMilnorConclusionFor F
      (from_axioms_to_posterior_of_blackwell F hblackwell hax) :=
  hhm.posterior_value_conclusion F hax
    (from_axioms_to_posterior_of_blackwell F hblackwell hax)
    (fun {A} [Fintype A] [DecidableEq A] [Nonempty A] q hq =>
      finitePosteriorLawHMHypotheses_of_blackwell_axioms
        F hblackwell hax hplc q hq)

/--
**Herstein-Milnor Posterior Value Assumptions**

Provides a value functional V on experiments that represents block comparisons
at full-support priors. This packages the application of Herstein-Milnor to
the quotient comparison on posterior-law space M_q.

Paper: Lemma postsep (lines 1000-1196).

**Key proof structure from paper:**
- PosteriorLawSufficiency gives well-defined quotient comparison ≽_q on M_q
- A6 (public-coin independence) gives mixture independence
- A2 (continuity) gives closed upper/lower contour sets
- Herstein-Milnor gives affine functional F_q representing ≽_q
- The integral representation F_q(μ) = ∫ φ_q(r) dμ(r) follows

We state the value functional directly as the external assumption.
This is a data-carrying structure (not Prop) because it provides V.
-/
structure FiniteHersteinMilnorAssumptions.{v} where
  /-- Value functional V : (PrefFamily, PosteriorLawSufficiency proof, prior, experiment) → ℝ.
      Paper: F_q(μ_{q,P}) for the posterior law μ_{q,P}. -/
  V :
    ∀ (F : PrefFamily.{v}) (_hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → FiniteExperimentOn A → ℝ
  /-- V respects posterior-law equivalence: same posterior law ⟹ same value.
      Paper: F_q depends only on the law μ_{q,P}, not on P. -/
  V_respects_same_posterior_law :
    ∀ (F : PrefFamily.{v}) (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' → V F hpls q E = V F hpls q E'
  /-- V represents block comparisons at full-support priors.
      Paper (postsep): q^0 ≽_{P⊔Q} q^1 ↔ F_q(μ_{q,P}) ≥ F_q(μ_{q,Q}). -/
  V_represents_block_comparisons :
    ∀ (F : PrefFamily.{v}) (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (E₁ E₂ : FiniteExperimentOn A),
      ExperimentPairPref F E₁ E₂ q q ↔ V F hpls q E₁ ≥ V F hpls q E₂
  /-- V is zero-normalized: V_q(U_A) = 0 (uninformative channel has zero value).
      Paper (line 1301): F_q(δ_q) = 0.
      The uninformative experiment induces the point-mass δ_q on M_q. -/
  V_zero_normalized :
    ∀ (F : PrefFamily.{v}) (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      V F hpls q (uninformativeExperiment A) = 0

end TraceableAgency
