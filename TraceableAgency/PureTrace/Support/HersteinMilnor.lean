/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.PosteriorApproximation
import TraceableAgency.PureTrace.Support.Relabeling

/-!
# External Herstein--Milnor Posterior Value Assumptions

This file owns the Herstein--Milnor interface used by the sufficiency spine.
Blackwell-specific posterior-law replacement remains in `TraceableAgency/PureTrace/Support/Blackwell.lean`.
The only external HM premise is the generic affine-utility theorem for abstract
convex mixture spaces.  The posterior-law quotient and the paper-specific
normalized value representation are constructed in Lean below.
-/

namespace TraceableAgency

universe u

open Filter Topology

/-!
## Herstein--Milnor setup

These are external assumptions for the Herstein-Milnor mixture-space theorem,
which establishes that preferences on a mixture space satisfying completeness,
transitivity, independence, and continuity are represented by an affine functional.

Paper reference: Lemma postsep.

The paper uses:
1. PosteriorLawSufficiency to define a quotient comparison on M_q
2. derived public-coin independence for mixture independence
3. A2 (continuity) for closed contour sets
4. Herstein-Milnor to get an affine representative F_q

The final route applies only the generic mixture-space theorem stated below.
The older direct data package retained at the end of this file is a legacy
compatibility interface and is not reachable from `FinalHMInterface` or the
main theorem.
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

/-!
## Preference-free Herstein--Milnor theorem boundary

The external theorem below is stated on an arbitrary convex mixture space.
The coordinates merely give an auditable way to say that points are separated,
that mixtures are convex combinations, and that sequences converge.  No
preference family, experiment, posterior law, or paper-specific construction
occurs in this boundary.
-/

/-- An abstract convex mixture space presented by separating affine
coordinates.  Coordinate injectivity entails the usual mixture identities. -/
structure AbstractConvexMixtureSpace.{v} (X : Type v) where
  Coordinate : Type v
  coordinate : X → Coordinate → ℝ
  coordinate_ext :
    ∀ x y : X, (∀ k, coordinate x k = coordinate y k) → x = y
  mix : Set.Ioo (0 : ℝ) 1 → X → X → X
  coordinate_mix :
    ∀ (t : Set.Ioo (0 : ℝ) 1) (x y : X) (k : Coordinate),
      coordinate (mix t x y) k =
        t.1 * coordinate x k + (1 - t.1) * coordinate y k

theorem AbstractConvexMixtureSpace.mix_self
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (t : Set.Ioo (0 : ℝ) 1) (x : X) :
    M.mix t x x = x := by
  apply M.coordinate_ext
  intro k
  rw [M.coordinate_mix]
  ring

theorem AbstractConvexMixtureSpace.mix_swap
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (t : Set.Ioo (0 : ℝ) 1) (x y : X) :
    M.mix t x y =
      M.mix ⟨1 - t.1, sub_pos.mpr t.2.2, by linarith [t.2.1]⟩ y x := by
  apply M.coordinate_ext
  intro k
  rw [M.coordinate_mix, M.coordinate_mix]
  ring

/-- Pointwise-coordinate convergence on an abstract convex mixture space. -/
def AbstractConvexMixtureSpace.Converges
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (xseq : ℕ → X) (x : X) : Prop :=
  ∀ k, Tendsto (fun n => M.coordinate (xseq n) k) atTop
    (𝓝 (M.coordinate x k))

/-- The standard weak-order, independence, and continuity hypotheses of the
Herstein--Milnor mixture-space theorem. -/
structure ContinuousIndependentWeakOrder
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) : Prop where
  complete : ∀ x y, R x y ∨ R y x
  transitive : ∀ x y z, R x y → R y z → R x z
  independence :
    ∀ (x y z : X) (t : Set.Ioo (0 : ℝ) 1),
      R x y ↔ R (M.mix t x z) (M.mix t y z)
  sequentially_closed :
    ∀ (xseq : ℕ → X) (x : X) (yseq : ℕ → X) (y : X),
      M.Converges xseq x →
      M.Converges yseq y →
      (∀ n, R (xseq n) (yseq n)) →
      R x y

/-- The standard affine-utility conclusion of Herstein--Milnor. -/
structure AffineUtilityRepresentation
    {X : Type u} (M : AbstractConvexMixtureSpace X)
    (R : X → X → Prop) where
  utility : X → ℝ
  represents : ∀ x y, R x y ↔ utility x ≥ utility y
  affine :
    ∀ (t : Set.Ioo (0 : ℝ) 1) (x y : X),
      utility (M.mix t x y) =
        t.1 * utility x + (1 - t.1) * utility y

/-- The classical Herstein--Milnor theorem in generic mixture-space form. -/
structure ClassicalHersteinMilnorMixtureTheoremAssumptions.{v} where
  affine_utility :
    ∀ {X : Type (v + 1)} (M : AbstractConvexMixtureSpace X)
      (R : X → X → Prop),
      ContinuousIndependentWeakOrder M R →
      Nonempty (AffineUtilityRepresentation M R)

/-- The input-side hypotheses needed to apply Herstein--Milnor to the
posterior-law quotient at a fixed full-support prior. -/
structure FinitePosteriorLawHMHypothesesFor
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
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
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
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
  rcases (hax.weakOrder.1 commonP).1 x y with hxy | hyx
  · left
    have hblock :=
      (hax.blockCoherence.finite_block (K := HMTwoBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTwoBlock.left) (j := HMTwoBlock.right) (by decide)
        (qᵢ := q) (qⱼ := q)).mp hxy
    simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
      Act, Out, C] using hblock
  · right
    have hblock :=
      (hax.blockCoherence.finite_block (K := HMTwoBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTwoBlock.right) (j := HMTwoBlock.left) (by decide)
        (qᵢ := q) (qⱼ := q)).mp hyx
    simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
      Act, Out, C] using hblock

/-- Transitivity of the posterior-law HM comparison, proved in a common
three-block environment and transported back with A3. -/
theorem posteriorLawHMRel_transitive_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
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
      (hax.blockCoherence.finite_block (K := HMTripleBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTripleBlock.left) (j := HMTripleBlock.middle) (by decide)
        (qᵢ := q) (qⱼ := q)).mpr (by
          simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
            Act, Out, C] using hEG)
    simpa [commonP, x, y] using hcommon
  have hyz : F.rel commonP y z := by
    have hcommon :=
      (hax.blockCoherence.finite_block (K := HMTripleBlock) (Act := Act) (Out := Out) (P := C)
        (i := HMTripleBlock.middle) (j := HMTripleBlock.right) (by decide)
        (qᵢ := q) (qⱼ := q)).mpr (by
          simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
            Act, Out, C] using hGH)
    simpa [commonP, y, z] using hcommon
  have hxz : F.rel commonP x z := (hax.weakOrder.1 commonP).2 x y z hxy hyz
  have hblock :=
    (hax.blockCoherence.finite_block (K := HMTripleBlock) (Act := Act) (Out := Out) (P := C)
      (i := HMTripleBlock.left) (j := HMTripleBlock.right) (by decide)
      (qᵢ := q) (qⱼ := q)).mp hxz
  simpa [posteriorLawHMRel, ExperimentPairPref, blockExperimentChannel,
    Act, Out, C] using hblock

/-- The reverse lottery comparison in the block with `G` on the left and `E`
on the right.  The bundled definition supplies the experiments' private
outcome-type instances at the boundary. -/
def posteriorLawHMReverseSwappedBlock
    (F : PrefFamily.{u})
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (E G : FiniteExperimentOn A) : Prop :=
  @F.rel (A ⊕ A) (G.OutcomeType ⊕ E.OutcomeType)
    inferInstance inferInstance
    (@instFintypeSum G.OutcomeType E.OutcomeType G.outFintype E.outFintype)
    (@instDecidableEqSum G.OutcomeType E.OutcomeType G.outDecEq E.outDecEq)
    (blockExperimentChannel G E) (inrDist q) (inlDist q)

/-- Reversing the lottery positions in one two-block environment is the same
comparison as swapping the two experiments.  This is the ordered-pair clause
of block coherence, isolated for the strict half of the derived public-coin
argument. -/
theorem posteriorLawHMRel_iff_reverse_swapped_block
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E G : FiniteExperimentOn A) :
    posteriorLawHMRel F q E G ↔
      posteriorLawHMReverseSwappedBlock F q E G := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype G.OutcomeType := G.outFintype
  letI : DecidableEq G.OutcomeType := G.outDecEq
  simpa [posteriorLawHMRel, posteriorLawHMReverseSwappedBlock,
    ExperimentPairPref, blockExperimentChannel] using
      (Relabeling.block_swap_rel_of_axioms F hax G.P E.P q q).symm

/-- Public-coin independence at a full-support prior is derived from
posterior-law substitution and branchwise continuation monotonicity.

This is the paper's `lem:publiccoin`: an uninformative first-stage binary
experiment chooses the informative continuation with probability `t` and a
common continuation with probability `1-t`.  Padding gives the two informative
continuations a common outcome alphabet.  The weak clause of branchwise
monotonicity proves the forward implication; its strict clause proves the
converse by contradiction. -/
theorem posteriorLawHMRel_public_mix_independence_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (E G R : FiniteExperimentOn A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    posteriorLawHMRel F q E G ↔
      posteriorLawHMRel F q
        (hmPublicMixExperiment t ht0 ht1 E R)
        (hmPublicMixExperiment t ht0 ht1 G R) := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype G.OutcomeType := G.outFintype
  letI : DecidableEq G.OutcomeType := G.outDecEq
  letI : Fintype R.OutcomeType := R.outFintype
  letI : DecidableEq R.OutcomeType := R.outDecEq
  let actionSumFintype : Fintype (A ⊕ A) := inferInstance
  let actionSumDecEq : DecidableEq (A ⊕ A) := inferInstance
  letI : Fintype (A ⊕ A) := actionSumFintype
  letI : DecidableEq (A ⊕ A) := actionSumDecEq
  let padFintype : Fintype (E.OutcomeType ⊕ G.OutcomeType) := inferInstance
  let padDecEq : DecidableEq (E.OutcomeType ⊕ G.OutcomeType) := inferInstance
  letI : Fintype (E.OutcomeType ⊕ G.OutcomeType) := padFintype
  letI : DecidableEq (E.OutcomeType ⊕ G.OutcomeType) := padDecEq
  let U : Channel A PUnit.{u+1} := Channel.uninformativeChannelU A
  let C : Channel A (PUnit.{u+1} ⊕ PUnit.{u+1}) :=
    publicMixChannel t ht0 ht1 U U
  let O₂ : PUnit.{u+1} ⊕ PUnit.{u+1} → Type u
    | Sum.inl _ => E.OutcomeType ⊕ G.OutcomeType
    | Sum.inr _ => R.OutcomeType
  let o2Fintype : ∀ c, Fintype (O₂ c)
    | Sum.inl _ => padFintype
    | Sum.inr _ => R.outFintype
  let o2DecEq : ∀ c, DecidableEq (O₂ c)
    | Sum.inl _ => padDecEq
    | Sum.inr _ => R.outDecEq
  letI : ∀ c, Fintype (O₂ c) := o2Fintype
  letI : ∀ c, DecidableEq (O₂ c) := o2DecEq
  let QE : ∀ c, Channel A (O₂ c)
    | Sum.inl _ => outcomePadLeft (Y := G.OutcomeType) E.P
    | Sum.inr _ => R.P
  let QG : ∀ c, Channel A (O₂ c)
    | Sum.inl _ => outcomePadRight (O := E.OutcomeType) G.P
    | Sum.inr _ => R.P
  let compFintype :
      Fintype ((c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c) := inferInstance
  let compDecEq :
      DecidableEq ((c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c) := inferInstance
  letI : Fintype ((c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c) :=
    compFintype
  letI : DecidableEq ((c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c) :=
    compDecEq
  let CE : Channel A ((c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c) :=
    seqComposeDep C O₂ QE
  let CG : Channel A ((c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c) :=
    seqComposeDep C O₂ QG
  let Epad : FiniteExperimentOn A :=
    { OutcomeType := E.OutcomeType ⊕ G.OutcomeType
      outFintype := padFintype
      outDecEq := padDecEq
      channel := outcomePadLeft (Y := G.OutcomeType) E.P }
  let Gpad : FiniteExperimentOn A :=
    { OutcomeType := E.OutcomeType ⊕ G.OutcomeType
      outFintype := padFintype
      outDecEq := padDecEq
      channel := outcomePadRight (O := E.OutcomeType) G.P }
  let Ecomp : FiniteExperimentOn A :=
    { OutcomeType := (c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c
      outFintype := compFintype
      outDecEq := compDecEq
      channel := CE }
  let Gcomp : FiniteExperimentOn A :=
    { OutcomeType := (c : PUnit.{u+1} ⊕ PUnit.{u+1}) × O₂ c
      outFintype := compFintype
      outDecEq := compDecEq
      channel := CG }
  let Emix : FiniteExperimentOn A := hmPublicMixExperiment t ht0 ht1 E R
  let Gmix : FiniteExperimentOn A := hmPublicMixExperiment t ht0 ht1 G R
  have hEpad : SamePosteriorLawExp q E Epad := by
    intro φ _hφ
    change posteriorLawIntegral q E.P φ =
      posteriorLawIntegral q (outcomePadLeft (Y := G.OutcomeType) E.P) φ
    exact (posteriorLawIntegral_outcomePadLeft q E.P φ).symm
  have hGpad : SamePosteriorLawExp q G Gpad := by
    intro φ _hφ
    change posteriorLawIntegral q G.P φ =
      posteriorLawIntegral q (outcomePadRight (O := E.OutcomeType) G.P) φ
    exact (posteriorLawIntegral_outcomePadRight q G.P φ).symm
  have hU_marginal :
      Channel.outcomeMarginal U q default = 1 := by
    simp [U, Channel.outcomeMarginal_apply, Channel.uninformativeChannelU,
      q.sum_eq_one]
  have hU_posterior :
      Channel.posterior U q default = q := by
    ext a
    simp [U, Channel.posterior, Channel.outcomeMarginal_apply,
      Channel.uninformativeChannelU, q.sum_eq_one]
  have hC_left_marginal :
      Channel.outcomeMarginal C q (Sum.inl default) = t := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_outcomeMarginal_publicMixChannel_inl]
    rw [hU_marginal, mul_one]
  have hC_right_marginal :
      Channel.outcomeMarginal C q (Sum.inr default) = 1 - t := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_outcomeMarginal_publicMixChannel_inr]
    rw [hU_marginal, mul_one]
  have hC_left_posterior :
      Channel.posterior C q (Sum.inl default) = q := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_posterior_publicMixChannel_inl, hU_posterior]
  have hC_right_posterior :
      Channel.posterior C q (Sum.inr default) = q := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_posterior_publicMixChannel_inr, hU_posterior]
  have hEcomp : SamePosteriorLawExp q Ecomp Emix := by
    intro φ _hφ
    change posteriorLawIntegral q CE φ =
      posteriorLawIntegral q (publicMixChannel t ht0 ht1 E.P R.P) φ
    rw [posteriorLawIntegral_seqComposeDep_eq_sum,
      hm_posteriorLawIntegral_publicMixChannel]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    rw [hC_left_marginal, hC_right_marginal,
      hC_left_posterior, hC_right_posterior,
      posteriorLawIntegral_outcomePadLeft]
  have hGcomp : SamePosteriorLawExp q Gcomp Gmix := by
    intro φ _hφ
    change posteriorLawIntegral q CG φ =
      posteriorLawIntegral q (publicMixChannel t ht0 ht1 G.P R.P) φ
    rw [posteriorLawIntegral_seqComposeDep_eq_sum,
      hm_posteriorLawIntegral_publicMixChannel]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique]
    rw [hC_left_marginal, hC_right_marginal,
      hC_left_posterior, hC_right_posterior,
      posteriorLawIntegral_outcomePadRight]
  have hpad :
      posteriorLawHMRel F q E G ↔ posteriorLawHMRel F q Epad Gpad :=
    hpls q hq E G Epad Gpad hEpad hGpad
  have hcomp :
      posteriorLawHMRel F q Ecomp Gcomp ↔
        posteriorLawHMRel F q Emix Gmix :=
    hpls q hq Ecomp Gcomp Emix Gmix hEcomp hGcomp
  constructor
  · intro hEG
    have hbranch :
        ∀ c, BranchPositive C q c →
          F.rel (blockChannel (QE c) (QG c))
            (inlDist (branchPosterior C q c))
            (inrDist (branchPosterior C q c)) := by
      intro c _hc
      rcases c with (_ | _)
      · simpa [QE, QG, O₂, Epad, Gpad, hmExperimentOfChannel,
          FiniteExperimentOn.ofChannel, posteriorLawHMRel,
          ExperimentPairPref, blockExperimentChannel, branchPosterior,
          hC_left_posterior] using
          (hpad.mp hEG)
      · have hself := experimentPairPref_self_of_axioms F hax q R
        simpa [QE, QG, O₂, posteriorLawHMRel, ExperimentPairPref,
          blockExperimentChannel, branchPosterior,
          hC_right_posterior] using hself
    have hCECG :=
      hax.branchContinuation.1 O₂ q C QE QG hbranch
    have hCECG' : posteriorLawHMRel F q Ecomp Gcomp := by
      simpa [posteriorLawHMRel, Ecomp, Gcomp, CE, CG,
        hmExperimentOfChannel, FiniteExperimentOn.ofChannel,
        ExperimentPairPref, blockExperimentChannel] using hCECG
    exact hcomp.mp hCECG'
  · intro hmix
    have hCECG : posteriorLawHMRel F q Ecomp Gcomp := hcomp.mpr hmix
    by_contra hnot
    have hGE : posteriorLawHMRel F q G E := by
      rcases posteriorLawHMRel_complete_of_axioms F hax q E G with hEG | hGE
      · exact False.elim (hnot hEG)
      · exact hGE
    have hGpadEpad : posteriorLawHMRel F q Gpad Epad := by
      exact (hpls q hq G E Gpad Epad hGpad hEpad).mp hGE
    have hnotEpadGpad : ¬ posteriorLawHMRel F q Epad Gpad := by
      intro h
      exact hnot (hpad.mpr h)
    have hnotReversePad :
        ¬ posteriorLawHMReverseSwappedBlock F q Epad Gpad := by
      intro hreverse
      exact hnotEpadGpad
        ((posteriorLawHMRel_iff_reverse_swapped_block
          F hax q Epad Gpad).mpr hreverse)
    have hbranch_rev :
        ∀ c, BranchPositive C q c →
          F.rel (blockChannel (QG c) (QE c))
            (inlDist (branchPosterior C q c))
            (inrDist (branchPosterior C q c)) := by
      intro c _hc
      rcases c with (_ | _)
      · simpa [QE, QG, O₂, Epad, Gpad, hmExperimentOfChannel,
          FiniteExperimentOn.ofChannel, posteriorLawHMRel,
          ExperimentPairPref, blockExperimentChannel, branchPosterior,
          hC_left_posterior] using
          hGpadEpad
      · have hself := experimentPairPref_self_of_axioms F hax q R
        simpa [QE, QG, O₂, posteriorLawHMRel, ExperimentPairPref,
          blockExperimentChannel, branchPosterior,
          hC_right_posterior] using hself
    have hleftPositive : BranchPositive C q (Sum.inl default) := by
      change Channel.outcomeMarginal C q (Sum.inl default) > 0
      rw [hC_left_marginal]
      exact ht0
    have hstrictComp :=
      hax.branchContinuation.2 O₂ q C QG QE hbranch_rev
        ⟨Sum.inl default, hleftPositive, by
          constructor
          · simpa [QE, QG, O₂, Epad, Gpad, hmExperimentOfChannel,
              FiniteExperimentOn.ofChannel, posteriorLawHMRel,
              ExperimentPairPref, blockExperimentChannel, branchPosterior,
              hC_left_posterior] using hGpadEpad
          · intro hreverse
            apply hnotReversePad
            simpa [posteriorLawHMReverseSwappedBlock, Epad, Gpad,
              hmExperimentOfChannel, FiniteExperimentOn.ofChannel,
              blockExperimentChannel, QE, QG, O₂, branchPosterior,
              hC_left_posterior] using hreverse⟩
    have hreverseComp :=
      (posteriorLawHMRel_iff_reverse_swapped_block
        F hax q Ecomp Gcomp).mp hCECG
    exact hstrictComp.2 (by
      simpa [posteriorLawHMReverseSwappedBlock, Ecomp, Gcomp, CE, CG,
        hmExperimentOfChannel, FiniteExperimentOn.ofChannel,
        blockExperimentChannel] using hreverseComp)

/-- Primitive closed-graph continuity is stable under taking a block of two
pointwise-convergent fixed-alphabet channel sequences. -/
theorem experimentPairPref_limit_of_channelConverges
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A)
    (Pₙ : ℕ → Channel A O) (P : Channel A O)
    (Qₙ : ℕ → Channel A Y) (Q : Channel A Y)
    (hP : ChannelConverges Pₙ P)
    (hQ : ChannelConverges Qₙ Q)
    (hrel :
      ∀ n,
        ExperimentPairPref F
          (FiniteExperimentOn.ofChannel (Pₙ n))
          (FiniteExperimentOn.ofChannel (Qₙ n)) q q) :
    ExperimentPairPref F
      (FiniteExperimentOn.ofChannel P)
      (FiniteExperimentOn.ofChannel Q) q q := by
  have hblock :
      ChannelConverges
        (fun n => blockChannel (Pₙ n) (Qₙ n))
        (blockChannel P Q) := by
    intro a o
    cases a with
    | inl a =>
        cases o with
        | inl o => simpa using hP a o
        | inr y => exact tendsto_const_nhds
    | inr a =>
        cases o with
        | inl o => exact tendsto_const_nhds
        | inr y => simpa using hQ a y
  have hqLeft :
      DistConverges (fun _ => (inlDist q : Dist (A ⊕ A))) (inlDist q) := by
    intro a
    exact tendsto_const_nhds
  have hqRight :
      DistConverges (fun _ => (inrDist q : Dist (A ⊕ A))) (inrDist q) := by
    intro a
    exact tendsto_const_nhds
  have hclosed :=
    hax.closedGraph
      (fun n => blockChannel (Pₙ n) (Qₙ n))
      (blockChannel P Q)
      (fun _ => inlDist q) (fun _ => inrDist q)
      (inlDist q) (inrDist q)
      hblock hqLeft hqRight
      (by
        intro n
        change
          ExperimentPairPref F
            (FiniteExperimentOn.ofChannel (Pₙ n))
            (FiniteExperimentOn.ofChannel (Qₙ n)) q q
        exact hrel n)
  change
    ExperimentPairPref F
      (FiniteExperimentOn.ofChannel P)
      (FiniteExperimentOn.ofChannel Q) q q at hclosed
  exact hclosed

/-- Posterior-law continuity (`lem:plcont`) derived from the ordinal axioms.

Lean constructs continuous barycentric coordinates by explicit finite
vertex insertion. It turns them into a single fixed-alphabet spread of the
left sequence and merge of the right sequence, proves channel
convergence and the Blackwell order relations, and proves that the limiting
channels have the requested posterior laws. A4 ranks the spread and merge;
A1/A3 give transitivity; primitive A2 closes the fixed-alphabet comparison;
and finite Blackwell replacement substitutes the equal-law limits.

Thus posterior-law continuity is a conclusion, not a field of the final HM
interface. -/
theorem posteriorLawContinuity_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{u})
    (hax : PureTraceConditions F) :
    PosteriorLawContinuity F := by
  intro A _ _ _ q hq Eₙ E Gₙ G hE hG hrel
  let hreplacement : FiniteBlackwellPosteriorAssumptions.{u} :=
    blackwellPosteriorReplacement_of_samePosteriorGarblings hblackwell
  let hpls : PosteriorLawSufficiency F :=
    from_axioms_to_posterior_of_blackwell F hreplacement hax
  let data :=
    finitePosteriorLawFixedSandwich q hq Eₙ E Gₙ G hE hG
  letI : Fintype data.UpperOutcome := data.upperFintype
  letI : DecidableEq data.UpperOutcome := data.upperDecidableEq
  letI : Fintype data.LowerOutcome := data.lowerFintype
  letI : DecidableEq data.LowerOutcome := data.lowerDecidableEq
  have hfixedRel :
      ∀ n,
        ExperimentPairPref F
          (FiniteExperimentOn.ofChannel (data.upperSeq n))
          (FiniteExperimentOn.ofChannel (data.lowerSeq n)) q q := by
    intro n
    have hupper :
        ExperimentPairPref F
          (FiniteExperimentOn.ofChannel (data.upperSeq n))
          (Eₙ n) q q :=
      experimentPairPref_of_postprocess F hax q _ _
        (data.upper_spreads_left n)
    have hlower :
        ExperimentPairPref F
          (Gₙ n)
          (FiniteExperimentOn.ofChannel (data.lowerSeq n)) q q :=
      experimentPairPref_of_postprocess F hax q _ _
        (data.right_spreads_lower n)
    exact
      posteriorLawHMRel_transitive_of_axioms F hax q _ (Gₙ n) _
        (posteriorLawHMRel_transitive_of_axioms F hax q _ (Eₙ n) _
          hupper (hrel n))
        hlower
  have hfixed :
      ExperimentPairPref F
        (FiniteExperimentOn.ofChannel data.upperLimit)
        (FiniteExperimentOn.ofChannel data.lowerLimit) q q :=
    experimentPairPref_limit_of_channelConverges
      F hax q data.upperSeq data.upperLimit
      data.lowerSeq data.lowerLimit
      data.upper_channel_converges
      data.lower_channel_converges hfixedRel
  exact
    (hpls q hq
      (FiniteExperimentOn.ofChannel data.upperLimit)
      (FiniteExperimentOn.ofChannel data.lowerLimit)
      E G data.upper_limit_law data.lower_limit_law).mp hfixed

/-- The A1 local nontriviality witness, transported to the HM experiment
comparison. -/
theorem posteriorLawHMRel_nontrivial_full_revelation_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Nontrivial A]
    (q : Dist A) (hq : q.FullSupport) :
    F.strictRel
      (blockChannel (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannel A))
      (inlDist q) (inrDist q) := by
  exact hax.weakOrder.2 q hq

/-- The Herstein--Milnor input hypotheses for the posterior-law quotient are
proved from `PureTraceConditions` plus posterior-law sufficiency and posterior-law
continuity.

In v6, posterior-law continuity is no longer a clause of Axiom A2; it is the
derived lemma `lem:plcont`, supplied here as the explicit hypothesis `hplc`.
Previously this field was discharged by `hax.closedGraph.2`. -/
theorem finitePosteriorLawHMHypotheses_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
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
    exact posteriorLawHMRel_public_mix_independence_of_axioms
      F hax hpls q hq E G R t ht0 ht1
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
    (hax : PureTraceConditions F)
    (hplc : PosteriorLawContinuity F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    FinitePosteriorLawHMHypothesesFor F hax
      (from_axioms_to_posterior_of_blackwell F hblackwell hax) q hq :=
  finitePosteriorLawHMHypotheses_of_axioms F hax
    (from_axioms_to_posterior_of_blackwell F hblackwell hax) hplc q hq

/-!
## Internal posterior-law mixture-space specialization

We now construct the actual mixture space to which the generic classical
theorem is applied.  Its points are experiments modulo equality of posterior
laws.  Continuous test functions are separating affine coordinates.
-/

/-- Continuous real test functions on the finite probability simplex. -/
def ContinuousPosteriorTest
    (A : Type u) [Fintype A] [DecidableEq A] [Nonempty A] :=
  { φ : Dist A → ℝ // Continuous φ }

/-- Equality of posterior laws as a setoid on finite experiments. -/
def posteriorLawExperimentSetoid
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : Setoid (FiniteExperimentOn A) where
  r := SamePosteriorLawExp q
  iseqv :=
    { refl := by
        intro E φ _hφ
        rfl
      symm := by
        intro E G h φ hφ
        exact (h φ hφ).symm
      trans := by
        intro E G H hEG hGH φ hφ
        exact (hEG φ hφ).trans (hGH φ hφ) }

/-- The mixture space of finitely supported posterior laws attainable at
prior `q`, represented as a quotient of finite experiments. -/
abbrev PosteriorLawMixtureSpace
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :=
  Quotient (posteriorLawExperimentSetoid q)

/-- Posterior-law integration descends to a separating coordinate on the
quotient. -/
noncomputable def posteriorLawMixtureCoordinate
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    PosteriorLawMixtureSpace q → ContinuousPosteriorTest A → ℝ :=
  Quotient.lift
    (fun E φ => posteriorLawIntegralExp q E φ.1)
    (by
      intro E G hsame
      funext φ
      exact hsame φ.1 φ.2)

@[simp] theorem posteriorLawMixtureCoordinate_mk
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A)
    (φ : ContinuousPosteriorTest A) :
    posteriorLawMixtureCoordinate q ⟦E⟧ =
      fun ψ => posteriorLawIntegralExp q E ψ.1 := by
  rfl

theorem posteriorLawMixtureCoordinate_out
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (x : PosteriorLawMixtureSpace q)
    (φ : ContinuousPosteriorTest A) :
    posteriorLawMixtureCoordinate q x φ =
      posteriorLawIntegralExp q x.out φ.1 := by
  change posteriorLawMixtureCoordinate q x φ =
    posteriorLawMixtureCoordinate q ⟦x.out⟧ φ
  rw [Quotient.out_eq x]

/-- Public-coin mixing is compatible with posterior-law equivalence. -/
theorem hmPublicMixExperiment_respects_samePosteriorLaw
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    {E E' R R' : FiniteExperimentOn A}
    (hE : SamePosteriorLawExp q E E')
    (hR : SamePosteriorLawExp q R R') :
    SamePosteriorLawExp q
      (hmPublicMixExperiment t ht0 ht1 E R)
      (hmPublicMixExperiment t ht0 ht1 E' R') := by
  intro φ hφ
  rw [hm_posteriorLawIntegral_publicMixExperiment,
    hm_posteriorLawIntegral_publicMixExperiment,
    hE φ hφ, hR φ hφ]

/-- Convex mixing on the posterior-law quotient. -/
noncomputable def posteriorLawMixture
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (t : Set.Ioo (0 : ℝ) 1) :
    PosteriorLawMixtureSpace q →
      PosteriorLawMixtureSpace q → PosteriorLawMixtureSpace q :=
  Quotient.map₂
    (hmPublicMixExperiment t.1 t.2.1 t.2.2)
    (fun {_ _} hE {_ _} hR =>
      hmPublicMixExperiment_respects_samePosteriorLaw
        q t.1 t.2.1 t.2.2 hE hR)

@[simp] theorem posteriorLawMixture_mk
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (t : Set.Ioo (0 : ℝ) 1)
    (E R : FiniteExperimentOn A) :
    posteriorLawMixture q t ⟦E⟧ ⟦R⟧ =
      ⟦hmPublicMixExperiment t.1 t.2.1 t.2.2 E R⟧ := by
  rfl

/-- The posterior-law quotient, entirely internally, is an abstract convex
mixture space in the sense used by the external theorem. -/
noncomputable def posteriorLawAbstractConvexMixtureSpace
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    AbstractConvexMixtureSpace (PosteriorLawMixtureSpace q) where
  Coordinate := ULift.{u + 1} (ContinuousPosteriorTest A)
  coordinate := fun x φ => posteriorLawMixtureCoordinate q x φ.down
  coordinate_ext := by
    intro x y hxy
    induction x using Quotient.inductionOn with
    | _ E =>
      induction y using Quotient.inductionOn with
      | _ G =>
        apply Quotient.sound
        intro φ hφ
        exact hxy ⟨⟨φ, hφ⟩⟩
  mix := posteriorLawMixture q
  coordinate_mix := by
    intro t x y φ
    induction x using Quotient.inductionOn with
    | _ E =>
      induction y using Quotient.inductionOn with
      | _ R =>
        exact hm_posteriorLawIntegral_publicMixExperiment
          q t.1 t.2.1 t.2.2 E R φ.down.1

/-- The quotient preference relation induced by block comparison. -/
def posteriorLawMixtureRel
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (hhyp : FinitePosteriorLawHMHypothesesFor F hax hpls q hq) :
    PosteriorLawMixtureSpace q → PosteriorLawMixtureSpace q → Prop :=
  fun x y =>
    Quotient.liftOn₂ x y
      (posteriorLawHMRel F q)
      (by
        intro E G E' G' hE hG
        exact propext (hhyp.quotient_well_defined E G E' G' hE hG))

@[simp] theorem posteriorLawMixtureRel_mk
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (hhyp : FinitePosteriorLawHMHypothesesFor F hax hpls q hq)
    (E G : FiniteExperimentOn A) :
    posteriorLawMixtureRel F hax hpls q hq hhyp ⟦E⟧ ⟦G⟧ ↔
      posteriorLawHMRel F q E G := by
  rfl

theorem posteriorLawMixtureRel_out
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (hhyp : FinitePosteriorLawHMHypothesesFor F hax hpls q hq)
    (x y : PosteriorLawMixtureSpace q) :
    posteriorLawMixtureRel F hax hpls q hq hhyp x y ↔
      posteriorLawHMRel F q x.out y.out := by
  change posteriorLawMixtureRel F hax hpls q hq hhyp x y ↔
    posteriorLawMixtureRel F hax hpls q hq hhyp ⟦x.out⟧ ⟦y.out⟧
  rw [Quotient.out_eq x, Quotient.out_eq y]

/-- All hypotheses of the generic Herstein--Milnor theorem are derived for
the posterior-law quotient from the paper's already-proved HM input package. -/
theorem continuousIndependentWeakOrder_posteriorLaw
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (hhyp : FinitePosteriorLawHMHypothesesFor F hax hpls q hq) :
    ContinuousIndependentWeakOrder
      (posteriorLawAbstractConvexMixtureSpace q)
      (posteriorLawMixtureRel F hax hpls q hq hhyp) where
  complete := by
    intro x y
    rcases hhyp.complete x.out y.out with hxy | hyx
    · exact Or.inl ((posteriorLawMixtureRel_out
        F hax hpls q hq hhyp x y).2 hxy)
    · exact Or.inr ((posteriorLawMixtureRel_out
        F hax hpls q hq hhyp y x).2 hyx)
  transitive := by
    intro x y z hxy hyz
    apply (posteriorLawMixtureRel_out
      F hax hpls q hq hhyp x z).2
    exact hhyp.transitive x.out y.out z.out
      ((posteriorLawMixtureRel_out
        F hax hpls q hq hhyp x y).1 hxy)
      ((posteriorLawMixtureRel_out
        F hax hpls q hq hhyp y z).1 hyz)
  independence := by
    intro x y z t
    induction x using Quotient.inductionOn with
    | _ E =>
      induction y using Quotient.inductionOn with
      | _ G =>
        induction z using Quotient.inductionOn with
        | _ R =>
          exact hhyp.public_mix_independence
            E G R t.1 t.2.1 t.2.2
  sequentially_closed := by
    intro xseq x yseq y hx hy hrel
    have hx' :
        PosteriorLawConvergesAtExp q (fun n => (xseq n).out) x.out := by
      intro φ hφ
      have hcoord := hx ⟨⟨φ, hφ⟩⟩
      simpa only [posteriorLawAbstractConvexMixtureSpace,
        posteriorLawMixtureCoordinate_out] using hcoord
    have hy' :
        PosteriorLawConvergesAtExp q (fun n => (yseq n).out) y.out := by
      intro φ hφ
      have hcoord := hy ⟨⟨φ, hφ⟩⟩
      simpa only [posteriorLawAbstractConvexMixtureSpace,
        posteriorLawMixtureCoordinate_out] using hcoord
    apply (posteriorLawMixtureRel_out
      F hax hpls q hq hhyp x y).2
    apply hhyp.closed_upper_contour
      (fun n => (xseq n).out) x.out
      (fun n => (yseq n).out) y.out hx' hy'
    intro n
    exact (posteriorLawMixtureRel_out
      F hax hpls q hq hhyp (xseq n) (yseq n)).1 (hrel n)

/-!
## Internally derived posterior-value conclusion

Lean proves `FinitePosteriorLawHMHypothesesFor`, constructs the quotient
mixture space, and applies the preference-free generic Herstein--Milnor theorem.
The project-specific value conclusion below is therefore derived rather than
assumed.
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
  /-- The selected Herstein--Milnor representative is affine on convex
  mixtures of posterior laws.  This is a property of the selected cardinal
  representative, not of every ordinal transform representing the same order. -/
  V_affine_of_posteriorLawIntegral_mix :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (_ht0 : 0 < t) (_ht1 : t < 1)
      (E_mix E₁ E₂ : FiniteExperimentOn A),
      (∀ φ : Dist A → ℝ, Continuous φ →
        posteriorLawIntegralExp q E_mix φ =
          t * posteriorLawIntegralExp q E₁ φ +
            (1 - t) * posteriorLawIntegralExp q E₂ φ) →
      V q E_mix = t * V q E₁ + (1 - t) * V q E₂
  /-- Normalization at the no-information experiment. -/
  V_zero_normalized :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      V q (uninformativeExperiment A) = 0

/-- The affine utility selected by the generic theorem on one posterior-law
quotient. -/
noncomputable def posteriorLawAffineUtilityRepresentation
    (hhm : ClassicalHersteinMilnorMixtureTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (hhyp : FinitePosteriorLawHMHypothesesFor F hax hpls q hq) :
    AffineUtilityRepresentation
      (posteriorLawAbstractConvexMixtureSpace q)
      (posteriorLawMixtureRel F hax hpls q hq hhyp) :=
  Classical.choice
    (hhm.affine_utility
      (posteriorLawAbstractConvexMixtureSpace q)
      (posteriorLawMixtureRel F hax hpls q hq hhyp)
      (continuousIndependentWeakOrder_posteriorLaw
        F hax hpls q hq hhyp))

/-- Shift the selected affine utility so the no-information posterior law has
value zero.  This normalization is internal and preserves both order and
affinity. -/
noncomputable def normalizedPosteriorLawAffineUtility
    (hhm : ClassicalHersteinMilnorMixtureTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (hhyp : FinitePosteriorLawHMHypothesesFor F hax hpls q hq)
    (x : PosteriorLawMixtureSpace q) : ℝ :=
  let rep :=
    posteriorLawAffineUtilityRepresentation hhm F hax hpls q hq hhyp
  rep.utility x - rep.utility ⟦uninformativeExperiment A⟧

/-- Select the normalized quotient utility at full-support priors.  Its value
away from full support is irrelevant to the classical theorem and is set to
zero; the spine subsequently performs its own proved support completion. -/
noncomputable def genericHMPosteriorValue
    (hhm : ClassicalHersteinMilnorMixtureTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    (hall : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (hq : q.FullSupport),
      FinitePosteriorLawHMHypothesesFor F hax hpls q hq)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) : ℝ := by
  classical
  exact if hq : q.FullSupport then
      normalizedPosteriorLawAffineUtility
        hhm F hax hpls q hq (hall q hq) ⟦E⟧
    else
      0

/-- Derive the entire paper-specific posterior-value conclusion from the
generic mixture-space theorem. -/
noncomputable def finiteHersteinMilnorConclusion_of_generic
    (hhm : ClassicalHersteinMilnorMixtureTheoremAssumptions.{u})
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F)
    (hall : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (hq : q.FullSupport),
      FinitePosteriorLawHMHypothesesFor F hax hpls q hq) :
    FiniteHersteinMilnorConclusionFor F hpls where
  V := genericHMPosteriorValue hhm F hax hpls hall
  V_respects_same_posterior_law := by
    intro A _ _ _ q E E' hsame
    classical
    by_cases hq : q.FullSupport
    · simp only [genericHMPosteriorValue, hq, dite_true]
      exact congrArg
        (normalizedPosteriorLawAffineUtility
          hhm F hax hpls q hq (hall q hq))
        (Quotient.sound hsame)
    · simp [genericHMPosteriorValue, hq]
  V_represents_block_comparisons := by
    intro A _ _ _ q hq E₁ E₂
    classical
    let hhyp := hall q hq
    let rep :=
      posteriorLawAffineUtilityRepresentation hhm F hax hpls q hq hhyp
    have hrep :=
      rep.represents (⟦E₁⟧ : PosteriorLawMixtureSpace q) ⟦E₂⟧
    change posteriorLawHMRel F q E₁ E₂ ↔
      genericHMPosteriorValue hhm F hax hpls hall q E₁ ≥
        genericHMPosteriorValue hhm F hax hpls hall q E₂
    simpa [genericHMPosteriorValue, hq,
      normalizedPosteriorLawAffineUtility, hhyp, rep] using hrep
  V_affine_of_posteriorLawIntegral_mix := by
    intro A _ _ _ q hq t ht0 ht1 E_mix E₁ E₂ hmix
    classical
    let hhyp := hall q hq
    let rep :=
      posteriorLawAffineUtilityRepresentation hhm F hax hpls q hq hhyp
    let ti : Set.Ioo (0 : ℝ) 1 := ⟨t, ht0, ht1⟩
    have hsame :
        SamePosteriorLawExp q E_mix
          (hmPublicMixExperiment t ht0 ht1 E₁ E₂) := by
      intro φ hφ
      exact (hmix φ hφ).trans
        (hm_posteriorLawIntegral_publicMixExperiment
          q t ht0 ht1 E₁ E₂ φ).symm
    have hquot :
        (⟦E_mix⟧ : PosteriorLawMixtureSpace q) =
          (posteriorLawAbstractConvexMixtureSpace q).mix ti ⟦E₁⟧ ⟦E₂⟧ := by
      exact Quotient.sound hsame
    have haff := rep.affine ti
      (⟦E₁⟧ : PosteriorLawMixtureSpace q) ⟦E₂⟧
    change genericHMPosteriorValue hhm F hax hpls hall q E_mix =
      t * genericHMPosteriorValue hhm F hax hpls hall q E₁ +
        (1 - t) * genericHMPosteriorValue hhm F hax hpls hall q E₂
    simp only [genericHMPosteriorValue, hq, dite_true,
      normalizedPosteriorLawAffineUtility]
    rw [hquot, haff]
    ring
  V_zero_normalized := by
    intro A _ _ _ q hq
    simp [genericHMPosteriorValue, hq,
      normalizedPosteriorLawAffineUtility]

/-- Apply the generic HM theorem after the formalized
Blackwell/posterior-law-sufficiency bridge. -/
noncomputable def finiteHersteinMilnorConclusion_of_blackwell_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{u})
    (hhm : ClassicalHersteinMilnorMixtureTheoremAssumptions.{u})
    (hax : PureTraceConditions F) :
    FiniteHersteinMilnorConclusionFor F
      (from_axioms_to_posterior_of_blackwell F
        (blackwellPosteriorReplacement_of_samePosteriorGarblings hblackwell) hax) :=
  finiteHersteinMilnorConclusion_of_generic hhm F hax
    (from_axioms_to_posterior_of_blackwell F
      (blackwellPosteriorReplacement_of_samePosteriorGarblings hblackwell) hax)
    (fun {A} [Fintype A] [DecidableEq A] [Nonempty A] q hq =>
      finitePosteriorLawHMHypotheses_of_blackwell_axioms
        F (blackwellPosteriorReplacement_of_samePosteriorGarblings hblackwell)
          hax (posteriorLawContinuity_of_axioms F hblackwell hax) q hq)

/--
**Legacy direct posterior-value package**

Provides a value functional V on experiments that represents block comparisons
at full-support priors. This packages the application of Herstein-Milnor to
the quotient comparison on posterior-law space M_q.

Paper: Lemma postsep.

**Key proof structure from paper:**
- PosteriorLawSufficiency gives well-defined quotient comparison ≽_q on M_q
- the public-coin lemma derived from A3 and A6 gives mixture independence
- A2 (continuity) gives closed upper/lower contour sets
- Herstein-Milnor gives affine functional F_q representing ≽_q
- The integral representation F_q(μ) = ∫ φ_q(r) dμ(r) follows

This older data-carrying interface is retained for compatibility with legacy
intermediate constructors.  It is not an assumption of the final theorem.
-/
structure FiniteHersteinMilnorAssumptions.{v} where
  /-- Value functional V : (PrefFamily, PosteriorLawSufficiency proof, prior, experiment) → ℝ.
      Paper: F_q(μ_{q,P}) for the posterior law μ_{q,P}. -/
  V :
    ∀ (F : PrefFamily.{v}) (_hax : PureTraceConditions F)
      (_hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → FiniteExperimentOn A → ℝ
  /-- V respects posterior-law equivalence: same posterior law ⟹ same value.
      Paper: F_q depends only on the law μ_{q,P}, not on P. -/
  V_respects_same_posterior_law :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' →
        V F hax hpls q E = V F hax hpls q E'
  /-- V represents block comparisons at full-support priors.
      Paper (postsep): q^0 ≽_{P⊔Q} q^1 ↔ F_q(μ_{q,P}) ≥ F_q(μ_{q,Q}). -/
  V_represents_block_comparisons :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (E₁ E₂ : FiniteExperimentOn A),
      ExperimentPairPref F E₁ E₂ q q ↔
        V F hax hpls q E₁ ≥ V F hax hpls q E₂
  /-- Affinity of the selected cardinal representative.  The quantification is
  over the representative selected by this structure, not over arbitrary
  ordinally equivalent value functions. -/
  V_affine_of_posteriorLawIntegral_mix :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (t : ℝ) (_ht0 : 0 < t) (_ht1 : t < 1)
      (E_mix E₁ E₂ : FiniteExperimentOn A),
      (∀ φ : Dist A → ℝ, Continuous φ →
        posteriorLawIntegralExp q E_mix φ =
          t * posteriorLawIntegralExp q E₁ φ +
            (1 - t) * posteriorLawIntegralExp q E₂ φ) →
      V F hax hpls q E_mix =
        t * V F hax hpls q E₁ + (1 - t) * V F hax hpls q E₂
  /-- V is zero-normalized: V_q(U_A) = 0 (uninformative channel has zero value).
      Paper: F_q(δ_q) = 0.
      The uninformative experiment induces the point-mass δ_q on M_q. -/
  V_zero_normalized :
    ∀ (F : PrefFamily.{v}) (hax : PureTraceConditions F)
      (hpls : PosteriorLawSufficiency F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      V F hax hpls q (uninformativeExperiment A) = 0

end TraceableAgency
