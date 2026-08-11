/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Behaviour.Representation
import TraceableAgency.PureTrace.Statement
import TraceableAgency.Basic.SupportRestriction
import TraceableAgency.PureTrace.Support.Blackwell
import TraceableAgency.PureTrace.Support.HersteinMilnor

/-!
# Sufficiency Proof Spine

This file defines the historical abstract interfaces for the sufficiency
direction `PureTraceConditions F → PureTraceMIRepresentation F`.  They remain available for compatibility
and for stating intermediate concepts, but the public theorem no longer uses
the old assumption-bundle assembly below.

The closed paper-faithful route is implemented in the neighbouring modules:

1. `Posterior` and `Affine` descend preferences to the fixed-prior
   posterior-law quotient and apply primitive A2 only to the closed segments
   required by Herstein--Milnor.
2. `ProductGauge` selects the canonical relabelling/support-compatible
   representative and derives product quasi-additivity and its positive slice
   factors.
3. `Branch` derives branch aggregation, its tangent cocycle, and the normalized
   chain rule directly from that selected value.
4. `FaceCoherence` proves the nested-face cardinal cocycle and performs the
   scale-only cardinal alignment; `Scales` compares product and sequential
   scales and collapses the interaction coefficient.
5. `EntropyReduction` applies the resulting grouping recursion and the proved
   finite Faddeev theorem; `Final` assembles `PureTraceMIRepresentation F`.

In particular, that public dependency chain does not construct a
posterior-separable integrand and does not use the global posterior-law
continuity or `FinalHMInterface` compatibility route.  This fact is checked
transitively by `TraceableAgency.Theorem1.PaperFaithfulDependencyAudit`.

## What This File Provides

1. Core sufficiency propositions (interfaces for each proof stage)
2. `SufficiencyMIPackage`: the final package strong enough to imply PureTraceMIRepresentation
3. `MIRep_of_SufficiencyMIPackage`: collapse from α·MI to MI representation
4. `SufficiencySpineAssumptions`: bridges between stages
5. `SufficiencyStatement_of_spine`: assembly theorem
6. Connection to main theorem spine
-/

namespace TraceableAgency

universe u

/-!
## Auxiliary Definitions for Posterior Laws

These support the sufficiency propositions with meaningful posterior-law concepts.
-/

/-- The posterior-law integral for an experiment at prior q:
    ∫ φ(r) dμ_{q,E}(r) = Σ_o m(o) * φ(r_o).
    This uses the existing FiniteExperimentOn structure. -/
noncomputable def posteriorLawIntegralExp' {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (φ : Dist A → ℝ) : ℝ :=
  posteriorLawIntegralExp q E φ

/-- The posterior-law integral as a specific functional for channels:
    ∫ φ(r) dμ_{q,P}(r) = Σ_o m(o) * φ(r_o).
    This captures the induced posterior law's integration behavior. -/
noncomputable def posteriorLawIntegral' {A O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) (φ : Dist A → ℝ) : ℝ :=
  ∑ o, (Channel.outcomeMarginal P q) o * φ (Channel.posterior P q o)

/-- Two channels induce the same posterior law at q iff they give the same
    posterior-law integral for all bounded continuous φ. -/
def SamePosteriorLaw {A O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (P : Channel A O) (Q : Channel A Y) : Prop :=
  ∀ φ : Dist A → ℝ, Continuous φ →
    posteriorLawIntegral' q P φ = posteriorLawIntegral' q Q φ

/-!
## Auxiliary: Experiment from Channel

Packages a channel into a FiniteExperimentOn structure for use in value functionals.
-/

/-- Package a channel as a finite experiment.
    This allows value functionals V : Dist A → FiniteExperimentOn A → ℝ
    to be evaluated on channels. -/
def experimentOfChannel {A O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) : FiniteExperimentOn A :=
  FiniteExperimentOn.ofChannel P

/-- Alias for the canonical uninformative channel from Basic/Channel.lean.
    Uses `Channel.uninformativeChannelU` which has outcome type PUnit.{u+1}. -/
abbrev uninformativeChannelU := @Channel.uninformativeChannelU

/-!
## Stage 1: Posterior-Law Sufficiency

Paper Lemmas blockcoh--blackwell, plsuff.

At a full-support prior, experiments with the same posterior law are ranked identically.
This is the key reduction that makes the comparison depend only on the induced
distribution of beliefs, not on the specific channel structure.

Note: `PosteriorLawSufficiency` is defined in TraceableAgency/PureTrace/Support/Blackwell.lean along with
`from_axioms_to_posterior_of_blackwell` which proves it from `FiniteBlackwellPosteriorAssumptions`.
-/

/-!
## Stage 2: Posterior-Separable Representation

Paper Lemma postsep.

There exists a value functional V that:
1. Depends only on the posterior law (respects SamePosteriorLawExp)
2. Represents the block-comparison preference
3. Will eventually be shown to be affine (via Herstein--Milnor)
-/

/-- A convex identity between finite posterior laws descends to the positive
support face.  The proof compares the proposed mixture with the concrete
public-coin mixture, uses finite posterior-law extensionality under support
restriction, and then invokes the explicit public-mixture calculation on the
restricted experiments. -/
theorem posteriorLawIntegralMix_restrictToSupport
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E_mix E₁ E₂ : FiniteExperimentOn A)
    (hmix : ∀ φ : Dist A → ℝ, Continuous φ →
      posteriorLawIntegralExp q E_mix φ =
        t * posteriorLawIntegralExp q E₁ φ +
          (1 - t) * posteriorLawIntegralExp q E₂ φ) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    ∀ ψ : Dist (supportSubtype q) → ℝ, Continuous ψ →
      posteriorLawIntegralExp q.restrictToSupport
          (E_mix.restrictToSupport q) ψ =
        t * posteriorLawIntegralExp q.restrictToSupport
            (E₁.restrictToSupport q) ψ +
          (1 - t) * posteriorLawIntegralExp q.restrictToSupport
            (E₂.restrictToSupport q) ψ := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  have hsame :
      SamePosteriorLawExp q E_mix
        (hmPublicMixExperiment t ht0 ht1 E₁ E₂) := by
    intro φ hφ
    exact (hmix φ hφ).trans
      (hm_posteriorLawIntegral_publicMixExperiment
        q t ht0 ht1 E₁ E₂ φ).symm
  have hrestricted :=
    samePosteriorLawExp_restrictToSupport q E_mix
      (hmPublicMixExperiment t ht0 ht1 E₁ E₂) hsame
  intro ψ hψ
  have hEq := hrestricted ψ hψ
  have hpublic :
      (hmPublicMixExperiment t ht0 ht1 E₁ E₂).restrictToSupport q =
        hmPublicMixExperiment t ht0 ht1
          (E₁.restrictToSupport q) (E₂.restrictToSupport q) := by
    rfl
  rw [hpublic,
    hm_posteriorLawIntegral_publicMixExperiment
      q.restrictToSupport t ht0 ht1
        (E₁.restrictToSupport q) (E₂.restrictToSupport q) ψ] at hEq
  exact hEq

/--
**Posterior Value Representation (explicit)**

A real-valued functional V on experiments, carried explicitly (not existentially).
This allows later stages to reference the same V.

Paper: "There is a continuous affine functional F_q : M_q → ℝ such that
μ ≽_q ν ↔ F_q(μ) ≥ F_q(ν)"
-/
structure PosteriorValueRepresentation (F : PrefFamily.{u}) where
  /-- The value functional V : (prior, experiment) → ℝ -/
  V : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → FiniteExperimentOn A → ℝ
  /-- V respects posterior-law equivalence: same posterior law ⟹ same value -/
  respects_same_posterior_law :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' → V q E = V q E'
  /-- V represents block comparisons at full-support priors -/
  represents_block_comparisons :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (E₁ E₂ : FiniteExperimentOn A),
      ExperimentPairPref F E₁ E₂ q q ↔ V q E₁ ≥ V q E₂
  /-- Affinity of this selected cardinal representative on convex mixtures of
  posterior laws.  An arbitrary strictly increasing transform is therefore not
  another `PosteriorValueRepresentation`; this records the cardinal content
  supplied by Herstein--Milnor. -/
  affine_of_posteriorLawIntegral_mix :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A)
      (t : ℝ) (_ht0 : 0 < t) (_ht1 : t < 1)
      (E_mix E₁ E₂ : FiniteExperimentOn A),
      (∀ φ : Dist A → ℝ, Continuous φ →
        posteriorLawIntegralExp q E_mix φ =
          t * posteriorLawIntegralExp q E₁ φ +
            (1 - t) * posteriorLawIntegralExp q E₂ φ) →
      V q E_mix = t * V q E₁ + (1 - t) * V q E₂
  /-- V is zero-normalized: V_q(δ_q) = 0 (no-information value is zero).
      Paper: F_q(δ_q) = 0.
      The no-information experiment is the uninformative channel U_A. -/
  zero_normalized :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      V q (experimentOfChannel (uninformativeChannelU A)) = 0

/-- Complete a full-support-selected value at a boundary prior by evaluating
the same experiment on the prior's positive support face.  This is a
definition, not a cross-face normalization assumption. -/
noncomputable def supportCompletedPosteriorValue
    (Vraw :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → FiniteExperimentOn A → ℝ)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) : ℝ := by
  classical
  exact if hq : q.FullSupport then
    Vraw q E
  else
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    Vraw q.restrictToSupport (E.restrictToSupport q)

/--
**Posterior-Separable Representation** (Prop version)

Existence statement: there exists a PosteriorValueRepresentation.
-/
def PosteriorSeparableRepresentation (F : PrefFamily.{u}) : Prop :=
  Nonempty (PosteriorValueRepresentation F)

/--
**From Posterior-Law Sufficiency to Value Representation via Herstein-Milnor**

This is the second bridge in the sufficiency spine.
Paper: Lemma postsep.

The proof uses the external Herstein-Milnor assumption to construct
a PosteriorValueRepresentation from PosteriorLawSufficiency.
-/
noncomputable def posteriorValueRep_of_HersteinMilnor
    (F : PrefFamily.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hax : PureTraceConditions F)
    (hpls : PosteriorLawSufficiency F) :
    PosteriorValueRepresentation F where
  V := supportCompletedPosteriorValue (hhm.V F hax hpls)
  respects_same_posterior_law := by
    intro A _ _ _ q E E' hsame
    classical
    by_cases hq : q.FullSupport
    · simp only [supportCompletedPosteriorValue, hq, if_pos]
      exact hhm.V_respects_same_posterior_law
        F hax hpls q E E' hsame
    · letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      have hrsame :=
        samePosteriorLawExp_restrictToSupport q E E' hsame
      simp only [supportCompletedPosteriorValue, hq, if_neg]
      exact hhm.V_respects_same_posterior_law
        F hax hpls q.restrictToSupport
          (E.restrictToSupport q) (E'.restrictToSupport q) hrsame
  represents_block_comparisons := fun {A} [_] [_] [_] q hq E₁ E₂ =>
    by
      simpa [supportCompletedPosteriorValue, hq] using
        hhm.V_represents_block_comparisons F hax hpls q hq E₁ E₂
  affine_of_posteriorLawIntegral_mix :=
    by
      intro A _ _ _ q t ht0 ht1 E_mix E₁ E₂ hmix
      classical
      by_cases hq : q.FullSupport
      · simpa [supportCompletedPosteriorValue, hq] using
          hhm.V_affine_of_posteriorLawIntegral_mix
            F hax hpls q hq t ht0 ht1 E_mix E₁ E₂ hmix
      · letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
        have hmixSupport :=
          posteriorLawIntegralMix_restrictToSupport
            q t ht0 ht1 E_mix E₁ E₂ hmix
        simpa [supportCompletedPosteriorValue, hq] using
          hhm.V_affine_of_posteriorLawIntegral_mix
            F hax hpls q.restrictToSupport
              (Dist.restrictToSupport_fullSupport q)
              t ht0 ht1
              (E_mix.restrictToSupport q)
              (E₁.restrictToSupport q)
              (E₂.restrictToSupport q)
              hmixSupport
  zero_normalized := fun {A} [_] [_] [_] q hq => by
    have h := hhm.V_zero_normalized F hax hpls q hq
    have heq : experimentOfChannel (uninformativeChannelU A) = uninformativeExperiment A := by
      simp only [experimentOfChannel, uninformativeChannelU, uninformativeExperiment,
                 Channel.uninformativeChannelU, FiniteExperimentOn.ofChannel]
    rw [show supportCompletedPosteriorValue (hhm.V F hax hpls) q
        (experimentOfChannel (uninformativeChannelU A)) =
          hhm.V F hax hpls q
            (experimentOfChannel (uninformativeChannelU A)) by
      simp [supportCompletedPosteriorValue, hq]]
    rw [heq]
    exact h

/-- Convert the theorem-shaped Herstein--Milnor conclusion into the spine's
posterior value representation. -/
noncomputable def posteriorValueRep_of_HersteinMilnorConclusion
    (F : PrefFamily.{u})
    (hpls : PosteriorLawSufficiency F)
    (hhm : FiniteHersteinMilnorConclusionFor F hpls) :
    PosteriorValueRepresentation F where
  V := supportCompletedPosteriorValue hhm.V
  respects_same_posterior_law := by
    intro A _ _ _ q E E' hsame
    classical
    by_cases hq : q.FullSupport
    · simp only [supportCompletedPosteriorValue, hq, if_pos]
      exact hhm.V_respects_same_posterior_law q E E' hsame
    · letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      have hrsame :=
        samePosteriorLawExp_restrictToSupport q E E' hsame
      simp only [supportCompletedPosteriorValue, hq, if_neg]
      exact hhm.V_respects_same_posterior_law
        q.restrictToSupport
          (E.restrictToSupport q) (E'.restrictToSupport q) hrsame
  represents_block_comparisons := fun {A} [_] [_] [_] q hq E₁ E₂ =>
    by
      simpa [supportCompletedPosteriorValue, hq] using
        hhm.V_represents_block_comparisons q hq E₁ E₂
  affine_of_posteriorLawIntegral_mix :=
    by
      intro A _ _ _ q t ht0 ht1 E_mix E₁ E₂ hmix
      classical
      by_cases hq : q.FullSupport
      · simpa [supportCompletedPosteriorValue, hq] using
          hhm.V_affine_of_posteriorLawIntegral_mix
            q hq t ht0 ht1 E_mix E₁ E₂ hmix
      · letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
        have hmixSupport :=
          posteriorLawIntegralMix_restrictToSupport
            q t ht0 ht1 E_mix E₁ E₂ hmix
        simpa [supportCompletedPosteriorValue, hq] using
          hhm.V_affine_of_posteriorLawIntegral_mix
            q.restrictToSupport
              (Dist.restrictToSupport_fullSupport q)
              t ht0 ht1
              (E_mix.restrictToSupport q)
              (E₁.restrictToSupport q)
              (E₂.restrictToSupport q)
              hmixSupport
  zero_normalized := fun {A} [_] [_] [_] q hq => by
    have h := hhm.V_zero_normalized q hq
    have heq : experimentOfChannel (uninformativeChannelU A) = uninformativeExperiment A := by
      simp only [experimentOfChannel, uninformativeExperiment, FiniteExperimentOn.ofChannel]
    rw [show supportCompletedPosteriorValue hhm.V q
        (experimentOfChannel (uninformativeChannelU A)) =
          hhm.V q (experimentOfChannel (uninformativeChannelU A)) by
      simp [supportCompletedPosteriorValue, hq]]
    rw [heq]
    exact h

/-- From the paper axioms to a posterior value representation using the cleaner
theorem-shaped Herstein--Milnor interface: Lean proves the HM hypotheses, then
the external HM theorem supplies the value conclusion.  The Blackwell argument
is a compatibility parameter here; the final route supplies the internally
proved `finiteSamePosteriorLawBlackwellEquivalence`. -/
noncomputable def posteriorValueRep_of_axioms_HMTheorem
    (F : PrefFamily.{u})
    (hblackwell : FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{u})
    (hhm : ClassicalHersteinMilnorMixtureTheoremAssumptions.{u})
    (hax : PureTraceConditions F) :
    PosteriorValueRepresentation F :=
  posteriorValueRep_of_HersteinMilnorConclusion F
    (from_axioms_to_posterior_of_blackwell F
      (blackwellPosteriorReplacement_of_samePosteriorGarblings hblackwell) hax)
    (finiteHersteinMilnorConclusion_of_blackwell_axioms
      F hblackwell hhm hax)

/--
**Legacy From-Axioms-to-Value Combined Bridge**

Retains the older packaged Blackwell-replacement and direct HM interfaces.
The public final route instead constructs Blackwell replacement internally
and uses the generic HM theorem.

Paper: Lemmas blockcoh--blackwell + postsep.
-/
noncomputable def posteriorValueRep_of_axioms
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hhm : FiniteHersteinMilnorAssumptions.{u})
    (hax : PureTraceConditions F) :
    PosteriorValueRepresentation F :=
  posteriorValueRep_of_HersteinMilnor F hhm
    hax
    (from_axioms_to_posterior_of_blackwell F hblackwell hax)

/-!
## Stage 3: Branch Aggregation Structure

Paper Lemma branchagg.

From branchwise monotonicity (A6), we derive that the value of a sequential
experiment is an aggregation of branch values with positive coefficients.
-/

/--
**Branch Aggregation Structure**

The value functional decomposes into branch contributions with positive
coefficients β(q, r) depending only on prior and reached posterior.

Paper: "There are positive branch coefficients β(q, r_o), depending only on q
and the reached posterior r_o, such that for every continuation profile {Q^o},
F_q(μ_{q,P₁▷{Q^o}}) = F_q(μ_{q,P₁}) + Σ_o m(o) β(q,r_o) F_{r_o}(μ_{r_o,Q^o})"
-/
structure BranchAggregationStructure (F : PrefFamily.{u}) where
  /-- The underlying value representation -/
  value_rep : PosteriorValueRepresentation F
  /-- Branch coefficient β(q, r) depending on prior q and reached posterior r.
      Paper notation: β(q, r_o) -/
  branchCoeff :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → Dist A → ℝ
  /-- Branch coefficients are positive for nondegenerate posteriors.
      Paper: "positive branch coefficients" -/
  branchCoeff_pos :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A) (_hq : q.FullSupport) (_hr : ∃ a b : A, a ≠ b ∧ 0 < r a ∧ 0 < r b),
      0 < branchCoeff q r
  /-- Branch aggregation formula (uniform continuation outcome type version).
      Paper: F_q(μ_{q,P₁▷{Q^o}}) = F_q(μ_{q,P₁}) + Σ_o m(o) β(q,r_o) F_{r_o}(μ_{r_o,Q^o})
      Note: We sum over all outcomes; zero-probability branches contribute zero. -/
  branch_aggregation :
    ∀ {A O₁ O₂ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁] [Fintype O₂] [DecidableEq O₂]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (Q : O₁ → Channel A O₂),
      value_rep.V q (experimentOfChannel (P₁ ▷ Q)) =
      value_rep.V q (experimentOfChannel P₁) +
      ∑ o₁ : O₁,
        (Channel.outcomeMarginal P₁ q) o₁ *
        branchCoeff q (Channel.posterior P₁ q o₁) *
        value_rep.V (Channel.posterior P₁ q o₁) (experimentOfChannel (Q o₁))

/-!
## Stage 4: Scale Coherence Structure

Paper Lemmas chain--scalecoherence.

The branch-coefficient cocycle β(q,r) = a_q/a_r collapses to a universal scale.
-/

/--
**Scale Coherence Structure**

The branch coefficients satisfy a cocycle property β(q,r) = a_q/a_r,
and a two-grouping argument shows a_q is actually universal (independent of q).

Paper: "β(q,r) β(r,s) = β(q,s) ...
Hence β(q,r) = a_q/a_r for positive scales a_q"

Paper: "Lemma scalecoherence uses the chain rule and a two-grouping
argument to eliminate the interaction term and prove the scale a_q is universal."
-/
structure ScaleCoherenceStructure (F : PrefFamily.{u}) where
  /-- Branch aggregation structure (prerequisite). -/
  branch_agg : BranchAggregationStructure F
  /-- The prior-dependent scale function a_q.
      Paper: a_q := 1/β(q_0,q) -/
  scale :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → ℝ
  /-- Scale is positive at full-support priors.
      Paper: "positive scales a_q" -/
  scale_pos :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      0 < scale q
  /-- Branch coefficients factor as β(q,r) = a_q/a_r (cocycle property).
      Paper: β(q,r) = a_q/a_r -/
  branchCoeff_factorization :
    ∀ {A O₁ : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O₁] [DecidableEq O₁]
      (q : Dist A) (_hq : q.FullSupport)
      (P₁ : Channel A O₁) (o₁ : O₁),
      BranchPositive P₁ q o₁ →
      branch_agg.branchCoeff q (Channel.posterior P₁ q o₁) =
        scale q / scale (Channel.posterior P₁ q o₁)
  /-- Universal scale: a_q = a is independent of q.
      Paper: "prove the scale a_q is universal" -/
  scale_universal :
    ∀ {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport),
      scale q = scale r

/-!
## Stage 5: Entropy Reduction Representation

Paper Lemma faddeevsketch first part.

With universal scale a, define entropy H(q) as the rescaled full-revelation value.
Then every channel value reduces to an entropy-difference formula.
-/

/--
**Entropy Reduction Representation**

With universal scale, the value functional takes the entropy-reduction form:
V̂_q(μ_{q,P}) = H(q) - Σ_o m(o) H(r_o)

where V̂ = V/a is the rescaled value functional.

Paper: "F̂_q(μ_{q,P}) = H(q) - Σ_{o:m(o)>0} m(o) H(r_o)"
-/
structure EntropyReductionRepresentation (F : PrefFamily.{u}) where
  /-- Scale coherence (prerequisite). -/
  scale_coherence : ScaleCoherenceStructure F
  /-- The entropy function H(q) = V̂_q(χ_q) where χ_q is full revelation.
      Paper: H(q) := F_q(χ_q) -/
  Hfun :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
      Dist A → ℝ
  /-- The value functional satisfies the entropy-reduction formula.
      Paper: V̂_q(μ_{q,P}) = H(q) - Σ_o m(o) H(r_o).
      Using posteriorLawIntegral: V̂_q(E) = H(q) - ∫ H(r) dμ_{q,E}(r) -/
  value_entropy_reduction :
    ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (q : Dist A) (_hq : q.FullSupport) (P : Channel A O),
      scale_coherence.branch_agg.value_rep.V q (experimentOfChannel P) /
        scale_coherence.scale q =
      Hfun q - posteriorLawIntegral q P Hfun

/-!
## Stage 5b: Cross-Prior Block Representation

Paper Lemma blockbridge, reused after scale coherence in
Lemma faddeevsketch.

This is deliberately separate from entropy reduction. The paper proves
blockbridge before entropy reduction, then observes that universal scale lets it
be read in the normalized value units.
-/

/--
**Cross-Prior Block Representation (scaled)**

The normalized value functional represents block comparisons across possibly
different priors and action alphabets.
-/
structure CrossPriorBlockRepresentation (F : PrefFamily.{u}) where
  /-- Entropy reduction representation whose normalized value is used below. -/
  entropy_reduction : EntropyReductionRepresentation F
  /-- Cross-prior block representation (scaled).
      Paper Lemma blockbridge + scale coherence:
      q^0 ≽_{P⊔Q} r^1 ↔ V̂(q,P) ≥ V̂(r,Q)
      where V̂ = V/a is the rescaled (normalized) value functional.
      This is the key bridge that enables cross-prior comparisons. -/
  cross_prior_block_rep :
    ∀ {A B O Y : Type u}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O]
      [Fintype Y] [DecidableEq Y]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (P : Channel A O) (Q : Channel B Y),
      F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
        entropy_reduction.scale_coherence.branch_agg.value_rep.V q (experimentOfChannel P) /
          entropy_reduction.scale_coherence.scale q ≥
        entropy_reduction.scale_coherence.branch_agg.value_rep.V r (experimentOfChannel Q) /
          entropy_reduction.scale_coherence.scale r

/-!
## Stage 6: Faddeev Entropy Form

Paper Lemma faddeevsketch Faddeev part.

The function H satisfies Faddeev's recursion, hence H = α·Shannon for some α ≥ 0.
-/

/--
**Faddeev Entropy Form**

The entropy function H satisfies Faddeev's recursion and therefore
equals α · Shannon entropy for some α ≥ 0.

Paper: "H(q) = α Sh(q) for some α ≥ 0"
-/
structure FaddeevEntropyForm (F : PrefFamily.{u}) where
  /-- Cross-prior block representation, carrying the prerequisite entropy-reduction
      representation separately from the entropy-reduction theorem itself. -/
  cross_prior : CrossPriorBlockRepresentation F
  /-- The positive scale α from Faddeev's theorem.
      Paper: α ≥ 0, and α > 0 follows from local non-triviality. -/
  alpha : ℝ
  /-- α is positive (from local non-triviality: ∃ q with H(q) > 0). -/
  alpha_pos : 0 < alpha
  /-- H = α · Shannon entropy.
      Paper: "Faddeev's theorem therefore gives H(q) = α Sh(q)" -/
  H_eq_alpha_shannon :
    ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A),
      cross_prior.entropy_reduction.Hfun q = alpha * H(q)
  /-- A3 duplicate-block equivalence.
      Paper Axiom A3 first clause:
        q ≽_P q' ↔ q^0 ≽_{P⊔P} (q')^1
      This is carried from PureTraceConditions and is needed for the global-sketch proof. -/
  a3_block_equivalence :
    ∀ {A O : Type u} [Fintype A] [DecidableEq A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q q' : Dist A),
      F.rel P q q' ↔ F.rel (blockChannel P P) (inlDist q) (inrDist q')

/-!
## Final Sufficiency Packages

We define two packages:
1. `SufficiencyMIPackage`: the full package matching `PureTraceMIRepresentation` (no Nonempty restriction)
2. `FullSupportSufficiencyMIPackage`: restricted to full-support priors (provable from Faddeev)

The paper's proof works first on full-support priors. Extending to boundary priors
requires support restriction / face continuity arguments.
-/

/--
**Final Sufficiency Package**

The end result of the sufficiency proof: a positive scale α such that
F.rel P q q' ↔ α·I(q,P) ≥ α·I(q',P).

Since α > 0, this is equivalent to I(q,P) ≥ I(q',P), i.e., PureTraceMIRepresentation F.

Note: This quantifies over all finite A (including empty), matching PureTraceMIRepresentation.
-/
def SufficiencyMIPackage (F : PrefFamily.{u}) : Prop :=
  ∃ (alpha : ℝ), 0 < alpha ∧
    ∀ {A O : Type u} [Fintype A] [DecidableEq A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q q' : Dist A),
      F.rel P q q' ↔ alpha * mutualInfo q P ≥ alpha * mutualInfo q' P

/--
**Full-Support Sufficiency Package**

The MI representation restricted to full-support priors.
This is what the paper's globalsketch lemma proves directly.

Paper: Lemma globalsketch works with full-support priors.
Extension to boundary priors uses support restriction / face continuity.
-/
def FullSupportSufficiencyMIPackage (F : PrefFamily.{u}) : Prop :=
  ∃ (alpha : ℝ), 0 < alpha ∧
    ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype O] [DecidableEq O]
      (P : Channel A O) (q q' : Dist A),
      q.FullSupport → q'.FullSupport →
      (F.rel P q q' ↔ alpha * mutualInfo q P ≥ alpha * mutualInfo q' P)

/--
**Full-Support Block MI Package**

The MI representation for block-supported cross-prior comparisons whose two
branches may have different action and outcome alphabets.

This is the support-face block comparison needed by boundary extension when
the two boundary priors have different positive supports.
-/
def FullSupportBlockMI (F : PrefFamily.{u}) : Prop :=
  ∃ (alpha : ℝ), 0 < alpha ∧
    ∀ {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
      (P : Channel A O) (Q : Channel B Y) (q : Dist A) (r : Dist B),
      q.FullSupport →
      r.FullSupport →
      (F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
        alpha * mutualInfo q P ≥ alpha * mutualInfo r Q)

/--
**Boundary Extension**

Extends full-support MI representation to arbitrary priors.
This corresponds to the paper's Lemma supprestrict (support restriction).

**Paper method (Lemma supprestrict):**
For boundary prior r with support B ⊂ A:
1. The posterior law μ_{r,P} depends only on rows P(·|b) for b ∈ B
2. Channels agreeing on B are indifferent at prior r
3. F.rel comparison at r equals comparison at restricted prior r|_B on face B
4. This uses A5 (neutrality under stochastic maps) for the projection/embedding

**Proof of representation extension:**
If q or q' is on the boundary, restrict each pair (q,P) and (q',P) to their
positive-probability supports, apply the full-support theorem on each restricted
alphabet, and pull back. Deleting zero-probability actions preserves MI.

This legacy proposition interface is retained for compatibility. The public
proof uses the checked support-restriction construction directly and does not
depend on this declaration.
-/
def FullSupportMIRepExtendsToBoundary (F : PrefFamily.{u}) : Prop :=
  PureTraceConditions F → FullSupportSufficiencyMIPackage F → SufficiencyMIPackage F

/--
**Collapse Lemma**: SufficiencyMIPackage implies PureTraceMIRepresentation.

This is pure arithmetic using alpha_pos.
-/
theorem MIRep_of_SufficiencyMIPackage
    (F : PrefFamily.{u})
    (hpkg : SufficiencyMIPackage F) :
    PureTraceMIRepresentation F := by
  obtain ⟨alpha, hα_pos, hrep⟩ := hpkg
  intro A O instFA instDA instFO instDO P q q'
  have h : F.rel P q q' ↔ alpha * mutualInfo q P ≥ alpha * mutualInfo q' P :=
    hrep P q q'
  rw [h]
  constructor
  · intro hge
    nlinarith
  · intro hge
    nlinarith

/--
**Full-Support Faddeev-to-MI Bridge**: FaddeevEntropyForm implies FullSupportSufficiencyMIPackage.

This is the non-tautological proof of the final bridge for full-support priors.
The proof combines:
1. a3_block_equivalence: F.rel P q q' ↔ F.rel (blockChannel P P) (inlDist q) (inrDist q')
2. cross_prior_block_rep: block comparison ↔ normalized value comparison
3. value_entropy_reduction: V̂(q,P) = Hfun(q) - posteriorLawIntegral q P Hfun
4. H_eq_alpha_shannon: Hfun(q) = α · H(q)
5. mutualInfo_eq_entropy_sub_posteriorLawIntegral: I(q,P) = H(q) - posteriorLawIntegral q P entropy

Paper: Lemma globalsketch.
-/
private theorem fullSupportMI_rep_aux
    (F : PrefFamily.{u})
    (hfad : FaddeevEntropyForm F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A)
    (hq : q.FullSupport) (hq' : q'.FullSupport) :
    F.rel P q q' ↔ hfad.alpha * mutualInfo q P ≥ hfad.alpha * mutualInfo q' P := by
  rw [hfad.a3_block_equivalence P q q']
  rw [hfad.cross_prior.cross_prior_block_rep q q' hq hq' P P]
  have h_val_q := hfad.cross_prior.entropy_reduction.value_entropy_reduction q hq P
  have h_val_q' := hfad.cross_prior.entropy_reduction.value_entropy_reduction q' hq' P
  have h_Hfun_eq : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A] (r : Dist A),
      hfad.cross_prior.entropy_reduction.Hfun r = hfad.alpha * H(r) := hfad.H_eq_alpha_shannon
  have h_lin : ∀ r : Dist A, posteriorLawIntegral r P hfad.cross_prior.entropy_reduction.Hfun =
      hfad.alpha * posteriorLawIntegral r P entropy := fun r => by
    unfold posteriorLawIntegral
    simp only [h_Hfun_eq]
    rw [Finset.mul_sum]
    congr 1; ext o; ring
  have h_mi_q := mutualInfo_eq_entropy_sub_posteriorLawIntegral q P
  have h_mi_q' := mutualInfo_eq_entropy_sub_posteriorLawIntegral q' P
  rw [h_val_q, h_val_q', h_Hfun_eq, h_Hfun_eq, h_lin, h_lin, h_mi_q, h_mi_q']
  constructor <;> intro h <;> linarith

theorem FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm
    (F : PrefFamily.{u})
    (hfad : FaddeevEntropyForm F) :
    FullSupportSufficiencyMIPackage F :=
  ⟨hfad.alpha, hfad.alpha_pos, @fullSupportMI_rep_aux F hfad⟩

/--
**Full-Support Block MI from Faddeev Form**

This is the cross-support analogue of `FullSupportSufficiencyMIPackage`.
It is derived from the existing cross-prior block representation and Faddeev
entropy form; it is not a boundary-specific external assumption.
-/
private theorem fullSupportBlockMI_rep_aux
    (F : PrefFamily.{u})
    (hfad : FaddeevEntropyForm F)
    {A B O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (P : Channel A O) (Q : Channel B Y) (q : Dist A) (r : Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport) :
    F.rel (blockChannel P Q) (inlDist q) (inrDist r) ↔
      hfad.alpha * mutualInfo q P ≥ hfad.alpha * mutualInfo r Q := by
  rw [hfad.cross_prior.cross_prior_block_rep q r hq hr P Q]
  have h_val_q := hfad.cross_prior.entropy_reduction.value_entropy_reduction q hq P
  have h_val_r := hfad.cross_prior.entropy_reduction.value_entropy_reduction r hr Q
  have h_Hfun_eq : ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      (s : Dist A),
      hfad.cross_prior.entropy_reduction.Hfun s = hfad.alpha * H(s) := hfad.H_eq_alpha_shannon
  have h_lin_q : posteriorLawIntegral q P hfad.cross_prior.entropy_reduction.Hfun =
      hfad.alpha * posteriorLawIntegral q P entropy := by
    unfold posteriorLawIntegral
    simp only [h_Hfun_eq]
    rw [Finset.mul_sum]
    congr 1
    ext o
    ring
  have h_lin_r : posteriorLawIntegral r Q hfad.cross_prior.entropy_reduction.Hfun =
      hfad.alpha * posteriorLawIntegral r Q entropy := by
    unfold posteriorLawIntegral
    simp only [h_Hfun_eq]
    rw [Finset.mul_sum]
    congr 1
    ext y
    ring
  have h_mi_q := mutualInfo_eq_entropy_sub_posteriorLawIntegral q P
  have h_mi_r := mutualInfo_eq_entropy_sub_posteriorLawIntegral r Q
  rw [h_val_q, h_val_r, h_Hfun_eq, h_Hfun_eq, h_lin_q, h_lin_r, h_mi_q, h_mi_r]
  constructor <;> intro h <;> linarith

theorem FullSupportBlockMI_of_FaddeevEntropyForm
    (F : PrefFamily.{u})
    (hfad : FaddeevEntropyForm F) :
    FullSupportBlockMI F :=
  ⟨hfad.alpha, hfad.alpha_pos, @fullSupportBlockMI_rep_aux F hfad⟩

/--
**Combined Final Bridge**: FaddeevEntropyForm plus boundary extension implies SufficiencyMIPackage.

This combines the full-support proof with the boundary extension assumption.
-/
theorem SufficiencyMIPackage_of_FaddeevEntropyForm_and_boundary
    (F : PrefFamily.{u})
    (hfad : FaddeevEntropyForm F)
    (hboundary : FullSupportMIRepExtendsToBoundary F)
    (hax : PureTraceConditions F) :
    SufficiencyMIPackage F :=
  hboundary hax (FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm F hfad)

/-!
## Sufficiency Spine Assumptions

These express that the paper's sufficiency stages yield the final MI package.
Each bridge is an explicit assumption that will be refined/proved in later stages.
-/

/--
**Sufficiency Spine Assumptions**

Bundle of bridge assumptions connecting the sufficiency stages.
Each field is an implication that will be proved in subsequent stages.

Note: The sufficiency stages carry data (value functional V, branch coefficients β,
scale function a, entropy function H, and scale α). The bridges therefore return
data-carrying structures, not bare Props. The final step produces SufficiencyMIPackage
which is Prop (via existential).
-/
structure SufficiencySpineAssumptions where
  /-- Stage 1: Axioms imply posterior-law sufficiency.
      Paper Lemmas blockcoh--blackwell, plsuff. -/
  from_axioms_to_posterior :
    ∀ F : PrefFamily.{u}, PureTraceConditions F → PosteriorLawSufficiency F
  /-- Stage 2: Posterior-law sufficiency implies posterior-separable representation.
      Paper Lemma postsep. Uses Herstein--Milnor.
      Returns a chosen value functional V. -/
  posterior_to_value_rep :
    ∀ F : PrefFamily.{u}, PosteriorLawSufficiency F → PosteriorValueRepresentation F
  /-- Stage 3: Value representation implies branch aggregation.
      Paper Lemma branchagg. Uses A6.
      Returns the same V plus branch coefficients β(q,r). -/
  value_rep_to_branch :
    ∀ F : PrefFamily.{u}, PosteriorValueRepresentation F → BranchAggregationStructure F
  /-- Stage 4: Branch aggregation implies scale coherence.
      Paper Lemmas chain--scalecoherence.
      Returns the same (V, β) plus scale function a_q and cocycle/universality. -/
  branch_to_scale :
    ∀ F : PrefFamily.{u}, BranchAggregationStructure F → ScaleCoherenceStructure F
  /-- Stage 5: Scale coherence implies entropy reduction representation.
      Paper Lemma faddeevsketch first part.
      Returns the same (V, β, a) plus entropy function H. -/
  scale_to_entropy_reduction :
    ∀ F : PrefFamily.{u}, ScaleCoherenceStructure F → EntropyReductionRepresentation F
  /-- Stage 5b: Entropy reduction plus blockbridge gives cross-prior block representation.
      Paper Lemma blockbridge plus universal scale.
      Returns the normalized cross-prior comparison bridge. -/
  entropy_reduction_to_cross_prior :
    ∀ F : PrefFamily.{u}, EntropyReductionRepresentation F → CrossPriorBlockRepresentation F
  /-- Stage 6a: Cross-prior block representation plus Faddeev recursion implies Faddeev form.
      Paper Lemma faddeevsketch Faddeev recursion. Uses Faddeev's theorem.
      Returns the same (V, β, a, H) plus scale α with H = α·Shannon. -/
  entropy_to_faddeev :
    ∀ F : PrefFamily.{u}, CrossPriorBlockRepresentation F → FaddeevEntropyForm F
  /-- Stage 6b: Faddeev form implies full-support MI package.
      Paper Lemma globalsketch (full-support case).
      **PROVED**: See `FullSupportSufficiencyMIPackage_of_FaddeevEntropyForm`. -/
  faddeev_to_full_support_mi_package :
    ∀ F : PrefFamily.{u}, FaddeevEntropyForm F → FullSupportSufficiencyMIPackage F
  /-- Stage 6c: Boundary extension from full-support to arbitrary priors.
      Paper: support restriction / face continuity argument.
      This uses PureTraceConditions (notably support-restriction machinery) and extends
      the full-support result to priors with zero-probability states. -/
  boundary_extension :
    ∀ F : PrefFamily.{u}, FullSupportMIRepExtendsToBoundary F

/-!
## Assembly Theorem
-/

/--
**Sufficiency Assembly**

Given the spine assumptions, derive PureTraceSufficiency.
-/
theorem SufficiencyStatement_of_spine
    (hspine : SufficiencySpineAssumptions.{u}) :
    PureTraceSufficiency.{u} := by
  intro F hax
  apply MIRep_of_SufficiencyMIPackage F
  have h1 : PosteriorLawSufficiency F := hspine.from_axioms_to_posterior F hax
  have h2 : PosteriorValueRepresentation F := hspine.posterior_to_value_rep F h1
  have h3 : BranchAggregationStructure F := hspine.value_rep_to_branch F h2
  have h4 : ScaleCoherenceStructure F := hspine.branch_to_scale F h3
  have h5 : EntropyReductionRepresentation F := hspine.scale_to_entropy_reduction F h4
  have h5b : CrossPriorBlockRepresentation F := hspine.entropy_reduction_to_cross_prior F h5
  have h6 : FaddeevEntropyForm F := hspine.entropy_to_faddeev F h5b
  have h7 : FullSupportSufficiencyMIPackage F := hspine.faddeev_to_full_support_mi_package F h6
  exact hspine.boundary_extension F hax h7

/-!
## Connection to Main Theorem Spine
-/

/--
**Sufficiency and Block Scale from Spine**

Given sufficiency spine assumptions, derive both PureTraceSufficiency
and PureTraceBlockConclusion.

Note: The block scale derivation uses `pureTraceBlocks_of_representation` which
is proved in Main.lean. The connection is via the existing theorem
`pureTraceBlockConclusion_from_sufficiency`.
-/
theorem SufficiencyAndBlockScale_of_spine
    (hspine : SufficiencySpineAssumptions.{u}) :
    PureTraceSufficiency.{u} ∧ PureTraceBlockConclusion.{u} := by
  constructor
  · exact SufficiencyStatement_of_spine hspine
  · exact pureTraceBlockConclusion_from_sufficiency
      (SufficiencyStatement_of_spine hspine) pureTraceBlocksFromRepresentation_proved

/--
**Main Theorem from the sufficiency spine**

Given sufficiency spine assumptions, derive the full main characterisation.
The benchmark direction uses the internally proved finite data-processing
inequalities.
-/
theorem MainCharacterizationWithMoreover_of_spine
    (hspine : SufficiencySpineAssumptions.{u}) :
    PureTraceCharacterizationWithBlocks.{u} := by
  apply pureTraceCharacterization_from_components
  · exact SufficiencyStatement_of_spine hspine
  · exact pureTraceNecessity_of_representation
  · exact (SufficiencyAndBlockScale_of_spine hspine).2

/-!
## External Assumptions Documentation

The sufficiency proof relies on external classical results that are not
proved in this development. These are documented here and will be
bundled in TraceableAgency/PureTrace/Support/ files.
-/

/--
**External Herstein--Milnor Assumption**

The Herstein--Milnor mixture-space theorem (1953) states that a complete,
transitive, continuous preference on a mixture space has an affine
(expected utility) representation.

Used in: Stage 2 (posterior-separable representation).
Reference: Herstein & Milnor, "An Axiomatic Approach to Measurable Utility"
-/
def HersteinMilnorAssumption : Prop :=
  ∀ {X : Type u} [inst : Nonempty X]
    (rel : X → X → Prop)
    (mix : ℝ → X → X → X)
    (_hcomplete : ∀ x y, rel x y ∨ rel y x)
    (_htrans : ∀ x y z, rel x y → rel y z → rel x z)
    (_hcont : ∀ x y z, rel x y → ∃ t : ℝ, 0 < t ∧ t < 1 ∧ rel (mix t z x) y)
    (_hmix : ∀ t x y, mix t x y = mix (1-t) y x),
    ∃ (f : X → ℝ), ∀ x y, rel x y ↔ f x ≥ f y

/--
**External Faddeev Assumption**

Faddeev's theorem (1956) characterises Shannon entropy as the unique
(up to scale) function satisfying certain recursion properties on
finite probability distributions.

Used in: Stage 6a (entropy form).
Reference: Faddeev (1956), Baez--Fritz--Leinster (2011) Theorem 6.

Note: The full statement involves continuity, permutation invariance,
expansibility, and Faddeev's recursion. This documentation-level predicate is
not consumed by the assembled theorem; the active interface is split in
`External.Faddeev` into entropy regularity, Faddeev recursion, classical
Faddeev, and positivity assumptions.
-/
def FaddeevAssumption : Prop :=
  ∀ (H_func : ∀ {A : Type u} [Fintype A] [DecidableEq A], Dist A → ℝ)
    (_hcont : ∀ {A : Type u} [Fintype A] [DecidableEq A],
      Continuous (fun q : Dist A => H_func q))
    (_hpoint :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] (a : A),
        H_func (Dist.pure a) = 0),
    ∃ (α : ℝ), α ≥ 0 ∧ ∀ {A : Type u} [Fintype A] [DecidableEq A] (q : Dist A),
      H_func q = α * H(q)

/--
**Legacy finite Blackwell statement**

This older proposition states one direction of the finite Blackwell theorem.
It is retained for compatibility and is not a public assumption; the stronger
mutual-garbling result is proved in `TraceableAgency/PureTrace/Support/Blackwell.lean`.

Used in: Stage 1 (posterior-law sufficiency).
Reference: Blackwell (1953).
-/
def FiniteBlackwellAssumption : Prop :=
  ∀ {A O Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (_hq : q.FullSupport)
    (P : Channel A O) (Q : Channel A Y),
    SamePosteriorLaw q P Q →
    ∃ (T : Channel O Y), ∀ a o, (Channel.postprocess P T) a o = Q a o

end TraceableAgency
