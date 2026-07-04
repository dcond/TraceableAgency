/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Info.MutualInfo
import TraceableAgency.Basic.Channel
import TraceableAgency.Basic.Convergence
import TraceableAgency.Behaviour.Axioms

/-!
# External Finite Data Processing Inequality Assumptions

This file contains external assumptions for finite information-theoretic
data processing inequalities (DPI). These are standard results in finite
information theory that are not proved in this development.

## Main definitions

* `FiniteDPIAssumptions` - a structure bundling the finite DPI inequalities
  needed to close the benchmark direction (A4 and A5 axioms for MIPrefFamily).

## Status

These assumptions are:
1. Standard finite information-theory results
2. NOT proved in this Lean development
3. Used as explicit, auditable external assumptions
4. No anonymous `axiom` declarations are used

The two inequalities are:
1. **Outcome post-processing DPI**: I(q, P∘T) ≤ I(q, P)
2. **Action Bayes-pushforward DPI**: I(qS, P̂) ≤ I(q, P) when P̂ is a valid completion

## References

* Cover & Thomas, "Elements of Information Theory", Chapter 2
* The data processing inequality is a standard consequence of the chain rule
  and non-negativity of conditional mutual information.
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
## Finite Data Processing Inequality Assumptions

These are the standard finite DPI inequalities needed for the benchmark direction.
-/

/--
External finite information-theoretic assumptions used to close the benchmark
direction (axioms A4 and A5 for MIPrefFamily).

These are standard finite data-processing inequalities for mutual information.
They are NOT proved in this development but are used as explicit external assumptions.

* `outcome_postprocess`: Post-processing outcomes cannot increase mutual information.
  For any channel P : A → Δ(O) and post-processing T : O → Δ(O'), we have
  I(q, P∘T) ≤ I(q, P).

* `action_bayes_pushforward`: Coarsening actions via a valid Bayesian pushforward
  cannot increase mutual information. For action kernel S : A → Δ(A') and
  any valid completion P̂ of the pushforward channel S^q P, we have
  I(qS, P̂) ≤ I(q, P).
-/
structure FiniteDPIAssumptions.{v} : Prop where
  /-- Outcome post-processing DPI: I(q, P∘T) ≤ I(q, P).
      Post-processing the outcomes of a channel cannot increase mutual information.
      This is the standard data processing inequality for outcome garbling. -/
  outcome_postprocess :
    ∀ {A O O' : Type v} [Fintype A] [DecidableEq A]
      [Fintype O] [DecidableEq O] [Fintype O'] [DecidableEq O']
      (q : Dist A) (P : Channel A O) (T : Channel O O'),
      mutualInfo q (Channel.postprocess P T) ≤ mutualInfo q P
  /-- Action Bayes-pushforward DPI: I(qS, P̂) ≤ I(q, P).
      Coarsening actions via Bayesian pushforward cannot increase MI.
      For action kernel S : A → Δ(A'), prior q, channel P : A → Δ(O),
      and any valid completion P̂ : A' → Δ(O) of the pushforward S^q P,
      the mutual information cannot increase. -/
  action_bayes_pushforward :
    ∀ {A A' O : Type v} [Fintype A] [DecidableEq A]
      [Fintype A'] [DecidableEq A'] [Fintype O] [DecidableEq O] [Nonempty A]
      (P : Channel A O) (q : Dist A) (S : Channel.ActionKernel A A')
      (P_hat : Channel A' O),
      Channel.IsBayesPushforwardCompletion P q S P_hat →
      mutualInfo (Channel.actionPushforward q S) P_hat ≤ mutualInfo q P

/-!
## Finite Blackwell / Posterior-Law Sufficiency Assumptions

These are external assumptions for the finite Blackwell equivalence theorem,
which establishes that two channels inducing the same posterior law at a
full-support prior are mutual garblings of each other.

Paper reference: Lemma blackwell (lines 891-961) and Lemma plsuff (lines 963-998).

The paper proves:
1. Same posterior law ⟹ mutual garblings exist: Q = PT and P = QT' for some T, T'
2. Combined with A4 (post-processing aversion): q^0 ≽_{P⊔Q} q^1 and q^0 ≽_{Q⊔P} q^1
3. Combined with A3 (block coherence) and A1 transitivity: same-posterior-law
   experiments may be replaced inside pairwise block comparisons.

The finite Blackwell/garbling equivalence remains a classical finite theorem.
The A4/A3/A1 replacement plumbing is proved below.
-/

/-- Experiment-level postprocessing/garbling relation. -/
def ExperimentPostprocesses {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (E E' : FiniteExperimentOn A) : Prop :=
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype E'.OutcomeType := E'.outFintype
  ∃ T : Channel E.OutcomeType E'.OutcomeType,
    E'.P = Channel.postprocess E.P T

/--
Classical finite Blackwell equivalence at a fixed full-support prior:
same posterior law gives garblings in both directions.

This is the exact finite theorem isolated from paper Lemma `blackwell`.
It does not mention preferences, A3/A4, or block replacement.
-/
structure FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{v} : Prop where
  same_posterior_left_garbling :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' →
      ExperimentPostprocesses E E'
  same_posterior_right_garbling :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport)
      (E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' →
      ExperimentPostprocesses E' E

/--
**Finite Blackwell Posterior-Law Assumptions**

At a full-support prior, two experiments inducing the same posterior law
can be substituted in block comparisons without changing the preference.

This packages:
1. The finite Blackwell equivalence theorem (same posterior ⟹ mutual garblings)
2. Application of A4 (post-processing aversion) to get indifference
3. Use of A3 (finite-block coherence) to transfer indifference across environments
4. Transitivity from A1 to derive the replacement property

Paper: Lemmas blackwell + plsuff + blockcoh (lines 810-998).

**Key proof structure from paper:**
- Blackwell (lem:blackwell): Same posterior law ⟹ Q = PT, P = QT' for garblings T, T'
- A4 gives: q^0 ≽_{P⊔Q} q^1 (using Q = PT)
- A4 + A3 reverse-block gives: q^1 ≽_{P⊔Q} q^0 (using P = QT')
- Combined: q^0 ~_{P⊔Q} q^1
- For replacement: place E, E', G in 3-block environment, use A3 + transitivity

We state the replacement property directly as the external assumption,
and reconstruct it below from the classical finite mutual-garbling interface.
-/
structure FiniteBlackwellPosteriorAssumptions.{v} : Prop where
  /-- Left replacement: same posterior law allows substitution on the left.
      Paper proof: E ~_{E⊔E'} E' by Blackwell+A4, then place in 3-block with G,
      use A3 finite-block coherence and A1 transitivity.
      If E ~ E' (same posterior) then (E ≽ G ↔ E' ≽ G) in block comparisons. -/
  left_replacement :
    ∀ {F : PrefFamily.{v}} {A : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      (hax : TraceAxioms F)
      (q : Dist A) (_hq : q.FullSupport)
      (E E' G : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' →
      (ExperimentPairPref F E G q q ↔ ExperimentPairPref F E' G q q)
  /-- Right replacement: same posterior law allows substitution on the right.
      Paper proof: symmetric to left replacement.
      If E ~ E' (same posterior) then (G ≽ E ↔ G ≽ E') in block comparisons. -/
  right_replacement :
    ∀ {F : PrefFamily.{v}} {A : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      (hax : TraceAxioms F)
      (q : Dist A) (_hq : q.FullSupport)
      (G E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' →
      (ExperimentPairPref F G E q q ↔ ExperimentPairPref F G E' q q)

theorem experimentPairPref_of_postprocess
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    ExperimentPostprocesses E E' →
    ExperimentPairPref F E E' q q := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype E'.OutcomeType := E'.outFintype
  letI : DecidableEq E'.OutcomeType := E'.outDecEq
  rintro ⟨T, hT⟩
  unfold ExperimentPairPref blockExperimentChannel
  rw [hT]
  exact hax.a4 E.P T q

theorem experimentPairPref_self_of_axioms
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) :
    ExperimentPairPref F E E q q := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  have hself : F.rel E.P q q := by
    rcases (hax.a1.1 E.P).1 q q with h | h <;> exact h
  have hblock := (hax.a3.1 E.P q q).mp hself
  simpa [ExperimentPairPref, blockExperimentChannel] using hblock

theorem blackwell_rel_replace_by_equiv
    {α : Type*} (R : α → α → Prop)
    (htrans : ∀ x y z, R x y → R y z → R x z)
    {x x' y y' : α}
    (hxx' : R x x') (hx'x : R x' x)
    (hyy' : R y y') (hy'y : R y' y) :
    (R x y ↔ R x' y') := by
  constructor
  · intro hxy
    exact htrans x' y y' (htrans x' x y hx'x hxy) hyy'
  · intro hx'y'
    exact htrans x y' y (htrans x x' y' hxx' hx'y') hy'y

/-- Four labels for replacing both sides of a two-block comparison in the
Blackwell/posterior-law sufficiency proof. -/
inductive BlackwellPairBlockReplacementBlock : Type u
  | originalLeft
  | replacementLeft
  | originalRight
  | replacementRight
  deriving DecidableEq, Fintype

open BlackwellPairBlockReplacementBlock

def blackwellPairBlockReplacementAct
    (A A' B B' : Type u) : BlackwellPairBlockReplacementBlock → Type u
  | originalLeft => A
  | replacementLeft => A'
  | originalRight => B
  | replacementRight => B'

noncomputable instance blackwellPairBlockReplacementActFintype
    {A A' B B' : Type u} [Fintype A] [Fintype A'] [Fintype B] [Fintype B'] :
    ∀ k : BlackwellPairBlockReplacementBlock,
      Fintype (blackwellPairBlockReplacementAct A A' B B' k)
  | originalLeft => show Fintype A from inferInstance
  | replacementLeft => show Fintype A' from inferInstance
  | originalRight => show Fintype B from inferInstance
  | replacementRight => show Fintype B' from inferInstance

instance blackwellPairBlockReplacementActDecidableEq
    {A A' B B' : Type u} [DecidableEq A] [DecidableEq A'] [DecidableEq B]
    [DecidableEq B'] :
    ∀ k : BlackwellPairBlockReplacementBlock,
      DecidableEq (blackwellPairBlockReplacementAct A A' B B' k)
  | originalLeft => show DecidableEq A from inferInstance
  | replacementLeft => show DecidableEq A' from inferInstance
  | originalRight => show DecidableEq B from inferInstance
  | replacementRight => show DecidableEq B' from inferInstance

def blackwellPairBlockReplacementOut
    (O O' Y Y' : Type u) : BlackwellPairBlockReplacementBlock → Type u
  | originalLeft => O
  | replacementLeft => O'
  | originalRight => Y
  | replacementRight => Y'

noncomputable instance blackwellPairBlockReplacementOutFintype
    {O O' Y Y' : Type u} [Fintype O] [Fintype O'] [Fintype Y] [Fintype Y'] :
    ∀ k : BlackwellPairBlockReplacementBlock,
      Fintype (blackwellPairBlockReplacementOut O O' Y Y' k)
  | originalLeft => show Fintype O from inferInstance
  | replacementLeft => show Fintype O' from inferInstance
  | originalRight => show Fintype Y from inferInstance
  | replacementRight => show Fintype Y' from inferInstance

instance blackwellPairBlockReplacementOutDecidableEq
    {O O' Y Y' : Type u} [DecidableEq O] [DecidableEq O'] [DecidableEq Y]
    [DecidableEq Y'] :
    ∀ k : BlackwellPairBlockReplacementBlock,
      DecidableEq (blackwellPairBlockReplacementOut O O' Y Y' k)
  | originalLeft => show DecidableEq O from inferInstance
  | replacementLeft => show DecidableEq O' from inferInstance
  | originalRight => show DecidableEq Y from inferInstance
  | replacementRight => show DecidableEq Y' from inferInstance

noncomputable def blackwellPairBlockReplacementChannel
    {A A' B B' O O' Y Y' : Type u}
    [Fintype O] [Fintype O'] [Fintype Y] [Fintype Y']
    (P : Channel A O) (P' : Channel A' O')
    (Q : Channel B Y) (Q' : Channel B' Y') :
    ∀ k : BlackwellPairBlockReplacementBlock,
      Channel (blackwellPairBlockReplacementAct A A' B B' k)
        (blackwellPairBlockReplacementOut O O' Y Y' k)
  | originalLeft => show Channel A O from P
  | replacementLeft => show Channel A' O' from P'
  | originalRight => show Channel B Y from Q
  | replacementRight => show Channel B' Y' from Q'

/--
Common-block transfer: if each side of a two-block comparison is weakly
equivalent to a replacement side, then A3 and A1 transitivity preserve the
pairwise comparison.
-/
theorem blackwell_pairwise_block_replacement_from_weak_equiv
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
  let k0 : BlackwellPairBlockReplacementBlock.{u} := originalLeft
  let k1 : BlackwellPairBlockReplacementBlock.{u} := replacementLeft
  let k2 : BlackwellPairBlockReplacementBlock.{u} := originalRight
  let k3 : BlackwellPairBlockReplacementBlock.{u} := replacementRight
  let Act := blackwellPairBlockReplacementAct A A' B B'
  let Out := blackwellPairBlockReplacementOut O O' Y Y'
  let C := blackwellPairBlockReplacementChannel P P' Q Q'
  let commonP := blockFamilyChannel Act Out C
  let x := blockEmbedDist Act k0 q
  let x' := blockEmbedDist Act k1 q'
  let y := blockEmbedDist Act k2 r
  let y' := blockEmbedDist Act k3 r'
  have htrans :
      ∀ a b c : Dist ((k : BlackwellPairBlockReplacementBlock) × Act k),
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
    simpa [commonP, x, y, k0, k2, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using
      (hax.a3.2 (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k0) (j := k2) h02_ne
        (qᵢ := q) (qⱼ := r))
  have hcommon_01 : F.rel commonP x x' := by
    have h :=
      (hax.a3.2 (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k0) (j := k1) h01_ne
        (qᵢ := q) (qⱼ := q')).mpr hleft_to_new
    simpa [commonP, x, x', k0, k1, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using h
  have hcommon_10 : F.rel commonP x' x := by
    have h :=
      (hax.a3.2 (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k1) (j := k0) h10_ne
        (qᵢ := q') (qⱼ := q)).mpr hleft_to_old
    simpa [commonP, x, x', k0, k1, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using h
  have hcommon_23 : F.rel commonP y y' := by
    have h :=
      (hax.a3.2 (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k2) (j := k3) h23_ne
        (qᵢ := r) (qⱼ := r')).mpr hright_to_new
    simpa [commonP, y, y', k2, k3, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using h
  have hcommon_32 : F.rel commonP y' y := by
    have h :=
      (hax.a3.2 (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k3) (j := k2) h32_ne
        (qᵢ := r') (qⱼ := r)).mpr hright_to_old
    simpa [commonP, y, y', k2, k3, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using h
  have hreplace : F.rel commonP x y ↔ F.rel commonP x' y' :=
    blackwell_rel_replace_by_equiv (fun a b => F.rel commonP a b) htrans
      hcommon_01 hcommon_10 hcommon_23 hcommon_32
  have hcommon_13 :
      F.rel commonP x' y' ↔
        F.rel (blockChannel P' Q') (inlDist q') (inrDist r') := by
    simpa [commonP, x', y', k1, k3, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using
      (hax.a3.2 (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k1) (j := k3) h13_ne
        (qᵢ := q') (qⱼ := r'))
  exact hcommon_02.symm.trans (hreplace.trans hcommon_13)

/--
A1/A3 common-block replacement for experiment-pair preferences: if the left
side and right side are each weakly equivalent to replacements in both
directions, then the whole pairwise block comparison is preserved.
-/
theorem experimentPairPref_replacement_from_weak_equiv
    (F : PrefFamily.{u}) (hax : TraceAxioms F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A)
    (E E' G G' : FiniteExperimentOn A)
    (hE_to_new : ExperimentPairPref F E E' q q)
    (hE_to_old : ExperimentPairPref F E' E q q)
    (hG_to_new : ExperimentPairPref F G G' q q)
    (hG_to_old : ExperimentPairPref F G' G q q) :
    ExperimentPairPref F E G q q ↔
      ExperimentPairPref F E' G' q q := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype E'.OutcomeType := E'.outFintype
  letI : DecidableEq E'.OutcomeType := E'.outDecEq
  letI : Fintype G.OutcomeType := G.outFintype
  letI : DecidableEq G.OutcomeType := G.outDecEq
  letI : Fintype G'.OutcomeType := G'.outFintype
  letI : DecidableEq G'.OutcomeType := G'.outDecEq
  have h :=
    blackwell_pairwise_block_replacement_from_weak_equiv
      F hax E.P E'.P G.P G'.P q q q q
      (by simpa [ExperimentPairPref, blockExperimentChannel] using hE_to_new)
      (by simpa [ExperimentPairPref, blockExperimentChannel] using hE_to_old)
      (by simpa [ExperimentPairPref, blockExperimentChannel] using hG_to_new)
      (by simpa [ExperimentPairPref, blockExperimentChannel] using hG_to_old)
  simpa [ExperimentPairPref, blockExperimentChannel] using h

/--
Reconstruct the old Blackwell/posterior replacement package from the classical
finite same-posterior-law mutual-garbling theorem plus internal A4/A3/A1
replacement plumbing.
-/
theorem blackwellPosteriorReplacement_of_samePosteriorGarblings
    (hgarble : FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{u}) :
    FiniteBlackwellPosteriorAssumptions.{u} where
  left_replacement := by
    intro F A instFA instDA instNA hax q hq E E' G hsame
    have hE_to_E' : ExperimentPairPref F E E' q q :=
      experimentPairPref_of_postprocess F hax q E E'
        (hgarble.same_posterior_left_garbling q hq E E' hsame)
    have hE'_to_E : ExperimentPairPref F E' E q q :=
      experimentPairPref_of_postprocess F hax q E' E
        (hgarble.same_posterior_right_garbling q hq E E' hsame)
    have hG_self : ExperimentPairPref F G G q q :=
      experimentPairPref_self_of_axioms F hax q G
    exact
      experimentPairPref_replacement_from_weak_equiv F hax q E E' G G
        hE_to_E' hE'_to_E hG_self hG_self
  right_replacement := by
    intro F A instFA instDA instNA hax q hq G E E' hsame
    have hE_to_E' : ExperimentPairPref F E E' q q :=
      experimentPairPref_of_postprocess F hax q E E'
        (hgarble.same_posterior_left_garbling q hq E E' hsame)
    have hE'_to_E : ExperimentPairPref F E' E q q :=
      experimentPairPref_of_postprocess F hax q E' E
        (hgarble.same_posterior_right_garbling q hq E E' hsame)
    have hG_self : ExperimentPairPref F G G q q :=
      experimentPairPref_self_of_axioms F hax q G
    exact
      experimentPairPref_replacement_from_weak_equiv F hax q G G E E'
        hG_self hG_self hE_to_E' hE'_to_E

/-!
## Posterior-Law Sufficiency from Blackwell Assumptions

Given the Blackwell replacement properties, we can prove PosteriorLawSufficiency.
-/

/--
**Posterior-Law Sufficiency**

If two pairs of experiments induce the same posterior laws (E₁ ~ E₁' and E₂ ~ E₂'),
then their block comparisons are equivalent.

Paper: "only the induced law of posterior beliefs about acts matters"
-/
def PosteriorLawSufficiency (F : PrefFamily.{u}) : Prop :=
  ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (_hq : q.FullSupport)
    (E₁ E₂ E₁' E₂' : FiniteExperimentOn A),
    SamePosteriorLawExp q E₁ E₁' →
    SamePosteriorLawExp q E₂ E₂' →
    (ExperimentPairPref F E₁ E₂ q q ↔ ExperimentPairPref F E₁' E₂' q q)

/--
**From Axioms to Posterior-Law Sufficiency via Blackwell**

This is the first bridge in the sufficiency spine.
Paper: Lemmas blockcoh--blackwell, plsuff (lines 810-998).

The proof uses:
1. left_replacement: E₁ ~ E₁' ⟹ (E₁ ≽ E₂ ↔ E₁' ≽ E₂)
2. right_replacement: E₂ ~ E₂' ⟹ (E₁' ≽ E₂ ↔ E₁' ≽ E₂')

Combined: E₁ ≽ E₂ ↔ E₁' ≽ E₂ ↔ E₁' ≽ E₂'
-/
theorem from_axioms_to_posterior_of_blackwell
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hax : TraceAxioms F) :
    PosteriorLawSufficiency F := by
  intro A instFA instDA instNA q hq E₁ E₂ E₁' E₂' hsame₁ hsame₂
  calc ExperimentPairPref F E₁ E₂ q q
      ↔ ExperimentPairPref F E₁' E₂ q q := hblackwell.left_replacement hax q hq E₁ E₁' E₂ hsame₁
    _ ↔ ExperimentPairPref F E₁' E₂' q q := hblackwell.right_replacement hax q hq E₁' E₂ E₂' hsame₂

end TraceableAgency
