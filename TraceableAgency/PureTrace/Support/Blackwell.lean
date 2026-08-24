/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Info.DataProcessing
import TraceableAgency.Basic.Channel
import TraceableAgency.Basic.Convergence
import TraceableAgency.PureTrace.Behaviour.Conditions

/-!
# Finite Blackwell Equivalence

The finite mutual-information data-processing inequalities are proved
internally in `TraceableAgency.Info.DataProcessing`.  This file also proves
the finite same-posterior-law Blackwell equivalence by constructing the
garbling kernels explicitly.
-/

namespace TraceableAgency

universe u

/-!
## Finite Blackwell statement

The proposition-valued record below states the exact finite Blackwell theorem:
two channels inducing the same posterior law at a full-support prior are
mutual garblings of each other.  It is retained as a compatibility-friendly
statement schema; `finiteSamePosteriorLawBlackwellEquivalence` constructs its
canonical inhabitant below.

Paper reference: Lemma blackwell and Lemma plsuff.

The paper proves:
1. Same posterior law ⟹ mutual garblings exist: Q = PT and P = QT' for some T, T'
2. Combined with main-text A6 (record post-processing): q^0 ≽_{P⊔Q} q^1 and q^0 ≽_{Q⊔P} q^1
3. Combined with main-text A5 (block coherence) and A1 transitivity: same-posterior-law
   experiments may be replaced inside pairwise block comparisons.

Both the finite Blackwell/garbling equivalence and the A6/A5/A1 replacement
plumbing are proved below.
-/

/-- Experiment-level postprocessing/garbling relation. -/
def ExperimentPostprocesses {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (E E' : FiniteExperimentOn A) : Prop :=
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype E'.OutcomeType := E'.outFintype
  ∃ T : Channel E.OutcomeType E'.OutcomeType,
    E'.P = Channel.postprocess E.P T

/--
Finite Blackwell equivalence at a fixed full-support prior:
same posterior law gives garblings in both directions.

This is the exact statement of paper Lemma `blackwell`.
It does not mention preferences, A5/A6, or block replacement.
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

/-!
## Constructive proof of finite Blackwell equivalence

For a posterior `r`, `posteriorClassMass q E r` is the total probability of
all outcomes of `E` that induce `r`.  Equality of finite posterior laws says
exactly that these class masses agree.  The garbling below forgets which
outcome inside a posterior class was observed and redraws an outcome of the
target experiment proportionally to its marginal probability inside the same
class.  Null source outcomes receive an arbitrary stochastic row; full support
of the prior makes every such source column identically zero.
-/

/-- Total outcome mass carried by one exact posterior value. -/
noncomputable def posteriorClassMass
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (r : Dist A) : ℝ := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  exact
    ∑ o : E.OutcomeType,
      if E.posterior q o = r then E.outcomeMarginal q o else 0

theorem posteriorClassMass_nonneg
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (r : Dist A) :
    0 ≤ posteriorClassMass q E r := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  unfold posteriorClassMass
  apply Finset.sum_nonneg
  intro o _ho
  split_ifs
  · exact (E.outcomeMarginal q).nonneg o
  · exact le_rfl

/-- The mass of an outcome is bounded by the mass of its posterior class. -/
theorem outcomeMarginal_le_posteriorClassMass
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (o : E.OutcomeType) :
    E.outcomeMarginal q o ≤
      posteriorClassMass q E (E.posterior q o) := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  unfold posteriorClassMass
  calc
    E.outcomeMarginal q o =
        (if E.posterior q o = E.posterior q o
          then E.outcomeMarginal q o else 0) := by simp
    _ ≤ ∑ y : E.OutcomeType,
          if E.posterior q y = E.posterior q o
            then E.outcomeMarginal q y else 0 := by
      have h :=
        Finset.single_le_sum
          (s := Finset.univ)
          (f := fun y : E.OutcomeType =>
            if E.posterior q y = E.posterior q o
              then E.outcomeMarginal q y else 0)
          (fun y _hy => by
            split_ifs
            · exact (E.outcomeMarginal q).nonneg y
            · exact le_rfl)
          (Finset.mem_univ o)
      simpa using h

/-- Equal finite posterior laws give equal mass to every exact posterior
class.  The passage from continuous tests to the class indicator is the
finite interpolation theorem already proved in `Basic.Convergence`. -/
theorem posteriorClassMass_eq_of_samePosteriorLawExp
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A)
    (hsame : SamePosteriorLawExp q E E') (r : Dist A) :
    posteriorClassMass q E r = posteriorClassMass q E' r := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype E'.OutcomeType := E'.outFintype
  have h :=
    samePosteriorLawExp_all_test_functions q E E' hsame
      (fun s : Dist A => if s = r then 1 else 0)
  simpa [posteriorLawIntegralExp, posteriorClassMass] using h

/-- The conditional marginal distribution of outcomes inside one positive
posterior class. -/
noncomputable def posteriorClassDistribution
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) (r : Dist A)
    (hpos : 0 < posteriorClassMass q E r) :
    @Dist E.OutcomeType E.outFintype := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  refine
    { prob := fun o =>
        if E.posterior q o = r then
          E.outcomeMarginal q o / posteriorClassMass q E r
        else 0
      nonneg := ?_
      sum_eq_one := ?_ }
  · intro o
    split_ifs
    · exact div_nonneg ((E.outcomeMarginal q).nonneg o) (le_of_lt hpos)
    · exact le_rfl
  · calc
      (∑ o : E.OutcomeType,
          if E.posterior q o = r then
            E.outcomeMarginal q o / posteriorClassMass q E r
          else 0) =
          (∑ o : E.OutcomeType,
            (if E.posterior q o = r then E.outcomeMarginal q o else 0) /
              posteriorClassMass q E r) := by
            apply Finset.sum_congr rfl
            intro o _ho
            split_ifs <;> simp
      _ =
          (∑ o : E.OutcomeType,
            if E.posterior q o = r then E.outcomeMarginal q o else 0) /
              posteriorClassMass q E r := by
            rw [Finset.sum_div]
      _ = posteriorClassMass q E r / posteriorClassMass q E r := by
            rfl
      _ = 1 := div_self (ne_of_gt hpos)

/-- Kernel that randomizes only within the target experiment's posterior
class.  A zero-mass class uses an arbitrary target-channel row. -/
noncomputable def posteriorMatchingKernel
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A) :
    @Channel E.OutcomeType E'.OutcomeType E'.outFintype := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype E'.OutcomeType := E'.outFintype
  exact fun o =>
    if hpos : 0 < posteriorClassMass q E' (E.posterior q o) then
      posteriorClassDistribution q E' (E.posterior q o) hpos
    else
      E'.P (Classical.arbitrary A)

theorem posteriorMatchingKernel_apply_of_classMass_pos_of_eq
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A)
    (o : E.OutcomeType) (y : E'.OutcomeType)
    (hpos : 0 < posteriorClassMass q E' (E.posterior q o))
    (hpost : E'.posterior q y = E.posterior q o) :
    posteriorMatchingKernel q E E' o y =
      E'.outcomeMarginal q y /
        posteriorClassMass q E' (E.posterior q o) := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype E'.OutcomeType := E'.outFintype
  unfold posteriorMatchingKernel
  rw [dif_pos hpos]
  simp [posteriorClassDistribution, hpost]

theorem posteriorMatchingKernel_apply_of_classMass_pos_of_ne
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn A)
    (o : E.OutcomeType) (y : E'.OutcomeType)
    (hpos : 0 < posteriorClassMass q E' (E.posterior q o))
    (hpost : E'.posterior q y ≠ E.posterior q o) :
    posteriorMatchingKernel q E E' o y = 0 := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype E'.OutcomeType := E'.outFintype
  unfold posteriorMatchingKernel
  rw [dif_pos hpos]
  simp [posteriorClassDistribution, hpost]

/-- One direction of finite Blackwell equivalence: equality of posterior laws
constructs an explicit post-processing from `E` to `E'`. -/
theorem experimentPostprocesses_of_samePosteriorLawExp
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (E E' : FiniteExperimentOn A)
    (hsame : SamePosteriorLawExp q E E') :
    ExperimentPostprocesses E E' := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype E'.OutcomeType := E'.outFintype
  letI : DecidableEq E'.OutcomeType := E'.outDecEq
  let T := posteriorMatchingKernel q E E'
  refine ⟨T, ?_⟩
  ext a y
  have hterm :
      ∀ o : E.OutcomeType,
        q a * (E.P a o * T o y) =
          if E'.posterior q y = E.posterior q o then
            (E.outcomeMarginal q o * E.posterior q o a) *
              (E'.outcomeMarginal q y /
                posteriorClassMass q E' (E.posterior q o))
          else 0 := by
    intro o
    by_cases hmo : 0 < E.outcomeMarginal q o
    · have hclassE :
          0 < posteriorClassMass q E (E.posterior q o) :=
        lt_of_lt_of_le hmo
          (outcomeMarginal_le_posteriorClassMass q E o)
      have hclassE' :
          0 < posteriorClassMass q E' (E.posterior q o) := by
        rw [← posteriorClassMass_eq_of_samePosteriorLawExp q E E'
          hsame (E.posterior q o)]
        exact hclassE
      by_cases hpost : E'.posterior q y = E.posterior q o
      · rw [posteriorMatchingKernel_apply_of_classMass_pos_of_eq
          q E E' o y hclassE' hpost]
        rw [if_pos hpost]
        rw [show q a * (E.P a o *
              (E'.outcomeMarginal q y /
                posteriorClassMass q E' (E.posterior q o))) =
            (q a * E.P a o) *
              (E'.outcomeMarginal q y /
                posteriorClassMass q E' (E.posterior q o)) by ring]
        rw [← posterior_mul_marginal q E.P o a]
        simp only [FiniteExperimentOn.outcomeMarginal,
          FiniteExperimentOn.posterior]
      · rw [posteriorMatchingKernel_apply_of_classMass_pos_of_ne
          q E E' o y hclassE' hpost]
        rw [if_neg hpost]
        ring
    · have hmozero : E.outcomeMarginal q o = 0 :=
        le_antisymm (le_of_not_gt hmo) ((E.outcomeMarginal q).nonneg o)
      have hjointzero : q a * E.P a o = 0 := by
        rw [← posterior_mul_marginal q E.P o a]
        change E.outcomeMarginal q o * E.posterior q o a = 0
        rw [hmozero]
        ring
      rw [show q a * (E.P a o * T o y) =
          (q a * E.P a o) * T o y by ring]
      rw [hjointzero]
      simp [hmozero]
  have hscaled :
      q a * Channel.postprocess E.P T a y =
        ∑ o : E.OutcomeType,
          if E'.posterior q y = E.posterior q o then
            (E.outcomeMarginal q o * E.posterior q o a) *
              (E'.outcomeMarginal q y /
                posteriorClassMass q E' (E.posterior q o))
          else 0 := by
    change q a * (∑ o : E.OutcomeType, E.P a o * T o y) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _ho
    exact hterm o
  have hscaled_target :
      q a * Channel.postprocess E.P T a y = q a * E'.P a y := by
    rw [hscaled]
    by_cases hmy : 0 < E'.outcomeMarginal q y
    · have hclassE' :
          0 < posteriorClassMass q E' (E'.posterior q y) :=
        lt_of_lt_of_le hmy
          (outcomeMarginal_le_posteriorClassMass q E' y)
      have hclassEq :
          posteriorClassMass q E (E'.posterior q y) =
            posteriorClassMass q E' (E'.posterior q y) :=
        posteriorClassMass_eq_of_samePosteriorLawExp q E E' hsame
          (E'.posterior q y)
      have hfactor :
          (∑ o : E.OutcomeType,
            if E'.posterior q y = E.posterior q o then
              (E.outcomeMarginal q o * E.posterior q o a) *
                (E'.outcomeMarginal q y /
                  posteriorClassMass q E' (E.posterior q o))
            else 0) =
            posteriorClassMass q E (E'.posterior q y) *
              (E'.posterior q y a *
                (E'.outcomeMarginal q y /
                  posteriorClassMass q E' (E'.posterior q y))) := by
        unfold posteriorClassMass
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro o _ho
        by_cases hpost : E'.posterior q y = E.posterior q o
        · simp only [hpost, ↓reduceIte]
          ring
        · have hpost' : E.posterior q o ≠ E'.posterior q y :=
            fun h => hpost h.symm
          simp only [hpost, hpost', ↓reduceIte, zero_mul]
      rw [hfactor, hclassEq]
      have hclassNe :
          posteriorClassMass q E' (E'.posterior q y) ≠ 0 :=
        ne_of_gt hclassE'
      calc
        posteriorClassMass q E' (E'.posterior q y) *
              (E'.posterior q y a *
                (E'.outcomeMarginal q y /
                  posteriorClassMass q E' (E'.posterior q y))) =
            E'.outcomeMarginal q y * E'.posterior q y a := by
              field_simp [hclassNe]
        _ = q a * E'.P a y :=
          posterior_mul_marginal q E'.P y a
    · have hmyzero : E'.outcomeMarginal q y = 0 :=
        le_antisymm (le_of_not_gt hmy) ((E'.outcomeMarginal q).nonneg y)
      have hjointzero : q a * E'.P a y = 0 := by
        rw [← posterior_mul_marginal q E'.P y a]
        change E'.outcomeMarginal q y * E'.posterior q y a = 0
        rw [hmyzero]
        ring
      simp [hmyzero, hjointzero]
  exact
    (mul_left_cancel₀ (ne_of_gt (hq a)) hscaled_target).symm

theorem samePosteriorLawExp_symm
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    {q : Dist A} {E E' : FiniteExperimentOn A}
    (hsame : SamePosteriorLawExp q E E') :
    SamePosteriorLawExp q E' E := by
  intro φ hφ
  exact (hsame φ hφ).symm

/-- Prior-specific finite Blackwell equivalence in the direct paper form:
equal posterior laws produce stochastic garblings in both directions. -/
theorem finiteBlackwellEquivalence_of_samePosteriorLawExp
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (E E' : FiniteExperimentOn A)
    (hsame : SamePosteriorLawExp q E E') :
    ExperimentPostprocesses E E' ∧ ExperimentPostprocesses E' E :=
  ⟨experimentPostprocesses_of_samePosteriorLawExp q hq E E' hsame,
    experimentPostprocesses_of_samePosteriorLawExp q hq E' E
      (samePosteriorLawExp_symm hsame)⟩

/-- Finite Blackwell equivalence, proved internally. -/
theorem finiteSamePosteriorLawBlackwellEquivalence :
    FiniteSamePosteriorLawBlackwellEquivalenceAssumptions.{u} where
  same_posterior_left_garbling := by
    intro A _ _ _ q hq E E' hsame
    exact
      (finiteBlackwellEquivalence_of_samePosteriorLawExp
        q hq E E' hsame).1
  same_posterior_right_garbling := by
    intro A _ _ _ q hq E E' hsame
    exact
      (finiteBlackwellEquivalence_of_samePosteriorLawExp
        q hq E E' hsame).2

/--
**Finite Blackwell Posterior-Law Assumptions**

At a full-support prior, two experiments inducing the same posterior law
can be substituted in block comparisons without changing the preference.

This packages:
1. The finite Blackwell equivalence theorem (same posterior ⟹ mutual garblings)
2. Application of main-text A6 (record post-processing) to get indifference
3. Use of main-text A5 (finite-block coherence) to transfer indifference across environments
4. Transitivity from A1 to derive the replacement property

Paper: Lemmas blackwell + plsuff + blockcoh.

**Key proof structure from paper:**
- Blackwell (lem:blackwell): Same posterior law ⟹ Q = PT, P = QT' for garblings T, T'
- A6 gives: q^0 ≽_{P⊔Q} q^1 (using Q = PT)
- A6 + A5 reverse-block gives: q^1 ≽_{P⊔Q} q^0 (using P = QT')
- Combined: q^0 ~_{P⊔Q} q^1
- For replacement: place E, E', G in 3-block environment, use A5 + transitivity

The record states the replacement property used by older internal APIs.  It
is not a public assumption: it is reconstructed below from the proved finite
mutual-garbling theorem.
-/
structure FiniteBlackwellPosteriorAssumptions.{v} : Prop where
  /-- Left replacement: same posterior law allows substitution on the left.
      Paper proof: E ~_{E⊔E'} E' by Blackwell+A6, then place in 3-block with G,
      use A5 finite-block coherence and A1 transitivity.
      If E ~ E' (same posterior) then (E ≽ G ↔ E' ≽ G) in block comparisons. -/
  left_replacement :
    ∀ {F : PrefFamily.{v}} {A : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      (hax : PureTraceConditions F)
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
      (hax : PureTraceConditions F)
      (q : Dist A) (_hq : q.FullSupport)
      (G E E' : FiniteExperimentOn A),
      SamePosteriorLawExp q E E' →
      (ExperimentPairPref F G E q q ↔ ExperimentPairPref F G E' q q)

theorem experimentPairPref_of_postprocess
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
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
  exact hax.recordProcessing E.P T q

theorem experimentPairPref_self_of_axioms
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) :
    ExperimentPairPref F E E q q := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  have hself : F.rel E.P q q := by
    rcases (hax.weakOrder.1 E.P).1 q q with h | h <;> exact h
  have hblock := (hax.blockCoherence.duplication E.P q q).mp hself
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
equivalent to a replacement side, then A5 and A1 transitivity preserve the
pairwise comparison.
-/
theorem blackwell_pairwise_block_replacement_from_weak_equiv
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
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
    (hax.weakOrder.1 commonP).2
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
      (hax.blockCoherence.finite_block (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k0) (j := k2) h02_ne
        (qᵢ := q) (qⱼ := r))
  have hcommon_01 : F.rel commonP x x' := by
    have h :=
      (hax.blockCoherence.finite_block (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k0) (j := k1) h01_ne
        (qᵢ := q) (qⱼ := q')).mpr hleft_to_new
    simpa [commonP, x, x', k0, k1, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using h
  have hcommon_10 : F.rel commonP x' x := by
    have h :=
      (hax.blockCoherence.finite_block (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k1) (j := k0) h10_ne
        (qᵢ := q') (qⱼ := q)).mpr hleft_to_old
    simpa [commonP, x, x', k0, k1, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using h
  have hcommon_23 : F.rel commonP y y' := by
    have h :=
      (hax.blockCoherence.finite_block (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k2) (j := k3) h23_ne
        (qᵢ := r) (qⱼ := r')).mpr hright_to_new
    simpa [commonP, y, y', k2, k3, Act, Out, C, blackwellPairBlockReplacementAct,
      blackwellPairBlockReplacementOut, blackwellPairBlockReplacementChannel] using h
  have hcommon_32 : F.rel commonP y' y := by
    have h :=
      (hax.blockCoherence.finite_block (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
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
      (hax.blockCoherence.finite_block (K := BlackwellPairBlockReplacementBlock) (Act := Act) (Out := Out)
        (P := C) (i := k1) (j := k3) h13_ne
        (qᵢ := q') (qⱼ := r'))
  exact hcommon_02.symm.trans (hreplace.trans hcommon_13)

/--
A1/A5 common-block replacement for experiment-pair preferences: if the left
side and right side are each weakly equivalent to replacements in both
directions, then the whole pairwise block comparison is preserved.
-/
theorem experimentPairPref_replacement_from_weak_equiv
    (F : PrefFamily.{u}) (hax : PureTraceConditions F)
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
Reconstruct the old Blackwell/posterior replacement package from the finite
same-posterior-law mutual-garbling theorem plus internal A6/A5/A1
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

/-- Canonical posterior-replacement package obtained from the internally
proved finite Blackwell equivalence. -/
theorem finiteBlackwellPosteriorReplacement :
    FiniteBlackwellPosteriorAssumptions.{u} :=
  blackwellPosteriorReplacement_of_samePosteriorGarblings
    finiteSamePosteriorLawBlackwellEquivalence

/-!
## Posterior-Law Sufficiency from finite Blackwell equivalence

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
Paper: Lemmas blockcoh--blackwell, plsuff.

The proof uses:
1. left_replacement: E₁ ~ E₁' ⟹ (E₁ ≽ E₂ ↔ E₁' ≽ E₂)
2. right_replacement: E₂ ~ E₂' ⟹ (E₁' ≽ E₂ ↔ E₁' ≽ E₂')

Combined: E₁ ≽ E₂ ↔ E₁' ≽ E₂ ↔ E₁' ≽ E₂'
-/
theorem from_axioms_to_posterior_of_blackwell
    (F : PrefFamily.{u})
    (hblackwell : FiniteBlackwellPosteriorAssumptions.{u})
    (hax : PureTraceConditions F) :
    PosteriorLawSufficiency F := by
  intro A instFA instDA instNA q hq E₁ E₂ E₁' E₂' hsame₁ hsame₂
  calc ExperimentPairPref F E₁ E₂ q q
      ↔ ExperimentPairPref F E₁' E₂ q q := hblackwell.left_replacement hax q hq E₁ E₁' E₂ hsame₁
    _ ↔ ExperimentPairPref F E₁' E₂' q q := hblackwell.right_replacement hax q hq E₁' E₂ E₂' hsame₂

/-- Posterior-law sufficiency derived from the trace axioms, using the
internally proved finite Blackwell theorem. -/
theorem posteriorLawSufficiency_of_axioms
    (F : PrefFamily.{u})
    (hax : PureTraceConditions F) :
    PosteriorLawSufficiency F :=
  from_axioms_to_posterior_of_blackwell F
    finiteBlackwellPosteriorReplacement hax

end TraceableAgency
