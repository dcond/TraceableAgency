/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Info.Identities
import TraceableAgency.PureTrace.Behaviour.Conditions
import TraceableAgency.Theorem1.Statements

/-!
# Marked terminal laws

This file develops the finite, full-support Blackwell argument for the joint
terminal statistic consisting of the realized payoff and the posterior over
actions.  Its matching kernels rewrite only the explicit record coordinate;
the realized payoff is copied in every row.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

/-- A finite joint experiment with fixed payoff and action alphabets and a
nonempty finite explicit-record alphabet. -/
structure MarkedTerminalExperiment
    (O A : Type u) [Fintype O] [Fintype A] where
  RecordType : Type u
  recordFintype : Fintype RecordType
  recordDecEq : DecidableEq RecordType
  recordNonempty : Nonempty RecordType
  channel : Channel A (O × RecordType)

namespace MarkedTerminalExperiment

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Shorthand for the bundled joint channel. -/
abbrev K (E : MarkedTerminalExperiment O A) :
    @Channel A (O × E.RecordType)
      (@instFintypeProd O E.RecordType inferInstance E.recordFintype) :=
  E.channel

/-- Marginal probability of a visible payoff-record pair. -/
noncomputable def outcomeMarginal
    (E : MarkedTerminalExperiment O A) (q : TraceableAgency.Dist A) :
    @TraceableAgency.Dist (O × E.RecordType)
      (@instFintypeProd O E.RecordType inferInstance E.recordFintype) := by
  letI : Fintype E.RecordType := E.recordFintype
  exact Channel.outcomeMarginal E.K q

/-- Posterior over actions after a visible payoff-record pair. -/
noncomputable def posterior
    (E : MarkedTerminalExperiment O A) (q : TraceableAgency.Dist A)
    (z : O × E.RecordType) : TraceableAgency.Dist A := by
  letI : Fintype E.RecordType := E.recordFintype
  exact Channel.posterior E.K q z

end MarkedTerminalExperiment

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Integral of an arbitrary real test against the finite law of
`(realized payoff, posterior over actions)`. -/
noncomputable def markedTerminalIntegral
    (q : TraceableAgency.Dist A) (E : MarkedTerminalExperiment O A)
    (phi : O × TraceableAgency.Dist A → ℝ) : ℝ := by
  letI : Fintype E.RecordType := E.recordFintype
  exact
    ∑ z : O × E.RecordType,
      E.outcomeMarginal q z * phi (z.1, E.posterior q z)

/-- Equality of marked terminal laws.  All real tests are admitted, so this
is literal equality of the two finite laws rather than only a topological
surrogate. -/
def SameMarkedTerminalLaw
    (q : TraceableAgency.Dist A) (E E' : MarkedTerminalExperiment O A) : Prop :=
  ∀ phi : O × TraceableAgency.Dist A → ℝ,
    markedTerminalIntegral q E phi = markedTerminalIntegral q E' phi

/-- Marked-terminal-law equality is an equivalence relation at each prior. -/
def markedTerminalSetoid (q : TraceableAgency.Dist A) :
    Setoid (MarkedTerminalExperiment O A) where
  r := SameMarkedTerminalLaw q
  iseqv :=
    { refl := by
        intro E phi
        rfl
      symm := by
        intro E E' h phi
        exact (h phi).symm
      trans := by
        intro E E' E'' h h' phi
        exact (h phi).trans (h' phi) }

/-- Total mass of one exact marked class `(o, posterior)`. -/
noncomputable def markedPosteriorClassMass
    (q : TraceableAgency.Dist A) (E : MarkedTerminalExperiment O A)
    (o : O) (p : TraceableAgency.Dist A) : ℝ := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  exact
    ∑ r : E.RecordType,
      if E.posterior q (o, r) = p then
        E.outcomeMarginal q (o, r)
      else 0

theorem markedPosteriorClassMass_nonneg
    (q : TraceableAgency.Dist A) (E : MarkedTerminalExperiment O A)
    (o : O) (p : TraceableAgency.Dist A) :
    0 ≤ markedPosteriorClassMass q E o p := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  unfold markedPosteriorClassMass
  apply Finset.sum_nonneg
  intro r _hr
  split_ifs
  · exact (E.outcomeMarginal q).nonneg (o, r)
  · exact le_rfl

/-- An outcome's mass is bounded by its marked posterior-class mass. -/
theorem outcomeMarginal_le_markedPosteriorClassMass
    (q : TraceableAgency.Dist A) (E : MarkedTerminalExperiment O A)
    (o : O) (r : E.RecordType) :
    E.outcomeMarginal q (o, r) ≤
      markedPosteriorClassMass q E o (E.posterior q (o, r)) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  unfold markedPosteriorClassMass
  calc
    E.outcomeMarginal q (o, r) =
        (if E.posterior q (o, r) = E.posterior q (o, r) then
          E.outcomeMarginal q (o, r) else 0) := by simp
    _ ≤ ∑ s : E.RecordType,
        if E.posterior q (o, s) = E.posterior q (o, r) then
          E.outcomeMarginal q (o, s) else 0 := by
      exact Finset.single_le_sum
        (f := fun s : E.RecordType =>
          if E.posterior q (o, s) = E.posterior q (o, r) then
            E.outcomeMarginal q (o, s) else 0)
        (fun s _hs => by
          split_ifs
          · exact (E.outcomeMarginal q).nonneg (o, s)
          · exact le_rfl)
        (Finset.mem_univ r)

/-- Equal marked laws give equal mass to every exact marked class. -/
theorem markedPosteriorClassMass_eq_of_sameMarkedTerminalLaw
    (q : TraceableAgency.Dist A) (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E')
    (o : O) (p : TraceableAgency.Dist A) :
    markedPosteriorClassMass q E o p =
      markedPosteriorClassMass q E' o p := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : Fintype E'.RecordType := E'.recordFintype
  let indicator := fun x : O × TraceableAgency.Dist A =>
    if x.1 = o ∧ x.2 = p then (1 : ℝ) else 0
  have h := hsame indicator
  have hE : markedTerminalIntegral q E indicator =
      markedPosteriorClassMass q E o p := by
    unfold markedTerminalIntegral markedPosteriorClassMass
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single o]
    · simp [indicator]
    · intro o' _ho' hne
      simp [indicator, hne]
    · simp
  have hE' : markedTerminalIntegral q E' indicator =
      markedPosteriorClassMass q E' o p := by
    unfold markedTerminalIntegral markedPosteriorClassMass
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_eq_single o]
    · simp [indicator]
    · intro o' _ho' hne
      simp [indicator, hne]
    · simp
  exact hE.symm.trans (h.trans hE')

/-- Conditional distribution of target records within one positive marked
posterior class. -/
noncomputable def markedPosteriorClassDistribution
    (q : TraceableAgency.Dist A) (E : MarkedTerminalExperiment O A)
    (o : O) (p : TraceableAgency.Dist A)
    (hpos : 0 < markedPosteriorClassMass q E o p) :
    @TraceableAgency.Dist E.RecordType E.recordFintype := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  refine
    { prob := fun r =>
        if E.posterior q (o, r) = p then
          E.outcomeMarginal q (o, r) /
            markedPosteriorClassMass q E o p
        else 0
      nonneg := ?_
      sum_eq_one := ?_ }
  · intro r
    split_ifs
    · exact div_nonneg ((E.outcomeMarginal q).nonneg (o, r))
        (le_of_lt hpos)
    · exact le_rfl
  · calc
      (∑ r : E.RecordType,
          if E.posterior q (o, r) = p then
            E.outcomeMarginal q (o, r) /
              markedPosteriorClassMass q E o p
          else 0) =
          (∑ r : E.RecordType,
            (if E.posterior q (o, r) = p then
              E.outcomeMarginal q (o, r) else 0) /
                markedPosteriorClassMass q E o p) := by
            apply Finset.sum_congr rfl
            intro r _hr
            split_ifs <;> simp
      _ = markedPosteriorClassMass q E o p /
            markedPosteriorClassMass q E o p := by
          rw [← Finset.sum_div]
          rfl
      _ = 1 := div_self (ne_of_gt hpos)

/-- Payoff-preserving record matcher.  A positive source class is randomized
within the target experiment's class having the same payoff and posterior.
The arbitrary fallback row is used only for a null marked class. -/
noncomputable def markedPosteriorMatchingProcessor
    (q : TraceableAgency.Dist A) (E E' : MarkedTerminalExperiment O A) :
    @RecordProcessor O E.RecordType E'.RecordType E'.recordFintype := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  exact fun z =>
    if hpos : 0 < markedPosteriorClassMass q E' z.1
        (E.posterior q z) then
      markedPosteriorClassDistribution q E' z.1
        (E.posterior q z) hpos
    else
      TraceableAgency.Dist.pure (Classical.arbitrary E'.RecordType)

theorem markedPosteriorMatchingProcessor_apply_of_pos_of_eq
    (q : TraceableAgency.Dist A) (E E' : MarkedTerminalExperiment O A)
    (z : O × E.RecordType) (s : E'.RecordType)
    (hpos : 0 < markedPosteriorClassMass q E' z.1
      (E.posterior q z))
    (hpost : E'.posterior q (z.1, s) = E.posterior q z) :
    markedPosteriorMatchingProcessor q E E' z s =
      E'.outcomeMarginal q (z.1, s) /
        markedPosteriorClassMass q E' z.1 (E.posterior q z) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  unfold markedPosteriorMatchingProcessor
  rw [dif_pos hpos]
  simp [markedPosteriorClassDistribution, hpost]

theorem markedPosteriorMatchingProcessor_apply_of_pos_of_ne
    (q : TraceableAgency.Dist A) (E E' : MarkedTerminalExperiment O A)
    (z : O × E.RecordType) (s : E'.RecordType)
    (hpos : 0 < markedPosteriorClassMass q E' z.1
      (E.posterior q z))
    (hpost : E'.posterior q (z.1, s) ≠ E.posterior q z) :
    markedPosteriorMatchingProcessor q E E' z s = 0 := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  unfold markedPosteriorMatchingProcessor
  rw [dif_pos hpos]
  simp [markedPosteriorClassDistribution, hpost]

/-! ## Full-support payoff-preserving Blackwell equivalence -/

/-- The target joint experiment is obtained from the source by rewriting only
the explicit record coordinate. -/
def MarkedExperimentRecordPostprocesses
    (E E' : MarkedTerminalExperiment O A) : Prop := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  exact ∃ T : RecordProcessor O E.RecordType E'.RecordType,
    E'.K = recordPostprocess E.K T

/-- One direction of the marked finite Blackwell theorem.  The constructed
processor never changes the payoff coordinate. -/
theorem markedExperimentRecordPostprocesses_of_sameMarkedTerminalLaw
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E') :
    MarkedExperimentRecordPostprocesses E E' := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  let processor := markedPosteriorMatchingProcessor q E E'
  let T := payoffPreservingRecordKernel processor
  unfold MarkedExperimentRecordPostprocesses
  refine ⟨processor, ?_⟩
  change E'.K = Channel.postprocess E.K T
  ext a y
  rcases y with ⟨oy, s⟩
  have hterm :
      ∀ z : O × E.RecordType,
        q a * (E.K a z * T z (oy, s)) =
          if oy = z.1 ∧
              E'.posterior q (oy, s) = E.posterior q z then
            (E.outcomeMarginal q z * E.posterior q z a) *
              (E'.outcomeMarginal q (oy, s) /
                markedPosteriorClassMass q E' z.1
                  (E.posterior q z))
          else 0 := by
    intro z
    rcases z with ⟨oz, r⟩
    by_cases hm : 0 < E.outcomeMarginal q (oz, r)
    · have hclassE :
          0 < markedPosteriorClassMass q E oz
            (E.posterior q (oz, r)) :=
        lt_of_lt_of_le hm
          (outcomeMarginal_le_markedPosteriorClassMass q E oz r)
      have hclassE' :
          0 < markedPosteriorClassMass q E' oz
            (E.posterior q (oz, r)) := by
        rw [← markedPosteriorClassMass_eq_of_sameMarkedTerminalLaw
          q E E' hsame oz (E.posterior q (oz, r))]
        exact hclassE
      by_cases hpay : oy = oz
      · subst oy
        by_cases hpost :
            E'.posterior q (oz, s) = E.posterior q (oz, r)
        · have hprocessor :=
            markedPosteriorMatchingProcessor_apply_of_pos_of_eq
              q E E' (oz, r) s hclassE' hpost
          have hT : T (oz, r) (oz, s) =
              E'.outcomeMarginal q (oz, s) /
                markedPosteriorClassMass q E' oz
                  (E.posterior q (oz, r)) := by
            simpa [T, payoffPreservingRecordKernel, processor] using hprocessor
          rw [hT]
          rw [show q a *
                (E.K a (oz, r) *
                  (E'.outcomeMarginal q (oz, s) /
                    markedPosteriorClassMass q E' oz
                      (E.posterior q (oz, r)))) =
              (q a * E.K a (oz, r)) *
                (E'.outcomeMarginal q (oz, s) /
                  markedPosteriorClassMass q E' oz
                    (E.posterior q (oz, r))) by ring]
          rw [← posterior_mul_marginal q E.K (oz, r) a]
          change
            (E.outcomeMarginal q (oz, r) *
                E.posterior q (oz, r) a) *
                (E'.outcomeMarginal q (oz, s) /
                  markedPosteriorClassMass q E' oz
                    (E.posterior q (oz, r))) =
              if oz = oz ∧
                  E'.posterior q (oz, s) = E.posterior q (oz, r) then
                (E.outcomeMarginal q (oz, r) *
                    E.posterior q (oz, r) a) *
                  (E'.outcomeMarginal q (oz, s) /
                    markedPosteriorClassMass q E' oz
                      (E.posterior q (oz, r)))
              else 0
          rw [if_pos ⟨rfl, hpost⟩]
        · have hprocessor :=
            markedPosteriorMatchingProcessor_apply_of_pos_of_ne
              q E E' (oz, r) s hclassE' hpost
          have hT : T (oz, r) (oz, s) = 0 := by
            simpa [T, payoffPreservingRecordKernel, processor] using hprocessor
          rw [hT]
          simp [hpost]
      · have hT : T (oz, r) (oy, s) = 0 := by
          simp [T, payoffPreservingRecordKernel, hpay]
        rw [hT]
        simp [hpay]
    · have hmzero : E.outcomeMarginal q (oz, r) = 0 :=
        le_antisymm (le_of_not_gt hm)
          ((E.outcomeMarginal q).nonneg (oz, r))
      have hjointzero : q a * E.K a (oz, r) = 0 := by
        rw [← posterior_mul_marginal q E.K (oz, r) a]
        change E.outcomeMarginal q (oz, r) *
          E.posterior q (oz, r) a = 0
        rw [hmzero]
        ring
      rw [show q a * (E.K a (oz, r) * T (oz, r) (oy, s)) =
          (q a * E.K a (oz, r)) * T (oz, r) (oy, s) by ring]
      rw [hjointzero]
      simp [hmzero]
  have hscaled :
      q a * Channel.postprocess E.K T a (oy, s) =
        ∑ z : O × E.RecordType,
          if oy = z.1 ∧
              E'.posterior q (oy, s) = E.posterior q z then
            (E.outcomeMarginal q z * E.posterior q z a) *
              (E'.outcomeMarginal q (oy, s) /
                markedPosteriorClassMass q E' z.1
                  (E.posterior q z))
          else 0 := by
    change q a * (∑ z : O × E.RecordType,
      E.K a z * T z (oy, s)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _hz
    exact hterm z
  have hscaled_target :
      q a * Channel.postprocess E.K T a (oy, s) =
        q a * E'.K a (oy, s) := by
    rw [hscaled]
    by_cases hmy : 0 < E'.outcomeMarginal q (oy, s)
    · have hclassE' :
          0 < markedPosteriorClassMass q E' oy
            (E'.posterior q (oy, s)) :=
        lt_of_lt_of_le hmy
          (outcomeMarginal_le_markedPosteriorClassMass q E' oy s)
      have hclassEq :
          markedPosteriorClassMass q E oy
              (E'.posterior q (oy, s)) =
            markedPosteriorClassMass q E' oy
              (E'.posterior q (oy, s)) :=
        markedPosteriorClassMass_eq_of_sameMarkedTerminalLaw
          q E E' hsame oy (E'.posterior q (oy, s))
      have hfactor :
          (∑ z : O × E.RecordType,
            if oy = z.1 ∧
                E'.posterior q (oy, s) = E.posterior q z then
              (E.outcomeMarginal q z * E.posterior q z a) *
                (E'.outcomeMarginal q (oy, s) /
                  markedPosteriorClassMass q E' z.1
                    (E.posterior q z))
            else 0) =
            markedPosteriorClassMass q E oy
                (E'.posterior q (oy, s)) *
              (E'.posterior q (oy, s) a *
                (E'.outcomeMarginal q (oy, s) /
                  markedPosteriorClassMass q E' oy
                    (E'.posterior q (oy, s)))) := by
        rw [Fintype.sum_prod_type]
        rw [Finset.sum_eq_single oy]
        · unfold markedPosteriorClassMass
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro r _hr
          by_cases hpost :
              E'.posterior q (oy, s) = E.posterior q (oy, r)
          · simp only [hpost, and_self, ↓reduceIte]
            ring
          · have hpost' :
                E.posterior q (oy, r) ≠ E'.posterior q (oy, s) :=
              fun h => hpost h.symm
            simp [hpost, hpost']
        · intro oz _hoz hne
          have hne' : oy ≠ oz := fun h => hne h.symm
          simp [hne']
        · simp
      rw [hfactor, hclassEq]
      have hclassNe :
          markedPosteriorClassMass q E' oy
            (E'.posterior q (oy, s)) ≠ 0 :=
        ne_of_gt hclassE'
      calc
        markedPosteriorClassMass q E' oy
              (E'.posterior q (oy, s)) *
            (E'.posterior q (oy, s) a *
              (E'.outcomeMarginal q (oy, s) /
                markedPosteriorClassMass q E' oy
                  (E'.posterior q (oy, s)))) =
            E'.outcomeMarginal q (oy, s) *
              E'.posterior q (oy, s) a := by
                field_simp [hclassNe]
        _ = q a * E'.K a (oy, s) :=
          posterior_mul_marginal q E'.K (oy, s) a
    · have hmyzero : E'.outcomeMarginal q (oy, s) = 0 :=
        le_antisymm (le_of_not_gt hmy)
          ((E'.outcomeMarginal q).nonneg (oy, s))
      have hjointzero : q a * E'.K a (oy, s) = 0 := by
        rw [← posterior_mul_marginal q E'.K (oy, s) a]
        change E'.outcomeMarginal q (oy, s) *
          E'.posterior q (oy, s) a = 0
        rw [hmyzero]
        ring
      simp [hmyzero, hjointzero]
  exact (mul_left_cancel₀ (ne_of_gt (hq a)) hscaled_target).symm

theorem sameMarkedTerminalLaw_symm
    {q : TraceableAgency.Dist A}
    {E E' : MarkedTerminalExperiment O A}
    (hsame : SameMarkedTerminalLaw q E E') :
    SameMarkedTerminalLaw q E' E := by
  intro phi
  exact (hsame phi).symm

/-- Equal marked terminal laws at a full-support prior yield
payoff-preserving record simulations in both directions. -/
theorem finiteMarkedBlackwellEquivalence
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E') :
    MarkedExperimentRecordPostprocesses E E' ∧
      MarkedExperimentRecordPostprocesses E' E :=
  ⟨markedExperimentRecordPostprocesses_of_sameMarkedTerminalLaw
      q hq E E' hsame,
    markedExperimentRecordPostprocesses_of_sameMarkedTerminalLaw
      q hq E' E (sameMarkedTerminalLaw_symm hsame)⟩

/-! ## Preference indifference and representative replacement -/

/-- Bundled form of the paper's cross-channel weak comparison.  The wrapper
keeps each experiment's stored record instances internal. -/
def MarkedPairWeak
    (F : FixedPayoffPrefFamily O)
    (q : TraceableAgency.Dist A) (E : MarkedTerminalExperiment O A)
    (r : TraceableAgency.Dist A) (G : MarkedTerminalExperiment O A) : Prop := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  exact pairWeak F q E.K r G.K

/-- A payoff-preserving record simulation gives the corresponding weak block
comparison by A4. -/
theorem pairWeak_of_markedRecordPostprocesses
    (F : FixedPayoffPrefFamily O) (h4 : A4_RecordDataProcessing F)
    (q : TraceableAgency.Dist A)
    (E E' : MarkedTerminalExperiment O A)
    (hpost : MarkedExperimentRecordPostprocesses E E') :
    MarkedPairWeak F q E q E' := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  change pairWeak F q E.K q E'.K
  rcases hpost with ⟨T, hT⟩
  simpa [hT] using h4 E.K T q

/-- The cross-environment indifference relation actually used for replacing
terminal-law representatives: each oriented two-block comparison holds. -/
def MarkedPairIndifferent
    (F : FixedPayoffPrefFamily O) (q : TraceableAgency.Dist A)
    (E E' : MarkedTerminalExperiment O A) : Prop := by
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  exact MarkedPairWeak F q E q E' ∧ MarkedPairWeak F q E' q E

/-- Equal marked terminal laws at full support are indifferent in both
oriented pair comparisons. -/
theorem markedPairIndifferent_of_sameMarkedTerminalLaw
    (F : FixedPayoffPrefFamily O) (h4 : A4_RecordDataProcessing F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E') :
    MarkedPairIndifferent F q E E' := by
  rcases finiteMarkedBlackwellEquivalence q hq E E' hsame with
    ⟨hforward, hback⟩
  exact
    ⟨pairWeak_of_markedRecordPostprocesses F h4 q E E' hforward,
      pairWeak_of_markedRecordPostprocesses F h4 q E' E hback⟩

/-- Four labels used to replace both representatives in a pair comparison. -/
inductive MarkedReplacementBlock : Type u
  | oldLeft
  | newLeft
  | oldRight
  | newRight
  deriving DecidableEq, Fintype

open MarkedReplacementBlock

/-- Record family of the common four-block replacement environment. -/
def markedReplacementRecord
    (E E' G G' : MarkedTerminalExperiment O A) :
    MarkedReplacementBlock → Type u
  | oldLeft => E.RecordType
  | newLeft => E'.RecordType
  | oldRight => G.RecordType
  | newRight => G'.RecordType

/-- A1/A3 four-block transfer: two-sided weak equivalence of each
representative makes the cross-experiment pair comparison independent of the
chosen representatives. -/
theorem marked_pairWeak_replacement_from_weakEquiv
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (q r : TraceableAgency.Dist A)
    (E E' G G' : MarkedTerminalExperiment O A)
    (hleftForward : MarkedPairWeak F q E q E')
    (hleftBackward : MarkedPairWeak F q E' q E)
    (hrightForward : MarkedPairWeak F r G r G')
    (hrightBackward : MarkedPairWeak F r G' r G) :
    MarkedPairWeak F q E r G ↔ MarkedPairWeak F q E' r G' := by
  classical
  let k0 : MarkedReplacementBlock.{u} := oldLeft
  let k1 : MarkedReplacementBlock.{u} := newLeft
  let k2 : MarkedReplacementBlock.{u} := oldRight
  let k3 : MarkedReplacementBlock.{u} := newRight
  let Act : MarkedReplacementBlock → Type u := fun _ => A
  let Rec := markedReplacementRecord E E' G G'
  letI : Nonempty MarkedReplacementBlock := ⟨oldLeft⟩
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype E'.RecordType := E'.recordFintype
  letI : DecidableEq E'.RecordType := E'.recordDecEq
  letI : Nonempty E'.RecordType := E'.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  letI : Fintype G'.RecordType := G'.recordFintype
  letI : DecidableEq G'.RecordType := G'.recordDecEq
  letI : Nonempty G'.RecordType := G'.recordNonempty
  letI : ∀ k, Fintype (Act k) := fun _ => inferInstance
  letI : ∀ k, DecidableEq (Act k) := fun _ => inferInstance
  letI : ∀ k, Nonempty (Act k) := fun _ => inferInstance
  letI : ∀ k, Fintype (Rec k) := fun k => by
    cases k
    · exact E.recordFintype
    · exact E'.recordFintype
    · exact G.recordFintype
    · exact G'.recordFintype
  letI : ∀ k, DecidableEq (Rec k) := fun k => by
    cases k
    · exact E.recordDecEq
    · exact E'.recordDecEq
    · exact G.recordDecEq
    · exact G'.recordDecEq
  letI : ∀ k, Nonempty (Rec k) := fun k => by
    cases k
    · exact E.recordNonempty
    · exact E'.recordNonempty
    · exact G.recordNonempty
    · exact G'.recordNonempty
  let C : ∀ k : MarkedReplacementBlock,
      Channel (Act k) (O × Rec k) := fun k => by
    cases k
    · exact E.K
    · exact E'.K
    · exact G.K
    · exact G'.K
  change pairWeak F q E.K r G.K ↔ pairWeak F q E'.K r G'.K
  change pairWeak F q E.K q E'.K at hleftForward
  change pairWeak F q E'.K q E.K at hleftBackward
  change pairWeak F r G.K r G'.K at hrightForward
  change pairWeak F r G'.K r G.K at hrightBackward
  let commonK := commonPayoffBlockFamilyChannel Act Rec C
  let x := commonPayoffBlockEmbed Act k0 q
  let x' := commonPayoffBlockEmbed Act k1 q
  let y := commonPayoffBlockEmbed Act k2 r
  let y' := commonPayoffBlockEmbed Act k3 r
  have htrans :
      ∀ a b c : TraceableAgency.Dist
          ((k : MarkedReplacementBlock) × Act k),
        F.rel commonK a b → F.rel commonK b c → F.rel commonK a c :=
    (h1 commonK).2
  have h02 : k0 ≠ k2 := by decide
  have h01 : k0 ≠ k1 := by decide
  have h10 : k1 ≠ k0 := by decide
  have h23 : k2 ≠ k3 := by decide
  have h32 : k3 ≠ k2 := by decide
  have h13 : k1 ≠ k3 := by decide
  have hcommon02 :
      F.rel commonK x y ↔ pairWeak F q E.K r G.K := by
    have hh := h3.irrelevant_blocks Act Rec C k0 k2 h02 q r
    change F.rel commonK x y ↔ pairWeak F q (C k0) r (C k2) at hh
    have hc0 : C k0 = E.K := by rfl
    have hc2 : C k2 = G.K := by rfl
    rw [hc0, hc2] at hh
    exact hh
  have hcommon01 : F.rel commonK x x' := by
    have hh :=
      (h3.irrelevant_blocks Act Rec C k0 k1 h01 q q).mpr
        hleftForward
    change F.rel commonK x x' at hh
    exact hh
  have hcommon10 : F.rel commonK x' x := by
    have hh :=
      (h3.irrelevant_blocks Act Rec C k1 k0 h10 q q).mpr
        hleftBackward
    change F.rel commonK x' x at hh
    exact hh
  have hcommon23 : F.rel commonK y y' := by
    have hh :=
      (h3.irrelevant_blocks Act Rec C k2 k3 h23 r r).mpr
        hrightForward
    change F.rel commonK y y' at hh
    exact hh
  have hcommon32 : F.rel commonK y' y := by
    have hh :=
      (h3.irrelevant_blocks Act Rec C k3 k2 h32 r r).mpr
        hrightBackward
    change F.rel commonK y' y at hh
    exact hh
  have hreplace : F.rel commonK x y ↔ F.rel commonK x' y' :=
    rel_replace_by_equiv (fun a b => F.rel commonK a b) htrans
      hcommon01 hcommon10 hcommon23 hcommon32
  have hcommon13 :
      F.rel commonK x' y' ↔ pairWeak F q E'.K r G'.K := by
    have hh := h3.irrelevant_blocks Act Rec C k1 k3 h13 q r
    change F.rel commonK x' y' ↔ pairWeak F q (C k1) r (C k3) at hh
    have hc1 : C k1 = E'.K := by rfl
    have hc3 : C k3 = G'.K := by rfl
    rw [hc1, hc3] at hh
    exact hh
  exact hcommon02.symm.trans (hreplace.trans hcommon13)

/-- Consequently, `pairWeak` is well-defined on full-support marked-terminal
law representatives in both arguments. -/
theorem pairWeak_respects_sameMarkedTerminalLaw
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h3 : A3_BlockComparisonCoherence F)
    (h4 : A4_RecordDataProcessing F)
    (q r : TraceableAgency.Dist A) (hq : q.FullSupport) (hr : r.FullSupport)
    (E E' G G' : MarkedTerminalExperiment O A)
    (hleft : SameMarkedTerminalLaw q E E')
    (hright : SameMarkedTerminalLaw r G G') :
    MarkedPairWeak F q E r G ↔ MarkedPairWeak F q E' r G' := by
  have hEi := markedPairIndifferent_of_sameMarkedTerminalLaw
    F h4 q hq E E' hleft
  have hGi := markedPairIndifferent_of_sameMarkedTerminalLaw
    F h4 r hr G G' hright
  exact marked_pairWeak_replacement_from_weakEquiv F h1 h3 q r E E' G G'
    hEi.1 hEi.2 hGi.1 hGi.2

end TraceableAgency.Theorem1
