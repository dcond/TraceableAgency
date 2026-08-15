/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MarkedHM
import TraceableAgency.Theorem1.NormalizeAffine
import TraceableAgency.Theorem1.PureMIAffine
import TraceableAgency.Theorem1.TraceScaleTools

/-!
# Constant-payoff embedding into marked terminal laws

At a fixed payoff, an ordinary finite experiment is a marked experiment whose
record is the ordinary outcome.  This construction descends from posterior-law
classes to marked-terminal-law classes, preserves public mixtures, and embeds
the mutual-information order into the marked preference order.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- A finite experiment's outcome alphabet is inhabited because any channel
row is a probability distribution on it. -/
theorem finiteExperimentOutcomeNonempty
    (E : FiniteExperimentOn A) : Nonempty E.OutcomeType :=
  @Relabeling.nonempty_of_dist E.OutcomeType E.outFintype
    (E.channel (Classical.choice inferInstance))

/-- Bundle the constant-payoff lift of an ordinary finite experiment as a
marked terminal experiment. -/
noncomputable abbrev constantPayoffMarkedExperiment
    (o : O) (E : FiniteExperimentOn A) :
    MarkedTerminalExperiment O A :=
  { RecordType := E.OutcomeType
    recordFintype := E.outFintype
    recordDecEq := E.outDecEq
    recordNonempty := finiteExperimentOutcomeNonempty E
    channel :=
      @constantPayoffLift O A E.OutcomeType inferInstance inferInstance
        E.outFintype o E.channel }

@[simp]
theorem constantPayoffMarkedExperiment_outcomeMarginal
    (q : TraceableAgency.Dist A) (o o' : O)
    (E : FiniteExperimentOn A) (r : E.OutcomeType) :
    (constantPayoffMarkedExperiment o E).outcomeMarginal q (o', r) =
      if o' = o then E.outcomeMarginal q r else 0 := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  change Channel.outcomeMarginal (constantPayoffLift o E.P) q (o', r) = _
  simp [Channel.outcomeMarginal_apply, FiniteExperimentOn.outcomeMarginal]

@[simp]
theorem constantPayoffMarkedExperiment_posterior_same
    (q : TraceableAgency.Dist A) (o : O)
    (E : FiniteExperimentOn A) (r : E.OutcomeType) :
    (constantPayoffMarkedExperiment o E).posterior q (o, r) =
      E.posterior q r := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  change Channel.posterior (constantPayoffLift o E.P) q (o, r) =
    Channel.posterior E.P q r
  apply TraceableAgency.Dist.ext
  intro a
  unfold Channel.posterior
  have hmarg : Channel.outcomeMarginal
      (constantPayoffLift o E.P) q (o, r) =
        Channel.outcomeMarginal E.P q r := by
    simpa [FiniteExperimentOn.outcomeMarginal] using
      constantPayoffMarkedExperiment_outcomeMarginal q o o E r
  by_cases hp : Channel.outcomeMarginal E.P q r > 0
  · have hp' : Channel.outcomeMarginal
        (constantPayoffLift o E.P) q (o, r) > 0 := by
      simpa [hmarg] using hp
    simp only [dif_pos hp, dif_pos hp']
    simp [constantPayoffLift]
  · have hp' : ¬ Channel.outcomeMarginal
        (constantPayoffLift o E.P) q (o, r) > 0 := by
      simpa [hmarg] using hp
    simp only [dif_neg hp, dif_neg hp']

/-- Integration against a constant-payoff marked law is ordinary
posterior-law integration with the payoff coordinate fixed. -/
theorem markedTerminalIntegral_constantPayoffMarkedExperiment
    (q : TraceableAgency.Dist A) (o : O)
    (E : FiniteExperimentOn A)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q (constantPayoffMarkedExperiment o E) phi =
      posteriorLawIntegralExp q E (fun p ↦ phi (o, p)) := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  unfold markedTerminalIntegral posteriorLawIntegralExp
  rw [Fintype.sum_prod_type, Finset.sum_eq_single o]
  · apply Finset.sum_congr rfl
    intro r _hr
    rw [constantPayoffMarkedExperiment_outcomeMarginal,
      if_pos rfl, constantPayoffMarkedExperiment_posterior_same]
  · intro o' _ho' hne
    have hmargZero : ∀ r : E.OutcomeType,
        (constantPayoffMarkedExperiment o E).outcomeMarginal q (o', r) = 0 := by
      intro r
      rw [constantPayoffMarkedExperiment_outcomeMarginal, if_neg hne]
    simp_rw [hmargZero, zero_mul, Finset.sum_const_zero]
  · simp

/-- Equality of ordinary posterior laws implies equality of their
constant-payoff marked terminal laws. -/
theorem sameMarkedTerminalLaw_constantPayoffMarkedExperiment
    (q : TraceableAgency.Dist A) (o : O)
    (E G : FiniteExperimentOn A)
    (hsame : SamePosteriorLawExp q E G) :
    SameMarkedTerminalLaw q
      (constantPayoffMarkedExperiment o E)
      (constantPayoffMarkedExperiment o G) := by
  intro phi
  rw [markedTerminalIntegral_constantPayoffMarkedExperiment,
    markedTerminalIntegral_constantPayoffMarkedExperiment]
  exact samePosteriorLawExp_all_test_functions q E G hsame
    (fun p ↦ phi (o, p))

/-- The constant-payoff construction descended to posterior-law classes. -/
noncomputable def constantPayoffMarkedEmbedding
    (q : TraceableAgency.Dist A) (o : O) :
    PosteriorLawMixtureSpace q →
      MarkedTerminalMixtureSpace (O := O) (A := A) q :=
  Quotient.map (constantPayoffMarkedExperiment o)
    (fun {_ _} hsame ↦
      sameMarkedTerminalLaw_constantPayoffMarkedExperiment q o _ _ hsame)

@[simp]
theorem constantPayoffMarkedEmbedding_mk
    (q : TraceableAgency.Dist A) (o : O)
    (E : FiniteExperimentOn A) :
    constantPayoffMarkedEmbedding q o ⟦E⟧ =
      (⟦constantPayoffMarkedExperiment o E⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) q) := by
  rfl

/-- The bundled constant-payoff construction and the concrete marked public
mixture have the same marked terminal law. -/
theorem sameMarkedTerminalLaw_constantPayoff_publicMix
    (q : TraceableAgency.Dist A) (o : O)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E G : FiniteExperimentOn A) :
    SameMarkedTerminalLaw q
      (constantPayoffMarkedExperiment o
        (hmPublicMixExperiment t ht0 ht1 E G))
      (markedPublicMixExperiment t ht0 ht1
        (constantPayoffMarkedExperiment o E)
        (constantPayoffMarkedExperiment o G)) := by
  intro phi
  rw [markedTerminalIntegral_constantPayoffMarkedExperiment,
    hm_posteriorLawIntegral_publicMixExperiment,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_constantPayoffMarkedExperiment,
    markedTerminalIntegral_constantPayoffMarkedExperiment]

/-- The quotient embedding is affine: it commutes exactly with the abstract
public-mixture operations. -/
theorem constantPayoffMarkedEmbedding_mix
    (q : TraceableAgency.Dist A) (o : O)
    (t : Set.Ioo (0 : ℝ) 1) (x y : PosteriorLawMixtureSpace q) :
    constantPayoffMarkedEmbedding q o
        ((posteriorLawAbstractConvexMixtureSpace q).mix t x y) =
      (markedTerminalAbstractConvexMixtureSpace q).mix t
        (constantPayoffMarkedEmbedding q o x)
        (constantPayoffMarkedEmbedding q o y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      apply Quotient.sound
      exact sameMarkedTerminalLaw_constantPayoff_publicMix
        q o t.1 t.2.1 t.2.2 E G

/-- At the v5 trace anchor, the constant-payoff affine map is an order
embedding of the mutual-information order into the marked-terminal order. -/
theorem constantPayoffMarkedEmbedding_order_iff
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y : PosteriorLawMixtureSpace q) :
    pureMIRel q x y ↔
      markedTerminalMixtureRel F h q hq
        (constantPayoffMarkedEmbedding q h.traceAnchor x)
        (constantPayoffMarkedEmbedding q h.traceAnchor y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      letI : Fintype E.OutcomeType := E.outFintype
      letI : DecidableEq E.OutcomeType := E.outDecEq
      letI : Nonempty E.OutcomeType :=
        Relabeling.nonempty_of_dist (E.P (Classical.choice inferInstance))
      letI : Fintype G.OutcomeType := G.outFintype
      letI : DecidableEq G.OutcomeType := G.outDecEq
      letI : Nonempty G.OutcomeType :=
        Relabeling.nonempty_of_dist (G.P (Classical.choice inferInstance))
      change mutualInfo q E.P ≥ mutualInfo q G.P ↔
        pairWeak F q (constantPayoffLift h.traceAnchor E.P)
          q (constantPayoffLift h.traceAnchor G.P)
      exact (constantPayoff_pairWeak_iff_mutualInfo
        F h q E.P q G.P).symm

/-- Pull the marked Herstein--Milnor representative back through the fixed
payoff affine order embedding. -/
noncomputable def constantPayoffMarkedPullbackAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (posteriorLawAbstractConvexMixtureSpace q) (pureMIRel q) :=
  pullbackAffineUtility
    (posteriorLawAbstractConvexMixtureSpace q)
    (markedTerminalAbstractConvexMixtureSpace q)
    (pureMIRel q) (markedTerminalMixtureRel F h q hq)
    (markedTerminalAffineUtilityRepresentation F h q hq)
    (constantPayoffMarkedEmbedding q h.traceAnchor)
    (constantPayoffMarkedEmbedding_order_iff F h q hq)
    (constantPayoffMarkedEmbedding_mix q h.traceAnchor)

end TraceableAgency.Theorem1
