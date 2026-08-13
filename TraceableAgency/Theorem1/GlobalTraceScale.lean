/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.CommonMarkedScale
import TraceableAgency.Theorem1.PureMIAffine
import TraceableAgency.Theorem1.PureMarkedEmbedding

/-!
# A single trace scale on all nontrivial full-support fibres

The normalized marked-terminal representative is pulled back through the
constant-payoff embedding at the separate v4 trace anchor.  Affine uniqueness
identifies the intercept as the normalized material value of that anchor and
the slope as a positive multiple of mutual information.  Exact normalization
under independent dummy actions then identifies the multiplier across all
nontrivial full-support finite action alphabets.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A B : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]

/-! ## The normalized fixed-payoff pullback -/

/-- Pull the normalized marked representative back to the pure posterior-law
space at the v4 trace anchor. -/
noncomputable def normalizedConstantTraceAnchorPullbackAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (posteriorLawAbstractConvexMixtureSpace q) (pureMIRel q) :=
  pullbackAffineUtility
    (posteriorLawAbstractConvexMixtureSpace q)
    (markedTerminalAbstractConvexMixtureSpace q)
    (pureMIRel q) (markedTerminalMixtureRel F h q hq)
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (constantPayoffMarkedEmbedding q h.traceAnchor)
    (constantPayoffMarkedEmbedding_order_iff F h q hq)
    (constantPayoffMarkedEmbedding_mix q h.traceAnchor)

/-- The trace-anchor lift of the uninformative experiment has the same marked
terminal law as the degenerate trace-anchor payoff lottery. -/
theorem sameMarkedTerminalLaw_constantTraceAnchor_uninformative
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) :
    SameMarkedTerminalLaw q
      (constantPayoffMarkedExperiment (h.traceAnchor)
        (uninformativeExperiment A))
      (markedPayoffLotteryExperiment (A := A)
        (TraceableAgency.Dist.pure h.traceAnchor)) := by
  intro phi
  rw [markedTerminalIntegral_constantPayoffMarkedExperiment]
  change posteriorLawIntegralExp q
      (experimentOfChannel (Channel.uninformativeChannelU A))
        (fun p => phi (h.traceAnchor, p)) = _
  rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior,
    markedTerminalIntegral_markedPayoffLottery]
  unfold payoffLotteryExpected
  simp [TraceableAgency.Dist.pure_apply]

/-- Zero information identifies the affine intercept as the normalized
material utility of the trace anchor. -/
theorem normalizedConstantTraceAnchor_uninformative_eq_materialUtility
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    normalizedMarkedUtility F h q hq
      (constantPayoffMarkedExperiment (h.traceAnchor)
        (uninformativeExperiment A)) =
      materialPayoffUtility F h h.traceAnchor := by
  calc
    normalizedMarkedUtility F h q hq
        (constantPayoffMarkedExperiment (h.traceAnchor)
          (uninformativeExperiment A)) =
        normalizedMarkedUtility F h q hq
          (markedPayoffLotteryExperiment (A := A)
            (TraceableAgency.Dist.pure h.traceAnchor)) :=
      normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _
        (sameMarkedTerminalLaw_constantTraceAnchor_uninformative F h q)
    _ = materialPayoffUtility F h h.traceAnchor := by
      have hv := normalizedMarkedUtility_payoffLottery
        (A := A) F h q hq (TraceableAgency.Dist.pure h.traceAnchor)
      rw [expectedPayoffUtility_payoffLotteryChannel] at hv
      simpa [payoffLotteryExpected, TraceableAgency.Dist.pure_apply] using hv

/-- On a nontrivial full-support fibre, normalized marked utility at the
trace anchor is its material intercept plus a positive multiple of mutual
information. -/
theorem normalizedConstantTraceAnchor_positiveMultiple_exists
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] :
    ∃ a : ℝ, 0 < a ∧
      ∀ x : PosteriorLawMixtureSpace q,
        (normalizedConstantTraceAnchorPullbackAffineUtilityRepresentation
          F h q hq).utility x =
            materialPayoffUtility F h h.traceAnchor +
              a * pureMIUtility q x := by
  obtain ⟨a, b, ha, hab⟩ :=
    affineUtilityRepresentation_positiveAffine_unique
      (posteriorLawAbstractConvexMixtureSpace q) (pureMIRel q)
      (pureMIAffineUtilityRepresentation q)
      (normalizedConstantTraceAnchorPullbackAffineUtilityRepresentation F h q hq)
      (pureMIAffineUtility_nonconstant q hq)
  let x0 : PosteriorLawMixtureSpace q := ⟦uninformativeExperiment A⟧
  have hzero := hab x0
  have hb : b = materialPayoffUtility F h h.traceAnchor := by
    change
      normalizedMarkedUtility F h q hq
          (constantPayoffMarkedExperiment (h.traceAnchor)
            (uninformativeExperiment A)) =
        a * mutualInfo q (Channel.uninformativeChannelU A) + b at hzero
    rw [normalizedConstantTraceAnchor_uninformative_eq_materialUtility,
      mutualInfo_uninformativeChannelU] at hzero
    linarith
  refine ⟨a, ha, ?_⟩
  intro x
  rw [hab x, hb]
  simp [pureMIAffineUtilityRepresentation]
  ring

/-- The positive mutual-information coefficient on one full-support fibre. -/
noncomputable def traceLambdaAtPrior
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] : ℝ :=
  Classical.choose (normalizedConstantTraceAnchor_positiveMultiple_exists F h q hq)

theorem traceLambdaAtPrior_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] :
    0 < traceLambdaAtPrior F h q hq :=
  (Classical.choose_spec
    (normalizedConstantTraceAnchor_positiveMultiple_exists F h q hq)).1

theorem normalizedConstantTraceAnchor_eq_traceLambdaAtPrior_mul_pureMI
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (x : PosteriorLawMixtureSpace q) :
    (normalizedConstantTraceAnchorPullbackAffineUtilityRepresentation
      F h q hq).utility x =
      materialPayoffUtility F h h.traceAnchor +
        traceLambdaAtPrior F h q hq * pureMIUtility q x :=
  (Classical.choose_spec
    (normalizedConstantTraceAnchor_positiveMultiple_exists F h q hq)).2 x

theorem normalizedMarkedUtility_constantTraceAnchor_eq_traceLambdaAtPrior_mul_mutualInfo
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (E : FiniteExperimentOn A) :
    normalizedMarkedUtility F h q hq
        (constantPayoffMarkedExperiment (h.traceAnchor) E) =
      materialPayoffUtility F h h.traceAnchor +
        traceLambdaAtPrior F h q hq *
        @mutualInfo A E.OutcomeType _ E.outFintype q E.P := by
  simpa [normalizedConstantTraceAnchorPullbackAffineUtilityRepresentation,
    pullbackAffineUtility, normalizedMarkedUtility] using
      normalizedConstantTraceAnchor_eq_traceLambdaAtPrior_mul_pureMI
        F h q hq (⟦E⟧ : PosteriorLawMixtureSpace q)

/-! ## Pure dummy lifts and mutual information -/

/-- Adjoin an independent right action coordinate to an ordinary finite
experiment while keeping exactly the same outcome alphabet. -/
noncomputable def pureIndependentDummyExperiment
    (E : FiniteExperimentOn A) : FiniteExperimentOn (A × B) where
  OutcomeType := E.OutcomeType
  outFintype := E.outFintype
  outDecEq := E.outDecEq
  channel := fun ab => E.P ab.1

/-- The right-coordinate version of `pureIndependentDummyExperiment`. -/
noncomputable def pureRightIndependentDummyExperiment
    (E : FiniteExperimentOn B) : FiniteExperimentOn (A × B) where
  OutcomeType := E.OutcomeType
  outFintype := E.outFintype
  outDecEq := E.outDecEq
  channel := fun ab => E.P ab.2

/-- Mutual information is unchanged when an independent ignored right action
coordinate is added. -/
theorem mutualInfo_pureIndependentDummyExperiment
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (E : FiniteExperimentOn A) :
    @mutualInfo (A × B) E.OutcomeType _ E.outFintype (prodDist q r)
        (pureIndependentDummyExperiment (B := B) E).P =
      @mutualInfo A E.OutcomeType _ E.outFintype q E.P := by
  letI : Fintype E.OutcomeType := E.outFintype
  change mutualInfo (prodDist q r) (fun ab => E.P ab.1) =
    mutualInfo q E.P
  unfold mutualInfo
  have hout : Channel.outcomeMarginal (fun ab : A × B => E.P ab.1)
      (prodDist q r) = Channel.outcomeMarginal E.P q := by
    ext z
    simp only [Channel.outcomeMarginal_apply]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _ha
    calc
      (∑ b, prodDist q r (a, b) * E.P a z) =
          q a * E.P a z * ∑ b, r b := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        simp only [prodDist_apply_pair]
        ring
      _ = q a * E.P a z := by rw [r.sum_eq_one, mul_one]
  rw [hout]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∑ b, prodDist q r (a, b) * entropy (E.P a)) =
        q a * entropy (E.P a) * ∑ b, r b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [prodDist_apply_pair]
      ring
    _ = q a * entropy (E.P a) := by rw [r.sum_eq_one, mul_one]

/-- Mutual information is unchanged when an independent ignored left action
coordinate is added. -/
theorem mutualInfo_pureRightIndependentDummyExperiment
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (E : FiniteExperimentOn B) :
    @mutualInfo (A × B) E.OutcomeType _ E.outFintype (prodDist q r)
        (pureRightIndependentDummyExperiment (A := A) E).P =
      @mutualInfo B E.OutcomeType _ E.outFintype r E.P := by
  letI : Fintype E.OutcomeType := E.outFintype
  change mutualInfo (prodDist q r) (fun ab => E.P ab.2) =
    mutualInfo r E.P
  unfold mutualInfo
  have hout : Channel.outcomeMarginal (fun ab : A × B => E.P ab.2)
      (prodDist q r) = Channel.outcomeMarginal E.P r := by
    ext z
    simp only [Channel.outcomeMarginal_apply]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _hb
    calc
      (∑ a, prodDist q r (a, b) * E.P b z) =
          (∑ a, q a) * (r b * E.P b z) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _ha
        simp only [prodDist_apply_pair]
        ring
      _ = r b * E.P b z := by rw [q.sum_eq_one, one_mul]
  rw [hout]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  calc
    (∑ a, prodDist q r (a, b) * entropy (E.P b)) =
        (∑ a, q a) * (r b * entropy (E.P b)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [prodDist_apply_pair]
      ring
    _ = r b * entropy (E.P b) := by rw [q.sum_eq_one, one_mul]

/-- Dummy lifting commutes with the constant-payoff marked construction. -/
theorem independentDummyMarkedExperiment_constantPayoff
    (o : O) (E : FiniteExperimentOn A) :
    independentDummyMarkedExperiment (B := B)
        (constantPayoffMarkedExperiment o E) =
      constantPayoffMarkedExperiment o
        (pureIndependentDummyExperiment (B := B) E) := by
  rfl

/-- Right dummy lifting commutes with the constant-payoff marked
construction. -/
theorem rightIndependentDummyMarkedExperiment_constantPayoff
    (o : O) (E : FiniteExperimentOn B) :
    rightIndependentDummyMarkedExperiment (A := A)
        (constantPayoffMarkedExperiment o E) =
      constantPayoffMarkedExperiment o
        (pureRightIndependentDummyExperiment (A := A) E) := by
  rfl

/-! ## Equality of all fibre coefficients -/

/-- Passing from a nontrivial fibre to a product fibre by adjoining a right
dummy preserves its positive mutual-information coefficient. -/
theorem traceLambdaAtPrior_prod_left
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport) [Nontrivial A] :
    traceLambdaAtPrior F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) =
      traceLambdaAtPrior F h q hq := by
  let E : FiniteExperimentOn A :=
    FiniteExperimentOn.ofChannel (Channel.idChannel : Channel A A)
  letI : Fintype E.OutcomeType := E.outFintype
  let ED : FiniteExperimentOn (A × B) :=
    pureIndependentDummyExperiment (B := B) E
  have hsource :=
    normalizedMarkedUtility_constantTraceAnchor_eq_traceLambdaAtPrior_mul_mutualInfo
      F h q hq E
  have htarget :=
    normalizedMarkedUtility_constantTraceAnchor_eq_traceLambdaAtPrior_mul_mutualInfo
      F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) ED
  have hpreserve := normalizedMarkedUtility_independentDummy
    F h q r hq hr
      (constantPayoffMarkedExperiment (h.traceAnchor) E)
  rw [independentDummyMarkedExperiment_constantPayoff] at hpreserve
  rw [htarget, hsource] at hpreserve
  have hmi :
      @mutualInfo (A × B) ED.OutcomeType _ ED.outFintype (prodDist q r) ED.P =
        @mutualInfo A E.OutcomeType _ E.outFintype q E.P := by
    dsimp only [ED]
    exact mutualInfo_pureIndependentDummyExperiment (B := B) q r E
  rw [hmi] at hpreserve
  have hmiId : mutualInfo q E.P = entropy q := by
    dsimp only [E, FiniteExperimentOn.ofChannel]
    exact mutualInfo_idChannel' q
  rw [hmiId] at hpreserve
  have hentropy : 0 < entropy q :=
    entropy_pos_of_fullSupport_nontrivial q hq
  nlinarith

/-- Passing from a nontrivial right-coordinate fibre to the same product
fibre preserves its coefficient. -/
theorem traceLambdaAtPrior_prod_right
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport) [Nontrivial B] :
    traceLambdaAtPrior F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) =
      traceLambdaAtPrior F h r hr := by
  let E : FiniteExperimentOn B :=
    FiniteExperimentOn.ofChannel (Channel.idChannel : Channel B B)
  letI : Fintype E.OutcomeType := E.outFintype
  let ED : FiniteExperimentOn (A × B) :=
    pureRightIndependentDummyExperiment (A := A) E
  have hsource :=
    normalizedMarkedUtility_constantTraceAnchor_eq_traceLambdaAtPrior_mul_mutualInfo
      F h r hr E
  have htarget :=
    normalizedMarkedUtility_constantTraceAnchor_eq_traceLambdaAtPrior_mul_mutualInfo
      F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) ED
  have hpreserve := normalizedMarkedUtility_rightIndependentDummy
    F h q r hq hr
      (constantPayoffMarkedExperiment (h.traceAnchor) E)
  rw [rightIndependentDummyMarkedExperiment_constantPayoff] at hpreserve
  rw [htarget, hsource] at hpreserve
  have hmi :
      @mutualInfo (A × B) ED.OutcomeType _ ED.outFintype (prodDist q r) ED.P =
        @mutualInfo B E.OutcomeType _ E.outFintype r E.P := by
    dsimp only [ED]
    exact mutualInfo_pureRightIndependentDummyExperiment (A := A) q r E
  rw [hmi] at hpreserve
  have hmiId : mutualInfo r E.P = entropy r := by
    dsimp only [E, FiniteExperimentOn.ofChannel]
    exact mutualInfo_idChannel' r
  rw [hmiId] at hpreserve
  have hentropy : 0 < entropy r :=
    entropy_pos_of_fullSupport_nontrivial r hr
  nlinarith

/-! ## The single universe-polymorphic reference coefficient -/

/-- A fixed two-action reference alphabet living in the ambient universe. -/
abbrev TraceReferenceAction : Type u := ULift.{u, 0} Bool

/-- The fixed full-support reference prior. -/
noncomputable def traceReferencePrior :
    TraceableAgency.Dist TraceReferenceAction.{u} :=
  TraceableAgency.Dist.uniform

theorem traceReferencePrior_fullSupport :
    (traceReferencePrior.{u}).FullSupport :=
  TraceableAgency.Dist.uniform_fullSupport

/-- The single trace multiplier, fixed on the uniform lifted-Bool fibre. -/
noncomputable def globalTraceLambda
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor) : ℝ :=
  traceLambdaAtPrior F h traceReferencePrior.{u}
    traceReferencePrior_fullSupport.{u}

theorem globalTraceLambda_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor) :
    0 < globalTraceLambda F h :=
  traceLambdaAtPrior_pos F h traceReferencePrior.{u}
    traceReferencePrior_fullSupport.{u}

/-- Every nontrivial full-support finite fibre has the reference coefficient. -/
theorem traceLambdaAtPrior_eq_globalTraceLambda
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] :
    traceLambdaAtPrior F h q hq = globalTraceLambda F h := by
  let r : TraceableAgency.Dist TraceReferenceAction.{u} :=
    traceReferencePrior.{u}
  have hr : r.FullSupport := traceReferencePrior_fullSupport.{u}
  exact
    (traceLambdaAtPrior_prod_left F h q r hq hr).symm.trans
      (traceLambdaAtPrior_prod_right F h q r hq hr)

/-- Quotient-level global trace formula at the separate v4 trace anchor. -/
theorem normalizedConstantTraceAnchor_eq_globalTraceLambda_mul_pureMI
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (x : PosteriorLawMixtureSpace q) :
    (normalizedConstantTraceAnchorPullbackAffineUtilityRepresentation
      F h q hq).utility x =
      materialPayoffUtility F h h.traceAnchor +
        globalTraceLambda F h * pureMIUtility q x := by
  rw [normalizedConstantTraceAnchor_eq_traceLambdaAtPrior_mul_pureMI,
    traceLambdaAtPrior_eq_globalTraceLambda]

/-- Raw-experiment global trace formula at the separate v4 trace anchor. -/
theorem normalizedMarkedUtility_constantTraceAnchor_eq_globalTraceLambda_mul_mutualInfo
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (E : FiniteExperimentOn A) :
    normalizedMarkedUtility F h q hq
        (constantPayoffMarkedExperiment (h.traceAnchor) E) =
      materialPayoffUtility F h h.traceAnchor +
        globalTraceLambda F h *
        @mutualInfo A E.OutcomeType _ E.outFintype q E.P := by
  rw [normalizedMarkedUtility_constantTraceAnchor_eq_traceLambdaAtPrior_mul_mutualInfo,
    traceLambdaAtPrior_eq_globalTraceLambda]

end TraceableAgency.Theorem1
