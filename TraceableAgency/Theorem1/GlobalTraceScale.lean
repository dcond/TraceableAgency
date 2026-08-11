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
constant-low-payoff embedding.  Affine uniqueness identifies that pullback
with a positive multiple of mutual information, with zero intercept.  Exact
normalization under independent dummy actions then identifies the multiplier
across all nontrivial full-support finite action alphabets.
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
space at the chosen low material payoff. -/
noncomputable def normalizedConstantLowPullbackAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (posteriorLawAbstractConvexMixtureSpace q) (pureMIRel q) :=
  pullbackAffineUtility
    (posteriorLawAbstractConvexMixtureSpace q)
    (markedTerminalAbstractConvexMixtureSpace q)
    (pureMIRel q) (markedTerminalMixtureRel F h q hq)
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (constantPayoffMarkedEmbedding q (materialLowOutcome F h))
    (constantPayoffMarkedEmbedding_order_iff F h q hq
      (materialLowOutcome F h))
    (constantPayoffMarkedEmbedding_mix q (materialLowOutcome F h))

/-- The constant-low lift of the uninformative experiment has the same marked
terminal law as the degenerate low-payoff lottery. -/
theorem sameMarkedTerminalLaw_constantLow_uninformative
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) :
    SameMarkedTerminalLaw q
      (constantPayoffMarkedExperiment (materialLowOutcome F h)
        (uninformativeExperiment A))
      (markedMaterialLowExperiment (A := A) F h) := by
  intro phi
  rw [markedTerminalIntegral_constantPayoffMarkedExperiment]
  change posteriorLawIntegralExp q
      (experimentOfChannel (Channel.uninformativeChannelU A))
        (fun p => phi (materialLowOutcome F h, p)) = _
  rw [posteriorLawIntegralExp_uninformativeChannelU_eq_prior,
    markedTerminalIntegral_markedPayoffLottery]
  unfold payoffLotteryExpected
  simp [TraceableAgency.Dist.pure_apply]

/-- Zero information and the low-payoff normalization identify the additive
constant in affine uniqueness as zero. -/
theorem normalizedConstantLow_uninformative_eq_zero
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    normalizedMarkedUtility F h q hq
      (constantPayoffMarkedExperiment (materialLowOutcome F h)
        (uninformativeExperiment A)) = 0 := by
  calc
    normalizedMarkedUtility F h q hq
        (constantPayoffMarkedExperiment (materialLowOutcome F h)
          (uninformativeExperiment A)) =
        normalizedMarkedUtility F h q hq
          (markedMaterialLowExperiment (A := A) F h) :=
      normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq _ _
        (sameMarkedTerminalLaw_constantLow_uninformative F h q)
    _ = 0 := normalizedMarkedUtility_low F h q hq

/-- On a nontrivial full-support fibre, normalized marked utility at the
chosen constant low payoff is a positive multiple of mutual information. -/
theorem normalizedConstantLow_positiveMultiple_exists
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] :
    ∃ a : ℝ, 0 < a ∧
      ∀ x : PosteriorLawMixtureSpace q,
        (normalizedConstantLowPullbackAffineUtilityRepresentation
          F h q hq).utility x = a * pureMIUtility q x := by
  obtain ⟨a, b, ha, hab⟩ :=
    affineUtilityRepresentation_positiveAffine_unique
      (posteriorLawAbstractConvexMixtureSpace q) (pureMIRel q)
      (pureMIAffineUtilityRepresentation q)
      (normalizedConstantLowPullbackAffineUtilityRepresentation F h q hq)
      (pureMIAffineUtility_nonconstant q hq)
  let x0 : PosteriorLawMixtureSpace q := ⟦uninformativeExperiment A⟧
  have hzero := hab x0
  have hb : b = 0 := by
    change
      normalizedMarkedUtility F h q hq
          (constantPayoffMarkedExperiment (materialLowOutcome F h)
            (uninformativeExperiment A)) =
        a * mutualInfo q (Channel.uninformativeChannelU A) + b at hzero
    rw [normalizedConstantLow_uninformative_eq_zero,
      mutualInfo_uninformativeChannelU] at hzero
    linarith
  refine ⟨a, ha, ?_⟩
  intro x
  rw [hab x, hb]
  simp [pureMIAffineUtilityRepresentation]

/-- The positive mutual-information coefficient on one full-support fibre. -/
noncomputable def traceLambdaAtPrior
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] : ℝ :=
  Classical.choose (normalizedConstantLow_positiveMultiple_exists F h q hq)

theorem traceLambdaAtPrior_pos
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] :
    0 < traceLambdaAtPrior F h q hq :=
  (Classical.choose_spec
    (normalizedConstantLow_positiveMultiple_exists F h q hq)).1

theorem normalizedConstantLow_eq_traceLambdaAtPrior_mul_pureMI
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (x : PosteriorLawMixtureSpace q) :
    (normalizedConstantLowPullbackAffineUtilityRepresentation
      F h q hq).utility x =
      traceLambdaAtPrior F h q hq * pureMIUtility q x :=
  (Classical.choose_spec
    (normalizedConstantLow_positiveMultiple_exists F h q hq)).2 x

theorem normalizedMarkedUtility_constantLow_eq_traceLambdaAtPrior_mul_mutualInfo
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (E : FiniteExperimentOn A) :
    normalizedMarkedUtility F h q hq
        (constantPayoffMarkedExperiment (materialLowOutcome F h) E) =
      traceLambdaAtPrior F h q hq *
        @mutualInfo A E.OutcomeType _ E.outFintype q E.P := by
  simpa [normalizedConstantLowPullbackAffineUtilityRepresentation,
    pullbackAffineUtility, normalizedMarkedUtility] using
      normalizedConstantLow_eq_traceLambdaAtPrior_mul_pureMI
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
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport) [Nontrivial A] :
    traceLambdaAtPrior F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) =
      traceLambdaAtPrior F h q hq := by
  let E : FiniteExperimentOn A :=
    FiniteExperimentOn.ofChannel (Channel.idChannel : Channel A A)
  let ED : FiniteExperimentOn (A × B) :=
    pureIndependentDummyExperiment (B := B) E
  have hsource :=
    normalizedMarkedUtility_constantLow_eq_traceLambdaAtPrior_mul_mutualInfo
      F h q hq E
  have htarget :=
    normalizedMarkedUtility_constantLow_eq_traceLambdaAtPrior_mul_mutualInfo
      F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) ED
  have hpreserve := normalizedMarkedUtility_independentDummy
    F h q r hq hr
      (constantPayoffMarkedExperiment (materialLowOutcome F h) E)
  rw [independentDummyMarkedExperiment_constantPayoff] at hpreserve
  rw [htarget, hsource] at hpreserve
  have hmi :
      @mutualInfo (A × B) ED.OutcomeType _ ED.outFintype (prodDist q r) ED.P =
        @mutualInfo A E.OutcomeType _ E.outFintype q E.P := by
    dsimp only [ED]
    exact mutualInfo_pureIndependentDummyExperiment (B := B) q r E
  rw [hmi] at hpreserve
  change traceLambdaAtPrior F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr) *
        mutualInfo q (Channel.idChannel : Channel A A) =
    traceLambdaAtPrior F h q hq *
      mutualInfo q (Channel.idChannel : Channel A A) at hpreserve
  rw [mutualInfo_idChannel'] at hpreserve
  have hentropy : 0 < entropy q :=
    entropy_pos_of_fullSupport_nontrivial q hq
  nlinarith

/-- Passing from a nontrivial right-coordinate fibre to the same product
fibre preserves its coefficient. -/
theorem traceLambdaAtPrior_prod_right
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (r : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hr : r.FullSupport) [Nontrivial B] :
    traceLambdaAtPrior F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) =
      traceLambdaAtPrior F h r hr := by
  let E : FiniteExperimentOn B :=
    FiniteExperimentOn.ofChannel (Channel.idChannel : Channel B B)
  let ED : FiniteExperimentOn (A × B) :=
    pureRightIndependentDummyExperiment (A := A) E
  have hsource :=
    normalizedMarkedUtility_constantLow_eq_traceLambdaAtPrior_mul_mutualInfo
      F h r hr E
  have htarget :=
    normalizedMarkedUtility_constantLow_eq_traceLambdaAtPrior_mul_mutualInfo
      F h (prodDist q r)
        (markedDummy_prodDist_fullSupport q r hq hr) ED
  have hpreserve := normalizedMarkedUtility_rightIndependentDummy
    F h q r hq hr
      (constantPayoffMarkedExperiment (materialLowOutcome F h) E)
  rw [rightIndependentDummyMarkedExperiment_constantPayoff] at hpreserve
  rw [htarget, hsource] at hpreserve
  have hmi :
      @mutualInfo (A × B) ED.OutcomeType _ ED.outFintype (prodDist q r) ED.P =
        @mutualInfo B E.OutcomeType _ E.outFintype r E.P := by
    dsimp only [ED]
    exact mutualInfo_pureRightIndependentDummyExperiment (A := A) q r E
  rw [hmi] at hpreserve
  change traceLambdaAtPrior F h (prodDist q r)
      (markedDummy_prodDist_fullSupport q r hq hr) *
        mutualInfo r (Channel.idChannel : Channel B B) =
    traceLambdaAtPrior F h r hr *
      mutualInfo r (Channel.idChannel : Channel B B) at hpreserve
  rw [mutualInfo_idChannel'] at hpreserve
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
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) : ℝ :=
  traceLambdaAtPrior F h traceReferencePrior.{u}
    traceReferencePrior_fullSupport.{u}

theorem globalTraceLambda_pos
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    0 < globalTraceLambda F h :=
  traceLambdaAtPrior_pos F h traceReferencePrior.{u}
    traceReferencePrior_fullSupport.{u}

/-- Every nontrivial full-support finite fibre has the reference coefficient. -/
theorem traceLambdaAtPrior_eq_globalTraceLambda
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A] :
    traceLambdaAtPrior F h q hq = globalTraceLambda F h := by
  let r : TraceableAgency.Dist TraceReferenceAction.{u} :=
    traceReferencePrior.{u}
  have hr : r.FullSupport := traceReferencePrior_fullSupport.{u}
  exact
    (traceLambdaAtPrior_prod_left F h q r hq hr).symm.trans
      (traceLambdaAtPrior_prod_right F h q r hq hr)

/-- Quotient-level global trace formula at the chosen low material payoff. -/
theorem normalizedConstantLow_eq_globalTraceLambda_mul_pureMI
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (x : PosteriorLawMixtureSpace q) :
    (normalizedConstantLowPullbackAffineUtilityRepresentation
      F h q hq).utility x =
      globalTraceLambda F h * pureMIUtility q x := by
  rw [normalizedConstantLow_eq_traceLambdaAtPrior_mul_pureMI,
    traceLambdaAtPrior_eq_globalTraceLambda]

/-- Raw-experiment global trace formula at the chosen low material payoff. -/
theorem normalizedMarkedUtility_constantLow_eq_globalTraceLambda_mul_mutualInfo
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) [Nontrivial A]
    (E : FiniteExperimentOn A) :
    normalizedMarkedUtility F h q hq
        (constantPayoffMarkedExperiment (materialLowOutcome F h) E) =
      globalTraceLambda F h *
        @mutualInfo A E.OutcomeType _ E.outFintype q E.P := by
  rw [normalizedMarkedUtility_constantLow_eq_traceLambdaAtPrior_mul_mutualInfo,
    traceLambdaAtPrior_eq_globalTraceLambda]

end TraceableAgency.Theorem1
