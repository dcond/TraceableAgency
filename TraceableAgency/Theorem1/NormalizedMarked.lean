/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MarkedHM
import TraceableAgency.Theorem1.MaterialUtility

/-!
# A common normalization for fixed-prior marked-terminal utility

The arbitrary affine representative on the marked-terminal quotient is
normalized at the material high/low outcomes selected by A7.  Payoff lotteries
embed affinely and order-reflectingly into this quotient, so affine uniqueness
identifies the restriction of the normalized marked utility with the common
material expected-utility scale.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## The payoff-lottery affine embedding -/

/-- Bundle an action-independent payoff lottery as a marked terminal
experiment with its unique uninformative record. -/
noncomputable abbrev markedPayoffLotteryExperiment
    (ell : TraceableAgency.Dist O) : MarkedTerminalExperiment O A :=
  { RecordType := PUnit.{u + 1}
    recordFintype := inferInstance
    recordDecEq := inferInstance
    recordNonempty := inferInstance
    channel := payoffLotteryChannel ell }

/-- A payoff lottery's marked-terminal integral is ordinary expectation of
the test at the unchanged prior. -/
theorem markedTerminalIntegral_markedPayoffLottery
    (q : TraceableAgency.Dist A) (ell : TraceableAgency.Dist O)
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral q (markedPayoffLotteryExperiment ell) phi =
      payoffLotteryExpected (fun o => phi (o, q)) ell := by
  classical
  have hmarg : ∀ o : O,
      (markedPayoffLotteryExperiment ell).outcomeMarginal q
          (o, (PUnit.unit : PUnit.{u + 1})) =
        ell o := by
    intro o
    change Channel.outcomeMarginal (payoffLotteryChannel ell) q
      (o, (PUnit.unit : PUnit.{u + 1})) = ell o
    rw [outcomeMarginal_payoffLotteryChannel]
    rfl
  have hpost : ∀ o : O, 0 < ell o →
      (markedPayoffLotteryExperiment ell).posterior q
          (o, (PUnit.unit : PUnit.{u + 1})) = q := by
    intro o ho
    change Channel.posterior
      (payoffLotteryChannel (A := A) ell :
        Channel A (O × PUnit.{u + 1})) q
        (o, PUnit.unit) = q
    apply TraceableAgency.Dist.ext
    intro a
    unfold Channel.posterior
    have hp : Channel.outcomeMarginal
        (payoffLotteryChannel (A := A) ell :
          Channel A (O × PUnit.{u + 1})) q
        (o, PUnit.unit) > 0 := by
      rw [outcomeMarginal_payoffLotteryChannel]
      exact ho
    rw [dif_pos hp]
    change q a *
        (payoffLotteryChannel (A := A) ell :
          Channel A (O × PUnit.{u + 1})) a (o, PUnit.unit) /
        Channel.outcomeMarginal
          (payoffLotteryChannel (A := A) ell :
            Channel A (O × PUnit.{u + 1})) q
          (o, PUnit.unit) = q a
    rw [payoffLotteryChannel_apply,
      outcomeMarginal_payoffLotteryChannel]
    simp only [payoffLotteryRecordDist_apply]
    field_simp [ne_of_gt ho]
  unfold markedTerminalIntegral payoffLotteryExpected
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  apply Finset.sum_congr rfl
  intro o _ho
  by_cases hopos : 0 < ell o
  · rw [hmarg, hpost o hopos]
  · have hozero : ell o = 0 :=
      le_antisymm (le_of_not_gt hopos) (ell.nonneg o)
    rw [hmarg, hozero]
    simp

/-- The payoff simplex embedded into the marked-law quotient at `q`. -/
noncomputable def markedPayoffLotteryEmbedding
    (q : TraceableAgency.Dist A) (ell : TraceableAgency.Dist O) :
    MarkedTerminalMixtureSpace (O := O) (A := A) q :=
  ⟦markedPayoffLotteryExperiment ell⟧

/-- The embedding identifies the singleton payoff-lottery order with the
fixed-prior marked pair order. -/
theorem markedPayoffLotteryEmbedding_order
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (ell m : TraceableAgency.Dist O) :
    payoffLotteryRel F ell m ↔
      markedTerminalMixtureRel F h q hq
        (markedPayoffLotteryEmbedding q ell)
        (markedPayoffLotteryEmbedding q m) := by
  change payoffLotteryRel F ell m ↔
    markedTerminalMixtureRel F h q hq
      (⟦markedPayoffLotteryExperiment ell⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) q)
      ⟦markedPayoffLotteryExperiment m⟧
  rw [markedTerminalMixtureRel_mk]
  change payoffLotteryRel F ell m ↔
    pairWeak F q (payoffLotteryChannel ell) q (payoffLotteryChannel m)
  rw [payoffLotteryRel_iff_expectedMaterialUtility F h,
    pairWeak_payoffLottery_iff_expectedMaterialUtility F h ell m q q]

/-- The payoff-lottery embedding preserves interior mixtures exactly in the
marked-law quotient; the public branch record disappears because it does not
change `(payoff, posterior)`. -/
theorem markedPayoffLotteryEmbedding_mix
    (q : TraceableAgency.Dist A)
    (t : Set.Ioo (0 : ℝ) 1) (ell m : TraceableAgency.Dist O) :
    markedPayoffLotteryEmbedding q
        (payoffLotteryMixtureSpace.mix t ell m) =
      (markedTerminalAbstractConvexMixtureSpace q).mix t
        (markedPayoffLotteryEmbedding q ell)
        (markedPayoffLotteryEmbedding q m) := by
  apply (markedTerminalAbstractConvexMixtureSpace q).coordinate_ext
  intro phi
  change markedTerminalIntegral q
      (markedPayoffLotteryExperiment
        (payoffLotteryMixtureSpace.mix t ell m)) phi.down =
    markedTerminalIntegral q
      (markedPublicMixExperiment t.1 t.2.1 t.2.2
        (markedPayoffLotteryExperiment ell)
        (markedPayoffLotteryExperiment m)) phi.down
  rw [markedTerminalIntegral_markedPayoffLottery,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_markedPayoffLottery,
    markedTerminalIntegral_markedPayoffLottery]
  unfold payoffLotteryExpected
  rw [payoffLotteryMixtureSpace_mix]
  simp_rw [TraceableAgency.Dist.mix_apply, add_mul]
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;>
    apply Finset.sum_congr rfl <;>
    intro o _ho <;>
    ring

/-! ## A7 normalization on each full-support marked fibre -/

/-- The chosen high material outcome, bundled on the fixed action alphabet. -/
noncomputable abbrev markedMaterialHighExperiment
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    MarkedTerminalExperiment O A :=
  markedPayoffLotteryExperiment
    (TraceableAgency.Dist.pure (materialHighOutcome F h))

/-- The chosen low material outcome, bundled on the fixed action alphabet. -/
noncomputable abbrev markedMaterialLowExperiment
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F) :
    MarkedTerminalExperiment O A :=
  markedPayoffLotteryExperiment
    (TraceableAgency.Dist.pure (materialLowOutcome F h))

/-- The A7 anchors remain strictly ordered in every full-support marked-law
fibre. -/
theorem markedMaterialAnchors_HMStrict
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    HMStrict (markedTerminalMixtureRel F h q hq)
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialHighOutcome F h)))
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialLowOutcome F h))) := by
  have hs := materialChosenAnchors_strict_everyPrior F h q q
  have hp := (pairStrict_iff_pairWeak_not_swap
    F h.a1 h.a3 h.a4 h.a5 q
      (payoffLotteryChannel
        (TraceableAgency.Dist.pure (materialHighOutcome F h))) q
      (payoffLotteryChannel
        (TraceableAgency.Dist.pure (materialLowOutcome F h)))).1 hs
  constructor
  · apply (markedTerminalMixtureRel_mk F h q hq
      (markedMaterialHighExperiment F h)
      (markedMaterialLowExperiment F h)).2
    simpa [MarkedPairWeak] using hp.1
  · intro hreverse
    apply hp.2
    have hr := (markedTerminalMixtureRel_mk F h q hq
      (markedMaterialLowExperiment F h)
      (markedMaterialHighExperiment F h)).1 hreverse
    simpa [MarkedPairWeak] using hr

/-- The marked-terminal affine representation normalized at the same A7
anchors used for the common material payoff index. -/
noncomputable def normalizedMarkedAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq) :=
  normalizeAffineUtility
    (markedTerminalAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    (markedMaterialAnchors_HMStrict F h q hq)

@[simp]
theorem normalizedMarkedAffineUtility_high
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    (normalizedMarkedAffineUtilityRepresentation F h q hq).utility
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialHighOutcome F h))) = 1 := by
  exact normalizeAffineUtility_high
    (markedTerminalAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    (markedMaterialAnchors_HMStrict F h q hq)

@[simp]
theorem normalizedMarkedAffineUtility_low
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    (normalizedMarkedAffineUtilityRepresentation F h q hq).utility
      (markedPayoffLotteryEmbedding q
        (TraceableAgency.Dist.pure (materialLowOutcome F h))) = 0 := by
  exact normalizeAffineUtility_low
    (markedTerminalAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialHighOutcome F h)))
    (markedPayoffLotteryEmbedding q
      (TraceableAgency.Dist.pure (materialLowOutcome F h)))
    (markedMaterialAnchors_HMStrict F h q hq)

/-- The normalized quotient utility evaluated on a raw marked experiment. -/
noncomputable def normalizedMarkedUtility
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E : MarkedTerminalExperiment O A) : ℝ :=
  (normalizedMarkedAffineUtilityRepresentation F h q hq).utility
    (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q)

/-- The normalized marked utility still represents the marked pair order. -/
theorem normalizedMarkedUtility_represents
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    MarkedPairWeak F q E q G ↔
      normalizedMarkedUtility F h q hq E ≥
        normalizedMarkedUtility F h q hq G := by
  rw [← markedTerminalMixtureRel_mk F h q hq E G]
  exact (normalizedMarkedAffineUtilityRepresentation F h q hq).represents _ _

/-- Normalization preserves public-mixture affinity. -/
theorem normalizedMarkedUtility_publicMix
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A) :
    normalizedMarkedUtility F h q hq
        (markedPublicMixExperiment t ht0 ht1 E R) =
      t * normalizedMarkedUtility F h q hq E +
        (1 - t) * normalizedMarkedUtility F h q hq R := by
  let ti : Set.Ioo (0 : ℝ) 1 := ⟨t, ht0, ht1⟩
  simpa [normalizedMarkedUtility,
    markedTerminalAbstractConvexMixtureSpace] using
      (normalizedMarkedAffineUtilityRepresentation F h q hq).affine ti
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦R⟧

/-- The normalized marked utility is literally a function of the full marked
terminal law. -/
theorem normalizedMarkedUtility_respects_sameMarkedTerminalLaw
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E') :
    normalizedMarkedUtility F h q hq E =
      normalizedMarkedUtility F h q hq E' := by
  unfold normalizedMarkedUtility
  congr 1
  exact Quotient.sound hsame

@[simp]
theorem normalizedMarkedUtility_high
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    normalizedMarkedUtility F h q hq
      (markedMaterialHighExperiment F h) = 1 :=
  normalizedMarkedAffineUtility_high F h q hq

@[simp]
theorem normalizedMarkedUtility_low
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    normalizedMarkedUtility F h q hq
      (markedMaterialLowExperiment F h) = 0 :=
  normalizedMarkedAffineUtility_low F h q hq

/-! ## Identification with material expected utility -/

/-- On every payoff lottery, normalized marked utility is exactly the common
material expected utility.  This is affine-representation uniqueness along
the payoff-lottery embedding, not an additional normalization convention. -/
theorem normalizedMarkedUtility_payoffLottery
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (ell : TraceableAgency.Dist O) :
    normalizedMarkedUtility F h q hq
        (markedPayoffLotteryExperiment ell) =
      expectedPayoffUtility (materialPayoffUtility F h) q
        (payoffLotteryChannel ell) := by
  have hunique := normalizedAffineUtility_eq_along_embedding
    payoffLotteryMixtureSpace
    (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
    (payoffLotteryRel F)
    (markedTerminalMixtureRel (O := O) (A := A) F h q hq)
    (materialAffineUtility F h)
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (markedPayoffLotteryEmbedding q)
    (markedPayoffLotteryEmbedding_order F h q hq)
    (markedPayoffLotteryEmbedding_mix q)
    (TraceableAgency.Dist.pure (materialHighOutcome F h))
    (TraceableAgency.Dist.pure (materialLowOutcome F h))
    (materialChosenAnchors_HMStrict F h)
    (materialAffineUtility_low F h)
    (materialAffineUtility_high F h)
    (normalizedMarkedAffineUtility_low F h q hq)
    (normalizedMarkedAffineUtility_high F h q hq)
    ell
  calc
    normalizedMarkedUtility F h q hq
        (markedPayoffLotteryExperiment ell) =
        (materialAffineUtility F h).utility ell := hunique
    _ = payoffLotteryExpected (materialPayoffUtility F h) ell :=
      materialAffineUtility_eq_expected F h ell
    _ = expectedPayoffUtility (materialPayoffUtility F h) q
        (payoffLotteryChannel ell) :=
      (expectedPayoffUtility_payoffLotteryChannel
        (materialPayoffUtility F h) ell q).symm

end TraceableAgency.Theorem1
