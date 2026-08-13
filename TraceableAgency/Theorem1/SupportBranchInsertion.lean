/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.BranchInsertion
import TraceableAgency.Theorem1.SupportMarkedLift

/-!
# Inserting a continuation from a boundary posterior's support face

The reached branch posterior may lie on the boundary of the ambient action
simplex.  Its support face is nevertheless full support.  This file extends a
marked continuation from that face, inserts it into the reached branch, and
transports both the mixture structure and the order to the outer full-support
fibre.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-! ## Representative and quotient maps -/

/-- Extend a continuation from the reached posterior's support face and then
insert it at the distinguished branch. -/
noncomputable def supportBranchInsertionExperiment
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target))) :
    MarkedTerminalExperiment O A :=
  branchInsertionExperiment P target o0
    (supportExtendMarkedExperiment (branchPosterior P q target) E)

/-- Support-face law equality is preserved by extension and branch
insertion. -/
theorem sameMarkedTerminalLaw_supportBranchInsertion
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O)
    (E G : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target)))
    (hsame : SameMarkedTerminalLaw
      (branchPosterior P q target).restrictToSupport E G) :
    SameMarkedTerminalLaw q
      (supportBranchInsertionExperiment q P target o0 E)
      (supportBranchInsertionExperiment q P target o0 G) := by
  exact sameMarkedTerminalLaw_branchInsertion q P target o0 _ _
    (sameMarkedTerminalLaw_supportExtend
      (branchPosterior P q target) hsame)

/-- The induced map from the full-support support fibre to the outer marked
terminal-law fibre. -/
noncomputable def supportBranchInsertionMixtureMap
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) :
    MarkedTerminalMixtureSpace
        (O := O) (A := supportSubtype (branchPosterior P q target))
        (branchPosterior P q target).restrictToSupport →
      MarkedTerminalMixtureSpace (O := O) (A := A) q :=
  fun x ↦ branchInsertionMixtureMap q P target o0
    (supportExtendMarkedMixtureMap (branchPosterior P q target) x)

@[simp]
theorem supportBranchInsertionMixtureMap_mk
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target))) :
    supportBranchInsertionMixtureMap q P target o0
        (⟦E⟧ : MarkedTerminalMixtureSpace
          (O := O) (A := supportSubtype (branchPosterior P q target))
          (branchPosterior P q target).restrictToSupport) =
      (⟦supportBranchInsertionExperiment q P target o0 E⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) q) := by
  rfl

/-- Support extension followed by insertion commutes with public mixing. -/
theorem supportBranchInsertionMixtureMap_affine
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace
      (O := O) (A := supportSubtype (branchPosterior P q target))
      (branchPosterior P q target).restrictToSupport) :
    supportBranchInsertionMixtureMap q P target o0
        ((markedTerminalAbstractConvexMixtureSpace
          (branchPosterior P q target).restrictToSupport).mix t x y) =
      (markedTerminalAbstractConvexMixtureSpace q).mix t
        (supportBranchInsertionMixtureMap q P target o0 x)
        (supportBranchInsertionMixtureMap q P target o0 y) := by
  unfold supportBranchInsertionMixtureMap
  rw [supportExtendMarkedMixtureMap_affine,
    branchInsertionMixtureMap_affine]

/-- The common-record insertion of a raw channel agrees in marked terminal
law with insertion of that channel bundled using the same record instance. -/
private theorem sameMarkedTerminalLaw_branchInsertionCommon_rawChannel
    {R : Type u} [Fintype R] [DecidableEq R] [Nonempty R]
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (K : Channel A (O × R)) :
    SameMarkedTerminalLaw q
      (branchInsertionCommonExperiment P target o0 K)
      (branchInsertionExperiment P target o0
        (markedExperimentOfChannel K)) := by
  classical
  intro phi
  change
    markedChannelIntegral q
        (commonPayoffCompound (branchInsertionCommonRecord target R) P
          (branchInsertionCommonContinuation target o0 K)) phi =
      markedChannelIntegral q
        (commonPayoffCompound
          (branchInsertionRecord target (markedExperimentOfChannel K)) P
          (branchInsertionContinuation target o0
            (markedExperimentOfChannel K))) phi
  rw [markedChannelIntegral_commonPayoffCompound,
    markedChannelIntegral_commonPayoffCompound]
  apply Finset.sum_congr rfl
  intro y _hy
  by_cases hyt : y = target
  · subst y
    rw [markedChannelIntegral_branchInsertionCommonContinuation_target,
      markedChannelIntegral_branchInsertionContinuation_target]
    rfl
  · rw [markedChannelIntegral_branchInsertionCommonContinuation_of_ne
        _ _ _ _ _ hyt,
      markedChannelIntegral_branchInsertionContinuation_of_ne
        _ _ _ _ _ hyt]

/-! ## Exact boundary-order embedding -/

/-- Insertion from the support face is an exact order embedding even when the
reached posterior is on the boundary of the ambient action simplex. -/
theorem markedPairWeak_supportBranchInsertion_iff
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O)
    (E G : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target))) :
    MarkedPairWeak F (branchPosterior P q target).restrictToSupport E
        (branchPosterior P q target).restrictToSupport G ↔
      MarkedPairWeak F q
        (supportBranchInsertionExperiment q P target o0 E) q
        (supportBranchInsertionExperiment q P target o0 G) := by
  classical
  let r := branchPosterior P q target
  let hrs : r.restrictToSupport.FullSupport :=
    Dist.restrictToSupport_fullSupport r
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  let Epad := markedPadLeftExperiment E G.RecordType
  let Gpad0 := markedPadRightExperiment E.RecordType G
  let Gpad : MarkedTerminalExperiment O (supportSubtype r) :=
    { RecordType := Epad.RecordType
      recordFintype := Epad.recordFintype
      recordDecEq := Epad.recordDecEq
      recordNonempty := Epad.recordNonempty
      channel := Gpad0.K }
  let R := Epad.RecordType
  letI : Fintype R := Epad.recordFintype
  letI : DecidableEq R := Epad.recordDecEq
  letI : Nonempty R := Epad.recordNonempty
  let EKraw : Channel A (O × R) := supportExtendChannel r Epad.K
  let GKraw : Channel A (O × R) := supportExtendChannel r Gpad.K
  let EK : MarkedTerminalExperiment O A := markedExperimentOfChannel EKraw
  let GK : MarkedTerminalExperiment O A := markedExperimentOfChannel GKraw
  have hEpad : SameMarkedTerminalLaw r.restrictToSupport E Epad := by
    exact sameMarkedTerminalLaw_markedPadLeft r.restrictToSupport E
  have hGpad : SameMarkedTerminalLaw r.restrictToSupport G Gpad := by
    intro phi
    simpa [Gpad, Gpad0, Epad] using
      (sameMarkedTerminalLaw_markedPadRight
        r.restrictToSupport (R := E.RecordType) G) phi
  have hEextend : SameMarkedTerminalLaw r
      (supportExtendMarkedExperiment r E) EK := by
    simpa [EK, EKraw, Epad, markedExperimentOfChannel,
      supportExtendMarkedExperiment] using
      sameMarkedTerminalLaw_supportExtend r hEpad
  have hGextend : SameMarkedTerminalLaw r
      (supportExtendMarkedExperiment r G) GK := by
    simpa [GK, GKraw, Gpad, markedExperimentOfChannel,
      supportExtendMarkedExperiment] using
      sameMarkedTerminalLaw_supportExtend r hGpad
  have hEcommon : SameMarkedTerminalLaw q
      (branchInsertionCommonExperiment P target o0 EKraw)
      (branchInsertionExperiment P target o0 EK) := by
    simpa [EK] using
      (sameMarkedTerminalLaw_branchInsertionCommon_rawChannel
        q P target o0 EKraw)
  have hGcommon : SameMarkedTerminalLaw q
      (branchInsertionCommonExperiment P target o0 GKraw)
      (branchInsertionExperiment P target o0 GK) := by
    simpa [GK] using
      (sameMarkedTerminalLaw_branchInsertionCommon_rawChannel
        q P target o0 GKraw)
  have hEinsert : SameMarkedTerminalLaw q
      (branchInsertionExperiment P target o0
        (supportExtendMarkedExperiment r E))
      (branchInsertionExperiment P target o0 EK) := by
    exact sameMarkedTerminalLaw_branchInsertion
      q P target o0 _ _ hEextend
  have hGinsert : SameMarkedTerminalLaw q
      (branchInsertionExperiment P target o0
        (supportExtendMarkedExperiment r G))
      (branchInsertionExperiment P target o0 GK) := by
    exact sameMarkedTerminalLaw_branchInsertion
      q P target o0 _ _ hGextend
  have hEcompOriginal : SameMarkedTerminalLaw q
      (branchInsertionCommonExperiment P target o0 EKraw)
      (supportBranchInsertionExperiment q P target o0 E) := by
    intro phi
    exact (hEcommon phi).trans (hEinsert phi).symm
  have hGcompOriginal : SameMarkedTerminalLaw q
      (branchInsertionCommonExperiment P target o0 GKraw)
      (supportBranchInsertionExperiment q P target o0 G) := by
    intro phi
    exact (hGcommon phi).trans (hGinsert phi).symm
  have hpad :
      MarkedPairWeak F r.restrictToSupport E r.restrictToSupport G ↔
        MarkedPairWeak F r.restrictToSupport Epad
          r.restrictToSupport Gpad :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 r.restrictToSupport r.restrictToSupport hrs hrs
        E Epad G Gpad hEpad hGpad
  have hext :
      MarkedPairWeak F r.restrictToSupport Epad
          r.restrictToSupport Gpad ↔
        pairWeak F r EKraw r GKraw := by
    simpa [MarkedPairWeak, EKraw, GKraw, Epad, Gpad,
      supportExtendMarkedExperiment] using
      (markedPairWeak_supportExtend_iff F h r Epad Gpad)
  have hcore :
      pairWeak F r EKraw r GKraw ↔
        MarkedPairWeak F q
          (branchInsertionCommonExperiment P target o0 EKraw) q
          (branchInsertionCommonExperiment P target o0 GKraw) := by
    simpa only [r] using
      (pairWeak_branchInsertionCommon_iff
        (R := R) F h q P target htarget o0 EKraw GKraw)
  have hcomp :
      MarkedPairWeak F q
          (branchInsertionCommonExperiment P target o0 EKraw) q
          (branchInsertionCommonExperiment P target o0 GKraw) ↔
        MarkedPairWeak F q
          (supportBranchInsertionExperiment q P target o0 E) q
          (supportBranchInsertionExperiment q P target o0 G) :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 q q hq hq
        (branchInsertionCommonExperiment P target o0 EKraw)
        (supportBranchInsertionExperiment q P target o0 E)
        (branchInsertionCommonExperiment P target o0 GKraw)
        (supportBranchInsertionExperiment q P target o0 G)
        hEcompOriginal hGcompOriginal
  exact hpad.trans (hext.trans (hcore.trans hcomp))

/-- Exact order embedding on the two marked-terminal-law quotients. -/
theorem supportBranchInsertionMixtureMap_rel_iff
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O)
    (x y : MarkedTerminalMixtureSpace
      (O := O) (A := supportSubtype (branchPosterior P q target))
      (branchPosterior P q target).restrictToSupport) :
    markedTerminalMixtureRel F h
        (branchPosterior P q target).restrictToSupport
        (Dist.restrictToSupport_fullSupport (branchPosterior P q target)) x y ↔
      markedTerminalMixtureRel F h q hq
        (supportBranchInsertionMixtureMap q P target o0 x)
        (supportBranchInsertionMixtureMap q P target o0 y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      simpa [markedTerminalMixtureRel_mk] using
        (markedPairWeak_supportBranchInsertion_iff
          F h q hq P target htarget o0 E G)

/-! ## Pullback representation and its positive scale -/

/-- Pull back the normalized outer-fibre utility along support extension and
branch insertion. -/
noncomputable def supportBranchInsertionPullbackAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O) :
    AffineUtilityRepresentation
      (markedTerminalAbstractConvexMixtureSpace
        (O := O) (A := supportSubtype (branchPosterior P q target))
        (branchPosterior P q target).restrictToSupport)
      (markedTerminalMixtureRel F h
        (branchPosterior P q target).restrictToSupport
        (Dist.restrictToSupport_fullSupport
          (branchPosterior P q target))) :=
  pullbackAffineUtility
    (markedTerminalAbstractConvexMixtureSpace
      (O := O) (A := supportSubtype (branchPosterior P q target))
      (branchPosterior P q target).restrictToSupport)
    (markedTerminalAbstractConvexMixtureSpace
      (O := O) (A := A) q)
    (markedTerminalMixtureRel F h
      (branchPosterior P q target).restrictToSupport
      (Dist.restrictToSupport_fullSupport
        (branchPosterior P q target)))
    (markedTerminalMixtureRel F h q hq)
    (normalizedMarkedAffineUtilityRepresentation F h q hq)
    (supportBranchInsertionMixtureMap q P target o0)
    (supportBranchInsertionMixtureMap_rel_iff
      F h q hq P target htarget o0)
    (supportBranchInsertionMixtureMap_affine q P target o0)

/-- Affine uniqueness supplies one positive coefficient and one additive
constant on the reached posterior's support fibre.  No numerical
identification of that coefficient is asserted here. -/
theorem supportBranchInsertionPullback_positiveAffine_exists
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O) :
    ∃ a b : ℝ, 0 < a ∧
      ∀ x : MarkedTerminalMixtureSpace
        (O := O) (A := supportSubtype (branchPosterior P q target))
        (branchPosterior P q target).restrictToSupport,
        (supportBranchInsertionPullbackAffineUtilityRepresentation
          F h q hq P target htarget o0).utility x =
          a * (normalizedMarkedAffineUtilityRepresentation F h
            (branchPosterior P q target).restrictToSupport
            (Dist.restrictToSupport_fullSupport
              (branchPosterior P q target))).utility x + b := by
  let r := branchPosterior P q target
  let hrs : r.restrictToSupport.FullSupport :=
    Dist.restrictToSupport_fullSupport r
  have hnonconstant :
      ∃ x y : MarkedTerminalMixtureSpace
          (O := O) (A := supportSubtype r) r.restrictToSupport,
        (normalizedMarkedAffineUtilityRepresentation
          F h r.restrictToSupport hrs).utility x ≠
        (normalizedMarkedAffineUtilityRepresentation
          F h r.restrictToSupport hrs).utility y := by
    refine ⟨markedPayoffLotteryEmbedding r.restrictToSupport
        (TraceableAgency.Dist.pure (materialHighOutcome F h)),
      markedPayoffLotteryEmbedding r.restrictToSupport
        (TraceableAgency.Dist.pure (materialLowOutcome F h)), ?_⟩
    rw [normalizedMarkedAffineUtility_high,
      normalizedMarkedAffineUtility_low]
    norm_num
  exact affineUtilityRepresentation_positiveAffine_unique
    (markedTerminalAbstractConvexMixtureSpace
      (O := O) (A := supportSubtype r) r.restrictToSupport)
    (markedTerminalMixtureRel F h r.restrictToSupport hrs)
    (normalizedMarkedAffineUtilityRepresentation
      F h r.restrictToSupport hrs)
    (supportBranchInsertionPullbackAffineUtilityRepresentation
      F h q hq P target htarget o0)
    hnonconstant

/-- The positive affine coefficient selected from uniqueness. -/
noncomputable def supportBranchInsertionScale
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O) : ℝ :=
  Classical.choose
    (supportBranchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget o0)

/-- The additive constant selected together with the support-insertion
coefficient. -/
noncomputable def supportBranchInsertionOffset
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O) : ℝ :=
  Classical.choose (Classical.choose_spec
    (supportBranchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget o0))

theorem supportBranchInsertionScale_pos
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O) :
    0 < supportBranchInsertionScale F h q hq P target htarget o0 := by
  exact (Classical.choose_spec (Classical.choose_spec
    (supportBranchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget o0))).1

theorem supportBranchInsertionPullback_eq_scale_add_offset
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O)
    (x : MarkedTerminalMixtureSpace
      (O := O) (A := supportSubtype (branchPosterior P q target))
      (branchPosterior P q target).restrictToSupport) :
    (supportBranchInsertionPullbackAffineUtilityRepresentation
      F h q hq P target htarget o0).utility x =
      supportBranchInsertionScale F h q hq P target htarget o0 *
        (normalizedMarkedAffineUtilityRepresentation F h
          (branchPosterior P q target).restrictToSupport
          (Dist.restrictToSupport_fullSupport
            (branchPosterior P q target))).utility x +
      supportBranchInsertionOffset F h q hq P target htarget o0 := by
  exact (Classical.choose_spec (Classical.choose_spec
    (supportBranchInsertionPullback_positiveAffine_exists
      F h q hq P target htarget o0))).2 x

/-- The positive-affine formula specialized to a raw support-face marked
experiment. -/
theorem normalizedMarkedUtility_supportBranchInsertion
    (F : FixedPayoffPrefFamily O) {traceAnchor : O} (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (P : Channel A Y) (target : Y)
    (htarget : BranchPositive P q target) (o0 : O)
    (E : MarkedTerminalExperiment O
      (supportSubtype (branchPosterior P q target))) :
    normalizedMarkedUtility F h q hq
        (supportBranchInsertionExperiment q P target o0 E) =
      supportBranchInsertionScale F h q hq P target htarget o0 *
        normalizedMarkedUtility F h
          (branchPosterior P q target).restrictToSupport
          (Dist.restrictToSupport_fullSupport
            (branchPosterior P q target)) E +
      supportBranchInsertionOffset F h q hq P target htarget o0 := by
  simpa [supportBranchInsertionPullbackAffineUtilityRepresentation,
    pullbackAffineUtility, normalizedMarkedUtility] using
    (supportBranchInsertionPullback_eq_scale_add_offset
      F h q hq P target htarget o0
      (⟦E⟧ : MarkedTerminalMixtureSpace
        (O := O) (A := supportSubtype (branchPosterior P q target))
        (branchPosterior P q target).restrictToSupport))

end TraceableAgency.Theorem1
