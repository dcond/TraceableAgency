import TraceableAgency.Theorem1.MarkedHM
import TraceableAgency.Theorem1.FiniteBranchExtension

/-! # Affine marked-law fibres without either relevance axiom

This file exposes precisely the structural and continuity assumptions used in
the original marked-law argument. Proof provenance: the corresponding
`MarkedHM.lean` proofs are preserved, with `PairOrder.lean` wrappers narrowed
to their actually used fields. All generic mixture/law lemmas are reused. The generic Herstein--Milnor theorem also
covers the all-indifferent order; no nondegeneracy is assumed here.
-/
namespace TraceableAgency.Theorem1.V11
open TraceableAgency Filter Set Topology
universe u

structure AffineAxioms {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) : Prop where
  a1 : A1_WeakOrder F
  a2 : A2_Continuity F
  a3 : A5_BlockComparisonCoherence F
  a4 : A6_RecordDataProcessing F
  a5 : A7_ActionDataProcessing F
  a6 : FiniteBranchContinuationConsistency F

theorem affineAxioms_of_paper
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h2 : A2_Continuity F)
    (h5 : A5_BlockComparisonCoherence F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F) (h8 : A8_RecordwiseSureThing F) :
    AffineAxioms F :=
  ⟨h1, h2, h5, h6, h7,
    finiteBranchContinuationConsistency_of_recordwiseSureThing F h1 h5 h6 h7 h8⟩

theorem pairWeak_complete
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ∨ pairWeak F p L q K := by
  let C := commonPayoffBlockChannel K L
  rcases (h.a1 C).1 (leftBlockDist q) (rightBlockDist p) with hqp | hpq
  · exact Or.inl hqp
  · exact Or.inr
      ((sameBlock_reverse_iff_pairWeak_swap F h.a1 h.a3 h.a4 h.a5
        q K p L).1 hpq)

/-- Three labels used to assemble transitivity of cross-environment pairs in
one primitive block environment. -/
theorem pairWeak_transitive
    {O A B C R S T : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype C] [DecidableEq C] [Nonempty C]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S))
    (s : TraceableAgency.Dist C) (M : Channel C (O × T)) :
    pairWeak F q K p L → pairWeak F p L s M → pairWeak F q K s M :=
  pairWeak_transitive_of_structural F h.a1 h.a3 q K p L s M

theorem pairWeak_transitive_sameAction
    {O A R S T : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype T] [DecidableEq T] [Nonempty T]
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist A) (L : Channel A (O × S))
    (s : TraceableAgency.Dist A) (M : Channel A (O × T)) :
    pairWeak F q K p L → pairWeak F p L s M → pairWeak F q K s M :=
  pairWeak_transitive F h q K p L s M

theorem pairWeak_refl
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R)) :
    pairWeak F q K q K := by
  have hself : F.rel K q q := by
    rcases (h.a1 K).1 q q with hq | hq <;> exact hq
  exact (h.a3.duplication K q q).1 hself

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

def markedTerminalMixtureRel
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    MarkedTerminalMixtureSpace (O := O) (A := A) q →
      MarkedTerminalMixtureSpace (O := O) (A := A) q → Prop :=
  fun x y =>
    Quotient.liftOn₂ x y
      (fun E G => MarkedPairWeak F q E q G)
      (by
        intro E G E' G' hE hG
        exact propext
          (pairWeak_respects_sameMarkedTerminalLaw
            F h.a1 h.a3 h.a4 q q hq hq E E' G G' hE hG))

@[simp]

theorem markedTerminalMixtureRel_mk
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    markedTerminalMixtureRel F h q hq
        (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦G⟧ ↔
      MarkedPairWeak F q E q G := by
  rfl

theorem markedTerminalMixtureRel_out
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y ↔
      MarkedPairWeak F q x.out q y.out := by
  change markedTerminalMixtureRel F h q hq x y ↔
    markedTerminalMixtureRel F h q hq ⟦x.out⟧ ⟦y.out⟧
  rw [Quotient.out_eq x, Quotient.out_eq y]

theorem markedTerminalMixtureRel_complete
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y ∨
      markedTerminalMixtureRel F h q hq y x := by
  let E := x.out
  let G := y.out
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  rcases pairWeak_complete F h q E.K q G.K with hEG | hGE
  · left
    exact (markedTerminalMixtureRel_out F h q hq x y).2 hEG
  · right
    exact (markedTerminalMixtureRel_out F h q hq y x).2 hGE

theorem markedTerminalMixtureRel_transitive
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y z : MarkedTerminalMixtureSpace (O := O) (A := A) q) :
    markedTerminalMixtureRel F h q hq x y →
    markedTerminalMixtureRel F h q hq y z →
    markedTerminalMixtureRel F h q hq x z := by
  intro hxy hyz
  let E := x.out
  let G := y.out
  let H := z.out
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  letI : Fintype H.RecordType := H.recordFintype
  letI : DecidableEq H.RecordType := H.recordDecEq
  letI : Nonempty H.RecordType := H.recordNonempty
  apply (markedTerminalMixtureRel_out F h q hq x z).2
  exact pairWeak_transitive_sameAction F h q E.K q G.K q H.K
    ((markedTerminalMixtureRel_out F h q hq x y).1 hxy)
    ((markedTerminalMixtureRel_out F h q hq y z).1 hyz)

theorem markedPairWeak_publicMix_independence
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G R : MarkedTerminalExperiment O A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    MarkedPairWeak F q E q G ↔
      MarkedPairWeak F q
        (markedPublicMixExperiment t ht0 ht1 E R) q
        (markedPublicMixExperiment t ht0 ht1 G R) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  letI : Fintype R.RecordType := R.recordFintype
  letI : DecidableEq R.RecordType := R.recordDecEq
  letI : Nonempty R.RecordType := R.recordNonempty
  let Y := PUnit.{u + 1} ⊕ PUnit.{u + 1}
  letI : Fintype Y := inferInstance
  letI : DecidableEq Y := inferInstance
  letI : Nonempty Y := inferInstance
  let U : Channel A PUnit.{u + 1} := Channel.uninformativeChannelU A
  let C : Channel A Y := publicMixChannel t ht0 ht1 U U
  let Epad := markedPadLeftExperiment E G.RecordType
  let Gpad := markedPadRightExperiment E.RecordType G
  let Rec : Y → Type u
    | Sum.inl _ => E.RecordType ⊕ G.RecordType
    | Sum.inr _ => R.RecordType
  let recFintype : ∀ y, Fintype (Rec y)
    | Sum.inl _ => inferInstance
    | Sum.inr _ => R.recordFintype
  let recDecEq : ∀ y, DecidableEq (Rec y)
    | Sum.inl _ => inferInstance
    | Sum.inr _ => R.recordDecEq
  let recNonempty : ∀ y, Nonempty (Rec y)
    | Sum.inl _ => inferInstance
    | Sum.inr _ => R.recordNonempty
  letI : ∀ y, Fintype (Rec y) := recFintype
  letI : ∀ y, DecidableEq (Rec y) := recDecEq
  letI : ∀ y, Nonempty (Rec y) := recNonempty
  let QE : ∀ y, Channel A (O × Rec y)
    | Sum.inl _ => Epad.K
    | Sum.inr _ => R.K
  let QG : ∀ y, Channel A (O × Rec y)
    | Sum.inl _ => Gpad.K
    | Sum.inr _ => R.K
  let compFintype : Fintype ((y : Y) × Rec y) := inferInstance
  let compDecEq : DecidableEq ((y : Y) × Rec y) := inferInstance
  let compNonempty : Nonempty ((y : Y) × Rec y) := inferInstance
  letI : Fintype ((y : Y) × Rec y) := compFintype
  letI : DecidableEq ((y : Y) × Rec y) := compDecEq
  letI : Nonempty ((y : Y) × Rec y) := compNonempty
  let Ecomp : MarkedTerminalExperiment O A :=
    { RecordType := (y : Y) × Rec y
      recordFintype := compFintype
      recordDecEq := compDecEq
      recordNonempty := compNonempty
      channel := commonPayoffCompound Rec C QE }
  let Gcomp : MarkedTerminalExperiment O A :=
    { RecordType := (y : Y) × Rec y
      recordFintype := compFintype
      recordDecEq := compDecEq
      recordNonempty := compNonempty
      channel := commonPayoffCompound Rec C QG }
  let Emix := markedPublicMixExperiment t ht0 ht1 E R
  let Gmix := markedPublicMixExperiment t ht0 ht1 G R
  have hEpad : SameMarkedTerminalLaw q E Epad := by
    exact sameMarkedTerminalLaw_markedPadLeft q E
  have hGpad : SameMarkedTerminalLaw q G Gpad := by
    exact sameMarkedTerminalLaw_markedPadRight q G
  have hU_marginal : Channel.outcomeMarginal U q default = 1 := by
    simp [U, Channel.outcomeMarginal_apply,
      Channel.uninformativeChannelU, q.sum_eq_one]
  have hU_posterior : Channel.posterior U q default = q := by
    apply TraceableAgency.Dist.ext
    intro a
    simp [U, Channel.posterior, Channel.outcomeMarginal_apply,
      Channel.uninformativeChannelU, q.sum_eq_one]
  have hC_left_marginal :
      Channel.outcomeMarginal C q (Sum.inl default) = t := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_outcomeMarginal_publicMixChannel_inl, hU_marginal, mul_one]
  have hC_right_marginal :
      Channel.outcomeMarginal C q (Sum.inr default) = 1 - t := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_outcomeMarginal_publicMixChannel_inr, hU_marginal, mul_one]
  have hC_left_posterior :
      Channel.posterior C q (Sum.inl default) = q := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_posterior_publicMixChannel_inl, hU_posterior]
  have hC_right_posterior :
      Channel.posterior C q (Sum.inr default) = q := by
    rw [show C = publicMixChannel t ht0 ht1 U U by rfl,
      hm_posterior_publicMixChannel_inr, hU_posterior]
  have hEcomp : SameMarkedTerminalLaw q Ecomp Emix := by
    intro phi
    change markedChannelIntegral q (commonPayoffCompound Rec C QE) phi =
      markedTerminalIntegral q
        (markedPublicMixExperiment t ht0 ht1 E R) phi
    rw [markedChannelIntegral_commonPayoffCompound,
      markedTerminalIntegral_publicMix]
    simp only [Y, Fintype.sum_sum_type, Fintype.sum_unique]
    rw [hC_left_marginal, hC_right_marginal,
      hC_left_posterior, hC_right_posterior]
    change
      t * markedTerminalIntegral q Epad phi +
          (1 - t) * markedTerminalIntegral q R phi =
        t * markedTerminalIntegral q E phi +
          (1 - t) * markedTerminalIntegral q R phi
    rw [← hEpad phi]
  have hGcomp : SameMarkedTerminalLaw q Gcomp Gmix := by
    intro phi
    change markedChannelIntegral q (commonPayoffCompound Rec C QG) phi =
      markedTerminalIntegral q
        (markedPublicMixExperiment t ht0 ht1 G R) phi
    rw [markedChannelIntegral_commonPayoffCompound,
      markedTerminalIntegral_publicMix]
    simp only [Y, Fintype.sum_sum_type, Fintype.sum_unique]
    rw [hC_left_marginal, hC_right_marginal,
      hC_left_posterior, hC_right_posterior]
    change
      t * markedTerminalIntegral q Gpad phi +
          (1 - t) * markedTerminalIntegral q R phi =
        t * markedTerminalIntegral q G phi +
          (1 - t) * markedTerminalIntegral q R phi
    rw [← hGpad phi]
  have hpad :
      MarkedPairWeak F q E q G ↔ MarkedPairWeak F q Epad q Gpad :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 q q hq hq E Epad G Gpad hEpad hGpad
  have hcomp :
      MarkedPairWeak F q Ecomp q Gcomp ↔
        MarkedPairWeak F q Emix q Gmix :=
    pairWeak_respects_sameMarkedTerminalLaw
      F h.a1 h.a3 h.a4 q q hq hq Ecomp Emix Gcomp Gmix hEcomp hGcomp
  constructor
  · intro hEG
    have hbranch : ∀ y, BranchPositive C q y →
        pairWeak F (branchPosterior C q y) (QE y)
          (branchPosterior C q y) (QG y) := by
      intro y _hy
      rcases y with (_ | _)
      · simpa [QE, QG, Epad, Gpad, branchPosterior,
          hC_left_posterior, MarkedPairWeak] using hpad.mp hEG
      · simpa [QE, QG, branchPosterior, hC_right_posterior] using
          (pairWeak_refl F h q R.K)
    have hraw := h.a6.1 Rec C QE QG q hbranch
    have hbundled : MarkedPairWeak F q Ecomp q Gcomp := by
      simpa [MarkedPairWeak, Ecomp, Gcomp] using hraw
    exact hcomp.mp hbundled
  · intro hmix
    have hbundled : MarkedPairWeak F q Ecomp q Gcomp := hcomp.mpr hmix
    have hraw : pairWeak F q (commonPayoffCompound Rec C QE)
        q (commonPayoffCompound Rec C QG) := by
      simpa [MarkedPairWeak, Ecomp, Gcomp] using hbundled
    by_contra hnot
    have hGE : MarkedPairWeak F q G q E := by
      rcases pairWeak_complete F h q E.K q G.K with hEG | hGE
      · exact False.elim (hnot (by simpa [MarkedPairWeak] using hEG))
      · simpa [MarkedPairWeak] using hGE
    have hGpadEpad : MarkedPairWeak F q Gpad q Epad := by
      exact (pairWeak_respects_sameMarkedTerminalLaw
        F h.a1 h.a3 h.a4 q q hq hq G Gpad E Epad hGpad hEpad).mp hGE
    have hnotEpadGpad : ¬ MarkedPairWeak F q Epad q Gpad := by
      intro hp
      exact hnot (hpad.mpr hp)
    have hstrictPad : pairStrict F q Gpad.K q Epad.K := by
      exact (pairStrict_iff_pairWeak_not_swap
        F h.a1 h.a3 h.a4 h.a5 q Gpad.K q Epad.K).2
          ⟨by simpa [MarkedPairWeak] using hGpadEpad,
            by simpa [MarkedPairWeak] using hnotEpadGpad⟩
    have hbranchRev : ∀ y, BranchPositive C q y →
        pairWeak F (branchPosterior C q y) (QG y)
          (branchPosterior C q y) (QE y) := by
      intro y _hy
      rcases y with (_ | _)
      · simpa [QE, QG, Epad, Gpad, branchPosterior,
          hC_left_posterior, MarkedPairWeak] using hGpadEpad
      · simpa [QE, QG, branchPosterior, hC_right_posterior] using
          (pairWeak_refl F h q R.K)
    have hleftPositive : BranchPositive C q (Sum.inl default) := by
      change Channel.outcomeMarginal C q (Sum.inl default) > 0
      rw [hC_left_marginal]
      exact ht0
    have hstrictRaw := h.a6.2 Rec C QG QE q hbranchRev
      ⟨Sum.inl default, hleftPositive, by
        simpa [QG, QE, branchPosterior, hC_left_posterior] using hstrictPad⟩
    have hstrictParts := (pairStrict_iff_pairWeak_not_swap
      F h.a1 h.a3 h.a4 h.a5 q
        (commonPayoffCompound Rec C QG) q
        (commonPayoffCompound Rec C QE)).1 hstrictRaw
    exact hstrictParts.2 hraw

theorem markedTerminalMixtureRel_independence
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (x y z : MarkedTerminalMixtureSpace (O := O) (A := A) q)
    (t : Set.Ioo (0 : ℝ) 1) :
    markedTerminalMixtureRel F h q hq x y ↔
      markedTerminalMixtureRel F h q hq
        ((markedTerminalAbstractConvexMixtureSpace q).mix t x z)
        ((markedTerminalAbstractConvexMixtureSpace q).mix t y z) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      induction z using Quotient.inductionOn with
      | _ R =>
        simpa [markedTerminalAbstractConvexMixtureSpace,
          markedTerminalMixtureRel_mk] using
            markedPairWeak_publicMix_independence
              F h q hq E G R t.1 t.2.1 t.2.2

/-! ## A fixed-alphabet closed public segment -/

/-- The closed public segment, including its zero and one endpoints, on the
single record alphabet `E.RecordType ⊕ L.RecordType`. -/
theorem markedPairWeak_closedSegment_limit_left
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A)
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (𝓝 t))
    (E L T : MarkedTerminalExperiment O A)
    (hrel : ∀ n,
      MarkedPairWeak F q (markedClosedSegmentExperiment (tseq n) E L) q T) :
    MarkedPairWeak F q (markedClosedSegmentExperiment t E L) q T := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  letI : Fintype T.RecordType := T.recordFintype
  letI : DecidableEq T.RecordType := T.recordDecEq
  letI : Nonempty T.RecordType := T.recordNonempty
  let Kseq := fun n => commonPayoffBlockChannel
    (markedClosedSegmentExperiment (tseq n) E L).K T.K
  let K := commonPayoffBlockChannel
    (markedClosedSegmentExperiment t E L).K T.K
  have hK : ChannelConverges Kseq K := by
    intro a z
    rcases a with a | a
    · rcases z with ⟨o, rs⟩
      rcases rs with (r | s) | u
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inl r)
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inr s)
      · exact tendsto_const_nhds
    · rcases z with ⟨o, rs⟩
      rcases rs with (r | s) | u
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
  have hleft : DistConverges
      (fun _ => (leftBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (leftBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  have hright : DistConverges
      (fun _ => (rightBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (rightBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  change F.rel K (leftBlockDist q) (rightBlockDist q)
  exact h.a2 Kseq K
    (fun _ => leftBlockDist q) (fun _ => rightBlockDist q)
    (leftBlockDist q) (rightBlockDist q)
    hK hleft hright (by
      intro n
      change F.rel (Kseq n) (leftBlockDist q) (rightBlockDist q)
      simpa [Kseq, MarkedPairWeak, pairWeak] using hrel n)

theorem markedPairWeak_closedSegment_limit_right
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A)
    {tseq : ℕ → HMUnitInterval} {t : HMUnitInterval}
    (ht : Tendsto tseq atTop (𝓝 t))
    (T E L : MarkedTerminalExperiment O A)
    (hrel : ∀ n,
      MarkedPairWeak F q T q (markedClosedSegmentExperiment (tseq n) E L)) :
    MarkedPairWeak F q T q (markedClosedSegmentExperiment t E L) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype L.RecordType := L.recordFintype
  letI : DecidableEq L.RecordType := L.recordDecEq
  letI : Nonempty L.RecordType := L.recordNonempty
  letI : Fintype T.RecordType := T.recordFintype
  letI : DecidableEq T.RecordType := T.recordDecEq
  letI : Nonempty T.RecordType := T.recordNonempty
  let Kseq := fun n => commonPayoffBlockChannel T.K
    (markedClosedSegmentExperiment (tseq n) E L).K
  let K := commonPayoffBlockChannel T.K
    (markedClosedSegmentExperiment t E L).K
  have hK : ChannelConverges Kseq K := by
    intro a z
    rcases a with a | a
    · rcases z with ⟨o, rs⟩
      rcases rs with u | (r | s)
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
      · exact tendsto_const_nhds
    · rcases z with ⟨o, rs⟩
      rcases rs with u | (r | s)
      · exact tendsto_const_nhds
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inl r)
      · simpa [Kseq, K, commonPayoffBlockChannel,
          sumPayoffRecordEquiv, Relabeling.relabelChannel, blockChannel] using
          markedClosedSegment_channelConverges ht E L a (o, Sum.inr s)
  have hleft : DistConverges
      (fun _ => (leftBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (leftBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  have hright : DistConverges
      (fun _ => (rightBlockDist q : TraceableAgency.Dist (A ⊕ A)))
      (rightBlockDist q) := by
    intro a
    exact tendsto_const_nhds
  change F.rel K (leftBlockDist q) (rightBlockDist q)
  exact h.a2 Kseq K
    (fun _ => leftBlockDist q) (fun _ => rightBlockDist q)
    (leftBlockDist q) (rightBlockDist q)
    hK hleft hright (by
      intro n
      change F.rel (Kseq n) (leftBlockDist q) (rightBlockDist q)
      simpa [Kseq, MarkedPairWeak, pairWeak] using hrel n)

theorem markedTerminalMixtureRel_segment_calibration
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (high target low : MarkedTerminalMixtureSpace (O := O) (A := A) q)
    (hhigh : markedTerminalMixtureRel F h q hq high target)
    (hlow : markedTerminalMixtureRel F h q hq target low) :
    ∃ t : HMUnitInterval,
      HMIndiff (markedTerminalMixtureRel F h q hq) target
        (hmSegment (markedTerminalAbstractConvexMixtureSpace q)
          t high low) := by
  induction high using Quotient.inductionOn with
  | _ E =>
    induction target using Quotient.inductionOn with
    | _ T =>
      induction low using Quotient.inductionOn with
      | _ L =>
        let M := markedTerminalAbstractConvexMixtureSpace
          (O := O) (A := A) q
        let Rel := markedTerminalMixtureRel
          (O := O) (A := A) F h q hq
        let upper : Set HMUnitInterval :=
          {t | Rel (hmSegment M t
            (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦L⟧) ⟦T⟧}
        let lower : Set HMUnitInterval :=
          {t | Rel ⟦T⟧ (hmSegment M t
            (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦L⟧)}
        have hupperClosed : IsClosed upper := by
          apply IsSeqClosed.isClosed
          intro tseq t htmem htt
          have hraw : ∀ n,
              MarkedPairWeak F q
                (markedClosedSegmentExperiment (tseq n) E L) q T := by
            intro n
            apply (markedTerminalMixtureRel_mk F h q hq
              (markedClosedSegmentExperiment (tseq n) E L) T).1
            rw [markedClosedSegment_quotient_eq_hmSegment]
            exact htmem n
          have hlim := markedPairWeak_closedSegment_limit_left
            F h q htt E L T hraw
          change Rel (hmSegment M t ⟦E⟧ ⟦L⟧) ⟦T⟧
          rw [← markedClosedSegment_quotient_eq_hmSegment]
          exact (markedTerminalMixtureRel_mk F h q hq
            (markedClosedSegmentExperiment t E L) T).2 hlim
        have hlowerClosed : IsClosed lower := by
          apply IsSeqClosed.isClosed
          intro tseq t htmem htt
          have hraw : ∀ n,
              MarkedPairWeak F q T q
                (markedClosedSegmentExperiment (tseq n) E L) := by
            intro n
            apply (markedTerminalMixtureRel_mk F h q hq T
              (markedClosedSegmentExperiment (tseq n) E L)).1
            rw [markedClosedSegment_quotient_eq_hmSegment]
            exact htmem n
          have hlim := markedPairWeak_closedSegment_limit_right
            F h q htt T E L hraw
          change Rel ⟦T⟧ (hmSegment M t ⟦E⟧ ⟦L⟧)
          rw [← markedClosedSegment_quotient_eq_hmSegment]
          exact (markedTerminalMixtureRel_mk F h q hq T
            (markedClosedSegmentExperiment t E L)).2 hlim
        have honeUpper : hmUnitOne ∈ upper := by
          simpa [upper, M, Rel] using hhigh
        have hzeroLower : hmUnitZero ∈ lower := by
          simpa [lower, M, Rel] using hlow
        by_contra hinter
        have hdisjoint : upper ∩ lower = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro t ht
          exact hinter ⟨t, ht.2, ht.1⟩
        have hcover :
            (Set.univ : Set HMUnitInterval) ⊆ upperᶜ ∪ lowerᶜ := by
          intro t _ht
          by_cases hu : t ∈ upper
          · right
            intro hl
            have : t ∈ upper ∩ lower := ⟨hu, hl⟩
            rw [hdisjoint] at this
            exact this
          · exact Or.inl hu
        have hleftNonempty :
            ((Set.univ : Set HMUnitInterval) ∩ upperᶜ).Nonempty := by
          refine ⟨hmUnitZero, Set.mem_univ _, ?_⟩
          intro hzUpper
          have : hmUnitZero ∈ upper ∩ lower := ⟨hzUpper, hzeroLower⟩
          rw [hdisjoint] at this
          exact this
        have hrightNonempty :
            ((Set.univ : Set HMUnitInterval) ∩ lowerᶜ).Nonempty := by
          refine ⟨hmUnitOne, Set.mem_univ _, ?_⟩
          intro hoLower
          have : hmUnitOne ∈ upper ∩ lower := ⟨honeUpper, hoLower⟩
          rw [hdisjoint] at this
          exact this
        have hboth :=
          isPreconnected_univ upperᶜ lowerᶜ
            hupperClosed.isOpen_compl hlowerClosed.isOpen_compl
            hcover hleftNonempty hrightNonempty
        rcases hboth with ⟨t, _htuniv, hnotUpper, hnotLower⟩
        rcases markedTerminalMixtureRel_complete F h q hq
            (hmSegment M t ⟦E⟧ ⟦L⟧) ⟦T⟧ with hST | hTS
        · exact hnotUpper hST
        · exact hnotLower hTS

theorem markedTerminalHMCalibratableWeakOrder
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    HMCalibratableWeakOrder
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq) where
  complete := markedTerminalMixtureRel_complete F h q hq
  transitive := markedTerminalMixtureRel_transitive F h q hq
  independence := markedTerminalMixtureRel_independence F h q hq
  segment_calibration :=
    markedTerminalMixtureRel_segment_calibration F h q hq

noncomputable def markedTerminalAffineUtilityRepresentation
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport) :
    AffineUtilityRepresentation
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq) :=
  Classical.choice
    (genericHersteinMilnorAffineUtility_of_calibratable
      (markedTerminalAbstractConvexMixtureSpace (O := O) (A := A) q)
      (markedTerminalMixtureRel (O := O) (A := A) F h q hq)
      (markedTerminalHMCalibratableWeakOrder F h q hq))

theorem markedTerminalAffineUtility_represents_mk
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    MarkedPairWeak F q E q G ↔
      (markedTerminalAffineUtilityRepresentation F h q hq).utility
          (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ≥
        (markedTerminalAffineUtilityRepresentation F h q hq).utility
          (⟦G⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) := by
  rw [← markedTerminalMixtureRel_mk F h q hq E G]
  exact (markedTerminalAffineUtilityRepresentation F h q hq).represents _ _

theorem markedTerminalAffineUtility_affine_mk
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (t : Set.Ioo (0 : ℝ) 1) (E R : MarkedTerminalExperiment O A) :
    (markedTerminalAffineUtilityRepresentation F h q hq).utility
        (⟦markedPublicMixExperiment t.1 t.2.1 t.2.2 E R⟧ :
          MarkedTerminalMixtureSpace (O := O) (A := A) q) =
      t.1 * (markedTerminalAffineUtilityRepresentation F h q hq).utility
          (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) +
        (1 - t.1) *
          (markedTerminalAffineUtilityRepresentation F h q hq).utility
            (⟦R⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) := by
  simpa [markedTerminalAbstractConvexMixtureSpace] using
    (markedTerminalAffineUtilityRepresentation F h q hq).affine t
      (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q) ⟦R⟧

noncomputable def markedAffineUtility
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E : MarkedTerminalExperiment O A) : ℝ :=
  (markedTerminalAffineUtilityRepresentation F h q hq).utility
    (⟦E⟧ : MarkedTerminalMixtureSpace (O := O) (A := A) q)

theorem markedAffineUtility_respects_sameMarkedTerminalLaw
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' : MarkedTerminalExperiment O A)
    (hsame : SameMarkedTerminalLaw q E E') :
    markedAffineUtility F h q hq E = markedAffineUtility F h q hq E' := by
  unfold markedAffineUtility
  congr 1
  exact Quotient.sound hsame

theorem markedAffineUtility_represents
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E G : MarkedTerminalExperiment O A) :
    MarkedPairWeak F q E q G ↔
      markedAffineUtility F h q hq E ≥ markedAffineUtility F h q hq G := by
  exact markedTerminalAffineUtility_represents_mk F h q hq E G

theorem markedAffineUtility_publicMix
    (F : FixedPayoffPrefFamily O) (h : AffineAxioms F)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E R : MarkedTerminalExperiment O A) :
    markedAffineUtility F h q hq
        (markedPublicMixExperiment t ht0 ht1 E R) =
      t * markedAffineUtility F h q hq E +
        (1 - t) * markedAffineUtility F h q hq R := by
  let ti : Set.Ioo (0 : ℝ) 1 := ⟨t, ht0, ht1⟩
  exact markedTerminalAffineUtility_affine_mk F h q hq ti E R

/-- Lemma 11(b), directly with precisely its six numbered axioms. -/
theorem terminal_affine_exists_v11
    (F : FixedPayoffPrefFamily O)
    (h1 : A1_WeakOrder F) (h2 : A2_Continuity F)
    (h5 : A5_BlockComparisonCoherence F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F) (h8 : A8_RecordwiseSureThing F)
    (q : Dist A) (hq : q.FullSupport) :
    ∃ W : MarkedTerminalExperiment O A → ℝ,
      (∀ E G, MarkedPairWeak F q E q G ↔ W E ≥ W G) ∧
      (∀ (t : Set.Ioo (0 : ℝ) 1) E G,
        W (markedPublicMixExperiment t.1 t.2.1 t.2.2 E G) =
          t.1 * W E + (1 - t.1) * W G) ∧
      (∀ E G, SameMarkedTerminalLaw q E G → W E = W G) := by
  let h := affineAxioms_of_paper F h1 h2 h5 h6 h7 h8
  refine ⟨markedAffineUtility F h q hq, ?_, ?_, ?_⟩
  · exact markedAffineUtility_represents F h q hq
  · intro t E G
    exact markedAffineUtility_publicMix F h q hq t.1 t.2.1 t.2.2 E G
  · exact markedAffineUtility_respects_sameMarkedTerminalLaw F h q hq

end TraceableAgency.Theorem1.V11
