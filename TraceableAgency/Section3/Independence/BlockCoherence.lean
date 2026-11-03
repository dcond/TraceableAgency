import TraceableAgency.Section3.Independence.Basic

/-!
# Independence of block coherence

A bonus equal to the product of all action probabilities is continuous and
vanishes on every block-supported comparison. It therefore escapes A6--A8,
but duplication can remove a strictly valued full-support bonus.
-/

namespace TraceableAgency.Section3.Independence

open TraceableAgency Theorem1 Filter Topology

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]

noncomputable def supportBonus {A : Type u} [Fintype A] (q : Dist A) : ℝ :=
  ∏ a, q a

@[simp] theorem supportBonus_inl {A B : Type u} [Fintype A] [Fintype B]
    [Nonempty B] (q : Dist A) : supportBonus (inlDist (B := B) q) = 0 := by
  classical
  exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inr (Classical.arbitrary B))) rfl

@[simp] theorem supportBonus_inr {A B : Type u} [Fintype A] [Fintype B]
    [Nonempty A] (q : Dist B) : supportBonus (inrDist (A := A) q) = 0 := by
  classical
  exact Finset.prod_eq_zero (Finset.mem_univ (Sum.inl (Classical.arbitrary A))) rfl

@[simp] theorem supportBonus_pure {A : Type u} [Fintype A] [DecidableEq A]
    [Nontrivial A] (a : A) : supportBonus (Dist.pure a) = 0 := by
  obtain ⟨b, hb⟩ := exists_ne a
  exact Finset.prod_eq_zero (Finset.mem_univ b) (by simp [Dist.pure_apply, hb])

noncomputable def supportBonusFamily (v : O → ℝ) : FixedPayoffPrefFamily O :=
  scoreFamily (fun q K => traceTemperedValue v 1 q K + supportBonus q)

theorem supportBonus_pairWeak (v : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (supportBonusFamily v) q K p L ↔ pairWeak (traceScoreFamily v 1) q K p L := by
  unfold pairWeak supportBonusFamily traceScoreFamily scoreFamily
  simp only [leftBlockDist, rightBlockDist, supportBonus_inl, supportBonus_inr, add_zero]

theorem supportBonus_a2 (v : O → ℝ) : A2_Continuity (supportBonusFamily v) := by
  apply scoreFamily_a2
  intro A R _ _ _ _ _ _ Kn K qn q hK hq
  exact (tendsto_traceTemperedValue_of_converges v 1 Kn K qn q hK hq).add
    (tendsto_finsetProd _ fun a _ => hq a)

theorem supportBonus_a3 (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) :
    A3_MaterialRelevance (supportBonusFamily v) := by
  obtain ⟨op, om, hne, hstrict⟩ :=
    (traceTemperedAxiomsV10_of_representation hv (by norm_num : (0:ℝ)<1)
      (traceScoreFamily_rep v 1)).a3
  refine ⟨op, om, hne, ?_⟩
  simpa only [FixedPayoffPrefFamily.strictRel, supportBonusFamily, traceScoreFamily,
    scoreFamily, materialRelevanceBetterPrior, materialRelevanceWorsePrior,
    supportBonus_pure, add_zero] using hstrict

theorem supportBonus_a4 (v : O → ℝ) (hv : ¬ IsConstantPayoffIndex v) :
    A4_TraceRelevance (supportBonusFamily v) := by
  obtain ⟨o, hstrict⟩ :=
    (traceTemperedAxiomsV10_of_representation hv (by norm_num : (0:ℝ)<1)
      (traceScoreFamily_rep v 1)).a4
  refine ⟨o, ?_⟩
  simpa only [FixedPayoffPrefFamily.strictRel, supportBonusFamily, traceScoreFamily,
    scoreFamily, traceRelevanceRevealingPrior, traceRelevanceUnrevealingPrior,
    supportBonus_inl, supportBonus_inr, add_zero] using hstrict

theorem supportBonus_a6 (v : O → ℝ) : A6_RecordDataProcessing (supportBonusFamily v) := by
  intro A R S _ _ _ _ _ _ _ _ _ K T q
  rw [supportBonus_pairWeak]
  exact traceScoreFamily_a6 v 1 (by norm_num) K T q

theorem supportBonus_a7 (v : O → ℝ) : A7_ActionDataProcessing (supportBonusFamily v) := by
  intro A B R _ _ _ _ _ _ _ _ _ K q S Kh hc
  rw [supportBonus_pairWeak]
  exact traceScoreFamily_a7 v 1 (by norm_num) K q S Kh hc

theorem supportBonus_a8 (v : O → ℝ) : A8_RecordwiseSureThing (supportBonusFamily v) := by
  intro A R _ _ _ _ _ _ q P K L M hy
  simp only [supportBonus_pairWeak]
  exact traceScoreFamily_a8 v 1 (by norm_num) q P K L M hy

theorem supportBonus_not_a5 [Nonempty O] (v : O → ℝ) :
    ¬ A5_BlockComparisonCoherence (supportBonusFamily v) := by
  intro h
  let o : O := Classical.arbitrary O
  let K := uninformativeAtPayoff (A := RelevanceBit.{u}) o
  let p : Dist RelevanceBit.{u} := Dist.pure (ULift.up false)
  let q : Dist RelevanceBit.{u} := Dist.uniform
  have hp : supportBonus p = 0 := supportBonus_pure _
  have hq : supportBonus q = (1:ℝ)/4 := by
    norm_num [supportBonus, q, Dist.uniform_apply, RelevanceBit]
  have hpair : pairWeak (supportBonusFamily v) p K q K := by
    rw [supportBonus_pairWeak, pairWeak_iff_value_ge (traceScoreFamily_rep v 1)]
    simp only [K, traceTemperedValue_uninformativeAtPayoff, le_refl]
  have hc := (h.duplication K p q).mpr hpair
  change traceTemperedValue v 1 p K + supportBonus p ≥
    traceTemperedValue v 1 q K + supportBonus q at hc
  rw [hp, hq, show K = uninformativeAtPayoff o from rfl,
    traceTemperedValue_uninformativeAtPayoff, traceTemperedValue_uninformativeAtPayoff] at hc
  linarith

theorem supportBonus_counterexample [Nonempty O] (v : O → ℝ)
    (hv : ¬ IsConstantPayoffIndex v) :
    let F := supportBonusFamily v
    A1_WeakOrder F ∧ A2_Continuity F ∧ A3_MaterialRelevance F ∧ A4_TraceRelevance F ∧
    ¬ A5_BlockComparisonCoherence F ∧ A6_RecordDataProcessing F ∧
    A7_ActionDataProcessing F ∧ A8_RecordwiseSureThing F := by
  exact ⟨scoreFamily_a1 _, supportBonus_a2 v, supportBonus_a3 v hv,
    supportBonus_a4 v hv, supportBonus_not_a5 v, supportBonus_a6 v,
    supportBonus_a7 v, supportBonus_a8 v⟩

end TraceableAgency.Section3.Independence
