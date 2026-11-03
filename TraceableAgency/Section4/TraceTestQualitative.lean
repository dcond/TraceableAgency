import TraceableAgency.Section4.TraceTest
import TraceableAgency.Section4.InformationZero
import TraceableAgency.Theorem1.PureTrace

namespace TraceableAgency.Section4

open TraceableAgency Theorem1 Section3

universe u

variable {O : Type u} [Fintype O] [DecidableEq O]
variable {A R : Type u}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype R] [DecidableEq R] [Nonempty R]

def PaysSurely (K : Channel A (O × R)) (o : O) : Prop :=
  ∀ a o' r, o' ≠ o → K a (o',r) = 0

theorem paysSurely_iff_constantPayoffLift (K : Channel A (O × R)) (o : O) :
    PaysSurely K o ↔ ∃ P : Channel A R, K = constantPayoffLift o P := by
  constructor
  · intro h
    let P : Channel A R := fun a =>
      { prob := fun r => K a (o,r)
        nonneg := fun r => (K a).nonneg (o,r)
        sum_eq_one := by
          have hs := (K a).sum_eq_one
          rw [Fintype.sum_prod_type, Finset.sum_eq_single o] at hs
          · exact hs
          · intro o' _ ho
            simp [h a o' _ ho]
          · simp }
    refine ⟨P, ?_⟩
    ext a z
    rcases z with ⟨o',r⟩
    by_cases ho : o' = o
    · subst o'
      simp [constantPayoffLift_apply_same,P]
    · simp [constantPayoffLift_apply, ho, h a o' r ho]
  · rintro ⟨P,rfl⟩
    intro a o' r ho
    simp [constantPayoffLift_apply,ho]

theorem constantPayoffLift_redraw (o : O) (P : Channel A R)
    {S : Type u} [Fintype S] [DecidableEq S] (d : Dist S) :
    recordPostprocess (constantPayoffLift o P) (redrawRecordProcessor d) =
      constantPayoffLift o (fun _ : A => d) := by
  rw [show redrawRecordProcessor (O := O) (R := R) d =
      liftRecordProcessor (fun _ : R => d) by rfl,
    ← constantPayoffLift_postprocess]
  congr 1
  ext a s
  simp only [Channel.postprocess]
  rw [← Finset.sum_mul, (P a).sum_eq_one, one_mul]

theorem constantPayoffLift_erase (o : O) (P : Channel A R) :
    recordPostprocess (constantPayoffLift o P) eraseAllRecordsProcessor =
      uninformativeAtPayoff o := by
  change recordPostprocess (constantPayoffLift o P)
    (redrawRecordProcessor (Dist.pure (PUnit.unit : PUnit.{u+1}))) = _
  rw [constantPayoffLift_redraw]
  ext a z
  rcases z with ⟨o',r⟩
  cases r
  simp [constantPayoffLift_apply,uninformativeAtPayoff,Dist.pure_apply]

theorem silent_prior_comparison (F : FixedPayoffPrefFamily O) (h7 : A7_ActionDataProcessing F)
    (o : O) (q p : Dist A) :
    pairWeak F q (uninformativeAtPayoff o) p (uninformativeAtPayoff o) := by
  have he : (payoffLotteryChannel (A := A) (Dist.pure o) : Channel A (O × PUnit.{u+1})) = uninformativeAtPayoff o := by
    ext a z
    rcases z with ⟨o',r⟩
    cases r
    simp [payoffLotteryChannel_apply, uninformativeAtPayoff, Dist.pure_apply]
  have hh := payoffLottery_pairWeak F h7 (Dist.pure o) q p
  change pairWeak F q (payoffLotteryChannel (A := A) (Dist.pure o) : Channel A (O × PUnit.{u+1}))
    p (payoffLotteryChannel (A := A) (Dist.pure o) : Channel A (O × PUnit.{u+1})) at hh
  rw [he] at hh
  exact hh

theorem pure_action_output_independent (K : Channel A (O × R)) (a : A) :
    ActionOutputIndependent (Dist.pure a) K := by
  intro b z
  have hm : Channel.outcomeMarginal K (Dist.pure a) = K a := by
    ext z
    simp [Channel.outcomeMarginal_apply, Dist.pure_apply]
  rw [hm]
  by_cases hb : b = a <;> simp [Dist.pure_apply,hb]

theorem silent_to_constantPayoffLift_of_independent
    (F : FixedPayoffPrefFamily O) (h1 : A1_WeakOrder F)
    (h5 : A5_BlockComparisonCoherence F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F)
    (o : O) (P : Channel A R) (q : Dist A)
    (hi : ActionOutputIndependent q (constantPayoffLift o P)) :
    pairWeak F q (uninformativeAtPayoff o) q (constantPayoffLift o P) := by
  let d := Channel.outcomeMarginal P q
  let C := constantPayoffLift o (fun _ : A => d)
  have hgen : recordPostprocess (uninformativeAtPayoff (A := A) o)
      (redrawRecordProcessor d) = C := by
    rw [← constantPayoffLift_uninformative]
    exact constantPayoffLift_redraw o _ d
  have hfirst : pairWeak F q (uninformativeAtPayoff o) q C := by
    simpa [hgen] using h6 (uninformativeAtPayoff (A := A) o) (redrawRecordProcessor d) q
  have hlast : pairWeak F q C q (constantPayoffLift o P) := by
    apply pairWeak_of_samePriorJointLaw F h7
    intro a z
    rcases z with ⟨o',r⟩
    by_cases ho : o' = o
    · subst o'
      have hh := hi a (o,r)
      simpa [C,d,Channel.outcomeMarginal_apply,constantPayoffLift_apply] using hh.symm
    · simp [C,constantPayoffLift_apply,ho]
  exact pairWeak_transitive_of_structural F h1 h5 _ _ _ _ _ _ hfirst hlast

/-- The weak part needs exactly A1 and A5--A7, including boundary priors. -/
theorem qualitative_trace_weak
    (F : FixedPayoffPrefFamily O) (h1 : A1_WeakOrder F)
    (h5 : A5_BlockComparisonCoherence F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F)
    (K : Channel A (O × R)) (o : O) (hpay : PaysSurely K o) (q : Dist A) (a : A) :
    F.rel K q (Dist.pure a) := by
  obtain ⟨P,rfl⟩ := (paysSurely_iff_constantPayoffLift K o).mp hpay
  have hfirst : pairWeak F q (constantPayoffLift o P) q (uninformativeAtPayoff o) := by
    simpa [constantPayoffLift_erase] using h6 (constantPayoffLift o P) eraseAllRecordsProcessor q
  have hmid := silent_prior_comparison F h7 o q (Dist.pure a)
  have hlast := silent_to_constantPayoffLift_of_independent F h1 h5 h6 h7 o P (Dist.pure a)
    (pure_action_output_independent _ a)
  exact (h5.duplication _ _ _).mpr
    (pairWeak_transitive_of_structural F h1 h5 _ _ _ _ _ _ hfirst
      (pairWeak_transitive_of_structural F h1 h5 _ _ _ _ _ _ hmid hlast))

theorem qualitative_trace_independent
    (F : FixedPayoffPrefFamily O) (h1 : A1_WeakOrder F)
    (h5 : A5_BlockComparisonCoherence F) (h6 : A6_RecordDataProcessing F)
    (h7 : A7_ActionDataProcessing F)
    (K : Channel A (O × R)) (o : O) (hpay : PaysSurely K o)
    (q : Dist A) (hi : ActionOutputIndependent q K) (a : A) :
    F.indiffRel K q (Dist.pure a) := by
  refine ⟨qualitative_trace_weak F h1 h5 h6 h7 K o hpay q a, ?_⟩
  obtain ⟨P,rfl⟩ := (paysSurely_iff_constantPayoffLift K o).mp hpay
  have hfirst : pairWeak F (Dist.pure a) (constantPayoffLift o P)
      (Dist.pure a) (uninformativeAtPayoff o) := by
    simpa [constantPayoffLift_erase] using
      h6 (constantPayoffLift o P) eraseAllRecordsProcessor (Dist.pure a)
  have hmid := silent_prior_comparison F h7 o (Dist.pure a) q
  have hlast := silent_to_constantPayoffLift_of_independent F h1 h5 h6 h7 o P q hi
  exact (h5.duplication _ _ _).mpr
    (pairWeak_transitive_of_structural F h1 h5 _ _ _ _ _ _ hfirst
      (pairWeak_transitive_of_structural F h1 h5 _ _ _ _ _ _ hmid hlast))

/-- Adding A4 yields one constant-payoff lottery strictly above every pure action. -/
theorem qualitative_trace_strict_exists
    (F : FixedPayoffPrefFamily O) (h1 : A1_WeakOrder F)
    (h4 : A4_TraceRelevance F) (h5 : A5_BlockComparisonCoherence F)
    (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F) :
    ∃ o : O, ∀ a : TraceActions.{u},
      F.strictRel (traceRelevanceBenchmarkChannel.{u,u,u} o)
        traceRelevanceRevealingPrior.{u,u} (Dist.pure a) := by
  obtain ⟨o,hs⟩ := h4
  refine ⟨o,fun a => ?_⟩
  have hp : PaysSurely (traceRelevanceBenchmarkChannel.{u,u,u} o) o := by
    intro b o' r ho
    cases b <;> simp [traceRelevanceBenchmarkChannel, Dist.pure_apply, ho]
  have hi := (mutualInfo_eq_zero_iff_independent _ _).mp (trace_unrevealing_information o)
  have he := qualitative_trace_independent F h1 h5 h6 h7 _ o hp
    traceRelevanceUnrevealingPrior hi a
  refine ⟨(h1 _).2 _ _ _ hs.1 he.1, ?_⟩
  intro hh
  exact hs.2 ((h1 _).2 _ _ _ he.1 hh)

end TraceableAgency.Section4
