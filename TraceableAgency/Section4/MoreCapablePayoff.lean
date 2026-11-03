import TraceableAgency.Section4.MoreCapable

/-! Proposition 30's counterexample inside any fixed finite payoff alphabet.
The alphabet may contain any number of other payoffs: the two channels use
one common sure payoff, and only their record technologies differ. -/
namespace TraceableAgency.Section4.MoreCapable
open TraceableAgency Theorem1
universe u

private theorem sum_lift {X : Type} [Fintype X] (f : ULift.{u} X → ℝ) :
    (∑ x, f x) = ∑ x, f (ULift.up x) :=
  (Equiv.sum_comp (Equiv.ulift.symm : X ≃ ULift.{u} X) f).symm

private noncomputable def lowerDist {X : Type} [Fintype X]
    (q : Dist (ULift.{u} X)) : Dist X where
  prob x := q (ULift.up x)
  nonneg x := q.nonneg _
  sum_eq_one := by rw [← sum_lift]; exact q.sum_eq_one

private noncomputable def liftChannel {A R : Type} [Fintype A] [Fintype R]
    (K : Channel A R) : Channel (ULift.{u} A) (ULift.{u} R) := fun a =>
  { prob := fun r => K a.down r.down
    nonneg := fun r => (K a.down).nonneg r.down
    sum_eq_one := by rw [sum_lift]; exact (K a.down).sum_eq_one }

private theorem mutualInfo_liftChannel {A R : Type} [Fintype A] [Fintype R]
    (K : Channel A R) (q : Dist (ULift.{u} A)) :
    mutualInfo q (liftChannel K) = mutualInfo (lowerDist q) K := by
  unfold mutualInfo entropy
  simp only [sum_lift,Channel.outcomeMarginal_apply,liftChannel,lowerDist,ULift.down_up]

private theorem liftChannel_not_garbling :
    ¬ ∃ T : Channel (ULift.{u} (Bool ⊕ Unit)) (ULift.{u} Bool),
      Channel.postprocess (liftChannel erasure) T = liftChannel noisyBinary := by
  rintro ⟨T,h⟩
  apply erasure_not_garbling_noisyBinary
  refine ⟨fun r => lowerDist (T (ULift.up r)),?_⟩
  funext a
  apply Dist.ext
  intro s
  have he := congrArg
    (fun K : Channel (ULift.{u} Bool) (ULift.{u} Bool) => K (ULift.up a) (ULift.up s)) h
  simpa only [Channel.postprocess,liftChannel,lowerDist,sum_lift,ULift.down_up] using he

variable {O : Type u} [Fintype O] [DecidableEq O]

/-- The erasure experiment, paying the chosen common material outcome surely. -/
noncomputable def erasureAtPayoff (o : O) :
    Channel (ULift.{u} Bool) (O × ULift.{u} (Bool ⊕ Unit)) :=
  constantPayoffLift o (liftChannel erasure)

/-- The binary symmetric experiment, with exactly the same sure material outcome. -/
noncomputable def noisyAtPayoff (o : O) :
    Channel (ULift.{u} Bool) (O × ULift.{u} Bool) :=
  constantPayoffLift o (liftChannel noisyBinary)

theorem atPayoff_same_payoff_kernels (o : O) :
    SamePayoffKernels (erasureAtPayoff o) (noisyAtPayoff o) := by
  intro a o'
  by_cases ho : o' = o
  · subst o'
    simp only [erasureAtPayoff,noisyAtPayoff,constantPayoffLift_apply_same]
    rw [(liftChannel erasure a).sum_eq_one,(liftChannel noisyBinary a).sum_eq_one]
  · simp [erasureAtPayoff,noisyAtPayoff,constantPayoffLift_apply,ho]

theorem atPayoff_information_dominance (o : O) :
    InformationDominates (erasureAtPayoff o) (noisyAtPayoff o) := by
  intro q
  simp only [erasureAtPayoff,noisyAtPayoff,mutualInfo_constantPayoffLift,
    mutualInfo_liftChannel]
  exact erasure_moreCapable_noisyBinary (lowerDist q)

theorem atPayoff_not_record_garbling (o : O) :
    ¬ GarblingDominates (erasureAtPayoff o) (noisyAtPayoff o) := by
  rintro ⟨T,h⟩
  apply liftChannel_not_garbling
  refine ⟨fun r => T (o,r),?_⟩
  funext a
  apply Dist.ext
  intro s
  have he := congrArg
    (fun K : Channel (ULift.{u} Bool) (O × ULift.{u} Bool) => K a (o,s)) h
  simpa [recordPostprocess,Channel.postprocess,payoffPreservingRecordKernel,
    erasureAtPayoff,noisyAtPayoff,constantPayoffLift_apply,Fintype.sum_prod_type] using he

/-- For every admissible fixed payoff alphabet, more-capable dominance does
not imply payoff-preserving record garbling. The supplied payoff is the common
sure outcome, so the result also applies when the alphabet has at least two elements. -/
theorem exists_moreCapable_not_garbling_at_payoff (o : O) :
    ∃ (K : Channel (ULift.{u} Bool) (O × ULift.{u} (Bool ⊕ Unit)))
      (L : Channel (ULift.{u} Bool) (O × ULift.{u} Bool)),
      SamePayoffKernels K L ∧ InformationDominates K L ∧ ¬ GarblingDominates K L :=
  ⟨erasureAtPayoff o,noisyAtPayoff o,atPayoff_same_payoff_kernels o,
    atPayoff_information_dominance o,atPayoff_not_record_garbling o⟩

end TraceableAgency.Section4.MoreCapable
