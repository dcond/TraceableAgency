import TraceableAgency.Theorem1.MaterialCalibration.Partition
import TraceableAgency.Theorem1.MaterialCalibration.Relabeling
import TraceableAgency.Theorem1.MaterialCalibration.FullRevelation

/-!
# Identifying the non-singleton partition support

The posterior after the non-singleton cell is `inlDist r`. Its positive
support is canonically the original action alphabet when `r` has full
support. The corresponding material-normalized values agree by relabeling.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {A O R : Type u}
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype O] [DecidableEq O]
variable [Fintype R] [DecidableEq R] [Nonempty R]

/-- The positive support of the left-embedded full-support prior is the
original action alphabet. -/
noncomputable def inlSupportEquiv (r : Dist A) (hr : r.FullSupport) :
    supportSubtype (inlDist r : Dist (A ⊕ PUnit.{u+1})) ≃ A where
  toFun s := Sum.elim id (fun _ => Classical.arbitrary A) s.val
  invFun a := ⟨Sum.inl a, hr a⟩
  left_inv s := by
    rcases s with ⟨a, ha⟩
    cases a with
    | inl a => rfl
    | inr b => simp at ha
  right_inv a := rfl

@[simp] theorem inlSupportEquiv_symm_val (r : Dist A) (hr : r.FullSupport) (a : A) :
    ((inlSupportEquiv r hr).symm a).val = Sum.inl a := rfl

/-- The positive support of a pure prior contains exactly its named action. -/
theorem supportSubtype_pure_subsingleton (a : A) :
    Subsingleton (supportSubtype (Dist.pure a)) := by
  have hval (s : supportSubtype (Dist.pure a)) : s.val = a := by
    by_contra hne
    have hs := s.property
    simp [Dist.pure_apply, hne] at hs
  constructor
  intro s t
  apply Subtype.ext
  exact (hval s).trans (hval t).symm

/-- The posterior support on the singleton partition cell is a singleton. -/
theorem partitionRecord_false_support_subsingleton (r : Dist A)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Subsingleton (supportSubtype
      (branchPosterior (partitionRecordChannel (A := A))
        (partitionPrior r t ht0 (le_of_lt ht1)) (ULift.up false))) := by
  rw [partitionRecord_posterior_false r t ht0 ht1]
  exact supportSubtype_pure_subsingleton (Sum.inr PUnit.unit : A ⊕ PUnit.{u+1})

/-- Restricting the posterior and renaming its support recovers `r` exactly. -/
theorem relabelDist_inlSupport (r : Dist A) (hr : r.FullSupport) :
    Relabeling.relabelDist (inlSupportEquiv r hr)
      (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport = r := by
  ext a
  rfl

/-- A channel restricted to this support becomes its original left rows. -/
theorem relabelChannel_inlSupport (r : Dist A) (hr : r.FullSupport)
    (C : Channel (A ⊕ PUnit.{u+1}) (O × R)) (K : Channel A (O × R))
    (hC : ∀ a, C (Sum.inl a) = K a) :
    Relabeling.relabelChannel (inlSupportEquiv r hr) (Equiv.refl (O × R))
      (Channel.restrictToSupport C (inlDist r)) = K := by
  ext a z
  change C (Sum.inl a) z = K a z
  rw [hC]

/-- Any continuation supported on the left cell has exactly its original
material-normalized value after support restriction. -/
theorem normalizedMarkedUtility_inlSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport)
    (C : Channel (A ⊕ PUnit.{u+1}) (O × R)) (K : Channel A (O × R))
    (hC : ∀ a, C (Sum.inl a) = K a) :
    normalizedMarkedUtility F h
        (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport
        (Dist.restrictToSupport_fullSupport _)
        (markedExperimentOfChannel (Channel.restrictToSupport C (inlDist r))) =
      normalizedMarkedUtility F h r hr (markedExperimentOfChannel K) := by
  have hv := normalizedMarkedUtility_actionEquiv F h (inlSupportEquiv r hr)
    (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport
    (Dist.restrictToSupport_fullSupport _)
    (Channel.restrictToSupport C (inlDist r))
  simpa only [relabelDist_inlSupport, relabelChannel_inlSupport r hr C K hC] using hv.symm

/-- Full revelation and any deterministic payoff profile commute with the
identification of the partition support with its original action set. -/
theorem relabelFullRevealWithPayoff_inlSupport
    (r : Dist A) (hr : r.FullSupport) (g : A → O) :
    Relabeling.relabelChannel (inlSupportEquiv r hr)
      (Equiv.prodCongr (Equiv.refl O) (inlSupportEquiv r hr))
      (fullRevealWithPayoff (fun a => g (inlSupportEquiv r hr a))) =
      fullRevealWithPayoff g := by
  ext a z
  rcases z with ⟨o, b⟩
  simp [Relabeling.relabelChannel, Relabeling.relabelDist,
    fullRevealWithPayoff, Dist.pure_apply,
    (inlSupportEquiv r hr).symm.injective.eq_iff]

/-- In particular, the full-revelation material upgrades used to define the
scale have the same normalized value on the reached support and at `r`. -/
theorem normalizedMarkedUtility_fullReveal_inlSupport
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (r : Dist A) (hr : r.FullSupport) (g : A → O) :
    normalizedMarkedUtility F h
        (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport
        (Dist.restrictToSupport_fullSupport _)
        (fullRevealWithPayoffExperiment (fun a => g (inlSupportEquiv r hr a))) =
      normalizedMarkedUtility F h r hr (fullRevealWithPayoffExperiment g) := by
  have hv := normalizedMarkedUtility_actionRecordEquiv F h
    (inlSupportEquiv r hr) (inlSupportEquiv r hr)
    (inlDist r : Dist (A ⊕ PUnit.{u+1})).restrictToSupport
    (Dist.restrictToSupport_fullSupport _)
    (fullRevealWithPayoff (fun a => g (inlSupportEquiv r hr a)))
  simpa only [relabelDist_inlSupport, relabelFullRevealWithPayoff_inlSupport,
    fullRevealWithPayoffExperiment] using hv.symm

end TraceableAgency.Theorem1.MaterialCalibration
