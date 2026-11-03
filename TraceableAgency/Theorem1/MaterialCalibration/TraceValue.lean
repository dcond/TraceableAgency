import TraceableAgency.Theorem1.MaterialCalibration.BranchComparison

/-!
# Record value and material-normalized full-revelation value

The definitions are made before any information representation. Boundary
priors are evaluated on their positive support.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-- Value of a record experiment when the material payoff is the low anchor. -/
noncomputable def materialTraceValue
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y) : ℝ :=
  normalizedMarkedUtility F h q hq
    (payoffBranchExperiment P (fun _ ↦ materialLowOutcome F h))

/-- Full-revelation value at the low payoff, evaluated on positive support. -/
noncomputable def materialEntropy
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (q : Dist A) : ℝ :=
  normalizedMarkedUtility F h q.restrictToSupport
    (Dist.restrictToSupport_fullSupport q)
    (fullRevealWithPayoffExperiment
      (fun _ : supportSubtype q ↦ materialLowOutcome F h))

/-- A full-support prior has its original action alphabet as support. -/
def materialFullSupportEquiv (q : Dist A) (hq : q.FullSupport) :
    supportSubtype q ≃ A where
  toFun := Subtype.val
  invFun a := ⟨a, hq a⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem relabelDist_materialFullSupportEquiv (q : Dist A) (hq : q.FullSupport) :
    Relabeling.relabelDist (materialFullSupportEquiv q hq) q.restrictToSupport = q := by
  ext a
  rfl

theorem relabelFullReveal_materialFullSupportEquiv
    (q : Dist A) (hq : q.FullSupport) (o : O) :
    Relabeling.relabelChannel (materialFullSupportEquiv q hq)
        (Equiv.prodCongr (Equiv.refl O) (materialFullSupportEquiv q hq))
        (fullRevealWithPayoff (fun _ : supportSubtype q ↦ o)) =
      fullRevealWithPayoff (fun _ : A ↦ o) := by
  ext a z
  rcases z with ⟨o', b⟩
  simp [Relabeling.relabelChannel, Relabeling.relabelDist,
    fullRevealWithPayoff, Dist.pure_apply,
    (materialFullSupportEquiv q hq).symm.injective.eq_iff]

/-- On an interior prior, the support-based definition is the ordinary
material-normalized value of full revelation. -/
theorem materialEntropy_eq_fullReveal
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) :
    materialEntropy F h q =
      normalizedMarkedUtility F h q hq
        (fullRevealWithPayoffExperiment (fun _ : A ↦ materialLowOutcome F h)) := by
  have hv := normalizedMarkedUtility_actionRecordEquiv F h
    (materialFullSupportEquiv q hq) (materialFullSupportEquiv q hq)
    q.restrictToSupport (Dist.restrictToSupport_fullSupport q)
    (fullRevealWithPayoff (fun _ : supportSubtype q ↦ materialLowOutcome F h))
  simp only [relabelDist_materialFullSupportEquiv,
    relabelFullReveal_materialFullSupportEquiv] at hv
  exact hv.symm

end TraceableAgency.Theorem1.MaterialCalibration
