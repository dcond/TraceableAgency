import TraceableAgency.Theorem1.MaterialCalibration.TraceValue

/-!
# Continuity from material benchmarks

Fixed material lotteries calibrate every real utility threshold after mixing
the tested experiment toward the material midpoint. A2 therefore makes both
numerical contour sets closed as the prior varies. No information
representation or entropy calibration is used.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency Filter Set Topology

universe u v

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Primitive A2 closes comparisons of fixed experiments when the common
prior varies coordinatewise. -/
theorem markedPairWeak_fixedExperiments_limit
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (qseq : ℕ → Dist A) (q : Dist A)
    (hconv : DistConverges qseq q)
    (E G : MarkedTerminalExperiment O A)
    (hrel : ∀ n, MarkedPairWeak F (qseq n) E (qseq n) G) :
    MarkedPairWeak F q E q G := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  let K := commonPayoffBlockChannel E.K G.K
  have hleft : DistConverges
      (fun n ↦ (leftBlockDist (qseq n) : Dist (A ⊕ A)))
      (leftBlockDist q) := by
    intro a
    cases a with
    | inl a => exact hconv a
    | inr a => exact tendsto_const_nhds
  have hright : DistConverges
      (fun n ↦ (rightBlockDist (qseq n) : Dist (A ⊕ A)))
      (rightBlockDist q) := by
    intro a
    cases a with
    | inl a => exact tendsto_const_nhds
    | inr a => exact hconv a
  change F.rel K (leftBlockDist q) (rightBlockDist q)
  exact h.a2 (fun _ ↦ K) K
    (fun n ↦ leftBlockDist (qseq n))
    (fun n ↦ rightBlockDist (qseq n))
    (leftBlockDist q) (rightBlockDist q)
    (by intro a z; exact tendsto_const_nhds) hleft hright hrel

/-- A continuously parametrized prior has closed fixed-experiment comparison
sets. The first-countability assumption converts sequential A2 into closedness. -/
theorem isClosed_markedPairWeak_fixedExperiments
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {X : Type v} [TopologicalSpace X] [FirstCountableTopology X]
    (q : X → Dist A)
    (hcoord : ∀ a, Continuous (fun x ↦ q x a))
    (E G : MarkedTerminalExperiment O A) :
    IsClosed {x | MarkedPairWeak F (q x) E (q x) G} := by
  rw [← isSeqClosed_iff_isClosed]
  intro xseq x hmem hx
  apply markedPairWeak_fixedExperiments_limit F h (fun n ↦ q (xseq n)) (q x)
      (fun a ↦ ((hcoord a).tendsto x).comp hx) E G
  exact hmem

/-- Any real threshold becomes a material lottery after a sufficiently small
mixture with the material midpoint. -/
theorem exists_material_mixture_cut (c : ℝ) :
    ∃ t : ℝ, ∃ ht0 : 0 < t, ∃ ht1 : t < 1,
      ∃ b : ℝ, 0 < b ∧ b < 1 ∧ b = t * c + (1 - t) / 2 := by
  let t := 1 / (2 * (|c| + 1))
  have hd : 0 < 2 * (|c| + 1) := by positivity
  have ht0 : 0 < t := one_div_pos.mpr hd
  have htid : t * (2 * (|c| + 1)) = 1 := by
    dsimp [t]
    field_simp
  have ht1 : t < 1 := by
    have := abs_nonneg c
    nlinarith
  refine ⟨t, ht0, ht1, t * c + (1 - t) / 2, ?_, ?_, rfl⟩
  · have hprod : 0 ≤ t * (c + |c|) :=
      mul_nonneg (le_of_lt ht0) (by linarith [neg_le_abs c])
    nlinarith
  · have hprod : 0 ≤ t * (|c| - c) :=
      mul_nonneg (le_of_lt ht0) (by linarith [le_abs_self c])
    nlinarith

/-- Both numerical comparisons with any real cutoff are preference comparisons
between two fixed experiments, uniformly over full-support priors. -/
theorem exists_fixedExperiments_material_cut
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (E : MarkedTerminalExperiment O A) (c : ℝ) :
    ∃ T B : MarkedTerminalExperiment O A,
      ∀ (q : Dist A) (hq : q.FullSupport),
        (normalizedMarkedUtility F h q hq E ≤ c ↔
          MarkedPairWeak F q B q T) ∧
        (c ≤ normalizedMarkedUtility F h q hq E ↔
          MarkedPairWeak F q T q B) := by
  obtain ⟨t, ht0, ht1, b, hb0, hb1, hb⟩ := exists_material_mixture_cut c
  let C : MarkedTerminalExperiment O A :=
    markedPublicMixExperiment (1 / 2) (by norm_num) (by norm_num)
      (markedMaterialHighExperiment F h) (markedMaterialLowExperiment F h)
  let T := markedPublicMixExperiment t ht0 ht1 E C
  let B : MarkedTerminalExperiment O A :=
    markedPublicMixExperiment b hb0 hb1
      (markedMaterialHighExperiment F h) (markedMaterialLowExperiment F h)
  refine ⟨T, B, ?_⟩
  intro q hq
  have hC : normalizedMarkedUtility F h q hq C = 1 / 2 := by
    simp [C, normalizedMarkedUtility_publicMix]
  have hT : normalizedMarkedUtility F h q hq T =
      t * normalizedMarkedUtility F h q hq E + (1 - t) / 2 := by
    simp only [T, normalizedMarkedUtility_publicMix, hC]
    ring
  have hB : normalizedMarkedUtility F h q hq B = b := by
    simp [B, normalizedMarkedUtility_publicMix]
  rw [normalizedMarkedUtility_represents F h q hq,
    normalizedMarkedUtility_represents F h q hq,
    hT, hB, hb]
  constructor <;> constructor <;> intro hc <;> nlinarith

/-- Material normalization makes the utility of every fixed experiment
continuous along any continuously parametrized family of interior priors. -/
theorem normalizedMarkedUtility_continuous_of_coordinateContinuous
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    {X : Type v} [TopologicalSpace X] [FirstCountableTopology X]
    (q : X → Dist A) (hq : ∀ x, (q x).FullSupport)
    (hcoord : ∀ a, Continuous (fun x ↦ q x a))
    (E : MarkedTerminalExperiment O A) :
    Continuous (fun x ↦ normalizedMarkedUtility F h (q x) (hq x) E) := by
  rw [continuous_iff_lower_upperSemicontinuous]
  constructor
  · rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro c
    obtain ⟨T, B, heq⟩ := exists_fixedExperiments_material_cut F h E c
    have hs : {x | normalizedMarkedUtility F h (q x) (hq x) E ≤ c} =
        {x | MarkedPairWeak F (q x) B (q x) T} := by
      ext x
      exact (heq (q x) (hq x)).1
    change IsClosed {x | normalizedMarkedUtility F h (q x) (hq x) E ≤ c}
    rw [hs]
    exact isClosed_markedPairWeak_fixedExperiments F h q hcoord B T
  · rw [upperSemicontinuous_iff_isClosed_preimage]
    intro c
    obtain ⟨T, B, heq⟩ := exists_fixedExperiments_material_cut F h E c
    have hs : {x | c ≤ normalizedMarkedUtility F h (q x) (hq x) E} =
        {x | MarkedPairWeak F (q x) T (q x) B} := by
      ext x
      exact (heq (q x) (hq x)).2
    change IsClosed {x | c ≤ normalizedMarkedUtility F h (q x) (hq x) E}
    rw [hs]
    exact isClosed_markedPairWeak_fixedExperiments F h q hcoord T B

/-- The material-normalized entropy candidate satisfies the binary interior
continuity required by the classical Faddeev theorem. -/
theorem materialEntropy_binary_continuous
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) :
    Continuous (fun t : Set.Ioo (0 : ℝ) 1 ↦
      materialEntropy F h (faddeevBinaryDistInterior t)) := by
  have hcoord : ∀ a : ULift.{u, 0} Bool,
      Continuous (fun t : Set.Ioo (0 : ℝ) 1 ↦ faddeevBinaryDistInterior t a) := by
    intro a
    rcases a with ⟨a⟩
    cases a
    · change Continuous (fun t : Set.Ioo (0 : ℝ) 1 ↦ 1 - t.1)
      exact continuous_const.sub continuous_subtype_val
    · change Continuous (fun t : Set.Ioo (0 : ℝ) 1 ↦ t.1)
      exact continuous_subtype_val
  have hc := normalizedMarkedUtility_continuous_of_coordinateContinuous F h
    faddeevBinaryDistInterior faddeevBinaryDistInterior_fullSupport hcoord
    (fullRevealWithPayoffExperiment
      (fun _ : ULift.{u, 0} Bool ↦ materialLowOutcome F h))
  exact hc.congr (fun t ↦
    (materialEntropy_eq_fullReveal F h (faddeevBinaryDistInterior t)
      (faddeevBinaryDistInterior_fullSupport t)).symm)

end TraceableAgency.Theorem1.MaterialCalibration
