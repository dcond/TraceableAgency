import TraceableAgency.Theorem1.MaterialCalibration.PayoffSeparation
import TraceableAgency.Theorem1.Sequentialization

/-!
# Numerical assembly with a freshly identified information coefficient

The coefficient is an arbitrary parameter. The only input is the new
constant-payoff record formula; no old trace-scale construction is used.
-/

namespace TraceableAgency.Theorem1.MaterialCalibration

open TraceableAgency

universe u

/-- Numerical input supplied by the material-first entropy identification. -/
def ConstantRecordValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ) : Prop :=
  ∀ {A Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y),
    normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P (fun _ ↦ materialLowOutcome F h)) =
      lambda * mutualInfo q P

/-- Full-support value formula with a coefficient independent of the old proof. -/
def MaterialNormalizedValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ) : Prop :=
  ∀ {A R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (hq : q.FullSupport) (K : Channel A (O × R)),
    normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) =
      traceTemperedValue (materialPayoffUtility F h) lambda q K

theorem normalizedMarkedUtility_payoffBranch_formula_material
    {O A Y : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ)
    (htrace : ConstantRecordValueFormula F h lambda)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A Y) (g : Y → O) :
    normalizedMarkedUtility F h q hq (payoffBranchExperiment P g) =
      traceTemperedValue (materialPayoffUtility F h) lambda q
        (payoffBranchCompound P g) := by
  have hv := normalizedMarkedUtility_payoffBranch_difference_from_low_material
    F h q hq P g
  rw [htrace q hq P] at hv
  rw [traceTemperedValue_payoffBranchCompound]
  linarith

/-- Sequentialization changes only the naming and copying of observed records. -/
theorem normalizedMarkedUtility_sequentialization_material
    {O A R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : Dist A) (hq : q.FullSupport) (K : Channel A (O × R)) :
    letI : Nonempty O := payoffNonemptyOfChannel K
    normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) =
      normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (sequentializedChannel K)) := by
  letI : Nonempty O := payoffNonemptyOfChannel K
  have hpair := sequentialization_pairWeakEquiv F h.a4 q K
  have hf := (pairWeak_markedExperiments_iff_normalizedMarkedUtility
    F h q q hq hq (markedExperimentOfChannel K)
      (markedExperimentOfChannel (sequentializedChannel K))).mp hpair.1
  have hb := (pairWeak_markedExperiments_iff_normalizedMarkedUtility
    F h q q hq hq (markedExperimentOfChannel (sequentializedChannel K))
      (markedExperimentOfChannel K)).mp hpair.2
  exact le_antisymm hb hf

/-- Material separation and record identification give the value of every
payoff-record experiment, including singleton action alphabets. -/
theorem materialNormalizedValueFormula_of_constantRecordValueFormula
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor) (lambda : ℝ)
    (htrace : ConstantRecordValueFormula F h lambda) :
    MaterialNormalizedValueFormula F h lambda := by
  intro A R _ _ _ _ _ _ q hq K
  letI : Nonempty O := payoffNonemptyOfChannel K
  rw [normalizedMarkedUtility_sequentialization_material F h q hq K]
  change normalizedMarkedUtility F h q hq
      (payoffBranchExperiment K (fun y : O × R ↦ y.1)) = _
  rw [normalizedMarkedUtility_payoffBranch_formula_material F h lambda htrace]
  change traceTemperedValue (materialPayoffUtility F h) lambda q
      (sequentializedChannel K) = _
  unfold traceTemperedValue
  rw [expectedPayoffUtility_sequentializedChannel, mutualInfo_sequentializedChannel]

end TraceableAgency.Theorem1.MaterialCalibration
