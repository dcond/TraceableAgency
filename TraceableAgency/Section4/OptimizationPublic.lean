import TraceableAgency.Section4.OptimizationLogit
import TraceableAgency.Section4.OptimizationCollapse
import TraceableAgency.Theorem1.MaterialCalibration.Proof

/-! Preference-facing optimality and logit conclusions, with the representation
witnesses supplied by the unchanged material-first proof of A1--A8. -/
namespace TraceableAgency.Section4
open Theorem1
universe u
variable {O : Type u} [Fintype O] [DecidableEq O]

def PreferenceOptimal (F : FixedPayoffPrefFamily O)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q : Dist A) : Prop :=
  ∀ p : Dist A, F.rel K q p

noncomputable def expectedRowUtility {A R : Type u} [Fintype R]
    (v : O → ℝ) (K : Channel A (O × R)) (a : A) : ℝ :=
  ∑ z, K a z * v z.1

theorem preferenceOptimal_iff_value
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F v lambda)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q : Dist A) :
    PreferenceOptimal F K q ↔ IsOptimal (expectedRowUtility v K) lambda K q := by
  unfold PreferenceOptimal IsOptimal
  apply forall_congr'
  intro p
  exact hrep K q p

theorem preference_optimality_condition
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F v lambda) (hl : 0 < lambda)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (q : Dist A) :
    PreferenceOptimal F K q ↔ CoversRows K (Channel.outcomeMarginal K q) ∧
      ∃ c : ℝ, (∀ a, expectedRowUtility v K a +
        lambda * finiteKL (K a) (Channel.outcomeMarginal K q) ≤ c) ∧
        (∀ a, 0 < q a → expectedRowUtility v K a +
          lambda * finiteKL (K a) (Channel.outcomeMarginal K q) = c) := by
  rw [preferenceOptimal_iff_value hrep]
  exact optimal_iff_kkt _ hl K q

theorem preference_disjoint_logit
    {F : FixedPayoffPrefFamily O} {v : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F v lambda) (hl : 0 < lambda)
    {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (K : Channel A (O × R)) (hd : DisjointRows K) (q : Dist A) :
    PreferenceOptimal F K q ↔ q = logitDist (expectedRowUtility v K) lambda := by
  rw [preferenceOptimal_iff_value hrep]
  exact disjoint_optimal_iff_logit _ hl K hd q

theorem optimization_of_axioms (F : FixedPayoffPrefFamily O) (hax : TraceTemperedAxiomsV10 F) :
    ∃ (v : O → ℝ) (lambda : ℝ), ¬ IsConstantPayoffIndex v ∧ 0 < lambda ∧
      WithinChannelRepresentation F v lambda ∧ SameWitnessBlockRepresentation F v lambda ∧
      (∀ {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype R] [DecidableEq R] [Nonempty R] (K : Channel A (O × R)),
        (∃ q, PreferenceOptimal F K q) ∧
        (∀ q, PreferenceOptimal F K q ↔ CoversRows K (Channel.outcomeMarginal K q) ∧
          ∃ c, (∀ a, rowScore (expectedRowUtility v K) lambda K
            (Channel.outcomeMarginal K q) a ≤ c) ∧
          (∀ a, 0 < q a → rowScore (expectedRowUtility v K) lambda K
            (Channel.outcomeMarginal K q) a = c)) ∧
        (DisjointRows K → ∀ q, PreferenceOptimal F K q ↔
          q = logitDist (expectedRowUtility v K) lambda)) := by
  obtain ⟨v,lambda,hv,hl,hrep,hblock⟩ :=
    (MaterialCalibration.theorem1V10Clauses_material F).2 hax
  refine ⟨v,lambda,hv,hl,hrep,hblock,?_⟩
  intro A R _ _ _ _ _ _ K
  obtain ⟨q,hq⟩ := exists_optimal (expectedRowUtility v K) lambda K
  exact ⟨⟨q,(preferenceOptimal_iff_value hrep K q).mpr hq⟩,
    fun q => preference_optimality_condition hrep hl K q,
    fun hd q => preference_disjoint_logit hrep hl K hd q⟩

end TraceableAgency.Section4
