import TraceableAgency.Theorem1.MaterialCalibration.Proof

/-! Corollary 22: equal expected material utility and equal laws of posteriors
on actions imply indifference. The posterior law is unmarked: the joint law
of payoff and posterior is not assumed equal. -/
namespace TraceableAgency.Section3
open Theorem1
universe u

noncomputable def visibleExperiment
    {A Z : Type u} [Fintype A] [Fintype Z] [DecidableEq Z]
    (K : Channel A Z) : FiniteExperimentOn A :=
  ⟨Z, inferInstance, inferInstance, K⟩

theorem mutualInfo_eq_of_same_posterior_law
    {A Z Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (K : Channel A Z) (L : Channel A Y)
    (hlaw : SamePosteriorLawExp q (visibleExperiment K) (visibleExperiment L)) :
    mutualInfo q K = mutualInfo q L := by
  have hh := hlaw entropy continuous_entropy
  change (∑ z, Channel.outcomeMarginal K q z * entropy (Channel.posterior K q z)) =
    ∑ y, Channel.outcomeMarginal L q y * entropy (Channel.posterior L q y) at hh
  rw [mutualInfo_entropyReduction, mutualInfo_entropyReduction, hh]

theorem no_payoff_trace_complementarity_of_representation
    {O A R S : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) (v : O → ℝ) (lambda : ℝ)
    (hrep : WithinChannelRepresentation F v lambda)
    (q : Dist A) (K : Channel A (O × R)) (L : Channel A (O × S))
    (hmaterial : expectedPayoffUtility v q K = expectedPayoffUtility v q L)
    (hlaw : SamePosteriorLawExp q (visibleExperiment K) (visibleExperiment L)) :
    pairIndiff F q K q L := by
  have hi := mutualInfo_eq_of_same_posterior_law q K L hlaw
  have hv : traceTemperedValue v lambda q K = traceTemperedValue v lambda q L := by
    simp only [traceTemperedValue, hmaterial, hi]
  unfold pairIndiff
  dsimp only
  rw [hrep, hrep, traceTemperedValue_commonBlock_left,
    traceTemperedValue_commonBlock_right, hv]
  exact ⟨le_rfl, le_rfl⟩

/-- A1–A8 provide the same material utility and trace weight for the
representation and every comparison in Corollary 22. -/
theorem no_payoff_trace_complementarity_of_axioms
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (hax : TraceTemperedAxiomsV10 F) :
    ∃ (v : O → ℝ) (lambda : ℝ),
      ¬ IsConstantPayoffIndex v ∧ 0 < lambda ∧ WithinChannelRepresentation F v lambda ∧
      ∀ {A R S : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype R] [DecidableEq R] [Nonempty R]
        [Fintype S] [DecidableEq S] [Nonempty S]
        (q : Dist A) (K : Channel A (O × R)) (L : Channel A (O × S)),
        expectedPayoffUtility v q K = expectedPayoffUtility v q L →
        SamePosteriorLawExp q (visibleExperiment K) (visibleExperiment L) →
        pairIndiff F q K q L := by
  obtain ⟨v, lambda, hv, hl, hr⟩ := (MaterialCalibration.theorem1V10Clauses_material F).1.mp hax
  refine ⟨v, lambda, hv, hl, hr, ?_⟩
  intro A R S _ _ _ _ _ _ _ _ _ q K L hm hp
  exact no_payoff_trace_complementarity_of_representation F v lambda hr q K L hm hp

end TraceableAgency.Section3
