import TraceableAgency.Section3.UniquenessAffine

/-! # Uniqueness of the material index and information coefficient -/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1

universe u

variable {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
variable {F : FixedPayoffPrefFamily O}

/-- Any two trace-tempered representations of the complete preference family
have the same positive affine change of units for material and trace values. -/
theorem traceTempered_parameters_unique
    {u v : O → ℝ} {lambda mu : ℝ}
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda)
    (hrep' : WithinChannelRepresentation F v mu) :
    ∃ alpha beta : ℝ, 0 < alpha ∧
      (∀ o, v o = alpha * u o + beta) ∧ mu = alpha * lambda := by
  obtain ⟨alpha, beta, halpha, hform⟩ :=
    positiveAffine_of_commonScale_branchAdditive hlambda hrep
      (commonScale_valueIndex hrep') (branchAdditive_valueIndex v mu)
  have huv (o : O) : v o = alpha * u o + beta := by
    have h := hform (.ofChannel (Dist.pure PUnit.unit) (deterministicPayoffChannel o))
    dsimp only [valueIndex, FiniteExperiment.ofChannel] at h
    simpa only [traceTemperedValue_deterministicPayoffChannel] using h
  refine ⟨alpha, beta, halpha, huv, ?_⟩
  let o : O := Classical.choice ‹Nonempty O›
  let q : Dist RelevanceBit.{u} := Dist.uniform
  have hH : 0 < entropy q :=
    entropy_pos_of_fullSupport_nontrivial q Dist.uniform_fullSupport
  have h := hform (.ofChannel q (fullRevealAtPayoff o))
  dsimp only [valueIndex, FiniteExperiment.ofChannel] at h
  rw [traceTemperedValue_fullRevealAtPayoff, traceTemperedValue_fullRevealAtPayoff, huv o] at h
  have hz : (mu - alpha * lambda) * entropy q = 0 := by nlinarith only [h]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt hH))

/-- Fixing the utilities of any two materially distinct outcomes fixes both
parameters, without requiring that the chosen numerical anchors be zero/one. -/
theorem traceTempered_parameters_unique_of_common_anchors
    {u v : O → ℝ} {lambda mu : ℝ}
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda)
    (hrep' : WithinChannelRepresentation F v mu)
    (lo hi : O) (hne : u lo ≠ u hi)
    (hlo : v lo = u lo) (hhi : v hi = u hi) :
    v = u ∧ mu = lambda := by
  obtain ⟨alpha, beta, _, huv, hmu⟩ := traceTempered_parameters_unique hlambda hrep hrep'
  have h0 := huv lo
  have h1 := huv hi
  rw [hlo] at h0
  rw [hhi] at h1
  have hz : (alpha - 1) * (u lo - u hi) = 0 := by nlinarith only [h0, h1]
  have halpha : alpha = 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hne))
  have hbeta : beta = 0 := by rw [halpha] at h0; linarith
  constructor
  · funext o
    simpa [halpha, hbeta] using huv o
  · simpa [halpha] using hmu

 theorem normalized_trace_coefficient_unique
    {u v : O → ℝ} {lambda mu : ℝ}
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda)
    (hrep' : WithinChannelRepresentation F v mu)
    (lo hi : O) (hu0 : u lo = 0) (hu1 : u hi = 1)
    (hv0 : v lo = 0) (hv1 : v hi = 1) : mu = lambda := by
  exact (traceTempered_parameters_unique_of_common_anchors hlambda hrep hrep' lo hi
    (by rw [hu0, hu1]; norm_num) (hv0.trans hu0.symm) (hv1.trans hu1.symm)).2

/-- The information coefficient measured in any fixed nonzero material
utility gap is independent of the representing parameters. -/
theorem trace_coefficient_per_material_gap_unique
    {u v : O → ℝ} {lambda mu : ℝ}
    (hlambda : 0 < lambda)
    (hrep : WithinChannelRepresentation F u lambda)
    (hrep' : WithinChannelRepresentation F v mu)
    (lo hi : O) (hne : u hi ≠ u lo) :
    mu / (v hi - v lo) = lambda / (u hi - u lo) := by
  obtain ⟨alpha, beta, halpha, huv, hmu⟩ := traceTempered_parameters_unique hlambda hrep hrep'
  rw [hmu, huv hi, huv lo]
  have hgap : alpha * u hi + beta - (alpha * u lo + beta) = alpha * (u hi - u lo) := by ring
  rw [hgap, mul_div_mul_left _ _ (ne_of_gt halpha)]

end TraceableAgency.Section3
