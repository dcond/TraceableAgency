import TraceableAgency.Section4.Binary.ComparativeStatics

/-! Complete binary classification and the unique interior first-order root.
Endpoint limits below are the finite-KL cases; missing support is handled by
the exact pure-choice threshold, without a convention for infinite real KL. -/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1 Set Filter Topology
universe u
variable {Z : Type u} [Fintype Z]

 theorem binary_exists_unique_interior_iff (p r : Dist Z) (hne : p ≠ r)
    {gap lambda : ℝ} (hg : 0 ≤ gap) (hl : 0 < lambda) :
    (∃! q, IsOptimal (binaryRewards gap) lambda (binaryChannel p r) q ∧
      q (ULift.up true) ∈ Ioo (0 : ℝ) 1) ↔
      ¬ (SupportIncluded r p ∧ lambda*finiteKL r p ≤ gap) := by
  classical
  constructor
  · rintro ⟨q,⟨hq,hint⟩,_⟩ ht
    have hp := (binary_pure_high_iff p r gap hl).mpr ht
    have he := optimal_unique_of_output_injective (binaryRewards gap) hl
      (binaryChannel p r) (binary_output_injective p r hne) q (Dist.pure (ULift.up false)) hq hp
    have hz : q (ULift.up true) = 0 := by simp [he,Dist.pure_apply]
    linarith [hint.1]
  · intro ht
    obtain ⟨q,hq,hu⟩ := binary_exists_unique_optimal p r hne gap hl
    exact ⟨q,⟨hq,binary_optimal_interior p r hne hg hl ht q hq⟩,fun s hs => hu s hs.1⟩

 theorem binary_interior_optimal_iff_equation (p r : Dist Z)
    {gap lambda : ℝ} (hl : 0 < lambda) (q : Dist RelevanceBit.{u})
    (hx : q (ULift.up true) ∈ Ioo (0 : ℝ) 1) :
    IsOptimal (binaryRewards gap) lambda (binaryChannel p r) q ↔
      gap = lambda*binaryGain p r (q (ULift.up true)) := by
  classical
  constructor
  · exact fun hq => binary_interior_equation p r hl q hq hx
  · intro he
    have hc : CoversRows (binaryChannel p r) (Channel.outcomeMarginal (binaryChannel p r) q) := by
      intro a z hz
      rw [binary_outcomeMarginal]
      rcases mixMass_pos_or_both_zero p r hx z with hh | ⟨hp,hr⟩
      · exact hh
      · rcases a with ⟨a⟩
        cases a <;> simp [binaryChannel,hp,hr] at hz
    have hs (a : RelevanceBit.{u}) :
        rowScore (binaryRewards gap) lambda (binaryChannel p r)
          (Channel.outcomeMarginal (binaryChannel p r) q) a =
        lambda*finiteKL p (Channel.outcomeMarginal (binaryChannel p r) q) := by
      rw [binaryGain_eq_KL_difference] at he
      rcases a with ⟨a⟩
      cases a <;> simp [rowScore,binaryRewards,binaryChannel] <;> nlinarith
    exact (optimal_iff_kkt (binaryRewards gap) hl (binaryChannel p r) q).mpr
      ⟨hc,_,fun a => (hs a).le,fun a _ => hs a⟩

 theorem binary_exists_unique_interior_root (p r : Dist Z) (hne : p ≠ r)
    {gap lambda : ℝ} (hg : 0 ≤ gap) (hl : 0 < lambda)
    (ht : ¬ (SupportIncluded r p ∧ lambda*finiteKL r p ≤ gap)) :
    ∃! x, x ∈ Ioo (0 : ℝ) 1 ∧ gap = lambda*binaryGain p r x := by
  obtain ⟨q,⟨hq,hx⟩,_⟩ := (binary_exists_unique_interior_iff p r hne hg hl).mpr ht
  refine ⟨q (ULift.up true),⟨hx,binary_interior_equation p r hl q hq hx⟩,?_⟩
  intro x hh
  have heq : binaryGain p r x = binaryGain p r (q (ULift.up true)) := by
    have he := binary_interior_equation p r hl q hq hx
    nlinarith [hh.2]
  exact (binaryGain_strictAnti p r hne).injOn hh.1 hx heq

 theorem binaryGain_zero (p r : Dist Z) : binaryGain p r 0 = finiteKL r p := by
  classical
  have hh := binaryGain_eq_KL_difference p r (Dist.pure (ULift.up false))
  simpa [Dist.pure_apply,outcomeMarginal_pure_action,binaryChannel,finiteKL_self] using hh

 theorem binaryGain_one (p r : Dist Z) : binaryGain p r 1 = -finiteKL p r := by
  classical
  have hh := binaryGain_eq_KL_difference p r (Dist.pure (ULift.up true))
  simpa [Dist.pure_apply,outcomeMarginal_pure_action,binaryChannel,finiteKL_self] using hh

 theorem continuousOn_binaryGain (p r : Dist Z) :
    ContinuousOn (binaryGain p r) (Ioo (0 : ℝ) 1) := by
  intro x hx
  exact (((hasDerivAt_mixEntropySlope p r x (fun z =>
    (mixMass_pos_or_both_zero p r hx z).imp (fun h => ne_of_gt h) id)).add_const
      (entropy p)).sub_const (entropy r)).continuousAt.continuousWithinAt

 theorem binaryGain_tendsto_zero_of_support (p r : Dist Z) (hc : SupportIncluded r p) :
    Tendsto (binaryGain p r) (𝓝 0) (𝓝 (finiteKL r p)) := by
  have hd := hasDerivAt_mixEntropySlope p r 0 (fun z => by
    by_cases hz : p z = 0
    · right
      refine ⟨hz,?_⟩
      by_contra hn
      have hp := hc z (lt_of_le_of_ne (r.nonneg z) (Ne.symm hn))
      linarith
    · left
      simpa [mixMass] using hz)
  have hh := ((hd.add_const (entropy p)).sub_const (entropy r)).continuousAt.tendsto
  change Tendsto (binaryGain p r) (𝓝 0) (𝓝 (binaryGain p r 0)) at hh
  simpa [binaryGain_zero] using hh

 theorem binaryGain_tendsto_one_of_support (p r : Dist Z) (hc : SupportIncluded p r) :
    Tendsto (binaryGain p r) (𝓝 1) (𝓝 (-finiteKL p r)) := by
  have hd := hasDerivAt_mixEntropySlope p r 1 (fun z => by
    by_cases hz : r z = 0
    · right
      refine ⟨?_,hz⟩
      by_contra hn
      have hr := hc z (lt_of_le_of_ne (p.nonneg z) (Ne.symm hn))
      linarith
    · left
      simpa [mixMass] using hz)
  have hh := ((hd.add_const (entropy p)).sub_const (entropy r)).continuousAt.tendsto
  change Tendsto (binaryGain p r) (𝓝 1) (𝓝 (binaryGain p r 1)) at hh
  simpa [binaryGain_one] using hh

end TraceableAgency.Section4
