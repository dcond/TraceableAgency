import TraceableAgency.Section3.Range

/-! # Ordinal uniqueness on the exact attainable half-line -/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1

universe u

variable {O : Type u} [Fintype O] [DecidableEq O] [Nonempty O]
variable {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}

/-- Every common-scale real index is exactly a strictly increasing transform
of the trace-tempered value on its entire attainable domain. -/
theorem commonScale_iff_strictMono_transform
    (hlambda : 0 < lambda) (hrep : WithinChannelRepresentation F u lambda)
    (W : CommonIndex O) :
    CommonScaleRepresentation F W ↔
      ∃ phi : Set.Ici (minPayoff u) → ℝ, StrictMono phi ∧
        ∀ E, W E = phi ⟨valueIndex u lambda E,
          minPayoff_le_valueIndex u hlambda.le E⟩ := by
  have hsurj (x : Set.Ici (minPayoff u)) :
      ∃ E, valueIndex u lambda E = x.1 := by
    have hx : x.1 ∈ Set.range (valueIndex u lambda) := by
      rw [valueIndex_range u hlambda]
      exact x.2
    exact hx
  let witness : Set.Ici (minPayoff u) → FiniteExperiment O :=
    fun x => Classical.choose (hsurj x)
  have hvalue (x : Set.Ici (minPayoff u)) :
      valueIndex u lambda (witness x) = x.1 := Classical.choose_spec (hsurj x)
  rw [commonScale_iff_order hrep]
  constructor
  · intro horder
    refine ⟨fun x => W (witness x), ?_, ?_⟩
    · intro x y hxy
      change x.1 < y.1 at hxy
      apply lt_of_le_of_ne
      · exact (horder _ _).mpr (by simpa only [hvalue] using hxy.le)
      · intro heq
        have hh := (horder (witness y) (witness x)).mp heq.ge
        rw [hvalue, hvalue] at hh
        exact (not_le.mpr hxy) hh
    · intro E
      apply le_antisymm
      · apply (horder _ _).mpr
        rw [hvalue]
      · apply (horder _ _).mpr
        rw [hvalue]
  · rintro ⟨phi, hphi, hW⟩ E D
    rw [hW, hW]
    exact hphi.le_iff_le

theorem commonScale_eq_of_value_eq
    (hrep : WithinChannelRepresentation F u lambda)
    {W : CommonIndex O} (hW : CommonScaleRepresentation F W)
    {E D : FiniteExperiment O}
    (heq : valueIndex u lambda E = valueIndex u lambda D) : W E = W D := by
  apply le_antisymm
  · exact (commonScale_order_iff hrep hW E D).mpr heq.le
  · exact (commonScale_order_iff hrep hW D E).mpr heq.ge

end TraceableAgency.Section3
