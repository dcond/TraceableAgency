import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact participation compensation when a new signal changes the optimal
plan. These optimization facts apply to any continuous old value and gain. -/
namespace TraceableAgency.Section4
open Set

/-- Optimality on the feasible binary-effort interval, including feasibility. -/
def IsIntervalOptimal (f : ℝ → ℝ) (q : ℝ) : Prop :=
  q ∈ Icc (0 : ℝ) 1 ∧ ∀ x ∈ Icc (0 : ℝ) 1, f x ≤ f q

theorem exists_intervalOptimal (f : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1)) : ∃ q, IsIntervalOptimal f q := by
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn (by exact ⟨0, by simp⟩) hf
  exact ⟨q, hq, hmax⟩

noncomputable def compensation (J G : ℝ → ℝ) (oldPlan newPlan : ℝ) : ℝ :=
  J newPlan + G newPlan - J oldPlan

theorem compensation_lower_bound (J G : ℝ → ℝ) {oldPlan newPlan : ℝ}
    (hold : oldPlan ∈ Icc (0 : ℝ) 1)
    (hnew : IsIntervalOptimal (fun q => J q + G q) newPlan) :
    G oldPlan ≤ compensation J G oldPlan newPlan := by
  have hh := hnew.2 oldPlan hold
  dsimp [compensation]
  linarith

theorem compensation_upper_bound (J G : ℝ → ℝ) {oldPlan newPlan gainPlan : ℝ}
    (hold : IsIntervalOptimal J oldPlan)
    (hnew : newPlan ∈ Icc (0 : ℝ) 1)
    (hgain : IsIntervalOptimal G gainPlan) :
    compensation J G oldPlan newPlan ≤ G gainPlan := by
  have hh := hold.2 newPlan hnew
  have hg := hgain.2 newPlan hnew
  dsimp [compensation]
  linarith

theorem compensation_exact_base_adjustment (J G : ℝ → ℝ)
    (oldPlan newPlan base : ℝ) :
    (base-compensation J G oldPlan newPlan) + (J newPlan+G newPlan) =
      base+J oldPlan := by
  dsimp [compensation]
  ring

theorem intervalOptimal_add_base_iff (f : ℝ → ℝ) (base q : ℝ) :
    IsIntervalOptimal (fun x => base+f x) q ↔ IsIntervalOptimal f q := by
  simp only [IsIntervalOptimal, add_le_add_iff_left]

theorem compensation_weak_participation (J G : ℝ → ℝ) {oldPlan newPlan : ℝ}
    (hold : oldPlan ∈ Icc (0 : ℝ) 1)
    (hnew : IsIntervalOptimal (fun q => J q+G q) newPlan) (base : ℝ) :
    base+J oldPlan ≤ (base-G oldPlan)+(J newPlan+G newPlan) := by
  have hh := hnew.2 oldPlan hold
  linarith

theorem exists_compensation_bounds (J G : ℝ → ℝ)
    (hJ : ContinuousOn J (Icc (0 : ℝ) 1))
    (hG : ContinuousOn G (Icc (0 : ℝ) 1)) :
    ∃ oldPlan newPlan gainPlan,
      IsIntervalOptimal J oldPlan ∧
      IsIntervalOptimal (fun q => J q+G q) newPlan ∧
      IsIntervalOptimal G gainPlan ∧
      G oldPlan ≤ compensation J G oldPlan newPlan ∧
      compensation J G oldPlan newPlan ≤ G gainPlan := by
  obtain ⟨q0,h0⟩ := exists_intervalOptimal J hJ
  obtain ⟨q1,h1⟩ := exists_intervalOptimal (fun q => J q+G q) (hJ.add hG)
  obtain ⟨qG,hg⟩ := exists_intervalOptimal G hG
  exact ⟨q0,q1,qG,h0,h1,hg,compensation_lower_bound J G h0.1 h1,
    compensation_upper_bound J G h0 h1.1 hg⟩

theorem compensation_zero_of_zero_gain (J G : ℝ → ℝ) {oldPlan newPlan : ℝ}
    (hG : ∀ q ∈ Icc (0 : ℝ) 1, G q = 0)
    (hold : IsIntervalOptimal J oldPlan)
    (hnew : IsIntervalOptimal (fun q => J q+G q) newPlan) :
    compensation J G oldPlan newPlan = 0 := by
  have hlo := compensation_lower_bound J G hold.1 hnew
  have hhi := hold.2 newPlan hnew.1
  rw [hG oldPlan hold.1] at hlo
  dsimp [compensation] at *
  rw [hG newPlan hnew.1] at hlo ⊢
  linarith

end TraceableAgency.Section4
