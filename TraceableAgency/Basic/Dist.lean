/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.Ring.Real

/-!
# Finite Probability Distributions

Custom finite probability distribution type for the traceable agency formalization.
Avoids full MeasureTheory; uses finite vectors with sum-to-one constraint.
-/

open Filter Topology

namespace TraceableAgency

variable {A : Type*} [Fintype A]

/-- A finite probability distribution over a finite type `A`. -/
structure Dist (A : Type*) [Fintype A] where
  prob : A → ℝ
  nonneg : ∀ a, 0 ≤ prob a
  sum_eq_one : ∑ a, prob a = 1

namespace Dist

instance : CoeFun (Dist A) (fun _ => A → ℝ) where
  coe := Dist.prob

@[ext]
theorem ext {q q' : Dist A} (h : ∀ a, q a = q' a) : q = q' := by
  cases q; cases q'; congr; funext a; exact h a

theorem prob_nonneg (q : Dist A) (a : A) : 0 ≤ q a := q.nonneg a

theorem prob_le_one (q : Dist A) (a : A) : q a ≤ 1 := by
  have h := q.sum_eq_one
  have hsum : q a ≤ ∑ b, q b := Finset.single_le_sum (fun b _ => q.nonneg b) (Finset.mem_univ a)
  linarith

/-- The support of a distribution (as a set, not computable Finset). -/
def support (q : Dist A) : Set A := {a | q a > 0}

/-- A distribution has full support if every element has positive probability. -/
def FullSupport (q : Dist A) : Prop := ∀ a, q a > 0

theorem fullSupport_iff_support_eq_univ (q : Dist A) :
    q.FullSupport ↔ q.support = Set.univ := by
  simp [FullSupport, support, Set.eq_univ_iff_forall]

variable [DecidableEq A]

/-- The Dirac distribution concentrated at a single point. -/
def pure (a : A) : Dist A where
  prob := fun b => if b = a then 1 else 0
  nonneg := fun b => by split_ifs <;> linarith
  sum_eq_one := by simp [Finset.sum_ite_eq]

theorem pure_apply (a b : A) : (pure a) b = if b = a then 1 else 0 := rfl

@[simp]
theorem pure_apply_self (a : A) : (pure a) a = 1 := by
  rw [pure_apply, if_pos rfl]

@[simp]
theorem pure_apply_ne (a b : A) (h : b ≠ a) : (pure a) b = 0 := by
  rw [pure_apply, if_neg h]

theorem pure_support (a : A) : (pure a).support = {a} := by
  ext b
  simp only [support, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hpos
    by_contra hne
    rw [pure_apply, if_neg hne] at hpos
    linarith
  · intro heq
    rw [heq, pure_apply_self]
    linarith

section Mix

variable {A : Type*} [Fintype A]

/-- Convex combination of two distributions. -/
def mix (t : ℝ) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1) (q r : Dist A) : Dist A where
  prob := fun a => t * q a + (1 - t) * r a
  nonneg := fun a => by
    apply add_nonneg
    · exact mul_nonneg ht_nonneg (q.nonneg a)
    · exact mul_nonneg (by linarith) (r.nonneg a)
  sum_eq_one := by
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [q.sum_eq_one, r.sum_eq_one]
    ring

@[simp]
theorem mix_apply (t : ℝ) (ht_nonneg : 0 ≤ t) (ht_le_one : t ≤ 1)
    (q r : Dist A) (a : A) :
    (mix t ht_nonneg ht_le_one q r) a = t * q a + (1 - t) * r a := rfl

end Mix

/-!
## Uniform Distribution
-/

section Uniform

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform : Dist A where
  prob := fun _ => 1 / Fintype.card A
  nonneg := fun _ => by
    apply div_nonneg
    · linarith
    · exact Nat.cast_nonneg _
  sum_eq_one := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_one_div, div_self]
    exact Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)

@[simp]
theorem uniform_apply (a : A) : (uniform (A := A)) a = 1 / Fintype.card A := rfl

theorem uniform_fullSupport : (uniform (A := A)).FullSupport := by
  intro a
  simp only [uniform_apply]
  apply div_pos
  · linarith
  · exact Nat.cast_pos.mpr Fintype.card_pos

end Uniform

/-!
## Full-Support Smoothing

For boundary extension, we can mix any distribution with a full-support distribution
to get a full-support approximation.
-/

section Smoothing

variable {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Smooth a distribution by mixing with uniform: (1-ε)q + ε·uniform. -/
noncomputable def smooth (q : Dist A) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) : Dist A :=
  Dist.mix (1 - ε) (by linarith) (by linarith) q uniform

theorem smooth_apply (q : Dist A) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (a : A) :
    (smooth q ε hε0 hε1) a = (1 - ε) * q a + ε / Fintype.card A := by
  simp only [smooth, mix_apply, uniform_apply]
  ring

theorem smooth_fullSupport (q : Dist A) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    (smooth q ε hε0 hε1).FullSupport := by
  intro a
  rw [smooth_apply]
  apply add_pos_of_nonneg_of_pos
  · apply mul_nonneg
    · linarith
    · exact q.nonneg a
  · apply div_pos hε0
    exact Nat.cast_pos.mpr Fintype.card_pos

/-- The smoothing sequence: qₙ = (1 - 1/(n+2)) q + (1/(n+2)) uniform. -/
noncomputable def smoothSeq (q : Dist A) (n : ℕ) : Dist A :=
  smooth q (1 / (n + 2 : ℝ))
    (by positivity)
    (by have h : (1 : ℝ) ≤ n + 2 := by
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        have hpos : (0 : ℝ) < n + 2 := by linarith
        rw [div_le_one hpos]
        exact h)

theorem smoothSeq_fullSupport (q : Dist A) (n : ℕ) :
    (smoothSeq q n).FullSupport :=
  smooth_fullSupport q _ (by positivity) _

/-- The smoothing sequence converges pointwise to the original distribution. -/
theorem smoothSeq_tendsto (q : Dist A) (a : A) :
    Tendsto (fun n => (smoothSeq q n) a) atTop (𝓝 (q a)) := by
  simp only [smoothSeq, smooth_apply]
  have h1 : ∀ n : ℕ, (1 - 1 / (n + 2 : ℝ)) * q a + 1 / (n + 2 : ℝ) / Fintype.card A =
      q a + (1 / (n + 2 : ℝ)) * (1 / Fintype.card A - q a) := by
    intro n; ring
  simp_rw [h1]
  have h2 : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2)) atTop (𝓝 0) := by
    have h2a : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h2b : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have h2c : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) := h2b.comp h2a
    convert h2c using 1
    ext n
    simp only [one_div]
  have h3 : Tendsto (fun n : ℕ => q a + (1 / (n + 2 : ℝ)) * (1 / Fintype.card A - q a))
      atTop (𝓝 (q a + 0 * (1 / Fintype.card A - q a))) := by
    apply Tendsto.add tendsto_const_nhds
    apply Tendsto.mul h2 tendsto_const_nhds
  simp only [zero_mul, add_zero] at h3
  exact h3

end Smoothing

/-!
## Topology on Dist A

The finite-dimensional topology on Dist A, induced by the coordinate map to A → ℝ.
This makes Dist A a compact metrizable space (subset of the simplex in ℝ^|A|).
-/

/-- The topology on Dist A induced by the coordinate embedding into A → ℝ.
    A sequence qₙ → q iff qₙ(a) → q(a) for all a ∈ A. -/
instance instTopologicalSpaceDist : TopologicalSpace (Dist A) :=
  TopologicalSpace.induced Dist.prob inferInstance

/-- The coordinate embedding is continuous (trivially, by definition of induced topology). -/
theorem continuous_prob : Continuous (Dist.prob : Dist A → (A → ℝ)) :=
  continuous_induced_dom

/-- The coordinate projection q ↦ q(a) is continuous. -/
theorem continuous_prob_apply (a : A) : Continuous (fun q : Dist A => q a) :=
  (continuous_apply a).comp continuous_prob

end Dist

end TraceableAgency
