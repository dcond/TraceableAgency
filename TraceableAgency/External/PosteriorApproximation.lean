/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.Blackwell
import TraceableAgency.Info.Identities

/-!
# Finite posterior-law approximation by explicit vertex insertion

This file derives the preference-free posterior-law sandwich used by the
ordinal continuity proof. Continuous barycentric coordinates adapted to any
prescribed finite set are constructed explicitly by recursively inserting
vertices into the ordinary probability simplex.

The construction of those coordinates, their conversion to channels,
Blackwell spreads/merges, and fixed-alphabet convergence are all carried out
in Lean.
-/

set_option linter.style.header false

namespace TraceableAgency

open Filter Topology

universe u

/-- Finite barycentric-coordinate data adapted to a prescribed finite family
of points. -/
structure FiniteAdaptedSimplexBarycentricGrid
    {A I : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype I]
    (target : I → Dist A) where
  Vertex : Type u
  vertexFintype : Fintype Vertex
  vertexDecidableEq : DecidableEq Vertex
  vertexNonempty : Nonempty Vertex
  point : Vertex → Dist A
  weights : Dist A → @Dist Vertex vertexFintype
  continuous_weight :
    ∀ v : Vertex, Continuous (fun r : Dist A => weights r v)
  barycenter :
    ∀ (r : Dist A) (a : A),
      @Finset.sum Vertex ℝ _ (@Finset.univ Vertex vertexFintype)
        (fun v => weights r v * point v a) = r a
  targetVertex : I → Vertex
  weights_target :
    ∀ i : I,
      weights (target i) =
        @Dist.pure Vertex vertexFintype vertexDecidableEq (targetVertex i)
  point_target :
    ∀ i : I, point (targetVertex i) = target i

namespace FiniteAdaptedSimplexBarycentricGrid

variable {A I : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype I]
  {target : I → Dist A}

/-!
## Explicit insertion of prescribed vertices

No triangulation theorem is needed.  Starting from the usual coordinates of
the probability simplex, insert a point `t` into any finite barycentric grid
as follows.  If `c_v` are the grid coordinates of `t`, put

`μ(r) = min { w_v(r) / c_v | c_v > 0 }`.

The new coordinate at `t` is `μ(r)` and the old coordinate at `v` is
`w_v(r) - μ(r)c_v`.  These coordinates are nonnegative, continuous, sum to
one, and have the same barycenter.  At `t` the new coordinate is one.  At an
old prescribed point distinct from `t`, one coordinate in the support of
`c` vanishes, so `μ` is zero and the old pure coordinates are preserved.
-/

/-- Vertices carrying positive weight in the representation of `t`. -/
noncomputable def positiveVertices
    (g : FiniteAdaptedSimplexBarycentricGrid target) (t : Dist A) :
    Finset g.Vertex := by
  letI : Fintype g.Vertex := g.vertexFintype
  exact Finset.univ.filter (fun v => 0 < g.weights t v)

theorem positiveVertices_nonempty
    (g : FiniteAdaptedSimplexBarycentricGrid target) (t : Dist A) :
    (g.positiveVertices t).Nonempty := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  by_contra h
  have hzero : ∀ v : g.Vertex, g.weights t v = 0 := by
    intro v
    have hnot : ¬ 0 < g.weights t v := by
      intro hpos
      exact h ⟨v, by simp [positiveVertices, hpos]⟩
    exact le_antisymm (le_of_not_gt hnot) ((g.weights t).nonneg v)
  have hone := (g.weights t).sum_eq_one
  simp_rw [hzero] at hone
  simp at hone

/-- Amount of the representation of `t` that can be subtracted from the
representation of `r` while retaining nonnegative coordinates. -/
noncomputable def insertionCoeff
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (t r : Dist A) : ℝ := by
  letI : Fintype g.Vertex := g.vertexFintype
  exact
    (g.positiveVertices t).inf' (g.positiveVertices_nonempty t)
      (fun v => g.weights r v / g.weights t v)

theorem insertionCoeff_nonneg
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (t r : Dist A) :
    0 ≤ g.insertionCoeff t r := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  unfold insertionCoeff
  apply Finset.le_inf'
  intro v hv
  have hpos : 0 < g.weights t v := by
    simpa [positiveVertices] using hv
  exact div_nonneg ((g.weights r).nonneg v) hpos.le

theorem insertionCoeff_le_ratio
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (t r : Dist A) (v : g.Vertex)
    (hv : 0 < g.weights t v) :
    g.insertionCoeff t r ≤ g.weights r v / g.weights t v := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  unfold insertionCoeff
  apply Finset.inf'_le
  simp [positiveVertices, hv]

theorem continuous_insertionCoeff
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (t : Dist A) :
    Continuous (g.insertionCoeff t) := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  unfold insertionCoeff
  apply Continuous.finset_inf'_apply
  intro v hv
  exact (g.continuous_weight v).div_const (g.weights t v)

theorem insertionCoeff_self
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (t : Dist A) :
    g.insertionCoeff t t = 1 := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  unfold insertionCoeff
  apply Finset.inf'_eq_of_forall
  intro v hv
  have hpos : 0 < g.weights t v := by
    simpa [positiveVertices] using hv
  exact div_self (ne_of_gt hpos)

theorem point_eq_of_weights_eq_pure
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (r : Dist A) (v : g.Vertex)
    (hweights : g.weights r = @Dist.pure g.Vertex g.vertexFintype
      g.vertexDecidableEq v) :
    g.point v = r := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  ext a
  have hbar := g.barycenter r a
  rw [hweights] at hbar
  simpa [Dist.pure_apply] using hbar

theorem insertionCoeff_eq_zero_of_pure_of_ne
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (t r : Dist A) (v₀ : g.Vertex)
    (hweights : g.weights r = @Dist.pure g.Vertex g.vertexFintype
      g.vertexDecidableEq v₀)
    (hne : r ≠ t) :
    g.insertionCoeff t r = 0 := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  have hexists :
      ∃ v : g.Vertex, 0 < g.weights t v ∧ v ≠ v₀ := by
    by_contra h
    have hpos_only : ∀ v : g.Vertex, 0 < g.weights t v → v = v₀ := by
      intro v hv
      by_contra hvne
      exact h ⟨v, hv, hvne⟩
    have hzero : ∀ v : g.Vertex, v ≠ v₀ → g.weights t v = 0 := by
      intro v hvne
      have hnot : ¬ 0 < g.weights t v := fun hv => hvne (hpos_only v hv)
      exact le_antisymm (le_of_not_gt hnot) ((g.weights t).nonneg v)
    have hsum_single :
        (∑ v : g.Vertex, g.weights t v) = g.weights t v₀ := by
      apply Finset.sum_eq_single v₀
      · intro v _hv hvne
        exact hzero v hvne
      · intro hv
        exact (hv (Finset.mem_univ v₀)).elim
    have hv₀ : g.weights t v₀ = 1 := by
      rw [← hsum_single]
      exact (g.weights t).sum_eq_one
    have hpure :
        g.weights t =
          @Dist.pure g.Vertex g.vertexFintype g.vertexDecidableEq v₀ := by
      ext v
      by_cases hv : v = v₀
      · subst v
        simp [hv₀]
      · simp [hv, hzero v hv]
    have ht := g.point_eq_of_weights_eq_pure t v₀ hpure
    have hr := g.point_eq_of_weights_eq_pure r v₀ hweights
    exact hne (hr.symm.trans ht)
  obtain ⟨v, htv, hvne⟩ := hexists
  have hrv : g.weights r v = 0 := by
    rw [hweights]
    simp [hvne]
  have hle := g.insertionCoeff_le_ratio t r v htv
  rw [hrv, zero_div] at hle
  exact le_antisymm hle (g.insertionCoeff_nonneg t r)

/-- Insert one prescribed point as a new barycentric vertex. -/
noncomputable def insertTarget
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (t : Dist A) :
    FiniteAdaptedSimplexBarycentricGrid
      (fun x : Option I => x.elim t target) := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  let μ := g.insertionCoeff t
  let c := g.weights t
  let newWeights : Dist A → Dist (Option g.Vertex) := fun r =>
    { prob := fun
        | none => μ r
        | some v => g.weights r v - μ r * c v
      nonneg := by
        intro x
        cases x with
        | none => exact g.insertionCoeff_nonneg t r
        | some v =>
            by_cases hcv : 0 < c v
            · have hle := g.insertionCoeff_le_ratio t r v hcv
              exact sub_nonneg.mpr ((le_div_iff₀ hcv).mp hle)
            · have hczero : c v = 0 :=
                le_antisymm (le_of_not_gt hcv) (c.nonneg v)
              simp [hczero, (g.weights r).nonneg v]
      sum_eq_one := by
        simp only [Fintype.sum_option]
        change μ r + ∑ v : g.Vertex, (g.weights r v - μ r * c v) = 1
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        rw [(g.weights r).sum_eq_one, c.sum_eq_one]
        ring }
  exact
    { Vertex := Option g.Vertex
      vertexFintype := inferInstance
      vertexDecidableEq := inferInstance
      vertexNonempty := ⟨none⟩
      point := fun
        | none => t
        | some v => g.point v
      weights := newWeights
      continuous_weight := by
        intro x
        cases x with
        | none => exact g.continuous_insertionCoeff t
        | some v =>
            exact (g.continuous_weight v).sub
              ((g.continuous_insertionCoeff t).mul_const (c v))
      barycenter := by
        intro r a
        simp only [Fintype.sum_option]
        change
          μ r * t a +
              ∑ v : g.Vertex,
                (g.weights r v - μ r * c v) * g.point v a =
            r a
        calc
          μ r * t a +
                ∑ v : g.Vertex,
                  (g.weights r v - μ r * c v) * g.point v a =
              (∑ v : g.Vertex, g.weights r v * g.point v a) +
                μ r *
                  (t a - ∑ v : g.Vertex, c v * g.point v a) := by
                    simp_rw [sub_mul]
                    rw [Finset.sum_sub_distrib]
                    simp_rw [mul_assoc]
                    rw [← Finset.mul_sum]
                    ring
          _ = r a := by
            rw [g.barycenter r a, g.barycenter t a]
            ring
      targetVertex := fun
        | none => none
        | some i => if target i = t then none else some (g.targetVertex i)
      weights_target := by
        intro x
        cases x with
        | none =>
            ext y
            cases y with
            | none =>
                simp [newWeights, μ, g.insertionCoeff_self t]
            | some v =>
                simp [newWeights, μ, c, g.insertionCoeff_self t]
        | some i =>
            by_cases hit : target i = t
            · simp only [Option.elim_some]
              rw [hit]
              ext y
              cases y with
              | none =>
                  simp [newWeights, μ, g.insertionCoeff_self t]
              | some v =>
                  simp [newWeights, μ, c,
                    g.insertionCoeff_self t]
            · have hμ :
                  g.insertionCoeff t (target i) = 0 :=
                g.insertionCoeff_eq_zero_of_pure_of_ne
                  t (target i) (g.targetVertex i)
                  (g.weights_target i) hit
              ext y
              cases y with
              | none =>
                  simp [newWeights, μ, hμ, hit]
              | some v =>
                  simp [newWeights, μ, hμ, g.weights_target i,
                    Dist.pure_apply, hit]
      point_target := by
        intro x
        cases x with
        | none => rfl
        | some i =>
            by_cases hit : target i = t
            · simp [hit]
            · simp [hit, g.point_target i] }

/-- Transport an adapted grid along an equivalence of target indices. -/
noncomputable def reindex
    {J : Type u} [Fintype J]
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (e : I ≃ J) :
    FiniteAdaptedSimplexBarycentricGrid
      (fun j => target (e.symm j)) where
  Vertex := g.Vertex
  vertexFintype := g.vertexFintype
  vertexDecidableEq := g.vertexDecidableEq
  vertexNonempty := g.vertexNonempty
  point := g.point
  weights := g.weights
  continuous_weight := g.continuous_weight
  barycenter := g.barycenter
  targetVertex := fun j => g.targetVertex (e.symm j)
  weights_target := fun j => g.weights_target (e.symm j)
  point_target := fun j => g.point_target (e.symm j)

/-- Base barycentric grid: the ordinary coordinates of the probability
simplex. -/
noncomputable def emptyTargetGrid :
    FiniteAdaptedSimplexBarycentricGrid
      (fun i : PEmpty => (i.elim : Dist A)) where
  Vertex := A
  vertexFintype := inferInstance
  vertexDecidableEq := inferInstance
  vertexNonempty := inferInstance
  point := Dist.pure
  weights := id
  continuous_weight := fun a => Dist.continuous_prob_apply a
  barycenter := by
    intro r a
    simp [Dist.pure_apply]
  targetVertex := PEmpty.elim
  weights_target := fun i => i.elim
  point_target := fun i => i.elim

/-- Every finite family of points of a finite probability simplex admits the
required continuous barycentric grid.  This is proved by explicit recursive
vertex insertion, not assumed from a triangulation theorem. -/
theorem exists_adaptedGrid
    (target : I → Dist A) :
    Nonempty (FiniteAdaptedSimplexBarycentricGrid target) := by
  classical
  let P : ∀ (J : Type u) [Fintype J], Prop :=
    fun J _ => ∀ targetJ : J → Dist A,
      Nonempty (FiniteAdaptedSimplexBarycentricGrid targetJ)
  apply
    Fintype.induction_empty_option
      (P := P)
      (fun J K _ e hJ targetK => by
        letI : Fintype J := Fintype.ofEquiv K e.symm
        let gJ := Classical.choice (hJ (fun j => targetK (e j)))
        let gK := gJ.reindex e
        exact ⟨by simpa using gK⟩)
      (by
        intro target0
        exact ⟨by
          convert (emptyTargetGrid (A := A)) using 1
          funext i
          exact i.elim⟩)
      (fun J _ hJ targetOption => by
        let gJ := Classical.choice (hJ (fun j => targetOption (some j)))
        let gOption := gJ.insertTarget (targetOption none)
        exact ⟨by
          convert gOption using 1
          funext x
          cases x <;> rfl⟩)
      I target

/-- The mass placed at a grid vertex after spreading every posterior according
to its barycentric coordinates. -/
noncomputable def spreadMass
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) (v : g.Vertex) : ℝ :=
  posteriorLawIntegralExp q E (fun r => g.weights r v)

theorem spreadMass_nonneg
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) (v : g.Vertex) :
    0 ≤ g.spreadMass q E v := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : Fintype E.OutcomeType := E.outFintype
  unfold spreadMass posteriorLawIntegralExp
  exact Finset.sum_nonneg fun o _ =>
    mul_nonneg ((E.outcomeMarginal q).nonneg o)
      ((g.weights (E.posterior q o)).nonneg v)

theorem spreadMass_sum
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) :
    letI : Fintype g.Vertex := g.vertexFintype
    ∑ v : g.Vertex, g.spreadMass q E v = 1 := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : Fintype E.OutcomeType := E.outFintype
  unfold spreadMass posteriorLawIntegralExp
  rw [Finset.sum_comm]
  calc
    (∑ o : E.OutcomeType,
        ∑ v : g.Vertex,
          E.outcomeMarginal q o * g.weights (E.posterior q o) v) =
        ∑ o : E.OutcomeType,
          E.outcomeMarginal q o *
            ∑ v : g.Vertex, g.weights (E.posterior q o) v := by
              apply Finset.sum_congr rfl
              intro o _ho
              rw [Finset.mul_sum]
    _ = ∑ o : E.OutcomeType, E.outcomeMarginal q o := by
      simp only [(g.weights _).sum_eq_one, mul_one]
    _ = 1 := (E.outcomeMarginal q).sum_eq_one

/-- The grid-spread posterior mass as a finite distribution. -/
noncomputable def spreadDist
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) :
    @Dist g.Vertex g.vertexFintype := by
  letI : Fintype g.Vertex := g.vertexFintype
  exact
    { prob := g.spreadMass q E
      nonneg := g.spreadMass_nonneg q E
      sum_eq_one := g.spreadMass_sum q E }

theorem spread_barycenter
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) (a : A) :
    letI : Fintype g.Vertex := g.vertexFintype
    ∑ v : g.Vertex, g.spreadDist q E v * g.point v a = q a := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : Fintype E.OutcomeType := E.outFintype
  change
    (∑ v : g.Vertex,
      g.spreadMass q E v * g.point v a) = q a
  unfold spreadMass posteriorLawIntegralExp
  calc
    (∑ v : g.Vertex,
        (∑ o : E.OutcomeType,
          E.outcomeMarginal q o * g.weights (E.posterior q o) v) *
            g.point v a) =
        ∑ v : g.Vertex,
          ∑ o : E.OutcomeType,
            (E.outcomeMarginal q o * g.weights (E.posterior q o) v) *
              g.point v a := by
                apply Finset.sum_congr rfl
                intro v _hv
                rw [Finset.sum_mul]
    _ = ∑ o : E.OutcomeType,
          ∑ v : g.Vertex,
            (E.outcomeMarginal q o * g.weights (E.posterior q o) v) *
              g.point v a := Finset.sum_comm
    _ = ∑ o : E.OutcomeType,
          E.outcomeMarginal q o *
            ∑ v : g.Vertex,
              g.weights (E.posterior q o) v * g.point v a := by
                apply Finset.sum_congr rfl
                intro o _ho
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro v _hv
                ring
    _ = ∑ o : E.OutcomeType,
          E.outcomeMarginal q o * E.posterior q o a := by
      apply Finset.sum_congr rfl
      intro o _ho
      rw [g.barycenter]
    _ = ∑ o : E.OutcomeType, q a * E.P a o := by
      apply Finset.sum_congr rfl
      intro o _ho
      exact posterior_mul_marginal q E.P o a
    _ = q a := by
      rw [← Finset.mul_sum, (E.P a).sum_eq_one, mul_one]

/-- Canonical channel implementing the grid-spread posterior law at a
full-support prior. -/
noncomputable def spreadChannel
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A) :
    @Channel A g.Vertex g.vertexFintype := by
  letI : Fintype g.Vertex := g.vertexFintype
  exact fun a =>
    { prob := fun v => g.spreadDist q E v * g.point v a / q a
      nonneg := fun v =>
        div_nonneg
          (mul_nonneg ((g.spreadDist q E).nonneg v) ((g.point v).nonneg a))
          (le_of_lt (hq a))
      sum_eq_one := by
        rw [← Finset.sum_div, g.spread_barycenter q E a]
        exact div_self (ne_of_gt (hq a)) }

theorem outcomeMarginal_spreadChannel
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (v : g.Vertex) :
    letI : Fintype g.Vertex := g.vertexFintype
    (Channel.outcomeMarginal (g.spreadChannel q hq E) q) v =
      g.spreadDist q E v := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  unfold Channel.outcomeMarginal spreadChannel
  change (∑ a : A,
      q a * (g.spreadDist q E v * g.point v a / q a)) =
    g.spreadDist q E v
  calc
    (∑ a : A,
        q a * (g.spreadDist q E v * g.point v a / q a)) =
        ∑ a : A, g.spreadDist q E v * g.point v a := by
          apply Finset.sum_congr rfl
          intro a _ha
          field_simp [ne_of_gt (hq a)]
    _ = g.spreadDist q E v * ∑ a : A, g.point v a := by
      rw [Finset.mul_sum]
    _ = g.spreadDist q E v := by
      rw [(g.point v).sum_eq_one, mul_one]

theorem posterior_spreadChannel_of_pos
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (v : g.Vertex) (hv : 0 < g.spreadMass q E v) :
    letI : Fintype g.Vertex := g.vertexFintype
    Channel.posterior (g.spreadChannel q hq E) q v = g.point v := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  have hv' : 0 < g.spreadDist q E v := by
    exact hv
  have hmarg :
      (Channel.outcomeMarginal (g.spreadChannel q hq E) q) v =
        g.spreadDist q E v :=
    g.outcomeMarginal_spreadChannel q hq E v
  ext a
  unfold Channel.posterior
  rw [dif_pos (hmarg.symm ▸ hv')]
  simp only [spreadChannel]
  rw [hmarg]
  field_simp [ne_of_gt hv', ne_of_gt (hq a)]

theorem posteriorLawIntegral_spreadChannel
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (φ : Dist A → ℝ) :
    letI : Fintype g.Vertex := g.vertexFintype
    posteriorLawIntegral q (g.spreadChannel q hq E) φ =
      ∑ v : g.Vertex, g.spreadDist q E v * φ (g.point v) := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  unfold posteriorLawIntegral
  apply Finset.sum_congr rfl
  intro v _hv
  rw [g.outcomeMarginal_spreadChannel q hq E v]
  by_cases hpos : 0 < g.spreadDist q E v
  · rw [g.posterior_spreadChannel_of_pos q hq E v hpos]
  · have hzero : g.spreadDist q E v = 0 :=
      le_antisymm (le_of_not_gt hpos) ((g.spreadDist q E).nonneg v)
    rw [hzero, zero_mul, zero_mul]

theorem posteriorLawIntegral_spreadChannel_eq_exp
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (φ : Dist A → ℝ) :
    letI : Fintype g.Vertex := g.vertexFintype
    posteriorLawIntegral q (g.spreadChannel q hq E) φ =
      posteriorLawIntegralExp q E
        (fun r => ∑ v : g.Vertex, g.weights r v * φ (g.point v)) := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : Fintype E.OutcomeType := E.outFintype
  rw [g.posteriorLawIntegral_spreadChannel q hq E φ]
  change
    (∑ v : g.Vertex,
      g.spreadMass q E v * φ (g.point v)) =
    posteriorLawIntegralExp q E
      (fun r => ∑ v : g.Vertex, g.weights r v * φ (g.point v))
  unfold spreadMass posteriorLawIntegralExp
  calc
    (∑ v : g.Vertex,
        (∑ o : E.OutcomeType,
          E.outcomeMarginal q o * g.weights (E.posterior q o) v) *
            φ (g.point v)) =
        ∑ v : g.Vertex,
          ∑ o : E.OutcomeType,
            (E.outcomeMarginal q o * g.weights (E.posterior q o) v) *
              φ (g.point v) := by
                apply Finset.sum_congr rfl
                intro v _hv
                rw [Finset.sum_mul]
    _ = ∑ o : E.OutcomeType,
          ∑ v : g.Vertex,
            (E.outcomeMarginal q o * g.weights (E.posterior q o) v) *
              φ (g.point v) := Finset.sum_comm
    _ = ∑ o : E.OutcomeType,
          E.outcomeMarginal q o *
            ∑ v : g.Vertex,
              g.weights (E.posterior q o) v * φ (g.point v) := by
                apply Finset.sum_congr rfl
                intro o _ho
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro v _hv
                ring

/-- A grid adapted to every posterior of `E` represents the posterior law of
`E` exactly; no limiting mesh argument is needed. -/
theorem samePosteriorLawExp_spreadChannel_of_adapted
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (g : @FiniteAdaptedSimplexBarycentricGrid
      A E.OutcomeType inferInstance inferInstance inferInstance
      E.outFintype
      (fun o : E.OutcomeType => E.posterior q o)) :
    letI : Fintype E.OutcomeType := E.outFintype
    letI : DecidableEq E.OutcomeType := E.outDecEq
    letI : Fintype g.Vertex := g.vertexFintype
    letI : DecidableEq g.Vertex := g.vertexDecidableEq
    SamePosteriorLawExp q
      (FiniteExperimentOn.ofChannel (g.spreadChannel q hq E)) E := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  classical
  intro φ _hφ
  change
    posteriorLawIntegral q (g.spreadChannel q hq E) φ =
      posteriorLawIntegralExp q E φ
  rw [g.posteriorLawIntegral_spreadChannel_eq_exp q hq E φ]
  unfold posteriorLawIntegralExp
  apply Finset.sum_congr rfl
  intro o _ho
  congr 1
  dsimp
  rw [g.weights_target o]
  simp [Dist.pure_apply, g.point_target o]

theorem spreadChannel_converges
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport)
    (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A)
    (hE : PosteriorLawConvergesAtExp q Eₙ E) :
    letI : Fintype g.Vertex := g.vertexFintype
    letI : DecidableEq g.Vertex := g.vertexDecidableEq
    ChannelConverges
      (fun n => g.spreadChannel q hq (Eₙ n))
      (g.spreadChannel q hq E) := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  intro a v
  change Tendsto
    (fun n => g.spreadMass q (Eₙ n) v * g.point v a / q a)
    atTop
    (𝓝 (g.spreadMass q E v * g.point v a / q a))
  exact
    (((hE (fun r => g.weights r v) (g.continuous_weight v)).mul_const
      (g.point v a)).div_const (q a))

/-- Garbling from the grid-spread experiment back to the original
experiment. At a positive grid mass it is Bayes' reverse kernel; a zero-mass
row is immaterial and is completed by any row of the original channel. -/
noncomputable def spreadGarblingKernel
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) :
    @Channel g.Vertex E.OutcomeType E.outFintype := by
  letI : Fintype g.Vertex := g.vertexFintype
  letI : Fintype E.OutcomeType := E.outFintype
  intro v
  by_cases hv : 0 < g.spreadMass q E v
  · exact
      { prob := fun o =>
          E.outcomeMarginal q o * g.weights (E.posterior q o) v /
            g.spreadMass q E v
        nonneg := fun o =>
          div_nonneg
            (mul_nonneg ((E.outcomeMarginal q).nonneg o)
              ((g.weights (E.posterior q o)).nonneg v))
            (le_of_lt hv)
        sum_eq_one := by
          rw [← Finset.sum_div]
          change g.spreadMass q E v / g.spreadMass q E v = 1
          exact div_self (ne_of_gt hv) }
  · exact E.P (Classical.arbitrary A)

theorem spreadMass_eq_zero_summand
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A)
    (v : g.Vertex) (hv : g.spreadMass q E v = 0)
    (o : E.OutcomeType) :
    E.outcomeMarginal q o * g.weights (E.posterior q o) v = 0 := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : Fintype E.OutcomeType := E.outFintype
  have hsum :
      (∑ o' : E.OutcomeType,
        E.outcomeMarginal q o' * g.weights (E.posterior q o') v) = 0 := by
    exact hv
  exact
    summand_eq_zero_of_sum_eq_zero_of_nonneg'
      (fun o' : E.OutcomeType =>
        E.outcomeMarginal q o' * g.weights (E.posterior q o') v)
      (fun o' =>
        mul_nonneg ((E.outcomeMarginal q).nonneg o')
          ((g.weights (E.posterior q o')).nonneg v))
      hsum o

/-- The canonical grid spread Blackwell-dominates the original experiment.
This is proved by the explicit reverse Bayesian kernel above. -/
theorem experimentPostprocesses_of_spreadChannel
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A) :
    letI : Fintype g.Vertex := g.vertexFintype
    letI : DecidableEq g.Vertex := g.vertexDecidableEq
    ExperimentPostprocesses
      (FiniteExperimentOn.ofChannel (g.spreadChannel q hq E)) E := by
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  classical
  refine ⟨g.spreadGarblingKernel q E, ?_⟩
  symm
  funext a
  ext o
  unfold Channel.postprocess
  change
    (∑ v : g.Vertex,
      (g.spreadMass q E v * g.point v a / q a) *
        g.spreadGarblingKernel q E v o) = E.P a o
  calc
    (∑ v : g.Vertex,
        (g.spreadMass q E v * g.point v a / q a) *
          g.spreadGarblingKernel q E v o) =
        ∑ v : g.Vertex,
          E.outcomeMarginal q o *
            g.weights (E.posterior q o) v * g.point v a / q a := by
              apply Finset.sum_congr rfl
              intro v _hv
              by_cases hpos : 0 < g.spreadMass q E v
              · rw [spreadGarblingKernel]
                simp only [dif_pos hpos]
                field_simp [ne_of_gt hpos, ne_of_gt (hq a)]
              · have hzero : g.spreadMass q E v = 0 :=
                  le_antisymm (le_of_not_gt hpos)
                    (g.spreadMass_nonneg q E v)
                have hsummand :=
                  g.spreadMass_eq_zero_summand q E v hzero o
                rw [hzero, zero_mul, zero_div, zero_mul]
                rw [hsummand, zero_mul, zero_div]
    _ = E.outcomeMarginal q o *
          (∑ v : g.Vertex,
            g.weights (E.posterior q o) v * g.point v a) / q a := by
            rw [Finset.mul_sum, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro v _hv
            ring
    _ = E.outcomeMarginal q o * E.posterior q o a / q a := by
      rw [g.barycenter]
    _ = E.P a o := by
      apply (div_eq_iff (ne_of_gt (hq a))).2
      have hbayes :
          E.outcomeMarginal q o * E.posterior q o a =
            q a * E.P a o := by
        exact posterior_mul_marginal q E.P o a
      rw [hbayes]
      ring

/-- Merge an experiment by applying the grid's continuous barycentric weights
to each posterior. -/
noncomputable def mergeChannel
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) :
    @Channel A g.Vertex g.vertexFintype := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype g.Vertex := g.vertexFintype
  exact Channel.postprocess E.P (fun o => g.weights (E.posterior q o))

theorem experimentPostprocesses_mergeChannel
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (E : FiniteExperimentOn A) :
    letI : Fintype g.Vertex := g.vertexFintype
    letI : DecidableEq g.Vertex := g.vertexDecidableEq
    ExperimentPostprocesses E
      (FiniteExperimentOn.ofChannel (g.mergeChannel q E)) := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  refine ⟨fun o => g.weights (E.posterior q o), ?_⟩
  rfl

theorem mergeChannel_apply_eq_integral
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (a : A) (v : g.Vertex) :
    letI : Fintype g.Vertex := g.vertexFintype
    g.mergeChannel q E a v =
      posteriorLawIntegralExp q E
        (fun r => r a * g.weights r v) / q a := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : Fintype g.Vertex := g.vertexFintype
  unfold mergeChannel Channel.postprocess posteriorLawIntegralExp
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro o _ho
  have hbayes :
      E.outcomeMarginal q o * E.posterior q o a = q a * E.P a o := by
    exact posterior_mul_marginal q E.P o a
  apply (eq_div_iff (ne_of_gt (hq a))).2
  calc
    E.P a o * g.weights (E.posterior q o) v * q a =
        (q a * E.P a o) * g.weights (E.posterior q o) v := by ring
    _ = (E.outcomeMarginal q o * E.posterior q o a) *
        g.weights (E.posterior q o) v := by rw [← hbayes]
    _ = (E.outcomeMarginal q o *
        (E.posterior q o a * g.weights (E.posterior q o) v)) := by ring

theorem mergeChannel_converges
    (g : FiniteAdaptedSimplexBarycentricGrid target)
    (q : Dist A) (hq : q.FullSupport)
    (Eₙ : ℕ → FiniteExperimentOn A) (E : FiniteExperimentOn A)
    (hE : PosteriorLawConvergesAtExp q Eₙ E) :
    letI : Fintype g.Vertex := g.vertexFintype
    letI : DecidableEq g.Vertex := g.vertexDecidableEq
    ChannelConverges
      (fun n => g.mergeChannel q (Eₙ n))
      (g.mergeChannel q E) := by
  classical
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  intro a v
  simp_rw [g.mergeChannel_apply_eq_integral q hq]
  exact
    (hE (fun r => r a * g.weights r v)
      ((Dist.continuous_prob_apply a).mul (g.continuous_weight v))).div_const
        (q a)

theorem mergeChannel_eq_spreadChannel_of_adapted
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (g : @FiniteAdaptedSimplexBarycentricGrid
      A E.OutcomeType inferInstance inferInstance inferInstance
      E.outFintype
      (fun o : E.OutcomeType => E.posterior q o)) :
    letI : Fintype E.OutcomeType := E.outFintype
    letI : DecidableEq E.OutcomeType := E.outDecEq
    letI : Fintype g.Vertex := g.vertexFintype
    letI : DecidableEq g.Vertex := g.vertexDecidableEq
    g.mergeChannel q E = g.spreadChannel q hq E := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  classical
  funext a
  ext v
  rw [g.mergeChannel_apply_eq_integral q hq E a v]
  change
    posteriorLawIntegralExp q E
      (fun r => r a * g.weights r v) / q a =
    g.spreadMass q E v * g.point v a / q a
  congr 1
  unfold spreadMass
  unfold posteriorLawIntegralExp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro o _ho
  dsimp
  rw [g.weights_target o]
  by_cases hv : v = g.targetVertex o
  · subst v
    simp [g.point_target o]
  · simp [hv]

theorem samePosteriorLawExp_mergeChannel_of_adapted
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (g : @FiniteAdaptedSimplexBarycentricGrid
      A E.OutcomeType inferInstance inferInstance inferInstance
      E.outFintype
      (fun o : E.OutcomeType => E.posterior q o)) :
    letI : Fintype E.OutcomeType := E.outFintype
    letI : DecidableEq E.OutcomeType := E.outDecEq
    letI : Fintype g.Vertex := g.vertexFintype
    letI : DecidableEq g.Vertex := g.vertexDecidableEq
    SamePosteriorLawExp q
      (FiniteExperimentOn.ofChannel (g.mergeChannel q E)) E := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  letI : Fintype g.Vertex := g.vertexFintype
  letI : DecidableEq g.Vertex := g.vertexDecidableEq
  rw [g.mergeChannel_eq_spreadChannel_of_adapted q hq E]
  exact g.samePosteriorLawExp_spreadChannel_of_adapted q hq E

end FiniteAdaptedSimplexBarycentricGrid

/-- A single fixed-alphabet spread/merge sandwich for two weakly convergent
posterior-law sequences. The upper grid is adapted to the atoms of the left
limit and the lower grid to the atoms of the right limit. -/
structure FinitePosteriorLawFixedSandwichData
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A)
    (leftSeq : ℕ → FiniteExperimentOn A) (leftLimit : FiniteExperimentOn A)
    (rightSeq : ℕ → FiniteExperimentOn A) (rightLimit : FiniteExperimentOn A)
    where
  UpperOutcome : Type u
  upperFintype : Fintype UpperOutcome
  upperDecidableEq : DecidableEq UpperOutcome
  LowerOutcome : Type u
  lowerFintype : Fintype LowerOutcome
  lowerDecidableEq : DecidableEq LowerOutcome
  upperSeq : ℕ → @Channel A UpperOutcome upperFintype
  upperLimit : @Channel A UpperOutcome upperFintype
  lowerSeq : ℕ → @Channel A LowerOutcome lowerFintype
  lowerLimit : @Channel A LowerOutcome lowerFintype
  upper_channel_converges : ChannelConverges upperSeq upperLimit
  lower_channel_converges : ChannelConverges lowerSeq lowerLimit
  upper_spreads_left :
    ∀ n,
      letI : Fintype UpperOutcome := upperFintype
      letI : DecidableEq UpperOutcome := upperDecidableEq
      ExperimentPostprocesses
        (FiniteExperimentOn.ofChannel (upperSeq n)) (leftSeq n)
  right_spreads_lower :
    ∀ n,
      letI : Fintype LowerOutcome := lowerFintype
      letI : DecidableEq LowerOutcome := lowerDecidableEq
      ExperimentPostprocesses
        (rightSeq n) (FiniteExperimentOn.ofChannel (lowerSeq n))
  upper_limit_law :
    letI : Fintype UpperOutcome := upperFintype
    letI : DecidableEq UpperOutcome := upperDecidableEq
    SamePosteriorLawExp q
      (FiniteExperimentOn.ofChannel upperLimit) leftLimit
  lower_limit_law :
    letI : Fintype LowerOutcome := lowerFintype
    letI : DecidableEq LowerOutcome := lowerDecidableEq
    SamePosteriorLawExp q
      (FiniteExperimentOn.ofChannel lowerLimit) rightLimit

/-- The fixed-alphabet posterior-law sandwich follows in Lean from the
explicit finite vertex-insertion construction above. -/
noncomputable def finitePosteriorLawFixedSandwich
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (leftSeq : ℕ → FiniteExperimentOn A) (leftLimit : FiniteExperimentOn A)
    (rightSeq : ℕ → FiniteExperimentOn A) (rightLimit : FiniteExperimentOn A)
    (hleft : PosteriorLawConvergesAtExp q leftSeq leftLimit)
    (hright : PosteriorLawConvergesAtExp q rightSeq rightLimit) :
    FinitePosteriorLawFixedSandwichData
      q leftSeq leftLimit rightSeq rightLimit := by
  letI : Fintype leftLimit.OutcomeType := leftLimit.outFintype
  letI : DecidableEq leftLimit.OutcomeType := leftLimit.outDecEq
  letI : Fintype rightLimit.OutcomeType := rightLimit.outFintype
  letI : DecidableEq rightLimit.OutcomeType := rightLimit.outDecEq
  let upperGrid :=
    Classical.choice
      (FiniteAdaptedSimplexBarycentricGrid.exists_adaptedGrid
        (fun o : leftLimit.OutcomeType => leftLimit.posterior q o))
  let lowerGrid :=
    Classical.choice
      (FiniteAdaptedSimplexBarycentricGrid.exists_adaptedGrid
        (fun o : rightLimit.OutcomeType => rightLimit.posterior q o))
  exact
    { UpperOutcome := upperGrid.Vertex
      upperFintype := upperGrid.vertexFintype
      upperDecidableEq := upperGrid.vertexDecidableEq
      LowerOutcome := lowerGrid.Vertex
      lowerFintype := lowerGrid.vertexFintype
      lowerDecidableEq := lowerGrid.vertexDecidableEq
      upperSeq := fun n => upperGrid.spreadChannel q hq (leftSeq n)
      upperLimit := upperGrid.spreadChannel q hq leftLimit
      lowerSeq := fun n => lowerGrid.mergeChannel q (rightSeq n)
      lowerLimit := lowerGrid.mergeChannel q rightLimit
      upper_channel_converges :=
        upperGrid.spreadChannel_converges q hq leftSeq leftLimit hleft
      lower_channel_converges :=
        lowerGrid.mergeChannel_converges q hq rightSeq rightLimit hright
      upper_spreads_left := fun n =>
        upperGrid.experimentPostprocesses_of_spreadChannel q hq (leftSeq n)
      right_spreads_lower := fun n =>
        lowerGrid.experimentPostprocesses_mergeChannel q (rightSeq n)
      upper_limit_law :=
        upperGrid.samePosteriorLawExp_spreadChannel_of_adapted
          q hq leftLimit
      lower_limit_law :=
        lowerGrid.samePosteriorLawExp_mergeChannel_of_adapted
          q hq rightLimit }

end TraceableAgency
