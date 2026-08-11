/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation.AtomicSpanning

namespace TraceableAgency

universe u v

/-!
### Full-support branch reachability

The finite construction is binary: choose a positive branch mass `ε` dominated
by `q` relative to the target posterior `r`, set
`P(a, target) = ε r(a) / q(a)`, and put the remaining probability on the other
branch.
-/

/-- A narrow finite-order interface: for any two full-support finite
distributions, choose a positive branch mass `ε` small enough that
`ε r(a) ≤ q(a)` for every action. -/
structure FinitePositiveBranchMassDominatedAssumptions : Prop where
  exists_dominated_mass :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q r : Dist A), q.FullSupport → r.FullSupport →
      ∃ ε : ℝ, 0 < ε ∧ ∀ a : A, ε * r a ≤ q a

/-- A full-support finite distribution has a positive uniform lower bound on
all coordinates. -/
theorem exists_positive_lower_bound_fullSupport {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : A, δ ≤ q a := by
  classical
  let vals : Finset ℝ := Finset.univ.image (fun a : A => q a)
  have hvals_nonempty : vals.Nonempty := by
    rcases (inferInstance : Nonempty A) with ⟨a0⟩
    exact ⟨q a0, by simp [vals]⟩
  let δ : ℝ := vals.min' hvals_nonempty
  refine ⟨δ, ?_, ?_⟩
  · have hmem : δ ∈ vals := Finset.min'_mem vals hvals_nonempty
    rcases Finset.mem_image.mp hmem with ⟨a, _ha, haeq⟩
    rw [← haeq]
    exact hq a
  · intro a
    have hmem : q a ∈ vals := by simp [vals]
    exact Finset.min'_le vals (q a) hmem

/-- Full-support finite distributions have a positive branch mass dominated by
the source prior relative to the target posterior. -/
theorem exists_positive_branch_mass_dominated {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) (_hr : r.FullSupport) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : A, ε * r a ≤ q a := by
  rcases exists_positive_lower_bound_fullSupport q hq with ⟨δ, hδ_pos, hδ_le⟩
  refine ⟨δ / 2, by linarith, ?_⟩
  intro a
  have hε_nonneg : 0 ≤ δ / 2 := by linarith
  have hr_le_one : r a ≤ 1 := Dist.prob_le_one r a
  have hmul_le : (δ / 2) * r a ≤ δ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr_le_one hε_nonneg]
  have hhalf_le_delta : δ / 2 ≤ δ := by linarith
  exact le_trans hmul_le (le_trans hhalf_le_delta (hδ_le a))

/-- Full-support source priors have a positive branch mass dominated by any
finite target posterior, including boundary posteriors. -/
theorem exists_positive_branch_mass_dominated_target {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : A, ε * r a ≤ q a := by
  rcases exists_positive_lower_bound_fullSupport q hq with ⟨δ, hδ_pos, hδ_le⟩
  refine ⟨δ / 2, by linarith, ?_⟩
  intro a
  have hε_nonneg : 0 ≤ δ / 2 := by linarith
  have hr_le_one : r a ≤ 1 := Dist.prob_le_one r a
  have hmul_le : (δ / 2) * r a ≤ δ / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hr_le_one hε_nonneg]
  have hhalf_le_delta : δ / 2 ≤ δ := by linarith
  exact le_trans hmul_le (le_trans hhalf_le_delta (hδ_le a))

/-- The finite dominated-mass interface is internally proved by taking half of
the positive minimum of the source prior's coordinates. -/
theorem positiveBranchMassDominated_of_finite :
    FinitePositiveBranchMassDominatedAssumptions.{u} where
  exists_dominated_mass := by
    intro A _ _ _ q r hq hr
    exact exists_positive_branch_mass_dominated q r hq hr

/-- Binary first-stage channel with target branch posterior `r`, assuming a
positive dominated branch mass has been chosen. -/
noncomputable def binaryReachChannel {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) : Channel A (ULift.{u} Bool) :=
  fun a =>
    { prob := fun b => if b.down then ε * r a / q a else 1 - ε * r a / q a
      nonneg := by
        intro b
        by_cases hb : b.down = true
        · simp [hb]
          exact div_nonneg (mul_nonneg hε_nonneg (r.nonneg a)) (q.nonneg a)
        · have hble : ε * r a / q a ≤ 1 := by
            by_cases hqpos : 0 < q a
            · rw [div_le_iff₀ hqpos]
              simpa using hdom a
            · have hqzero : q a = 0 := le_antisymm (le_of_not_gt hqpos) (q.nonneg a)
              have hmul_nonneg : 0 ≤ ε * r a := mul_nonneg hε_nonneg (r.nonneg a)
              have hmul_zero : ε * r a = 0 := by
                exact le_antisymm (by simpa [hqzero] using hdom a) hmul_nonneg
              simp [hqzero, hmul_zero]
          simp [hb, hble]
      sum_eq_one := by
        have huniv :
            (Finset.univ : Finset (ULift.{u} Bool)) =
              {ULift.up false, ULift.up true} := by
          ext b
          cases b with
          | up b =>
            cases b <;> simp
        rw [huniv]
        simp }

/-- Under a dominated positive branch mass, the binary reachability channel has
target branch marginal `ε`. -/
theorem outcomeMarginal_binaryReachChannel_true {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (ε : ℝ) (hε_nonneg : 0 ≤ ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    (Channel.outcomeMarginal (binaryReachChannel q r ε hε_nonneg hdom) q) (ULift.up true) =
      ε := by
  unfold Channel.outcomeMarginal binaryReachChannel
  simp
  calc
    (∑ a : A, q a * (ε * r a / q a)) =
        ∑ a : A, ε * r a := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases hqpos : q a = 0
      · have hmul_nonneg : 0 ≤ ε * r a := mul_nonneg hε_nonneg (r.nonneg a)
        have hmul_zero : ε * r a = 0 :=
          le_antisymm (by simpa [hqpos] using hdom a) hmul_nonneg
        simp [hqpos, hmul_zero]
      · field_simp [hqpos]
    _ = ε * ∑ a : A, r a := by
      simp [Finset.mul_sum]
    _ = ε := by
      rw [r.sum_eq_one]
      ring

/-- The dominated binary channel reaches the target full-support posterior on
the `true` branch. -/
theorem branchPosterior_binaryReachChannel_true {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (ε : ℝ) (hε_pos : 0 < ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    branchPosterior (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q (ULift.up true) = r := by
  ext a
  unfold branchPosterior Channel.posterior
  have hmarg :
      (Channel.outcomeMarginal (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q) (ULift.up true) =
        ε :=
    outcomeMarginal_binaryReachChannel_true q r ε (le_of_lt hε_pos) hdom
  have hmarg_pos :
      (Channel.outcomeMarginal (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q) (ULift.up true) > 0 := by
    rw [hmarg]
    exact hε_pos
  rw [dif_pos hmarg_pos]
  change
    q a * (ε * r a / q a) /
      (Channel.outcomeMarginal (binaryReachChannel q r ε (le_of_lt hε_pos) hdom) q) (ULift.up true) =
        r a
  rw [hmarg]
  by_cases hqzero : q a = 0
  · have hmul_nonneg : 0 ≤ ε * r a := mul_nonneg (le_of_lt hε_pos) (r.nonneg a)
    have hmul_zero : ε * r a = 0 :=
      le_antisymm (by simpa [hqzero] using hdom a) hmul_nonneg
    have hra_zero : r a = 0 := by
      nlinarith
    simp [hqzero, hra_zero]
  · field_simp [hqzero, ne_of_gt hε_pos]

/-- A dominated positive branch mass gives the required full-support branch
reachability witness. -/
theorem fullSupportBranchReachability_of_dominated_mass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport) (_hr : r.FullSupport)
    (ε : ℝ) (hε_pos : 0 < ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    ∃ (O₁ : Type u), ∃ (hO₁ : Fintype O₁),
    ∃ (hO₁dec : DecidableEq O₁),
      letI : Fintype O₁ := hO₁
      letI : DecidableEq O₁ := hO₁dec
      ∃ (P₁ : Channel A O₁), ∃ target : O₁,
        BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r := by
  refine ⟨ULift.{u} Bool, inferInstance, inferInstance,
    binaryReachChannel q r ε (le_of_lt hε_pos) hdom, ULift.up true, ?_, ?_⟩
  · unfold BranchPositive
    rw [outcomeMarginal_binaryReachChannel_true q r ε (le_of_lt hε_pos) hdom]
    exact hε_pos
  · exact branchPosterior_binaryReachChannel_true q r ε hε_pos hdom

/-- A dominated positive branch mass reaches any target posterior from a
full-support source prior.  This is the boundary-capable version of
`fullSupportBranchReachability_of_dominated_mass`; the construction itself never
uses full support of the target. -/
theorem branchReachability_of_dominated_mass {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (_hq : q.FullSupport)
    (ε : ℝ) (hε_pos : 0 < ε)
    (hdom : ∀ a : A, ε * r a ≤ q a) :
    ∃ (O₁ : Type u), ∃ (hO₁ : Fintype O₁),
    ∃ (hO₁dec : DecidableEq O₁),
      letI : Fintype O₁ := hO₁
      letI : DecidableEq O₁ := hO₁dec
      ∃ (P₁ : Channel A O₁), ∃ target : O₁,
        BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r := by
  refine ⟨ULift.{u} Bool, inferInstance, inferInstance,
    binaryReachChannel q r ε (le_of_lt hε_pos) hdom, ULift.up true, ?_, ?_⟩
  · unfold BranchPositive
    rw [outcomeMarginal_binaryReachChannel_true q r ε (le_of_lt hε_pos) hdom]
    exact hε_pos
  · exact branchPosterior_binaryReachChannel_true q r ε hε_pos hdom

/-- Every finite target posterior, full-support or boundary, is reachable with
positive probability from any full-support source prior. -/
theorem branchReachability_of_fullSupport_prior {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q r : Dist A) (hq : q.FullSupport) :
    ∃ (O₁ : Type u), ∃ (hO₁ : Fintype O₁),
    ∃ (hO₁dec : DecidableEq O₁),
      letI : Fintype O₁ := hO₁
      letI : DecidableEq O₁ := hO₁dec
      ∃ (P₁ : Channel A O₁), ∃ target : O₁,
        BranchPositive P₁ q target ∧ branchPosterior P₁ q target = r := by
  rcases exists_positive_branch_mass_dominated_target q r hq with
    ⟨ε, hε_pos, hdom⟩
  exact branchReachability_of_dominated_mass q r hq ε hε_pos hdom

/-- The full-support reachability package follows from the finite dominated
positive branch-mass choice interface. -/
theorem fullSupportBranchReachability_of_dominatedMass
    (hmass : FinitePositiveBranchMassDominatedAssumptions.{u}) :
    FiniteFullSupportBranchReachabilityAssumptions.{u} where
  reaches := by
    intro A _ _ _ q r hq hr
    rcases hmass.exists_dominated_mass q r hq hr with ⟨ε, hε_pos, hdom⟩
    exact fullSupportBranchReachability_of_dominated_mass q r hq hr ε hε_pos hdom

/-- Full-support branch reachability is internal: choose a finite dominated
positive branch mass, then use the explicit binary reachability channel. -/
theorem fullSupportBranchReachability_of_finite :
    FiniteFullSupportBranchReachabilityAssumptions.{u} :=
  fullSupportBranchReachability_of_dominatedMass positiveBranchMassDominated_of_finite

/-- Finite linear-functional same-sign scalar interface.

For linear functionals on signed posterior laws, agreement of the positive
half-space and of the zero set forces a positive scalar multiple relation. -/
structure FiniteLinearFunctionalSameSignScalarAssumptions : Prop where
  same_sign_scalar :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (L₁ L₂ : PosteriorLawSigned A → ℝ),
      (∀ η ζ : PosteriorLawSigned A,
        L₁ (posteriorLawSignedAdd η ζ) = L₁ η + L₁ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₁ (posteriorLawSignedSMul c η) = c * L₁ η) →
      (∀ η ζ : PosteriorLawSigned A,
        L₂ (posteriorLawSignedAdd η ζ) = L₂ η + L₂ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₂ (posteriorLawSignedSMul c η) = c * L₂ η) →
      (∀ η : PosteriorLawSigned A,
        η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
          (0 < L₁ η ↔ 0 < L₂ η) ∧ (L₁ η = 0 ↔ L₂ η = 0)) →
      (∃ η : PosteriorLawSigned A, L₂ η ≠ 0) →
      ∃ β : ℝ, 0 < β ∧ ∀ η : PosteriorLawSigned A, L₁ η = β * L₂ η

/-- Tangent-subspace version of the same-sign scalar theorem.

This is the faithful linear-algebra interface for the branch path argument:
A6 supplies sign agreement only on genuine tangent signed posterior laws, not
on all extensional functionals `PosteriorLawSigned A`. -/
structure FiniteLinearFunctionalSameSignScalarOnTangentAssumptions : Prop where
  same_sign_scalar_on_tangent :
    ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (L₁ L₂ : PosteriorLawSigned A → ℝ),
      (∀ η ζ : PosteriorLawSigned A,
        L₁ (posteriorLawSignedAdd η ζ) = L₁ η + L₁ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₁ (posteriorLawSignedSMul c η) = c * L₁ η) →
      (∀ η ζ : PosteriorLawSigned A,
        L₂ (posteriorLawSignedAdd η ζ) = L₂ η + L₂ ζ) →
      (∀ c : ℝ, ∀ η : PosteriorLawSigned A,
        L₂ (posteriorLawSignedSMul c η) = c * L₂ η) →
      (∀ η : PosteriorLawSigned A,
        PosteriorLawTangent η →
        η ≠ ((fun _ => 0) : PosteriorLawSigned A) →
          (0 < L₁ η ↔ 0 < L₂ η) ∧ (L₁ η = 0 ↔ L₂ η = 0)) →
      (∃ η : PosteriorLawSigned A, PosteriorLawTangent η ∧ L₂ η ≠ 0) →
      ∃ β : ℝ, 0 < β ∧
        ∀ η : PosteriorLawSigned A, PosteriorLawTangent η → L₁ η = β * L₂ η

/-- Zero scalar multiplication preserves the custom zero signed posterior law. -/
private theorem posteriorLawSignedSMul_zero_zero {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] :
    posteriorLawSignedSMul 0 ((fun _ => 0) : PosteriorLawSigned A) =
      ((fun _ => 0) : PosteriorLawSigned A) := by
  funext φ
  simp [posteriorLawSignedSMul]

/-- A custom-linear functional sends the custom zero signed posterior law to
zero. -/
private theorem posteriorLawLinear_zero_of_smul {A : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    (L : PosteriorLawSigned A → ℝ)
    (hsmul : ∀ c : ℝ, ∀ η : PosteriorLawSigned A,
      L (posteriorLawSignedSMul c η) = c * L η) :
    L ((fun _ => 0) : PosteriorLawSigned A) = 0 := by
  simpa [posteriorLawSignedSMul_zero_zero] using
    hsmul 0 ((fun _ => 0) : PosteriorLawSigned A)

/-- Direct finite-dimensional ratio proof of the tangent same-sign scalar
theorem.

This discharges the linear-algebra part of the branch path argument on the
tangent subspace.  It deliberately uses the project's custom signed-law
addition and scalar multiplication operations rather than introducing a
separate mathlib linear-map wrapper. -/
theorem finiteLinearFunctionalSameSignScalarOnTangent_of_direct :
    FiniteLinearFunctionalSameSignScalarOnTangentAssumptions.{u} where
  same_sign_scalar_on_tangent := by
    intro A _ _ _ L₁ L₂ hL₁add hL₁smul hL₂add hL₂smul hsign hnonzero
    classical
    let zeroη : PosteriorLawSigned A := (fun _ => 0)
    have hL₁_zero : L₁ zeroη = 0 := by
      simpa [zeroη] using posteriorLawLinear_zero_of_smul L₁ hL₁smul
    have hL₂_zero : L₂ zeroη = 0 := by
      simpa [zeroη] using posteriorLawLinear_zero_of_smul L₂ hL₂smul
    rcases hnonzero with ⟨x0, hx0_tan, hx0_L₂_ne⟩
    let x : PosteriorLawSigned A :=
      if 0 < L₂ x0 then x0 else posteriorLawSignedSMul (-1) x0
    have hx_tan : PosteriorLawTangent x := by
      dsimp [x]
      split_ifs
      · exact hx0_tan
      · exact PosteriorLawTangent_smul (-1) hx0_tan
    have hx_L₂_pos : 0 < L₂ x := by
      dsimp [x]
      split_ifs with hpos
      · exact hpos
      · have hx0_le : L₂ x0 ≤ 0 := le_of_not_gt hpos
        have hx0_lt : L₂ x0 < 0 := lt_of_le_of_ne hx0_le hx0_L₂_ne
        rw [hL₂smul]
        linarith
    have hx_L₂_ne : L₂ x ≠ 0 := ne_of_gt hx_L₂_pos
    have hx_ne : x ≠ zeroη := by
      intro hx_eq
      have : L₂ x = 0 := by
        simpa [hx_eq, zeroη] using hL₂_zero
      exact hx_L₂_ne this
    have hx_L₁_pos : 0 < L₁ x := (hsign x hx_tan hx_ne).1.mpr hx_L₂_pos
    let β : ℝ := L₁ x / L₂ x
    have hβ_pos : 0 < β := div_pos hx_L₁_pos hx_L₂_pos
    refine ⟨β, hβ_pos, ?_⟩
    intro y hy_tan
    let c : ℝ := -(L₂ y / L₂ x)
    let z : PosteriorLawSigned A :=
      posteriorLawSignedAdd y (posteriorLawSignedSMul c x)
    have hz_tan : PosteriorLawTangent z := by
      exact PosteriorLawTangent_add hy_tan (PosteriorLawTangent_smul c hx_tan)
    have hz_L₂_zero : L₂ z = 0 := by
      calc
        L₂ z = L₂ y + L₂ (posteriorLawSignedSMul c x) := by
          simp [z, hL₂add]
        _ = L₂ y + c * L₂ x := by
          rw [hL₂smul]
        _ = 0 := by
          dsimp [c]
          field_simp [hx_L₂_ne]
          ring_nf
    have hz_L₁_zero : L₁ z = 0 := by
      by_cases hz_zero : z = zeroη
      · simpa [hz_zero, zeroη] using hL₁_zero
      · exact (hsign z hz_tan hz_zero).2.mpr hz_L₂_zero
    have hz_L₁_expand : L₁ z = L₁ y + c * L₁ x := by
      calc
        L₁ z = L₁ y + L₁ (posteriorLawSignedSMul c x) := by
          simp [z, hL₁add]
        _ = L₁ y + c * L₁ x := by
          rw [hL₁smul]
    have hsum : L₁ y + c * L₁ x = 0 := by
      simpa [hz_L₁_expand] using hz_L₁_zero
    change L₁ y = β * L₂ y
    dsimp [β, c] at hsum ⊢
    field_simp [hx_L₂_ne] at hsum ⊢
    ring_nf at hsum ⊢
    linarith

end TraceableAgency
