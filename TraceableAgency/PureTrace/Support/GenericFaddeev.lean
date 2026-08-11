/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.Faddeev
import TraceableAgency.Vendor.Shannon.Final

/-!
# A finite Faddeev theorem

This file discharges `ClassicalFaddeevTheoremAssumptions` in Lean.  The proof
uses the elementary finite Shannon-uniqueness development vendored (under its
MIT licence) in `TraceableAgency.Vendor.Shannon`, together with bridge lemmas
proving that the weaker Faddeev hypotheses used by this project imply the
hypotheses of that development.

No preference-theoretic assumption occurs in this file.
-/

namespace TraceableAgency

universe u v

open Filter Topology

namespace GenericFaddeev

noncomputable section

/- All finite types in this generic proof are used extensionally; choosing
classical decidable equality once prevents irrelevant instance choices from
leaking into the polymorphic entropy functional. -/
local instance genericClassicalDecidableEq {X : Type v} : DecidableEq X :=
  Classical.decEq X

/-! ## The two finite-distribution representations -/

/-- Forget the named `Dist` structure in favour of the subtype representation
used by the finite Shannon development. -/
def toShannonProb {A : Type} [Fintype A] (q : Dist A) :
    Shannon.ProbDist A :=
  ⟨q.prob, q.nonneg, q.sum_eq_one⟩

/-- Return from the subtype representation to the project's `Dist`. -/
def ofShannonProb {A : Type} [Fintype A] (q : Shannon.ProbDist A) :
    Dist A where
  prob := q.1
  nonneg := q.2.1
  sum_eq_one := q.2.2

@[simp]
theorem toShannonProb_apply {A : Type} [Fintype A]
    (q : Dist A) (a : A) :
    toShannonProb q a = q a := rfl

@[simp]
theorem ofShannonProb_apply {A : Type} [Fintype A]
    (q : Shannon.ProbDist A) (a : A) :
    ofShannonProb q a = q a := rfl

@[simp]
theorem ofShannonProb_toShannonProb {A : Type} [Fintype A]
    (q : Dist A) :
    ofShannonProb (toShannonProb q) = q := by
  ext a
  rfl

@[simp]
theorem toShannonProb_ofShannonProb {A : Type} [Fintype A]
    (q : Shannon.ProbDist A) :
    toShannonProb (ofShannonProb q) = q := by
  rfl

/-- The two entropy definitions agree on probability distributions. -/
theorem entropy_eq_shannonEntropyNat {A : Type} [Fintype A]
    (q : Dist A) :
    H(q) = Shannon.entropyNat (toShannonProb q) := by
  classical
  unfold entropy Shannon.entropyNat
  calc
    (∑ a, entropyTerm (q a)) =
        ∑ a, -(q a * Real.log (q a)) := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases hzero : q a = 0
      · simp [hzero]
      · have hpos : 0 < q a := lt_of_le_of_ne (q.nonneg a) (Ne.symm hzero)
        rw [entropyTerm_eq_neg_mul_log hpos]
        ring
    _ = -(∑ a, q a * Real.log (q a)) := by
      rw [← Finset.sum_neg_distrib]

/-! ## The augmented entropy functional -/

/-- Lift a small finite distribution to the ambient universe used by `Hfun`. -/
def liftShannonProb
    {A : Type} [Fintype A]
    (q : Shannon.ProbDist A) :
    Dist (ULift.{u, 0} A) where
  prob := fun a => q a.down
  nonneg := fun a => q.2.1 a.down
  sum_eq_one := by
    exact
      ((Equiv.ulift (α := A)).symm.sum_comp
        (fun a : ULift.{u, 0} A => q a.down)).symm.trans q.2.2

@[simp]
theorem liftShannonProb_apply
    {A : Type} [Fintype A]
    (q : Shannon.ProbDist A) (a : ULift.{u, 0} A) :
    liftShannonProb q a = q a.down := rfl

/-- Add ordinary Shannon entropy to the candidate.  This harmless device makes
strict growth on uniform laws automatic once weak growth of the candidate has
been derived from grouping and nonnegativity. -/
def augmented
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    {A : Type} [Fintype A]
    (q : Shannon.ProbDist A) : ℝ :=
  letI : Nonempty (ULift.{u, 0} A) :=
    Nonempty.map ULift.up (Shannon.nonempty_of_probDist q)
  Hfun (liftShannonProb.{u} q) + Shannon.entropyNat q

/-! ## Expansibility upgrades full-support symmetry to global symmetry -/

/-- Relabeling transports supports bijectively. -/
def supportRelabelEquiv
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) :
    supportSubtype q ≃ supportSubtype (Relabeling.relabelDist e q) where
  toFun a := ⟨e a.1, by
    simpa [Dist.support, Relabeling.relabelDist_apply] using a.2⟩
  invFun b := ⟨e.symm b.1, by
    simpa [Dist.support, Relabeling.relabelDist_apply] using b.2⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv b := by
    apply Subtype.ext
    simp

theorem restrict_relabel_eq_relabel_restrict
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    letI : Nonempty (supportSubtype (Relabeling.relabelDist e q)) :=
      supportSubtype_nonempty (Relabeling.relabelDist e q)
    (Relabeling.relabelDist e q).restrictToSupport =
      Relabeling.relabelDist (supportRelabelEquiv e q) q.restrictToSupport := by
  ext b
  rfl

/-- The stated full-support relabeling axiom plus support restriction gives
ordinary relabeling invariance, including boundary distributions. -/
theorem relabel_invariant
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) :
    Hfun (Relabeling.relabelDist e q) = Hfun q := by
  classical
  let r := Relabeling.relabelDist e q
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  letI : Nonempty (supportSubtype r) := supportSubtype_nonempty r
  have hrelabel :
      Hfun (Relabeling.relabelDist (supportRelabelEquiv e q)
        q.restrictToSupport) =
        Hfun q.restrictToSupport :=
    h.fullSupport_relabel (supportRelabelEquiv e q) q.restrictToSupport
      (Dist.restrictToSupport_fullSupport q)
  calc
    Hfun r = Hfun r.restrictToSupport := h.support_restriction r
    _ = Hfun (Relabeling.relabelDist (supportRelabelEquiv e q)
          q.restrictToSupport) := by
      simpa [r] using
        congrArg Hfun (restrict_relabel_eq_relabel_restrict e q)
    _ = Hfun q.restrictToSupport := hrelabel
    _ = Hfun q := (h.support_restriction q).symm

/-! ## Relabeling and grouping for the lifted functional -/

def liftEquiv {A B : Type} (e : A ≃ B) :
    ULift.{u, 0} A ≃ ULift.{u, 0} B where
  toFun a := ULift.up (e a.down)
  invFun b := ULift.up (e.symm b.down)
  left_inv a := by
    cases a
    simp
  right_inv b := by
    cases b
    simp

def liftSigmaEquiv
    {A : Type} {B : A → Type} :
    ((a : ULift.{u, 0} A) × ULift.{u, 0} (B a.down)) ≃
      ULift.{u, 0} ((a : A) × B a) where
  toFun x := ULift.up ⟨x.1.down, x.2.down⟩
  invFun x := ⟨ULift.up x.down.1, ULift.up x.down.2⟩
  left_inv x := by
    rcases x with ⟨⟨a⟩, ⟨b⟩⟩
    rfl
  right_inv x := by
    rcases x with ⟨⟨a, b⟩⟩
    rfl

theorem liftShannonProb_relabel
    {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Shannon.ProbDist A) :
    liftShannonProb (Shannon.relabelProb e q) =
      Relabeling.relabelDist (liftEquiv e) (liftShannonProb q) := by
  ext b
  rfl

theorem liftShannonProb_compose
    {A : Type} [Fintype A]
    {B : A → Type} [∀ a, Fintype (B a)]
    (p : Shannon.ProbDist A)
    (q : ∀ a, Shannon.ProbDist (B a)) :
    liftShannonProb (Shannon.composeProb p q) =
      Relabeling.relabelDist liftSigmaEquiv
        (sigmaDist (liftShannonProb p)
          (fun a : ULift.{u, 0} A => liftShannonProb (q a.down))) := by
  classical
  letI : ∀ a : ULift.{u, 0} A,
      DecidableEq (ULift.{u, 0} (B a.down)) :=
    fun _ => Classical.decEq _
  ext x
  rfl

theorem entropy_relabel
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) :
    H(Relabeling.relabelDist e q) = H(q) := by
  classical
  unfold entropy
  simpa [Relabeling.relabelDist_apply] using
    e.symm.sum_comp (fun a : A => entropyTerm (q a))

theorem entropy_liftShannonProb
    {A : Type} [Fintype A] (q : Shannon.ProbDist A) :
    H(liftShannonProb.{u} q) = Shannon.entropyNat q := by
  classical
  calc
    H(liftShannonProb.{u} q) =
        ∑ a : A, entropyTerm (q a) := by
      unfold entropy
      simpa using
        ((Equiv.ulift.{u, 0} (α := A)).symm.sum_comp
          (fun a : ULift.{u, 0} A => entropyTerm (q a.down))).symm
    _ = H(ofShannonProb q) := rfl
    _ = Shannon.entropyNat q := entropy_eq_shannonEntropyNat (ofShannonProb q)

theorem entropyNat_relabel
    {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Shannon.ProbDist A) :
    Shannon.entropyNat (Shannon.relabelProb e q) =
      Shannon.entropyNat q := by
  classical
  unfold Shannon.entropyNat
  congr 1
  simpa [Shannon.relabelProb] using
    e.symm.sum_comp (fun a : A => q a * Real.log (q a))

theorem entropyNat_compose
    {A : Type} [Fintype A]
    {B : A → Type} [∀ a, Fintype (B a)]
    (p : Shannon.ProbDist A)
    (q : ∀ a, Shannon.ProbDist (B a)) :
    Shannon.entropyNat (Shannon.composeProb p q) =
      Shannon.entropyNat p +
        ∑ a, p a * Shannon.entropyNat (q a) := by
  classical
  rw [← entropy_liftShannonProb.{0}, liftShannonProb_compose.{0},
    entropy_relabel, entropy_sigma_chain, entropy_liftShannonProb.{0}]
  apply congrArg (fun z => Shannon.entropyNat p + z)
  calc
    (∑ x : ULift.{0, 0} A,
        (liftShannonProb p) x *
          H(liftShannonProb (q x.down))) =
        ∑ a : A, p a * H(liftShannonProb (q a)) := by
      exact
        ((Equiv.ulift.{0, 0} (α := A)).symm.sum_comp
          (fun x : ULift.{0, 0} A =>
            (liftShannonProb p) x *
              H(liftShannonProb (q x.down)))).symm
    _ = ∑ a : A, p a * Shannon.entropyNat (q a) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [entropy_liftShannonProb]

theorem augmented_nonnegative
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A : Type} [Fintype A] (q : Shannon.ProbDist A) :
    0 ≤ augmented Hfun q := by
  classical
  letI : Nonempty (ULift.{u, 0} A) :=
    Nonempty.map ULift.up (Shannon.nonempty_of_probDist q)
  dsimp [augmented]
  have hSh : 0 ≤ Shannon.entropyNat q := by
    calc
      0 ≤ H(ofShannonProb q) := entropy_nonneg _
      _ = Shannon.entropyNat q := by
        simpa using entropy_eq_shannonEntropyNat (ofShannonProb q)
  exact add_nonneg (h.nonnegative _) hSh

theorem augmented_relabel
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Shannon.ProbDist A) :
    augmented Hfun (Shannon.relabelProb e q) = augmented Hfun q := by
  classical
  letI : Nonempty (ULift.{u, 0} A) :=
    Nonempty.map ULift.up (Shannon.nonempty_of_probDist q)
  letI : Nonempty (ULift.{u, 0} B) :=
    Nonempty.map ULift.up
      (Shannon.nonempty_of_probDist (Shannon.relabelProb e q))
  dsimp [augmented]
  rw [liftShannonProb_relabel, relabel_invariant Hfun h,
    entropyNat_relabel]

theorem augmented_grouping
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A : Type} [Fintype A]
    {B : A → Type} [∀ a, Fintype (B a)]
    (p : Shannon.ProbDist A)
    (q : ∀ a, Shannon.ProbDist (B a)) :
    augmented Hfun (Shannon.composeProb p q) =
      augmented Hfun p + ∑ a, p a * augmented Hfun (q a) := by
  classical
  letI : Nonempty (ULift.{u, 0} A) :=
    Nonempty.map ULift.up (Shannon.nonempty_of_probDist p)
  letI : ∀ a : ULift.{u, 0} A, Nonempty (ULift.{u, 0} (B a.down)) :=
    fun a => Nonempty.map ULift.up (Shannon.nonempty_of_probDist (q a.down))
  letI : Nonempty ((a : ULift.{u, 0} A) × ULift.{u, 0} (B a.down)) := by
    let a := Classical.choice (inferInstance : Nonempty (ULift.{u, 0} A))
    exact ⟨⟨a, Classical.choice (inferInstance :
      Nonempty (ULift.{u, 0} (B a.down)))⟩⟩
  letI : Nonempty (ULift.{u, 0} ((a : A) × B a)) :=
    Nonempty.map liftSigmaEquiv
      (inferInstance :
        Nonempty ((a : ULift.{u, 0} A) × ULift.{u, 0} (B a.down)))
  have hgroup :=
    h.strong_additivity
      (fun a : ULift.{u, 0} A => ULift.{u, 0} (B a.down))
      (liftShannonProb p)
      (fun a : ULift.{u, 0} A => liftShannonProb (q a.down))
  have hHfun :
      Hfun (liftShannonProb (Shannon.composeProb p q)) =
        Hfun (liftShannonProb p) +
          ∑ a, p a * Hfun (liftShannonProb (q a)) := by
    rw [liftShannonProb_compose, relabel_invariant Hfun h]
    have hgroup' :
        Hfun (sigmaDist (liftShannonProb p)
          (fun a : ULift.{u, 0} A => liftShannonProb (q a.down))) =
          Hfun (liftShannonProb p) +
            ∑ a : ULift.{u, 0} A,
              (liftShannonProb p) a *
                Hfun (liftShannonProb (q a.down)) := by
      convert hgroup using 1
    rw [hgroup']
    exact congrArg (fun z => Hfun (liftShannonProb p) + z)
      (((Equiv.ulift.{u, 0} (α := A)).symm.sum_comp
        (fun x : ULift.{u, 0} A =>
          (liftShannonProb p) x *
            Hfun (liftShannonProb (q x.down)))).symm)
  have hbase :
      Hfun (liftShannonProb (Shannon.composeProb p q)) +
          Shannon.entropyNat (Shannon.composeProb p q) =
        (Hfun (liftShannonProb p) + Shannon.entropyNat p) +
          ∑ x : A, p x *
            (Hfun (liftShannonProb (q x)) +
              Shannon.entropyNat (q x)) := by
    rw [hHfun, entropyNat_compose]
    have hsum :
        (∑ x : A,
            p x * (Hfun (liftShannonProb (q x)) +
              Shannon.entropyNat (q x))) =
          (∑ x : A, p x * Hfun (liftShannonProb (q x))) +
            ∑ x : A, p x * Shannon.entropyNat (q x) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hsum]
    ring
  simp only [augmented]
  convert hbase using 1
  congr

/-! ## Uniform laws: weak monotonicity from finite block partitions -/

/-- The rational grouping calculation needs only grouping and relabeling, not
continuity or monotonicity. -/
theorem grouping_on_rational_counts_weak
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a))
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A)
    (n : A → ℕ)
    (hpos : ∀ a, 0 < n a)
    (N : ℕ)
    (hN : 0 < N)
    (hsum : (∑ a, n a) = N)
    (hp : ∀ a, p a = (n a : ℝ) / (N : ℝ)) :
    Shannon.Apos G ⟨N, hN⟩ =
      G p + ∑ a, p a * Shannon.Apos G ⟨n a, hpos a⟩ := by
  classical
  let q : (a : A) → Shannon.ProbDist (Fin (n a)) :=
    fun a => Shannon.uniformPNat ⟨n a, hpos a⟩
  have hcard : Fintype.card ((a : A) × Fin (n a)) = N := by
    calc
      Fintype.card ((a : A) × Fin (n a)) =
          ∑ a, Fintype.card (Fin (n a)) := by simp
      _ = ∑ a, n a := by simp
      _ = N := hsum
  let e : ((a : A) × Fin (n a)) ≃ Fin N :=
    Fintype.equivFinOfCardEq hcard
  have hident :
      Shannon.relabelProb e (Shannon.composeProb p q) =
        Shannon.uniformPNat ⟨N, hN⟩ := by
    ext x
    have hNne : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have hnne : (n (e.symm x).1 : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hpos (e.symm x).1))
    simp [Shannon.relabelProb, Shannon.composeProb, Shannon.uniformPNat, q, hp]
    field_simp [hNne, hnne]
  calc
    Shannon.Apos G ⟨N, hN⟩ =
        G (Shannon.relabelProb e (Shannon.composeProb p q)) := by
      change G (Shannon.uniformPNat ⟨N, hN⟩) =
        G (Shannon.relabelProb e (Shannon.composeProb p q))
      rw [hident]
      rfl
    _ = G (Shannon.composeProb p q) := hrelabel e _
    _ = G p + ∑ a, p a * G (q a) := hgroup p q
    _ = G p + ∑ a, p a * Shannon.Apos G ⟨n a, hpos a⟩ := by
      rfl

/-- Block index for Euclidean division: full `N`-blocks and one singleton
block for each remainder point. -/
abbrev divisionBlocks (M N : ℕ) : Type :=
  Fin (M / N) ⊕ Fin (M % N)

def divisionCount (M N : ℕ) : divisionBlocks M N → ℕ
  | Sum.inl _ => N
  | Sum.inr _ => 1

theorem divisionCount_pos
    {M N : ℕ} (hN : 0 < N) :
    ∀ k : divisionBlocks M N, 0 < divisionCount M N k := by
  intro k
  cases k with
  | inl _ => exact hN
  | inr _ => exact Nat.zero_lt_one

theorem sum_divisionCount
    {M N : ℕ} :
    (∑ k : divisionBlocks M N, divisionCount M N k) = M := by
  classical
  simpa [divisionCount, divisionBlocks, Nat.mul_comm] using Nat.div_add_mod M N

/-- The outer law whose masses are the relative block sizes. -/
def divisionOuter
    (M N : ℕ) (hM : 0 < M) (_hN : 0 < N) :
    Shannon.ProbDist (divisionBlocks M N) := by
  refine ⟨fun k => (divisionCount M N k : ℝ) / (M : ℝ), ?_⟩
  constructor
  · intro k
    positivity
  · have hMne : (M : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hM)
    calc
      (∑ k : divisionBlocks M N,
          (divisionCount M N k : ℝ) / (M : ℝ)) =
          (∑ k : divisionBlocks M N,
            (divisionCount M N k : ℝ)) / (M : ℝ) := by
        rw [Finset.sum_div]
      _ = (M : ℝ) / (M : ℝ) := by
        rw [← Nat.cast_sum, sum_divisionCount]
      _ = 1 := div_self hMne

@[simp]
theorem divisionOuter_apply
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (k : divisionBlocks M N) :
    divisionOuter M N hM hN k =
      (divisionCount M N k : ℝ) / (M : ℝ) := rfl

/-- A grouping/nonnegative entropy on an `M`-point uniform law dominates the
contribution of all complete `N`-point blocks. -/
theorem Apos_division_lower_bound
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hnonneg :
      ∀ {A : Type} [Fintype A] (p : Shannon.ProbDist A), 0 ≤ G p)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a))
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    (((M / N) * N : ℕ) : ℝ) / (M : ℝ) *
        Shannon.Apos G ⟨N, hN⟩ ≤
      Shannon.Apos G ⟨M, hM⟩ := by
  classical
  let p := divisionOuter M N hM hN
  let n := divisionCount M N
  have hformula :=
    grouping_on_rational_counts_weak G hrelabel hgroup p n
      (divisionCount_pos hN) M hM sum_divisionCount
      (fun k => rfl)
  have houter : 0 ≤ G p := hnonneg p
  have hterms :
      0 ≤ ∑ k : divisionBlocks M N,
        p k * Shannon.Apos G ⟨n k, divisionCount_pos hN k⟩ := by
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (Shannon.prob_nonneg p k)
      (hnonneg (Shannon.uniformPNat ⟨n k, divisionCount_pos hN k⟩))
  have hfull :
      (((M / N) * N : ℕ) : ℝ) / (M : ℝ) *
          Shannon.Apos G ⟨N, hN⟩ ≤
        ∑ k : divisionBlocks M N,
          p k * Shannon.Apos G ⟨n k, divisionCount_pos hN k⟩ := by
    rw [Fintype.sum_sum_type]
    simp only [p, n, divisionOuter_apply, divisionCount]
    have hMN :
        (∑ _i : Fin (M / N),
            (N : ℝ) / (M : ℝ) * Shannon.Apos G ⟨N, hN⟩) =
          (((M / N) * N : ℕ) : ℝ) / (M : ℝ) *
            Shannon.Apos G ⟨N, hN⟩ := by
      simp [Nat.cast_mul]
      ring
    rw [hMN]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (by positivity)
        (hnonneg (Shannon.uniformPNat ⟨1, Nat.zero_lt_one⟩))))
  linarith [hformula, houter, hterms, hfull]

/-- Multiplicative additivity on uniform laws uses only grouping and
relabeling. -/
theorem Apos_mul_weak
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a))
    (n m : ℕ+) :
    Shannon.Apos G (n * m) =
      Shannon.Apos G n + Shannon.Apos G m := by
  let p : Shannon.ProbDist (Fin n) := Shannon.uniformPNat n
  let q : (a : Fin n) → Shannon.ProbDist (Fin m) :=
    fun _ => Shannon.uniformPNat m
  have hsum :
      (∑ a : Fin n, p a * G (q a)) =
        G (Shannon.uniformPNat m) := by
    change (∑ a : Fin n,
      p a * G (Shannon.uniformPNat m)) =
        G (Shannon.uniformPNat m)
    rw [← Finset.sum_mul, Shannon.prob_sum_eq_one]
    ring
  have hident :=
    Shannon.relabel_compose_uniform_eq_uniform_mul n m
  calc
    Shannon.Apos G (n * m) =
        G (Shannon.relabelProb
          (Shannon.sigmaConstFinEquivFinMul n m)
          (Shannon.composeProb p q)) := by
      change G (Shannon.uniformPNat (n * m)) =
        G (Shannon.relabelProb
          (Shannon.sigmaConstFinEquivFinMul n m)
          (Shannon.composeProb p q))
      rw [hident]
    _ = G (Shannon.composeProb p q) := hrelabel _ _
    _ = G p + ∑ a, p a * G (q a) := hgroup p q
    _ = Shannon.Apos G n + Shannon.Apos G m := by
      rw [hsum]
      rfl

theorem Apos_one_zero_weak
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a)) :
    Shannon.Apos G 1 = 0 := by
  have h := Apos_mul_weak G hrelabel hgroup 1 1
  simp only [one_mul] at h
  linarith

theorem Apos_pow_weak
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a))
    (n : ℕ+) (k : ℕ) :
    Shannon.Apos G (n ^ k) = (k : ℝ) * Shannon.Apos G n := by
  induction k with
  | zero =>
      simpa using Apos_one_zero_weak G hrelabel hgroup
  | succ k ih =>
      calc
        Shannon.Apos G (n ^ (k + 1)) =
            Shannon.Apos G (n ^ k * n) := by rw [pow_succ]
        _ = Shannon.Apos G (n ^ k) + Shannon.Apos G n :=
          Apos_mul_weak G hrelabel hgroup (n ^ k) n
        _ = (k : ℝ) * Shannon.Apos G n + Shannon.Apos G n := by rw [ih]
        _ = ((k + 1 : ℕ) : ℝ) * Shannon.Apos G n := by
          push_cast
          ring

def divisionWeight (M N : ℕ) : ℝ :=
  (((M / N) * N : ℕ) : ℝ) / (M : ℝ)

theorem divisionWeight_le_one
    {M N : ℕ} (hM : 0 < M) :
    divisionWeight M N ≤ 1 := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  rw [divisionWeight, div_le_one hMreal]
  exact_mod_cast Nat.div_mul_le_self M N

theorem one_sub_ratio_le_divisionWeight
    {M N : ℕ} (hM : 0 < M) (hN : 0 < N) :
    1 - (N : ℝ) / (M : ℝ) ≤ divisionWeight M N := by
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast hM
  have hdecompNat :
      (M / N) * N + M % N = M := by
    simpa [Nat.mul_comm] using Nat.div_add_mod M N
  have hdecomp :
      (M : ℝ) =
        (((M / N) * N : ℕ) : ℝ) + ((M % N : ℕ) : ℝ) := by
    exact_mod_cast hdecompNat.symm
  have hremNat : M % N < N := Nat.mod_lt M hN
  have hrem : ((M % N : ℕ) : ℝ) < (N : ℝ) := by
    exact_mod_cast hremNat
  rw [divisionWeight]
  have hrewrite :
      1 - (N : ℝ) / (M : ℝ) =
        ((M : ℝ) - (N : ℝ)) / (M : ℝ) := by
    field_simp
  rw [hrewrite]
  exact (div_le_div_iff_of_pos_right hMreal).2 (by linarith)

theorem divisionWeight_pow_tendsto_one
    {n m : ℕ} (hn : 0 < n) (hnm : n < m) :
    Tendsto (fun k : ℕ => divisionWeight (m ^ k) (n ^ k))
      atTop (𝓝 1) := by
  have hm : 0 < m := lt_trans hn hnm
  let r : ℝ := (n : ℝ) / (m : ℝ)
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    exact (div_lt_one (by exact_mod_cast hm)).2 (by exact_mod_cast hnm)
  have hrpow : Tendsto (fun k : ℕ => r ^ k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hlowerlim :
      Tendsto (fun k : ℕ => 1 - r ^ k) atTop (𝓝 1) := by
    convert tendsto_const_nhds.sub hrpow using 1
    all_goals norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerlim tendsto_const_nhds
    (Eventually.of_forall ?_) (Eventually.of_forall ?_)
  · intro k
    have hmpow : 0 < m ^ k := pow_pos hm k
    have hnpow : 0 < n ^ k := pow_pos hn k
    calc
      1 - r ^ k =
          1 - ((n ^ k : ℕ) : ℝ) / ((m ^ k : ℕ) : ℝ) := by
        simp [r, div_pow]
      _ ≤ divisionWeight (m ^ k) (n ^ k) :=
        one_sub_ratio_le_divisionWeight hmpow hnpow
  · intro k
    exact divisionWeight_le_one (pow_pos hm k)

theorem Apos_monotone_weak
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hnonneg :
      ∀ {A : Type} [Fintype A] (p : Shannon.ProbDist A), 0 ≤ G p)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a)) :
    Monotone (Shannon.Apos G) := by
  intro n m hnm
  by_cases heq : n = m
  · subst m
    exact le_rfl
  have hne : (n : ℕ) ≠ (m : ℕ) := by
    intro h
    apply heq
    exact Subtype.ext h
  have hlt : (n : ℕ) < (m : ℕ) := lt_of_le_of_ne hnm hne
  have hwlim :=
    divisionWeight_pow_tendsto_one n.2 hlt
  have hlim :
      Tendsto
        (fun k : ℕ =>
          divisionWeight ((m : ℕ) ^ k) ((n : ℕ) ^ k) *
            Shannon.Apos G n)
        atTop (𝓝 (Shannon.Apos G n)) := by
    convert hwlim.mul_const (Shannon.Apos G n) using 1
    · funext k
      rfl
    · simp
  apply le_of_tendsto hlim
  filter_upwards [eventually_atTop.2 ⟨1, fun k hk => hk⟩] with k hk
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlower :=
    Apos_division_lower_bound G hnonneg hrelabel hgroup
      ((m : ℕ) ^ k) ((n : ℕ) ^ k)
      (pow_pos m.2 k) (pow_pos n.2 k)
  change divisionWeight ((m : ℕ) ^ k) ((n : ℕ) ^ k) *
      Shannon.Apos G (n ^ k) ≤ Shannon.Apos G (m ^ k) at hlower
  rw [Apos_pow_weak G hrelabel hgroup,
    Apos_pow_weak G hrelabel hgroup] at hlower
  nlinarith

/-! ## Strict uniform growth for the augmented functional -/

def liftedCandidate
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    {A : Type} [Fintype A] (q : Shannon.ProbDist A) : ℝ :=
  augmented Hfun q - Shannon.entropyNat q

theorem liftedCandidate_nonnegative
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A : Type} [Fintype A] (q : Shannon.ProbDist A) :
    0 ≤ liftedCandidate Hfun q := by
  classical
  letI : Nonempty (ULift.{u, 0} A) :=
    Nonempty.map ULift.up (Shannon.nonempty_of_probDist q)
  simp only [liftedCandidate, augmented]
  have hh := h.nonnegative (liftShannonProb q)
  linarith

theorem liftedCandidate_relabel
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A B : Type} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Shannon.ProbDist A) :
    liftedCandidate Hfun (Shannon.relabelProb e q) =
      liftedCandidate Hfun q := by
  rw [liftedCandidate, liftedCandidate,
    augmented_relabel Hfun h, entropyNat_relabel]

theorem liftedCandidate_grouping
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A : Type} [Fintype A]
    {B : A → Type} [∀ a, Fintype (B a)]
    (p : Shannon.ProbDist A)
    (q : ∀ a, Shannon.ProbDist (B a)) :
    liftedCandidate Hfun (Shannon.composeProb p q) =
      liftedCandidate Hfun p +
        ∑ a, p a * liftedCandidate Hfun (q a) := by
  rw [liftedCandidate, augmented_grouping Hfun h,
    entropyNat_compose, liftedCandidate]
  simp only [liftedCandidate]
  have hsum :
      (∑ x : A,
          p x * (augmented Hfun (q x) - Shannon.entropyNat (q x))) =
        (∑ x : A, p x * augmented Hfun (q x)) -
          ∑ x : A, p x * Shannon.entropyNat (q x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsum]
  ring

theorem entropyNat_uniformPNat (n : ℕ+) :
    Shannon.entropyNat (Shannon.uniformPNat n) =
      Real.log (n : ℝ) := by
  classical
  unfold Shannon.entropyNat Shannon.uniformPNat
  have hn : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt n.2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Real.log_div (by norm_num) hn, Real.log_one]
  field_simp [hn]
  ring

theorem augmented_uniform_strictMono
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun) :
    StrictMono (Shannon.Apos (augmented Hfun)) := by
  have hcand :
      Monotone (Shannon.Apos (liftedCandidate Hfun)) :=
    Apos_monotone_weak (liftedCandidate Hfun)
      (liftedCandidate_nonnegative Hfun h)
      (liftedCandidate_relabel Hfun h)
      (liftedCandidate_grouping Hfun h)
  intro n m hnm
  have hc := hcand hnm.le
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast n.2
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast m.2
  have hcast : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  have hlog : Real.log (n : ℝ) < Real.log (m : ℝ) :=
    (Real.log_lt_log_iff hnpos hmpos).2 hcast
  change augmented Hfun (Shannon.uniformPNat n) <
    augmented Hfun (Shannon.uniformPNat m)
  have hnform :
      augmented Hfun (Shannon.uniformPNat n) =
        liftedCandidate Hfun (Shannon.uniformPNat n) +
          Shannon.entropyNat (Shannon.uniformPNat n) := by
    unfold liftedCandidate
    ring
  have hmform :
      augmented Hfun (Shannon.uniformPNat m) =
        liftedCandidate Hfun (Shannon.uniformPNat m) +
          Shannon.entropyNat (Shannon.uniformPNat m) := by
    unfold liftedCandidate
    ring
  rw [hnform, hmform, entropyNat_uniformPNat, entropyNat_uniformPNat]
  exact add_lt_add_of_le_of_lt hc hlog

/-! ## Binary continuity propagates to every simplex interior -/

def shannonBinaryProbInterior (t : Set.Ioo (0 : ℝ) 1) :
    Shannon.ProbDist Bool := by
  refine ⟨fun b => if b then t.1 else 1 - t.1, ?_⟩
  constructor
  · intro b
    cases b <;> simp [le_of_lt t.2.1, le_of_lt t.2.2]
  · simp

@[simp]
theorem shannonBinaryProbInterior_apply
    (t : Set.Ioo (0 : ℝ) 1) (b : Bool) :
    shannonBinaryProbInterior t b =
      if b then t.1 else 1 - t.1 := rfl

abbrev deletePoint {A : Type} (a₀ : A) := {a : A // a ≠ a₀}

theorem prob_lt_one_of_fullSupport_of_ne
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    {a₀ b : A} (hba : b ≠ a₀) :
    p a₀ < 1 := by
  have hsum := Shannon.prob_sum_eq_one p
  have hrest :
      p a₀ + p b ≤ ∑ a, p a := by
    have hsub :
        p b ≤ ∑ a ∈ Finset.univ.erase a₀, p a := by
      exact Finset.single_le_sum (fun a _ => Shannon.prob_nonneg p a)
        (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ b⟩)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a₀)]
    simpa [add_comm] using add_le_add_left hsub (p a₀)
  linarith [hp b]

def binaryParameter
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (a₀ b : A) (hba : b ≠ a₀) :
    Set.Ioo (0 : ℝ) 1 :=
  ⟨p a₀, hp a₀, prob_lt_one_of_fullSupport_of_ne p hp hba⟩

def deleteNormalize
    {A : Type} [Fintype A]
    (a₀ : A) (p : Shannon.ProbDist A)
    (ha₀ : p a₀ < 1) :
    Shannon.ProbDist (deletePoint a₀) := by
  let d : ℝ := 1 - p a₀
  have hd : 0 < d := sub_pos.mpr ha₀
  refine ⟨fun a => p a.1 / d, ?_⟩
  constructor
  · intro a
    exact div_nonneg (Shannon.prob_nonneg p a.1) hd.le
  · have hsplit :=
      Fintype.sum_eq_add_sum_subtype_ne (fun a : A => p a) a₀
    have htail : (∑ a : deletePoint a₀, p a.1) = d := by
      dsimp [d]
      linarith [Shannon.prob_sum_eq_one p, hsplit]
    calc
      (∑ a : deletePoint a₀, p a.1 / d) =
          (∑ a : deletePoint a₀, p a.1) / d := by
        rw [Finset.sum_div]
      _ = d / d := by rw [htail]
      _ = 1 := div_self (ne_of_gt hd)

@[simp]
theorem deleteNormalize_apply
    {A : Type} [Fintype A]
    (a₀ : A) (p : Shannon.ProbDist A)
    (ha₀ : p a₀ < 1) (a : deletePoint a₀) :
    deleteNormalize a₀ p ha₀ a = p a.1 / (1 - p a₀) := rfl

theorem deleteNormalize_fullSupport
    {A : Type} [Fintype A]
    (a₀ : A) (p : Shannon.ProbDist A)
    (hp : ∀ a, 0 < p a) (ha₀ : p a₀ < 1) :
    ∀ a, 0 < deleteNormalize a₀ p ha₀ a := by
  intro a
  rw [deleteNormalize_apply]
  exact div_pos (hp a.1) (sub_pos.mpr ha₀)

def splitFiber {A : Type} (a₀ : A) (b : Bool) : Type :=
  bif b then Unit else deletePoint a₀

instance instFintypeSplitFiber
    {A : Type} [Fintype A] (a₀ : A) (b : Bool) :
    Fintype (splitFiber a₀ b) := by
  cases b
  · change Fintype (deletePoint a₀)
    infer_instance
  · change Fintype Unit
    infer_instance

instance instSubsingletonSplitFiberTrue
    {A : Type} (a₀ : A) :
    Subsingleton (splitFiber a₀ true) := by
  change Subsingleton Unit
  infer_instance

def unitProb : Shannon.ProbDist Unit :=
  ⟨fun _ => 1, by simp [Shannon.IsProbDist]⟩

def splitInner
    {A : Type} [Fintype A]
    (a₀ : A) (p : Shannon.ProbDist A)
    (ha₀ : p a₀ < 1) :
    ∀ b, Shannon.ProbDist (splitFiber a₀ b) := by
  intro b
  cases b
  · exact deleteNormalize a₀ p ha₀
  · exact unitProb

@[simp]
theorem splitInner_false
    {A : Type} [Fintype A]
    (a₀ : A) (p : Shannon.ProbDist A) (ha₀ : p a₀ < 1) :
    splitInner a₀ p ha₀ false = deleteNormalize a₀ p ha₀ := by
  rfl

@[simp]
theorem splitInner_true
    {A : Type} [Fintype A]
    (a₀ : A) (p : Shannon.ProbDist A) (ha₀ : p a₀ < 1) :
    splitInner a₀ p ha₀ true = unitProb := by
  rfl

def pointSumEquiv {A : Type} (a₀ : A) :
    deletePoint a₀ ⊕ Unit ≃ A where
  toFun
    | Sum.inl a => a.1
    | Sum.inr _ => a₀
  invFun a :=
    if h : a = a₀ then Sum.inr () else Sum.inl ⟨a, h⟩
  left_inv x := by
    cases x with
    | inl a => simp [a.2]
    | inr a =>
        rcases a with ⟨⟩
        simp
  right_inv a := by
    by_cases h : a = a₀
    · simp [h]
    · simp [h]

def splitEquiv {A : Type} (a₀ : A) :
    ((b : Bool) × splitFiber a₀ b) ≃ A :=
  (Equiv.sumEquivSigmaBool (deletePoint a₀) Unit).symm.trans
    (pointSumEquiv a₀)

@[simp]
theorem splitEquiv_symm_apply_self
    {A : Type} (a₀ : A) :
    (splitEquiv a₀).symm a₀ = ⟨true, ()⟩ := by
  apply (splitEquiv a₀).injective
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem splitEquiv_symm_apply_ne
    {A : Type} (a₀ a : A) (h : a ≠ a₀) :
    (splitEquiv a₀).symm a = ⟨false, ⟨a, h⟩⟩ := by
  apply (splitEquiv a₀).injective
  rw [Equiv.apply_symm_apply]
  rfl

theorem relabel_split_compose_eq
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (a₀ b : A) (hba : b ≠ a₀) :
    Shannon.relabelProb (splitEquiv a₀)
      (Shannon.composeProb
        (shannonBinaryProbInterior (binaryParameter p hp a₀ b hba))
        (splitInner a₀ p
          (prob_lt_one_of_fullSupport_of_ne p hp hba))) = p := by
  classical
  ext a
  by_cases ha : a = a₀
  · subst a
    simp only [Shannon.relabelProb, Shannon.composeProb,
      shannonBinaryProbInterior_apply]
    rw [splitEquiv_symm_apply_self]
    simp [splitInner_true, unitProb, binaryParameter]
  · simp only [Shannon.relabelProb, Shannon.composeProb,
      shannonBinaryProbInterior_apply]
    rw [splitEquiv_symm_apply_ne a₀ a ha]
    simp [splitInner_false, binaryParameter, deleteNormalize_apply]
    have hden : 1 - p a₀ ≠ 0 :=
      ne_of_gt (sub_pos.mpr
        (prob_lt_one_of_fullSupport_of_ne p hp hba))
    field_simp [hden]

theorem grouping_split_formula
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a))
    (hsingleton :
      ∀ {S : Type} [Fintype S] [Subsingleton S]
        (r : Shannon.ProbDist S), G r = 0)
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (a₀ b : A) (hba : b ≠ a₀) :
    G p =
      G (shannonBinaryProbInterior (binaryParameter p hp a₀ b hba)) +
        (1 - p a₀) *
          G (deleteNormalize a₀ p
            (prob_lt_one_of_fullSupport_of_ne p hp hba)) := by
  classical
  let outer :=
    shannonBinaryProbInterior (binaryParameter p hp a₀ b hba)
  let inner :=
    splitInner a₀ p (prob_lt_one_of_fullSupport_of_ne p hp hba)
  have hrel :
      G p = G (Shannon.composeProb outer inner) := by
    calc
      G p = G (Shannon.relabelProb (splitEquiv a₀)
          (Shannon.composeProb outer inner)) := by
        rw [relabel_split_compose_eq p hp a₀ b hba]
      _ = G (Shannon.composeProb outer inner) := hrelabel _ _
  have hz : G (inner true) = 0 := hsingleton (inner true)
  rw [hrel, hgroup, Fintype.sum_bool, hz]
  simp [outer, inner, binaryParameter]
  exact Or.inl rfl

theorem probDist_tendsto_apply
    {A : Type} [Fintype A]
    {p : Shannon.ProbDist A} {q : ℕ → Shannon.ProbDist A}
    (hq : Tendsto q atTop (𝓝 p)) (a : A) :
    Tendsto (fun n => q n a) atTop (𝓝 (p a)) := by
  have hfun := tendsto_subtype_rng.mp hq
  exact tendsto_pi_nhds.mp hfun a

theorem binaryParameter_tendsto
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (q : ℕ → Shannon.ProbDist A) (hqfull : ∀ n a, 0 < q n a)
    (hq : Tendsto q atTop (𝓝 p))
    (a₀ b : A) (hba : b ≠ a₀) :
    Tendsto
      (fun n => binaryParameter (q n) (hqfull n) a₀ b hba)
      atTop (𝓝 (binaryParameter p hp a₀ b hba)) := by
  apply tendsto_subtype_rng.mpr
  exact probDist_tendsto_apply hq a₀

theorem deleteNormalize_tendsto
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (q : ℕ → Shannon.ProbDist A) (hqfull : ∀ n a, 0 < q n a)
    (hq : Tendsto q atTop (𝓝 p))
    (a₀ b : A) (hba : b ≠ a₀) :
    Tendsto
      (fun n =>
        deleteNormalize a₀ (q n)
          (prob_lt_one_of_fullSupport_of_ne (q n) (hqfull n) hba))
      atTop
      (𝓝 (deleteNormalize a₀ p
        (prob_lt_one_of_fullSupport_of_ne p hp hba))) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_pi_nhds.mpr
  intro a
  simp only [deleteNormalize_apply]
  have hnum := probDist_tendsto_apply hq a.1
  have hden :
      Tendsto (fun n : ℕ => 1 - q n a₀) atTop
        (𝓝 (1 - p a₀)) :=
    tendsto_const_nhds.sub (probDist_tendsto_apply hq a₀)
  exact hnum.div hden
    (ne_of_gt (sub_pos.mpr
      (prob_lt_one_of_fullSupport_of_ne p hp hba)))

/-- Binary interior continuity and grouping imply sequential continuity at
every full-support point of every finite simplex. -/
theorem sequentiallyContinuous_fullSupport_of_binary
    (G : {A : Type} → [Fintype A] → Shannon.ProbDist A → ℝ)
    (hrelabel :
      ∀ {A B : Type} [Fintype A] [Fintype B]
        (e : A ≃ B) (p : Shannon.ProbDist A),
        G (Shannon.relabelProb e p) = G p)
    (hgroup :
      ∀ {A : Type} [Fintype A]
        {B : A → Type} [∀ a, Fintype (B a)]
        (p : Shannon.ProbDist A)
        (q : ∀ a, Shannon.ProbDist (B a)),
        G (Shannon.composeProb p q) =
          G p + ∑ a, p a * G (q a))
    (hsingleton :
      ∀ {S : Type} [Fintype S] [Subsingleton S]
        (r : Shannon.ProbDist S), G r = 0)
    (hbinary :
      Continuous
        (fun t : Set.Ioo (0 : ℝ) 1 =>
          G (shannonBinaryProbInterior t)))
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (q : ℕ → Shannon.ProbDist A) (hqfull : ∀ n a, 0 < q n a)
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => G (q n)) atTop (𝓝 (G p)) := by
  classical
  have hcardpos : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr (Shannon.nonempty_of_probDist p)
  by_cases hcardone : Fintype.card A = 1
  · letI : Unique A :=
      Classical.choice
        (Fintype.card_eq_one_iff_nonempty_unique.mp hcardone)
    have hqn : ∀ n, G (q n) = 0 := fun n => hsingleton (q n)
    have hp0 : G p = 0 := hsingleton p
    simp [hqn, hp0]
  · have hcardgt : 1 < Fintype.card A := by omega
    letI : Nontrivial A :=
      Fintype.one_lt_card_iff_nontrivial.mp hcardgt
    obtain ⟨a₀, b, hab⟩ := exists_pair_ne A
    have hba : b ≠ a₀ := hab.symm
    let ptail :=
      deleteNormalize a₀ p
        (prob_lt_one_of_fullSupport_of_ne p hp hba)
    let qtail : ℕ → Shannon.ProbDist (deletePoint a₀) :=
      fun n =>
        deleteNormalize a₀ (q n)
          (prob_lt_one_of_fullSupport_of_ne (q n) (hqfull n) hba)
    have hptailfull : ∀ a, 0 < ptail a :=
      deleteNormalize_fullSupport a₀ p hp
        (prob_lt_one_of_fullSupport_of_ne p hp hba)
    have hqtailfull : ∀ n a, 0 < qtail n a := by
      intro n
      exact deleteNormalize_fullSupport a₀ (q n) (hqfull n)
        (prob_lt_one_of_fullSupport_of_ne (q n) (hqfull n) hba)
    have hqtail : Tendsto qtail atTop (𝓝 ptail) :=
      deleteNormalize_tendsto p hp q hqfull hq a₀ b hba
    have hcardtail :
        Fintype.card (deletePoint a₀) =
          Fintype.card A - 1 := by
      simp [deletePoint]
    have htailG :
        Tendsto (fun n => G (qtail n)) atTop (𝓝 (G ptail)) :=
      sequentiallyContinuous_fullSupport_of_binary
        G hrelabel hgroup hsingleton hbinary
        ptail hptailfull qtail hqtailfull hqtail
    have ht :=
      binaryParameter_tendsto p hp q hqfull hq a₀ b hba
    have hbin :
        Tendsto
          (fun n =>
            G (shannonBinaryProbInterior
              (binaryParameter (q n) (hqfull n) a₀ b hba)))
          atTop
          (𝓝 (G (shannonBinaryProbInterior
            (binaryParameter p hp a₀ b hba)))) :=
      hbinary.continuousAt.tendsto.comp ht
    have hscalar :
        Tendsto (fun n : ℕ => 1 - q n a₀) atTop
          (𝓝 (1 - p a₀)) :=
      tendsto_const_nhds.sub (probDist_tendsto_apply hq a₀)
    have hcombined := hbin.add (hscalar.mul htailG)
    have hformulaN :
        ∀ n,
          G (q n) =
            G (shannonBinaryProbInterior
              (binaryParameter (q n) (hqfull n) a₀ b hba)) +
              (1 - q n a₀) * G (qtail n) := by
      intro n
      exact grouping_split_formula G hrelabel hgroup hsingleton
        (q n) (hqfull n) a₀ b hba
    have hformulaP :
        G p =
          G (shannonBinaryProbInterior
            (binaryParameter p hp a₀ b hba)) +
            (1 - p a₀) * G ptail :=
      grouping_split_formula G hrelabel hgroup hsingleton
        p hp a₀ b hba
    convert hcombined using 1
    · funext n
      exact hformulaN n
    · rw [hformulaP]
termination_by Fintype.card A
decreasing_by
  rw [hcardtail]
  omega

theorem liftedCandidate_singleton_zero
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {S : Type} [Fintype S] [Subsingleton S]
    (p : Shannon.ProbDist S) :
    liftedCandidate Hfun p = 0 := by
  classical
  let s : S := Classical.choice (Shannon.nonempty_of_probDist p)
  letI : Unique S :=
    { default := s
      uniq := fun a => Subsingleton.elim _ _ }
  have hpone : p s = 1 := by
    have hsum := Shannon.prob_sum_eq_one p
    have huniv : (Finset.univ : Finset S) = {s} :=
      univ_eq_singleton_of_card_one s Fintype.card_unique
    rw [huniv] at hsum
    simpa using hsum
  have hlift :
      liftShannonProb p = Dist.pure (ULift.up s) := by
    ext x
    have hx : x = ULift.up s := Subsingleton.elim _ _
    subst x
    simp [hpone]
  letI : Nonempty (ULift.{u, 0} S) := ⟨ULift.up s⟩
  simp only [liftedCandidate, augmented]
  rw [hlift, h.pointMass_zero]
  ring

theorem liftedCandidate_binary_continuous
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun) :
    Continuous
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        liftedCandidate Hfun (shannonBinaryProbInterior t)) := by
  have hlift :
      ∀ t : Set.Ioo (0 : ℝ) 1,
        liftShannonProb (shannonBinaryProbInterior t) =
          faddeevBinaryDistInterior t := by
    intro t
    ext b
    rcases b with ⟨b⟩
    cases b <;> rfl
  have heq :
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        liftedCandidate Hfun (shannonBinaryProbInterior t)) =
      (fun t : Set.Ioo (0 : ℝ) 1 =>
        Hfun (faddeevBinaryDistInterior t)) := by
    funext t
    classical
    letI : Nonempty (ULift.{u, 0} Bool) := ⟨ULift.up false⟩
    simp only [liftedCandidate, augmented]
    rw [hlift]
    ring_nf
    congr
  rw [heq]
  exact h.binary_continuous

theorem liftedCandidate_sequentiallyContinuous_fullSupport
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (q : ℕ → Shannon.ProbDist A) (hqfull : ∀ n a, 0 < q n a)
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => liftedCandidate Hfun (q n))
      atTop (𝓝 (liftedCandidate Hfun p)) :=
  sequentiallyContinuous_fullSupport_of_binary
    (liftedCandidate Hfun)
    (liftedCandidate_relabel Hfun h)
    (liftedCandidate_grouping Hfun h)
    (liftedCandidate_singleton_zero Hfun h)
    (liftedCandidate_binary_continuous Hfun h)
    p hp q hqfull hq

theorem augmented_sequentiallyContinuous_fullSupport
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a)
    (q : ℕ → Shannon.ProbDist A) (hqfull : ∀ n a, 0 < q n a)
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun n => augmented Hfun (q n))
      atTop (𝓝 (augmented Hfun p)) := by
  have hcand :=
    liftedCandidate_sequentiallyContinuous_fullSupport
      Hfun h p hp q hqfull hq
  have hSh :=
    Shannon.continuous_entropyNat.continuousAt.tendsto.comp hq
  have hadd := hcand.add hSh
  convert hadd using 1
  · funext n
    change augmented Hfun (q n) =
      augmented Hfun (q n) - Shannon.entropyNat (q n) +
        Shannon.entropyNat (q n)
    ring
  · unfold liftedCandidate
    ring_nf

theorem augmentedShannonAxioms
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun) :
    Shannon.ShannonEntropyAxioms (augmented Hfun) where
  sequentiallyContinuous_fullSupport :=
    augmented_sequentiallyContinuous_fullSupport Hfun h
  uniformMonotone := augmented_uniform_strictMono Hfun h
  relabelInvariant := augmented_relabel Hfun h
  grouping := augmented_grouping Hfun h

/-! ## Shannon form and return to arbitrary universe/cardinality -/

theorem liftedCandidate_entropy_form_fullSupport
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun)
    {A : Type} [Fintype A]
    (p : Shannon.ProbDist A) (hp : ∀ a, 0 < p a) :
    liftedCandidate Hfun p =
      (Shannon.K (augmented Hfun) - 1) * Shannon.entropyNat p := by
  have hu :=
    Shannon.entropyNat_unique (augmented Hfun)
      (augmentedShannonAxioms Hfun h) p hp
  have haug :
      augmented Hfun p =
        Shannon.K (augmented Hfun) * Shannon.entropyNat p := by
    simpa [Shannon.entropyNat, mul_assoc, mul_left_comm, mul_comm] using hu
  unfold liftedCandidate
  rw [haug]
  ring

theorem faddeevScale_nonnegative
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun) :
    0 ≤ Shannon.K (augmented Hfun) - 1 := by
  let p : Shannon.ProbDist (Fin 2) := Shannon.uniformPNat 2
  have hp : ∀ a, 0 < p a := by
    intro a
    simp [p, Shannon.uniformPNat]
  have hform :=
    liftedCandidate_entropy_form_fullSupport Hfun h p hp
  have hnonneg := liftedCandidate_nonnegative Hfun h p
  have hent : Shannon.entropyNat p = Real.log 2 := by
    change
      Shannon.entropyNat (Shannon.uniformPNat (2 : ℕ+)) = Real.log 2
    exact entropyNat_uniformPNat 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [hent] at hform
  nlinarith

/-- Remove one universe lift from a distribution. -/
def lowerLiftedDist
    {A : Type} [Fintype A]
    (q : Dist (ULift.{u, 0} A)) :
    Shannon.ProbDist A := by
  refine ⟨fun a => q (ULift.up a), ?_⟩
  constructor
  · intro a
    exact q.nonneg _
  · have hsum :=
      (Equiv.ulift.{u, 0} (α := A)).sum_comp
        (fun a : A => q (ULift.up a))
    exact hsum.symm.trans q.sum_eq_one

@[simp]
theorem lowerLiftedDist_apply
    {A : Type} [Fintype A]
    (q : Dist (ULift.{u, 0} A)) (a : A) :
    lowerLiftedDist q a = q (ULift.up a) := rfl

@[simp]
theorem lift_lowerLiftedDist
    {A : Type} [Fintype A]
    (q : Dist (ULift.{u, 0} A)) :
    liftShannonProb (lowerLiftedDist q) = q := by
  ext a
  rcases a with ⟨a⟩
  rfl

theorem lowerLiftedDist_fullSupport
    {A : Type} [Fintype A]
    (q : Dist (ULift.{u, 0} A)) (hq : q.FullSupport) :
    ∀ a, 0 < lowerLiftedDist q a :=
  fun a => hq (ULift.up a)

theorem entropy_restrictToSupport
    {A : Type u} [Fintype A] [Nonempty A]
    (q : Dist A) :
    H(q.restrictToSupport) = H(q) := by
  classical
  unfold entropy
  change
    (∑ a : supportSubtype q, entropyTerm (q a.1)) =
      ∑ a : A, entropyTerm (q a)
  rw [← sum_supportSubtype_eq_sum_of_zero q
    (fun a : A => entropyTerm (q a))]
  intro a ha
  simp [ha]

/-- The lifted candidate is literally the original candidate on the lifted
distribution; this lemma hides irrelevant decidable-equality proofs. -/
theorem liftedCandidate_eq_Hfun_lift
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    {A : Type} [Fintype A] (p : Shannon.ProbDist A) :
    letI : Nonempty (ULift.{u, 0} A) :=
      Nonempty.map ULift.up (Shannon.nonempty_of_probDist p)
    liftedCandidate Hfun p = Hfun (liftShannonProb p) := by
  classical
  simp only [liftedCandidate, augmented]
  ring

/-- The exact finite Faddeev characterization used by the paper.  In
particular, the continuity hypothesis required here is only continuity of the
binary full-support family; continuity on every finite simplex was derived
above from grouping. -/
theorem finiteFaddeev_characterization
    (Hfun :
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A],
        Dist A → ℝ)
    (h : FiniteFaddeevStandardHypotheses Hfun) :
    ∃ alpha : ℝ, 0 ≤ alpha ∧
      ∀ {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
        (q : Dist A),
        Hfun q = alpha * H(q) := by
  let alpha := Shannon.K (augmented Hfun) - 1
  refine ⟨alpha, faddeevScale_nonnegative Hfun h, ?_⟩
  intro A _ _ _ q
  classical
  let r : Dist (supportSubtype q) := q.restrictToSupport
  letI smallDecidableEq :
      DecidableEq (Fin (Fintype.card (supportSubtype q))) :=
    genericClassicalDecidableEq
  let e :
      supportSubtype q ≃
        ULift.{u, 0} (Fin (Fintype.card (supportSubtype q))) :=
    (Fintype.equivFin (supportSubtype q)).trans
      (Equiv.ulift.{u, 0}).symm
  let s :
      Dist (ULift.{u, 0} (Fin (Fintype.card (supportSubtype q)))) :=
    Relabeling.relabelDist e r
  letI :
      Nonempty (ULift.{u, 0} (Fin (Fintype.card (supportSubtype q)))) :=
    Nonempty.map e (supportSubtype_nonempty q)
  let p : Shannon.ProbDist (Fin (Fintype.card (supportSubtype q))) :=
    lowerLiftedDist s
  have hsfull : s.FullSupport := by
    intro b
    change r (e.symm b) > 0
    exact Dist.restrictToSupport_fullSupport q (e.symm b)
  have hpfull : ∀ a, 0 < p a :=
    lowerLiftedDist_fullSupport s hsfull
  have hpform :=
    liftedCandidate_entropy_form_fullSupport Hfun h p hpfull
  have hcandidate : liftedCandidate Hfun p = Hfun s := by
    simp only [liftedCandidate, augmented]
    rw [lift_lowerLiftedDist]
    ring
  have hentropy : Shannon.entropyNat p = H(q) := by
    calc
      Shannon.entropyNat p = H(liftShannonProb.{u} p) :=
        (entropy_liftShannonProb p).symm
      _ = H(s) := by rw [lift_lowerLiftedDist]
      _ = H(r) := entropy_relabel e r
      _ = H(q) := entropy_restrictToSupport q
  calc
    Hfun q = Hfun r := h.support_restriction q
    _ = Hfun s := (relabel_invariant Hfun h e r).symm
    _ = liftedCandidate Hfun p := hcandidate.symm
    _ = alpha * Shannon.entropyNat p := hpform
    _ = alpha * H(q) := by rw [hentropy]

/-- A closed, executable witness for the last formerly external mathematical
interface. -/
theorem provedClassicalFaddeevTheoremAssumptions :
    ClassicalFaddeevTheoremAssumptions.{u} where
  of_standard_hypotheses := finiteFaddeev_characterization

end

end GenericFaddeev

end TraceableAgency
