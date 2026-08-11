/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.BranchAggregation

/-!
# Finite posterior-law integral representation

This file proves the finite affine-extension step used after
Herstein--Milnor.  The proof is elementary and finite:

1. binary affinity implies affinity for every finite public mixture;
2. at a full-support prior, a small common mass `ε` embeds every posterior
   atom into the Bayes-plausible set;
3. averaging those embeddings gives the desired pointwise integral
   representation;
4. an arbitrary prior is reduced to its positive-support face.

No topological representation theorem or convention is used.
-/

namespace TraceableAgency

universe u

/-!
## Finite public mixtures
-/

/-- A prior-independent first-stage draw with law `w`. -/
noncomputable def finiteMixFirstStage
    {A I : Type u} [Fintype I] (w : Dist I) : Channel A I :=
  fun _ => w

theorem outcomeMarginal_finiteMixFirstStage
    {A I : Type u} [Fintype A] [Fintype I]
    (q : Dist A) (w : Dist I) (i : I) :
    (Channel.outcomeMarginal (finiteMixFirstStage (A := A) w) q) i = w i := by
  simp [finiteMixFirstStage, Channel.outcomeMarginal_apply, ← Finset.sum_mul,
    q.sum_eq_one]

theorem posterior_finiteMixFirstStage_of_pos
    {A I : Type u} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype I]
    (q : Dist A) (w : Dist I) (i : I) (hi : 0 < w i) :
    Channel.posterior (finiteMixFirstStage (A := A) w) q i = q := by
  ext a
  unfold Channel.posterior
  rw [dif_pos]
  · change q a * w i /
        (Channel.outcomeMarginal (finiteMixFirstStage (A := A) w) q) i = q a
    rw [outcomeMarginal_finiteMixFirstStage]
    exact mul_div_cancel_right₀ (q a) (ne_of_gt hi)
  · rw [outcomeMarginal_finiteMixFirstStage]
    exact hi

/-- The experiment obtained by first drawing `i ∼ w`, independently of the
action, and then running `E i`. -/
noncomputable def finitePublicMixExperiment
    {A I : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype I] [DecidableEq I]
    (w : Dist I) (E : I → FiniteExperimentOn A) :
    FiniteExperimentOn A := by
  letI : ∀ i, Fintype (E i).OutcomeType := fun i => (E i).outFintype
  letI : ∀ i, DecidableEq (E i).OutcomeType := fun i => (E i).outDecEq
  exact
    { OutcomeType := (i : I) × (E i).OutcomeType
      outFintype := inferInstance
      outDecEq := inferInstance
      channel :=
        seqComposeDep (finiteMixFirstStage (A := A) w)
          (fun i => (E i).OutcomeType) (fun i => (E i).P) }

/-- Posterior-law integral of a finite public mixture. -/
theorem posteriorLawIntegralExp_finitePublicMixExperiment
    {A I : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype I] [DecidableEq I]
    (q : Dist A) (w : Dist I) (E : I → FiniteExperimentOn A)
    (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (finitePublicMixExperiment w E) φ =
      ∑ i : I, w i * posteriorLawIntegralExp q (E i) φ := by
  classical
  letI : ∀ i, Fintype (E i).OutcomeType := fun i => (E i).outFintype
  letI : ∀ i, DecidableEq (E i).OutcomeType := fun i => (E i).outDecEq
  unfold finitePublicMixExperiment posteriorLawIntegralExp
  change posteriorLawIntegral q
      (seqComposeDep (finiteMixFirstStage (A := A) w)
        (fun i => (E i).OutcomeType) (fun i => (E i).P)) φ =
    ∑ i : I, w i * posteriorLawIntegral q (E i).P φ
  rw [posteriorLawIntegral_seqComposeDep_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [outcomeMarginal_finiteMixFirstStage]
  by_cases hi : 0 < w i
  · rw [posterior_finiteMixFirstStage_of_pos q w i hi]
  · have hwi : w i = 0 :=
      le_antisymm (le_of_not_gt hi) (w.nonneg i)
    simp [hwi]

/-- Delete one positive component and renormalize the remaining weights. -/
noncomputable def eraseNormalizeDist
    {I : Type u} [Fintype I] [DecidableEq I]
    (w : Dist I) (i : I) (hi : w i < 1) : Dist I where
  prob := fun j => if j = i then 0 else w j / (1 - w i)
  nonneg := by
    intro j
    split_ifs
    · exact le_rfl
    · exact div_nonneg (w.nonneg j) (by linarith)
  sum_eq_one := by
    have hden : 1 - w i ≠ 0 := ne_of_gt (by linarith)
    have hsumErase :
        ∑ j ∈ (Finset.univ.erase i), w j = 1 - w i := by
      have h :=
        Finset.sum_erase_add (Finset.univ : Finset I) (fun j => w j)
          (Finset.mem_univ i)
      rw [w.sum_eq_one] at h
      linarith
    calc
      (∑ j : I, if j = i then 0 else w j / (1 - w i)) =
          ∑ j ∈ (Finset.univ.erase i), w j / (1 - w i) := by
            calc
              (∑ j : I, if j = i then 0 else w j / (1 - w i)) =
                  ∑ j ∈ (Finset.univ.erase i),
                    (if j = i then 0 else w j / (1 - w i)) := by
                      symm
                      exact Finset.sum_erase (Finset.univ : Finset I) (by simp)
              _ = ∑ j ∈ (Finset.univ.erase i), w j / (1 - w i) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    simp [(Finset.mem_erase.mp hj).1]
      _ = (∑ j ∈ (Finset.univ.erase i), w j) / (1 - w i) := by
            rw [Finset.sum_div]
      _ = 1 := by rw [hsumErase, div_self hden]

@[simp] theorem eraseNormalizeDist_self
    {I : Type u} [Fintype I] [DecidableEq I]
    (w : Dist I) (i : I) (hi : w i < 1) :
    eraseNormalizeDist w i hi i = 0 := by
  simp [eraseNormalizeDist]

theorem eraseNormalizeDist_apply_ne
    {I : Type u} [Fintype I] [DecidableEq I]
    (w : Dist I) (i j : I) (hi : w i < 1) (hji : j ≠ i) :
    eraseNormalizeDist w i hi j = w j / (1 - w i) := by
  simp [eraseNormalizeDist, hji]

private noncomputable def finiteMixSupport
    {I : Type u} [Fintype I] [DecidableEq I] (w : Dist I) : Finset I :=
  Finset.univ.filter (fun i => w i ≠ 0)

/-- Binary posterior-law affinity implies affinity for an arbitrary finite
public mixture. -/
theorem affineValue_finitePublicMix
    {A I : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype I] [DecidableEq I]
    (q : Dist A) (v : FiniteExperimentOn A → ℝ)
    (hlaw :
      ∀ E E' : FiniteExperimentOn A,
        SamePosteriorLawExp q E E' → v E = v E')
    (hbinary :
      ∀ (t : ℝ), 0 < t → t < 1 →
        ∀ E_mix E₁ E₂ : FiniteExperimentOn A,
          (∀ φ : Dist A → ℝ, Continuous φ →
            posteriorLawIntegralExp q E_mix φ =
              t * posteriorLawIntegralExp q E₁ φ +
                (1 - t) * posteriorLawIntegralExp q E₂ φ) →
          v E_mix = t * v E₁ + (1 - t) * v E₂)
    (w : Dist I) (E : I → FiniteExperimentOn A) :
    v (finitePublicMixExperiment w E) =
      ∑ i : I, w i * v (E i) := by
  classical
  have hex : ∃ i : I, 0 < w i := by
    by_contra h
    push Not at h
    have hz : ∀ i : I, w i = 0 := fun i =>
      le_antisymm (h i) (w.nonneg i)
    have := w.sum_eq_one
    simp [hz] at this
  obtain ⟨i, hi⟩ := hex
  by_cases hiOne : w i = 1
  · have hw : w = Dist.pure i := by
      ext j
      by_cases hji : j = i
      · subst j
        simp [hiOne]
      · have hsumErase :
            ∑ k ∈ (Finset.univ.erase i), w k = 0 := by
          have h :=
            Finset.sum_erase_add (Finset.univ : Finset I) (fun k => w k)
              (Finset.mem_univ i)
          rw [w.sum_eq_one, hiOne] at h
          linarith
        have hjle : w j ≤ ∑ k ∈ (Finset.univ.erase i), w k :=
          Finset.single_le_sum
            (fun k _ => w.nonneg k)
            (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
        have hwj : w j = 0 :=
          le_antisymm (by linarith) (w.nonneg j)
        simp [Dist.pure_apply_ne i j hji, hwj]
    have hsame :
        SamePosteriorLawExp q (finitePublicMixExperiment w E) (E i) := by
      intro φ _hφ
      rw [posteriorLawIntegralExp_finitePublicMixExperiment]
      rw [hw]
      rw [Fintype.sum_eq_single i]
      · simp
      · intro j hji
        simp [Dist.pure_apply_ne i j hji]
    calc
      v (finitePublicMixExperiment w E) = v (E i) :=
        hlaw _ _ hsame
      _ = ∑ j : I, w j * v (E j) := by
        rw [hw, Fintype.sum_eq_single i]
        · simp
        · intro j hji
          simp [Dist.pure_apply_ne i j hji]
  · have hiLt : w i < 1 :=
      lt_of_le_of_ne (Dist.prob_le_one w i) hiOne
    let w' := eraseNormalizeDist w i hiLt
    have hdecomp :
        ∀ φ : Dist A → ℝ, Continuous φ →
          posteriorLawIntegralExp q (finitePublicMixExperiment w E) φ =
            w i * posteriorLawIntegralExp q (E i) φ +
              (1 - w i) *
                posteriorLawIntegralExp q (finitePublicMixExperiment w' E) φ := by
      intro φ _hφ
      rw [posteriorLawIntegralExp_finitePublicMixExperiment,
        posteriorLawIntegralExp_finitePublicMixExperiment]
      let x : I → ℝ := fun j => posteriorLawIntegralExp q (E j) φ
      have hden : 1 - w i ≠ 0 := ne_of_gt (by linarith)
      rw [← Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j => w j * x j) (Finset.mem_univ i)]
      rw [← Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j => w' j * x j) (Finset.mem_univ i)]
      have hwself : w' i = 0 := eraseNormalizeDist_self w i hiLt
      rw [hwself, zero_mul, add_zero]
      have hrest :
          ∑ j ∈ (Finset.univ.erase i), w' j * x j =
            (∑ j ∈ (Finset.univ.erase i), w j * x j) / (1 - w i) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [eraseNormalizeDist_apply_ne w i j hiLt hji]
        ring
      rw [hrest]
      field_simp [hden]
      ring
    have haff :=
      hbinary (w i) hi hiLt
        (finitePublicMixExperiment w E) (E i)
        (finitePublicMixExperiment w' E) hdecomp
    have hiMem : i ∈ finiteMixSupport w := by
      simp [finiteMixSupport, ne_of_gt hi]
    have hsub :
        finiteMixSupport w' ⊆ (finiteMixSupport w).erase i := by
      intro j hj
      have hwjne : w' j ≠ 0 := by
        simpa [finiteMixSupport] using hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hwjne (eraseNormalizeDist_self w i hiLt)
      have hwjne' : w j ≠ 0 := by
        intro hwj
        apply hwjne
        rw [eraseNormalizeDist_apply_ne w i j hiLt hji, hwj, zero_div]
      exact Finset.mem_erase.mpr
        ⟨hji, by simpa [finiteMixSupport] using hwjne'⟩
    have hcard :
        (finiteMixSupport w').card < (finiteMixSupport w).card :=
      lt_of_le_of_lt (Finset.card_le_card hsub)
        (Finset.card_erase_lt_of_mem hiMem)
    have hrec :=
      affineValue_finitePublicMix q v hlaw hbinary w' E
    rw [hrec] at haff
    have hsum :
        (∑ j : I, w j * v (E j)) =
          w i * v (E i) +
            (1 - w i) * ∑ j : I, w' j * v (E j) := by
      let x : I → ℝ := fun j => v (E j)
      have hden : 1 - w i ≠ 0 := ne_of_gt (by linarith)
      rw [← Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j => w j * x j) (Finset.mem_univ i)]
      rw [← Finset.sum_erase_add (Finset.univ : Finset I)
        (fun j => w' j * x j) (Finset.mem_univ i)]
      have hwself : w' i = 0 := eraseNormalizeDist_self w i hiLt
      rw [hwself, zero_mul, add_zero]
      have hrest :
          ∑ j ∈ (Finset.univ.erase i), w' j * x j =
            (∑ j ∈ (Finset.univ.erase i), w j * x j) / (1 - w i) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        rw [eraseNormalizeDist_apply_ne w i j hiLt hji]
        ring
      rw [hrest]
      field_simp [hden]
      ring
    rw [hsum]
    exact haff
termination_by (finiteMixSupport w).card
decreasing_by exact hcard

/-!
## Full-support affine extension
-/

/-- A single positive mass, depending only on a full-support prior, that is
dominated by that prior relative to every posterior point. -/
noncomputable def integralAtomMass
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) : ℝ :=
  Classical.choose (exists_positive_lower_bound_fullSupport q hq) / 2

private theorem integralAtomMass_pos
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    0 < integralAtomMass q hq := by
  let h := Classical.choose_spec (exists_positive_lower_bound_fullSupport q hq)
  unfold integralAtomMass
  linarith [h.1]

private theorem integralAtomMass_lt_one
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    integralAtomMass q hq < 1 := by
  let h := Classical.choose_spec (exists_positive_lower_bound_fullSupport q hq)
  let a : A := Classical.arbitrary A
  have hle := h.2 a
  have hqle := Dist.prob_le_one q a
  unfold integralAtomMass
  linarith [h.1]

private theorem integralAtomMass_mul_le
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A) (a : A) :
    integralAtomMass q hq * r a ≤ q a := by
  let h := Classical.choose_spec (exists_positive_lower_bound_fullSupport q hq)
  have heps : 0 ≤ integralAtomMass q hq :=
    le_of_lt (integralAtomMass_pos q hq)
  have hrle := Dist.prob_le_one r a
  have hmul : integralAtomMass q hq * r a ≤ integralAtomMass q hq :=
    mul_le_of_le_one_right heps hrle
  unfold integralAtomMass at hmul
  exact le_trans hmul (by linarith [h.1, h.2 a])

/-- Bayes-plausible perturbation of full revelation that puts the common mass
`ε(q)` on the prescribed posterior `r`. -/
noncomputable def posteriorAtomProbLaw
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A) :
    AtomicPosteriorProbLaw A where
  I := Option A
  instFintypeI := inferInstance
  instDecidableEqI := inferInstance
  mass := fun x => match x with
    | none => integralAtomMass q hq
    | some a => q a - integralAtomMass q hq * r a
  point := fun x => match x with
    | none => r
    | some a => Dist.pure a
  mass_nonneg := by
    intro x
    cases x with
    | none => exact le_of_lt (integralAtomMass_pos q hq)
    | some a => linarith [integralAtomMass_mul_le q hq r a]
  mass_sum := by
    rw [Fintype.sum_option]
    simp only
    rw [Finset.sum_sub_distrib, q.sum_eq_one, ← Finset.mul_sum, r.sum_eq_one]
    ring

theorem posteriorAtomProbLaw_barycenter
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A) (a : A) :
    (posteriorAtomProbLaw q hq r).barycenterCoord a = q a := by
  classical
  unfold AtomicPosteriorProbLaw.barycenterCoord posteriorAtomProbLaw
  rw [Fintype.sum_option]
  simp only
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hba
    rw [Dist.pure_apply_ne b a hba.symm, mul_zero]

/-- Experiment realizing `posteriorAtomProbLaw`. -/
noncomputable def posteriorAtomExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A) :
    FiniteExperimentOn A :=
  (posteriorAtomProbLaw q hq r).experimentOfPosteriorProbLaw
    q hq (posteriorAtomProbLaw_barycenter q hq r)

theorem posteriorLawIntegralExp_posteriorAtomExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (r : Dist A)
    (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (posteriorAtomExperiment q hq r) φ =
      integralAtomMass q hq * φ r +
        ∑ a : A,
          (q a - integralAtomMass q hq * r a) * φ (Dist.pure a) := by
  rw [posteriorAtomExperiment,
    AtomicPosteriorProbLaw.posteriorLawIntegralExp_experimentOfPosteriorProbLaw]
  unfold AtomicPosteriorProbLaw.eval posteriorAtomProbLaw
  rw [Fintype.sum_option]

/-- Atomic posterior law of full revelation. -/
noncomputable def revelationProbLaw
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : AtomicPosteriorProbLaw A where
  I := A
  instFintypeI := inferInstance
  instDecidableEqI := inferInstance
  mass := q
  point := Dist.pure
  mass_nonneg := q.nonneg
  mass_sum := q.sum_eq_one

theorem revelationProbLaw_barycenter
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (a : A) :
    (revelationProbLaw q).barycenterCoord a = q a := by
  classical
  unfold AtomicPosteriorProbLaw.barycenterCoord revelationProbLaw
  rw [Fintype.sum_eq_single a]
  · simp
  · intro b hba
    rw [Dist.pure_apply_ne b a hba.symm, mul_zero]

/-- A full-revelation experiment, expressed through the same atomic-law
realization used in the proof. -/
noncomputable def revelationExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    FiniteExperimentOn A :=
  (revelationProbLaw q).experimentOfPosteriorProbLaw
    q hq (revelationProbLaw_barycenter q)

theorem posteriorLawIntegralExp_revelationExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (revelationExperiment q hq) φ =
      ∑ a : A, q a * φ (Dist.pure a) := by
  rw [revelationExperiment,
    AtomicPosteriorProbLaw.posteriorLawIntegralExp_experimentOfPosteriorProbLaw]
  rfl

private theorem posterior_barycenter_sum
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] (q : Dist A) (P : Channel A O) (a : A) :
    ∑ o : O,
        (Channel.outcomeMarginal P q) o *
          (Channel.posterior P q o) a = q a := by
  calc
    (∑ o : O,
        (Channel.outcomeMarginal P q) o *
          (Channel.posterior P q o) a) =
        ∑ o : O, q a * P a o := by
          apply Finset.sum_congr rfl
          intro o _
          exact posterior_mul_marginal q P o a
    _ = q a := by rw [← Finset.mul_sum, (P a).sum_eq_one, mul_one]

/-- Averaging the atom experiments associated with the posteriors of `E`
equals a public mixture of `E` and full revelation. -/
theorem posteriorAtom_average_law
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (E : FiniteExperimentOn A)
    (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q
        (@finitePublicMixExperiment A E.OutcomeType inferInstance inferInstance
          inferInstance E.outFintype E.outDecEq (E.outcomeMarginal q)
            (fun o => posteriorAtomExperiment q hq (E.posterior q o))) φ =
      integralAtomMass q hq * posteriorLawIntegralExp q E φ +
        (1 - integralAtomMass q hq) *
          posteriorLawIntegralExp q (revelationExperiment q hq) φ := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  rw [posteriorLawIntegralExp_finitePublicMixExperiment]
  simp_rw [posteriorLawIntegralExp_posteriorAtomExperiment]
  rw [posteriorLawIntegralExp_revelationExperiment]
  unfold posteriorLawIntegralExp
  let ε := integralAtomMass q hq
  let m := E.outcomeMarginal q
  let r := E.posterior q
  let c : A → ℝ := fun a => φ (Dist.pure a)
  change
    (∑ o : E.OutcomeType,
      m o * (ε * φ (r o) + ∑ a : A, (q a - ε * r o a) * c a)) =
      ε * (∑ o : E.OutcomeType, m o * φ (r o)) +
        (1 - ε) * ∑ a : A, q a * c a
  have hsplit :
      ∀ o : E.OutcomeType,
        m o * (ε * φ (r o) + ∑ a : A, (q a - ε * r o a) * c a) =
          m o * (ε * φ (r o)) +
            m o * ∑ a : A, (q a - ε * r o a) * c a := by
    intro o
    ring
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ o : E.OutcomeType, m o * (ε * φ (r o))) =
        ε * ∑ o : E.OutcomeType, m o * φ (r o) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro o _
    ring
  rw [hfirst]
  congr 1
  calc
    (∑ o : E.OutcomeType,
        m o * ∑ a : A, (q a - ε * r o a) * c a) =
        ∑ a : A,
          (∑ o : E.OutcomeType, m o * (q a - ε * r o a)) * c a := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro o _
            ring
    _ = ∑ a : A, ((1 - ε) * q a) * c a := by
          apply Finset.sum_congr rfl
          intro a _
          congr 1
          calc
            (∑ o : E.OutcomeType, m o * (q a - ε * r o a)) =
                q a * (∑ o : E.OutcomeType, m o) -
                  ε * (∑ o : E.OutcomeType, m o * r o a) := by
                    have hpoint :
                        ∀ o : E.OutcomeType,
                          m o * (q a - ε * r o a) =
                            m o * q a - ε * (m o * r o a) := by
                      intro o
                      ring
                    simp_rw [hpoint]
                    rw [Finset.sum_sub_distrib]
                    congr 1
                    · rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro o _
                      ring
                    · rw [Finset.mul_sum]
            _ = (1 - ε) * q a := by
                  rw [m.sum_eq_one]
                  have hb := posterior_barycenter_sum q E.P a
                  change (∑ o : E.OutcomeType, m o * r o a) = q a at hb
                  rw [hb]
                  ring
    _ = (1 - ε) * ∑ a : A, q a * c a := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring

/-- Explicit representing test function at a full-support prior. -/
noncomputable def fullSupportMarginalValue
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (v : FiniteExperimentOn A → ℝ) (r : Dist A) : ℝ :=
  (v (posteriorAtomExperiment q hq r) -
      (1 - integralAtomMass q hq) * v (revelationExperiment q hq)) /
    integralAtomMass q hq

/-- The elementary finite affine-extension theorem at a full-support prior. -/
theorem posteriorValue_eq_integral_fullSupport
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport)
    (v : FiniteExperimentOn A → ℝ)
    (hlaw :
      ∀ E E' : FiniteExperimentOn A,
        SamePosteriorLawExp q E E' → v E = v E')
    (hbinary :
      ∀ (t : ℝ), 0 < t → t < 1 →
        ∀ E_mix E₁ E₂ : FiniteExperimentOn A,
          (∀ φ : Dist A → ℝ, Continuous φ →
            posteriorLawIntegralExp q E_mix φ =
              t * posteriorLawIntegralExp q E₁ φ +
                (1 - t) * posteriorLawIntegralExp q E₂ φ) →
          v E_mix = t * v E₁ + (1 - t) * v E₂)
    (E : FiniteExperimentOn A) :
    v E =
      posteriorLawIntegralExp q E (fullSupportMarginalValue q hq v) := by
  classical
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  let ε := integralAtomMass q hq
  let R := revelationExperiment q hq
  let atoms : E.OutcomeType → FiniteExperimentOn A :=
    fun o => posteriorAtomExperiment q hq (E.posterior q o)
  let M := finitePublicMixExperiment (E.outcomeMarginal q) atoms
  have hεpos : 0 < ε := integralAtomMass_pos q hq
  have hεlt : ε < 1 := integralAtomMass_lt_one q hq
  have hmix :
      ∀ φ : Dist A → ℝ, Continuous φ →
        posteriorLawIntegralExp q M φ =
          ε * posteriorLawIntegralExp q E φ +
            (1 - ε) * posteriorLawIntegralExp q R φ := by
    intro φ _hφ
    exact posteriorAtom_average_law q hq E φ
  have hMaff :
      v M = ε * v E + (1 - ε) * v R :=
    hbinary ε hεpos hεlt M E R hmix
  have hMfinite :
      v M =
        ∑ o : E.OutcomeType,
          (E.outcomeMarginal q) o * v (atoms o) :=
    affineValue_finitePublicMix q v hlaw hbinary
      (E.outcomeMarginal q) atoms
  unfold posteriorLawIntegralExp fullSupportMarginalValue
  change v E =
    ∑ o : E.OutcomeType, (E.outcomeMarginal q) o *
      ((v (atoms o) - (1 - ε) * v R) / ε)
  have hsum :
      (∑ o : E.OutcomeType, (E.outcomeMarginal q) o *
        ((v (atoms o) - (1 - ε) * v R) / ε)) =
      ((∑ o : E.OutcomeType,
          (E.outcomeMarginal q) o * v (atoms o)) -
        (1 - ε) * v R) / ε := by
    have hterm :
        ∀ o : E.OutcomeType,
          (E.outcomeMarginal q) o *
              ((v (atoms o) - (1 - ε) * v R) / ε) =
            (((E.outcomeMarginal q) o * v (atoms o)) -
              (E.outcomeMarginal q) o * ((1 - ε) * v R)) / ε := by
      intro o
      ring
    simp_rw [hterm]
    rw [← Finset.sum_div, Finset.sum_sub_distrib]
    congr 2
    rw [← Finset.sum_mul, (E.outcomeMarginal q).sum_eq_one, one_mul]
  rw [hsum, ← hMfinite, hMaff]
  field_simp [ne_of_gt hεpos]
  ring

/-!
## Reduction of an arbitrary prior to its positive-support face
-/

/-- Extend a bundled face experiment to the ambient action type. -/
noncomputable def supportExtendExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn (supportSubtype q)) :
    FiniteExperimentOn A := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  exact experimentOfChannel (supportExtendChannel q E.P)

/-- Posterior integration for a support-extended experiment is integration on
the support face followed by the canonical inclusion. -/
theorem posteriorLawIntegralExp_supportExtendExperiment
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn (supportSubtype q))
    (φ : Dist A → ℝ) :
    posteriorLawIntegralExp q (supportExtendExperiment q E) φ =
      posteriorLawIntegralExp q.restrictToSupport E
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel q))) := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  change posteriorLawIntegral q (supportExtendChannel q E.P) φ =
    posteriorLawIntegral q.restrictToSupport E.P
      (fun d => φ (Channel.actionPushforward d (supportIncludeKernel q)))
  rw [posteriorLawIntegral_restrictToSupport]
  rw [restrictToSupport_supportExtendChannel]

/-- Extending two equal face posterior laws preserves their equality in the
ambient simplex. -/
theorem samePosteriorLawExp_supportExtend
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E E' : FiniteExperimentOn (supportSubtype q))
    (hsame : SamePosteriorLawExp q.restrictToSupport E E') :
    SamePosteriorLawExp q
      (supportExtendExperiment q E) (supportExtendExperiment q E') := by
  intro φ _hφ
  rw [posteriorLawIntegralExp_supportExtendExperiment,
    posteriorLawIntegralExp_supportExtendExperiment]
  exact samePosteriorLawExp_all_test_functions
    q.restrictToSupport E E' hsame
      (fun d => φ (Channel.actionPushforward d (supportIncludeKernel q)))

/-- An ambient experiment and the extension of its support restriction have
the same posterior law at the ambient prior. -/
theorem samePosteriorLawExp_supportExtend_restrict
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) :
    SamePosteriorLawExp q E
      (supportExtendExperiment q (E.restrictToSupport q)) := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  intro φ _hφ
  change posteriorLawIntegral q E.P φ =
    posteriorLawIntegral q
      (supportExtendChannel q (Channel.restrictToSupport E.P q)) φ
  rw [posteriorLawIntegral_restrictToSupport E.P q φ]
  rw [posteriorLawIntegral_restrictToSupport
    (supportExtendChannel q (Channel.restrictToSupport E.P q)) q φ]
  rw [restrictToSupport_supportExtendChannel]

private theorem actionPushforward_pure_comp_integral
    {A B C : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype C] [DecidableEq C]
    (d : Dist A) (f : A → B) (g : B → C) :
    Channel.actionPushforward
        (Channel.actionPushforward d (fun a => Dist.pure (f a)))
        (fun b => Dist.pure (g b)) =
      Channel.actionPushforward d (fun a => Dist.pure (g (f a))) := by
  ext c
  show (∑ b : B,
      (Channel.actionPushforward d (fun a => Dist.pure (f a))) b *
        (Dist.pure (g b) : Dist C) c) =
    ∑ a : A, d a * (Dist.pure (g (f a)) : Dist C) c
  change (∑ b : B,
      (∑ a : A, d a * (Dist.pure (f a) : Dist B) b) *
        (Dist.pure (g b) : Dist C) c) =
    ∑ a : A, d a * (Dist.pure (g (f a)) : Dist C) c
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hc : c = g (f a)
  · subst c
    rw [Fintype.sum_eq_single (f a)]
    · simp
    · intro b hba
      simp [Dist.pure_apply_ne (f a) b hba]
  · rw [Dist.pure_apply_ne (g (f a)) c hc, mul_zero]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hba : b = f a
    · subst b
      simp [Dist.pure_apply_ne (g (f a)) c hc]
    · rw [Dist.pure_apply_ne (f a) b hba, mul_zero, zero_mul]

/-- Inclusion of a support-face distribution followed by support projection is
the identity. -/
theorem actionPushforward_include_project
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (d : Dist (supportSubtype q)) :
    Channel.actionPushforward
        (Channel.actionPushforward d (supportIncludeKernel q))
        (supportProjectKernel q) = d := by
  change Channel.actionPushforward
      (Channel.actionPushforward d (fun a => Dist.pure a.1))
      (fun a => Dist.pure (supportProject q a)) = d
  rw [actionPushforward_pure_comp_integral]
  have hk :
      (fun a : supportSubtype q => Dist.pure (supportProject q a.1)) =
        (fun a : supportSubtype q => Dist.pure a) := by
    funext a
    rw [supportProject_coe]
  rw [hk]
  ext b
  change (∑ a : supportSubtype q, d a * (Dist.pure a) b) = d b
  rw [Fintype.sum_eq_single b]
  · simp
  · intro a hab
    rw [Dist.pure_apply_ne a b hab.symm, mul_zero]

/-- Pull a test function on the support face back to the ambient simplex by
the deterministic support projection. -/
noncomputable def liftSupportTest
    {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) (φ : Dist (supportSubtype q) → ℝ) :
    Dist A → ℝ :=
  fun r => φ (Channel.actionPushforward r (supportProjectKernel q))

/-- Integrating the pulled-back test function over an ambient experiment is
the same as integrating the original function over its support restriction. -/
theorem posteriorLawIntegralExp_liftSupportTest
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A)
    (φ : Dist (supportSubtype q) → ℝ) :
    posteriorLawIntegralExp q E (liftSupportTest q φ) =
      posteriorLawIntegralExp q.restrictToSupport
        (E.restrictToSupport q) φ := by
  letI : Fintype E.OutcomeType := E.outFintype
  letI : DecidableEq E.OutcomeType := E.outDecEq
  change posteriorLawIntegral q E.P (liftSupportTest q φ) =
    posteriorLawIntegral q.restrictToSupport
      (Channel.restrictToSupport E.P q) φ
  rw [posteriorLawIntegral_restrictToSupport]
  congr 1
  funext d
  unfold liftSupportTest
  rw [actionPushforward_include_project]

/-- Value of a face experiment read through ambient support extension. -/
noncomputable def supportFaceValue
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    FiniteExperimentOn (supportSubtype q) → ℝ :=
  fun E => hV.V q (supportExtendExperiment q E)

/-- Representing function at an arbitrary prior, obtained by proving the
full-support theorem on its positive-support face and pulling it back by the
support projection. -/
noncomputable def finiteMarginalValue
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : Dist A → ℝ :=
  liftSupportTest q
    (fullSupportMarginalValue q.restrictToSupport
      (Dist.restrictToSupport_fullSupport q) (supportFaceValue hV q))

/-- Finite posterior-law integral representation, including boundary priors. -/
theorem posteriorValue_eq_integral_finite
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) :
    hV.V q E = posteriorLawIntegralExp q E (finiteMarginalValue hV q) := by
  classical
  let qs := q.restrictToSupport
  let v := supportFaceValue hV q
  have hlaw :
      ∀ G G' : FiniteExperimentOn (supportSubtype q),
        SamePosteriorLawExp qs G G' → v G = v G' := by
    intro G G' hsame
    exact hV.respects_same_posterior_law q _ _
      (samePosteriorLawExp_supportExtend q G G' hsame)
  have hbinary :
      ∀ (t : ℝ), 0 < t → t < 1 →
        ∀ Gmix G₁ G₂ : FiniteExperimentOn (supportSubtype q),
          (∀ φ : Dist (supportSubtype q) → ℝ, Continuous φ →
            posteriorLawIntegralExp qs Gmix φ =
              t * posteriorLawIntegralExp qs G₁ φ +
                (1 - t) * posteriorLawIntegralExp qs G₂ φ) →
          v Gmix = t * v G₁ + (1 - t) * v G₂ := by
    intro t ht0 ht1 Gmix G₁ G₂ hmix
    apply hV.affine_of_posteriorLawIntegral_mix q t ht0 ht1
      (supportExtendExperiment q Gmix)
      (supportExtendExperiment q G₁)
      (supportExtendExperiment q G₂)
    intro φ _hφ
    rw [posteriorLawIntegralExp_supportExtendExperiment,
      posteriorLawIntegralExp_supportExtendExperiment,
      posteriorLawIntegralExp_supportExtendExperiment]
    let Gpublic := hmPublicMixExperiment t ht0 ht1 G₁ G₂
    have hsame : SamePosteriorLawExp qs Gmix Gpublic := by
      intro ψ hψ
      rw [hm_posteriorLawIntegral_publicMixExperiment]
      exact hmix ψ hψ
    have hall :=
      samePosteriorLawExp_all_test_functions qs Gmix Gpublic hsame
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel q)))
    rw [hm_posteriorLawIntegral_publicMixExperiment] at hall
    exact hall
  have hface :=
    posteriorValue_eq_integral_fullSupport qs
      (Dist.restrictToSupport_fullSupport q) v hlaw hbinary
      (E.restrictToSupport q)
  calc
    hV.V q E =
        hV.V q (supportExtendExperiment q (E.restrictToSupport q)) :=
      hV.respects_same_posterior_law q _ _
        (samePosteriorLawExp_supportExtend_restrict q E)
    _ = v (E.restrictToSupport q) := rfl
    _ = posteriorLawIntegralExp qs (E.restrictToSupport q)
          (fullSupportMarginalValue qs
            (Dist.restrictToSupport_fullSupport q) v) := hface
    _ = posteriorLawIntegralExp q E (finiteMarginalValue hV q) := by
      symm
      exact posteriorLawIntegralExp_liftSupportTest q E
        (fullSupportMarginalValue qs
          (Dist.restrictToSupport_fullSupport q) v)

/-- The downstream package is now constructed entirely in Lean. -/
noncomputable def finitePosteriorIntegralRepresentation_of_finite :
    FinitePosteriorIntegralRepresentationAssumptions.{u} where
  marginalValue := fun _F hV {_A} [_] [_] [_] q =>
    finiteMarginalValue hV q
  value_eq_integral := by
    intro F hV A _ _ _ q E
    exact posteriorValue_eq_integral_finite hV q E

end TraceableAgency
