/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.PreEntropyReady

/-!
# Canonical posterior-value representatives

Herstein--Milnor selects an affine utility separately on each full-support
posterior-law simplex.  The utility is unique only up to a positive scale.
This file removes that scale convention by dividing by the value of full
revelation.  At a boundary prior, the value is read on the positive support
face before applying the same normalization.

The resulting representative is canonical under support restriction and finite
relabeling.  No support/relabel coherence of arbitrarily selected marginal test
functions is assumed.
-/

namespace TraceableAgency

universe u

/-- Full-revelation anchor of a posterior-value representative. -/
noncomputable def posteriorFullRevelationValue
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  hV.V q (experimentOfChannel (Channel.idChannel : Channel A A))

/-- At a full-support non-singleton prior, full revelation has strictly
positive value relative to the zero-normalised no-information experiment. -/
theorem posteriorFullRevelationValue_pos
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    0 < posteriorFullRevelationValue hV q := by
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
  have hge :=
    (hV.represents_block_comparisons q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))).mp hstrict.1
  have hnrev : ¬
      hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) ≥
        hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) := by
    intro h
    exact hstrict.2
      ((hV.represents_block_comparisons q hq
        (experimentOfChannel (Channel.uninformativeChannelU A))
        (experimentOfChannel (Channel.idChannel : Channel A A))).mpr h)
  have hzero := hV.zero_normalized q hq
  dsimp [posteriorFullRevelationValue]
  rw [hzero] at hge hnrev
  linarith

/-- Convention-free value: use the raw HM utility at a full-support prior,
and its support-face utility at a boundary prior; divide by full revelation in
either case.  Singleton support faces carry the unique zero utility. -/
noncomputable def canonicalPosteriorValue
    {F : PrefFamily.{u}} (hV : PosteriorValueRepresentation F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (E : FiniteExperimentOn A) : ℝ := by
  classical
  exact if hq : q.FullSupport then
    if _hA : Subsingleton A then
      0
    else
      hV.V q E / posteriorFullRevelationValue hV q
  else
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    if _hS : Subsingleton (supportSubtype q) then
      0
    else
      hV.V q.restrictToSupport (E.restrictToSupport q) /
        posteriorFullRevelationValue hV q.restrictToSupport

/-- The convention-free posterior representative.  Boundary values are
defined on the positive support face, so arbitrary raw HM values at
non-full-support priors are discarded. -/
noncomputable def canonicalPosteriorValueRepresentation
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F) :
    PosteriorValueRepresentation F where
  V := canonicalPosteriorValue hV
  respects_same_posterior_law := by
    intro A _ _ _ q E E' hsame
    classical
    by_cases hq : q.FullSupport
    · by_cases hA : Subsingleton A
      · simp [canonicalPosteriorValue, hq, hA]
      · simp only [canonicalPosteriorValue, hq, hA, dite_false, dite_true]
        rw [hV.respects_same_posterior_law q E E' hsame]
    · letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      by_cases hS : Subsingleton (supportSubtype q)
      · simp [canonicalPosteriorValue, hq, hS]
      · have hrsame :=
          samePosteriorLawExp_restrictToSupport q E E' hsame
        simp only [canonicalPosteriorValue, hq, hS, dite_false, dite_true]
        rw [hV.respects_same_posterior_law q.restrictToSupport
          (E.restrictToSupport q) (E'.restrictToSupport q) hrsame]
  represents_block_comparisons := by
    intro A _ _ _ q hq E₁ E₂
    classical
    by_cases hA : Subsingleton A
    · haveI : Subsingleton A := hA
      have hzero₁ := branchValue_eq_zero_of_subsingleton F hV q hq E₁
      have hzero₂ := branchValue_eq_zero_of_subsingleton F hV q hq E₂
      have hpref :=
        hV.represents_block_comparisons q hq E₁ E₂
      simp [canonicalPosteriorValue, hq, hA, hzero₁, hzero₂] at hpref ⊢
      exact hpref
    · have hden := posteriorFullRevelationValue_pos hax hV q hq hA
      have hpref := hV.represents_block_comparisons q hq E₁ E₂
      simp only [canonicalPosteriorValue, hq, hA, dite_false, dite_true]
      rw [hpref]
      exact (div_le_div_iff_of_pos_right hden).symm
  affine_of_posteriorLawIntegral_mix := by
    intro A _ _ _ q t ht0 ht1 E_mix E₁ E₂ hmix
    classical
    by_cases hq : q.FullSupport
    · by_cases hA : Subsingleton A
      · simp [canonicalPosteriorValue, hq, hA]
      · rw [show canonicalPosteriorValue hV q E_mix =
            hV.V q E_mix / posteriorFullRevelationValue hV q by
            simp [canonicalPosteriorValue, hq, hA]]
        rw [show canonicalPosteriorValue hV q E₁ =
            hV.V q E₁ / posteriorFullRevelationValue hV q by
            simp [canonicalPosteriorValue, hq, hA]]
        rw [show canonicalPosteriorValue hV q E₂ =
            hV.V q E₂ / posteriorFullRevelationValue hV q by
            simp [canonicalPosteriorValue, hq, hA]]
        rw [hV.affine_of_posteriorLawIntegral_mix
          q t ht0 ht1 E_mix E₁ E₂ hmix]
        ring
    · letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
      by_cases hS : Subsingleton (supportSubtype q)
      · simp [canonicalPosteriorValue, hq, hS]
      · have hmixSupport :=
          posteriorLawIntegralMix_restrictToSupport
            q t ht0 ht1 E_mix E₁ E₂ hmix
        rw [show canonicalPosteriorValue hV q E_mix =
            hV.V q.restrictToSupport (E_mix.restrictToSupport q) /
              posteriorFullRevelationValue hV q.restrictToSupport by
            simp [canonicalPosteriorValue, hq, hS]]
        rw [show canonicalPosteriorValue hV q E₁ =
            hV.V q.restrictToSupport (E₁.restrictToSupport q) /
              posteriorFullRevelationValue hV q.restrictToSupport by
            simp [canonicalPosteriorValue, hq, hS]]
        rw [show canonicalPosteriorValue hV q E₂ =
            hV.V q.restrictToSupport (E₂.restrictToSupport q) /
              posteriorFullRevelationValue hV q.restrictToSupport by
            simp [canonicalPosteriorValue, hq, hS]]
        rw [hV.affine_of_posteriorLawIntegral_mix
          q.restrictToSupport t ht0 ht1
            (E_mix.restrictToSupport q)
            (E₁.restrictToSupport q)
            (E₂.restrictToSupport q)
            hmixSupport]
        ring
  zero_normalized := by
    intro A _ _ _ q hq
    classical
    by_cases hA : Subsingleton A
    · simp [canonicalPosteriorValue, hq, hA]
    · simp [canonicalPosteriorValue, hq, hA, hV.zero_normalized q hq]

/-- An equivalence carries the positive support of a relabelled prior back to
the original positive support. -/
noncomputable def canonicalRelabelSupportEquiv
    {A B : Type u} [Fintype A] [Fintype B]
    (e : A ≃ B) (q : Dist A) :
    supportSubtype (Relabeling.relabelDist e q) ≃ supportSubtype q where
  toFun b := ⟨e.symm b.1, by simpa using b.2⟩
  invFun a := ⟨e a.1, by simpa using a.2⟩
  left_inv b := by apply Subtype.ext; simp
  right_inv a := by apply Subtype.ext; simp

/-- Restriction of a relabelled prior is the relabelling of the restricted
prior by the induced support equivalence. -/
theorem canonical_restrictToSupport_relabelDist
    {A B : Type u} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B]
    (e : A ≃ B) (q : Dist A) :
    (Relabeling.relabelDist e q).restrictToSupport =
      Relabeling.relabelDist (canonicalRelabelSupportEquiv e q).symm
        q.restrictToSupport := by
  ext b
  change q (e.symm b.1) = q ((canonicalRelabelSupportEquiv e q) b).1
  rfl

/-- Restricting a relabelled channel agrees with relabelling the restricted
channel on the induced support equivalence. -/
theorem canonical_restrictToSupport_relabelChannel
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y) (q : Dist A) (P : Channel A O) :
    Channel.restrictToSupport (Relabeling.relabelChannel eA eO P)
        (Relabeling.relabelDist eA q) =
      Relabeling.relabelChannel (canonicalRelabelSupportEquiv eA q).symm eO
        (Channel.restrictToSupport P q) := by
  ext b y
  rfl

/-- A full-support type is equivalent to its positive support. -/
noncomputable def canonicalFullSupportRestrictEquiv
    {A : Type u} [Fintype A] (q : Dist A) (hq : q.FullSupport) :
    supportSubtype q ≃ A where
  toFun a := a.1
  invFun a := ⟨a, hq a⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv _ := rfl

/-- Full-support restriction is relabelling along the canonical support
equivalence. -/
theorem canonical_restrictToSupport_fullSupport_eq_relabel
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) :
    q.restrictToSupport =
      Relabeling.relabelDist (canonicalFullSupportRestrictEquiv q hq).symm q := by
  ext a
  simp [Dist.restrictToSupport_apply, Relabeling.relabelDist,
    canonicalFullSupportRestrictEquiv]

/-- Full-support channel restriction is action relabelling along the canonical
support equivalence. -/
theorem canonical_channel_restrictToSupport_fullSupport_eq_relabel
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    Channel.restrictToSupport P q =
      Relabeling.relabelChannel
        (canonicalFullSupportRestrictEquiv q hq).symm (Equiv.refl O) P := by
  ext a o
  rfl

/-- Full-revelation normalization cancels the unique positive scalar between
raw HM representatives on relabelled full-support simplexes. -/
theorem canonicalPosteriorValue_relabel_fullSupport
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (hq : q.FullSupport) (P : Channel A O) :
    canonicalPosteriorValue hV (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      canonicalPosteriorValue hV q (experimentOfChannel P) := by
  classical
  have hq' := Relabeling.relabelDist_fullSupport eA q hq
  by_cases hA : Subsingleton A
  · have hB : Subsingleton B :=
      ⟨fun b b' => eA.symm.injective
        (Subsingleton.elim (eA.symm b) (eA.symm b'))⟩
    simp [canonicalPosteriorValue, hq, hq', hA, hB]
  · have hB : ¬ Subsingleton B := by
      intro h
      apply hA
      exact ⟨fun a a' => eA.injective (Subsingleton.elim (eA a) (eA a'))⟩
    rcases posteriorValue_relabel_positiveScalar_fullSupport
        hax hV classicalFiniteAffineUtilityUniquenessAssumptions
        eA q hq hA with ⟨c, hc, hscalar⟩
    have hnum := hscalar eO P
    have hid :
        Relabeling.relabelChannel eA eA
            (Channel.idChannel : Channel A A) =
          (Channel.idChannel : Channel B B) := by
      funext b
      ext b'
      rw [Relabeling.relabelChannel_apply]
      simp only [Channel.idChannel]
      by_cases hbb : b' = b
      · subst hbb
        rw [Dist.pure_apply_self, Dist.pure_apply_self]
      · rw [Dist.pure_apply_ne (eA.symm b) (eA.symm b')
            (fun h => hbb (eA.symm.injective h)),
          Dist.pure_apply_ne b b' hbb]
    have hdenRaw := hscalar eA (Channel.idChannel : Channel A A)
    have hden :
        posteriorFullRevelationValue hV (Relabeling.relabelDist eA q) =
          c * posteriorFullRevelationValue hV q := by
      simpa [posteriorFullRevelationValue, hid] using hdenRaw
    have hcne : c ≠ 0 := ne_of_gt hc
    have hqden : posteriorFullRevelationValue hV q ≠ 0 :=
      ne_of_gt (posteriorFullRevelationValue_pos hax hV q hq hA)
    simp only [canonicalPosteriorValue, hq, hq', hA, hB,
      dite_false, dite_true]
    rw [hnum, hden]
    field_simp [hcne, hqden]

/-- The canonical value agrees exactly with its positive-support reading. -/
theorem canonicalPosteriorValue_supportFace
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
    canonicalPosteriorValue hV q (experimentOfChannel P) =
      canonicalPosteriorValue hV q.restrictToSupport
        (experimentOfChannel (Channel.restrictToSupport P q)) := by
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  classical
  by_cases hq : q.FullSupport
  · let e : A ≃ supportSubtype q :=
      (canonicalFullSupportRestrictEquiv q hq).symm
    have hdist : q.restrictToSupport = Relabeling.relabelDist e q := by
      simpa [e] using
        canonical_restrictToSupport_fullSupport_eq_relabel q hq
    have hchan :
        Channel.restrictToSupport P q =
          Relabeling.relabelChannel e (Equiv.refl O) P := by
      simpa [e] using
        canonical_channel_restrictToSupport_fullSupport_eq_relabel q hq P
    rw [hdist, hchan]
    exact (canonicalPosteriorValue_relabel_fullSupport
      hax hV e (Equiv.refl O) q hq P).symm
  · have hqs : q.restrictToSupport.FullSupport :=
      Dist.restrictToSupport_fullSupport q
    have hE :
        (experimentOfChannel P).restrictToSupport q =
          experimentOfChannel (Channel.restrictToSupport P q) := rfl
    by_cases hS : Subsingleton (supportSubtype q)
    · simp [canonicalPosteriorValue, hq, hqs, hS, hE]
    · simp [canonicalPosteriorValue, hq, hqs, hS, hE]

/-- The canonical posterior value is exactly natural under simultaneous finite
action and outcome relabelling, at arbitrary (including boundary) priors. -/
theorem canonicalPosteriorValue_relabel
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hV : PosteriorValueRepresentation F)
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (eA : A ≃ B) (eO : O ≃ Y)
    (q : Dist A) (P : Channel A O) :
    canonicalPosteriorValue hV (Relabeling.relabelDist eA q)
        (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
      canonicalPosteriorValue hV q (experimentOfChannel P) := by
  classical
  letI : Nonempty (supportSubtype q) := supportSubtype_nonempty q
  letI : Nonempty (supportSubtype (Relabeling.relabelDist eA q)) :=
    supportSubtype_nonempty _
  let es : supportSubtype q ≃
      supportSubtype (Relabeling.relabelDist eA q) :=
    (canonicalRelabelSupportEquiv eA q).symm
  have hdist :
      (Relabeling.relabelDist eA q).restrictToSupport =
        Relabeling.relabelDist es q.restrictToSupport := by
    simpa [es] using canonical_restrictToSupport_relabelDist eA q
  have hchan :
      Channel.restrictToSupport (Relabeling.relabelChannel eA eO P)
          (Relabeling.relabelDist eA q) =
        Relabeling.relabelChannel es eO (Channel.restrictToSupport P q) := by
    simpa [es] using
      canonical_restrictToSupport_relabelChannel eA eO q P
  rw [canonicalPosteriorValue_supportFace hax hV
      (Relabeling.relabelDist eA q) (Relabeling.relabelChannel eA eO P)]
  rw [canonicalPosteriorValue_supportFace hax hV q P]
  rw [hdist, hchan]
  exact canonicalPosteriorValue_relabel_fullSupport
    hax hV es eO q.restrictToSupport
      (Dist.restrictToSupport_fullSupport q)
      (Channel.restrictToSupport P q)

/-!
## Relabelling of signed posterior-law tangents

These finite-dimensional lemmas avoid choosing relabel-natural representing
test functions. An affine extension may be arbitrary away from the feasible
posterior-law polytope, but its value on an atomic tangent is fixed by feasible
differences. Relabelling therefore commutes with the linear part on exactly the
tangent domain used by branch aggregation.
-/

/-- Push a signed posterior law through an action equivalence. -/
noncomputable def relabelPosteriorLawSigned
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (η : PosteriorLawSigned A) :
    PosteriorLawSigned B :=
  fun ψ => η (fun d => ψ (Relabeling.relabelDist e d))

/-- Relabelling preserves finite atomic-linearity. -/
noncomputable def PosteriorLawSigned.AtomicLinear.relabel
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) {η : PosteriorLawSigned A}
    (hη : PosteriorLawSigned.AtomicLinear η) :
    PosteriorLawSigned.AtomicLinear (relabelPosteriorLawSigned e η) where
  witness := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    exact
      { I := hη.witness.I
        instFintypeI := inferInstance
        instDecidableEqI := inferInstance
        weight := hη.witness.weight
        point := fun i => Relabeling.relabelDist e (hη.witness.point i) }
  eval_eq := by
    letI : Fintype hη.witness.I := hη.witness.instFintypeI
    letI : DecidableEq hη.witness.I := hη.witness.instDecidableEqI
    funext ψ
    have h := congrFun hη.eval_eq
      (fun d => ψ (Relabeling.relabelDist e d))
    rw [AtomicPosteriorSignedLaw.eval_apply] at h
    exact h

/-- Relabelling preserves zero mass and zero barycentre. -/
theorem PosteriorLawTangent.relabel
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) {η : PosteriorLawSigned A}
    (hη : PosteriorLawTangent η) :
    PosteriorLawTangent (relabelPosteriorLawSigned e η) := by
  constructor
  · exact hη.1
  · intro b
    change η (fun d => (Relabeling.relabelDist e d) b) = 0
    simpa [Relabeling.relabelDist_apply] using hη.2 (e.symm b)

/-- The affine linear part on atomic tangents is relabel-natural whenever the
selected value itself is relabel-natural. -/
theorem affineLinearPart_relabel_atomicTangent
    {F : PrefFamily.{u}}
    (hlin : FiniteAffineLinearPartAssumptions.{u})
    (hV : PosteriorValueRepresentation F)
    (hrelab :
      ∀ {A B O Y : Type u}
        [Fintype A] [DecidableEq A] [Nonempty A]
        [Fintype B] [DecidableEq B] [Nonempty B]
        [Fintype O] [DecidableEq O]
        [Fintype Y] [DecidableEq Y]
        (eA : A ≃ B) (eO : O ≃ Y)
        (q : Dist A) (P : Channel A O),
        hV.V (Relabeling.relabelDist eA q)
            (experimentOfChannel (Relabeling.relabelChannel eA eO P)) =
          hV.V q (experimentOfChannel P))
    {A B : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (s : Dist A) (hs : s.FullSupport)
    (η : PosteriorLawSigned A)
    (hηatomic : PosteriorLawSigned.AtomicLinear η)
    (hηtan : PosteriorLawTangent η) :
    hlin.linearPart F hV (Relabeling.relabelDist e s)
        (relabelPosteriorLawSigned e η) =
      hlin.linearPart F hV s η := by
  classical
  by_cases hηzero : η = ((fun _ => 0) : PosteriorLawSigned A)
  · have hrelzero :
        relabelPosteriorLawSigned e η =
          ((fun _ => 0) : PosteriorLawSigned B) := by
        funext ψ
        simp [relabelPosteriorLawSigned, hηzero]
    rw [hrelzero, hηzero]
    rw [linearPart_zero hlin F hV, linearPart_zero hlin F hV]
  · rcases
      commonOutcomeAtomicLinearTangentRealization_of_atomicLinearSpanning
        (atomicLinearTangentSpanning_of_atomic
          finiteAtomicPosteriorTangentSpanning)
        s hs η hηatomic hηtan hηzero with
      ⟨t, ht, O, hO, hOdec, P, R, hreal⟩
    letI : Fintype O := hO
    letI : DecidableEq O := hOdec
    let P' : Channel B O :=
      Relabeling.relabelChannel e (Equiv.refl O) P
    let R' : Channel B O :=
      Relabeling.relabelChannel e (Equiv.refl O) R
    have hreal' :
        ∀ ψ : Dist B → ℝ,
          relabelPosteriorLawSigned e η ψ =
            t * posteriorLawDifferenceExp (Relabeling.relabelDist e s)
              (experimentOfChannel P') (experimentOfChannel R') ψ := by
      intro ψ
      change η (fun d => ψ (Relabeling.relabelDist e d)) = _
      rw [hreal]
      simp only [posteriorLawDifferenceExp,
        posteriorLawIntegralExp_experimentOfChannel]
      rw [posteriorLawIntegral_relabelChannel e (Equiv.refl O) s P ψ]
      rw [posteriorLawIntegral_relabelChannel e (Equiv.refl O) s R ψ]
    have hleft :
        hlin.linearPart F hV (Relabeling.relabelDist e s)
            (relabelPosteriorLawSigned e η) =
          t * (hV.V (Relabeling.relabelDist e s)
              (experimentOfChannel P') -
            hV.V (Relabeling.relabelDist e s)
              (experimentOfChannel R')) := by
      calc
        hlin.linearPart F hV (Relabeling.relabelDist e s)
            (relabelPosteriorLawSigned e η) =
            hlin.linearPart F hV (Relabeling.relabelDist e s)
              (posteriorLawSignedSMul t
                (posteriorLawDifferenceExp (Relabeling.relabelDist e s)
                  (experimentOfChannel P') (experimentOfChannel R'))) := by
              apply hlin.linearPart_ext
              intro ψ
              exact hreal' ψ
        _ = t * hlin.linearPart F hV (Relabeling.relabelDist e s)
              (posteriorLawDifferenceExp (Relabeling.relabelDist e s)
                (experimentOfChannel P') (experimentOfChannel R')) := by
              rw [hlin.linearPart_smul]
        _ = t * (hV.V (Relabeling.relabelDist e s)
              (experimentOfChannel P') -
            hV.V (Relabeling.relabelDist e s)
              (experimentOfChannel R')) := by
              rw [← hlin.value_difference]
    have hright :
        hlin.linearPart F hV s η =
          t * (hV.V s (experimentOfChannel P) -
            hV.V s (experimentOfChannel R)) := by
      calc
        hlin.linearPart F hV s η =
            hlin.linearPart F hV s
              (posteriorLawSignedSMul t
                (posteriorLawDifferenceExp s
                  (experimentOfChannel P) (experimentOfChannel R))) := by
              apply hlin.linearPart_ext
              intro φ
              exact hreal φ
        _ = t * hlin.linearPart F hV s
              (posteriorLawDifferenceExp s
                (experimentOfChannel P) (experimentOfChannel R)) := by
              rw [hlin.linearPart_smul]
        _ = t * (hV.V s (experimentOfChannel P) -
            hV.V s (experimentOfChannel R)) := by
              rw [← hlin.value_difference]
    rw [hleft, hright]
    rw [show hV.V (Relabeling.relabelDist e s)
          (experimentOfChannel P') =
        hV.V s (experimentOfChannel P) from
      hrelab e (Equiv.refl O) s P]
    rw [show hV.V (Relabeling.relabelDist e s)
          (experimentOfChannel R') =
        hV.V s (experimentOfChannel R) from
      hrelab e (Equiv.refl O) s R]

end TraceableAgency
