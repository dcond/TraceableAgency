/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.External.HersteinMilnor
import TraceableAgency.Behaviour.MIPreference

/-!
# Mutual information as an affine utility on posterior laws

The Appendix-D conclusion is ordinal.  To align its cardinal scale with the
marked-terminal representative, this file supplies the canonical affine
representative on the already constructed posterior-law quotient: mutual
information itself.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

variable {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]

/-- Every distribution on the universe-polymorphic singleton has zero entropy. -/
theorem entropy_punitU (p : TraceableAgency.Dist PUnit.{u + 1}) :
    entropy p = 0 := by
  unfold entropy
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have h : p PUnit.unit = 1 := by
    have hp := p.sum_eq_one
    simp only [Finset.univ_unique, Finset.sum_singleton] at hp
    exact hp
  rw [h, entropyTerm_one]

/-- The universe-polymorphic uninformative channel has zero mutual information. -/
theorem mutualInfo_uninformativeChannelU
    (q : TraceableAgency.Dist A) :
    mutualInfo q (Channel.uninformativeChannelU A) = 0 := by
  unfold mutualInfo
  have hMarginal :
      entropy (Channel.outcomeMarginal (Channel.uninformativeChannelU A) q) = 0 :=
    entropy_punitU _
  have hRow : ∀ a : A, entropy ((Channel.uninformativeChannelU A) a) = 0 :=
    fun _ ↦ entropy_punitU _
  simp_rw [hMarginal, hRow, mul_zero, Finset.sum_const_zero, sub_zero]

/-- Mutual information descends to equality classes of posterior laws. -/
noncomputable def pureMIUtility (q : TraceableAgency.Dist A) :
    PosteriorLawMixtureSpace q → ℝ :=
  Quotient.lift
    (fun E ↦ @mutualInfo A E.OutcomeType _ E.outFintype q E.P)
    (by
      intro E G hsame
      rw [mutualInfo_entropyReductionExp,
        mutualInfo_entropyReductionExp,
        hsame entropy continuous_entropy])

@[simp]
theorem pureMIUtility_mk
    (q : TraceableAgency.Dist A) (E : FiniteExperimentOn A) :
    pureMIUtility q ⟦E⟧ =
      @mutualInfo A E.OutcomeType _ E.outFintype q E.P := rfl

/-- The numerical weak order represented by mutual information. -/
def pureMIRel (q : TraceableAgency.Dist A)
    (x y : PosteriorLawMixtureSpace q) : Prop :=
  pureMIUtility q x ≥ pureMIUtility q y

/-- Mutual information is affine under the quotient's public mixtures. -/
noncomputable def pureMIAffineUtilityRepresentation
    (q : TraceableAgency.Dist A) :
    AffineUtilityRepresentation
      (posteriorLawAbstractConvexMixtureSpace q) (pureMIRel q) where
  utility := pureMIUtility q
  represents := by
    intro x y
    rfl
  affine := by
    intro t x y
    induction x using Quotient.inductionOn with
    | _ E =>
      induction y using Quotient.inductionOn with
      | _ G =>
        letI : Fintype E.OutcomeType := E.outFintype
        letI : DecidableEq E.OutcomeType := E.outDecEq
        letI : Fintype G.OutcomeType := G.outFintype
        letI : DecidableEq G.OutcomeType := G.outDecEq
        change
          mutualInfo q (publicMixChannel t.1 t.2.1 t.2.2 E.P G.P) =
            t.1 * mutualInfo q E.P + (1 - t.1) * mutualInfo q G.P
        exact mutualInfo_publicMixChannel q t.1 t.2.1 t.2.2 E.P G.P

/-- On a genuinely uncertain full-support prior, the mutual-information
affine utility is nonconstant (full revelation versus no information). -/
theorem pureMIAffineUtility_nonconstant
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    [Nontrivial A] :
    ∃ x y : PosteriorLawMixtureSpace q,
      (pureMIAffineUtilityRepresentation q).utility x ≠
        (pureMIAffineUtilityRepresentation q).utility y := by
  refine
    ⟨⟦FiniteExperimentOn.ofChannel
        (Channel.idChannel : Channel A A)⟧,
      ⟦FiniteExperimentOn.ofChannel
        (Channel.uninformativeChannelU A)⟧, ?_⟩
  simp only [pureMIAffineUtilityRepresentation, pureMIUtility_mk]
  change mutualInfo q (Channel.idChannel : Channel A A) ≠
    mutualInfo q (Channel.uninformativeChannelU A)
  rw [mutualInfo_idChannel', mutualInfo_uninformativeChannelU]
  exact ne_of_gt (entropy_pos_of_fullSupport_nontrivial q hq)

end TraceTemperedChoiceVerification
