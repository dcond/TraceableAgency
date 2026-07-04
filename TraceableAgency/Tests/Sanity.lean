/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Info.Identities
import TraceableAgency.Behaviour.MIPreference
import TraceableAgency.Main

/-!
# Sanity Tests

Small finite-type tests and examples to verify correctness of definitions.
Uses Bool, Fin 2, Unit as test types.
-/

set_option linter.style.header false

namespace TraceableAgency.Tests

open TraceableAgency

/-!
## Distribution Tests
-/

section DistTests

/-- Dirac distribution at true gives probability 1 at true. -/
example : Dist.pure true true = 1 := by simp [Dist.pure_apply_self]

/-- Dirac distribution at true gives probability 0 at false. -/
example : Dist.pure true false = 0 := by
  simp [Dist.pure_apply_ne _ _ (by decide : false ≠ true)]

/-- Product distribution factorizes correctly. -/
example (q₁ : Dist Bool) (q₂ : Dist Bool) :
    prodDist q₁ q₂ (true, false) = q₁ true * q₂ false := by
  simp [prodDist_apply_pair]

/-- Block embedding inl preserves original distribution. -/
example (q : Dist Bool) :
    @inlDist Bool Bool _ _ q (Sum.inl true) = q true := by
  simp [inlDist_apply_inl]

/-- Block embedding inl gives zero on the other side. -/
example (q : Dist Bool) :
    @inlDist Bool Bool _ _ q (Sum.inr false) = 0 := by
  simp [inlDist_apply_inr]

/-- Block embedding inr preserves original distribution. -/
example (r : Dist Bool) :
    @inrDist Bool Bool _ _ r (Sum.inr true) = r true := by
  simp [inrDist_apply_inr]

/-- Block embedding inr gives zero on the other side. -/
example (r : Dist Bool) :
    @inrDist Bool Bool _ _ r (Sum.inl false) = 0 := by
  simp [inrDist_apply_inl]

end DistTests

/-!
## Channel Tests
-/

section ChannelTests

/-- Identity channel row at a is Dirac at a. -/
example (a : Bool) : Channel.idChannel a = Dist.pure a := rfl

/-- Identity channel gives 1 on diagonal. -/
example : Channel.idChannel true true = 1 := by
  simp [Channel.idChannel, Dist.pure_apply_self]

/-- Identity channel gives 0 off diagonal. -/
example : Channel.idChannel true false = 0 := by
  rw [Channel.idChannel, Dist.pure_apply_ne _ _ (by decide : false ≠ true)]

/-- Outcome marginal under identity equals the prior. -/
theorem outcomeMarginal_idChannel (q : Dist Bool) :
    Channel.outcomeMarginal Channel.idChannel q = q := by
  ext b
  simp only [Channel.outcomeMarginal_apply, Channel.idChannel, Dist.pure_apply]
  have h : ∀ a : Bool, q a * (if b = a then 1 else 0) = if a = b then q a else 0 := fun a => by
    by_cases hab : a = b
    · rw [hab, if_pos rfl, mul_one, if_pos rfl]
    · have hba : b ≠ a := fun h => hab h.symm
      rw [if_neg hba, mul_zero, if_neg hab]
  simp_rw [h, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Product channel factorizes correctly. -/
example (P₁ : Channel Bool Bool) (P₂ : Channel Bool Bool) (a₁ a₂ o₁ o₂ : Bool) :
    prodChannel P₁ P₂ (a₁, a₂) (o₁, o₂) = P₁ a₁ o₁ * P₂ a₂ o₂ := by
  simp [prodChannel_apply_pair]

/-- Block channel left embedding works correctly. -/
example (P Q : Channel Bool Bool) (a : Bool) (o : Bool) :
    blockChannel P Q (Sum.inl a) (Sum.inl o) = P a o := by
  simp [blockChannel_apply_inl_inl]

/-- Block channel cross-block is zero. -/
example (P Q : Channel Bool Bool) (a : Bool) (y : Bool) :
    blockChannel P Q (Sum.inl a) (Sum.inr y) = 0 := by
  simp [blockChannel_apply_inl_inr]

end ChannelTests

/-!
## Entropy Tests
-/

section EntropyTests

/-- Entropy of Dirac distribution is zero.
    H(δ_a) = -1*log(1) - 0*log(0)... = 0 -/
theorem entropy_pure (a : Bool) : H(Dist.pure a) = 0 := by
  unfold entropy
  have h : ∀ b : Bool, entropyTerm ((Dist.pure a) b) = 0 := fun b => by
    by_cases hab : b = a
    · rw [hab, Dist.pure_apply_self, entropyTerm_one]
    · rw [Dist.pure_apply_ne _ _ hab, entropyTerm_zero]
  simp_rw [h, Finset.sum_const_zero]

/-- Entropy is non-negative (using existing theorem). -/
example (q : Dist Bool) : 0 ≤ H(q) := entropy_nonneg q

end EntropyTests

/-!
## Mutual Information Tests
-/

section MITests

/-- Block MI identity: left embedding preserves MI. -/
example (q : Dist Bool) (P Q : Channel Bool Bool) :
    mutualInfo (inlDist q) (blockChannel P Q) = mutualInfo q P := by
  exact mutualInfo_block_inl P Q q

/-- Block MI identity: right embedding preserves MI. -/
example (r : Dist Bool) (P Q : Channel Bool Bool) :
    mutualInfo (inrDist r) (blockChannel P Q) = mutualInfo r Q := by
  exact mutualInfo_block_inr P Q r

/-- Product MI additivity. -/
example (q₁ q₂ : Dist Bool) (P₁ P₂ : Channel Bool Bool) :
    mutualInfo (prodDist q₁ q₂) (prodChannel P₁ P₂) =
    mutualInfo q₁ P₁ + mutualInfo q₂ P₂ := by
  exact mutualInfo_prod q₁ q₂ P₁ P₂

/-- MI of identity channel equals entropy.
    I(q, Id) = H(q) - Σ_a q(a) * H(δ_a) = H(q) - 0 = H(q) -/
theorem mutualInfo_idChannel (q : Dist Bool) :
    mutualInfo q Channel.idChannel = H(q) := by
  unfold mutualInfo
  rw [outcomeMarginal_idChannel]
  simp only [Channel.idChannel]
  have h : ∀ a, H(Dist.pure a) = 0 := entropy_pure
  simp_rw [h, mul_zero, Finset.sum_const_zero, sub_zero]

end MITests

/-!
## Benchmark Theorem Tests
-/

section BenchmarkTests

/-- MIPrefFamily satisfies A8 (already proved). -/
example : A8_IndependentBackgroundSeparability MIPrefFamily := MIPrefFamily_A8

/-- Block same-scale follows from MIRep. -/
example (F : PrefFamily) (h : MIRep F) : BlockSameScaleRep F := blockSameScaleRep_of_MIRep F h

/-- MIPrefFamily is MIRep. -/
example : MIRep MIPrefFamily := MIPrefFamily_is_MIRep

end BenchmarkTests

end TraceableAgency.Tests

/-!
## Posterior/Bayes Tests (outside namespace for #check)
-/

#check TraceableAgency.posterior_mul_marginal
#check @TraceableAgency.sigmaDist
#check @TraceableAgency.entropy_sigma_chain

/-!
## Axiom Structure Tests
-/

#check TraceableAgency.A1_WeakOrderLocalNontriviality
#check TraceableAgency.A2_Continuity
#check TraceableAgency.A3_BlockComparisonCoherence
#check TraceableAgency.A4_OutcomePostprocessingAversion
#check TraceableAgency.A5_ActionCoarseningAversion
#check TraceableAgency.A6_PublicCoinIndependence
#check TraceableAgency.A7_BranchwiseContinuationMonotonicity
#check TraceableAgency.A7Strong_BranchwiseContinuationMonotonicity
#check TraceableAgency.A7_of_A7Strong
#check TraceableAgency.A8_IndependentBackgroundSeparability
#check TraceableAgency.TraceAxioms

/-!
## Theorem Spine Statements (from Main.lean)
-/

#check TraceableAgency.SufficiencyStatement
#check TraceableAgency.BenchmarkStatement
#check TraceableAgency.BlockScaleStatement
#check TraceableAgency.MainCharacterization
#check TraceableAgency.MainCharacterizationWithMoreover
