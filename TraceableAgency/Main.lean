/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Behaviour.Axioms
import TraceableAgency.Behaviour.MIPreference
import TraceableAgency.Basic.Blocks
import TraceableAgency.Info.Identities

/-!
# Main Theorem Statement and Spine

The main result (Theorem 1 in empowerment_v5.tex, lines 770-787):
A preference family satisfies axioms A1-A7 if and only if it is represented
by mutual information.

Moreover, under these conditions, block-supported cross-channel comparisons
are on the same scale.

This file defines:
- MIRep (already in MIPreference.lean)
- BlockSameScaleRep
- MainCharacterization
- MainCharacterizationWithMoreover
- SufficiencyStatement, BenchmarkStatement, BlockScaleStatement
- main_characterization_from_spine (logical assembly)
- TheoremSpinePackage
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-!
## Block Same-Scale Representation

Paper "moreover" clause (lines 778-787):
For every finite block environment ⨆_{k∈K} P_k, distinct blocks i,j,
and lotteries qᵢ ∈ Δ(Aᵢ), qⱼ ∈ Δ(Aⱼ):
  qᵢ^i ≽_{⨆_k P_k} qⱼ^j ↔ I_{qᵢ,Pᵢ} ≥ I_{qⱼ,Pⱼ}
-/

/-- Block same-scale representation: cross-block comparisons in any finite
    block environment are determined by mutual information on the same scale.

    Paper "moreover" clause (empowerment_v5.tex lines 778-787). -/
def BlockSameScaleRep (F : PrefFamily.{u}) : Prop :=
  ∀ {K : Type u} [Fintype K] [DecidableEq K]
    (Act : K → Type u) (Out : K → Type u)
    [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
    [∀ k, Fintype (Out k)] [∀ k, DecidableEq (Out k)]
    (P : ∀ k, Channel (Act k) (Out k))
    (i j : K) (_hij : i ≠ j)
    (qᵢ : Dist (Act i)) (qⱼ : Dist (Act j)),
    F.rel (blockFamilyChannel Act Out P)
      (blockEmbedDist Act i qᵢ)
      (blockEmbedDist Act j qⱼ)
    ↔
    mutualInfo qᵢ (P i) ≥ mutualInfo qⱼ (P j)

/-!
## Main Theorem Statements
-/

/-- The main characterization (paper Theorem 1, lines 770-777):
    TraceAxioms F ↔ MIRep F -/
def MainCharacterization : Prop :=
  ∀ F : PrefFamily.{u}, TraceAxioms F ↔ MIRep F

/-- The full theorem including the moreover clause (lines 778-787). -/
def MainCharacterizationWithMoreover : Prop :=
  ∀ F : PrefFamily.{u},
    (TraceAxioms F ↔ MIRep F) ∧
    (TraceAxioms F → BlockSameScaleRep F)

/-!
## Theorem Spine Components
-/

/-- Sufficiency: axioms imply MI representation.
    Paper: "(i) ⟹ (ii)", proved in sufficiency section. -/
def SufficiencyStatement : Prop :=
  ∀ F : PrefFamily.{u}, TraceAxioms F → MIRep F

/-- Benchmark: MI representation implies axioms.
    Paper: Lemma lem:MIbenchmark, lines 555-765. -/
def BenchmarkStatement : Prop :=
  ∀ F : PrefFamily.{u}, MIRep F → TraceAxioms F

/-- Block scale: axioms imply same-scale block representation.
    Paper: "moreover" clause, lines 778-787. -/
def BlockScaleStatement : Prop :=
  ∀ F : PrefFamily.{u}, TraceAxioms F → BlockSameScaleRep F

/-- Logical assembly: the three spine components imply the full theorem. -/
theorem main_characterization_from_spine
    (hsuff : SufficiencyStatement.{u})
    (hbench : BenchmarkStatement.{u})
    (hblock : BlockScaleStatement.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  intro F
  constructor
  · constructor
    · intro hax
      exact hsuff F hax
    · intro hrep
      exact hbench F hrep
  · intro hax
    exact hblock F hax

/-!
## Theorem Spine Package
-/

/-- Package of the three proof obligations. -/
structure TheoremSpinePackage : Prop where
  sufficiency : SufficiencyStatement.{u}
  benchmark : BenchmarkStatement.{u}
  blockScale : BlockScaleStatement.{u}

/-- Assembly from package. -/
theorem main_characterization_from_package
    (pkg : TheoremSpinePackage.{u}) :
    MainCharacterizationWithMoreover.{u} :=
  main_characterization_from_spine pkg.sufficiency pkg.benchmark pkg.blockScale

/-!
## Trivial MI Representation Lemma
-/

/-- The MI preference family trivially satisfies MIRep.
    (Already proved in MIPreference.lean as MIPrefFamily_is_MIRep) -/
theorem MIPrefFamily_MIRep : MIRep MIPrefFamily := MIPrefFamily_is_MIRep

/-- Benchmark/necessity direction: every MI-representable preference family
satisfies A1--A7.  Both finite data-processing inequalities are proved
internally. -/
theorem BenchmarkStatement_of_MIRep :
    BenchmarkStatement.{u} := by
  intro F hrep
  exact MIRep_TraceAxioms F hrep

/-!
## Block Scale from MIRep

The "moreover" clause follows from MIRep via the block mutual information identity.
This is provable without sufficiency.
-/

/-- Block same-scale representation follows from MI representation.
    Uses mutualInfo_blockFamily_embed to rewrite both MI terms. -/
theorem blockSameScaleRep_of_MIRep (F : PrefFamily.{u}) (hrep : MIRep F) :
    BlockSameScaleRep F := by
  intro K _ _ Act Out _ _ _ _ P i j _hij qᵢ qⱼ
  rw [hrep (blockFamilyChannel Act Out P) (blockEmbedDist Act i qᵢ) (blockEmbedDist Act j qⱼ)]
  rw [mutualInfo_blockFamily_embed Act Out P i qᵢ]
  rw [mutualInfo_blockFamily_embed Act Out P j qⱼ]

/-- Statement: MIRep implies BlockSameScaleRep.
    This is provable without sufficiency. -/
def BlockScaleFromMIRepStatement : Prop :=
  ∀ F : PrefFamily.{u}, MIRep F → BlockSameScaleRep F

/-- MIRep implies block same-scale representation. -/
theorem blockScaleFromMIRepStatement : BlockScaleFromMIRepStatement.{u} :=
  blockSameScaleRep_of_MIRep

/-- BlockScaleStatement follows from sufficiency plus block scale from MIRep.

    Logical dependency:
    - TraceAxioms F
    - SufficiencyStatement gives MIRep F
    - BlockScaleFromMIRepStatement gives BlockSameScaleRep F -/
theorem blockScaleStatement_from_sufficiency
    (hsuff : SufficiencyStatement.{u})
    (hblockMI : BlockScaleFromMIRepStatement.{u}) :
    BlockScaleStatement.{u} := by
  intro F hax
  exact hblockMI F (hsuff F hax)

/-!
## Stage Markers
-/

/-- Stage 1 definitions complete. -/
def Stage1DefinitionsComplete : Prop := True

/-- Stage 2 theorem spine defined. -/
def Stage2TheoremSpineComplete : Prop := True

/-- Stage 4A block scale from MIRep proved. -/
def Stage4ABlockScaleFromMIRepComplete : Prop := True

end TraceableAgency
