/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Behaviour.Conditions
import TraceableAgency.PureTrace.Behaviour.Representation
import TraceableAgency.Basic.Blocks
import TraceableAgency.Info.Identities

/-!
# Pure-trace characterization

This auxiliary result is consumed by the proof of Theorem 1. A preference
family satisfies six induced structural conditions if and only if it is
represented by mutual information.

Moreover, under these conditions, block-supported cross-channel comparisons
are on the same scale.

This file defines:
- PureTraceMIRepresentation
- PureTraceBlockRepresentation
- PureTraceCharacterization
- PureTraceCharacterizationWithBlocks
- PureTraceSufficiency, PureTraceNecessity, PureTraceBlockConclusion
- pureTraceCharacterization_from_components (logical assembly)
- PureTraceProofPackage
-/

namespace TraceableAgency

universe u

/-!
## Block Same-Scale Representation

Paper "moreover" clause:
For every finite block environment ⨆_{k∈K} P_k, distinct blocks i,j,
and lotteries qᵢ ∈ Δ(Aᵢ), qⱼ ∈ Δ(Aⱼ):
  qᵢ^i ≽_{⨆_k P_k} qⱼ^j ↔ I_{qᵢ,Pᵢ} ≥ I_{qⱼ,Pⱼ}
-/

/-- Cross-block comparisons in any finite block environment are determined by
mutual information on one common scale. -/
def PureTraceBlockRepresentation (F : PrefFamily.{u}) : Prop :=
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

/-- Equivalence between the induced conditions and mutual-information representation. -/
def PureTraceCharacterization : Prop :=
  ∀ F : PrefFamily.{u}, PureTraceConditions F ↔ PureTraceMIRepresentation F

/-- The pure-trace equivalence together with finite-block scale coherence. -/
def PureTraceCharacterizationWithBlocks : Prop :=
  ∀ F : PrefFamily.{u},
    (PureTraceConditions F ↔ PureTraceMIRepresentation F) ∧
    (PureTraceConditions F → PureTraceBlockRepresentation F)

/-!
## Theorem Spine Components
-/

/-- The induced conditions imply mutual-information representation. -/
def PureTraceSufficiency : Prop :=
  ∀ F : PrefFamily.{u}, PureTraceConditions F → PureTraceMIRepresentation F

/-- Mutual-information representation implies the induced conditions. -/
def PureTraceNecessity : Prop :=
  ∀ F : PrefFamily.{u}, PureTraceMIRepresentation F → PureTraceConditions F

/-- The induced conditions imply same-scale finite-block representation. -/
def PureTraceBlockConclusion : Prop :=
  ∀ F : PrefFamily.{u}, PureTraceConditions F → PureTraceBlockRepresentation F

/-- Logical assembly: the three spine components imply the full theorem. -/
theorem pureTraceCharacterization_from_components
    (hsuff : PureTraceSufficiency.{u})
    (hbench : PureTraceNecessity.{u})
    (hblock : PureTraceBlockConclusion.{u}) :
    PureTraceCharacterizationWithBlocks.{u} := by
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
structure PureTraceProofPackage : Prop where
  sufficiency : PureTraceSufficiency.{u}
  benchmark : PureTraceNecessity.{u}
  blockScale : PureTraceBlockConclusion.{u}

/-- Assembly from package. -/
theorem pureTraceCharacterization_from_package
    (pkg : PureTraceProofPackage.{u}) :
    PureTraceCharacterizationWithBlocks.{u} :=
  pureTraceCharacterization_from_components pkg.sufficiency pkg.benchmark pkg.blockScale

/-!
## Trivial MI Representation Lemma
-/

/-- The mutual-information preference family has its defining representation. -/
theorem mutualInformationFamily_representation :
    PureTraceMIRepresentation MIPrefFamily :=
  MIPrefFamily_is_MIRep

/-- Every mutual-information-representable family satisfies the induced conditions. -/
theorem pureTraceNecessity_of_representation :
    PureTraceNecessity.{u} := by
  intro F hrep
  exact MIRep_conditions F hrep

/-!
## Block Scale from PureTraceMIRepresentation

The "moreover" clause follows from PureTraceMIRepresentation via the block mutual information identity.
This is provable without sufficiency.
-/

/-- Mutual-information representation gives same-scale finite-block comparisons. -/
theorem pureTraceBlocks_of_representation
    (F : PrefFamily.{u}) (hrep : PureTraceMIRepresentation F) :
    PureTraceBlockRepresentation F := by
  intro K _ _ Act Out _ _ _ _ P i j _hij qᵢ qⱼ
  rw [hrep (blockFamilyChannel Act Out P) (blockEmbedDist Act i qᵢ) (blockEmbedDist Act j qⱼ)]
  rw [mutualInfo_blockFamily_embed Act Out P i qᵢ]
  rw [mutualInfo_blockFamily_embed Act Out P j qⱼ]

/-- Statement: PureTraceMIRepresentation implies PureTraceBlockRepresentation.
    This is provable without sufficiency. -/
def PureTraceBlocksFromRepresentation : Prop :=
  ∀ F : PrefFamily.{u}, PureTraceMIRepresentation F → PureTraceBlockRepresentation F

/-- PureTraceMIRepresentation implies block same-scale representation. -/
theorem pureTraceBlocksFromRepresentation_proved : PureTraceBlocksFromRepresentation.{u} :=
  pureTraceBlocks_of_representation

/-- PureTraceBlockConclusion follows from sufficiency plus block scale from PureTraceMIRepresentation.

    Logical dependency:
    - PureTraceConditions F
    - PureTraceSufficiency gives PureTraceMIRepresentation F
    - PureTraceBlocksFromRepresentation gives PureTraceBlockRepresentation F -/
theorem pureTraceBlockConclusion_from_sufficiency
    (hsuff : PureTraceSufficiency.{u})
    (hblockMI : PureTraceBlocksFromRepresentation.{u}) :
    PureTraceBlockConclusion.{u} := by
  intro F hax
  exact hblockMI F (hsuff F hax)

end TraceableAgency
