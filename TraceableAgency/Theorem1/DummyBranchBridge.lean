/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.CommonMarkedScale
import TraceableAgency.Theorem1.PayoffBranches

/-!
# Independent-dummy bridge for singleton-support branches

Adjoining a full-support nontrivial dummy action turns every posterior support
into a nontrivial support, while preserving the reached branch mass and the
normalized value of deterministic-payoff compounds.  These are the exact
identities needed to reduce a singleton-support reached branch to the
nontrivial-support case.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A B Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

/-! ## Nontriviality of product support -/

/-- Tensoring any finite prior with a full-support prior on a nontrivial type
makes the positive-support subtype of the product nontrivial. -/
theorem supportSubtype_prodDist_nontrivial_right
    [Nontrivial B]
    (r : TraceableAgency.Dist A) (s : TraceableAgency.Dist B)
    (hs : s.FullSupport) :
    Nontrivial (supportSubtype (prodDist r s)) := by
  classical
  rcases supportSubtype_nonempty r with ⟨a⟩
  obtain ⟨b₁, b₂, hb⟩ := exists_pair_ne B
  let x : supportSubtype (prodDist r s) :=
    ⟨(a.1, b₁), by
      rw [prodDist_apply_pair]
      exact mul_pos a.2 (hs b₁)⟩
  let y : supportSubtype (prodDist r s) :=
    ⟨(a.1, b₂), by
      rw [prodDist_apply_pair]
      exact mul_pos a.2 (hs b₂)⟩
  refine ⟨⟨x, y, ?_⟩⟩
  intro hxy
  apply hb
  exact congrArg (fun z : supportSubtype (prodDist r s) => z.1.2) hxy

/-! ## Exact normalized-value preservation -/

/-- A deterministic-payoff compound has exactly the same normalized marked
utility after an independent dummy action is adjoined to its first stage. -/
theorem normalizedMarkedUtility_payoffBranch_independentDummy
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (s : TraceableAgency.Dist B)
    (hq : q.FullSupport) (hs : s.FullSupport)
    (P : Channel A Y) (payoff : Y → O) :
    normalizedMarkedUtility F h (prodDist q s)
        (markedDummy_prodDist_fullSupport q s hq hs)
        (payoffBranchExperiment
          (independentDummyFirstStage (B := B) P) payoff) =
      normalizedMarkedUtility F h q hq
        (payoffBranchExperiment P payoff) := by
  change
    normalizedMarkedUtility F h (prodDist q s)
        (markedDummy_prodDist_fullSupport q s hq hs)
        (markedExperimentOfChannel
          (payoffBranchCompound
            (independentDummyFirstStage (B := B) P) payoff)) =
      normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel (payoffBranchCompound P payoff))
  rw [← independentDummy_payoffBranchCompound]
  exact normalizedMarkedUtility_independentDummy
    F h q s hq hs (payoffBranchExperiment P payoff)

/-! ## Reached branch identities -/

/-- The probability mass of every first-stage branch is unchanged by an
independent dummy action. -/
theorem branchMass_independentDummyFirstStage
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (s : TraceableAgency.Dist B) (target : Y) :
    Channel.outcomeMarginal
        (independentDummyFirstStage (B := B) P) (prodDist q s) target =
      Channel.outcomeMarginal P q target := by
  exact congrArg (fun d : TraceableAgency.Dist Y ↦ d target)
    (outcomeMarginal_independentDummyFirstStage P q s)

/-- A branch is reached with positive probability before the dummy lift iff
it is reached with positive probability after the lift. -/
theorem branchPositive_independentDummyFirstStage_iff
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (s : TraceableAgency.Dist B) (target : Y) :
    BranchPositive (independentDummyFirstStage (B := B) P)
        (prodDist q s) target ↔ BranchPositive P q target := by
  unfold BranchPositive
  rw [branchMass_independentDummyFirstStage]

/-- Direct forward form of positivity preservation, convenient when applying
branch-insertion results to the dummy-lifted first stage. -/
theorem branchPositive_independentDummyFirstStage
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (s : TraceableAgency.Dist B) (target : Y)
    (htarget : BranchPositive P q target) :
    BranchPositive (independentDummyFirstStage (B := B) P)
        (prodDist q s) target :=
  (branchPositive_independentDummyFirstStage_iff P q s target).2 htarget

/-- At a reached branch, the dummy-lifted posterior is the product of the
original posterior and the dummy prior. -/
theorem branchPosterior_independentDummyFirstStage_of_pos
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (s : TraceableAgency.Dist B) (target : Y)
    (htarget : BranchPositive P q target) :
    branchPosterior (independentDummyFirstStage (B := B) P)
        (prodDist q s) target =
      prodDist (branchPosterior P q target) s := by
  simpa [branchPosterior] using
    (posterior_independentDummyFirstStage_of_pos P q s target htarget)

/-- The dummy-lifted reached posterior has a nontrivial positive-support
subtype, even when the original reached posterior has singleton support. -/
theorem supportSubtype_branchPosterior_independentDummyFirstStage_nontrivial
    [Nontrivial B]
    (P : Channel A Y) (q : TraceableAgency.Dist A)
    (s : TraceableAgency.Dist B) (hs : s.FullSupport) (target : Y)
    (htarget : BranchPositive P q target) :
    Nontrivial
      (supportSubtype
        (branchPosterior (independentDummyFirstStage (B := B) P)
          (prodDist q s) target)) := by
  rw [branchPosterior_independentDummyFirstStage_of_pos
    P q s target htarget]
  exact supportSubtype_prodDist_nontrivial_right
    (branchPosterior P q target) s hs

end TraceableAgency.Theorem1
