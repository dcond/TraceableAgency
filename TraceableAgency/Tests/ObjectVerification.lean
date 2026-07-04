/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Behaviour.MIPreference
import TraceableAgency.Main

/-!
# Object Verification and Transfer Diagnostics

This file contains verification tests to confirm that the formal objects
are correctly set up and documents the benchmark transfer proof from
the canonical MI family to arbitrary `MIRep F` families.

## Contents

1. `#check` statements for all key objects
2. `#print axioms` for canonical proofs
3. Basic relation transfer diagnostics
4. Semantic examples confirming object correctness

## Transfer Summary

The transfer from `MIPrefFamily` to arbitrary `MIRep F` is implemented by
explicit relation-transfer lemmas and explicit instance threading for the
dependent block-experiment predicate used in A2.

**What Works**:
- All canonical proofs compile: MIPrefFamily_A1, ..., MIPrefFamily_A8
- MIPrefFamily_TraceAxioms_of_DPI compiles and proves the benchmark for canonical MI
- MIRep_TraceAxioms_of_DPI compiles and proves the benchmark for arbitrary MIRep F
- BenchmarkStatement_of_DPI exposes the main-theorem necessity component

**Engineering note**:
The previously fragile point was A2's `ExperimentPairPref`, whose outcome type
is hidden inside `FiniteExperimentOn`. The transfer lemma now supplies the
sum-type `Fintype` and `DecidableEq` instances explicitly.
-/

set_option linter.style.header false

namespace TraceableAgency.Tests.ObjectVerification

universe u

/-!
## Part A: Object #checks

Verify all key objects exist and have the expected types.
-/

section ObjectChecks

#check MIPrefFamily
#check @MIPrefFamily_is_MIRep
#check @MIPrefFamily_TraceAxioms_of_DPI
#check @MIRep_TraceAxioms_of_DPI
#check @BenchmarkStatement_of_DPI
#check FiniteDPIAssumptions
#check @MIPrefFamily_A1
#check @MIPrefFamily_A2
#check @MIPrefFamily_A3
#check @MIPrefFamily_A4_of_DPI
#check @MIPrefFamily_A5_of_DPI
#check @MIPrefFamily_A6
#check @MIPrefFamily_A7
#check @MIPrefFamily_A7Strong
#check @A7_of_A7Strong
#check @MIPrefFamily_A8
#check MIRep
#check TraceAxioms
#check BenchmarkStatement
#check BlockSameScaleRep
#check @blockSameScaleRep_of_MIRep

end ObjectChecks

/-!
## Part B: Axiom Checks

Verify that the canonical proofs do not use any hidden axioms beyond
the explicit FiniteDPIAssumptions parameter.

Expected output: propext, Classical.choice, Quot.sound (standard Lean axioms only)
No external mathematical axioms should appear.
-/

section AxiomChecks

#print axioms MIPrefFamily_TraceAxioms_of_DPI
#print axioms MIPrefFamily_A1
#print axioms MIPrefFamily_A2
#print axioms MIPrefFamily_A3
#print axioms MIPrefFamily_A6
#print axioms MIPrefFamily_A7
#print axioms MIPrefFamily_A8

end AxiomChecks

/-!
## Part C: Basic Relation Transfer (Monomorphic)

These prove that the basic relation transfer works when types are fixed.
This demonstrates the transfer is mathematically trivial.
-/

section MonomorphicTransfer

variable {A O : Type u}
variable [Fintype A] [DecidableEq A]
variable [Fintype O] [DecidableEq O]

/-- Relation transfer: F.rel ↔ MIPrefFamily.rel when MIRep F holds.
    This is the fundamental transfer lemma. -/
theorem rel_transfer_monomorphic
    (F : PrefFamily.{u}) (hrep : MIRep F)
    (P : Channel A O) (q r : Dist A) :
    F.rel P q r ↔ MIPrefFamily.rel P q r := by
  rw [hrep P q r]
  rfl

/-- Strict relation transfer follows from rel transfer. -/
theorem strict_transfer_monomorphic
    (F : PrefFamily.{u}) (hrep : MIRep F)
    (P : Channel A O) (q r : Dist A) :
    F.strictRel P q r ↔ MIPrefFamily.strictRel P q r := by
  unfold PrefFamily.strictRel
  have h1 := rel_transfer_monomorphic F hrep P q r
  have h2 := rel_transfer_monomorphic F hrep P r q
  constructor
  · intro ⟨hrel, hnot⟩
    exact ⟨h1.mp hrel, fun h => hnot (h2.mpr h)⟩
  · intro ⟨hrel, hnot⟩
    exact ⟨h1.mpr hrel, fun h => hnot (h2.mp h)⟩

end MonomorphicTransfer

/-!
## Part D: Semantic Examples

Confirm that the objects encode the intended concepts.
-/

section SemanticExamples

/-- MIPrefFamily satisfies MIRep (canonical representation). -/
example : MIRep MIPrefFamily := MIPrefFamily_is_MIRep

/-- Canonical axioms modulo DPI. -/
example (hdpi : FiniteDPIAssumptions.{u}) : TraceAxioms.{u} MIPrefFamily :=
  MIPrefFamily_TraceAxioms_of_DPI.{u} hdpi

/-- A3 is really included in TraceAxioms. -/
example (hdpi : FiniteDPIAssumptions.{u}) : A3_BlockComparisonCoherence.{u} MIPrefFamily :=
  (MIPrefFamily_TraceAxioms_of_DPI.{u} hdpi).a3

/-- A8 is really included in TraceAxioms. -/
example (hdpi : FiniteDPIAssumptions.{u}) : A8_IndependentBackgroundSeparability.{u} MIPrefFamily :=
  (MIPrefFamily_TraceAxioms_of_DPI.{u} hdpi).a8

/-- Block same-scale works for arbitrary F with MIRep. -/
example (F : PrefFamily.{u}) (hrep : MIRep F) : BlockSameScaleRep.{u} F :=
  blockSameScaleRep_of_MIRep F hrep

#check BenchmarkStatement

end SemanticExamples

/-!
## Part E: Transfer Documentation

### Transfer Pattern

For any axiom Ax, the transfer proof structure is:

```lean
theorem Ax_transfer (F : PrefFamily) (hrep : MIRep F) : Ax F := by
  have hAx := MIPrefFamily_Ax
  intro ...
  -- For each occurrence of F.rel P q r in the goal:
  have hiff := hrep P q r
  -- Rewrite using the iff to get MIPrefFamily.rel P q r
  -- Then apply hAx
```

This is mathematically trivial because `MIRep F` gives:
```
∀ P q r, F.rel P q r ↔ mutualInfo q P ≥ mutualInfo r P
```
which is exactly the definition of `MIPrefFamily.rel`.

### Resolved Engineering Point

The historical failure mode was typeclass synthesis. When writing:
```lean
intro A O [Fintype A] [DecidableEq A] ...
```
and later needing:
```lean
hrep (blockChannel P Q) (inlDist q) (inrDist r)
```
Lean sometimes needs help synthesizing `Fintype`/`DecidableEq` instances for
compound or dependent types. The current proof resolves this by using small
transfer lemmas and, for `ExperimentPairPref`, explicitly supplying the
sum-type instances from the two packaged finite experiments.

### Conclusion

`MIRep_TraceAxioms_of_DPI` is the benchmark direction for arbitrary
MI-representable preference families, modulo the explicit finite DPI
assumptions used for A4 and A5.
-/

end TraceableAgency.Tests.ObjectVerification
