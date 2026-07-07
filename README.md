# TraceableAgency

Lean 4 formalization of the main characterization theorem for traceable agency preferences over finite stochastic environments.

## Main Theorem

The public theorem is:

```lean
TraceableAgency.MainCharacterizationWithMoreover_clean
```

with type:

```lean
(hfad : ClassicalFaddeevTheoremAssumptions)
(hhm : FinalHMInterface)
(hdpi : FiniteDPIAssumptions) :
MainCharacterizationWithMoreover
```

The conclusion expands to:

```lean
∀ F, (TraceAxioms F ↔ MIRep F) ∧ (TraceAxioms F → BlockSameScaleRep F)
```

Here `TraceAxioms F` packages the paper's axioms A1-A8, `MIRep F` is the mutual-information representation, and `BlockSameScaleRep F` is the block same-scale "moreover" clause.

## External Interfaces

The theorem is proved modulo three explicitly stated finite classical interfaces:

* `ClassicalFaddeevTheoremAssumptions`
* `FinalHMInterface`
* `FiniteDPIAssumptions`

These are part of the Lean theorem boundary and are printed by the verification script.

## Requirements

This repository uses the Lean toolchain pinned in:

```text
lean-toolchain
```

and mathlib pinned in:

```text
lake-manifest.json
```

## Verification

Run:

```bash
lake build
./scripts/check_certificate.sh
```

The verification script prints the main theorem, its axioms, the expanded conclusion, the axiom package, and the three external interfaces. It also checks that the Lean source contains no `sorry`, tactic `admit`, or declaration-level `axiom`.

Expected theorem boundary:

```lean
TraceableAgency.MainCharacterizationWithMoreover_clean
  (hfad : ClassicalFaddeevTheoremAssumptions)
  (hhm : FinalHMInterface)
  (hdpi : FiniteDPIAssumptions) :
  MainCharacterizationWithMoreover
```

Expected `#print axioms` output:

```text
[propext, Classical.choice, Quot.sound]
```
