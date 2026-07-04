# TraceableAgency

Lean 4 formalisation of the main theorem of the empowerment / traceable-agency paper:
a preference family over finite stochastic environments satisfying behavioural axioms
(A1–A8) is represented by mutual information.

## Main result

The final theorem (`TraceableAgency/External/EntropyReductionClosure.lean`):

```lean
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
    (hfad : ClassicalFaddeevTheoremAssumptions)
    {F : PrefFamily}
    (hhm : FinalHMInterface)
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventions hhm hax) :
    MIRep F
```

It proves the **sufficiency** direction of the paper's Theorem 1:
`TraceAxioms F → MIRep F`, i.e. for every finite channel `P` and priors `q, q'`,

```
q ≽_P q'  ↔  I(q,P) ≥ I(q',P).
```

modulo the displayed classical interfaces (Herstein–Milnor, finite Blackwell,
Faddeev) and explicit representative/gauge/support normalisations.

The other two clauses of Theorem 1 are separate, kernel-checked theorems:

- **Necessity** `MIRep F → TraceAxioms F`: `BenchmarkStatement_of_DPI` (`Main.lean`),
  modulo the finite data-processing inequality.
- **Moreover / block same-scale**: `blockSameScaleRep_of_MIRep` (`Main.lean`), from `MIRep F`.

All three depend only on the standard axioms `[propext, Classical.choice, Quot.sound]`.

## Referee documentation

Read these together with the paper (`empowerment_v5(1).tex`) to verify faithfulness
without reading proof terms:

- `REFEREE_LEAN_ONLY_CERTIFICATE.md` — complete, self-contained transparent statement of
  the final theorem, every primitive, and every hypothesis/convention (verbatim Lean).
- `REFEREE_FAITHFULNESS_CERTIFICATE.md` — paper ⇄ Lean side-by-side faithfulness check.
- `REFEREE_LEAN_CERTIFICATION_DOSSIER.md` — kernel evidence (`#check` / `#print axioms`),
  scope, dependency graph.
- `EXTERNAL_ASSUMPTIONS_CLASSIFICATION.md` — status of every external assumption.

## Status of the external assumptions

The proof rests on three classical interfaces used as external theorems (not reproved
from first principles): finite Herstein–Milnor mixture-space representation, finite
Blackwell experiment equivalence, and Faddeev's finite entropy-uniqueness theorem —
plus a bundle of representative/gauge/support normalisations. The `FinalHMInterface.blackwell`
field is the *pure* finite Blackwell theorem; the A3/A4/A1 preference-replacement step is
proved internally.

Boundary support-extension (`FiniteCardinalSupportBoundaryAssumptions`): the boundary
`Hfun`-identity is proved (`hfun_eq_normalizedValue_idChannel_of_scale`, definitional for the
constructed representation); the remaining boundary value/scale coherence is under active
elimination (see the referee docs).

## Build

```
lake exe cache get   # fetch mathlib build cache
lake build
```

Toolchain: `leanprover/lean4` pinned in `lean-toolchain`; mathlib pinned in `lake-manifest.json`.

## Verify the certification

```
lake env lean <<'EOF'
import TraceableAgency
#check TraceableAgency.MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
#print axioms TraceableAgency.MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
EOF
```
