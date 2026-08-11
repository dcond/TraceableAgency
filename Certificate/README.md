# Theorem 1 certificate

This directory documents the correspondence between Theorem 1 of
[`trace_tempered_choice_v3.tex`](../Paper/trace_tempered_choice_v3.tex) and its
Lean proof.

## Reader entry points

- [`FORMALIZATION_CERTIFICATE.md`](FORMALIZATION_CERTIFICATE.md): mathematical
  statement, exact Axiom (A1)--(A8) translations, conclusion, and trust
  boundary.
- [`CLAIM_MAP.md`](CLAIM_MAP.md): stable LaTeX labels mapped to Lean
  declarations.
- [`PAPER_PROOF_ROADMAP.md`](PAPER_PROOF_ROADMAP.md): detailed paper-proof route
  following the checked Lean dependencies.
- [`SHA256SUMS`](SHA256SUMS): SHA-256 digest of every repository file other than
  the manifest itself.

## Formal boundary

- [`Statements.lean`](../TraceableAgency/Theorem1/Statements.lean) states the
  domain, Axioms (A1)--(A8), representation, and exact proposition
  `TraceableAgency.Theorem1.Theorem1Statement`.
- [`Proof.lean`](../TraceableAgency/Theorem1/Proof.lean) proves
  `trace_tempered_choice_v3_theorem1 : Theorem1Statement`.
- [`Axioms.lean`](../TraceableAgency/Theorem1/Axioms.lean) declares no extra
  axiom.
- [`Axioms.lean`](../TraceableAgency/Audit/Axioms.lean) rejects unexpected
  kernel axioms.
- [`Dependencies.lean`](../TraceableAgency/Audit/Dependencies.lean) rejects
  superseded stronger or unproved dependency routes.

## Reproduce

```bash
./scripts/check_theorem1_certificate.sh
```

The expected final kernel dependency list is exactly:

```text
propext
Classical.choice
Quot.sound
```

These are Lean/Mathlib foundations, not behavioral, information-theoretic,
topological, or representation-theorem assumptions.
