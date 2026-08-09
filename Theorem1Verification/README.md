# Theorem 1 verification package

This directory is the self-contained Lean verification package for Theorem 1
of `Paper/trace_tempered_choice_v3.tex`.

## Reader entry points

- [`FORMALIZATION_CERTIFICATE.md`](FORMALIZATION_CERTIFICATE.md) states the
  paper theorem and Lean theorem in mathematics, expands Axioms (A1)--(A8),
  explains the two standard finite translation identities, and records the
  exact trust boundary.
- [`CLAIM_MAP.md`](CLAIM_MAP.md) maps paper source lines to Lean declarations.
- [`PAPER_PROOF_ROADMAP.md`](PAPER_PROOF_ROADMAP.md) gives a paper-length proof
  route following the transitive dependency chain checked by Lean.
- [`CERTIFICATE_SHA256SUMS`](CERTIFICATE_SHA256SUMS) binds the authoritative
  paper artifacts, the complete project Lean source closure, the reader-facing
  certificate, and the pinned toolchain/dependency files to exact bytes.

## Formal boundary

- [`Statements.lean`](Statements.lean) contains the domain, Axioms (A1)--(A8),
  represented value, and the exact proposition `Theorem1Statement`.  It does
  not prove the proposition.
- [`Proof.lean`](Proof.lean) contains the final theorem
  `trace_tempered_choice_v3_theorem1 : Theorem1Statement`.
- [`Axioms.lean`](Axioms.lean) deliberately declares no extra axiom or theorem
  interface.
- [`PaperFaithfulAxiomAudit.lean`](PaperFaithfulAxiomAudit.lean) fails the build
  if an unexpected kernel axiom enters any audited public endpoint.
- [`PaperFaithfulDependencyAudit.lean`](PaperFaithfulDependencyAudit.lean)
  fails the build if the public theorem reaches a superseded unproved or
  stronger historical interface.

The remaining `.lean` files prove the intermediate reductions used by
`Proof.lean`; they are ordinary checked dependencies, not assumptions.

## Authoritative paper

- [`../Paper/trace_tempered_choice_v3.tex`](../Paper/trace_tempered_choice_v3.tex)
- [`../Paper/trace_tempered_choice_v3.pdf`](../Paper/trace_tempered_choice_v3.pdf)
- [`../Paper/appendix_a_pure_trace.tex`](../Paper/appendix_a_pure_trace.tex)
- [`../Paper/appendix_b_main_theorem.tex`](../Paper/appendix_b_main_theorem.tex)
- [`../Paper/appendix_c_auxiliary_results.tex`](../Paper/appendix_c_auxiliary_results.tex)

## Reproduce the certificate

From the repository root, run:

```bash
lake build Theorem1Verification
./scripts/check_theorem1_certificate.sh
```

The first command checks the theorem and both compile-time audits.  The second
also checks source hygiene, the SHA-256 manifest, the public declaration
surface, and a fresh `leanchecker` replay.

The same certificate script runs on every pull request to `main`, every push
to `main`, and manual dispatch through
`.github/workflows/theorem1-certificate.yml`.

The expected final kernel dependency report is a subset of, and currently
exactly:

```text
propext
Classical.choice
Quot.sound
```

These are Lean/Mathlib logical foundations.  There is no additional
behavioral, information-theoretic, topological, or representation-theorem
axiom at the final theorem boundary.
