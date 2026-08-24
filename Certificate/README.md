# Theorem 1 v10 certificate

This directory documents the correspondence between
[`trace_tempered_choice_v10.tex`](../Paper/trace_tempered_choice_v10.tex) and
the Lean theorem
`TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1`.

- [`FORMALIZATION_CERTIFICATE.md`](FORMALIZATION_CERTIFICATE.md): exact
  mathematical boundary, axiom translation, proof-facing bridges, and trust
  boundary.
- [`CLAIM_MAP.md`](CLAIM_MAP.md): stable paper anchors mapped to Lean
  declarations.
- [`THEOREM1_FORMAL_SPECIFICATION.md`](THEOREM1_FORMAL_SPECIFICATION.md):
  recursively extracted paper definitions, A1--A8, representation clauses,
  and exact theorem statement, with GitHub-rendered mathematical notation
  below the Lean.
- [`PAPER_PROOF_ROADMAP.md`](PAPER_PROOF_ROADMAP.md): v10 Appendix A mapped to
  the checked proof route.
- [`SHA256SUMS`](SHA256SUMS): SHA-256 digest of every repository file other
  than the manifest itself.

The exact current proposition is
`TraceableAgency.Theorem1.Theorem1StatementV10`. Its axiom bundle contains
exactly A1--A8; the certificate checks that no additional hypothesis enters
the public theorem. The generated specification stops at named Lean/Mathlib
boundary symbols and does not unfold them.

Appendix B contains auxiliary paper results and is outside this certified
endpoint.

Reproduce with:

```bash
./scripts/check_theorem1_certificate.sh
```

The expected final kernel dependency list is exactly:

```text
propext
Classical.choice
Quot.sound
```
