# Theorem 1 v5 certificate

This directory documents the correspondence between
[`trace_tempered_choice_v5.tex`](../Paper/trace_tempered_choice_v5.tex) and the
Lean theorem
`TraceTemperedChoiceVerification.trace_tempered_choice_v5_theorem1`.

- [`FORMALIZATION_CERTIFICATE.md`](FORMALIZATION_CERTIFICATE.md): exact
  mathematical boundary, v5 axiom translation, relevance bridge, and trust
  boundary.
- [`CLAIM_MAP.md`](CLAIM_MAP.md): stable paper anchors mapped to Lean
  declarations.
- [`PAPER_PROOF_ROADMAP.md`](PAPER_PROOF_ROADMAP.md): paper-to-code proof route.
- [`SHA256SUMS`](SHA256SUMS): SHA-256 digest of every repository file other
  than the manifest itself.

The exact proposition is `TraceableAgency.Theorem1.Theorem1StatementV5`.
The public proof has that proposition as its type. Appendix C is paper-only and
is outside this certified endpoint.

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
