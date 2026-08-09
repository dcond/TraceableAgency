# TraceableAgency

Lean 4 verification of Theorem 1 in *Trace-Tempered Choice: A Self-Contained
Axiomatisation with Explicit Payoffs and Records* (v3).

## Verified result

The public theorem is:

```lean
TraceTemperedChoiceVerification.trace_tempered_choice_v3_theorem1 :
  TraceTemperedChoiceVerification.Theorem1Statement
```

For every finite payoff alphabet `O` with at least two elements and every
preference family `F`, the statement proves:

1. Axioms (A1)--(A8) are equivalent to representation by expected payoff
   utility plus a strictly positive multiple of mutual information, with one
   nonconstant payoff index and one global information coefficient.
2. Under those axioms, the same witnesses represent every finite
   block-supported cross-channel comparison on the same scale.

The formal proposition preserves the paper's quantifier order and includes
the same-witness “moreover” clause as a separate conjunct.

## Paper

- [`Paper/trace_tempered_choice_v3.tex`](Paper/trace_tempered_choice_v3.tex) —
  authoritative source.
- [`Paper/trace_tempered_choice_v3.pdf`](Paper/trace_tempered_choice_v3.pdf) —
  compiled 54-page paper.
- [`Paper/appendix_a_pure_trace.tex`](Paper/appendix_a_pure_trace.tex) —
  pure-trace part of the single proof.
- [`Paper/appendix_b_main_theorem.tex`](Paper/appendix_b_main_theorem.tex) —
  completion of Theorem 1.
- [`Paper/appendix_c_auxiliary_results.tex`](Paper/appendix_c_auxiliary_results.tex)
  — auxiliary results not used to prove Theorem 1.

The axioms occur once in the main text.  Appendix A uses them rather than
introducing or repeating a second axiom system.

## Verification package

The reader-facing package is in
[`Theorem1Verification/`](Theorem1Verification/README.md):

- [`Statements.lean`](Theorem1Verification/Statements.lean) — exact formal
  statement, definitions, and Axioms (A1)--(A8).
- [`Proof.lean`](Theorem1Verification/Proof.lean) — final kernel proof.
- [`Axioms.lean`](Theorem1Verification/Axioms.lean) — deliberately empty of
  extra mathematical axioms.
- [`FORMALIZATION_CERTIFICATE.md`](Theorem1Verification/FORMALIZATION_CERTIFICATE.md)
  — mathematical translation of the paper statement, every axiom, the Lean
  declarations, and the complete trust boundary.
- [`CLAIM_MAP.md`](Theorem1Verification/CLAIM_MAP.md) — paper text to Lean
  declaration correspondence.
- [`PAPER_PROOF_ROADMAP.md`](Theorem1Verification/PAPER_PROOF_ROADMAP.md) —
  detailed human proof route following the checked dependency chain.
- [`CERTIFICATE_SHA256SUMS`](Theorem1Verification/CERTIFICATE_SHA256SUMS) —
  exact hashes for the complete project Lean source closure, paper artifacts,
  certificate machinery, and pinned toolchain/dependencies.

`TraceableAgency/` contains the checked finite probability, information
theory, affine-representation, entropy-characterization, and pure-trace
machinery used internally by the final proof.  It is supporting source, not a
second public theorem package.

## Trust boundary

The project declares no additional mathematical axiom.  The recursively
collected kernel dependencies of the final theorem are exactly:

```text
propext
Classical.choice
Quot.sound
```

The certificate separately documents the two presentation translations used
to compare paper and Lean: finite closed-graph versus sequential closedness,
and ratio-form versus entropy-form mutual information.

The build fails if an audited endpoint acquires any kernel axiom outside the
three-item whitelist or reaches a superseded stronger dependency route.

## Reproduce

The repository pins Lean and mathlib in `lean-toolchain` and
`lake-manifest.json`.  From the repository root, run:

```bash
lake build
./scripts/check_theorem1_certificate.sh
```

The certificate script verifies the artifact manifest, rejects proof holes
and project axioms, builds the exact theorem target, prints the public
statement and axiom dependencies, and replays the proof with
`leanchecker --fresh`.

The same script is configured in
`.github/workflows/theorem1-certificate.yml` for GitHub Actions.
