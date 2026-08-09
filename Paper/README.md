# Trace-Tempered Choice v3

This directory contains the paper certified by the Lean development.

## Authoritative paper

- [`trace_tempered_choice_v3.tex`](trace_tempered_choice_v3.tex) — source.
- [`trace_tempered_choice_v3.pdf`](trace_tempered_choice_v3.pdf) — compiled
  54-page paper.

The source states Axioms (A1)--(A8) once in the main text and inputs exactly
three proof appendices:

- [`appendix_a_pure_trace.tex`](appendix_a_pure_trace.tex) proves the
  pure-trace part of the argument directly from the main-text axioms.
- [`appendix_b_main_theorem.tex`](appendix_b_main_theorem.tex) combines that
  result with material-scale construction, branch calibration, payoff
  telescoping, and sequentialization to prove Theorem 1.
- [`appendix_c_auxiliary_results.tex`](appendix_c_auxiliary_results.tex)
  collects results that are not used in proving Theorem 1.

Build the paper with:

```bash
cd Paper
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  trace_tempered_choice_v3.tex
```

## Formal correspondence

The complete verification package is indexed at
[`../Theorem1Verification/README.md`](../Theorem1Verification/README.md).

- [`FORMALIZATION_CERTIFICATE.md`](../Theorem1Verification/FORMALIZATION_CERTIFICATE.md)
  translates the theorem, Axioms (A1)--(A8), and the representation into the
  exact Lean declarations and states the trust boundary.
- [`CLAIM_MAP.md`](../Theorem1Verification/CLAIM_MAP.md) maps paper source
  lines to declarations.
- [`PAPER_PROOF_ROADMAP.md`](../Theorem1Verification/PAPER_PROOF_ROADMAP.md)
  gives the detailed human proof route corresponding to the kernel proof.
- `Statements.lean`, the deliberately empty `Axioms.lean`, and `Proof.lean`
  form the public verification boundary.

From the repository root, run:

```bash
lake build
./scripts/check_theorem1_certificate.sh
```
