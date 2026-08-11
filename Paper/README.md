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

The pure-trace statement and common-scale block interface proved in Appendix A
are also kernel-checked by
`TraceableAgency.provedMainCharacterizationWithMoreover` and imported into the
material model by `Theorem1Verification/PureTrace.lean`.  The Appendix B
dependency chain is documented in
`Theorem1Verification/PAPER_PROOF_ROADMAP.md` and culminates in the checked
declaration `trace_tempered_choice_v3_theorem1`.
