# Paper snapshots and Theorem 1 proof

## Historical matched snapshot

The original Lean correspondence review used the axioms and main theorem of
`empowerment_v7`.

- [`empowerment_v7.tex`](empowerment_v7.tex) is that exact source snapshot.
- [`empowerment_v7.pdf`](empowerment_v7.pdf) is its compiled 50-page paper.

SHA-256:

```text
b6be0784355fe1aa37736b7ecc58bcb93d1e8dfc1fb4404a2781e34b4ace842b  empowerment_v7.tex
4b9fc6107bf75d4ecba4e21f6e882445356973f82c0bd40855d23d580619a71b  empowerment_v7.pdf
```

## Current paper

The authoritative source is
[`trace_tempered_choice_v3.tex`](trace_tempered_choice_v3.tex), which states
Axioms (A1)--(A8) once in the main text and inputs exactly three proof
appendices:

- [`appendix_a_pure_trace.tex`](appendix_a_pure_trace.tex) proves the
  pure-trace lemma on constant-payoff lifts.  It uses the main-text axioms
  directly and introduces no second axiom system.
- [`appendix_b_main_theorem.tex`](appendix_b_main_theorem.tex) combines the
  pure-trace lemma with the material scale, branch calibration, payoff
  telescope, and sequentialisation to prove Theorem 1.
- [`appendix_c_auxiliary_results.tex`](appendix_c_auxiliary_results.tex)
  collects the sign, uniqueness, matching, independence, and choice-result
  proofs that are not used in proving Theorem 1.

The compiled paper is
[`trace_tempered_choice_v3.pdf`](trace_tempered_choice_v3.pdf).  Build it with:

```sh
cd Paper
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  trace_tempered_choice_v3.tex
```

The pure-trace engine used in Appendix A is kernel-checked by
`TraceableAgency.provedMainCharacterizationWithMoreover` and imported into the
material model by `Theorem1Verification/PureTrace.lean`.  The Appendix B
dependency chain is documented in
`Theorem1Verification/PAPER_PROOF_ROADMAP.md` and culminates in the checked
declaration `trace_tempered_choice_v3_theorem1`.
