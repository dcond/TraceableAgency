# Paper

The authoritative paper is
[`trace_tempered_choice_v3.tex`](trace_tempered_choice_v3.tex); its reproducible
55-page build is [`trace_tempered_choice_v3.pdf`](trace_tempered_choice_v3.pdf).

The proof is organized as:

- [`appendix_a_pure_trace.tex`](appendix_a_pure_trace.tex): the auxiliary
  constant-payoff characterization;
- [`appendix_b_main_theorem.tex`](appendix_b_main_theorem.tex): completion of
  Theorem 1;
- [`appendix_c_auxiliary_results.tex`](appendix_c_auxiliary_results.tex):
  auxiliary results not used in Theorem 1.

The main text states Axioms (A1)--(A8) once. Appendix A uses their induced
constant-payoff consequences rather than introducing another axiom system.

From the repository root, verify the tracked PDF with:

```bash
./scripts/build_paper.sh --check
```

Use `./scripts/build_paper.sh --update` after an intentional source change.
The build fixes its date and PDF metadata, so independent builds are
byte-identical.

The Lean correspondence is documented in
[`../Certificate/CLAIM_MAP.md`](../Certificate/CLAIM_MAP.md) and
[`../Certificate/PAPER_PROOF_ROADMAP.md`](../Certificate/PAPER_PROOF_ROADMAP.md).
Copyright terms for the paper are stated in [`LICENSE`](LICENSE).
