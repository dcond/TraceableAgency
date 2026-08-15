# Paper

The authoritative source is
[`trace_tempered_choice_v5.tex`](trace_tempered_choice_v5.tex); its reproducible
build is [`trace_tempered_choice_v5.pdf`](trace_tempered_choice_v5.pdf).

The proof is organized as:

- [`appendix_a_pure_trace_v5.tex`](appendix_a_pure_trace_v5.tex): the
  fixed-channel relevance bridge and pure-trace characterization;
- [`appendix_b_main_theorem_v5.tex`](appendix_b_main_theorem_v5.tex): material
  normalization, the global trace scale at `o*`, branch increments, and
  Theorem 1;
- [`appendix_c_auxiliary_results_v5.tex`](appendix_c_auxiliary_results_v5.tex):
  auxiliary paper results not required by the formal Theorem 1 endpoint.

The v5 numbering is: A1 weak order, A2 continuity, A3 fixed-channel material
relevance, A4 fixed-channel trace relevance at one payoff, A5 block coherence,
A6 record data processing, A7 action data processing, and A8 the binary
recordwise sure-thing principle. Appendix A proves its weak-and-strict
finite-branch extension from A1 and A5--A7. “Action processor” is used
throughout v5.

From the repository root:

```bash
./scripts/build_paper.sh --check
```

Use `./scripts/build_paper.sh --update` after an intentional source change.
The build fixes its date and PDF metadata so independent builds are
byte-identical. Lean correspondence is documented in
[`../Certificate/CLAIM_MAP.md`](../Certificate/CLAIM_MAP.md) and
[`../Certificate/PAPER_PROOF_ROADMAP.md`](../Certificate/PAPER_PROOF_ROADMAP.md).
