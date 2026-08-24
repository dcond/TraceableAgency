# Paper

The authoritative source is
[`trace_tempered_choice_v10.tex`](trace_tempered_choice_v10.tex); its
reproducible build is
[`trace_tempered_choice_v10.pdf`](trace_tempered_choice_v10.pdf).

The proof appendices are organized as one main narrative and one auxiliary
appendix:

- [`appendix_a_representation_v10.tex`](appendix_a_representation_v10.tex)
  assembles Appendix A from shared affine preliminaries, the pure-trace core,
  and completion of the representation theorem;
- [`appendix_a_affine_preliminaries_v10.tex`](appendix_a_affine_preliminaries_v10.tex)
  derives terminal affine structure, the finite-branch extension, one-branch
  insertion, and the relevance bridge;
- [`appendix_a_pure_trace_v10.tex`](appendix_a_pure_trace_v10.tex) proves the
  pure-trace characterization and its scale-coherence steps;
- [`appendix_a_completion_v10.tex`](appendix_a_completion_v10.tex) identifies
  the common material and trace scales, exact branch weights, and completes
  Theorem 1;
- [`appendix_b_auxiliary_results_v10.tex`](appendix_b_auxiliary_results_v10.tex)
  contains auxiliary results not required by the formal Theorem 1 endpoint.

Axioms A1--A8 are weak order, continuity, material relevance, trace relevance,
block coherence, record data processing, action data processing, and the
binary recordwise sure-thing principle. Appendix A derives the weak-and-strict
finite-branch extension from A1 and A5--A8.

From the repository root:

```bash
./scripts/build_paper.sh --check
```

Use `./scripts/build_paper.sh --update` after an intentional source change.
The build fixes its date and PDF metadata so independent builds are
byte-identical. Lean correspondence is documented in
[`../Certificate/CLAIM_MAP.md`](../Certificate/CLAIM_MAP.md) and
[`../Certificate/PAPER_PROOF_ROADMAP.md`](../Certificate/PAPER_PROOF_ROADMAP.md).
