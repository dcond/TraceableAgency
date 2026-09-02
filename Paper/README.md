# Paper

The authoritative source is
[`trace_tempered_choice_v10.tex`](trace_tempered_choice_v10.tex); its
reproducible build is
[`trace_tempered_choice_v10.pdf`](trace_tempered_choice_v10.pdf).  The source
is self-contained: Appendix A proves Theorem 1 and Appendix B collects the
auxiliary results that the formal Theorem 1 endpoint does not cover.

Axioms A1--A8 are weak order, continuity, material relevance, trace relevance,
block coherence, record data processing, action data processing, and the
binary recordwise sure-thing principle.  Appendix A derives the weak-and-strict
finite-branch extension from A1 and A5--A8.

From the repository root:

```bash
./scripts/build_paper.sh --check
```

Use `./scripts/build_paper.sh --update` after an intentional source change.
The build fixes its date and PDF metadata so independent builds are
byte-identical.  Lean correspondence is documented in
[`../Certificate/CLAIM_MAP.md`](../Certificate/CLAIM_MAP.md) and
[`../Certificate/PAPER_PROOF_ROADMAP.md`](../Certificate/PAPER_PROOF_ROADMAP.md).
