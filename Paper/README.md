# Paper snapshots and Theorem 1 supplement

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

## Current Theorem 1 proof supplement

The current paper source is [`trace_tempered_choice_v3.tex`](trace_tempered_choice_v3.tex).
Its proof supplement is
[`theorem1_lean_faithful_appendix.pdf`](theorem1_lean_faithful_appendix.pdf),
with source split as follows:

- [`theorem1_lean_faithful_appendix.tex`](theorem1_lean_faithful_appendix.tex)
  is Appendix A: the Lean-faithful proof of the unique Theorem 1.
- [`theorem1_pure_trace_appendix.tex`](theorem1_pure_trace_appendix.tex) is
  Appendix B: the auxiliary pure-trace characterization and its full paper
  proof. It is generated verbatim from marked regions of v3.
- [`theorem1_lean_faithful_appendix_preview.tex`](theorem1_lean_faithful_appendix_preview.tex)
  is the standalone compilation wrapper.
- [`extract_lean_faithful_pure_trace.sh`](extract_lean_faithful_pure_trace.sh)
  regenerates Appendix B after the marked v3 source changes.

The exact closed Lean input for Appendix B is
`TraceableAgency.provedMainCharacterizationWithMoreover`. Its statement is
`(TraceAxioms F ↔ MIRep F) ∧ (TraceAxioms F → BlockSameScaleRep F)`. Appendix
A uses that proposition on the constant-payoff restriction, then carries out
the common-scale, deterministic-branch, payoff-telescope, and
sequentialization steps for Theorem 1. Appendix B preserves the paper's scalar
algebra order for readability; it explicitly records where the kernel proof
chooses its canonical representative earlier.

Regenerate and compile the supplement with:

```sh
./Paper/extract_lean_faithful_pure_trace.sh
cd Paper
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  -jobname=theorem1_lean_faithful_appendix \
  theorem1_lean_faithful_appendix_preview.tex
```
