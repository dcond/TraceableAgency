# TraceableAgency

[![Theorem 1 certificate](https://github.com/dcond/TraceableAgency/actions/workflows/theorem1-certificate.yml/badge.svg)](https://github.com/dcond/TraceableAgency/actions/workflows/theorem1-certificate.yml)

Lean 4 verification of Theorem 1 in *A Preference for Traceable Agency: An
Axiomatization of Expected Utility plus Mutual Information* (version 3).

## Verified theorem

```lean
TraceableAgency.Theorem1.trace_tempered_choice_v3_theorem1 :
  TraceableAgency.Theorem1.Theorem1Statement
```

For every finite payoff alphabet with at least two elements, the theorem proves
that Axioms (A1)--(A8) are equivalent to representation by expected payoff
utility plus a strictly positive global multiple of mutual information. The
same witnesses also represent every finite block-supported cross-channel
comparison.

The project declares no additional mathematical axiom. The final theorem's
recursively collected kernel foundations are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Repository layout

| Path | Role |
|---|---|
| [`TraceableAgency/Theorem1/`](TraceableAgency/Theorem1/) | Statement and proof of the paper's Theorem 1 |
| [`TraceableAgency/PureTrace/`](TraceableAgency/PureTrace/) | Auxiliary constant-payoff characterization used by the proof |
| [`TraceableAgency/Basic/`](TraceableAgency/Basic/) and [`TraceableAgency/Info/`](TraceableAgency/Info/) | Finite probability and information theory |
| [`TraceableAgency/Vendor/Shannon/`](TraceableAgency/Vendor/Shannon/) | Vendored finite Shannon theorem, with its own provenance and licence |
| [`TraceableAgency/Audit/`](TraceableAgency/Audit/) | Compile-time kernel-axiom and dependency audits |
| [`Certificate/`](Certificate/) | Claim map, formalization certificate, proof roadmap, and byte manifest |
| [`Paper/`](Paper/) | Authoritative TeX sources and reproducible PDF |

The compatibility umbrella
[`TraceableAgency/PureTrace/Compatibility.lean`](TraceableAgency/PureTrace/Compatibility.lean)
is not imported by the public theorem. The transitive dependency audit also
rejects every superseded stronger route, including compatibility declarations
that remain colocated with live implementation lemmas.

## Reproduce

The repository pins Lean and mathlib. From the repository root:

```bash
lake exe cache get
lake build TraceableAgency
lake build TraceableAgency.Audit
./scripts/build_paper.sh --check
./scripts/check_theorem1_certificate.sh
```

The certificate checks the complete repository manifest, rejects proof holes
and project axioms, builds the statement and proof, runs both compile-time
audits, checks the reproducible PDF, and replays the final proof with
`leanchecker --fresh`.

## Paper and correspondence

- [Paper source](Paper/trace_tempered_choice_v3.tex)
- [Compiled paper](Paper/trace_tempered_choice_v3.pdf)
- [Formalization certificate](Certificate/FORMALIZATION_CERTIFICATE.md)
- [Claim map](Certificate/CLAIM_MAP.md)
- [Proof roadmap](Certificate/PAPER_PROOF_ROADMAP.md)

## Citation and licence

Citation metadata is in [`CITATION.cff`](CITATION.cff). Lean source is licensed
under Apache-2.0; the paper remains © Daniele Condorelli and is not relicensed
by the source-code licence.
