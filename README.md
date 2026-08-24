# TraceableAgency

[![Theorem 1 certificate](https://github.com/dcond/TraceableAgency/actions/workflows/theorem1-certificate.yml/badge.svg)](https://github.com/dcond/TraceableAgency/actions/workflows/theorem1-certificate.yml)

Lean 4 verification of Theorem 1 in *A Preference for Traceable Agency: An
Axiomatization of Expected Utility plus Mutual Information* (version 10).

## Verified theorem

```lean
TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1 :
  TraceableAgency.Theorem1.Theorem1StatementV10
```

For every finite payoff alphabet with at least two elements, the theorem proves
that Axioms (A1)--(A8) are equivalent to representation by expected payoff
utility plus a strictly positive global multiple of mutual information.  The
same witnesses represent every finite block-supported cross-channel
comparison.

The v10 statement and axiom bundle are the canonical public API.  The bundle
contains exactly A1--A8, and the theorem adds no premise beyond those eight
behavioral hypotheses.

The project declares no additional mathematical axiom.  The final theorem's
recursively collected kernel foundations are exactly `propext`,
`Classical.choice`, and `Quot.sound`.

## Repository layout

| Path | Role |
|---|---|
| [`TraceableAgency/Theorem1/`](TraceableAgency/Theorem1/) | Exact v10 statement and proof |
| [`TraceableAgency/PureTrace/`](TraceableAgency/PureTrace/) | Auxiliary constant-payoff characterization |
| [`TraceableAgency/Basic/`](TraceableAgency/Basic/) and [`TraceableAgency/Info/`](TraceableAgency/Info/) | Finite probability and information theory |
| [`TraceableAgency/Audit/`](TraceableAgency/Audit/) | Kernel, dependency, public-declaration, and mechanical-specification audits |
| [`Certificate/`](Certificate/) | Claim map, formalization certificate, generated Theorem 1 specification, proof roadmap, and byte manifest |
| [`Paper/`](Paper/) | Authoritative v10 TeX sources and reproducible PDF |

## Reproduce

```bash
lake exe cache get
lake build TraceableAgency
lake build TraceableAgency.Audit
./scripts/build_theorem1_spec.sh --check
./scripts/build_paper.sh --check
./scripts/check_theorem1_certificate.sh
```

The certificate rejects proof holes and project axioms, checks the complete
repository manifest, rebuilds the v10 paper, audits the final declaration's
transitive dependencies, checks the recursively generated Theorem 1
specification, and replays the v10 certificate module with `leanchecker
--fresh`.

## Paper and correspondence

- [Paper source](Paper/trace_tempered_choice_v10.tex)
- [Compiled paper](Paper/trace_tempered_choice_v10.pdf)
- [Formalization certificate](Certificate/FORMALIZATION_CERTIFICATE.md)
- [Mechanical formal specification of Theorem 1](Certificate/THEOREM1_FORMAL_SPECIFICATION.md)
- [Claim map](Certificate/CLAIM_MAP.md)
- [Proof roadmap](Certificate/PAPER_PROOF_ROADMAP.md)

Citation metadata is in [`CITATION.cff`](CITATION.cff). Lean source is licensed
under Apache-2.0; the paper remains © Daniele Condorelli and is not relicensed
by the source-code licence.
