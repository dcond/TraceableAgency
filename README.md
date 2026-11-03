# TraceableAgency

[![Formalization certificate](https://github.com/dcond/TraceableAgency/actions/workflows/theorem1-certificate.yml/badge.svg?branch=main)](https://github.com/dcond/TraceableAgency/actions/workflows/theorem1-certificate.yml?query=branch%3Amain)

Lean 4 verification of all numbered mathematical results in *A Preference for
Traceable Agency: An Axiomatization of Expected Utility plus Mutual Information*
(version 11), including the appendices.

Start with the [formalization certificate](Certificate/FORMALIZATION_CERTIFICATE.md)
for the precise scope, statement and hypothesis correspondence, and verification
commands. The current paper is available as a
[PDF](Paper/trace_tempered_choice_v11.pdf) and
[TeX source](Paper/trace_tempered_choice_v11.tex).

The verification includes the material-first representation proof, uniqueness,
the sign trichotomy, independence of all eight axioms, choice and measurement
results, moral-hazard implications, and the audience proposition. The
[completed v11 correspondence map](Certificate/V11_PROVED_RESULTS.md) identifies
the exact weaker-axiom interfaces and the final additions to the original
[Section 3](Certificate/SECTION3_VERIFICATION.md) and
[Section 4](Certificate/SECTION4_VERIFICATION.md) checks.

## Proof surface and trust

Import `TraceableAgency` for the complete public proof surface, including the
material-first representation proof and every numbered result in the paper.

For every finite payoff alphabet with at least two elements, the representation
theorem proves that Axioms A1--A8 are equivalent to expected payoff utility
plus a strictly positive global multiple of mutual information. The same
witnesses represent every finite block-supported cross-channel comparison.
The exact axiom bundle contains only A1--A8.

The [complete trust report](Certificate/TRUST_BOUNDARY.md) describes the source
and dependency audits, mathematical conventions, and fresh kernel replay.
There are no project mathematical axioms or proof holes. The audited
mathematical dependency closure uses only the standard Lean foundations
`propext`, `Classical.choice`, and `Quot.sound`.

The certificate distinguishes the paper's stated results from supplementary
unnumbered calculations. The kernel checks the formal deductions; the claim
maps make their correspondence with the paper reviewable.

## Repository layout

| Path | Role |
|---|---|
| [`TraceableAgency/Theorem1/MaterialCalibration/`](TraceableAgency/Theorem1/MaterialCalibration/) | Material-first representation proof and appendix interfaces |
| [`TraceableAgency/Section3/`](TraceableAgency/Section3/) | Uniqueness, signs, axiom independence, and payoff--trace separation |
| [`TraceableAgency/Section4/`](TraceableAgency/Section4/) | Trace tests, optimal choice, measurement, moral hazard, and audience results |
| [`TraceableAgency/V11.lean`](TraceableAgency/V11.lean) | Additional exact statements completing the v11 correspondence audit |
| [`TraceableAgency/Basic/`](TraceableAgency/Basic/) and [`TraceableAgency/Info/`](TraceableAgency/Info/) | Finite probability and information theory |
| [`TraceableAgency/Audit/`](TraceableAgency/Audit/) | Kernel, dependency, public-declaration, and specification audits |
| [`Certificate/`](Certificate/) | Current certificate, detailed claim maps, trust report, and byte manifest |
| [`Paper/`](Paper/) | Current paper source and reproducible PDF |

## Build and verify

Install Lean with [elan](https://lean-lang.org/install/) and Git, then clone
the repository. Elan selects **Lean 4.32.1** from
[`lean-toolchain`](lean-toolchain); [`lake-manifest.json`](lake-manifest.json)
fixes the exact mathlib and transitive dependency revisions.

```bash
git clone https://github.com/dcond/TraceableAgency.git
cd TraceableAgency
lake exe cache get
lake build TraceableAgency
```

Open the repository folder in VS Code with the Lean 4 extension to inspect
the declarations interactively. The ordinary build checks the public proofs.
For the complete audit, use Bash, Python 3.10 or later, and
[ripgrep](https://github.com/BurntSushi/ripgrep) on Linux, macOS, or WSL:

```bash
./scripts/check_trust_boundary.sh
```

This checks the complete repository manifest and pinned dependency
sources, rejects proof holes and unchecked mechanisms, rebuilds every project
Lean source, audits the raw mathematical dependency closure including private
helpers, and performs mandatory fresh kernel replay. TeX is not needed for
the Lean verification.

To reproduce the paper PDF, install TeX Live 2026 with `latexmk` and run:

```bash
./scripts/build_paper.sh --check v11
```

The [GitHub workflow](.github/workflows/theorem1-certificate.yml) runs the
complete audit and checks reproducible paper builds.

For focused checks, use `scripts/check_section3_certificate.sh` and
`scripts/check_section4_certificate.sh`. See the certificate for their scope
and the additional v11 statements included in the complete audit.

## Contributing, citation, and licences

For corrections or reproduction problems, open an
[issue](https://github.com/dcond/TraceableAgency/issues). See
[`CONTRIBUTING.md`](CONTRIBUTING.md) for the checks and generated files to
update when submitting a change.

Citation metadata is in [`CITATION.cff`](CITATION.cff); GitHub's **Cite this
repository** button gives the preferred paper citation. For the software,
cite Daniele Condorelli (2026), *TraceableAgency: Lean verification of
Trace-Tempered Choice*, version 11.0.0, and the commit used.

Project Lean source is
licensed under [Apache-2.0](LICENSE). The adapted Shannon proof retains its
[MIT licence and attribution](TraceableAgency/Vendor/Shannon/README.md).
The [paper's separate licence](Paper/LICENSE) reserves its copyright to
Daniele Condorelli; it is not relicensed by the software licence.
