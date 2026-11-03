# Paper v11 verification certificates

Start with the [current formalization certificate](FORMALIZATION_CERTIFICATE.md).
It covers all 34 numbered mathematical results in
[paper v11](../Paper/trace_tempered_choice_v11.pdf), including Appendices A and B,
and links their statements to the checked Lean results.

The principal documents are:

- [Current certificate and complete result index](FORMALIZATION_CERTIFICATE.md).
- [Section 3](SECTION3_VERIFICATION.md): uniqueness, signs, and axiom independence.
- [Section 4](SECTION4_VERIFICATION.md): trace tests, choice, measurement, records,
  and moral-hazard applications.
- [V11 proved-result completion](V11_PROVED_RESULTS.md): exact weaker-axiom
  interfaces and the completed appendix statements.
- [Trust boundary](TRUST_BOUNDARY.md): foundations, mathematical conventions,
  source/dependency checks, private declarations, and fresh kernel replay.
- [Mechanical Theorem 1 specification](THEOREM1_FORMAL_SPECIFICATION.md): the
  exact formal statement, A1–A8, and their recursive semantic dependencies.
- [Byte manifest](SHA256SUMS): digests of repository files other than the manifest.

The original proof and its public names remain available. The
[original v10 certificate](FORMALIZATION_CERTIFICATE_V10.md) is preserved
verbatim; the [original claim map](CLAIM_MAP.md) and
[v10 proof roadmap](PAPER_PROOF_ROADMAP.md) document that earlier route.
The [v11 correspondence audit](V11_CORRESPONDENCE_AUDIT.md) is explicitly a
historical baseline, superseded within the agreed result scope by the
completion report.

Import `TraceableAgency` for the complete public surface. Reproduce the full
source rebuild, raw dependency audit, and mandatory fresh kernel replay with:

```sh
lake exe cache get
./scripts/check_trust_boundary.sh
```

The only foundational axioms reached are `propext`, `Classical.choice`, and
`Quot.sound`. The kernel checks formal deductions; the result maps make their
correspondence with the paper reviewable. See the current certificate's
[scope and conventions](FORMALIZATION_CERTIFICATE.md#scope-and-conventions)
for the distinction between the verified results and unnumbered calculations.
