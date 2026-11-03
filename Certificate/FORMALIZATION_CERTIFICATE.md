# Formalization certificate: paper v11

All **34 numbered mathematical results** in
[*A Preference for Traceable Agency*, version 11](../Paper/trace_tempered_choice_v11.pdf),
including the results in Appendices A and B, have been formalised and
machine-checked in Lean 4. This includes the numbered remarks with mathematical
content. The verified scope is their stated conclusions and hypotheses;
individual formal proofs may take a different route from the paper.

The [paper source](../Paper/trace_tempered_choice_v11.tex), the detailed claim
maps below, and the linked Lean declarations make the correspondence
reviewable. Import [`TraceableAgency`](../TraceableAgency.lean) for the complete
public surface. [`TraceableAgency.V11`](../TraceableAgency/V11.lean) exports the
additional statements that completed the v11 correspondence audit.

## Result index

The numbers refer to the current v11 paper. Together these rows cover every
numbered result.

| Results | Content | Detailed correspondence |
|---|---|---|
| 1 | Representation by expected payoff utility plus a positive multiple of mutual information, including common-scale block comparisons | [Material-first proof](../TraceableAgency/Theorem1/MaterialCalibration/Proof.lean); [exact formal specification](THEOREM1_FORMAL_SPECIFICATION.md) |
| 2–4 | Uniqueness, sign trichotomy, independence of all eight axioms | [Section 3 certificate](SECTION3_VERIFICATION.md) |
| 5, 23 | Trace test and qualitative trace preferences | [Section 4: trace test](SECTION4_VERIFICATION.md#trace-test) |
| 6–7, 24–27 | Optimal randomization, logit, binary classification, support, multiplicity, and the IIA example | [Section 4: optimal randomization](SECTION4_VERIFICATION.md#optimal-randomization); [completed endpoint limits](V11_PROVED_RESULTS.md#remaining-stated-results-closed) |
| 8, 31–33 | Elicitation, the information price, willingness to pay, and implementation controls | [Section 4: measurement](SECTION4_VERIFICATION.md#measurement); [zero-dilution completion](V11_PROVED_RESULTS.md#remaining-stated-results-closed) |
| 9–21 | Appendix A: structural lemmas, affine fibres, material calibration, entropy identification, and deterministic continuation | [Exact weaker-axiom interfaces](V11_PROVED_RESULTS.md#actual-axiom-use-rather-than-bundled-parameters); [completed Appendix A statements](V11_PROVED_RESULTS.md#remaining-stated-results-closed); [material-first modules](../TraceableAgency/Theorem1/MaterialCalibration/) |
| 22 | No payoff–trace complementarity | [Checked corollary](../TraceableAgency/Section3/V11NoComplementarity.lean) |
| 28–30 | Record garbling, recorded public coins, and more-capable dominance without garbling | [Section 4: records](SECTION4_VERIFICATION.md#records-and-moral-hazard); [more-capable comparison](../TraceableAgency/Section4/MoreCapable.lean); [counterexample at any payoff](../TraceableAgency/Section4/MoreCapablePayoff.lean) |
| 34 | Entropy-reduction audience reward iff the observer has the correct prior | [Checked audience theorem](../TraceableAgency/Section4/Interpretation/Audience.lean); [scope and hypotheses](V11_PROVED_RESULTS.md#remaining-stated-results-closed) |

The [Section 4 certificate](SECTION4_VERIFICATION.md) also maps the checked
moral-hazard applications, including incentive thresholds, team limits, and
compensation after adding a signal.

## Representation and exact hypotheses

The material-first public endpoint is

```lean
TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1_material :
  TraceableAgency.Theorem1.Theorem1StatementV10
```

<details>
<summary>Compatibility and the original proof</summary>

The `V10` names are retained for compatibility: the representation statement
and A1–A8 axiom bundle are unchanged in v11. The original public endpoint,
`TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1`, remains
proved as well. The [original v10 certificate](FORMALIZATION_CERTIFICATE_V10.md)
is preserved verbatim as a record of that proof route and its original scope.

</details>

The theorem fixes a finite payoff alphabet with at least two elements and
ranges over arbitrary finite nonempty action and record alphabets, including
boundary priors. Its preference premise contains exactly A1–A8. Intermediate
normalizations, full-support restrictions, and representation interfaces are
derived or constructed before use, not extra assumptions of the theorem.

The weaker assumptions stated in Appendix A are checked separately. In
particular, Lemma 11(b) uses A1, A2, A5–A8 without either relevance axiom;
Lemma 13 adds A3 but does not require A4. The
[completion map](V11_PROVED_RESULTS.md) identifies these precise endpoints and
the arbitrary-prior continuation identities. Application results retain their
stated model and parameter assumptions.

## Verification and reproduction

A complete project-source rebuild, raw dependency audit, and fresh kernel
replay passed on **2026-11-03**, as recorded in the
[proved-result completion report](V11_PROVED_RESULTS.md#scope-and-verification).
The mathematical Lean sources are unchanged from proof-completion commit
`5f7e8e8`; subsequent paper revisions preserve the stated results and hypotheses.
The [trust report](TRUST_BOUNDARY.md) gives the source inventory, dependency
pins, checks, and their limitations.

With the repository's pinned toolchain and dependencies installed, reproduce
the complete check with:

```sh
lake exe cache get
./scripts/check_trust_boundary.sh
```

This command rebuilds every project source, including private helpers and the
vendored Shannon proof, audits actual declaration types and bodies, and runs
mandatory fresh `leanchecker` replay. The only foundational axioms reached
are `propext`, `Classical.choice`, and `Quot.sound`. There are no project
mathematical axioms or proof holes. The
[byte manifest](SHA256SUMS) records the repository files used by the checks.

## Scope and conventions

“All numbered mathematical results” does not mean that every intermediate
calculation or unnumbered explanatory claim has a separate formal proof.
Examples outside that claim include the exact team Taylor remainder, the
additional posterior-law equality observation inside the garbling proof, and
unrestricted extended-real forecasting interpretations. The
[scope notes](V11_PROVED_RESULTS.md#scope-and-verification) distinguish these
from the completed stated results.

Lean uses natural logarithms. The paper's other fixed bases correspond to
rescaling the information coefficient; a general-base transport theorem is
not separately formalised. Null-event, support, comparison-environment, and
other conventions are documented in the [trust report](TRUST_BOUNDARY.md).

The kernel checks deductions from formal statements; it does not read the TeX
or decide whether the definitions capture the intended economics. The claim
maps and explicit hypotheses support that human semantic check. The
[historical correspondence audit](V11_CORRESPONDENCE_AUDIT.md) records the
pre-completion findings; the completion map above records their resolution
within the stated scope.
