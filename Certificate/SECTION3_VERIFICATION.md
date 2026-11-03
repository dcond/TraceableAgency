# Section 3 verification, paper v11

This certificate covers the results after the representation theorem in
Section 3 of [the v11 source snapshot](../Paper/trace_tempered_choice_v11.tex).
The representation theorem itself is already established by the material-first
route. Its formal A1–A8 statement is identical to the existing v10 interface.
The original proof, v10 paper, and original theorem names are preserved.

The branch `codex/section3-completion` starts at commit `d23e4d8` on
`codex/material-branch-calibration`.

## Paper-to-Lean map

Names below have prefix `TraceableAgency.Section3` unless another prefix is
shown. Import `TraceableAgency.Section3` to load the complete new surface.

| Paper claim | Checked declaration |
|---|---|
| Proposition 2(i): common-scale representations are precisely increasing transforms on the full half-line | `uniqueness_for_representation`, `commonScale_iff_strictMono_transform` |
| Full value range `[min u, ∞)` | `valueIndex_range` |
| Proposition 2(ii): numerical branch additivity is equivalent to a positive affine transformation | `branchAdditive_iff_positiveAffine` |
| Uniqueness from A1–A8, using the material-first witnesses | `uniqueness_of_axioms` |
| Utility and information-weight transformation | `traceTempered_parameters_unique` |
| Uniqueness after any two common distinct utility anchors | `traceTempered_parameters_unique_of_common_anchors` |
| Normalised information coefficient | `normalized_trace_coefficient_unique` |
| Corollary 3: positive, negative, and zero information weights | `TraceableAgency.Theorem1.Section3.sign_trichotomy` |
| Negative and neutral converse directions | `TraceableAgency.Theorem1.Section3.negative_axioms_of_representation`, `TraceableAgency.Theorem1.Section3.neutral_axioms_of_representation` |
| Positive trace relevance conflicts with reversed record processing, with either action-processing orientation | `TraceableAgency.Theorem1.Section3.positive_trace_incompatible_negative_record` |
| Proposition 4: each axiom is independent of the other seven | `axioms_independent` |
| Explicit non-derivability formulation | `no_axiom_implied_by_other_seven` |
| Conditional record-noise penalty satisfies exactly the seven retained axioms | `Independence.noise_counterexample`, `Independence.noiseScore_eq` |
| Gini posterior reduction satisfies exactly the seven retained axioms | `Independence.gini_counterexample` |
| Identical-row merge raises the Gini score from `3/8` to `1/2` | `Independence.giniMerge_information`, `Independence.giniFair_reveal_information`, `Independence.giniFamily_not_a7` |
| Every positive information cap satisfies A1–A7 and violates A8 | `Independence.satiation_counterexample` |

The claim map concerns Section 3, not all of Appendix B or the paper's choice
and moral-hazard applications.

## Exact mathematical boundary

`CommonScaleRepresentation` includes both within-channel comparisons and
arbitrary finite block comparisons, with the same index. The ordinal
transformation is defined on the entire attainable half-line, with no added
continuity assumption. `BranchAdditiveIndex` is the paper's numerical
continuation-difference identity, using a common continuation record alphabet.
All priors, including boundary priors, are admitted.

The sign theorem shares precisely A1–A3, A5, and A8 across its three clauses.
Negative processing reverses the canonical cross-channel comparison. The
equivalence with reversal inside the original block is derived from the
oriented axioms, not assumed. Neutral processing uses literal indifference
inside that block; it reduces experiments to material lotteries. The neutral
material scale is proved without positive trace relevance. All three clauses
include the same-witness finite-block representation.

`PaperAxiom F i` is the original predicate from `Theorem1/Statements.lean`,
with indices `0` through `7` corresponding to A1 through A8. The independence
theorem constructs a preference family on every fixed finite payoff alphabet
with at least two elements. Each witness satisfies the other seven full
axioms; only the omitted predicate fails.

## Independence constructions

Write `U` for expected payoff utility and `I` for mutual information.

| Omitted axiom | Witness |
|---|---|
| A1 | Coordinatewise order on `(U,I)` |
| A2 | Lexicographic order, prioritising `U` |
| A3 | `I` alone |
| A4 | `U` alone |
| A5 | `U + I + ∏ₐ q(a)` |
| A6 | `U + 2I − H(O,R) = U + I − H(O,R \| A)` |
| A7 | `U + I + H(q)`; the paper's `U + Gini reduction` is independently verified too |
| A8 | `U + min(I,c)`, for every `c > 0` |

The paper now uses the checked product-bonus witness for A5 and the independent
public-coin witness for A8. The product bonus vanishes on all canonical two-block
comparisons; duplication removes it from a full-support lottery. The first A7
witness is an additional shorter construction: the added prior entropy cancels in A6 and A8
comparisons but increases under an action processor that adds unrecorded
randomisation. The separate Gini proof includes continuity at null outputs,
garbling monotonicity, the compound chain identity, and the stated merge.
The paper allows any positive coefficient on conditional record noise; the
formal A6 counterexample fixes that coefficient at one, which suffices for
the independence claim. The paper retains the more general readable argument.

## Reproduction and trust

Use the repository's pinned Lean and mathlib versions:

```sh
lake exe cache get
./scripts/check_section3_certificate.sh
```

The script verifies the complete byte manifest, checks source hygiene, builds
the new public entry point, runs recursive dependency audits, checks the
material-first and original theorem routes, and replays the new audit module
with `leanchecker --fresh`.

`Section3/Audit.lean` traverses the actual types and proof bodies of the listed
endpoints. It rejects kernel foundations other than `propext`,
`Classical.choice`, and `Quot.sound`, and rejects dependence on the original
preference-to-representation endpoints. Generic finite probability, affine
utility, and entropy lemmas remain reusable. No mathematical axiom is added.

As with the existing certificate, a reader must check that the displayed
formal statements and definitions express the paper's claims. The kernel
then checks the deductions from those statements and the listed foundations.
