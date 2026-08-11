# Claim map: Theorem 1

## Certified boundary

- Paper result: `\label{thm:main}` in
  [`trace_tempered_choice_v3.tex`](../Paper/trace_tempered_choice_v3.tex).
- Lean proposition: `TraceableAgency.Theorem1.Theorem1Statement` in
  [`Statements.lean`](../TraceableAgency/Theorem1/Statements.lean).
- Kernel proof:
  `TraceableAgency.Theorem1.trace_tempered_choice_v3_theorem1` in
  [`Proof.lean`](../TraceableAgency/Theorem1/Proof.lean).
- Extra project axioms: none; [`Axioms.lean`](../TraceableAgency/Theorem1/Axioms.lean)
  declares nothing.

The proof declaration has exactly `Theorem1Statement` as its type. It cannot
change quantifier order, strengthen a hypothesis, or weaken a conclusion
without ceasing to typecheck.

## Domain and constructions

| Paper anchor | Mathematical role | Lean declaration |
|---|---|---|
| `sec:model` | Fixed finite payoff alphabet with cardinality at least two | Outer binders of `Theorem1Statement` |
| `sec:model` | Nonempty finite action and record alphabets | Binders of `FixedPayoffPrefFamily.rel` |
| `sec:model` | Joint channel from actions to payoff-record distributions | `Channel A (O × R)` |
| comparison-environment paragraph | Two-block environment and supported copies | `commonPayoffBlockChannel`, `leftBlockDist`, `rightBlockDist` |
| comparison-environment paragraph | Pair comparison inside one common environment | `pairWeak`, `pairStrict`, `pairIndiff` |
| comparison-environment paragraph | Arbitrary finite block environments | `commonPayoffBlockFamilyChannel`, `commonPayoffBlockEmbed` |
| `eq:record-processing` | Payoff-preserving record rewrite | `RecordProcessor`, `recordPostprocess` |
| `eq:action-processing` | Bayesian action-report completion, including null rows | `IsActionReportCompletion` |
| `eq:compound` | Shared-family sequential composition | `commonPayoffCompound` |

The paper writes block outputs with a common payoff coordinate and tagged
records, whereas the generic Lean block constructor initially tags whole
payoff-record pairs.
`sumPayoffRecordEquiv` and `sigmaPayoffRecordEquiv` implement the canonical
payoff-preserving reassociation. This is a relabeling of the same visible
random variable, not an additional assumption.

## Axiom correspondence

| Paper anchor | Paper clause | Lean declaration |
|---|---|---|
| `ax:weak-order` | (A1) weak order | `A1_WeakOrder` |
| `ax:continuity` | (A2) closed graph for fixed finite alphabets | `A2_Continuity` |
| `ax:block-coherence` | (A3) duplication and irrelevant blocks | `A3_BlockComparisonCoherence` |
| `ax:record-processing` | (A4) record data processing | `A4_RecordDataProcessing` |
| `ax:action-processing` | (A5) action data processing | `A5_ActionDataProcessing` |
| `ax:branch-consistency` | (A6) reached-branch weak and strict consistency | `A6_BranchwiseContinuationConsistency` |
| `ax:material-relevance` | (A7) strict comparison of two sure payoffs | `A7_MaterialRelevance` |
| `ax:positive-trace` | (A8) full revelation strictly beats no revelation | `A8_PositiveTraceOrientation` |
| `thm:main`, item (i) | All eight hypotheses together | `TraceTemperedAxioms` |

Faithfulness-sensitive details are literal in the Lean types:

- (A2) keeps the action, payoff, and record alphabets fixed while the channel
  and both lotteries converge.
- (A4) preserves payoff and permits the record processor to depend on payoff
  and record.
- (A5) quantifies over every completion satisfying the undivided joint-law
  equation, including unrestricted null reported-action rows.
- (A6) uses one dependent record family for both continuation profiles, ignores
  unreached branches, and requires weak improvement on every reached branch
  plus strict improvement on at least one reached branch for strictness.
- (A7) does not add a separate distinct-payoff premise.
- (A8) ranges over every nontrivial finite action type, full-support lottery,
  and payoff.

`A2_Continuity` uses coordinatewise sequential convergence. On these finite
Euclidean simplexes, this is equivalent to the paper's closed-set statement.

## Representation and conclusion

| Paper anchor | Paper clause | Lean declaration |
|---|---|---|
| `eq:mi` | Mutual information of action and visible payoff-record pair | `mutualInfo q K` |
| `eq:representation` | Expected payoff utility | `expectedPayoffUtility` |
| `eq:representation` | Expected utility plus a positive multiple of mutual information | `traceTemperedValue` |
| `thm:main`, item (ii) | One global nonconstant (u), one global λ>0 | Existentials preceding `WithinChannelRepresentation` |
| `thm:main`, moreover | Same witnesses for all finite block comparisons | `SameWitnessBlockRepresentation` and the second conjunct of `Theorem1Statement` |

Lean uses natural logarithms. Changing to any other fixed base greater than one
multiplies mutual information by a positive constant, absorbed by the
existential positive λ, so this does not alter the theorem.

## Proof correspondence

| Paper anchor | Lean route |
|---|---|
| `pt:prop:main` | `provedPureTraceCharacterization`; transported by `inducedPureConditions_of_components`, `inducedPureRepresentation_of_components`, and `inducedPureBlocks_of_components` |
| `lf:lem:terminal-affine` | `normalizedMarkedAffineUtilityRepresentation` |
| `lf:lem:material-scale` | `normalizedMarkedUtility_payoffLottery` and the material-scale normalization modules |
| `lf:lem:trace-scale` | `globalTraceLambda`, `globalTraceLambda_pos`, `normalizedMarkedUtility_constantLow_eq_globalTraceLambda_mul_mutualInfo` |
| `lf:lem:branch-increment` | `normalizedMarkedUtility_supportBranchInsertion`, `supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport`, `positiveBranchPayoffIncrementFormula` |
| `lf:lem:deterministic-assembly` | `normalizedMarkedUtility_payoffBranchFormula`, `normalizedMarkedUtility_sequentializedChannel` |
| `thm:main` | `representationClauses_of_fullSupportNormalizedValueFormula`, `theorem1Statement_of_positiveBranchPayoffIncrement`, `trace_tempered_choice_v3_theorem1` |

The pure-trace public import graph contains the current Herstein--Milnor,
product, branch, face, grouping, and Shannon route. Its compatibility umbrella
is not publicly imported, and the transitive dependency audit forbids every
superseded stronger declaration from the final theorem's closure.

## Kernel audit

[`TraceableAgency/Audit/Axioms.lean`](../TraceableAgency/Audit/Axioms.lean)
recursively checks the public endpoints against the exact whitelist:

```text
propext
Classical.choice
Quot.sound
```

[`TraceableAgency/Audit/Dependencies.lean`](../TraceableAgency/Audit/Dependencies.lean)
recursively rejects the superseded posterior-integral, global
posterior-law-continuity, `FinalHMInterface`, and all-representatives
relabeling routes. The certificate script also rejects `sorry`, `admit`, bare
project axioms, unsafe declaration construction, and a stale paper or manifest.
