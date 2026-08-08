# Claim map: `trace_tempered_choice_v3`, Theorem 1

## Source and verification boundary

- Informal source: `Paper/trace_tempered_choice_v3.tex` in the repository root.
- Result: Theorem 1, `thm:main`, lines 539--562.
- Lean statement: `TraceTemperedChoiceVerification.Theorem1Statement` in
  `Statements.lean`.
- Kernel-checked proof:
  `TraceTemperedChoiceVerification.trace_tempered_choice_v3_theorem1` in
  `Proof.lean`.
- Checked Appendix engine imported by `Axioms.lean`:
  `TraceableAgency.provedMainCharacterizationWithMoreover` from
  `TraceableAgency/MainTheorem.lean`, lines 109--114.  This is the closed
  pure-record characterization used at constant payoff.  No new Lean axiom or
  theorem-interface assumption is declared here.

## Domain correspondence

| Informal text | Source lines | Lean declaration |
|---|---:|---|
| Fixed finite payoff alphabet `O`, `|O| >= 2` | 326--327 | Outer `O` quantifier and `2 <= Fintype.card O` in `Theorem1Statement` |
| Nonempty finite actions `A` and records `R` | 326--330 | `FixedPayoffPrefFamily.rel`; every paper-relevant `A`/`R` binder has `Fintype`, `DecidableEq`, and `Nonempty` |
| Joint channel `K : A -> Delta(O x R)` | 327--330 | `Channel A (O × R)` |
| Primitive within-channel relation on `Delta(A)` | 332--338 | `FixedPayoffPrefFamily.rel` |
| Strict/symmetric parts | 391--393 | `FixedPayoffPrefFamily.strictRel`, `indiffRel`, `pairStrict`, `pairIndiff` |

The family has a genuinely fixed payoff coordinate.  It is not the existing
pure-record `TraceableAgency.PrefFamily`, whose entire output type varies and
has no distinguished payoff projection.

## Block environments

| Informal text | Source lines | Lean declaration |
|---|---:|---|
| Two-block `K sqcup L` with common payoff and tagged records | 364--381 | `commonPayoffBlockChannel` |
| Copies `q^0`, `p^1` | 373--381 | `leftBlockDist`, `rightBlockDist` |
| Pair shorthand `(q,K) >= (p,L)` | 387--393 | `pairWeak` |
| Arbitrary finite block family and copies `q_i^i` | 383--385 | `commonPayoffBlockFamilyChannel`, `commonPayoffBlockEmbed` |

The repository's generic block constructor has output
`(O × R) ⊕ (O × S)`.  The paper uses `O × (R ⊕ S)`, because only the record is
tagged.  `sumPayoffRecordEquiv` and `sigmaPayoffRecordEquiv` perform this exact
reassociation while retaining the common payoff coordinate.  This is a type
encoding, not a change in the visible random variable.

## Axioms A1--A8

| Informal clause | Source lines | Lean declaration |
|---|---:|---|
| A1 weak order | 345--346 | `A1_WeakOrder` |
| A2 closed graph in `(K,q,p)` for fixed alphabets | 348--354 | `A2_Continuity` |
| A3 duplication | 420--426 | `A3_BlockComparisonCoherence.duplication` |
| A3 irrelevant blocks | 427--433 | `A3_BlockComparisonCoherence.irrelevant_blocks` |
| Record processor and `KT` | 442--447 | `RecordProcessor`, `payoffPreservingRecordKernel`, `recordPostprocess` |
| A4 record data processing | 470--475 | `A4_RecordDataProcessing` |
| Action report, pushforward, and completion equation | 448--457 | `IsActionReportCompletion` |
| A5 action data processing | 477--483 | `A5_ActionDataProcessing` |
| Compound channel, reached branch, posterior | 458--466 | `commonPayoffCompound`, existing `BranchPositive`, existing `branchPosterior` |
| A6 weak branchwise implication | 485--495 | `A6_BranchwiseContinuationConsistency_Weak` |
| A6 reached-branch strictness | 496 | `A6_BranchwiseContinuationConsistency_Strict` |
| A7 material relevance | 502--508 | `A7_MaterialRelevance` |
| A8 positive trace orientation | 510--517 | `A8_PositiveTraceOrientation` |
| Combined hypotheses | 542 | `TraceTemperedAxioms` |

### A6 reading

Both continuation profiles use the same branch-dependent record family
`Rec y`.  This is the weakest faithful reading of v3: the construction directly
before A6 introduces `K^y : A -> Delta(O × R_y)`, and A6 then quantifies over
profiles `{K^y}` and `{L^y}` without introducing a second record family.  It
also agrees with the checked pure-record formalization's explicitly named
paper-faithful A6.  Allowing unrelated record families for the two profiles is
a useful stronger formulation, but it is not silently imposed here.

### Continuity reading

The paper says that the preference graph is closed in the usual finite
Euclidean product topology.  `A2_Continuity` states sequential closedness using
the repository's coordinatewise `ChannelConverges` and `DistConverges`.  Finite
Euclidean spaces are metrizable and first countable, so these formulations are
equivalent.  No cross-alphabet convergence is imposed.

### Null reported actions

`IsActionReportCompletion` uses the paper's undivided joint-law equality

```text
(qS)(b) * Khat(b,z) = sum_a q(a) S(b|a) K(a,z).
```

When `(qS)(b)=0`, nonnegativity makes the right side zero and the equation leaves
the row of `Khat` unrestricted.  A5 quantifies over every such completion.

## Representation and conclusion

| Informal text | Source lines | Lean declaration |
|---|---:|---|
| Induced visible distribution and MI | 525--537 | Existing `mutualInfo q K` with visible type `O × R` |
| Expected material utility | 536--537, 550 | `expectedPayoffUtility` |
| `V = E[u(O)] + lambda I(A;O,R)` | 543--551 | `traceTemperedValue` |
| One `u,lambda` for every `A,R,K,q,p` | 543--552 | Existential binders precede `WithinChannelRepresentation` in `Theorem1Statement` |
| `u` nonconstant, `lambda > 0` | 543 | Explicit conjuncts in `Theorem1Statement` |
| Same-scale finite-block moreover clause | 554--560 | `SameWitnessBlockRepresentation` and second conjunct of `Theorem1Statement` |

`mutualInfo` is defined in the imported checked development using Lean's
natural logarithm.  The paper permits any one fixed logarithm base; changing
base multiplies mutual information by a positive constant, which is absorbed
by the existential positive `lambda`.  Thus choosing natural logs neither
strengthens nor weakens the result.

The same-witness clause uses one existentially chosen `u,lambda` for both the
within-channel representation and all block comparisons.  This is the weakest
literal rendering of "represented on the same scale".  It does not strengthen
the prose to a claim about every possible representing pair; nor does it weaken
the paper's quantifier order to `for every environment, there exist u and
lambda` or allow fresh witnesses for the block clause.

## Empty types and computational structure

Every action or record alphabet that appears as an actual paper environment is
explicitly nonempty.  `Nontrivial A` in A8 is the finite-type rendering of
`|A| >= 2` and supplies nonemptiness.  General block index types are also marked
nonempty; the quantified distinct indices already imply this mathematically.

`DecidableEq` arguments support the repository's finite constructions and do
not add a behavioral or mathematical hypothesis.

## Verification result and proof correspondence

The final declaration has exactly the type `Theorem1Statement`; the proof does
not replace it by a strengthened premise or a weakened conclusion.  Its main
checked steps correspond to the informal proof as follows.

| Informal proof role | Lean declarations |
|---|---|
| Apply the Appendix-D characterization to constant-payoff experiments | `inducedPure_traceAxioms`, `inducedPure_MIRep`, `constantPayoff_pairWeak_iff_mutualInfo` in `PureTrace.lean`; ultimately `TraceableAgency.provedMainCharacterizationWithMoreover` |
| Obtain affine utilities on marked terminal laws and normalize them on the common material scale | `normalizedMarkedAffineUtilityRepresentation`, `normalizedMarkedUtility_payoffLottery` |
| Identify one common positive information coefficient across finite full-support priors | `globalTraceLambda`, `globalTraceLambda_pos`, `normalizedMarkedUtility_constantLow_eq_globalTraceLambda_mul_mutualInfo` |
| Delete zero-prior actions without changing behavior or value | `pairWeak_iff_supportRestriction`, `traceTemperedValue_restrictToSupport` |
| Insert a continuation at one reached branch, including boundary posteriors | `normalizedMarkedUtility_supportBranchInsertion` |
| Identify the branch insertion coefficient with the reached probability | `supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport` |
| Cover singleton-support branches without a convention or new axiom | `positiveBranchPayoffIncrementFormula`, using the exact independent lifted-Bool dummy bridge |
| Sum deterministic terminal-payoff branches | `normalizedMarkedUtility_payoffBranchFormula` |
| Reduce an arbitrary payoff-record channel to its terminal-payoff sequentialization | `normalizedMarkedUtility_sequentializedChannel` |
| Obtain arbitrary-prior within-channel and same-witness block representations | `representationClauses_of_fullSupportNormalizedValueFormula` |
| Prove the converse A1--A8 implication | `traceTemperedAxioms_of_representation` in `Benchmark.lean` |

The preliminary counterexample pass covered zero branch masses, singleton
action alphabets, boundary posteriors, null action-report rows, and degenerate
continuations.  These cases are proved inside the final path rather than
discarded: zero branches have identical marked laws, singleton action spaces
have zero mutual information, and boundary posteriors are restricted to their
positive support and then lifted back exactly.  No counterexample was found.

## Axiom and kernel audit

`Axioms.lean` declares no extra axiom.  Lean's `#print axioms` command reports
only the standard dependencies `propext`, `Classical.choice`, and `Quot.sound`
for `trace_tempered_choice_v3_theorem1`.  The verification sources contain no
`sorry`, `admit`, opaque placeholder, or unsafe declaration.  The checked
build target is:

```text
lake build Theorem1Verification
Build completed successfully (8667 jobs).
```
