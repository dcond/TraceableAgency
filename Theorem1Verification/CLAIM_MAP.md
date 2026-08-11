# Claim map: `trace_tempered_choice_v3`, Theorem 1

## Source and verification boundary

- Informal source: `Paper/trace_tempered_choice_v3.tex` in this repository.
- Result: Theorem 1, `thm:main`, lines 408--431.
- Lean statement: `TraceTemperedChoiceVerification.Theorem1Statement` in
  `Statements.lean`.
- Kernel-checked proof:
  `TraceTemperedChoiceVerification.trace_tempered_choice_v3_theorem1` in
  `Proof.lean`.
- Checked Appendix engine imported by `Axioms.lean`:
  `TraceableAgency.provedMainCharacterizationWithMoreover` from
  `TraceableAgency/MainTheorem.lean`.  Its sufficiency direction now closes
  through `SufficiencyStatement_of_paperReduction` and
  `MIRep_of_TraceAxioms_paperReduction`: the direct pure-trace reduction used
  at constant payoff.  No new Lean axiom or theorem-interface assumption is
  declared here, and the public theorem does not transitively use the older
  posterior-integral / `FinalHMInterface` route.

## Domain correspondence

| Informal text | Source lines | Lean declaration |
|---|---:|---|
| Fixed finite payoff alphabet `O`, `|O| >= 2` | 191 | Outer `O` quantifier and `2 <= Fintype.card O` in `Theorem1Statement` |
| Nonempty finite actions `A` and records `R` | 191--192 | `FixedPayoffPrefFamily.rel`; every paper-relevant `A`/`R` binder has `Fintype`, `DecidableEq`, and `Nonempty` |
| Joint channel `K : A -> Delta(O x R)` | 192--196 | `Channel A (O × R)` |
| Primitive within-channel relation on `Delta(A)` | 197--202 | `FixedPayoffPrefFamily.rel` |
| Strict/symmetric parts | 257--263 | `FixedPayoffPrefFamily.strictRel`, `indiffRel`, `pairStrict`, `pairIndiff` |

The family has a genuinely fixed payoff coordinate.  It is not the existing
pure-record `TraceableAgency.PrefFamily`, whose entire output type varies and
has no distinguished payoff projection.

## Block environments

| Informal text | Source lines | Lean declaration |
|---|---:|---|
| Two-block `K sqcup L` with common payoff and tagged records | 233--242 | `commonPayoffBlockChannel` |
| Copies `q^0`, `p^1` | 243--251 | `leftBlockDist`, `rightBlockDist` |
| Pair shorthand `(q,K) >= (p,L)` | 256--263 | `pairWeak` |
| Arbitrary finite block family and copies `q_i^i` | 253--255 | `commonPayoffBlockFamilyChannel`, `commonPayoffBlockEmbed` |

The repository's generic block constructor has output
`(O × R) ⊕ (O × S)`.  The paper uses `O × (R ⊕ S)`, because only the record is
tagged.  `sumPayoffRecordEquiv` and `sigmaPayoffRecordEquiv` perform this exact
reassociation while retaining the common payoff coordinate.  This is a type
encoding, not a change in the visible random variable.

## Axioms A1--A8

| Informal clause | Source lines | Lean declaration |
|---|---:|---|
| A1 weak order | 214--215 | `A1_WeakOrder` |
| A2 closed graph in `(K,q,p)` for fixed alphabets | 217--223 | `A2_Continuity` |
| A3 duplication | 273--279 | `A3_BlockComparisonCoherence.duplication` |
| A3 irrelevant blocks | 280--286 | `A3_BlockComparisonCoherence.irrelevant_blocks` |
| Record processor and `KT` | 293--300 | `RecordProcessor`, `payoffPreservingRecordKernel`, `recordPostprocess` |
| A4 record data processing | 317--322 | `A4_RecordDataProcessing` |
| Action report, pushforward, and completion equation | 301--313 | `IsActionReportCompletion` |
| A5 action data processing | 324--330 | `A5_ActionDataProcessing` |
| Compound channel, reached branch, posterior | 334--349 | `commonPayoffCompound`, existing `BranchPositive`, existing `branchPosterior` |
| A6 weak branchwise implication | 353--363 | `A6_BranchwiseContinuationConsistency_Weak` |
| A6 reached-branch strictness | 364 | `A6_BranchwiseContinuationConsistency_Strict` |
| A7 material relevance | 370--376 | `A7_MaterialRelevance` |
| A8 positive trace orientation | 378--386 | `A8_PositiveTraceOrientation` |
| Combined hypotheses | 411 | `TraceTemperedAxioms` |

### A6 reading

Both continuation profiles use the same branch-dependent record family
`Rec y`.  V3 now states this explicitly by quantifying one finite family
`(R_y)` and channels `K^y, L^y : A -> Delta(O × R_y)`.  This exactly matches
the checked full-payoff and pure-record declarations.  Allowing unrelated
record families for the two profiles is a stronger formulation and is not
assumed by Theorem 1.

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
| Induced visible distribution and MI | 394--406 | Existing `mutualInfo q K` with visible type `O × R` |
| Expected material utility | 419 | `expectedPayoffUtility` |
| `V = E[u(O)] + lambda I(A;O,R)` | 412--420 | `traceTemperedValue` |
| One `u,lambda` for every `A,R,K,q,p` | 412--420 | Existential binders precede `WithinChannelRepresentation` in `Theorem1Statement` |
| `u` nonconstant, `lambda > 0` | 412 | Explicit conjuncts in `Theorem1Statement` |
| Same-scale finite-block moreover clause | 423--430 | `SameWitnessBlockRepresentation` and second conjunct of `Theorem1Statement` |

`mutualInfo` is defined in the imported checked development using Lean's
natural logarithm.  The paper permits any one fixed base greater than one.
For such a base, changing base multiplies mutual information by a positive
constant, which is absorbed by the existential positive `lambda`.  Thus
choosing natural logs neither strengthens nor weakens the result.

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
| Apply the pure-trace characterization (Appendix A) to constant-payoff experiments | The Appendix engine follows `finiteHersteinMilnorConclusion_direct_of_axioms` (fixed-prior quotient and direct HM), `paperCanonicalPosteriorValue` (canonical normalization), `posteriorProductGaugeData_of_axioms` (independent-product gauge), `directBranchChain_of_posteriorValue` (direct tangent branch scalar), `directCardinalFaceDefectCocycle` and `directCoherentRelabelingFaceScales` (nested-face/cardinality coherence), and `MIRep_of_paperInteractionCollapse` / `MIRep_of_TraceAxioms_paperReduction` (grouping recursion and mutual information).  The main proof then uses `inducedPure_traceAxioms_of_components`, `inducedPure_MIRep_of_components`, and `inducedPure_blockSameScale_of_components` in `PureTrace.lean`, together with `constantPayoff_pairWeak_iff_mutualInfo` in `TraceScaleTools.lean`; ultimately `TraceableAgency.provedMainCharacterizationWithMoreover`. |
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
for `MIRep_of_TraceAxioms_paperReduction`,
`provedMainCharacterizationWithMoreover`, and
`trace_tempered_choice_v3_theorem1`.

`PaperFaithfulDependencyAudit.lean` recursively follows declaration bodies and
types.  It reports closure sizes 21,201, 21,204, 39,982, and 40,797 for,
respectively, the direct MI endpoint, the public pure-trace sufficiency
statement, the public characterization, and Theorem 1, with zero occurrences
of the forbidden posterior-integral, global posterior-law continuity,
`marginalValue`, old all-representatives relabelling, or `FinalHMInterface`
declarations on every path.

The changed proof path contains no `sorry`, `admit`, unchecked hole, new axiom,
opaque placeholder, or unsafe declaration.  Both checked build targets are:

```text
lake build
lake build Theorem1Verification
Build completed successfully.
```

The default target includes `Theorem1Verification`; the explicit second
command records the exact certification target without relying on that
project default.
