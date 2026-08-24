# Claim map: Theorem 1, version 10

## Certified boundary

- Paper result: `thm:main` in
  [`trace_tempered_choice_v10.tex`](../Paper/trace_tempered_choice_v10.tex).
- Exact proposition: `TraceableAgency.Theorem1.Theorem1StatementV10` in
  [`Statements.lean`](../TraceableAgency/Theorem1/Statements.lean).
- Public proof:
  `TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1` in
  [`Proof.lean`](../TraceableAgency/Theorem1/Proof.lean).
- Mechanical inventory: recursively generated Lean and mathematical forms in
  [`THEOREM1_FORMAL_SPECIFICATION.md`](THEOREM1_FORMAL_SPECIFICATION.md).
- Extra project axioms: none; the theorem-side
  [`Axioms.lean`](../TraceableAgency/Theorem1/Axioms.lean) declares nothing.

`Theorem1StatementV10` and `TraceTemperedAxiomsV10` are the canonical
statement and eight-field axiom bundle. `Audit/V10Certificate.lean` checks
and prints their exact types and the public theorem's kernel axioms.

## Domain and constructions

| Paper anchor | Mathematical role | Lean declaration |
|---|---|---|
| `sec:model` | Fixed finite payoff alphabet, cardinality at least two | Outer binders of `Theorem1StatementV10` |
| `sec:model` | Nonempty finite action/record alphabets and joint channel | `FixedPayoffPrefFamily`, `Channel A (O × R)` |
| comparison environments | Two-block and finite-block comparisons | `commonPayoffBlockChannel`, `commonPayoffBlockFamilyChannel`, `pairWeak`, `pairStrict` |
| `eq:record-processing` | Payoff-preserving record rewrite | `RecordProcessor`, `recordPostprocess` |
| `eq:action-processing` | Exact action-processor joint-law completion, including null rows | `IsActionProcessorCompletion` |
| `eq:compound` | Branch-dependent sequential composition | `commonPayoffCompound` |
| displayed mutual-information formula | Finite likelihood-ratio sum, with zero-joint-mass summands set to zero | `mutualInfoLikelihoodRatio`, `mutualInfoLikelihoodRatio_eq_mutualInfo` |

The block record tag is reassociated without moving the common payoff
coordinate by `sumPayoffRecordEquiv` and `sigmaPayoffRecordEquiv`.

## Exact axioms

| Number | Paper clause | Lean declaration |
|---|---|---|
| A1 | weak order | `A1_WeakOrder` |
| A2 | fixed-alphabet closed graph, formalized as equivalent sequential closedness | `A2_Continuity` |
| A3 | two distinct sure outcomes strictly ranked in one fixed two-action, no-record channel | `A3_MaterialRelevance` |
| A4 | fair revealing lottery strictly beats fair nonrevealing lottery in one fixed four-action channel at one payoff `o*` | `A4_TraceRelevance` |
| A5 | duplication and irrelevant-block coherence | `A5_BlockComparisonCoherence` |
| A6 | payoff-preserving record data processing | `A6_RecordDataProcessing` |
| A7 | action data processing for every exact completion | `A7_ActionDataProcessing` |
| A8 | binary recordwise sure-thing biconditional at reached record 1 | `A8_RecordwiseSureThing` |
| A1--A8 | exact v10 bundle | `TraceTemperedAxiomsV10` |

Faithfulness-sensitive details are literal in these types:

- A3 and A4 are within-channel comparisons in canonical fixed benchmark
  channels, not cross-channel assumptions.
- A4 existentially chooses one payoff; it does not quantify over every payoff.
- A6 processors may depend on realized payoff and record but preserve payoff.
- A7 uses the undivided joint-law equation, so zero-mass processed-action rows
  remain arbitrary and every completion is quantified.
- A8 uses one common record alphabet for `K`, `L`, and `M`, preserves the
  common continuation `M`, and is silent when binary record 1 is null.
- `recordwiseSureThing_iff_finiteBranchContinuationConsistency` derives the
  weak-and-strict finite property used downstream; it is not an additional
  public premise.

(A2) is sequential closedness, equivalent to a closed graph on these finite
Euclidean simplexes.

## Appendix A correspondence

| Paper stage | Main Lean route |
|---|---|
| `lf:lem:bookkeeping`, `lf:lem:terminal-affine` | `PairOrder.lean`, `SupportDummy.lean`, `MarkedTerminal.lean`, `MarkedHM.lean` |
| `pt:lem:finite-branch-extension`, `pt:cor:one-branch-a8` | `FiniteBranchExtension.lean`, `BranchInsertion.lean`, `SupportBranchInsertion.lean` |
| `lem:relevance-bridge` | `materialRelevance_bridge`, `traceRelevance_bridge`, `traceTemperedBridgeAxioms_of_v10` |
| `pt:prop:main`: affine fibres and support transport | `PureTrace/Proof/Posterior.lean`, `Affine.lean`, `PureTrace/Support/SupportRestriction.lean` |
| product, branch, and face scale coherence | `ProductGauge.lean`, `Branch.lean`, `FaceCoherence.lean`, `Scales.lean` and their support modules |
| `pt:lem:faddeevsketch` | `EntropyReduction.lean`, `GenericFaddeev.lean`, `provedPureTraceCharacterization` |
| `lf:lem:material-scale` | `MaterialUtility.lean`, `NormalizedMarked.lean`, `CommonMarkedScale.lean` |
| `lf:lem:trace-scale` | `PureMarkedEmbedding.lean`, `GlobalTraceScale.lean`, `ConstantTraceAnchorGeneral.lean` |
| arbitrary-continuation insertion against the all-`o*` background, nontrivial reached support | `BranchInsertion.lean`, `SupportBranchInsertion.lean`, `BranchScaleIdentification.lean` |
| deterministic payoff increment, including singleton reached support | `DummyBranchBridge.lean`, `PositiveBranchIncrement.lean` |
| deterministic crossed backgrounds and assembly | `PayoffBranchBackground.lean`, `PayoffBranchTelescope.lean` |
| arbitrary channels, boundaries, and final order | `FullSupportValueAssembly.lean`, `Sequentialization.lean`, `ValueSupport.lean`, `RepresentationAssembly.lean` |
| converse | `Benchmark.lean` |

The relevance bridge chooses the A4 witness `o*` and proves
`PositiveTraceOrientationAt F o*` without moving to another payoff.  Material
normalization and trace normalization are therefore formally separate.

The paper states the reached-branch lemma for arbitrary continuations and
backgrounds. Lean proves the arbitrary-continuation affine insertion formula
against the all-`o*` background when the reached support is nontrivial. The
independent-dummy argument extends only the deterministic payoff increment to
singleton reached support. Crossed-background independence is then proved for
deterministic payoff profiles and telescoped. Lean does not separately expose
the paper's full arbitrary-continuation/arbitrary-background intermediate
lemma. This sufficient proof-route specialization adds no assumption and does
not weaken the final theorem.

## Conclusion

| Paper clause | Lean declaration |
|---|---|
| expected payoff utility | `expectedPayoffUtility` |
| expected utility plus `lambda * mutualInfo` | `traceTemperedValue` |
| one global nonconstant `u`, one `lambda > 0` | `WithinChannelRepresentation` and the first conjunct of `Theorem1StatementV10` |
| same witnesses for all finite block comparisons | `SameWitnessBlockRepresentation` and the second conjunct |
| forward and converse closure | `theorem1V10Clauses`, `theorem1StatementV10` |
| public theorem | `TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1` |

Appendix B contains auxiliary results and is not claimed by the formal
Theorem 1 endpoint.

## Kernel audit

`TraceableAgency/Audit/Axioms.lean` recursively checks the public theorem
against the exact whitelist `propext`, `Classical.choice`, and
`Quot.sound`. `TraceableAgency/Audit/Dependencies.lean` rejects superseded
stronger routes. `TraceableAgency/Audit/V10Certificate.lean` performs
`#check`, `#print`, and `#print axioms` on the current declaration and checks
the finite-branch and relevance bridges.
