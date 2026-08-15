# Claim map: Theorem 1, version 5

## Certified boundary

- Paper result: `thm:main` in
  [`trace_tempered_choice_v5.tex`](../Paper/trace_tempered_choice_v5.tex).
- Exact proposition: `TraceableAgency.Theorem1.Theorem1StatementV5` in
  [`Statements.lean`](../TraceableAgency/Theorem1/Statements.lean).
- Public proof:
  `TraceTemperedChoiceVerification.trace_tempered_choice_v5_theorem1` in
  [`Proof.lean`](../TraceableAgency/Theorem1/Proof.lean).
- Extra project axioms: none; the theorem-side
  [`Axioms.lean`](../TraceableAgency/Theorem1/Axioms.lean) declares nothing.

## Domain and constructions

| Paper anchor | Mathematical role | Lean declaration |
|---|---|---|
| `sec:model` | Fixed finite payoff alphabet, cardinality at least two | Outer binders of `Theorem1StatementV5` |
| `sec:model` | Nonempty finite action/record alphabets and joint channel | `FixedPayoffPrefFamily`, `Channel A (O × R)` |
| comparison environments | Two-block and finite-block comparisons | `commonPayoffBlockChannel`, `commonPayoffBlockFamilyChannel`, `pairWeak`, `pairStrict` |
| `eq:record-processing` | Payoff-preserving record rewrite | `RecordProcessor`, `recordPostprocess` |
| `eq:action-processing` | Exact action-processor joint-law completion, including null rows | `IsActionProcessorCompletion` |
| `eq:compound` | Branch-dependent sequential composition | `commonPayoffCompound` |
| displayed mutual-information formula | Finite likelihood-ratio sum with zero-joint-mass summands set to zero | `mutualInfoLikelihoodRatio`, `mutualInfoLikelihoodRatio_eq_mutualInfo` |

The block record tag is reassociated without moving the common payoff
coordinate by `sumPayoffRecordEquiv` and `sigmaPayoffRecordEquiv`.

## Exact v5 axioms

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
| A1--A8 | exact bundle and field order | `TraceTemperedAxiomsV5` |

Faithfulness-sensitive details are literal in these types:

- A3 and A4 are within-channel comparisons in canonical fixed benchmark
  channels, not cross-channel assumptions.
- A4 existentially chooses one payoff. It does not quantify over every payoff.
- A6 processors may depend on realized payoff and record but preserve payoff.
- A7 uses the undivided joint-law equation, so zero-mass processed-action rows
  remain arbitrary and every completion is quantified.
- A8 has exactly one common record alphabet for `K`, `L`, and `M`, preserves
  the common continuation `M`, and is silent when binary record 1 is null.
- `recordwiseSureThing_iff_finiteBranchContinuationConsistency` derives the
  weak-and-strict finite property used downstream; it is not bundled as an
  additional public premise.

(A2) is formalized as sequential closedness, equivalent to the closed graph in this finite-dimensional setting.

## Relevance bridge

| Paper anchor | Lean declaration |
|---|---|
| `lem:relevance-bridge`, material part | `materialRelevance_bridge` |
| `lem:relevance-bridge`, trace part | `traceRelevance_bridge` |
| `pt:lem:finite-branch-extension` | `recordwiseSureThing_iff_finiteBranchContinuationConsistency` |
| v5 bundle to proof-facing bundle | `traceTemperedBridgeAxioms_of_v5` |
| proof-facing bundle back to v5 | `traceTemperedAxiomsV5_of_bridge` |

Both equivalences assume only A1 and A5--A8. A2 is not used. The trace bridge
chooses the A4 witness `o*` and proves `PositiveTraceOrientationAt F o*` for
every full-support prior on every nontrivial finite action alphabet. The bridge
never transports the comparison to another payoff.

Lean represents the proof-facing package as
`TraceTemperedBridgeAxioms F ostar`, indexed by the externally chosen anchor.
The index is necessary to keep the witness in `Prop`; it adds no hypothesis.

## Representation and scale separation

| Paper anchor | Lean route |
|---|---|
| material anchors `o+`, `o-` | `materialHighOutcome`, `materialLowOutcome`, `materialPayoffUtility` |
| pure trace at `o*` | `inducedPureRepresentation`, `normalizedConstantTraceAnchorPullbackAffineUtilityRepresentation` |
| global trace coefficient | `globalTraceLambda`, `globalTraceLambda_pos` |
| `W_q(E)=u(o*)+lambda I_q(E)` on the constant-`o*` face | `normalizedMarkedUtility_constantTraceAnchor_eq_globalTraceLambda_mul_mutualInfo` |
| reached branch increment `m[u(o)-u(o*)]` | `positiveBranchPayoffIncrement_of_nontrivialSupport`, `positiveBranchPayoffIncrementFormula` |
| deterministic branch assembly | `normalizedMarkedUtility_payoffBranchFormula` |
| arbitrary channels and boundaries | `fullSupportNormalizedValueFormula_of_positiveBranchPayoffIncrement`, `representationClauses_of_fullSupportNormalizedValueFormula` |

The baseline and branch formulas use the trace anchor only. They do not reuse
the low material anchor. Material normalization and trace normalization are
therefore formally separate.

## Conclusion

| Paper clause | Lean declaration |
|---|---|
| expected payoff utility | `expectedPayoffUtility` |
| expected utility plus `lambda * mutualInfo` | `traceTemperedValue` |
| one global nonconstant `u`, one `lambda > 0` | `WithinChannelRepresentation` and the first conjunct of `Theorem1StatementV5` |
| same witnesses for all finite block comparisons | `SameWitnessBlockRepresentation` and the second conjunct |
| forward and converse closure | `theorem1V5Clauses`, `theorem1StatementV5` |
| public theorem | `TraceTemperedChoiceVerification.trace_tempered_choice_v5_theorem1` |

Appendix C contains paper-only auxiliary results and is not claimed by the
formal Theorem 1 endpoint.

## Kernel audit

`TraceableAgency/Audit/Axioms.lean` recursively checks the v5 public theorem
against the exact whitelist `propext`, `Classical.choice`, and `Quot.sound`.
`TraceableAgency/Audit/Dependencies.lean` rejects superseded stronger routes.
`TraceableAgency/Audit/V5Certificate.lean` performs `#check`, `#print`, and
`#print axioms` on the exact public declaration and checks both relevance
bridges.
