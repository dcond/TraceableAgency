# Paper-to-Lean proof roadmap: version 10

This roadmap follows the single Appendix A narrative in the v10 paper through
the checked Lean dependency graph.  Declaration names are stable points of
correspondence; helper lemmas and file boundaries are implementation details.
Appendix B is auxiliary and is not part of the certified Theorem 1 endpoint.

## 1. Statement boundary

`Theorem1/Statements.lean` fixes one payoff alphabet and defines primitive
preferences only within a fixed joint channel.  It also constructs the
common-payoff block channels used to interpret cross-environment notation.

The current bundle is `TraceTemperedAxiomsV10`:

1. `A1_WeakOrder`
2. `A2_Continuity`
3. `A3_MaterialRelevance`
4. `A4_TraceRelevance`
5. `A5_BlockComparisonCoherence`
6. `A6_RecordDataProcessing`
7. `A7_ActionDataProcessing`
8. `A8_RecordwiseSureThing`

`Theorem1StatementV10` states the equivalence with a nonconstant payoff index
and a positive mutual-information coefficient, plus the same-witness finite
block clause. `Theorem1StatementV10` and `TraceTemperedAxiomsV10` are the
canonical public declarations.

(A2) is sequential closedness, equivalent to the closed graph in this
finite-dimensional setting.

## 2. Shared affine preliminaries

Paper anchors: `lf:lem:bookkeeping` and `lf:lem:terminal-affine`.

### Blocks, supports, and dummies

`PairOrder.lean` supplies the order-theoretic facts for explicit block
comparisons. `SupportDummy.lean`, `RightDummy.lean`, and
`ValueSupport.lean` derive support restriction and dummy-coordinate neutrality
from exact A7 processors and A5 block coherence.  These facts are proved, not
imposed as conventions about relabelling or zero-probability actions.

### Terminal laws and affine fibres

`MarkedTerminal.lean` proves that experiments with the same marked terminal
law are behaviorally interchangeable using payoff-preserving A6 processors.
`MarkedHM.lean` derives public-mixture independence from the finite-branch
form of A8 and obtains fixed-prior affine cardinalizations.  The normalization
machinery is isolated in `AffineTools.lean` and `NormalizeAffine.lean`.

The parallel pure-trace fixed-prior construction appears in
`PureTrace/Proof/Posterior.lean` and `PureTrace/Proof/Affine.lean`.

## 3. From the axioms to working forms

### Binary A8 to finite branches

Paper anchors: `pt:lem:finite-branch-extension` and
`pt:cor:one-branch-a8`.

`FiniteBranchExtension.lean` proves
`recordwiseSureThing_iff_finiteBranchContinuationConsistency` using only A1
and A5--A7 around the public binary A8.  The proof collapses one record against
its complement, pads continuations onto a common tagged record alphabet,
handles null rows with exact action-completion equations, and telescopes
finite hybrid profiles.  The strict finite clause is derived from weak order;
it is not a public hypothesis.

`BranchInsertion.lean` and `SupportBranchInsertion.lean` package the resulting
one-reached-branch insertion identities used later in scale calibration.

### Relevance bridge

Paper anchor: `lem:relevance-bridge`.

`RelevanceBridge.lean` derives the proof-facing forms of A3 and A4.

- `materialRelevance_bridge` moves the fixed two-action A3 comparison to the
  one-action payoff environments used for material normalization.
- `traceRelevance_bridge` keeps the single A4 payoff witness `o*` fixed while
  transporting the fair binary comparison to every full-support prior on a
  nontrivial finite action alphabet.

`traceTemperedBridgeAxioms_of_v10` combines these derived forms with the finite
A8 result; no field is added.
Neither relevance bridge uses A2.

## 4. Pure-trace core

Paper anchor: `pt:prop:main` in `appendix_a_pure_trace_v10.tex`.

`Theorem1/PureTrace.lean` embeds constant-payoff environments at the A4 anchor.
`inducedPureConditions_of_components` and
`inducedPureRepresentation_of_components` construct the pure-trace package
without A3, matching the weaker assumptions of the paper's pure-trace
proposition. `inducedPureConditions` and `inducedPureRepresentation` are
full-bundle compatibility wrappers. The checked proof then follows the order
of the paper:

1. Fixed-prior posterior-law sufficiency and affine values:
   `PureTrace/Proof/Posterior.lean`, `Affine.lean`.
2. Exact action/relabel transport and support faces:
   `PureTrace/Support/Relabeling.lean`, `SupportRestriction.lean`, and the
   transport results in `PureTrace.lean`.
3. Product calibration and background inertness:
   `PureTrace/Proof/ProductGauge.lean` and the support-scale modules.
4. Branch aggregation and coherent face scales:
   `PureTrace/Proof/Branch.lean`, `FaceCoherence.lean`, and `Scales.lean`.
5. Interaction collapse, entropy reduction, and Faddeev identification:
   `PureTrace/Proof/EntropyReduction.lean`, `Final.lean`, and
   `PureTrace/Support/GenericFaddeev.lean`.

`PureTrace/Theorem.lean` closes this route at
`provedPureTraceCharacterization`.  The final theorem does not import the
older compatibility routes rejected by the dependency audit.

## 5. Two common scales

### Material scale

Paper anchor: `lf:lem:material-scale`.

`PayoffLotteries.lean` and `MaterialUtility.lean` cardinalize ordinary payoff
lotteries and select A3's material high and low outcomes.
`NormalizedMarked.lean` normalizes every marked affine fibre at those same
outcomes, and `CommonMarkedScale.lean` uses affine uniqueness to identify one
common nonconstant index:

- `materialHighOutcome`
- `materialLowOutcome`
- `materialPayoffUtility`
- `materialPayoffUtility_nonconstant`

### Trace scale

Paper anchor: `lf:lem:trace-scale`.

`PureMarkedEmbedding.lean` embeds the pure-trace result at the separate A4
trace anchor. `GlobalTraceScale.lean` and
`ConstantTraceAnchorGeneral.lean` identify one coefficient, independent of
the prior:

\[
W_q(E)=u(o_*)+\lambda I_q(E).
\]

The main declarations are `globalTraceLambda`, `globalTraceLambda_pos`, and
`normalizedMarkedUtility_constantTraceAnchor_eq_globalTraceLambda_mul_mutualInfo`.
The intercept is `materialPayoffUtility F h h.traceAnchor`; the proof does not
identify the trace anchor with either material anchor.

## 6. Exact reached-branch weights

Paper anchors: `lf:lem:branch-weight`, `lf:lem:deterministic-assembly`, and
`lf:lem:branch-increment`.

`BranchInsertion.lean`, `SupportBranchInsertion.lean`, and
`BranchScaleIdentification.lean` prove the arbitrary-continuation affine
insertion formula against the all-`o*` background when the reached support is
nontrivial. `DummyBranchBridge.lean` and `PositiveBranchIncrement.lean` adjoin
a fixed full-support two-action dummy and transport back the deterministic
payoff increment when the original reached support is a singleton. The
resulting payoff change is

\[
m_y\,[u(o)-u(o_*)].
\]

`PayoffBranchBackground.lean` proves the crossed-background identity needed
for deterministic payoff continuations, and `PayoffBranchTelescope.lean`
changes finitely many payoff branches one at a time.

The paper states its reached-branch lemma for arbitrary continuations and
arbitrary backgrounds. Lean does not separately expose that full intermediate
lemma: arbitrary continuations are handled only against the all-`o*`
background with nontrivial reached support; dummy lifting extends only the
deterministic increment; and crossed-background independence is established
only for deterministic payoff profiles. This is exactly the specialization
used by the telescope and Theorem 1. It changes neither the theorem statement
nor its hypotheses.

## 7. Assembly for arbitrary channels and priors

`FullSupportValueAssembly.lean` sums the deterministic branch increments and
uses \(\sum_y m_y=1\) to obtain expected utility plus the constant-anchor trace
term.  The nonzero intercept is carried explicitly.

`Sequentialization.lean` represents an arbitrary payoff-record channel by
first revealing its visible `(payoff, record)` output and then delivering the
corresponding payoff; A6 proves the original and sequential channels
equivalent.  `SupportDummy.lean` and `ValueSupport.lean` reduce boundary priors
to their supports without changing expected utility or mutual information.

The numerical endpoint is
`fullSupportNormalizedValueFormula_of_positiveBranchPayoffIncrement`.
`RepresentationAssembly.lean` then uses A5 duplication for within-channel
comparisons and A5 irrelevant-block coherence for finite block comparisons.
The witnesses in both clauses are exactly `materialPayoffUtility F h` and
`globalTraceLambda F h`.

## 8. Converse and final closure

`Benchmark.lean` verifies A1--A8 from any nonconstant `u` and `lambda > 0`.
At A3 the pure payoff lotteries have zero mutual information and distinct
utility values.  At A4 the fair revealing and nonrevealing lotteries have
mutual-information values `log 2` and `0`.  Data processing and compound
identities supply A6--A8, including the exact null-row interpretation of A7.

`TheoremClosure.lean` exposes:

- `traceTemperedBridgeAxioms_imply_representation_and_block`
- `theorem1V10Clauses`
- `theorem1StatementV10`

The public declaration is:

```lean
TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1 :
  TraceableAgency.Theorem1.Theorem1StatementV10
```

## 9. Audit boundary

`Audit/Axioms.lean` recursively permits only `propext`, `Classical.choice`,
and `Quot.sound`. `Audit/Dependencies.lean` rejects superseded stronger routes.
`Audit/V10Certificate.lean` checks and prints the current statement, public
theorem, finite-branch bridge, relevance bridges, and kernel axioms. The
certificate script also rejects proof holes and project axioms, checks the
repository byte manifest, rebuilds the v10 PDF, and performs a fresh
`leanchecker` replay.
