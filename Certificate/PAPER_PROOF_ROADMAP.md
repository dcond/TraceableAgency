# Paper-to-Lean proof roadmap: version 5

This roadmap follows the proof of Theorem 1 from the v5 paper to the checked
Lean dependency graph. Declaration names are the stable points of
correspondence; helper lemmas remain implementation details.

## 1. Statement boundary

`Statements.lean` fixes one payoff alphabet and defines primitive preferences
only within a fixed joint channel. It then defines explicit common-payoff block
environments, record processors, action processors, and compounds.

The v5 bundle is `TraceTemperedAxiomsV5`:

1. `A1_WeakOrder`
2. `A2_Continuity`
3. `A3_MaterialRelevance`
4. `A4_TraceRelevance`
5. `A5_BlockComparisonCoherence`
6. `A6_RecordDataProcessing`
7. `A7_ActionDataProcessing`
8. `A8_RecordwiseSureThing`

`Theorem1StatementV5` states the equivalence with a nonconstant payoff index
and a positive mutual-information coefficient, plus the same-witness
finite-block clause.

(A2) is formalized as sequential closedness, equivalent to the closed graph in this finite-dimensional setting.

## 2. Binary-to-finite A8 bridge

Paper anchor: `pt:lem:finite-branch-extension`.

Lean module: `FiniteBranchExtension.lean`.

`recordwiseSureThing_iff_finiteBranchContinuationConsistency` proves the
paper's equivalence using only A1 and A5--A7. The forward proof collapses one
record against its complement, uses payoff-preserving record tags in both
directions, removes null rows with exact identity-action completions, and
telescopes finite hybrid profiles. The reverse proof obtains the binary
biconditional from the weak and strict finite clauses plus completeness.

The proof-facing bridge stores `FiniteBranchContinuationConsistency`, but
`traceTemperedBridgeAxioms_of_v5` constructs that field from public binary A8.
Conversely, `traceTemperedAxiomsV5_of_bridge` proves public binary A8 from the
derived finite property. No stronger public relevance assumption is present.

## 3. Appendix A: relevance bridge

Paper anchor: `lem:relevance-bridge`.

Lean module: `RelevanceBridge.lean`.

### Material part

`materialRelevance_fixed_implies_environment` starts from the two pure
lotteries in the fixed A3 channel. `materialSelectProcessor` and
`collapseToUnitProcessor` satisfy the exact A7 completion equation and replace
each pure support with its one-action deterministic-payoff environment.
`pairStrict_transport_of_structural` preserves strictness using only weak
order, block coherence, and the two data-processing axioms.

`materialRelevance_environment_implies_fixed` reverses these processors. It
also proves the selected outcomes are distinct: if the outcomes coincided, a
constant action processor would supply the forbidden reverse weak comparison.

Public equivalence: `materialRelevance_bridge`.

### Trace part: fixed four actions to fair binary trace

`traceRelevance_fixed_implies_fairBinary` converts the fixed A4 comparison
into fair binary full revelation versus an independent fair record.

- `traceLeftInclusionProcessor` inserts the revealing support.
- `traceSideProjectionProcessor` collapses the nonrevealing support.
- `traceLeftInclusion_isActionProcessorCompletion` and
  `traceSideProjectionRight_isActionProcessorCompletion` prove the exact
  joint-law equations, including zero-mass rows.

The payoff remains the A4 witness `ostar`.

### Trace part: arbitrary finite action alphabets

For a nontrivial finite `A`, choose distinct `a0,a1`.
`relevanceBitEmbed` and `relevanceBitRetract` have the proved left-inverse
identity `relevanceBitRetract_embed`. `embeddedFairPrior` is the fair law on
those two actions.

`fairBinaryTrace_implies_embeddedTrace` uses exact action processors and the
record rewrite `embeddedRecordRetractProcessor` to transport fair binary
strictness to full revelation on `A`. `embeddedTrace_with_commonRecord` then
puts both continuations over one record alphabet, as required by A8.

### Trace part: arbitrary full-support priors

`fairBinaryTrace_implies_positiveOrientationAt` uses
`exists_positive_branch_mass_dominated_target` and `binaryReachChannel` to
construct a positive branch with posterior `embeddedFairPrior a0 a1` from an
arbitrary full-support `q`.

Every reached branch weakly prefers full revelation to an independently
redrawn record by A6; the target branch is strict. A8 therefore makes the
compound comparison strict. `branchTaggedRevealProcessor` garbles full
revelation into the revealing compound, while `eraseAllRecordsProcessor`
garbles the other compound into silence. Structural strict transport gives
`PositiveTraceOrientationAt F ostar`.

The converse uses `traceRightInclusionProcessor`, the left side projection,
and a fair-record generator to return to the exact four-action A4 channel.

Public equivalence: `traceRelevance_bridge`.

Neither bridge uses A2. The trace bridge never changes `ostar`.

## 4. Pure trace at the one trace anchor

`traceTemperedBridgeAxioms F traceAnchor` indexes the proof-facing bundle by
the witness chosen in Appendix A. The pure-trace wrappers in `PureTrace.lean`
invoke positive orientation only at `h.traceAnchor`.

The current pure-trace route proves the auxiliary characterization through:

- posterior-law sufficiency and record/action processing;
- finite Herstein--Milnor representation;
- grouping and Faddeev recursion;
- product, face, and branch scale coherence;
- the vendored finite Shannon characterization.

The public dependency is `provedPureTraceCharacterization`; compatibility
routes are not imported by the final theorem.

## 5. Material normalization

`PayoffLotteries.lean` derives exact action-processor neutrality for
action-independent payoff lotteries. `MaterialUtility.lean` uses the material
relevance environment to choose two material anchors and normalize a global
nonconstant affine payoff index:

- `materialHighOutcome`
- `materialLowOutcome`
- `materialPayoffUtility`
- `materialPayoffUtility_nonconstant`

These anchors are used only for material scale normalization. No declaration
sets the trace anchor equal to either material anchor.

## 6. Global trace scale at `o*`

`PureMarkedEmbedding.lean` embeds pure-record experiments as marked
constant-payoff experiments at `h.traceAnchor`.

`GlobalTraceScale.lean` proves that the normalized marked utility on that face
has one positive coefficient, independent of the prior:

\[
W_q(E)=u(o_*)+\lambda I_q(E).
\]

The main declarations are `globalTraceLambda`, `globalTraceLambda_pos`, and
`normalizedMarkedUtility_constantTraceAnchor_eq_globalTraceLambda_mul_mutualInfo`.
`ConstantTraceAnchorGeneral.lean` extends the same formula to arbitrary
constant-(o_*) marked experiments.

The intercept is `materialPayoffUtility F h h.traceAnchor`; it is not assumed
to be zero.

## 7. Branch-scale identification

`BranchScaleIdentification.lean` calibrates a positive reached branch against
full revelation and silence at `o*`. The constant-(o_*) intercept appears on
both sides and cancels. The resulting local payoff change is

\[
m_y\,[u(o)-u(o_*)].
\]

`PositiveBranchIncrement.lean` removes the possible singleton-posterior issue
by adjoining a fixed full-support two-action dummy and transporting the result
back with exact action processors. Its endpoint is
`positiveBranchPayoffIncrementFormula`.

## 8. Deterministic profiles and arbitrary channels

`PayoffBranchTelescope.lean` changes finitely many payoff branches one at a
time. `FullSupportValueAssembly.lean` uses the branch increment and
(sum_y m_y=1) to obtain expected utility plus the constant-(o_*) trace
term. The nonzero intercept is handled explicitly.

An arbitrary payoff-record channel is sequentialized by first revealing its
visible `(payoff, record)` output and then delivering the corresponding payoff.
A6 proves the original and sequential channels equivalent. This yields
`fullSupportNormalizedValueFormula_of_positiveBranchPayoffIncrement`.

`SupportDummy.lean` and `ValueSupport.lean` restrict boundary priors to their
supports. Expected utility and mutual information are unchanged, so no
boundary representative is chosen.

## 9. Representation and same-witness block comparisons

`RepresentationAssembly.lean` converts the normalized numerical formula to
cross-channel order representation, then uses A5 duplication for
within-channel comparisons and A5 irrelevant-block coherence for arbitrary
finite block comparisons. The witnesses are exactly
`materialPayoffUtility F h` and `globalTraceLambda F h` in both clauses.

`TheoremClosure.lean` performs the final logic:

- `traceTemperedBridgeAxioms_imply_representation_and_block`
- `theorem1V5Clauses`
- `theorem1StatementV5`

## 10. Converse

`Benchmark.lean` evaluates the represented value under blocks, record
processing, exact action processing, and compounds. From nonconstant `u` and
`lambda > 0`, it proves the structural axioms and constructs
`TraceTemperedBridgeAxioms F ostar` directly at one selected material outcome.
`traceTemperedAxiomsV5_of_bridge` then returns to the exact fixed A3/A4
channels without passing through another axiom bundle.

At A3 the two fixed pure lotteries have distinct utility values and zero
mutual information. At A4 the fair revealing and nonrevealing lotteries both
pay `o*`, while their mutual-information values are `log 2` and `0`. Thus
positive `lambda` gives the required strict comparisons.

Endpoint: `traceTemperedAxiomsV5_of_representation`.

## 11. Public theorem and audit

`Proof.lean` exposes:

```lean
TraceTemperedChoiceVerification.trace_tempered_choice_v5_theorem1 :
  TraceableAgency.Theorem1.Theorem1StatementV5
```

`Audit/Axioms.lean` recursively whitelists only `propext`,
`Classical.choice`, and `Quot.sound`. `Audit/Dependencies.lean` rejects
superseded stronger routes. `Audit/V5Certificate.lean` checks and prints the
exact public declaration and both relevance bridges. The certificate script
also rejects proof holes and project axioms, rebuilds the v5 PDF, and performs
a fresh `leanchecker` replay.
