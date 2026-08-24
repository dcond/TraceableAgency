# Formalization certificate: `trace_tempered_choice_v10`, Theorem 1

## Certified result

The authoritative informal result is Theorem 1 (`thm:main`) in
`Paper/trace_tempered_choice_v10.tex`. Its formal statement and public proof are:

```lean
TraceableAgency.Theorem1.Theorem1StatementV10

TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1 :
  TraceableAgency.Theorem1.Theorem1StatementV10
```

The proof declaration has exactly the displayed proposition as its type. This
certificate covers Theorem 1 and its same-witness finite-block clause. It does
not claim formal verification of the paper-only auxiliary results in Appendix
B.

`Theorem1StatementV10` and `TraceTemperedAxiomsV10` are the canonical
formal statement and axiom bundle. `Audit/V10Certificate.lean` checks their
exact types and the public theorem's kernel axioms, ensuring that no premise
has been added.

[`THEOREM1_FORMAL_SPECIFICATION.md`](THEOREM1_FORMAL_SPECIFICATION.md) is a
generated, reader-facing inventory of the theorem's recursive local semantic
closure together with the checked identity for the paper's displayed
mutual-information formula. It prints the authoritative elaborated Lean
beside concise mathematical notation and treats external dependency
declarations as terminal symbols rather than unpacking them.

## Exact mathematical statement

Fix a finite payoff alphabet \(O\) with \(|O|\ge 2\). For every nonempty finite
action alphabet \(A\), record alphabet \(R\), and joint channel


\[
K:A\to\Delta(O\times R),
\]

the primitive family \(F\) supplies a relation \(\succeq_K\) on
\(\Delta(A)\). For \(u:O\to\mathbb R\) and \(\lambda\in\mathbb R\), define

\[
V_{u,\lambda}(q,K)
=\sum_a q(a)\sum_{o,r}K(o,r\mid a)u(o)
+\lambda I_{qK}(A;O,R).
\]

Lean proves that the exact v10 Axioms A1--A8 are equivalent to the existence of
one nonconstant \(u\), one \(\lambda>0\), and simultaneous representation of
every within-channel comparison by \(V_{u,\lambda}\). It also proves that one
pair of witnesses simultaneously represents all comparisons between
alternatives supported on distinct blocks of every finite common-payoff block
environment.

`mutualInfoLikelihoodRatio` formalizes the displayed finite
likelihood-ratio sum, setting every zero-joint-mass summand to zero.
`mutualInfoLikelihoodRatio_eq_mutualInfo` proves that this formula equals Lean's
entropy-difference definition of `mutualInfo`, without an additional axiom.

These are the two conjuncts of `Theorem1StatementV10`, respectively expressed
through `WithinChannelRepresentation` and `SameWitnessBlockRepresentation`.

## Domain and comparison environments

`FixedPayoffPrefFamily O` fixes the payoff alphabet across the family while
allowing arbitrary nonempty finite action and record alphabets. `DecidableEq`
is finite computational structure, not a behavioral premise.

Cross-channel notation is derived, not primitive. `pairWeak F q K p L`
compares the supported copies of \(q\) and \(p\) inside one explicit block
channel. Only record tags are added; `sumPayoffRecordEquiv` and
`sigmaPayoffRecordEquiv` retain the same payoff coordinate.

## Exact v10 axioms

### A1 — weak order

`A1_WeakOrder`: every fixed joint channel carries a complete and transitive
relation on its action lotteries.

### A2 — continuity

`A2_Continuity`: for fixed finite alphabets, coordinatewise convergence of the
channel and both lotteries preserves a weak comparison. On finite Euclidean
simplexes this is the paper's closed-graph formulation.

### A3 — fixed-channel material relevance

`A3_MaterialRelevance`: there are distinct \(o^+,o^-\) such that, inside the
canonical two-action no-record channel delivering those outcomes surely, the
pure \(o^+\) lottery is strictly preferred to the pure \(o^-\) lottery.

This is a single within-channel comparison. A cross-environment material
condition is not assumed.

### A4 — fixed-channel trace relevance at one payoff

`A4_TraceRelevance`: there is one payoff \(o_*\) and one canonical four-action
channel. Its left pair reveals the selected Boolean action, while its right
pair emits an independent fair Boolean record. The fair revealing lottery is
strictly preferred to the fair nonrevealing lottery in that same channel.

The existential payoff is deliberately singular. The theorem does not assume
positive trace orientation at every payoff.

### A5 — block-comparison coherence

`A5_BlockComparisonCoherence` contains exactly `duplication` and
`irrelevant_blocks`, connecting primitive within-channel comparisons to
supported comparisons in explicit finite block environments.

### A6 — record data processing

`A6_RecordDataProcessing`: a stochastic rewrite of the explicit record cannot
improve an alternative. `RecordProcessor` may depend on realized payoff and
record but `payoffPreservingRecordKernel` copies the payoff unchanged.

### A7 — action data processing

`A7_ActionDataProcessing`: a stochastic processor of the realized action
cannot improve an alternative for every completion satisfying

\[
(qS)(b)\widehat K(o,r\mid b)
=\sum_a q(a)S(b\mid a)K(o,r\mid a).
\]

`IsActionProcessorCompletion` is this undivided equation. At a zero-mass
processed action, nonnegativity makes the right side zero and leaves the
completion row unrestricted. Lean quantifies over every such completion.

### A8 — binary recordwise sure-thing principle

`A8_RecordwiseSureThing` is the paper's binary weak biconditional. The first
binary record must be reached; the two compounds differ only in its
continuation and share the same continuation after the other record.

`recordwiseSureThing_iff_finiteBranchContinuationConsistency` proves, from A1
and A5--A7, that this binary premise is equivalent to the weak-and-strict
finite-branch property used by the representation proof. The construction
collapses one finite record against its complement, pads continuations onto a
common tagged record alphabet, handles null rows through exact A7 completions,
and telescopes branch replacements using A1 and A5. The derived property is
`FiniteBranchContinuationConsistency`; it is not an extra axiom field.

### Bundle boundary

`TraceTemperedAxiomsV10` contains exactly these eight predicates, in this
numbering. It has no representation, posterior-continuity, Faddeev,
Herstein--Milnor, normalization, reachability, scale, or selection field.

## Fixed-channel relevance bridge

Appendix A's bridge is formalized in `RelevanceBridge.lean`.

`materialRelevance_bridge` proves, under A1 and A5--A7, that fixed A3 is
equivalent to strict comparison between the corresponding one-action sure
payoff environments. Exact action processors collapse each pure support and
reinsert it. The reverse proof also derives distinctness from strictness.

`traceRelevance_bridge` proves, under A1 and A5--A8,

\[
\mathrm{A4}(F)
\quad\Longleftrightarrow\quad
\exists o_*\;\mathrm{PositiveTraceOrientationAt}(F,o_*).
\]

The forward construction proceeds as follows.

1. Exact action processors extract fair binary full revelation and a fair
   independent record from the fixed four-action channel.
2. Two distinct actions are embedded in any nontrivial finite alphabet;
   exact processors and payoff-preserving record rewrites transport the strict
   comparison to the embedded fair prior.
3. From an arbitrary full-support prior, `binaryReachChannel` creates a
   positive branch whose posterior is that embedded fair prior.
4. The derived finite-branch lemma makes the compound comparison strict; A6 garbles full revelation to the
   revealing compound and the nonrevealing compound to silence.

All channels, processors, branch masses, posteriors, and null completions are
defined and proved in Lean. A2 is not used. Most importantly, every step keeps
the same payoff \(o_*\). The converse uses the fair binary prior, generates an
independent fair record from silence, and reinserts the two supports into the
fixed four-action channel.

`TraceTemperedBridgeAxioms F ostar` is a proof-facing `Prop` indexed by the
chosen trace anchor. `traceTemperedBridgeAxioms_of_v10` returns an existentially
indexed bundle, so extraction never moves data from a proposition into a
computational type and introduces no choice principle beyond the final proof's
audited foundations.

## Material and trace anchors remain separate

Material normalization chooses `materialHighOutcome` and
`materialLowOutcome` from A3's environment form and constructs the nonconstant
index `materialPayoffUtility`.

The trace proof is indexed independently by `traceAnchor = ostar`. Pure-trace
identification is invoked only on constant-\(o_*\) experiments. The global
formula on that face is

\[
W_q(E)=u(o_*)+\lambda I_q(E).
\]

This is formalized by the constant-trace-anchor modules, including
`GlobalTraceScale.lean` and `ConstantTraceAnchorGeneral.lean`. A reached branch
of mass \(m\) changed from \(o_*\) to \(o\) has increment

\[
m\,[u(o)-u(o_*)],
\]

proved by `positiveBranchPayoffIncrement_of_nontrivialSupport` when the reached
support is nontrivial. `DummyBranchBridge.lean` extends this deterministic
payoff increment to singleton reached supports. The packaged
`PositiveBranchPayoffIncrementFormula` still ranges over nontrivial global
action alphabets; the globally singleton case is handled separately by
`normalizedMarkedUtility_eq_traceTemperedValue_of_subsingleton`. There is no
identification of \(o_*\) with the low material anchor.

For the paper's broader reached-branch intermediate lemma, Lean proves the
arbitrary-continuation affine insertion formula against the all-\(o_*\)
background when the reached support is nontrivial. It then proves
crossed-background independence only for deterministic payoff profiles in
`PayoffBranchBackground.lean` and telescopes those profiles in
`PayoffBranchTelescope.lean`. Lean therefore exposes exactly the specialization
needed for Theorem 1, not a separate full
arbitrary-continuation/arbitrary-background lemma. This proof-route difference
adds no hypothesis and does not weaken the final theorem.

Finite telescoping uses \(\sum_y m_y=1\), so the intercept \(u(o_*)\) cancels
correctly and yields expected utility without an artificial zero baseline.

## Forward and converse closure

`fullSupportNormalizedValueFormula_of_positiveBranchPayoffIncrement` derives
the trace-tempered value formula for arbitrary channels at full-support
priors. Support restriction handles boundary priors without assigning them a
new normalized representative.

`representationClauses_of_fullSupportNormalizedValueFormula` produces the
within-channel and same-witness block conclusions. `theorem1V10Clauses` combines
this with the relevance bridge.

For the converse, the benchmark module proves weak order, continuity, block
coherence, both data-processing axioms, finite branch consistency, material
nonconstancy, and positive entropy of full revelation. It constructs the
proof-facing bridge directly at one fixed trace anchor. The reverse half of
the finite-branch lemma supplies public binary A8, and the reverse relevance
bridge gives the exact fixed A3/A4 channels. In particular, the A4
benchmark has mutual-information values \(\log 2\) and \(0\), so
\(\lambda>0\) supplies strictness.

## Trust boundary and reproducibility

There are no `sorry`, `admit`, or declaration-level project axioms on the
certified path. The recursive axiom audit permits exactly:

```text
propext
Classical.choice
Quot.sound
```

The dependency audit rejects superseded stronger proof routes.
`TraceableAgency/Audit/V10Certificate.lean` checks and prints the exact current
public declaration and its axioms. `scripts/check_theorem1_certificate.sh`
checks the byte manifest, source hygiene, complete Lean build, audits,
reproducible v10 PDF, and a fresh `leanchecker` replay.
