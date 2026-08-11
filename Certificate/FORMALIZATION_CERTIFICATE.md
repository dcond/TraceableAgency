# Formalization certificate: `trace_tempered_choice_v3`, Theorem 1

## Certified result

The authoritative informal result is Theorem 1 (`thm:main`) in
`Paper/trace_tempered_choice_v3.tex`.  Its formal statement and proof are:

```lean
TraceableAgency.Theorem1.Theorem1Statement

TraceableAgency.Theorem1.trace_tempered_choice_v3_theorem1 :
  TraceableAgency.Theorem1.Theorem1Statement
```

The second declaration has exactly the first declaration as its type.  The
proof therefore cannot silently strengthen the hypotheses, weaken the
conclusion, change the order of quantifiers, or prove a nearby proposition.

This certificate concerns Theorem 1 and its same-scale block clause only.  It
does not certify every later corollary in v3 or every advertised minimal-axiom
subset for auxiliary lemmas.

## Exact mathematical statement

Fix a finite payoff alphabet \(O\) with \(|O|\ge 2\).  A primitive family
\(F\) assigns, for every nonempty finite action alphabet \(A\), nonempty
finite record alphabet \(R\), and channel

\[
K:A\longrightarrow\Delta(O\times R),
\]

a binary relation \(\succeq_K\) on \(\Delta(A)\).  Put

\[
\mathsf{Ax}(F)
 :=\mathsf{A1}(F)\wedge\cdots\wedge\mathsf{A8}(F).
\]

For \(u:O\to\mathbb R\), \(\lambda\in\mathbb R\),
\(q\in\Delta(A)\), and \(K:A\to\Delta(O\times R)\), define

\[
V_{u,\lambda}(q,K)
 =\sum_a q(a)\sum_{o,r}K(o,r\mid a)u(o)
  +\lambda I_{qK}(A;O,R).
\]

Let \(\mathsf{Within}(F,u,\lambda)\) mean that, simultaneously for every
nonempty finite \(A,R\), every \(K\), and every
\(q,p\in\Delta(A)\),

\[
q\succeq_Kp
\quad\Longleftrightarrow\quad
V_{u,\lambda}(q,K)\ge V_{u,\lambda}(p,K).
\]

Let \(\mathsf{Blocks}(F,u,\lambda)\) mean that the same \(u,\lambda\)
represent every comparison between lotteries supported on two distinct blocks
of every finite common-payoff block environment.  Lean proves, for every such
\(O\) and every \(F\),

\[
\mathsf{Ax}(F)
\quad\Longleftrightarrow\quad
\exists u,\lambda:\
  u\text{ is nonconstant},\ \lambda>0,\
  \mathsf{Within}(F,u,\lambda),
\tag{T1}
\]

and also

\[
\mathsf{Ax}(F)
\quad\Longrightarrow\quad
\exists u,\lambda:\
  u\text{ is nonconstant},\ \lambda>0,\
  \mathsf{Within}(F,u,\lambda)\wedge
  \mathsf{Blocks}(F,u,\lambda).
\tag{M}
\]

Formula (M) is the weakest literal reading of the paper's "represented on the
same scale" clause: at least one representing pair \(u,\lambda\) works for
both kinds of comparison.  It does not claim that every possible representing
pair does so, and it does not choose new witnesses separately for each
environment.

In Lean, (T1) and (M) are the two conjuncts of `Theorem1Statement`.

## Domain and derived comparison notation

The fixed payoff coordinate is not a record label.  The two-block channel for
\(K:A\to\Delta(O\times R)\) and
\(L:B\to\Delta(O\times S)\) has output type
\(O\times(R\sqcup S)\): only the record is tagged.  The expression

\[
(q,K)\succeq(p,L)
\]

is not a second primitive preference.  It abbreviates the comparison between
the left- and right-block copies of \(q\) and \(p\) inside that one block
channel.  Lean's `commonPayoffBlockChannel`, `leftBlockDist`,
`rightBlockDist`, and `pairWeak` implement exactly this construction.

All paper action and record alphabets are nonempty.  Lean's `Fintype` and
`Nonempty` express finite nonempty sets.  `DecidableEq` is finite computational
structure used to evaluate sums and tagged constructions; every finite set
admits it, and it is not a behavioral premise.

Lean writes the payoff, action, and record types in one arbitrary universe
`u`.  This is bookkeeping, not a restriction on finite alphabets: every finite
set is equivalent to some `Fin n`, and finite types can be transported or
universe-lifted without changing any of the displayed distributions,
channels, or comparisons.

## Axioms (A1)--(A8): paper mathematics to Lean

### A1 - weak order

Paper mathematics: for every nonempty finite \(A,R\) and every
\(K:A\to\Delta(O\times R)\), the relation \(\succeq_K\) is complete and
transitive on \(\Delta(A)\).

Lean declaration: `A1_WeakOrder`.

There is no added independence, Archimedean, mixture, or nontriviality field in
full-payoff A1.

### A2 - continuity

Paper mathematics: for each fixed \(A,O,R\),

\[
G=\{(K,q,p):q\succeq_Kp\}
\]

is closed in the finite Euclidean product of channel and simplex coordinates.

Lean declaration: `A2_Continuity`.  It says that whenever \(K_n\to K\),
\(q_n\to q\), and \(p_n\to p\) coordinatewise and
\(q_n\succeq_{K_n}p_n\) for every \(n\), then
\(q\succeq_Kp\).

This is the same axiom under a standard finite-dimensional translation, not a
stronger continuity assumption.  The channel and simplex spaces are subsets
of a finite product of real coordinate spaces; coordinate convergence is the
product/Euclidean convergence, the space is metrizable, and in a metric space
a set is closed exactly when it is sequentially closed.  This topology bridge
is mathematical infrastructure used to read the paper statement; it is not a
separate behavioral hypothesis, and it is not claimed here as a separately
named Lean theorem.

### A3 - block-comparison coherence

Paper duplication clause:

\[
q\succeq_Kp
\quad\Longleftrightarrow\quad
(q,K)\succeq(p,K).
\]

Paper irrelevant-block clause: for every finite block family, distinct
\(i,j\), and \(q_i\in\Delta(A_i),q_j\in\Delta(A_j)\),

\[
q_i^i\succeq_{\bigsqcup_kK_k}q_j^j
\quad\Longleftrightarrow\quad
(q_i,K_i)\succeq(q_j,K_j).
\]

Lean declaration: `A3_BlockComparisonCoherence`, with fields `duplication`
and `irrelevant_blocks`.  The Lean general block output is reassociated by a
canonical finite equivalence so that the payoff coordinate remains common.

### A4 - record data processing

A record processor is a stochastic kernel \(T(r'\mid o,r)\) which may depend
on the realized payoff but copies that payoff unchanged.  It produces

\[
(KT)(o,r'\mid a)=\sum_rK(o,r\mid a)T(r'\mid o,r).
\]

The axiom is

\[
(q,K)\succeq(q,KT)
\]

for every admissible (A,R,R',K,T,q).

Lean declarations: `RecordProcessor`, `payoffPreservingRecordKernel`,
`recordPostprocess`, and `A4_RecordDataProcessing`.

### A5 - action data processing

For every stochastic report \(S:A\to\Delta(B)\), let

\[
(qS)(b)=\sum_aq(a)S(b\mid a).
\]

For every channel \(\widehat K:B\to\Delta(O\times R)\) satisfying the
undivided joint-law equation

\[
(qS)(b)\widehat K(o,r\mid b)
=\sum_aq(a)S(b\mid a)K(o,r\mid a)
\quad\text{for all }b,o,r,
\]

the axiom is

\[
(q,K)\succeq(qS,\widehat K).
\]

Lean declarations: `IsActionReportCompletion` and
`A5_ActionDataProcessing`.  If ((qS)(b)=0), nonnegativity makes the right
side zero, and the equation leaves that row of \(\widehat K\) unrestricted.
Both the paper and Lean quantify over every such completion; Lean does not
insert a canonical null-row convention.

### A6 - branchwise continuation consistency

Quantify one finite family of nonempty record alphabets
\((R_y)_{y\in Y}\), a first-stage channel \(P:A\to\Delta(Y)\), and two
continuation profiles

\[
K^y,L^y:A\longrightarrow\Delta(O\times R_y).
\]

Thus \(K^y\) and \(L^y\) share the record type within branch \(y\), while
\(R_y\) may vary with \(y\).  Define

\[
m(y)=\sum_aq(a)P(y\mid a),\qquad
q_y(a)=\frac{q(a)P(y\mid a)}{m(y)}
\]

when \(m(y)>0\).  If

\[
(q_y,K^y)\succeq(q_y,L^y)
\quad\text{for every }y\text{ with }m(y)>0,
\]

then

\[
(q,P\triangleright\{K^y\})
\succeq
(q,P\triangleright\{L^y\}).
\]

If at least one reached branch comparison is strict, the compound comparison
is strict.

Lean declarations: `commonPayoffCompound`,
`A6_BranchwiseContinuationConsistency_Weak`,
`A6_BranchwiseContinuationConsistency_Strict`, and their conjunction
`A6_BranchwiseContinuationConsistency`.

This is the weaker common-record-family A6 now stated explicitly in v3.  Lean
does not assume the stronger rule allowing unrelated record families for the
two profiles.  When a proof construction begins with different finite record
types, it first embeds both into a common tagged sum and only then invokes A6.

### A7 - material relevance

For a one-action, uninformative-record channel \(K_o\) delivering payoff
\(o\) surely, there exist \(o^+,o^-\in O\) such that

\[
(\delta_*,K_{o^+})\succ(\delta_*,K_{o^-}).
\]

Lean declarations: `deterministicPayoffChannel` and
`A7_MaterialRelevance`.

### A8 - positive trace orientation

For every finite \(A\) with \(|A|\ge2\), every full-support
\(q\in\Delta(A)\), and every fixed \(o\in O\), let
\(K_o^{\mathrm{id}}\) reveal the action in its record and let \(K_o^0\) have
an uninformative record.  The axiom is

\[
(q,K_o^{\mathrm{id}})\succ(q,K_o^0).
\]

Lean declarations: `fullRevealAtPayoff`, `uninformativeAtPayoff`, and
`A8_PositiveTraceOrientation`.  `Nontrivial A` is the finite-type form of
\(|A|\ge2\).

### The bundle contains nothing else

`TraceTemperedAxioms` has exactly eight fields, named `a1` through `a8`, with
the predicates above.  There is no posterior-continuity, affine-utility,
Faddeev, Herstein-Milnor, relabeling, support-face, normalization, scale,
background-independence, or representative-selection field.

## Conclusion: paper mathematics to Lean

`expectedPayoffUtility` is exactly

\[
\sum_aq(a)\sum_{o,r}K(o,r\mid a)u(o).
\]

`traceTemperedValue` adds `lambda * mutualInfo q K`, where the visible output
type passed to `mutualInfo` is the whole pair \(O\times R\).

Lean defines mutual information in the entropy/noise form.  Writing
\(z=(o,r)\) and \(m(z)=\sum_aq(a)K(z\mid a)\), that definition is

\[
H(m)-\sum_aq(a)H(K(\cdot\mid a)).
\]

Finite distributivity and
\(\log(x/y)=\log x-\log y\) on positive terms give

\[
\begin{aligned}
H(m)-\sum_aq(a)H(K(\cdot\mid a))
&=\sum_{a,z}q(a)K(z\mid a)
  \bigl(\log K(z\mid a)-\log m(z)\bigr)\\
&=\sum_{a,o,r}q(a)K(o,r\mid a)
  \log\frac{K(o,r\mid a)}{p_{qK}(o,r)}.
\end{aligned}
\]

Terms with \(q(a)K(o,r\mid a)=0\) are zero.  If a term is positive, then
both \(K(o,r\mid a)\) and \(p_{qK}(o,r)\) are positive, so the logarithmic
identity applies.  If the marginal is zero, every corresponding joint term is
zero.  Thus the entropy form used by Lean and the ratio form displayed in the
paper are the same finite functional; this algebraic translation adds no
assumption.  It is not advertised as a separately named bridge theorem in the
current Lean source.

Lean uses the natural logarithm.  For any paper base \(b>1\),
\(I_b=I_{\ln}/\ln b\), so replacing \(\lambda\) by
\(\lambda\ln b>0\) leaves the represented value unchanged.  V3 states the
necessary condition \(b>1\) explicitly.

`IsConstantPayoffIndex` means \(\exists c,\forall o,u(o)=c\); its negation is
exactly that \(u\) is nonconstant.  The witnesses \(u,\lambda\) are chosen
outside every \(A,R,K,q,p\) quantifier, so the scale is global rather than
environment-specific.

## Why the pure-trace input adds no assumption

The full proof invokes the checked pure-record theorem at a constant payoff.
`inducedPureConditions_of_components` constructs every induced pure-trace
condition from the full main-text axioms:

| Induced pure-trace condition | Constructed from full axioms |
|---|---|
| weak order | A1 |
| local nontriviality | A1, A3, A4, A8 |
| continuity | A2 |
| duplication | A3 |
| finite-block coherence | A1, A3, A4, A5 |
| record processing | A4 |
| action processing | A5 |
| branch consistency | A6 |

A7 is not needed for the pure-record theorem; it is used in the full-payoff
assembly to obtain a nonconstant material index.  The table is a construction
map, not a claim that every listed set is axiom-minimal.

The imported declaration
`TraceableAgency.provedPureTraceCharacterization` is a closed theorem.
Its Faddeev input is supplied by the proved Lean term
`TraceableAgency.GenericFaddeev.provedClassicalFaddeevTheoremAssumptions`.
There is no
Faddeev, Herstein-Milnor, or other theorem-interface parameter at the final
Theorem 1 boundary.

## What is assumed and what is proved

For the forward implication, the mathematical inputs are exactly:

1. the finite nonempty domain conditions and \(|O|\ge2\);
2. the primitive preference family \(F\); and
3. Axioms (A1)--(A8), packaged by `TraceTemperedAxioms F`.

Everything else in the representation proof is a theorem or construction in
the transitive Lean dependency closure.  In particular, terminal-law
sufficiency, support deletion, mixture independence, affine cardinalization,
material-scale normalization, the pure mutual-information characterization,
global scale alignment, branch-mass calibration, singleton and zero-mass
cases, payoff telescoping, sequentialization, and the finite-block conclusion
are proved rather than postulated.

For the reverse implication, Lean assumes the displayed representation with a
nonconstant \(u\) and positive \(\lambda\), then proves all eight predicates;
the endpoint is `traceTemperedAxioms_of_representation`.

## Kernel and dependency certificate

`Axioms.lean` deliberately contains no axiom, theorem-interface parameter, or
mathematical declaration.  `TraceableAgency/Audit/Axioms.lean` uses
`Lean.collectAxioms` and fails the build if any audited public endpoint depends
on a kernel axiom outside this explicit whitelist:

```text
propext
Classical.choice
Quot.sound
```

These are Lean/Mathlib logical foundations, not behavioral,
information-theoretic, or representation-theorem premises.  It would be
incorrect to say that the proof uses no logical foundations; the precise claim
is that it uses no project axiom or mathematical premise beyond the theorem's
displayed hypotheses.

`TraceableAgency/Audit/Dependencies.lean` recursively follows declaration types and
bodies from the direct mutual-information endpoint, the closed pure
characterization, and Theorem 1.  The build fails if that path reaches the
superseded posterior-integral, global posterior-law-continuity,
`marginalValue`, old all-representatives relabeling, or `FinalHMInterface`
route.

The standalone script `scripts/check_theorem1_certificate.sh` additionally:

- verifies `Certificate/SHA256SUMS`;
- builds the minimal statement, public theorem, and compatibility targets;
- rejects `sorry`, `admit`, declaration-level project axioms, and named
  kernel-bypass primitives throughout the project source;
- runs the recursive axiom and dependency audits; and
- replays `TraceableAgency.Theorem1.Proof` with `leanchecker --fresh`.

The default invocation performs every item in this list.  GitHub Actions uses
fresh runners for the paper and Lean jobs, performs the complete Lean kernel
build and both recursive audits, and omits only the redundant resource-heavy
fresh replay.  That replay remains part of the full local certificate.

Run:

```bash
lake build TraceableAgency.Theorem1
./scripts/check_theorem1_certificate.sh
```

The detailed proof dependency sequence is in `PAPER_PROOF_ROADMAP.md`; exact
stable-label correspondence is in `CLAIM_MAP.md`; byte identities are in
`Certificate/SHA256SUMS`.

## Certificate verdict

Within the explicitly stated finite-domain conditions and Lean's disclosed
logical foundations:

1. the formal theorem has the same quantifier order, A1--A8 hypotheses,
   representation, positivity/nonconstancy requirements, and same-witness
   block conclusion as v3 Theorem 1;
2. the two non-definitional presentation bridges - finite closedness versus
   sequential closedness, and entropy-form versus ratio-form mutual
   information - are exact finite mathematical identities described above,
   not extra behavioral assumptions;
3. no project axiom, hidden theorem interface, `sorry`, `admit`, or unchecked
   proof hole lies on the final dependency path; and
4. the result is accepted by the pinned Lean kernel.
