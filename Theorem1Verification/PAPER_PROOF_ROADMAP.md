# Paper-proof roadmap following the kernel-checked Lean proof

## Status and fidelity verdict

The formal statement proved in Lean is a faithful formalization of Theorem 1 of
`trace_tempered_choice_v3`, under the readings recorded in `CLAIM_MAP.md`.  In
particular, it has the same order of quantifiers, the same eight behavioral
assumptions, one payoff index and one strictly positive trace coefficient shared
across all finite environments, and the same-witness finite-block “moreover”
clause.

The current Lean proof is not a sentence-by-sentence transcription of the
paper, but it is now a faithful formal counterpart at the level that matters
for a paper proof: the same objects are constructed in the same dependency
order, and each substantive paper lemma has a kernel-checked Lean endpoint.
The pure-trace route no longer detours through global posterior-law continuity,
a posterior-separable integrand, or the historical `FinalHMInterface` assembly.
Those declarations remain in the repository for compatibility but are absent
from the transitive dependency closure of the public theorem.

The material-payoff completion likewise follows the narrower verified branch
argument adopted in the current paper, rather than the stronger
arbitrary-continuation recursion labelled `branch-recursion` in an earlier v3
draft:

1. insertion of a continuation into one reached branch is a positive-affine
   map on the relevant terminal-law quotient;
2. the affine slope is the probability of reaching that branch;
3. this gives the required increment when a deterministic terminal payoff is
   changed;
4. deterministic payoff branches are assembled by a finite telescope; and
5. every joint payoff-record channel is reduced to that deterministic-payoff
   form by an exact sequentialization.

The kernel check therefore validates Theorem 1 and the complete dependency
chain used in its current proof.  It should not be overstated as a check of
unused auxiliary assertions or of every advertised minimal subset of the
axioms.  Appendix A contains the single pure-trace proof, Appendix B wraps that
result into Theorem 1, and Appendix C collects auxiliary results not used in
the theorem proof.

## Audit of the pure-trace proof against Lean

The revised Appendix A and the public Lean dependency chain now agree stage by
stage:

| Paper step | Kernel-checked Lean endpoint |
|---|---|
| Descend to the fixed-prior posterior-law quotient and use A2 only to close one finite-alphabet segment | `directPosteriorLawMixtureRel`; `directPosteriorLawMixtureRel_segment_calibration`; `finiteHersteinMilnorConclusion_direct_of_axioms` |
| Select the canonical zero/full-revelation normalization, propagate it to support faces, and fix the independent-product coboundary gauge | `paperCanonicalPosteriorValue`; `posteriorProductGaugeData_of_axioms`; `PosteriorProductGaugeData.product_quasi_add` |
| Obtain direct branch aggregation and the full-support scalar cocycle from affine tangents, without choosing a posterior integrand | `directBranchChain_of_posteriorValue` |
| Prove that the boundary defect is prior-independent, invariant within a support face, multiplicative over nested canonical faces, and hence a cardinal coboundary | `directGeneralFaceDefect`; `directCardinalFaceDefect_cocycle`; `directCardinalFaceDefectCocycle`; `directCoherentRelabelingFaceScales` |
| Compare product and sequential revelation scales, derive the two-grouping equation, and force the interaction coefficient to vanish | `paperScaleComparisonCore`; `interactionCollapse_of_paperScaleComparison` |
| Apply the grouping recursion and the proved finite Faddeev theorem to obtain entropy reduction and mutual information | `MIRep_of_paperInteractionCollapse`; `MIRep_of_TraceAxioms_paperReduction` |

The remaining differences are formal bookkeeping rather than different
mathematics.  Lean names every support subtype and transports distributions
through explicit equivalences; it also separates the positive-product gauge,
the raw branch scale, and the final cardinal scale in their types.  The paper
can suppress those coercions once the relevant bijections are stated.

This audit found and repaired three genuine proof-presentation defects in the
earlier prose version:

1. The simultaneous data-processing calculation applied action processing
   before record processing.  The corrected construction first forms the
   record-processed channel and then applies action processing, with the
   supplied channel taken as the exact Bayesian completion, including all null
   rows.
2. The product calculation treated the two bracketings of a Cartesian product
   as literally identical.  It now transports through the canonical
   associating bijection, after the zero/full-revelation normalisation has made
   relabeling equality exact.
3. The product gauge was not explicitly propagated to boundary priors.  The
   post-gauge boundary representative is now defined from the gauged
   full-support representative on its positive support, so support coherence
   remains definitional.

After these repairs and the Lean refactor, the two routes have the same
intermediate construction as well as the same statement and downstream
interface.  The five-stage organization remains clearer for a human reader:
product calibration is a self-contained scalar-algebra block, the branch and
face argument is a geometric block, and the product/sequential comparison is
performed only when both scales exist.  Keeping Appendix A separate from the
material-payoff completion in Appendix B avoids interleaving two logically
independent calibrations.

## Exact theorem being proved

Fix a finite payoff set \(O\), with at least two elements.  For every nonempty
finite action set \(A\), nonempty finite record set \(R\), and channel

\[
K:A\longrightarrow \Delta(O\times R),
\]

there is a preference relation \(\succeq_K\) on \(\Delta(A)\).  The theorem
asserts that Axioms (A1)–(A8) are equivalent to the existence of a nonconstant
\(u:O\to\mathbb R\) and a number \(\lambda>0\) such that, simultaneously for
all such \(A,R,K\) and all \(q,p\in\Delta(A)\),

\[
q\succeq_Kp
\quad\Longleftrightarrow\quad
V(q,K)\ge V(p,K),
\]

where

\[
V(q,K)
=\sum_{a,o,r}q(a)K(o,r\mid a)u(o)
+\lambda I_{qK}(A;O,R).
\]

The same pair \((u,\lambda)\) must represent comparisons between priors
supported on distinct blocks of every finite common-payoff block environment.
Lean uses natural logarithms in mutual information.  Changing to any other
base greater than one only rescales the positive constant \(\lambda\).

The formal treatment takes the weakest literal reading of the “moreover”
clause: under the axioms, there exist particular witnesses \(u,\lambda\) that
represent both the within-channel and all stated block comparisons.  Axiom
(A6) is read with a common finite record family for the branches being
compared; when two continuations originally have different record types, the
Lean proof embeds both in a common tagged sum.  These readings should remain
explicit in the paper.

## Notation for the proof

For a prior \(q\) and channel \(K\), put

\[
p_{qK}(o,r)=\sum_a q(a)K(o,r\mid a).
\]

For every reached pair \((o,r)\), let

\[
\pi_{or}^{qK}(a)
=\frac{q(a)K(o,r\mid a)}{p_{qK}(o,r)}
\]

be the posterior.  The marked terminal law is the finite law

\[
\eta_{qK}
=\sum_{(o,r):p_{qK}(o,r)>0}
 p_{qK}(o,r)\,\delta_{(o,\pi_{or}^{qK})}.
\]

It records exactly the terminal payoff and the posterior about the action.  In
the Lean development, a “marked experiment” is a finite implementation of such
a law.  Two marked experiments are identified when all integrals against test
functions of \((o,\pi)\) agree.  Since the spaces are finite, this is equality
of marked terminal laws.

For alternatives living in different channel environments, write
\((q,K)\succeq(p,L)\) for the comparison obtained by placing \(K\) and \(L\) in
a common-payoff two-block channel and comparing the corresponding
block-supported priors.  This derived relation is not a new primitive.

The first auxiliary fact to establish is the following replacement calculus.
If \((q,K)\sim(q,K')\) and \((p,L)\sim(p,L')\), then

\[
(q,K)\succeq(p,L)
\quad\Longleftrightarrow\quad
(q,K')\succeq(p,L').
\]

The proof uses a common four-block environment containing all four
alternatives, Axiom (A3) to make unused blocks irrelevant, and transitivity
from Axiom (A1).  The same construction gives completeness, transitivity,
reflexivity, orientation reversal, and the usual weak/strict/indifference
calculus for the derived pair relation.  This step is explicit in Lean because
within-channel weak order alone does not automatically provide transitivity
between objects initially represented in different block channels.

## Forward direction: from Axioms (A1)–(A8) to the representation

For clarity, the paper proof can assume the full axiom bundle throughout.
Lean proves the theorem from that bundle.  Some v3 lemmas advertise smaller
subsets of the axioms; those minimal-dependence labels are not all independently
certified by the formalization and are unnecessary for Theorem 1.

### 1. Delete null actions and prove independent-dummy neutrality

Let \(S=\operatorname{supp}q\), let \(q^S\) be the restriction of \(q\) to
\(S\), and let \(K^S\) be the restriction of the rows of \(K\) to \(S\).
Projection \(S\hookrightarrow A\) and inclusion back into \(A\) give action
reports satisfying the exact joint-law equation in Axiom (A5).  On reported
actions of zero probability, the completion of the reported channel is
arbitrary; the axiom and the proof quantify over every such completion.  Applying
(A5) in both directions gives

\[
(q,K)\sim(q^S,K^S).
\]

Consequently every boundary-prior question may be moved to a full-support
prior on its support and transported back after the calculation.

Now let \(s\in\Delta(B)\), put \((q\otimes s)(a,b)=q(a)s(b)\), and lift \(K\)
by ignoring \(b\):

\[
K^\uparrow(o,r\mid a,b)=K(o,r\mid a).
\]

Projecting \((a,b)\) to \(a\) is an admissible action report.  Conversely,
from \(a\), report \((a,b)\) after drawing \(b\sim s\) independently.  The two
exact joint-law identities required by (A5) hold, so

\[
(q\otimes s,K^\uparrow)\sim(q,K).
\tag{D}
\]

Both support restriction and dummy neutrality will later be needed as exact
numerical identities, not merely ordinal observations.

### 2. Terminal-law sufficiency

Fix a full-support prior \(q\).  Suppose \(K\) and \(L\) have the same marked
terminal law.  For every payoff-posterior pair \((o,\pi)\), let
\(M_K(o,\pi)\) denote the total probability of the records of \(K\) that
produce that pair.  Define a payoff-preserving stochastic processor from a
record \(r\) of \(K\) to a record \(s\) of \(L\) by assigning positive
probability only when \(r\) and \(s\) induce the same payoff and posterior,
and, in that class, using

\[
T(s\mid o,r)
=\frac{p_{qL}(o,s)}{M_L(o,\pi_{or}^{qK})}.
\]

If the denominator is zero, choose an arbitrary probability row; such a row is
unreached and has no effect.  Equality of terminal laws says that the matching
class masses for \(K\) and \(L\) are equal.  Bayes’ identity

\[
q(a)K(o,r\mid a)=p_{qK}(o,r)\pi_{or}^{qK}(a)
\]

and full support of \(q\) then show, after summing within each class, that
postprocessing \(K\) by \(T\) gives \(L\).  Construct the reverse processor in
the same way.  Axiom (A4) gives both weak comparisons, hence

\[
\eta_{qK}=\eta_{qL}
\quad\Longrightarrow\quad
(q,K)\sim(q,L).
\tag{TL}
\]

The replacement calculus above allows this indifference to be substituted
inside any pair comparison.  For a boundary prior, first restrict to the
support as in Step 1.  This proof also handles zero-mass posterior classes
explicitly.

The Lean route differs slightly from v3 here.  It does not first define the
entire abstract set of all finite Bayes-plausible laws and prove a global
implementation formula.  It works with actual finite marked experiments and
then quotients them by (TL).  This domain is closed under every mixture and
embedding used below and contains every alternative in the theorem, so it is
sufficient for the representation proof.

### 3. Derive public-mixture independence and an affine index on each fibre

Given marked experiments \(E,G\) at the same full-support prior \(q\) and
\(t\in[0,1]\), define their public mixture by drawing an action-independent
binary signal, running \(E\) on the first branch and \(G\) on the second, and
retaining the branch tag in the record.  Its terminal law is exactly

\[
\eta_{q,tE\oplus(1-t)G}
=t\eta_{qE}+(1-t)\eta_{qG}.
\tag{M}
\]

For \(0<t<1\), Axiom (A6), including its strict clause, completeness, and
terminal-law replacement imply

\[
E\succeq_q L
\quad\Longleftrightarrow\quad
tE\oplus(1-t)G\succeq_q tL\oplus(1-t)G.
\tag{I}
\]

If branch record types differ, replace them by disjoint tagged sums before
applying (A6).  This is merely type alignment: the resulting channels have the
same marked terminal laws as the intended public mixtures.

Let \(\mathcal M_q\) be the quotient of finite marked experiments at \(q\) by
equality of marked terminal laws.  Formula (M) makes it a mixture space, and
(I) gives mixture independence.  Axiom (A2) supplies the needed Archimedean
content along every segment: for fixed endpoints and a fixed comparator, put
the alternatives into the finite union of their record alphabets.  The upper
and lower contour sets of \(t\in[0,1]\) are closed by (A2).  Completeness and
connectedness of \([0,1]\) then give the segment-calibration property used by
the mixture-space theorem.  Therefore the quotient order has a real-valued
affine representative \(W_q\):

\[
W_q(tE+(1-t)G)=tW_q(E)+(1-t)W_q(G).
\tag{A}
\]

This is the checked cardinalization step.  It is slightly more precise than
the sentence in v3 saying that continuity on the whole \(\mathcal E_q\)
allows a direct application of a mixture-space theorem: Lean proves exactly
the fixed-alphabet segment calibration required by the theorem it invokes.

### 4. Construct and normalize the material payoff index

On a singleton action set, records contain no information about the action.
By terminal-law sufficiency, an alternative is therefore equivalent to its
payoff lottery \(\ell\in\Delta(O)\).  The public-mixture argument and (A2)
give an affine representation \(U\) of these lotteries.  Axiom (A7) supplies
two deterministic outcomes, call them \(o^+\) and \(o^-\), with
\(o^+\succ o^-\).  Normalize

\[
U(\delta_{o^-})=0,
\qquad
U(\delta_{o^+})=1,
\]

and define

\[
u(o)=U(\delta_o).
\]

Affinity on the finite simplex gives

\[
U(\ell)=\sum_o\ell(o)u(o).
\tag{EU}
\]

In particular, \(u(o^-)=0\), \(u(o^+)=1\), and \(u\) is nonconstant.

An action report may ignore its input and independently draw any target prior.
Applying (A5) in both directions shows that the ranking of action-independent,
uninformative payoff lotteries is the same for every prior and action
alphabet.  Normalize each affine \(W_q\) by requiring

\[
W_q(\text{payoff lottery }\ell)=\sum_o\ell(o)u(o).
\tag{N}
\]

Two distinct anchors, \(o^-\) and \(o^+\), make this normalization unique.

Dummy lifting is an affine order embedding from the \(q\)-fibre to the
\(q\otimes s\)-fibre.  Affine uniqueness would allow a map \(x\mapsto cx+d\)
with \(c>0\), but the two normalized payoff anchors have the same values on
both fibres, forcing \(c=1\) and \(d=0\).  Hence (D) strengthens to

\[
W_{q\otimes s}(E^\uparrow)=W_q(E).
\tag{DN}
\]

To compare alternatives at priors \(q\in\Delta(A)\) and
\(p\in\Delta(B)\), lift the first by an independent \(p\)-coordinate and the
second by an independent \(q\)-coordinate.  Both now live on the common prior
\(q\otimes p\).  The replacement calculus, block coherence, and (DN) imply

\[
(q,E)\succeq(p,G)
\quad\Longleftrightarrow\quad
W_q(E)\ge W_p(G).
\tag{B}
\]

Support restriction handles boundary priors.  Formula (B) is the common-scale
block bridge needed at the end of the theorem.

### 5. Import the pure-record characterization from Appendix A

Fix the normalized low outcome \(o^-\), and lift every pure record experiment
\(P:A\to\Delta(R)\) to the constant-payoff channel

\[
K_P(o,r\mid a)
=\mathbf 1_{\{o=o^-\}}P(r\mid a).
\]

On this restriction, the eight axioms induce the pure-record hypotheses used
in Appendix A.  In Lean this is the theorem
`inducedPure_traceAxioms_of_components`; it takes exactly A1--A6 and A8, with
no A7 hypothesis.  The
ordinal conclusion and finite-block same-scale conclusion are obtained by a
direct application of the already checked
`provedMainCharacterizationWithMoreover`.  Thus, on every fixed-prior fibre,

\[
K_P\succeq K_Q
\quad\Longleftrightarrow\quad
I_q(A;R_P)\ge I_q(A;R_Q).
\tag{MI-order}
\]

This is where the hard Appendix A result is fully used.  It is not replaced by
an informal information-theoretic convention.

Mutual information is itself affine under public mixtures of posterior laws.
The constant-low embedding into the marked-terminal quotient is affine and
order-reflecting.  Therefore both \(W_q\) restricted to the constant-low face
and mutual information are affine representatives of the same nonconstant
order.  Positive-affine uniqueness yields, for every nontrivial full-support
prior,

\[
W_q(K_P)=\lambda_q I_q(A;R)+b_q,
\qquad \lambda_q>0.
\]

The uninformative constant-low experiment has mutual information zero and,
by (N), value \(u(o^-)=0\).  Hence \(b_q=0\):

\[
W_q(K_P)=\lambda_q I_q(A;R).
\tag{Fibre-MI}
\]

The coefficient is global.  Let \(q\) and \(p\) be two nontrivial
full-support priors.  Lift a nonconstant pure experiment at \(q\) to
\(q\otimes p\) by adding an independent right dummy.  Equation (DN) preserves
its value, and the information identity

\[
I_{q\otimes p}((A,B);R)=I_q(A;R)
\]

preserves its mutual information.  Comparing (Fibre-MI) before and after the
lift gives \(\lambda_{q\otimes p}=\lambda_q\).  A symmetric left-dummy lift
gives \(\lambda_{q\otimes p}=\lambda_p\), hence \(\lambda_q=\lambda_p\).
Lean fixes the uniform prior on `ULift Bool` as a reference fibre and defines
the common number \(\lambda\) there.  Axiom (A8), equivalently the strict
ranking of full revelation over no revelation at a genuinely uncertain
full-support prior, gives

\[
\lambda>0.
\]

Consequently every surely-low marked experiment, including one whose record
also carries redundant payoff tags, satisfies

\[
W_q(E)=\lambda I_q(A;O,R).
\tag{Low}
\]

This route replaces the v3 argument through a single global increasing
function \(\varphi(I)\), erasure intervals \([0,\log n]\), and a Jensen
equation.  The conclusion is the same; Lean obtains it fibre by fibre from
affine uniqueness and then aligns fibres by exact dummy identities.

### 6. Set up insertion into one reached branch

Let \(q\) be full support and nontrivial, let
\(P:A\to\Delta(Y)\) be a first-stage record channel, and fix a branch
\(y\in Y\).  Write

\[
m=m(y)=\sum_aq(a)P(y\mid a),
\qquad
r(a)=\frac{q(a)P(y\mid a)}{m}
\]

when \(m>0\).  The posterior \(r\) may lie on the boundary even though \(q\)
is full support.  Let \(S=\operatorname{supp}r\), and let \(r^S\) be its
full-support restriction.

Fix all branches other than \(y\) at the deterministic low payoff and an
uninformative continuation.  Given a marked continuation experiment \(E\) on
\(S\), extend it to the ambient action alphabet on the reached support and
insert it at branch \(y\).  Call the resulting marked experiment
\(\operatorname{Ins}_y(E)\).

Axiom (A6), its strict clause, support restriction, and the pair-order calculus
show that insertion preserves and reflects the continuation order.  Public
mixtures commute with insertion at the level of marked terminal laws.  Thus
the pullback

\[
E\longmapsto W_q(\operatorname{Ins}_y(E))
\]

is another affine representation of the normalized order on the \(r^S\)-fibre.
Positive-affine uniqueness gives constants \(c_y>0,d_y\) such that

\[
W_q(\operatorname{Ins}_y(E))
=c_yW_{r^S}(E)+d_y.
\tag{Ins}
\]

This is the general affine fact about continuation insertion that Lean needs.
Notice that it is a one-branch statement with all other branches at a fixed
low background.  It does not yet assert the full recursion formula for an
arbitrary profile of continuations.

### 7. Identify the insertion slope with branch probability

Assume first that \(S\) has at least two actions.  Compare two constant-low
continuations on \(S\):

* \(E^{\mathrm{full}}\), which fully reveals the action in \(S\);
* \(E^{0}\), which has an uninformative one-point record.

By (Low), their local values differ by

\[
W_{r^S}(E^{\mathrm{full}})-W_{r^S}(E^0)
=\lambda H(r^S).
\tag{L1}
\]

The mutual-information chain rule for branch insertion is proved as an exact
finite identity:

\[
I_q\!\left(A;\operatorname{Ins}_y(E)\right)
=I_q(A;Y)+m I_{r^S}(A;E).
\tag{Chain}
\]

Support extension does not change the continuation mutual information.  Since
both inserted experiments pay \(o^-\) surely, (Low) and (Chain) give

\[
W_q(\operatorname{Ins}_y(E^{\mathrm{full}}))
-W_q(\operatorname{Ins}_y(E^0))
=\lambda m H(r^S).
\tag{L2}
\]

On the other hand, subtracting the two instances of (Ins) and using (L1)
gives \(c_y\lambda H(r^S)\).  Full support and nontriviality imply
\(H(r^S)>0\), while \(\lambda>0\).  Cancellation therefore yields

\[
c_y=m.
\tag{Slope}
\]

Now compare, locally, the deterministic payoff \(o\) with the deterministic
low payoff.  By (N), their local values are \(u(o)\) and \(0\).  Subtracting
the corresponding instances of (Ins), using (Slope), and noting that the
intercept cancels gives

\[
W_q(\operatorname{Ins}_y(o))
-W_q(\operatorname{Ins}_y(o^-))
=m u(o).
\tag{PI}
\]

If \(S\) is a singleton, there is no nonzero local information direction with
which to perform the calibration.  Adjoin to the original action an independent
full-support uniform `ULift Bool` dummy.  The reached posterior becomes
\(r\otimes s\), whose support is nontrivial.  The branch probability is still
\(m\), and exact dummy neutrality preserves both compound values in (PI).
Apply the preceding argument in the enlarged problem and project the dummy
away.  Thus (PI) holds for every positive-probability branch.

If \(m=0\), changing the terminal payoff at branch \(y\) leaves the marked
terminal law unchanged.  Terminal-law sufficiency makes the value difference
zero, which is again \(m u(o)\).  Hence (PI) holds for all branches, including
unreached ones.

### 8. Remove the low-background restriction and telescope payoff branches

The proof only needs deterministic terminal continuations.  For two payoff
profiles that differ at branch \(y\), the value increment is independent of
the deterministic payoffs assigned to the other branches.  To see this without
assuming a linear formula in advance, use a public coin of probability one
half.  Cross the two backgrounds and the two payoffs so that

\[
\tfrac12 E(B,y\mapsto o)
+\tfrac12 E(B',y\mapsto o^-)
\]

and

\[
\tfrac12 E(B,y\mapsto o^-)
+\tfrac12 E(B',y\mapsto o)
\]

have exactly the same marked terminal law: branch by branch, the same two
deterministic outcomes occur with the same masses.  Affinity of \(W_q\) and
terminal-law equality imply equality of the crossed averages.  Rearranging
shows

\[
W_q(E(B,y\mapsto o))-W_q(E(B,y\mapsto o^-))
=W_q(E(B',y\mapsto o))-W_q(E(B',y\mapsto o^-)).
\tag{BG}
\]

Take \(B'\) to be the all-low background and use (PI).  Then change the
finitely many branches one at a time.  A finite induction, or telescope, gives
for every deterministic payoff profile \(g:Y\to O\),

\[
W_q(P,g)-W_q(P,o^-)
=\sum_{y\in Y}m(y)u(g(y)).
\tag{Tel}
\]

The all-low compound is a surely-low experiment.  Its information is exactly
the information in the first-stage record:

\[
I_q(A;Y,o^-)=I_q(A;Y).
\]

Using (Low), \(u(o^-)=0\), and (Tel),

\[
W_q(P,g)
=\lambda I_q(A;Y)+\sum_y m(y)u(g(y)).
\tag{DP}
\]

Equation (DP), not the stronger arbitrary-continuation recursion from the
earlier v3 draft, is the decisive assembly lemma in the checked proof.

### 9. Sequentialize an arbitrary payoff-record channel

Take an arbitrary channel \(K:A\to\Delta(O\times R)\), and put
\(Y=O\times R\).  Define the first stage

\[
P_K(y\mid a)=K(y\mid a),
\qquad y=(o,r),
\]

and after branch \(y=(o,r)\), pay \(o\) deterministically and reveal no further
information.  The resulting compound is the sequentialized channel.

There are exact payoff-preserving record processors in both directions.  From
the original channel, copy the observed pair \((o,r)\) into the sequential
record; from the sequentialized channel, delete the duplicate.  Both processors
leave the payoff coordinate unchanged.  Axiom (A4), applied twice, and the
replacement calculus give indifference between \(K\) and its
sequentialization.

Apply (DP) with \(g(o,r)=o\).  The first-stage mutual information is

\[
I_q(A;Y)=I_{qK}(A;O,R),
\]

and the material term is

\[
\sum_{o,r}p_{qK}(o,r)u(o)=\mathbb E_{q,K}[u(O)].
\]

Therefore, for every nontrivial full-support prior,

\[
W_q(K)=\mathbb E_{q,K}[u(O)]+
\lambda I_{qK}(A;O,R).
\tag{V}
\]

If the action set is a singleton, mutual information is zero.  Terminal-law
sufficiency reduces the channel to its payoff lottery, and (EU) gives (V)
directly.  Thus no nontriviality assumption remains.

For an arbitrary boundary prior, restrict to its support, apply (V), and use
the exact identities saying that support restriction preserves the payoff
marginal and mutual information.  Transport the result back with Step 1.  This
proves (V) for every prior in the theorem.

### 10. Recover within-channel and finite-block comparisons

At a full-support prior, \(W_q\) represents marked-experiment comparisons by
construction, so (V) gives the desired numerical representation.  For two
different priors or action alphabets, use the common-product lift and the
block bridge (B).  For boundary priors, first restrict to supports.  Hence

\[
(q,K)\succeq(p,L)
\quad\Longleftrightarrow\quad
V(q,K)\ge V(p,L)
\]

for the derived common-payoff pair comparison.

Taking \(K=L\), and using Axiom (A3) to identify a within-channel comparison
with the corresponding duplicated-block comparison, gives

\[
q\succeq_Kp
\quad\Longleftrightarrow\quad
V(q,K)\ge V(p,K).
\]

For a finite family of blocks, Axiom (A3) says that blocks other than the two
being compared are irrelevant.  Reducing to the two-block environment and
using the pair formula proves the “moreover” clause.  The witnesses are exactly
the same normalized \(u\) and global \(\lambda\) constructed above.

This completes the forward implication.  Axiom (A7) gave nonconstancy of
\(u\), and Axiom (A8) gave \(\lambda>0\).

## Converse direction: the represented value satisfies all eight axioms

Assume a nonconstant \(u:O\to\mathbb R\) and \(\lambda>0\), and define

\[
V(q,K)=\mathbb E_{q,K}[u(O)]+\lambda I_{qK}(A;O,R).
\]

Define each primitive relation by numerical comparison of \(V\).  Then:

1. **Axiom (A1).**  The usual order on \(\mathbb R\) is complete and
   transitive, so every \(\succeq_K\) is a weak order.

2. **Axiom (A2).**  On a fixed finite alphabet, expected utility is linear in
   the prior and mutual information is continuous, with the convention
   \(0\log 0=0\).  Therefore the upper and lower contour sets in every
   one-dimensional prior mixture are closed.

3. **Axiom (A3).**  Under a block-supported prior the block tag is constant.
   Adding or removing that constant tag changes neither the payoff law nor
   mutual information.  Duplicating a channel into blocks and adding irrelevant
   blocks therefore preserve every represented comparison.

4. **Axiom (A4).**  A payoff-preserving record processor leaves the payoff
   marginal, and hence expected utility, unchanged.  It produces a Markov chain
   \(A-(O,R)-(O,S)\), so the data-processing inequality gives
   \(I(A;O,S)\le I(A;O,R)\).  Since \(\lambda>0\), processing cannot improve
   represented value in the forbidden direction.

5. **Axiom (A5).**  For every action-report completion satisfying the axiom’s
   exact joint-law equation, the payoff-record marginal is unchanged.  Thus the
   expected-utility term is equal before and after reporting.  The joint law
   gives the Markov chain \((O,R)-A-B\), including arbitrary rows attached to
   zero-probability reported actions, and data processing gives
   \(I(B;O,R)\le I(A;O,R)\).

6. **Axiom (A6).**  For a first-stage channel with branch masses \(m(y)\),
   reached posteriors \(q_y\), and continuation profile \(K^y\), the two exact
   finite chain rules are

   \[
   \mathbb E[u(O)]
   =\sum_y m(y)\mathbb E_{q_y,K^y}[u(O)]
   \]

   and

   \[
   I(A;Y,O,R)
   =I(A;Y)+\sum_y m(y)I_{q_y,K^y}(A;O,R).
   \]

   Therefore the difference between the values of two continuation profiles
   under a common first stage is

   \[
   \sum_y m(y)
   \bigl(V(q_y,K^y)-V(q_y,L^y)\bigr).
   \]

   Branchwise weak inequalities make this sum nonnegative.  A strict
   inequality on any branch with \(m(y)>0\) makes it strictly positive.  These
   are exactly the weak and strict clauses of (A6).

7. **Axiom (A7).**  Since \(u\) is nonconstant, choose \(o^+,o^-\) with
   \(u(o^+)>u(o^-)\).  At singleton action sets the trace term is zero, so the
   two deterministic payoffs are strictly ranked.

8. **Axiom (A8).**  At a nontrivial full-support prior \(q\), an uninformative
   record has mutual information zero, while full revelation has
   \(I(A;A)=H(q)>0\).  The payoff is constant in both alternatives.  Since
   \(\lambda>0\), full revelation is strictly preferred.

This proves the reverse implication.  The Lean development checks the data
processing and chain-rule identities rather than taking them as hidden axioms.

## How the current v3 paper follows the checked proof

The main-text four-step sketch gives the architecture.  Appendix B implements
the checked route as follows.

1. It retains terminal-law sufficiency and includes the explicit finite matching
   processor, the zero-mass-class convention, and the four-block replacement
   argument.  It states support restriction separately.

2. It replaces the direct appeal to a continuous affine representative on the
   whole abstract \(\mathcal E_q\) by the quotient of attainable finite marked
   experiments and the fixed-alphabet segment-calibration argument.  One may
   still mention the implementation formula as intuition, but it is not a
   dependency of the verified proof.

3. It constructs the material payoff affine index first, normalizes low and high
   anchors to \(0\) and \(1\), and then normalizes every marked fibre by those
   anchors.  It proves dummy invariance numerically by affine uniqueness.

4. It invokes Appendix A for the ordinal mutual-information order.  It replaces
   the global \(\varphi\)/erasure-interval argument by
   fixed-fibre affine uniqueness plus product-dummy alignment of the
   coefficients.  This mirrors the checked proof exactly and is shorter.  The
   cardinal identity is first calibrated at the normalized low payoff; the
   ordinal Appendix A comparison remains available at every constant payoff,
   and the final representation then covers every payoff.

5. It replaces the stronger arbitrary-continuation branch recursion as a
   dependency of Theorem 1 with Steps 6–8 above: support-face affine insertion,
   entropy calibration of its slope, the dummy treatment of singleton reached
   supports, zero-mass branches, crossed-mixture background independence, and
   finite deterministic-payoff telescoping.

6. It retains sequentialization, shows the copy and delete processors explicitly,
   and splits off the singleton-action case before using the nontrivial branch
   argument.

7. In the converse, it retains the direct verification and states the two chain
   rules and the exact null-row handling for action reports.

The stronger arbitrary-continuation recursion formula is consistent with the
final representation and follows after Theorem 1 has been proved, but it is
not used as an intermediate dependency.  Appendix B uses only the narrower
branch-insertion and deterministic-telescope route checked in Lean.

## Lean correspondence

| Paper-proof component | Principal checked declarations |
|---|---|
| Formal theorem and eight axioms | `Statements.lean`: `Theorem1Statement`, `TraceTemperedAxioms` |
| Derived pair-order/replacement calculus | `PairOrder.lean` |
| Support deletion and dummy neutrality | `SupportDummy.lean`: `pairWeak_iff_supportRestriction`, `pairWeak_iff_independentDummy` |
| Terminal-law matching | `MarkedTerminal.lean`: `markedExperimentRecordPostprocesses_of_sameMarkedTerminalLaw`, `finiteMarkedBlackwellEquivalence`, `pairWeak_respects_sameMarkedTerminalLaw` |
| Public-mixture independence and HM calibration | `MarkedHM.lean`: `markedPairWeak_publicMix_independence`, `markedTerminalMixtureRel_independence`, `markedTerminalMixtureRel_segment_calibration`, `markedTerminalHMCalibratableWeakOrder` |
| Material expected utility | `MaterialUtility.lean`: `payoffLotteryAffineUtility_exists`, `materialPayoffUtility`, `materialAffineUtility_eq_expected` |
| Normalized common fibre scale | `NormalizedMarked.lean`; `CommonMarkedScale.lean`: `pairWeak_markedExperiments_iff_normalizedMarkedUtility` |
| Appendix A pure-trace input | `PureTrace.lean`: `inducedPure_traceAxioms_of_components`, `inducedPure_MIRep_of_components`, `inducedPure_blockSameScale_of_components` |
| Affine MI and global trace coefficient | `PureMIAffine.lean`, `PureMarkedEmbedding.lean`; `GlobalTraceScale.lean`: `traceLambdaAtPrior_eq_globalTraceLambda`, `globalTraceLambda_pos` |
| Surely-low formula | `ConstantLowGeneral.lean`: `normalizedMarkedUtility_eq_globalTraceLambda_mul_mutualInfo_of_sureLow` |
| Branch insertion and support face | `BranchInsertion.lean`: `normalizedMarkedUtility_branchInsertion`; `SupportBranchInsertion.lean`: `normalizedMarkedUtility_supportBranchInsertion` |
| MI insertion chain rule | `BranchInformation.lean`: `mutualInfo_branchInsertionExperiment`; `SupportBranchNumerics.lean`: `mutualInfo_supportBranchInsertionExperiment` |
| Branch-mass calibration | `BranchScaleIdentification.lean`: `supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport` |
| Singleton-support dummy bridge | `DummyBranchBridge.lean`; `PositiveBranchIncrement.lean`: `positiveBranchPayoffIncrementFormula` |
| Background independence and telescope | `PayoffBranchBackground.lean`: `normalizedMarkedUtility_branchPayoff_difference_background_independent`; `PayoffBranchTelescope.lean`: `normalizedMarkedUtility_payoffBranch_sum` |
| Deterministic payoff formula | `FullSupportValueAssembly.lean`: `normalizedMarkedUtility_payoffBranchFormula` |
| Sequentialization | `Sequentialization.lean`: `sequentialization_pairWeakEquiv`; `FullSupportValueAssembly.lean`: `normalizedMarkedUtility_sequentializedChannel` |
| Singleton action and boundary priors | `SingletonActionValue.lean`, `ValueSupport.lean` |
| Within/block assembly | `RepresentationAssembly.lean`, `TheoremClosure.lean` |
| Converse | `Benchmark.lean`: `traceTemperedAxioms_of_representation` |
| Kernel entry point | `Proof.lean`: `trace_tempered_choice_v3_theorem1` |

## Trust boundary and scope

`Axioms.lean` declares no extra mathematical axiom.  The proof imports a
kernel-checked pure-trace theorem with the same statement and common-scale
block conclusion as Appendix A, and otherwise derives every mathematical step
in Lean.  The standard declarations reported by
`#print axioms`—propositional extensionality, classical choice, and quotient
soundness—are Lean/Mathlib foundations used by the construction, not additional
behavioral or information-theoretic assumptions.

This roadmap concerns only Theorem 1.  It does not assert that later uniqueness
or comparative-statics results in v3 have been formalized.  Nor does it claim
that every individual minimal-axiom claim for each auxiliary paper lemma has
been checked.  It records the dependency chain that is sufficient, faithful to
the theorem’s hypotheses and conclusion, and accepted by the Lean kernel.
