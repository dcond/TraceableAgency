# Material-first proof of Theorem 1

This is a complete second proof of the original `Theorem1StatementV10`:
the exact A1--A8 characterization and its same-witness finite-block clause.
The original representation proof and its public theorem remain unchanged.

The first stage identifies continuation weights in material units **before**
identifying information value. The second stage derives entropy reduction,
grouping, and continuity, invokes the preference-free finite Faddeev theorem,
and assembles the representation. The proof-facing axiom bundle is the existing
equivalent relevance bridge. No old preference-to-information identification
or trace-scale calibration is used.

```lean
import TraceableAgency.Theorem1.MaterialCalibration

#check TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1_material
-- TraceableAgency.Theorem1.Theorem1StatementV10
```

The final proof is in `Proof.lean`. Intermediate declarations below are in
namespace `TraceableAgency.Theorem1.MaterialCalibration`.

## Results

Write `W_q` for the common affine marked-experiment utility, normalized so the
uninformative low and high material outcomes have values zero and one. For a
full-support prior `q`, a first-stage channel `P`, and a reached record `y`, let
`m_y = Pr(y)` and `r_y = Pr(a | y)`, restricted to its positive support.

* `revealMaterialUnit_eq_one`: every prior's full-revelation material unit is one.
* `supportBranchInsertionScale_eq_branchMass_material`: the positive affine
  coefficient of continuation insertion is exactly `m_y`. This includes singleton
  posterior supports and arbitrary constant background payoffs.
* `normalizedMarkedUtility_supportInsertion_difference_material`:
  `W_q(insert_y E) - W_q(insert_y G) = m_y (W_{r_y}(E) - W_{r_y}(G))`.
* `normalizedMarkedUtility_compound_oneBranch_difference_material` extends this
  comparison to arbitrary continuations on all other branches, using a common
  record alphabet for the two continuations at each branch, as in A8.
* `normalizedMarkedUtility_payoffBranch_difference_from_low_material`:
  `W_q(P,g) - W_q(P,low) = sum_y m_y u(g(y))`.
  Here `P` records `y` and the terminal payoff is `g(y)`; at this stage the record
  value is still unidentified. Null records contribute zero.
* `materialTraceValue_eq_entropy_sub_expected`: with `H(q)` the value of full
  revelation at the low payoff, `T_q(P) = H(q) - sum_y m_y H(r_y)`.
  `supportedMarkedValue_constantPayoffLift_eq_entropy_sub_expected` extends this
  identity to arbitrary outer priors as well as arbitrary posterior supports.
* `materialEntropy_sigmaDist`: `H(sigmaDist p q) = H(p) + sum_k p(k) H(q_k)`,
  including zero-probability cells and conditional distributions with zeros.
* `materialEntropy_binary_continuous`: binary-interior continuity, derived
  directly from A2 and material lottery comparisons.
* `exists_pos_materialEntropy_eq_entropy`: one `lambda > 0` satisfies
  `H(q) = lambda * entropy(q)` for every finite action set and every prior.
* `theorem1StatementV10_material`: the complete original theorem statement,
  with nonconstant material utility, positive information coefficient, and
  same-witness block comparisons.

## Proof route

1. **Affine marked-law differences.** Crossed public mixtures turn an equality
   of positively scaled differences of marked laws into the same equality of
   utility differences (`MarkedDirections`). The marked variable is the pair
   consisting of the material outcome and the posterior on actions.
2. **One material unit per prior.** Under full revelation, upgrading only action
   `a` has value `q(a) a_q`. Symmetry proves this at the uniform prior. Reaching
   the uniform prior from an arbitrary full-support prior, and comparing the
   same scaled marked-law directions, proves it generally (`Units`). This uses
   ordinal affine insertion, not an identified insertion coefficient.
3. **The insertion ratio.** Comparing a revealed-action upgrade directly and
   inside a reached branch gives `c_y a_{r_y} = m_y a_q`
   (`MarkedUnitRatio`). Support restriction covers all reached posteriors.
4. **Two-cell calibration.** Put an arbitrary prior `r` beside a singleton,
   each with probability one half. Two-way A7 processing merges the actions
   into the two cells while preserving every cell-dependent payoff comparison.
   The singleton cell equates the outer and binary units; the other cell then
   forces `a_r = 1` (`Partition*`, `UnitAnchors`, `Calibration`).
5. **Arbitrary continuation backgrounds.** Equal marked-law differences transfer
   the calibrated comparison to arbitrary unchanged continuations on the other
   branches (`BranchComparison`).
6. **Material payoff separation.** Inserting deterministic payoffs and
   telescoping over records gives expected material utility plus the
   unidentified constant-payoff record value (`PayoffSeparation`).
7. **Entropy reduction.** Telescope arbitrary continuation changes, and append
   full revelation on every branch. This compound has the same marked law as
   direct full revelation, giving `T_q(P) = H(q) - sum_y m_y H(r_y)`
   (`CompoundValue`, `TraceEntropy`). Support invariance extends it to all priors
   (`SupportedValue`, `TraceEntropySupport`).
8. **Grouping.** Two-way A7 processing identifies coarse revelation of a
   partition with full revelation of its cell lottery. Apply entropy reduction
   and identify the conditional supports (`EntropyProperties`, `EntropyGrouping`).
9. **Continuity.** For any real cutoff `c`, mix a tested experiment slightly
   toward the material midpoint. Its transformed cutoff lies in `(0,1)` and
   equals a fixed material lottery's value. A2 closes both comparison sets;
   hence normalized values vary continuously with interior priors
   (`EntropyContinuity`). No boundary-continuity assumption is added.
10. **Shannon identification.** Nonnegativity, point-mass normalization,
    relabeling, support restriction, binary continuity, and grouping meet
    `GenericFaddeev.finiteFaddeev_characterization`. A4 excludes a zero
    coefficient (`EntropyPositive`, `ShannonIdentification`).
11. **Final assembly.** Entropy reduction identifies record value with
    `lambda * mutualInfo`. Material separation and reversible sequentialization
    give the full numerical formula. Support restriction removes boundary
    restrictions; A5 supplies within-channel and block comparisons. The existing
    representation-to-axioms direction completes the iff
    (`ShannonAssembly`, `ValueAssembly`, `Representation`, `Proof`).

## Verification

```sh
lake build TraceableAgency.Theorem1.MaterialCalibration.Audit
lake build TraceableAgency.Theorem1.MaterialCalibration.RepresentationAudit
lake build TraceableAgency.Theorem1.MaterialCalibration
lake build TraceableAgency.Theorem1.Proof TraceableAgency.Audit.Axioms
lake env leanchecker --fresh TraceableAgency.Theorem1.MaterialCalibration.Proof
```

Both audits recursively inspect actual declaration dependencies, including
proof bodies. `Audit.lean` keeps the calibration stage entirely free of entropy
identification. `RepresentationAudit.lean` permits generic Shannon/Faddeev
mathematics and information identities, while excluding the old preference
representation and trace-scale route. Both reject kernel axioms outside
`propext`, `Classical.choice`, and `Quot.sound`. Elementary helpers housed in
mixed-purpose modules are individually documented; their proof bodies remain
audited. The original theorem's build and axiom audit are checked separately.

## Scope

This route uses material relevance and proves Theorem 1. It does not replace
the separate pure-trace result, which intentionally does not assume material
relevance. The new assembly uses the coefficient obtained here; it never refers
to the old `globalTraceLambda`. The public theorem type is exactly unchanged.
