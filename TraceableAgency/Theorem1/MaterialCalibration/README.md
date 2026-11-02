# Material-based branch calibration

This is an additive, experimental route toward a shorter proof of Theorem 1.
The original representation proof and its public theorem remain unchanged.

The completed first stage identifies continuation weights in material units
**before** identifying information value. It uses the exact paper axioms through
`branchCalibration_of_axioms` in namespace
`TraceableAgency.Theorem1.MaterialCalibration`.
The proof-facing bundle is the existing equivalent relevance bridge.

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
  Here `P` records `y` and the terminal payoff is `g(y)`; the value of the record
  at a constant payoff has not yet been identified. Null records contribute zero.

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

## Verification

```sh
lake build TraceableAgency.Theorem1.MaterialCalibration.Audit
lake build TraceableAgency.Theorem1.Proof TraceableAgency.Audit.Axioms
```

The new audit recursively checks actual declaration dependencies, including
proof bodies. It rejects information/entropy identification, the old trace-scale
calibration, and kernel axioms outside `propext`, `Classical.choice`, and
`Quot.sound`. It distinguishes reusable elementary helpers from identification
results that happen to share an imported module. The original theorem's build
and axiom audit are checked separately.

## Remaining representation work

The new route is not yet a second proof of the full representation theorem.
It still needs to derive the entropy chain rule and its continuity properties
for the material-normalized full-revelation value, apply the generic finite
Faddeev characterization, and assemble the representation and boundary cases.
The existing pure-trace proof remains available independently; this shortcut
uses material relevance and does not replace that separate result.

The next reusable endpoint is
`GenericFaddeev.finiteFaddeev_characterization`, whose hypotheses concern a
generic distribution functional: nonnegativity, zero at point masses,
relabeling and support invariance, binary-interior continuity, and `sigmaDist`
strong additivity. First telescope the arbitrary-background branch comparison
over all records to obtain the needed compound-value identity. A2 and material
lottery comparisons must then supply continuity on the new normalization.

The eventual representation assembly should be parameterized by the newly
obtained coefficient. Reusing `FullSupportValueAssembly` or
`RepresentationAssembly` unchanged would reintroduce the old proof through
their hard-coded `globalTraceLambda`.
