# Section 4 verification, paper v11

This certificate covers the mathematical choice implications in Section 4 of
[the v11 source snapshot](../Paper/trace_tempered_choice_v11.tex): the trace
test, optimal randomization, measurement, and moral hazard. It includes the
supporting optimization, compensation, and record-value results used there.
Import `TraceableAgency` for the complete current public surface. The original
Section 4 stage is exported by `TraceableAgency.Section4`; the later
[proved-result completion](V11_PROVED_RESULTS.md) adds the missing appendix
statements through `TraceableAgency.V11`.

The original Section 4 stage began at commit `05974fc` on
`codex/section3-completion`, preserving the earlier Lean proofs. The completed
mathematical Lean sources are unchanged from `5f7e8e8`. Subsequent v11 paper
revisions shorten proofs without changing their stated results or hypotheses.
See the [current certificate](FORMALIZATION_CERTIFICATE.md) for the complete
numbered-result index.

## Paper-to-Lean map

Names have prefix `TraceableAgency.Section4`; `BT` below abbreviates its
`BernoulliTechnology` namespace. The module names identify where to read the
statements and definitions, not additional assumptions.

### Trace test

| Claim | Checked declarations |
|---|---|
| Proposition 5: same consequence marginals, value gap lambda log 2, second-treatment indifference | `trace_all_marginals`, `trace_test_gap`, `traceSecond_value` |
| Positive, negative, and zero orientations | `trace_test_orientation` |
| Channel-blind impossibility and permutation-symmetric special case | `channelBlind_cannot_pass_trace_test`, `permutationSymmetric_channelBlind_trace_tie` |
| At a constant payoff, every lottery weakly beats each pure action under A1, A5–A7; action–output independence gives indifference; A4 supplies a strict instance | `qualitative_trace_weak`, `qualitative_trace_independent`, `qualitative_trace_strict_exists` |

Modules: `TraceTest`, `TraceTestQualitative`.

### Optimal randomization

| Claim | Checked declarations |
|---|---|
| Concavity, continuity, existence, and strict concavity in distinct output laws | `rowRewardValue_concave`, `continuous_rowRewardValue`, `exists_optimal`, `rowRewardValue_strictConcave_output` |
| Proposition 6: necessary and sufficient optimality condition, including boundary priors | `optimal_iff_kkt`, `preference_optimality_condition` |
| Same representation witnesses obtained from A1–A8 | `optimization_of_axioms` |
| Every reachable output has positive probability at an optimum | `exists_improvement_of_missing_output`, `optimal_coversRows` |
| Private outputs force full action support; exact pure-choice condition | `optimal_fullSupport_of_private_outputs`, `pure_optimal_iff` |
| All optima have the same output law; exact optimal face; uniqueness under affine independence of active rows | `optimal_output_unique`, `optimal_iff_output_and_active`, `optimal_unique_of_active_affineIndependent` |
| Identical rows can be collapsed, with arbitrary splitting within a class | `optimal_collapse_iff`, `material_optimal_collapse_iff` |
| Identical consequence rows make every lottery optimal | `material_constant_channel_all_optimal` |
| Zero information iff action and output are independent | `mutualInfo_eq_zero_iff_rows`, `mutualInfo_eq_zero_iff_independent` |
| Negative and zero information weights | `negative_optimal_iff`, `zero_optimal_iff`, `nonpositive_pure_optimal` |
| Corollary 7: disjoint rows give entropy and unique multinomial logit | `mutualInfo_eq_entropy_of_disjoint`, `disjoint_optimal_iff_logit`, `preference_disjoint_logit` |
| Logit odds, menu independence, and probability 1/3 for three equal-reward traces | `disjoint_menu_independent_odds`, `disjoint_equal_rewards_iff_uniform`, `disjoint_three_equal_rewards` |
| Overlap can violate IIA: exact two- and three-action example | `twoMenu_unique_optimum`, `overlap_unique_optimum`, `overlap_restricts_to_twoMenu`, `overlap_iia_ratios` |
| Equal expected rewards reduce choice to channel capacity | `constant_rewards_optimal_iff_capacity` |
| Binary pure high-reward threshold; unique interior optimum below it | `binary_pure_high_iff`, `binary_exists_unique_interior_iff` |
| Interior first-order equation and unique root | `binary_interior_optimal_iff_equation`, `binary_exists_unique_interior_root` |
| Weak comparative statics and strict interior comparative statics | `binary_gap_monotone`, `binary_lambda_monotone`, `binary_gap_strict_interior`, `binary_lambda_strict_interior` |
| Zero payoff gap makes the optimum independent of positive lambda | `binary_capacity_independent_lambda` |
| Entropy derivatives, decreasing marginal information, finite supported limits and infinite unsupported limits | `hasDerivAt_mixEntropy`, `hasDerivAt_mixEntropySlope`, `binaryGain_strictAnti`, `binaryGain_tendsto_zero_of_support`, `binaryGain_tendsto_one_of_support`, `binaryGain_tendsto_zero_of_not_support`, `binaryGain_tendsto_one_of_not_support` |

Modules: `Optimization*`, `InformationZero`, `ChoiceExamples`, `Binary/*`.
The explicit IIA example has optimum `(1/3, 4/9, 2/9)` on the three-action
menu, with odds `3/4`; restricting to the first two original rows gives the
unique fair lottery, with odds `1`.

### Measurement

| Claim | Checked declarations |
|---|---|
| Entire attainable strip of information and material utility | `attainable_information_material` |
| Parallel indifference lines, an informative indifference, unique global price | `indifference_lines`, `exists_price_identifying_indifference`, `unique_information_price` |
| Information price from actual cross-channel indifference | `behavioral_information_price` |
| Public dilution and the exact compensation identity | `dilution_value`, `dilution_information`, `dilution_material`, `dilution_indifference_iff` |
| General compensation feasibility and maximum-compensation bound | `dilution_compensation_feasible_iff_all_rates`, `dilution_max_compensation_bound`, `maximal_compensation_information_bound` |
| Proposition 8: unique compensation probability iff feasible; strict preference otherwise | `elicitation_existsUnique_iff`, `behavioral_elicitation_existsUnique_iff`, `elicitation_strict_infeasible` |
| Exact recovered coefficient; uniform-prior special case | `behavioral_elicited_price`, `uniform_elicited_price` |
| Sufficient dilution can always make elicitation feasible | `eventually_feasible_dilution` |
| Utility calibration, erasure control, invariance across designs | `material_utility_elicitation_existsUnique`, `erased_trace_controls_indifferent`, `elicited_prices_agree` |
| Shannon fair/quarter-prior ratio and rounding to 1.23 | `shannon_two_prior_prediction`, `shannon_two_prior_ratio_approx` |
| Actual Gini rival predicts 4/3; conditional on a feasible report, the capped rival returns exactly min{1,c/[(1−eps)H(q)]} | `gini_two_prior_prediction`, `capped_recovered_coefficient` |

Modules: `Measurement*`, `V11Measurement`. The experiments are actual finite channels, not
assumed value formulas. Unique global price uses nonconstant utility and a
positive information weight, as in Section 4. The implementation admits dilution zero as well;
the strictly positive dilution required by Proposition 8 is explicit in its
existence-and-uniqueness statement. Normalized utility calibration applies to
outcomes between the chosen anchors, exactly when a probability can elicit
their utility.

### Records and moral hazard

| Claim | Checked declarations |
|---|---|
| Value lost by garbling records is lambda times conditional mutual information | `information_loss_eq_conditional`, `record_garbling_value_loss` |
| Zero loss iff conditional independence, for positive lambda | `processingConditionalInfo_eq_zero_iff`, `record_garbling_value_eq_iff` |
| Recorded public mixing is affine; cost of hiding its coin | `recorded_coin_value`, `recorded_coin_hiding_cost`, `recorded_coin_hiding_eq_iff` |
| Uniform value dominance with identical payoff kernels is the more-capable order; garbling implies it, but its converse fails | `MoreCapable.uniform_value_dominance_iff`, `MoreCapable.garbling_implies_information_dominance`, `MoreCapable.exists_moreCapable_not_garbling_at_payoff` |
| Bernoulli moral-hazard information and value formulas | `BT.mutualInfo_eq`, `BT.rowRewardValue_eq` |
| Information derivatives, endpoint KL slopes, strictly negative curvature | `BT.hasDerivAt_information`, `BT.hasDerivAt_informationSlope`, `BT.informationSlope_zero`, `BT.informationSlope_one`, `BT.value_curvature_neg` |
| Exact high- and low-effort incentive thresholds and unique optimum | `BT.interval_high_optimal_iff`, `BT.interval_low_optimal_iff`, `BT.exists_unique_intervalOptimal` |
| Flat wage: unique interior optimum iff cost is below the trace threshold; zero effort otherwise | `BT.flat_wage_interior_iff`, `BT.flat_wage_unique_zero` |
| Independent random cost stays in a finite consequence space without revealing effort | `augmentedEffort_expectedUtility`, `augmentedEffort_information`, `augmentedEffort_value` |
| Averaging teammate strategies gives Bernoulli rows and preserves uniform bounds | `mixture_bernoulli`, `teamSuccess_bounds` |
| A Lipschitz function of the fraction working gives a marginal effect at most L/n | `team_fraction_gap_le` |
| Vanishing individual effect: trace premium vanishes, fixed-cost share diverges | `bernoulliKL_uniform_quadratic_bound`, `traceBonus_uniform_bound`, `traceBonus_tendsto_zero`, `costBonus_tendsto_atTop` |
| Extra visible signal has value lambda I(A;S given X), holding effort fixed | `signal_value_gain`, `BT.signalGain_eq_conditional`, `BT.signal_value_eq` |
| Reoptimized compensation exists and lies between the old-optimum gain and maximum gain | `BT.exists_signal_compensation_bounds` |
| Exact base-pay adjustment preserves participation and does not affect chosen effort | `compensation_exact_base_adjustment`, `compensation_weak_participation`, `intervalOptimal_add_base_iff` |
| Direct compensation is zero at lambda=0 | `BT.signal_compensation_zero` |
| Actual signal extension can change effort, with unchanged production probabilities | `BT.flat_signal_changes_effort`, `BT.flat_fullActionRecord_probability` |

Modules: `RecordInformation`, `RecordedCoin`, `MoreCapable*`, `SignalValue`, `MoralHazard/*`.
The signal example changes a unique zero-effort optimum to the unique interior
probability `exp(-cost/lambda)/(1+exp(-cost/lambda))` by revealing the action.
The compensation theorem permits reoptimization; it does not identify old
and new optimal lotteries.

In the finite-consequence cost implementation, `augmentedEffortChannel t q`
depends on the candidate plan `q`. The cost coordinate is independent of the
realized production variables and has expected cost `q*c`; it is not an
observed realized effort cost. Different plans therefore use different augmented
channels. The representation theorem's common-scale block clause justifies
comparing those plans, as explained in the paper's footnote. This construction
does not claim that the whole optimization takes place in one fixed augmented
channel.

The binary classification assumes distinct rows, a nonnegative payoff gap,
and positive lambda. The Bernoulli technology has `0 < p0 < p1 < 1`; its
flat-wage interior iff assumes positive cost and lambda. The team limit uses
uniformly nondegenerate success probabilities, positive gaps tending to zero,
and nonnegative lambda. A monotone Lipschitz technology supplies the `L/n`
example; divergence of the cost share assumes a fixed positive cost.

## Mathematical boundary and proof choices

The formalization uses finite probability distributions and natural logarithms.
`rowRewardValue` is expected row utility plus lambda times the existing
`mutualInfo`; `IsOptimal` compares against **every** prior on the action set.
Material row utilities are derived from payoff utility in the preference-facing
theorems. `optimization_of_axioms` obtains the same utility and positive
coefficient as the unchanged material-first representation theorem.

The real-valued `finiteKL` sum is used as divergence only under support
inclusion. Instead of extended-real arithmetic, the optimality equivalence
explicitly requires `CoversRows`; this condition is **proved necessary**, not
assumed about an optimum. Likewise the binary pure-choice iff requires both
`SupportIncluded` and the finite threshold. If an unused action can produce
a missing output, the proof constructs a profitable small deviation. Thus
the infinite-divergence case is included in the choice conclusions.

Conditional information is defined from the actual conditional channel and
posterior on actions at each reached processed output. Null outputs contribute
zero. Its equality case is proved as conditional independence. In the signal
application the processed observation is X and the retained observation is
(X,S), so the difference is exactly I(A;S given X).

The team limit uses a direct bound
`0 <= lambda * KL(p || p+d)/d <= lambda*d/epsilon^2`, uniformly when success
probabilities stay in `[epsilon,1-epsilon]`. This proves the main-text claim
without the appendix's precise quadratic coefficient and cubic Taylor
remainder. That exact expansion and the additional posterior-law formulation
inside the record-garbling proof remain outside the numbered-result claim.
Their application uses are covered by the direct bound and conditional
independence results above. The completed v11 modules now also prove the
unsupported binary endpoint limits and the more-capable/nongarbling
proposition, including the paper's exact channel counterexample. See the
[completion report](V11_PROVED_RESULTS.md) for these additions and the remaining
scope distinctions; verification of the stated results does not assert that
every intermediate calculation in Appendix B is separately formalized.

## Reproduction and trust

With the pinned Lean and mathlib versions installed:

```sh
lake exe cache get
./scripts/check_section4_certificate.sh
./scripts/check_trust_boundary.sh
```

The first script reproduces the original Section 4 certificate: it checks the
byte manifest and source hygiene, builds that entry point, runs the Section 4
and Section 3 foundation audits, checks both representation routes, and runs
`lake env leanchecker --fresh TraceableAgency.Section4.Audit`. The second
command additionally rebuilds and audits every project module, including the
later v11 additions and private helpers, with mandatory fresh replay.

`Section4/Audit.lean` enumerates every theorem in the public Section 4 namespace
loaded by its original entry point and recursively collects its axioms. It allows only `propext`,
`Classical.choice`, and `Quot.sound`, and rejects dependency on the old
preference-to-representation endpoints. There are no added mathematical axioms,
proof holes, or kernel bypasses. Generic existing probability and entropy
lemmas are reused without modification. Fresh replay checks the imported proof
declarations as well as the new ones.

The remaining human check is semantic: that the formal definitions and theorem
statements express the paper's claims. The kernel checks the deductions from
those statements and the listed foundations.
