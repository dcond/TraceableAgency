# v11 correspondence audit: statements, hypotheses, and remaining gaps

Audit baseline: commit `0786715` on `codex/section3-completion`.
This is a semantic comparison of the actual TeX and Lean definitions/types,
not a further axiom audit and not a claim inferred from successful compilation.
No paper text or mathematical proof was changed during this review.

## Text reviewed and conclusion

The canonical OneDrive v11 and `Paper/trace_tempered_choice_v11.tex` have
identical contents after removing trailing whitespace. Their line numbers
agree. Their SHA-256 hashes before whitespace normalization are respectively:

- OneDrive: `db640251a6792c3e9ae8d2d61aa64d44816fcc263857c6e000c91af095398cca`.
- Repository: `da6682b5dbe540c9eb87d743d86a7fb660e1e31a59f30560c20fff9f05071ba6`.

**Not every claim in v11 has an exact formal counterpart.** The eight numbered
main-text results, including the representation theorem, have the same
mathematical conclusions and hypotheses after the encoding
identifications below. No substantive error in those conclusions was found.
However, several minimally stated Appendix A lemmas have stronger Lean
premises, and some further claims in Appendix B are unformalized or only
partially formalized.

This audit inventories all **34 numbered results**, including remarks, and
the substantive unnumbered mathematical claims. It distinguishes:

- **Matched:** the formal statement has the paper's mathematical content,
  possibly through an equivalent encoding or a stronger checked statement.
- **Narrower:** an exported formal theorem has additional hypotheses or covers
  only part of the parameter/boundary range claimed in the paper.
- **Assembly:** checked results supply the conclusion by an identified short
  specialization or combination, but the paper's complete statement is not
  exported as one endpoint. This is not evidence that the mathematical claim
  is false, nor the same gap as an unproved substantive argument.
- **Unformalized:** the asserted result or a substantive part of its proof is
  not presently checked. Its truth is not established by the kernel audit.

Paper line references below refer to the v11 TeX. Lean paths are relative to
`TraceableAgency/`. `T/` abbreviates `Theorem1/`; `M/` abbreviates
`Theorem1/MaterialCalibration/`; `S3/` and `S4/` abbreviate `Section3/` and
`Section4/`.

## Findings requiring attention

### Substantive results not fully formalized

1. **Proposition 30, more-capable dominance and failure of the garbling
   converse** (paper 2468–2513; invoked at 913–915). There is no corresponding
   order theorem or formal erasure/BSC counterexample. Cancellation of equal
   material terms and garbling monotonicity have checked ingredients. The
   claimed separation between the two orders, including its explicit binary
   channels and derivative argument, is absent. The existing finite
   posterior-law Blackwell equivalence is a different theorem.

2. **Proposition 34, entropy-reduction audience** (2809–2853; invoked at
   1006–1011). When the observer's prior equals the actual prior, the reward
   identity follows immediately from `Info/Identities.lean:1091`. But the
   observer reward with a mismatched prior is not defined in Lean, and the
   necessity claim—equality for every channel forces `r = q` under
   `supp q ⊆ supp r` and nonzero lambda—is unformalized. The selective-revelation
   expansion and argument at 2835–2853 are not checked. The subsequent claim
   that the observer's prior must track deviations depends on this direction.

3. **Forecasting over arbitrary distributions, allowing infinite losses**
   (2784–2800; invoked at 880–883). `S4/OptimizationKL.lean:102` proves a real
   algebraic reference identity; `:64` and `:69` prove divergence
   nonnegativity/equality under support inclusion. These support the finite-loss
   interpretation. They do not verify the extended-real identity or
   minimization over every forecast, including forecasts assigning zero to
   possible outputs. Raw log-loss objectives and their optimization are not
   defined as such. Total real `finiteKL` cannot be substituted for that
   extended-real loss without its support guard.

4. **Infinite analytic limits and derivatives**: Proposition 24's limits
   `g(0+) = +∞` or `g(1−) = −∞` when the relevant support condition fails
   (2230–2231, 2258–2260) are not checked. Only the supported, finite limits
   appear in `S4/Binary/Classification.lean:83` and `:98`. The general unsupported
   directional derivative and its `lambda*d*t*log(1/t) + O(t)` expansion
   (2291–2294) are also unformalized. The exact choice conclusions are checked
   through explicit support conditions and profitable-deviation arguments.
   The real function values `binaryGain_zero/one` at `Classification.lean:66`
   and `:71` are **not** proofs of the missing infinite limits.

5. **Exact team asymptotics** (2703–2715). Neither the uniform expansion
   `KL(Bern(p) || Bern(p+d)) = d²/(2 log(b) p(1-p)) + O(d³)` nor the resulting
   trace-share leading coefficient/remainder is checked. Lean instead proves
   a uniform quadratic upper bound (`S4/MoralHazard/Teams.lean:56`) and the
   stated vanishing limit (`:85`). This verifies the main economic conclusion,
   not the displayed Taylor formulas.

6. **Record equality expressed as equality of posterior laws** (2440–2444).
   `S4/RecordInformation.lean:115` proves zero garbling cost iff conditional
   independence. The further equivalence with equality of the posterior laws,
   and the intervening almost-sure posterior identity, are not exported or
   separately proved. The proposition's stated conditional-independence
   conclusion is checked; this additional conclusion in its proof is not.

### Formal hypotheses stronger than the paper's

| Paper assertion | Actual checked scope | Consequence |
|---|---|---|
| Lemma 9, support restriction and dummy neutrality under A1, A5–A7 (1040–1056) | Relevant endpoints in `T/SupportDummy.lean:186,201,385` take the full `TraceTemperedBridgeAxioms` bundle; the replacement lemma at `:99` takes only A1 and A5 | The support/dummy conclusions used by the main theorem are checked. The complete minimal-axiom lemma is not exported as stated. |
| Lemma 11(b), affine representations under A1, A2, A5–A8, omitting A3/A4 (1165–1173) | `T/MarkedHM.lean:1333,1347,1360,1374` takes the full bridge bundle | The weaker-hypothesis version is not verified by those interfaces. Same-marked-law indifference in part (a) is proved under A6 alone. |
| Lemma 13, common material normalization without A4 (1271–1288) | `T/NormalizedMarked.lean:318`, `T/CommonMarkedScale.lean:175,190,207` use the full bridge bundle | The no-A4 common-scale theorem is not separately checked. This adds no premise to the final A1–A8 theorem. |
| General finite directional derivative requires only the deviating row's support to be covered (2284–2289) | `S4/OptimizationKKT.lean:52` requires coverage of **every** row | The exported derivative theorem is narrower. At an optimum, the stronger coverage condition is proved, so KKT itself matches. |
| Conditional-noise counterexample for every epsilon > 0 (2090–2113) | `S3/Independence/RecordProcessing.lean:13,19,242` fixes epsilon = 1 | Independence of A6 is fully proved, but not the whole parameterized family or its `1+epsilon` formula. |
| Main-text Lipschitz fraction-of-team example (850–854) | `S4/MoralHazard/Teams.lean:119` assumes a globally monotone, globally Lipschitz `G : ℝ → ℝ` | The appendix adds “increasing” at 2718, aligning the monotonicity assumption; the global-versus-feasible-domain qualification remains. The main text only says uniformly Lipschitz. A Lipschitz-only absolute-gap estimate is true but is not the exported theorem. Restricting G to the feasible fraction interval would also need an explicit extension/restricted-domain wrapper. |
| WTP feasibility at every 0 ≤ epsilon < 1, Proposition 32(iii) (2579–2591) | `S4/MeasurementDilution.lean:137` assumes epsilon > 0 | The value formula `:45` includes zero, making the missing zero-dilution iff an immediate assembly. The displayed general feasibility iff itself does not include that endpoint. |

The final characterization consumes exactly its stated eight axioms. These
findings concern the **stronger claims about weaker hypotheses** made by
individual preliminary lemmas, not additional hidden premises of Theorem 1.

### Wording that should be clarified

- **“On constant-payoff experiments alone”** (573–575) should say **“At a fixed
  constant payoff.”** If the sentence includes comparisons between experiments
  paying different sure outcomes, it is false. With utilities zero and one,
  low-payoff full revelation of a fair coin has value `lambda*log 2`, while
  high-payoff silence has value one. In natural-log units, changing lambda from one to two reverses
  their ranking. The intended common-payoff reading is valid.
- The strict comparative-statics sentence at 709–710 must retain its preceding
  **below-threshold/interior** qualification. The appendix states this correctly
  at 2237–2238, and the Lean strict theorems require both compared optima to be
  interior. It would be false as a global strictness claim: sufficiently large
  payoff gaps give the same pure optimum over an interval of lambda values.

## Definitions, axioms, and equivalent encodings

| Paper | Lean | Comparison of hypotheses and meaning |
|---|---|---|
| Finite fixed payoff alphabet, at least two outcomes; arbitrary finite nonempty A/R (189–204) | `T/Statements.lean:46,659`; `Basic/Dist.lean:24`; `Basic/Channel.lean:24` | Matches. All boundary priors and real probabilities are admitted. Universe/equality instances are implementation structure. |
| A1, weak order (218) | `T/Statements.lean:270` | Completeness and transitivity; no extra order condition. |
| A2, closed graph jointly in K,q,p (221–227) | `T/Statements.lean:283` | Sequential closedness on fixed finite alphabets, mathematically equivalent in the finite-dimensional domain. A separate theorem comparing a closed-graph predicate with this encoding is not exported. |
| A3, existential two-action, singleton-record benchmark (232–239) | `T/Statements.lean:465,484` | Canonical binary action and singleton record types. See canonical-label qualification below. |
| A4, one-payoff four-action benchmark (242–253) | `T/Statements.lean:499,528` | Canonical four actions and two records; one payoff witness in both texts, not every payoff. See qualification below. |
| Block comparisons and A5 (259–310) | `T/Statements.lean:108,131,153,167,182,298` | Tagged disjoint sums, arbitrary finite block families, ordered distinct blocks. Strictness reverses the comparison in the same block, as in the paper. |
| Payoff-preserving record processor and A6 (316–352) | `T/Statements.lean:198,203,222,328` | Lean specifies the distribution of the new record and copies the payoff. This parametrizes the paper's entire class of payoff-preserving kernels, including dependence on the old payoff and record. |
| Bayesian pushforward and A7 (328–360) | `T/Statements.lean:235,342` | Exact undivided joint-law equation; every completion at null processed actions is quantified. No full-support premise. |
| Compounding and A8 (365–404) | `T/Statements.lean:254,423` | Same q, P and common continuation; same action drawn once; retained first-stage record. Only the changed branch must be reached. Common continuation record alphabet matches. |
| MI and its zero-mass convention (414–422) | `Info/MutualInfo.lean:26,34,41,74` | Entropy and likelihood-ratio definitions are proved equal. Null contributions are zero. Log-base qualification below. |
| Theorem 1 and same-witness block clause (425–448) | `M/Proof.lean:37,63,74`; `T/Statements.lean:659`; `T/Benchmark.lean:400` | Both directions and finite-block representation, with the same parameters. No extra helper premise remains in the exported statement. |
| Arbitrary common-scale numerical index W (515–528) | `S3/UniquenessBasic.lean:29,44` | Arbitrary real-valued function, with no continuity or pre-imposed functional form. Includes finite-block comparisons. |
| Numerical branch additivity (530–547) | `S3/UniquenessBasic.lean:63` | Common continuation record alphabet; sum over all branches, with null terms weighted zero instead of omitted. |

**Canonical labels are not a literally identical isolated predicate.** On an
arbitrary label-sensitive preference family, existence of some labeled A3/A4
benchmark is not the same formula as strictness at the canonical Lean benchmark.
For the full characterization, the other structural axioms give the required
relabeling and padding neutrality, so the encoding is mathematically equivalent.
There is no dedicated arbitrary-benchmark-alphabet equivalence theorem. This
qualification is preferable to saying the isolated predicates are syntactically
identical.

**Logarithm base:** Lean uses natural logarithms. The paper permits any fixed
base b > 1 and explicitly chooses natural units for logit. The representation,
sign and uniqueness statements translate by `lambda_natural = lambda_b/log b`.
No general-base transport theorem is exported. Numerical coefficient/derivative
formulas in Lean are literally in natural units.

**Null events and KL:** arbitrary posteriors at null outputs are ignored by
positive-mass guards or zero weights. `finiteKL` is a real-valued formula whose
KL interpretation requires support inclusion. The formal KKT and binary
pure-choice iff make that condition explicit and prove its necessity. This is
equivalent to the paper's extended-real choice conditions; it is not a proof of
every displayed extended-real analytic formula.

## Inventory of all numbered results

| No. | Paper result and starting line | Formal counterpart / status |
|---:|---|---|
| 1 | Representation theorem, 425 | **Matched**, with the encoding qualifications above. `M/Proof.lean:37,63,74`. |
| 2 | Uniqueness, 550 | **Matched.** `S3/Uniqueness.lean:24,41`; parameter/anchor uniqueness in `UniquenessParameters.lean:16,43,65,77`. |
| 3 | Sign trichotomy, 590 | **Matched.** `S3/Signs.lean:75`; converses `Signs/Converse.lean:83,103`. Background is exactly A1–A3, A5, A8. Negative block-swap equivalence is proved in `Signs/Reverse.lean:100`, not assumed. |
| 4 | Independence, 614 | **Matched.** `S3/Independence.lean:34,79`. `[Nontrivial O]` corresponds to the model's cardinality condition. Some illustrative witnesses differ, as noted below. |
| 5 | Trace test, 642 | **Matched.** `S4/TraceTest.lean:62,72,78,99,139,160`: actual channels, all marginals, sign orientations and channel-blind impossibility. |
| 6 | Optimality condition, 717 | **Matched.** `S4/OptimizationKKT.lean:141`; preference-level `OptimizationPublic.lean:34`; same witnesses from axioms at `:58`. |
| 7 | Multinomial logit, 735 | **Matched**, natural logs and positive lambda. `S4/OptimizationLogit.lean:12,100`, `OptimizationPublic.lean:48`. |
| 8 | Eliciting trace weight, 776 | **Matched.** Positive entropy/dilution, normalized anchors, feasibility and uniqueness are explicit in `S4/MeasurementElicitation.lean:46,71,82`; genuine preference comparisons at `MeasurementControls.lean:101,110,121`. |
| 9 | Blocks, supports, dummies, 1040 | **Narrower minimal-axiom interfaces** for support/dummy components; see findings. Order and replacement ingredients: `T/PairOrder.lean:228`, `T/FiniteBranchExtension.lean:982`. |
| 10 | Finite-branch extension, 1074 | Part (a) **matched** at `T/FiniteBranchExtension.lean:1068`, including strictness and null branches. Part (b)'s arbitrary one-branch weak/strict biconditional is an **assembly gap**: forward implications at `:671,802` and reverse-direction order ingredients are checked, but no complete endpoint was found. |
| 11 | Terminal laws and affine fibres, 1165 | Part (a) **matched**, even under A6 alone (`T/MarkedTerminal.lean:504,566`). Part (b) **narrower hypotheses**, as above. |
| 12 | Fixed-channel/environment relevance, 1230 | **Matched**, with canonical-label qualification. `T/RelevanceBridge.lean:235,1073`; finite-branch bridge `T/FiniteBranchExtension.lean:970`. |
| 13 | Material utility/common affine scale, 1271 | **Narrower hypotheses:** full bridge rather than the paper's no-A4 version. Material utility and normalization conclusions themselves are checked. |
| 14 | Equal changes in marked laws, 1351 | **Matched.** `M/MarkedDirections.lean:31,67`. Equality against every real test function is equivalent to finite signed-law equality. |
| 15 | Affine insertion, 1386 | **Different proof packaging.** Positive insertion at a constant-payoff background is checked in `T/SupportBranchInsertion.lean:328,391,423`. Arbitrary backgrounds are handled after calibration in `M/BranchComparison.lean:80`, not by an exported pre-calibration coefficient theorem. The final calibrated identity is stronger for the uses in the theorem. |
| 16 | Material unit at each prior, 1441 | **Matched ingredients** in `M/Units.lean:163`, `UnitAnchors.lean:34,93`, `MarkedUnitRatio.lean:67`, `PartitionUnits.lean:60,71`. General pre-calibration relabel invariance is not a separate endpoint; checked relabeling and final unit-one results supply it. |
| 17 | Exact reached-branch weight, 1504 | **Matched at full-support outer priors**, including arbitrary backgrounds and singleton posterior supports (`M/Calibration.lean:30,91,120`, `BranchComparison.lean:80`, `CompoundValue.lean:23,72`). The paper's explicit all-prior/padded-alphabet wrapper is not exported. |
| 18 | Deterministic payoff separation, 1572 | **Matched at full support**, including null records and singleton action sets (`M/PayoffSeparation.lean:109,139,154`). Its separately stated all-prior version is an **assembly gap**, using checked supported values/final representation. |
| 19 | Entropy reduction/grouping, 1641 | **Matched**, including arbitrary priors and dependent grouping. `M/TraceEntropy.lean:172`, `TraceEntropySupport.lean:63`, `EntropyGrouping.lean:41`. |
| 20 | Shannon identification, 1684 | **Matched conclusion.** `M/ShannonIdentification.lean:18,32`, `ShannonAssembly.lean:19`, `TraceEntropySupport.lean:63`. The paper's particular endpoint-continuity argument is not the checked route. |
| 21 | Deterministic payoff continuation, 1777 | **Matched full-support formula** at `M/ValueAssembly.lean:42`; all-prior intermediate corollary is not separately packaged, although final all-prior representation is checked at `M/Representation.lean:18,48`. |
| 22 | No payoff–trace complementarity, 1929 | **Immediate assembly, no complete endpoint.** Use unmarked posterior-law equality (`Basic/Convergence.lean:230`), `Info/Identities.lean:1091`, equal expected utility and `S4/MeasurementControls.lean:87`. Equality of the stronger joint payoff/posterior law is not required. |
| 23 | Qualitative trace preferences, 2193 | **Matched exact weaker axioms.** `S4/TraceTestQualitative.lean:117,133,153`: A1/A5–A7 for weak preference and independence; additionally A4 for strict existence. |
| 24 | Optimal mixing, 2222 | Choice classification, unique interior root and weak/strict comparative statics **matched** (`S4/Binary/Choice.lean:91`; `Classification.lean:11,28,54`; `ComparativeStatics.lean:51,71,85,117,133`). The unsupported infinite limits in part (i) are **unformalized**. |
| 25 | Support and pure choice, 2316 | **Matched.** `S4/OptimizationSupport.lean:57`, `OptimizationKKT.lean:160,177`, `OptimizationFace.lean:34`, `OptimizationCorollaries.lean:80`. |
| 26 | Optimal marginal and multiplicity, 2365 | **Matched.** `S4/OptimizationGeometry.lean:41`, `OptimizationFace.lean:9,115`, `OptimizationCollapse.lean:69,84`. The uniqueness hypothesis is affine independence of active rows, not all rows. |
| 27 | Overlapping traces/IIA example, 2400 | **Matched exact channels and numbers.** `S4/ChoiceExamples.lean:6–122`: two-menu fair optimum, three-menu `(1/3,4/9,2/9)`, odds one versus 3/4. |
| 28 | Cost of record garbling, 2419 | **Matched proposition statement.** `S4/RecordInformation.lean:70,77,87,102,115`. Its proof's additional posterior-law equality characterization is **unformalized**. |
| 29 | Recorded coin, 2447 | **Matched.** `S4/RecordedCoin.lean:25,35,48,57,65`. The conditional-information encoding retains the original observation given the hidden-coin observation; the latter already contains O,R, so only the coin can add information. |
| 30 | Uniform dominance/more-capable vs garbling, 2468 | **Unformalized full proposition**, especially the nonconverse counterexample; see findings. |
| 31 | Single information price, 2519 | **Matched.** `S4/MeasurementRange.lean:125,137,145,150,173`; preference-level ratio `MeasurementControls.lean:95`. Nonconstant utility and positive lambda match the surrounding representation assumptions. |
| 32 | WTP for trace, 2548 | Value/compensation formulas **matched** at `S4/MeasurementDilution.lean:45,87,101,148`. Feasibility iff at `:137` requires positive dilution; the paper's zero-dilution endpoint is an **immediate assembly gap**. |
| 33 | Implementation and controls, 2621 | **Matched substantive content.** `S4/MeasurementElicitation.lean:90,102,113,127,135,141`, `MeasurementControls.lean:17,41,48,132`, `MeasurementTests.lean:157`. Utility-extreme anchors supply the `[0,1]` utility bounds required by the calibration existence theorem. Successful reports and positive entropy are explicit. |
| 34 | Entropy-reduction audience, 2809 | Correct-prior sufficiency is an immediate entropy-identity specialization; the reward model and **necessity direction are unformalized**. |

## Unnumbered claims and proof details

### Representation and independence

- The proof sketch (461–510) follows the checked material-first route under
  full A1–A8. It should not be read as a separate verification of each
  Appendix A lemma at its minimal stated hypotheses.
- Supported numerical values and their global order are checked in
  `M/SupportedValue.lean:24,32,45,56`. These supply the boundary convention,
  but do not themselves export every all-prior intermediate identity above.
- The paper's doubling recurrence and endpoint limit argument for binary
  entropy (1721–1740) are not separately formalized. The checked generic
  Faddeev theorem (`PureTrace/Support/GenericFaddeev.lean:1505`) uses binary
  interior continuity, support invariance and grouping to reach Shannon form.
  This is a proof-route difference, not a missing assumption in identification.
- The A1 and A2 counterexample **families and independence conclusions** are
  checked, but the particular displayed demonstrations differ. Pareto uses a
  block comparison of high-payoff silence with low-payoff revelation
  (`S3/Independence/Pareto.lean:84,111`), rather than paper 2043–2051's exact
  two-action coordinates. Lexicographic discontinuity uses a four-action
  block and geometric sequence (`Lexicographic.lean:112,162`), rather than
  paper 2053–2066's displayed three-action sequence. Those particular numerical
  illustrations are not separately certified.
- The paper's Gini family, including the exact `3/8 → 1/2` merge, is separately
  checked (`S3/Independence/Gini.lean:14`, `GiniExamples.lean:147,155,175`),
  even though the general independence aggregator uses another A7 witness.
  The satiation family is checked for **every** positive cap
  (`Satiation.lean:127,176`). The conditional-noise family is only the
  epsilon-one case, as flagged above.
- The introductory assertion that every finite joint law factors as a prior
  and channel (201–204) is not a separately identified endpoint in the paper
  interface. It is explanatory domain commentary, not a premise of the proof.

### Choice, records, and measurement

- Existence, continuity, concavity and strict concavity in different output
  laws are checked in `S4/OptimizationBasic.lean:96,105,119` and
  `OptimizationGeometry.lean:29`. The finite derivative has the stronger
  coverage assumption listed above; the unsupported case is handled by
  `OptimizationSupport.lean:21`'s explicit improvement rather than infinity
  arithmetic. The reference identity (2298) is checked at
  `OptimizationKL.lean:102` on the paper's support domain.
- Negative and zero information weights (footnote 730; 2346–2351) match
  `S4/OptimizationNonpositive.lean:42,78,84,89` exactly. Only the negative
  case requires zero information at an optimum.
- Arbitrary duplicate-row splitting is covered by the surjective collapse
  theorems (`S4/OptimizationCollapse.lean:36,56,69,84`). Uniqueness of combined
  class masses still needs uniqueness in the collapsed problem; the generic
  theorem does not claim that automatically. Three disjoint equal-reward
  alternatives receive 1/3 each (`OptimizationCorollaries.lean:56`).
- Disjoint-support IIA is checked for different menus
  (`S4/OptimizationCorollaries.lean:27`). The statement that overlap need not
  cause failure has no separately exported IIA-preserving overlapping example.
- The exact conditional-information formula in record garbling uses the
  original full output Z conditional on the processed output Z'. For a
  payoff-preserving processor Z' contains O already, giving the paper's
  `I(A;R | O,R')` interpretation. This is an equivalent conditional-observation
  encoding, not an extra payoff-independence assumption.
- Shannon's fair/quarter-prior ratio, its rounding to 1.23, and the Gini ratio
  4/3 are checked for actual successful elicitation reports
  (`S4/MeasurementTests.lean:69,81,121`). Positive entropy and dilution rule
  out a zero denominator. The capped estimate is checked conditional on a
  feasible report (`:157`); it is flat until the cap binds, not strictly falling
  everywhere. There is no mismatch in the paper's stated formula.

### Moral hazard

| Paper claim | Checked scope |
|---|---|
| Binary technology and objective, 811–828, 2651–2660 | `S4/MoralHazard/Basic.lean:25,59,71`, `Optimization.lean:22,34`: exactly `0 < p0 < p1 < 1`; binary simplex and interval optimization are linked. |
| Curvature and endpoint slopes, 2663–2666 | `Basic.lean:83,92,105,127,133` and `Incentives.lean:9,15`; natural-log units. |
| High-effort incentive iff and flat-wage classification, 829–838, 2668–2678 | `Optimization.lean:106,115,141,153`, `Incentives.lean:37,43`. Positive cost is required for the stated flat-wage interior classification; positive lambda matches the context. Bonus/cost restrictions are otherwise no stronger than the paper. No net-reward ordering is assumed. |
| Independent finite cost implementation, 815–822, 2680–2689 | Exact candidate-dependent numerical value and unchanged information at `Cost.lean:38,49,59,65`. The formal output is `(X,cost flag)`; including W would add a deterministic function of X. A cost-specific theorem comparing two augmented plans in their common block is not exported, though the checked value formula and common-scale representation supply it. |
| Team averaging and bounds, 840–848, 2692–2699 | `Teams.lean:97,100,140` handles an arbitrary finite joint teammate distribution fixed across the agent's actions. Teammates need not be independent of each other. Instantiating the Bernoulli incentive theorem for these averaged parameters is an immediate assembly; no dedicated team-threshold wrapper exists. |
| Vanishing trace share and diverging fixed-cost share, 850–854, 2711–2717 | Exact limits at `Teams.lean:85,156`, under positive gaps tending to zero and uniform success bounds; cost is fixed and positive for divergence. Exact leading terms/remainders are unformalized, as above. |
| L/n example, 2718–2719 | `Teams.lean:119` proves it for globally monotone and Lipschitz G. Main-text weaker wording and feasible-domain qualification are flagged above. Threshold-technology and essential-task caveats are not separate formal counterexample families. |
| Extra noncontractible signal, 856–858, 2725–2730 | `S4/SignalValue.lean:29,38,53`, `MoralHazard/SignalCompensation.lean:50,59,67`: actual joint channel, fixed production marginal, exact conditional-information gain. |
| Reoptimized compensation and bounds, 2733–2741 | `Compensation.lean:15,23,31,59` and `SignalCompensation.lean:76`. Maxima are encoded by maximizing plans. The generic bounds hold for **any** original optimizer, despite the instantiated existence theorem selecting one. |
| Base-pay adjustment and participation, 2743–2746 | `Compensation.lean:41,48,52`: exact/weak participation and invariance of effort to additive base pay. The money feasibility restriction is a stated modeling qualification, not silently supplied by Lean. |
| Signals may change effort; lambda-zero case, 2747–2750 | Actual witness at `SignalChangesEffort.lean:52`; zero compensation at `SignalCompensation.lean:94`. No principal-profit model or unconditional profit result is formalized, consistently with the paper's caveat. |

### Interpretation and literature

- Posterior entropy reduction, entropy-minus-noise and weighted divergence
  identities (2758–2764) have checked counterparts in
  `Info/Identities.lean:1091`, `Info/MutualInfo.lean:26,74` and
  `S4/OptimizationKL.lean:128`. Zero information iff supported rows coincide
  iff independence is checked at `S4/InformationZero.lean:12,57`.
- Information symmetry, including boundary priors, is proved by
  `Info/DataProcessing.lean:296`, `mutualInfo_bayes_reverse`. This verifies
  numerical symmetry, not a separate causal model of control.
- The disjoint-support entropy endpoint assumes all rows disjoint
  (`S4/OptimizationLogit.lean:12`). The weaker supported-rows-only statement
  at 2770–2771 is a straightforward support-restriction assembly using
  `Basic/SupportRestriction.lean:144` and entropy support invariance
  (`PureTrace/Support/GenericFaddeev.lean:1473`).
- Equal expected rewards imply capacity maximization
  (`S4/OptimizationCorollaries.lean:71`); existence is checked. The displayed
  maximum-value formula at 2779–2781 is an immediate algebraic assembly, not a
  separate capacity-valued endpoint.
- Preservation of MI under information-preserving reclassification
  (1001, 2802–2805) follows by applying checked data processing in both
  directions (`Info/DataProcessing.lean:359`). There is no standalone
  reclassification model. Identical noisy rows can have unbounded entropy
  with zero MI by combining the constant-channel and uniform-entropy results;
  no dedicated unbounded-noise example is exported.
- Opposed selective-legibility choices violating every sign orientation are
  an immediate consequence of the checked processing predicates, not a
  separately defined preference model. A passive audience leaving q,K,u fixed
  changes no argument of the represented formula; there is no additional
  formal audience experiment behind that observation.
- Historical and empirical descriptions of cited work, claims that a named
  published model falls into the channel-blind class, comparisons/nonnesting
  with rational inattention or external information-cost classes, and a
  monetary implementation of audience rewards are **not Lean-certified**.
  The own-model statements used in those comparisons are identified above;
  verifying the literature claims would be a separate source-based review.

## Appropriate verification claim

The defensible statement is that the repository checks the representation
theorem, its material-first route, the main uniqueness/sign/independence and
choice results, and the supporting endpoints specified in the certificates.
It does **not** check every preliminary lemma at its weakest printed hypotheses,
every analytic display, or every further interpretation proposition in v11.

To claim full literal v11 coverage, the substantive missing results above must
be formalized, the narrower hypotheses/boundary statements extended, and the
assembly gaps either given explicit endpoints or clearly identified as
combinations of checked statements. The ambiguous fixed-payoff sentence should
be clarified independently of formalization. None of those changes was made
silently as part of this audit.
