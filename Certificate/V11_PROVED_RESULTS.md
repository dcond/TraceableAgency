# v11 proved-result correspondence: completed additions

This follows the statement audit at commit `896a580`. The agreed scope is the
paper's stated results with proofs, rather than each intermediate calculation,
illustration, or explanatory paragraph. The original representation proof,
material-first proof, and application proofs are preserved. The additions are
exported by `TraceableAgency.V11`, also imported by the public root module.

The paper itself was unchanged at proof-completion commit `5f7e8e8`.
In particular, the weaker hypotheses of Appendix A Lemmas 9, 11 and 13 did
**not** need strengthening. The audience proof in v11 has since been rewritten
to follow the shorter argument formalized here; its proposition statement and
hypotheses are unchanged.

## Actual axiom use, rather than bundled parameters

The old interfaces passed a full `TraceTemperedBridgeAxioms` value even when
the proof did not use all its fields. The new interfaces expose the premises
that the proofs actually need:

| Result | Checked assumptions | New endpoint |
|---|---|---|
| Lemma 9, support and dummy neutrality | A7 for the two processing comparisons; A1 and A5 for replacement; A1, A5–A7 for same-block indifference | `Theorem1.supportRestriction_pairIndiff_v11`, `independentDummy_pairIndiff_v11` |
| Lemma 10(b), one-branch weak and strict equivalence | A1, A5–A8 | `Theorem1.pairWeak_oneBranchCompound_iff_v11`, `pairStrict_oneBranchCompound_iff_v11` |
| Lemma 11(b), affine marked-law representation | Exactly A1, A2, A5–A8; neither material nor trace relevance | `Theorem1.V11.terminal_affine_exists_v11` |
| Lemma 13, common material scale | Exactly A1–A3, A5–A8; no trace relevance | `Theorem1.V11.common_material_scale_exists_v11` |

The last two are explicit paper-facing theorems. Their premise bundles contain
no omitted relevance field. An independent recursive dependency inspection
also checked that the affine endpoint does not reach either relevance axiom,
and that the material/common-scale endpoints do not reach trace relevance,
the full bridge bundle, or a final representation theorem. Importing an old
file does not mean assuming its stronger theorem: the new proof bodies use
the appropriate general definitions and narrowed lemmas.

The narrowed proofs live in `Theorem1/V11Affine.lean` and
`Theorem1/V11Material.lean`; their source comments identify the original
arguments. Keeping those arguments separately preserves every old proof and
public interface.

## Remaining stated results closed

All names below are in the `TraceableAgency` namespace. `MC` abbreviates
`Theorem1.MaterialCalibration`.

| Paper result | Added checked statement |
|---|---|
| Lemma 15, positive affine insertion coefficient independent of background | `MC.affine_insertion_exists_v11` |
| Lemma 16, positive material unit, relabel invariance and branch ratio | `MC.material_unit_exists_v11`, with the unit proved equal to one |
| Lemma 17, exact branch weight at arbitrary outer priors | `MC.supportedMarkedValue_oneBranch_difference_v11`; different continuation record types and null targets are allowed |
| Lemma 18, deterministic payoff separation at arbitrary priors | `MC.supportedMarkedValue_payoffBranch_separation_v11` |
| Corollary 21, deterministic continuation value with one positive coefficient | `MC.exists_pos_payoffBranch_formula_v11` |
| Corollary 22, no payoff–trace complementarity | `Section3.no_payoff_trace_complementarity_of_axioms`; equality is of the unmarked law of posteriors on actions |
| Proposition 24(i), unsupported binary endpoint limits | `Section4.binaryGain_tendsto_zero_of_not_support`, `binaryGain_tendsto_one_of_not_support`; limits are respectively `atTop` and `atBot` |
| Proposition 30(i), uniform value dominance iff more-capable dominance | `Section4.MoreCapable.uniform_value_dominance_iff`, with identical payoff kernels and positive trace weight |
| Proposition 30(ii), garbling implication and failure of its converse | `Section4.MoreCapable.garbling_implies_information_dominance`, `exists_moreCapable_not_garbling_at_payoff` |
| Proposition 32(iii), feasibility including zero dilution | `Section4.dilution_compensation_feasible_iff_all_rates` |
| Proposition 34, entropy-reduction audience iff correct observer prior | `Section4.Interpretation.audience_entropy_reduction_iff` |

The cardinal Appendix A wrappers concern the actual supported, material-
normalized numerical value, not just an ordinally equivalent index. The
all-prior wrappers are derived after the completed representation; they are
not new premises used to prove it. Their derivation does not change the
existing material-first proof route.

The Proposition 30 counterexample uses exactly the paper's half-erasure and
one-fifth-crossover channels. Its final endpoint works at any finite payoff
alphabet `O : Type u`, using any supplied sure payoff `o : O`; it therefore
applies to the paper's nontrivial payoff alphabet. The information inequality
holds at every prior, including pure priors, and the proof rules out every
payoff-preserving record processor.

Proposition 34's expectation uses the actual prior `q`, while the observer
updates its own prior `r`. Its only substantive premises are the printed
support inclusion and nonzero trace weight. It includes pure actual priors,
boundary priors, observer mass outside actual support, and negative nonzero
weights. The necessity proof uses partial merging of two actions and strict
monotonicity of binary entropy, replacing the endpoint expansion in the
audit-baseline paper. The current v11 proof follows this same argument.

## Scope and verification

The historical audit also flagged proof details and unnumbered explanatory
claims. Under the user's clarified scope, the following were not made separate
formalization targets: exact Taylor remainders, the general directional
derivative display, the entire epsilon-parameterized independence illustration,
the extra posterior-law equality statement inside the garbling proof,
unrestricted forecasting/log-loss interpretation, and standalone notation or
logarithm-base transport lemmas. None is needed as an unproved premise of the
checked results above. Existing equivalent finite-domain encodings remain as
documented in the original audit.

Validation passed on 2026-11-03:

- `lake build TraceableAgency.V11` succeeded.
- `./scripts/check_trust_boundary.sh` succeeded, including the clean project
  source rebuild, pinned dependency checks, prohibited-mechanism scan, raw
  declaration dependency audit, and mandatory fresh kernel replay.
- The inventory covers 272 project source modules plus the two audit modules.
  All 274 Lean source files remained byte-identical to the inputs hashed at
  the start of the verification.
- The raw audit found 9,813 originating declarations, 6,011 theorem roots,
  1,670 internal/private theorem roots, and 9,661 mathematical roots. Their
  combined raw dependency closure contains 51,123 declarations.
- The only foundational axioms reached are `propext`, `Classical.choice`, and
  `Quot.sound`. No new project axiom, proof hole, unsafe mathematical
  dependency, or partial mathematical dependency was found.
- Every pre-existing mathematical proof file is unchanged from `896a580`.
  The only changes to pre-existing Lean files are the public root import and
  the exhaustive audit-import inventory. At that verification, both v10 and
  v11 paper files were unchanged, as was the canonical OneDrive v11. The later
  audience-proof rewrite changes no Lean file or proved statement.

These checks cover the new private helpers and public statements together
with every original project module. The historical correspondence audit is
retained, explicitly marked as the pre-completion baseline.
