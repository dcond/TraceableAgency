# External Assumptions Classification

> **AUTHORITATIVE FINAL STATUS (2026-07-03, commit `846a49b`).** The referee-grade
> certificate for the final theorem is `REFEREE_LEAN_CERTIFICATION_DOSSIER.md`; consult it
> first. The final theorem
> `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` takes exactly four inputs:
> `TraceAxioms F`, `FinalHMInterface`, `ClassicalFaddeevTheoremAssumptions`, and
> `FinalConstructedRepresentativeConventions hhm hax`. It **does not** take
> `CoherentRelabelingFaceScalesStructure F` (`hfaces`),
> `FiniteProductQuasiAdditivityForFaceScales hfaces` (`hprod`),
> `FiniteScaleCoherenceAssumptions`, `FiniteBranchAggregationAssumptions`,
> `FiniteCrossPriorBlockAssumptions`, `EntropyReductionRepresentation`, `FaddeevEntropyForm`,
> `SufficiencyMIPackage`, or `MIRep` as assumptions — all are constructed internally or
> eliminated. Any statement below that a monolith or `hfaces`/`hprod` "remains live" refers to
> **legacy compatibility APIs elsewhere in the source tree**, not to inputs of the final
> theorem. The `iff` necessity direction and the "moreover" block clause of TeX Theorem 1 are
> certified by the **separate** theorems `BenchmarkStatement_of_DPI` and
> `blockSameScaleRep_of_MIRep`, not by the final theorem.

This note records the status of the named external assumptions after Stage 13.
The point is to make the remaining gaps explicit and auditable.

## Interface Repairs Made

- `FullSupportMIRepExtendsToBoundary F` now requires `TraceAxioms F` before it
  extends a full-support MI representation to all priors.
- `A8_IndependentBackgroundSeparability` now allows the alternative background
  channels to have different outcome alphabets.
- `FiniteHersteinMilnorAssumptions` lives in `External/HersteinMilnor.lean`,
  not in `External/Blackwell.lean`.
- Stage 9A removed `FiniteEntropyReductionAssumptions`. The full-revelation
  posterior-law refinement and the entropy-reduction algebra are now internal.
- Stage 9B proved the normalized chain rule from `BranchAggregationStructure`
  and `ScaleCoherenceStructure`, using zero-branch erasure and positive-branch
  coefficient factorization. `FiniteNormalizedChainRuleAssumptions` has been
  removed from the public sufficiency bundle.
- Stage 9C inspected entropy regularity. `Hcandidate_singleton` and
  `Hcandidate_nonneg` do not follow from the current `ScaleCoherenceStructure`
  interface alone: zero normalization is full-support guarded, and
  nonnegativity needs order/A1 input. The separate
  `FiniteEntropyRegularityAssumptions` field was removed; these regularity
  obligations were moved to the Faddeev side.
- Stage 9D split the monolithic `FiniteFaddeevEntropyAssumptions` into named
  components. The A3 duplicate-block equivalence is now proved internally from
  `TraceAxioms.a3`.
- Stage 9E decomposed `PositiveEntropyScaleAssumptions`. Lean now proves
  `alpha > 0` from a fixed positive universe-lifted Bool-uniform `Hfun` witness
  and Shannon entropy positivity. At that stage the remaining external field was
  the narrower `PositiveEntropyWitnessAssumptions`.
- Stage 9F removed `PositiveEntropyWitnessAssumptions`. Lean now proves the
  fixed Bool-uniform positive `Hfun` witness from A1-style strictness, the
  cross-prior block representation, entropy reduction, singleton-zero
  regularity, and no-information posterior-law identities, assuming only the
  narrower `FiniteStrictBlockValueBridgeAssumptions`. That bridge isolates the
  remaining reverse-orientation/block-swap step and the universe-lifted
  no-information strictness needed to use the value interfaces.
- Stage 9G inspected `FiniteStrictBlockValueBridgeAssumptions`. The attempted
  A1/A4/A3 proof of lifted no-information strictness is blocked by the current
  universe-specific A4/A3 interfaces: A1 uses `Unit`, while the value machinery
  uses `PUnit.{u+1}`. A3 also lacks an action/outcome relabeling theorem for
  two-block label swaps. The combined bridge was split into
  `FiniteLiftedUninformativeStrictAssumptions` and `FiniteBlockSwapAssumptions`.
- Stage 9H replaced `FiniteLiftedUninformativeStrictAssumptions` and
  `FiniteBlockSwapAssumptions` with the single
  `FiniteRelabelingInvarianceAssumptions` field. Lean now defines explicit
  finite distribution/channel relabeling by equivalences and proves both
  `lifted_uninformative_strict_of_relabeling` and
  `block_swap_rel_of_relabeling` from that relabeling bridge.
- Stage 9I proved `FiniteRelabelingInvarianceAssumptions` internally. Outcome
  relabeling follows from deterministic reversible postprocessings and A4.
  Action relabeling follows from deterministic reversible action kernels,
  action-pushforward identities, Bayesian-completion identities, and A5. A3
  finite-block coherence plus A1 transitivity assemble the pairwise comparison.
  The public sufficiency bundle no longer has a relabeling field.
- Stage 9J split `FiniteFaddeevRecursionAssumptions` into three sharper
  coarse-reveal interfaces. Lean now defines `coarseRevealChannel` and proves
  the coarse marginal, positive-posterior, and posterior-law integral
  identities. The remaining recursion-side external content is explicitly:
  `FiniteHfunBlockEmbeddingInvarianceAssumptions`,
  `FiniteCoarseRevealEntropyReductionAssumptions`, and
  `FiniteCoarseRevealValueAssumptions`.
- Stage 9K proved the full-support coarse-reveal value identity from A5,
  deterministic projection/refinement kernels, Bayesian-completion identities,
  and the cross-prior value representation. The all-priors
  `FiniteCoarseRevealValueAssumptions` field was replaced by the narrower
  `FiniteCoarseRevealValueBoundaryAssumptions`, which only covers
  non-full-support `sigmaDist p q`.
- Stage 9L split `FiniteCoarseRevealValueBoundaryAssumptions` into value-level
  support transport and a restricted-support coarse-reveal value interface.
  Lean now proves the old boundary coarse-reveal value theorem from
  `FiniteValueSupportRestrictionAssumptions` and
  `FiniteRestrictedCoarseRevealValueAssumptions`.
- Stage 9M proved normalized-value support restriction for full-support ambient
  priors from A5 support comparisons and `cross_prior_block_rep`. The combined
  `FiniteValueSupportRestrictionAssumptions` field was split into
  `FiniteNormalizedValueSupportBoundaryAssumptions`, which is boundary-only,
  and `FiniteHfunSupportRestrictionAssumptions`, which carries the remaining
  `Hfun` support transport obligation.
- Stage 9N proved the identity-channel posterior integral is zero from
  singleton regularity, proved the full-support formula
  `Hfun q = normalizedValue q Channel.idChannel`, and proved the
  support-restricted ambient identity channel has the same posterior law and
  normalized value as the true identity channel on the support subtype. Thus
  full-support `Hfun` support restriction is internal. The live
  `FiniteHfunSupportRestrictionAssumptions` field was replaced by the narrower
  `FiniteHfunBoundaryIdentityAssumptions`; Lean derives the old Hfun support
  package from this boundary identity plus normalized-value support transport.
- Stage 9O consolidated the three remaining boundary/cardinal Faddeev-recursion
  assumptions into the single `FiniteCardinalSupportBoundaryAssumptions`
  interface. This is not a proof of cardinal boundary extension; it prevents
  assumption sprawl and makes the remaining boundary-cardinal obligation one
  faithful auditable bridge. Lean derives the three previous helper interfaces
  from this single assumption.
- Stage 10A decomposed `FiniteCrossPriorBlockAssumptions`: it no longer returns
  `CrossPriorBlockRepresentation` directly from entropy reduction. Its live
  field is the paper-specific unscaled full-support blockbridge
  `unscaled_cross_prior_block_rep`; Lean proves
  `crossPriorBlockRepresentation_of_unscaled` by applying universal scale.
- Stage 10B decomposed that unscaled full-support blockbridge into
  `FiniteProductLiftValueAssumptions` and
  `FiniteProductBlockTransferAssumptions`. Lean proves
  `productLiftedComparison_represents` from the existing posterior value
  representation and `prodDist_fullSupport`, then proves
  `unscaled_cross_prior_block_rep_of_product_parts` from the two new
  product-level components. At that stage,
  `FiniteCrossPriorBlockAssumptions` contained those two components, and
  `FiniteCrossPriorBlockAssumptions.unscaled_cross_prior_block_rep` is a
  compatibility theorem, not an assumed field.
- Stage 10C proved the product-to-original block transfer from A3/A4/A5.
  Lean now defines the projection and embedding kernels, proves their
  action-pushforward and Bayesian-completion identities, derives the A4/A5 weak
  comparisons, and proves `product_block_transfer_of_A5_A3` using a common
  four-block A3 environment plus transitivity. The live
  `FiniteCrossPriorBlockAssumptions` record now contains only
  `FiniteProductLiftValueAssumptions`; the product-block transfer is internal.
- Stage 10D decomposed the remaining product-lift value identities into the
  paper's coherent product quasi-additivity formula
  `FiniteCoherentProductQuasiAdditivityAssumptions`. Lean now derives
  `FiniteProductLiftValueAssumptions` from coherent product quasi-additivity
  and zero normalization of the no-information experiment. Thus the live
  `FiniteCrossPriorBlockAssumptions` record contains coherent product
  quasi-additivity, not the two lift identities themselves.
- Stage 10E decomposed coherent product quasi-additivity itself. Lean proves the
  A8-to-value-order coordinate-independence consequences
  `product_left_coordinate_value_order_independent` and
  `product_right_coordinate_value_order_independent`. The remaining live
  `FiniteCrossPriorBlockAssumptions` fields are now
  `FinitePairwiseProductBilinearAssumptions` and
  `FiniteProductGaugeCoherenceAssumptions`. Lean derives the old
  `FiniteCoherentProductQuasiAdditivityAssumptions` compatibility package from
  these two fields.
- Stage 10F decomposed `FinitePairwiseProductBilinearAssumptions` into the
  paper's Step 2 slice-affine pieces:
  `FiniteProductLeftSliceAffineAssumptions`,
  `FiniteProductSliceInterceptAssumptions`, and
  `FiniteProductSliceSlopeAssumptions`. Lean proves
  `pairwiseProductBilinear_of_sliceAffine`, so pairwise bilinear product form is
  no longer the live cross-prior external field. The coherent gauge step still
  depends on the derived pairwise package.
- Stage 10G proved the first-coordinate product-slice same-order theorem
  internally. Lean now defines `productLeftSliceValue`, proves
  `product_left_noInfo_value_order_iff_base` from the Stage 10C
  A3/A4/A5 projection/embedding transfer, and proves
  `product_left_slice_same_order` by combining that with A8 value-order
  coordinate independence. The old `FiniteProductLeftSliceAffineAssumptions`
  package is now derived from the narrower
  `FiniteAffineSliceUniquenessAssumptions`, which isolates the remaining
  affine-HM uniqueness step turning same-order affine representatives into a
  positive affine transform.
- Stage 10H decomposed `FiniteAffineSliceUniquenessAssumptions`. Lean now
  derives it from `FinitePosteriorValueAffineAssumptions`,
  `FiniteProductLeftSlicePublicMixAffineAssumptions`,
  `FiniteValueNonconstancyAssumptions`,
  `singletonSliceAffine_of_singletonCollapse` (now proved internally), and
  `ClassicalAffineUtilityUniquenessAssumptions` via
  `affineSliceUniqueness_of_parts`. This isolates the missing HM-affine
  content into value public-mix affinity, product-slice public-mix affinity,
  base-value nonconstancy, and the classical positive affine transform
  uniqueness theorem. The singleton compatibility is now proved internally
  (Stage 10N) from A8 + posterior-law collapse on degenerate domains.
- Stage 10I decomposed product-slice public-mix affinity. Lean defines the
  canonical outcome equivalence
  `prodSumDistribEquiv : ((O ⊕ Z) × Y) ≃ ((O × Y) ⊕ (Z × Y))`, proves the
  channel-level postprocessing identity
  `prodChannel_publicMix_left_postprocess`, and derives
  `FiniteProductLeftSlicePublicMixAffineAssumptions` from
  `FinitePosteriorValueAffineAssumptions` plus the narrow structural
  `FiniteProductPublicMixPosteriorLawAssumptions`. The live cross-prior bundle
  now contains that posterior-law compatibility, not the broad product-slice
  affinity field.
- Stage 10J proved the product/public-mix posterior-law compatibility
  structurally. Lean defines the local deterministic equivalence kernel
  `posteriorLawEquivKernel`, proves posterior-law integral invariance under
  deterministic bijective outcome postprocessing via finite-sum reindexing,
  proves `samePosteriorLaw_prod_publicMix_left_of_postprocess` from
  `prodChannel_publicMix_left_postprocess`, and derives
  `FiniteProductPublicMixPosteriorLawAssumptions` internally as
  `productPublicMixPosteriorLaw_of_structural`. The live cross-prior bundle no
  longer contains a product/public-mix posterior-law field.
- Stage 10K decomposed channel-level value public-mix affinity into a structural
  posterior-law mixture theorem plus a law-level Herstein-Milnor value-affinity
  interface. Lean proves the public-mix outcome marginals and branch posterior
  identities, proves `posteriorLawIntegral_publicMixChannel`, and derives
  `FinitePosteriorValueAffineAssumptions` from the new
  `FinitePosteriorLawValueAffineAssumptions`. The live cross-prior bundle now
  contains the law-level posterior value affinity field, not the direct
  channel-level `FinitePosteriorValueAffineAssumptions` field.
- Stage 10L decomposed base-value nonconstancy. Lean proves the general
  `value_ne_of_strict_experiment_pref` lemma: a strict experiment-pair
  preference represented by `PosteriorValueRepresentation` forces distinct
  values. At Stage 10L the live cross-prior bundle contained the narrower
  ordinal `FiniteA1ExperimentPairStrictnessAssumptions`, and Lean derived
  `FiniteValueNonconstancyAssumptions` from it.
- Stage 10M proved the A1 experiment-pair strictness bridge. Lean factored the
  reusable finite relabeling and block-swap plumbing into
  `External.Relabeling`, proves Unit/PUnit no-information strictness from A1
  and deterministic relabeling, converts the swapped reverse comparison into
  the `ExperimentPairPref` orientation, and packages this as
  `a1ExperimentPairStrictness_of_axioms`. The live cross-prior bundle no longer
  contains `FiniteA1ExperimentPairStrictnessAssumptions`; value nonconstancy is
  derived internally from A1 plus the value representation.
- Stage 10N proved singleton first-slice affine handling internally via
  `singletonSliceAffine_of_singletonCollapse`. The live cross-prior bundle no
  longer contains `FiniteSingletonSliceAffineAssumptions`.
- Stage 10O proved the intercept preconditions `leftSliceIntercept_eq_noInfo_productLeftSliceValue`,
  `leftSliceIntercept_uninformative_eq_zero`, and
  `leftSliceIntercept_same_order_as_Vr`.
- Stage 10P proved right-coordinate product/public-mix structural compatibility
  and public-mix affinity for the intercept via
  `leftSliceIntercept_publicMix_affine`.
- Stage 10Q replaced the live `FiniteProductSliceInterceptAssumptions` field by
  the narrower `ClassicalSecondCoordinateAffineUniquenessAssumptions`. Lean
  derives the old intercept package as
  `productSliceIntercept_of_secondCoordinateAffineUniqueness` from that
  uniqueness theorem plus the Stage 10O/10P same-order, zero, and public-mix
  affine facts.
- Stage 10R replaced the live `FiniteProductSliceSlopeAssumptions` field by
  the narrower `ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions`.
  Lean proves the first-coordinate slice difference identity
  `leftSliceSlope_mul_value_gap_eq_product_value_gap` and derives the old slope
  compatibility package as
  `productSliceSlope_of_secondCoordinateSlopeAffineUniqueness`.
- Stage 10S decomposed the live gauge/common-kappa package. Lean proves the
  structural product relabeling facts `relabelDist_prodAssoc`,
  `relabelChannel_prodAssoc`, `relabelDist_prodComm`, and
  `relabelChannel_prodComm`. The old `FiniteProductGaugeCoherenceAssumptions`
  package is now derived from
  `FiniteProductGaugeNormalizationAssumptions` and
  `FiniteProductInteractionUniversalityAssumptions` by
  `productGaugeCoherence_of_parts`.
- Stage 10T decomposed `FiniteProductGaugeNormalizationAssumptions`, the
  paper Step 3 linear-coefficient normalization package. Lean now defines
  `linearCoeffRho`, proves `linearCoeffRho_pos`, records the C1-C3 triple
  product coefficient equations in
  `FiniteProductLinearCoeffAssociativityAssumptions`, records the coordinate
  swap/rho reciprocity in `FiniteProductLinearCoeffSwapAssumptions`, and
  isolates the remaining normalized representative choice in
  `FiniteProductPositiveGaugeChoiceAssumptions`. The old Step 3 normalization
  package is reconstructed by `productGaugeNormalization_of_step3_parts`, and
  `FiniteCrossPriorBlockAssumptions.gauge_normalization` is now a theorem.
- Stage 10U decomposed the live C1-C3 coefficient associativity package. Lean
  proves structural posterior-law transport for simultaneous action/outcome
  relabeling (`outcomeMarginal_relabelChannel`,
  `posterior_relabelChannel_of_pos`, `posteriorLawIntegral_relabelChannel`)
  and the product-associativity posterior-law integral identity
  `posteriorLawIntegral_prodAssoc`. The live cross-prior bundle now contains
  `FiniteTripleProductValueAssociativityAssumptions` and
  `FiniteTripleProductCoeffExtractionAssumptions`; the old
  `FiniteProductLinearCoeffAssociativityAssumptions` package is reconstructed
  by `linearCoeffAssociativity_of_triple_parts`.
- Stage 10V proves the nondegenerate coefficient-extraction cases:
  `coeff_assoc_A_from_triple_of_nontrivial_left`,
  `coeff_assoc_mixed_from_triple_of_nontrivial_middle`, and
  `coeff_assoc_B_from_triple_of_nontrivial_right`. It also proves
  `V_prod_uninformative_uninformative_eq_zero`,
  `V_idChannel_ne_zero_of_A1`,
  `product_pair_bilinear_right_uninformative`, and
  `product_pair_bilinear_left_uninformative`. The live cross-prior bundle no
  longer contains full `FiniteTripleProductCoeffExtractionAssumptions`; it
  contains only `FiniteTripleProductCoeffExtractionSingletonAssumptions`, and
  reconstructs the full extraction package with
  `tripleProductCoeffExtraction_of_nondegenerate_and_singleton`.
- Stage 10W reclassified the remaining singleton coefficient equations as
  gauge conventions rather than value-extraction facts. Lean proves
  `product_pair_bilinear_subsingleton_left` and
  `product_pair_bilinear_subsingleton_right`, showing that on singleton
  fibres the corresponding coordinate value is identically zero and the
  omitted coefficients are not read by the value formula. The live cross-prior
  field is now `FiniteSingletonCoefficientGaugeConventionAssumptions`; the old
  singleton extraction compatibility package is reconstructed by
  `tripleProductCoeffExtractionSingleton_of_gaugeConvention`.
- Stage 10X decomposed value-level triple-product associativity. Lean proves
  `tripleProductValueAssociates_of_value_relabeling` from the structural
  product associativity relabeling facts plus the new coherent-representative
  interface `FinitePosteriorValueRelabelingAssumptions`. The old
  `FiniteTripleProductValueAssociativityAssumptions` package is now
  reconstructed by `tripleProductValueAssociativity_of_value_relabeling`, and
  `FiniteCrossPriorBlockAssumptions.gauge_triple_value_assoc` is a theorem.
  The remaining live content is value-representative coherence under
  simultaneous action/outcome relabeling, classified as HM/posterior-value
  representative coherence rather than product algebra.
- Stage 10Y decomposed the coordinate-swap/rho reciprocity package. Lean proves
  `product_value_swap_eq_of_value_relabeling` from coherent posterior value
  relabeling plus structural product-swap relabeling, then extracts the
  nondegenerate coefficient equations
  `leftCoeff_eq_swapped_rightCoeff_of_value_swap_nondegenerate` and
  `rightCoeff_eq_swapped_leftCoeff_of_value_swap_nondegenerate`. From these
  equations and coefficient positivity, Lean proves
  `linearCoeffRho_reciprocity_of_value_swap_nondegenerate`. Singleton swap
  cases are not value-identifiable for the same reason as Stage 10W, so the
  live cross-prior field is now
  `FiniteProductLinearCoeffSwapSingletonConventionAssumptions`; the old
  `FiniteProductLinearCoeffSwapAssumptions` package is reconstructed by
  `productLinearCoeffSwap_of_valueSwap_and_singletonConvention`, and
  `FiniteCrossPriorBlockAssumptions.gauge_coeff_swap` is a theorem.
- Stage 10Z decomposed the positive gauge-choice bridge. Lean now defines the
  paper's coefficient transform laws
  `gaugeTransformedLeftCoeff` and `gaugeTransformedRightCoeff` for a positive
  prior-dependent gauge `F_q^* = φ(q) F_q`. The live cross-prior fields are
  now `FiniteProductReferenceGaugeTransformAssumptions` and
  `FiniteCurrentRepresentativesGaugeNormalizedAssumptions`: the first records
  a positive reference gauge and normalized transformed coefficients, while the
  second records the representative-choice convention that the current
  `ScaleCoherenceStructure` already uses the post-gauge representatives. The
  old `FiniteProductPositiveGaugeChoiceAssumptions` package is reconstructed by
  `positiveGaugeChoice_of_representativeGaugeConvention`, and
  `FiniteCrossPriorBlockAssumptions.gauge_choice` is a theorem. Lean still does
  not implement an operation replacing the `PosteriorValueRepresentation`
  inside `ScaleCoherenceStructure` by a rescaled one.
- Stage 10AA decomposed the interaction/common-kappa package. Lean records the
  Step 4 equations K1-K4 as
  `FiniteProductInteractionAssociativityAssumptions`, records nondegenerate
  interaction swap symmetry as `FiniteProductInteractionSwapAssumptions`, and
  isolates Step 5 singleton compatibility as
  `FiniteSingletonInteractionCoefficientConventionAssumptions`. Lean proves
  the nondegenerate common-coefficient extraction
  `interactionCoeff_eq_reference_of_assoc_nondegenerate` using K1-K3 and the
  lifted-Bool reference prior, then reconstructs the old
  `FiniteProductInteractionUniversalityAssumptions` package with
  `interactionUniversality_of_parts`. Thus the old interaction universality
  field is no longer live.
- Stage 10AB proved the normalized triple-product interaction associativity
  equations K1-K4. Lean proves the normalized product formula helper
  `product_pair_bilinear_normalized`, proves K1, K2, and K3 by specializing
  triple-product value associativity with one no-information coordinate and
  cancelling A1 nonzero witnesses, and proves K4 algebraically from K1-K3.
  The old `FiniteProductInteractionAssociativityAssumptions` package is now
  reconstructed by
  `productInteractionAssociativity_of_tripleValue_and_gaugeNormalization`, so
  interaction associativity is no longer live in `FiniteCrossPriorBlockAssumptions`.
- Stage 10AC proved the nondegenerate interaction-swap equation. Lean proves
  `interactionCoeff_eq_swapped_of_value_swap_nondegenerate` from product-swap
  value equality, the Stage 10AB normalized product formula, and A1 nonzero
  full-revelation witnesses, then reconstructs
  `FiniteProductInteractionSwapAssumptions` with
  `productInteractionSwap_of_valueSwap_and_gaugeNormalization`. Thus
  interaction swap is no longer live in `FiniteCrossPriorBlockAssumptions`.
- Stage 10AD verified the singleton interaction degeneracy. Lean proves
  `product_pair_bilinear_subsingleton_left_interaction_drops_out` and
  `product_pair_bilinear_subsingleton_right_interaction_drops_out`: when either
  product factor is singleton, the interaction term is identically zero because
  the singleton coordinate value is identically zero. Therefore singleton
  interaction coefficients are not value-identifiable by coefficient
  extraction. The remaining `FiniteSingletonInteractionCoefficientConventionAssumptions`
  field is explicitly classified as a Step 5 singleton/gauge convention.
- Stage 10AE reassembled PDF Lemma 12 (`coherentnorm`) explicitly. Lean now
  exposes
  `coherentProductQuasiAdditivity_of_gaugeNormalization_and_interaction` and
  `coherentnorm_of_decomposed_components`, so the coherent product
  quasi-additivity package is derived directly from the reconstructed pairwise
  bilinear product form, Step 3 gauge normalization, and Steps 4-5 interaction
  universality. `FiniteCoherentProductQuasiAdditivityAssumptions`,
  `FiniteProductGaugeCoherenceAssumptions`,
  `FiniteProductGaugeNormalizationAssumptions`, and
  `FiniteProductInteractionUniversalityAssumptions` are compatibility packages,
  not live monolithic assumptions.
- Stage 11 audited the source-order lemmas before `coherentnorm`. The coherent
  product dependencies are now either internal, classical finite-dimensional
  representation/affine-uniqueness interfaces, or explicit
  representative/gauge conventions, except for
  `FiniteBlackwellPosteriorAssumptions`: its Lean statement is not merely the
  textbook finite Blackwell theorem, but the same-posterior-law block
  replacement bridge after applying A4/A3/A1. It remains a narrow
  paper-specific gap rather than a classical theorem or convention.
- Stage 11A decomposed `FiniteBlackwellPosteriorAssumptions`. Lean now
  isolates the paper's finite Blackwell theorem as
  `FiniteSamePosteriorLawBlackwellEquivalenceAssumptions`, which states only
  that same posterior law at a full-support prior gives experiment
  postprocessings/garblings in both directions. Lean proves
  `experimentPairPref_of_postprocess` from A4, proves
  `experimentPairPref_self_of_axioms` from A1 and A3, proves the common
  four-block A1/A3 transfer
  `blackwell_pairwise_block_replacement_from_weak_equiv`, and reconstructs the
  old replacement package as
  `blackwellPosteriorReplacement_of_samePosteriorGarblings`. The public
  sufficiency bundle now carries the narrower finite mutual-garbling theorem;
  `FiniteBlackwellPosteriorAssumptions` is a compatibility package, not the
  live external field.
- Stage 12 audited the named result "Exact relabelling invariance"
  (`cor:permutationinvariance`). The structural action/outcome relabeling and
  posterior-law transport facts are internal, and Lean now exposes the named
  compatibility theorem `exactRelabelingInvariance_of_valueRelabeling`. The
  exact cardinal equality of the selected posterior value representatives is
  precisely the existing `FinitePosteriorValueRelabelingAssumptions` field.
  Thus exact relabelling invariance is classified as a coherent
  representative-choice convention, not as a new product-algebra or gauge
  theorem. The paper presents it as a corollary from coherent normalization and
  action-bijection scaling; Lean currently records the already-normalized
  representative choice directly rather than implementing that scalar
  normalization proof.
- Stage 12A closed the named result "Support restriction" (`lem:supprestrict`)
  for the current Lean formalization. Lean now states the posterior-law
  reduction clause explicitly as `posteriorLawIntegral_restrictToSupport`,
  proving that deleting zero-prior rows and pushing restricted posteriors back
  to the ambient action set preserves posterior-law integrals. The preference
  face-identification clause is exposed as
  `preference_support_restriction_of_axioms`, assembled from the A5
  projection/inclusion weak comparisons and the A1/A3 common-block theorem
  `pairwise_support_restriction_from_weak_equiv`. The boundary MI extension is
  still `FullSupportMIRepExtendsToBoundary_of_supportRestriction`. No
  `FiniteSupportRestrictionAssumptions` field remains live; later
  Faddeev-side boundary/cardinal support interfaces are separate downstream
  obligations, not this named support-restriction lemma.
- Stage 12B audited and explicitly reassembled the named result "Cross-prior
  block representation" (`lem:blockbridge`). Lean now exposes
  `blockbridge_fullSupport_of_decomposed_components` for the unscaled
  full-support bridge and
  `crossPriorBlockRepresentation_of_decomposed_components` for the scaled
  `CrossPriorBlockRepresentation`. No monolithic blockbridge assumption is
  live: the unscaled bridge is assembled from coherent product
  quasi-additivity, product-lift value identities, same-prior value
  representation, and the A3/A4/A5 product-to-block transfer. The formal
  `CrossPriorBlockRepresentation` is full-support guarded; arbitrary-prior
  boundary uses are handled by the separate support-restriction and boundary
  extension layer.
- The unused documentation-level `FaddeevAssumption` no longer has a vacuous
  recursion premise.
- Stage 8A replaced the public sufficiency bundle's coarse boundary field with
  `FiniteSupportRestrictionAssumptions`.
- Stage 8B removed the full-support block/cross-support MI bridge from
  `FiniteSupportRestrictionAssumptions` and proved it as
  `FullSupportBlockMI_of_FaddeevEntropyForm`.
- Stage 8C proved the support inclusion/projection kernels, their
  action-pushforward identities, their Bayesian-completion facts, and the two
  one-sided A5 weak comparisons.
- Stage 8D proved the remaining A1/A3 common-block assembly from those weak
  comparisons to the final pairwise support-deletion equivalence.
  `FiniteSupportRestrictionAssumptions` has been removed from the public
  sufficiency bundle.

## PDF Lemma 12 (`coherentnorm`) Status

Lean package for the conclusion:

- `FiniteCoherentProductQuasiAdditivityAssumptions`
- `coherentProductQuasiAdditivity_of_gaugeNormalization_and_interaction`
- `coherentnorm_of_decomposed_components`
- `FiniteCrossPriorBlockAssumptions.coherent_product`

Internally proved or structurally reconstructed:

- pairwise bilinear decomposition from left-slice affine, intercept, and slope pieces;
- intercept same-order, zero, and public-mix affine facts;
- slope difference/gap helper and slope package reconstruction;
- structural product public-mix/posterior-law compatibility;
- structural product associativity/swap relabeling and posterior-law transport;
- C1-C3 coefficient extraction in nondegenerate cases;
- singleton coefficient degeneracy and reclassification as gauge convention;
- nondegenerate coordinate-swap/rho reciprocity;
- K1-K4 interaction associativity from normalized triple-product expansions;
- nondegenerate interaction swap symmetry;
- nondegenerate common-κ extraction from K1-K3;
- singleton interaction degeneracy and reclassification as Step 5 singleton/gauge convention;
- final coherent quasi-additivity reassembly from pairwise bilinear form,
  gauge normalization, and interaction universality.

Still external/classical/convention for Lemma 12:

- `FinitePosteriorLawValueAffineAssumptions`: HM/posterior-law affine value representation interface.
- `FinitePosteriorValueRelabelingAssumptions`: coherent representative invariance under action/outcome relabeling.
- `ClassicalAffineUtilityUniquenessAssumptions`: first-coordinate affine-utility uniqueness.
- `ClassicalSecondCoordinateAffineUniquenessAssumptions`: intercept affine-utility uniqueness.
- `ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions`: slope affine-utility uniqueness.
- `FiniteSingletonCoefficientGaugeConventionAssumptions`: singleton linear-coefficient gauge convention.
- `FiniteProductLinearCoeffSwapSingletonConventionAssumptions`: singleton swap/rho gauge convention.
- `FiniteProductReferenceGaugeTransformAssumptions`: explicit positive reference-gauge transform interface.
- `FiniteCurrentRepresentativesGaugeNormalizedAssumptions`: convention that the current Lean representatives are already post-gauge.
- `FiniteSingletonInteractionCoefficientConventionAssumptions`: singleton interaction coefficient convention extending common κ to degenerate factors.

These remaining fields are not entropy/Faddeev/Shannon/MI assumptions. They are
classified as classical finite-dimensional affine representation interfaces,
coherent representative-choice interfaces, or singleton/gauge conventions.

## Exact Relabelling Invariance Status

Paper result:

- Exact relabelling invariance (`cor:permutationinvariance`): for a bijection
  of action labels, the coherently normalized representative at the relabeled
  prior assigns exactly the same value to the relabeled posterior law.

Lean target:

- `FinitePosteriorValueRelabelingAssumptions`
- `exactRelabelingInvariance_of_valueRelabeling`

Internal structural facts:

- `Relabeling.relabelDist` and `Relabeling.relabelChannel` define finite
  distribution/channel relabeling by equivalences.
- `posteriorLawIntegral_relabelChannel` proves posterior-law integral transport
  under simultaneous action/outcome relabeling.
- `relabelDist_prodAssoc`, `relabelChannel_prodAssoc`,
  `relabelDist_prodComm`, and `relabelChannel_prodComm` give the product
  associativity/swap relabeling facts used by coherentnorm.
- `product_value_swap_eq_of_value_relabeling` and
  `tripleProductValueAssociates_of_value_relabeling` are derived consequences
  once exact value relabeling of the chosen representatives is supplied.

Classification:

- The structural relabeling and posterior-law transport layer is internal.
- The exact cardinal equality
  `V_{e_* q}(e_* experiment) = V_q(experiment)` is a coherent
  representative-choice convention, already isolated as
  `FinitePosteriorValueRelabelingAssumptions`.
- It is not a separate live product/gauge gap, and it is not an
  entropy/Faddeev/Shannon/MI assumption.

## Support Restriction Status

Paper result:

- Support restriction (`lem:supprestrict`): zero-prior rows do not affect the
  posterior law, channels agreeing on the positive support are behaviorally
  equivalent at the boundary prior, comparisons at a boundary prior identify
  with comparisons on the full-support face, and representatives at boundary
  priors are read through the support face.

Lean targets:

- `supportSubtype`, `Dist.restrictToSupport`, and
  `Channel.restrictToSupport`
- `posteriorLawIntegral_restrictToSupport`
- `rel_ambient_to_support` and `rel_support_to_ambient`
- `pairwise_support_restriction_from_weak_equiv`
- `preference_support_restriction_of_axioms`
- `FullSupportMIRepExtendsToBoundary_of_supportRestriction`

Internal/proved:

- pure support deletion algebra: full support of the restricted prior, outcome
  marginal preservation, conditional entropy sum preservation, and mutual
  information preservation;
- posterior-law integral support reduction via support inclusion;
- A5 projection and inclusion weak comparisons;
- A1/A3 common-block assembly of those weak comparisons into the support-face
  preference equivalence;
- boundary MI extension from full-support block MI plus support restriction.

Classification:

- No live `FiniteSupportRestrictionAssumptions` field remains.
- The named support-restriction lemma is internal for the current Lean
  formalization.
- Later `FiniteCardinalSupportBoundaryAssumptions` and related Hfun/Faddeev
  boundary interfaces are downstream cardinal-extension obligations, not a
  remaining gap in `lem:supprestrict`.

## Cross-Prior Block Representation Status

Paper result:

- Cross-prior block representation (`lem:blockbridge`): for finite priors and
  channels, the two-block comparison is represented by comparing the two
  posterior-law values. The paper proves the bridge first for full-support
  priors using coherent product quasi-additivity and product-lift
  indifferences, then invokes support restriction for boundary priors.

Lean targets:

- `ProductLiftedComparison`
- `productLiftedComparison_represents`
- `product_block_transfer_of_A5_A3`
- `productLiftValue_of_coherentProductQuasiAdditivity`
- `unscaled_cross_prior_block_rep_of_product_parts`
- `FiniteCrossPriorBlockAssumptions.unscaled_cross_prior_block_rep`
- `blockbridge_fullSupport_of_decomposed_components`
- `CrossPriorBlockRepresentation`
- `crossPriorBlockRepresentation_of_unscaled`
- `crossPriorBlockRepresentation_of_decomposed_components`

Internal structural pieces:

- same-prior product-lifted comparisons are represented by
  `PosteriorValueRepresentation.represents_block_comparisons`;
- coherent product quasi-additivity and zero normalization give the two
  product-lift value identities;
- A3/A4/A5 projection/embedding replacement gives the
  product-to-original-block equivalence;
- universal positive scale converts the unscaled full-support bridge to the
  scaled `CrossPriorBlockRepresentation`.

Classification:

- No live field directly assumes the cross-prior block representation.
- The full-support blockbridge is reassembled internally from the decomposed
  coherent-product interfaces and A3/A4/A5 transfer.
- The formal `CrossPriorBlockRepresentation` remains full-support guarded by
  design. Boundary/all-prior uses are delegated to the already audited support
  restriction layer and later cardinal boundary extensions.

## Branch Aggregation, Cocycle, And Normalised Chain Rule Status

Paper results:

- `Branch aggregation`: first-stage/continuation experiments decompose as
  `F_q(P₁▷Q) = F_q(P₁) + Σ_o m(o) β(q,r_o) F_{r_o}(Q^o)`.
- `Branch-coefficient cocycle and normalised chain rule`: the coefficients
  satisfy cocycle/factorization `β(q,r)=a_q/a_r`, and normalized values satisfy
  the exact chain rule.

Internal structural pieces now proved:

- `posterior_seqComposeDep_of_pos`;
- `posteriorLawIntegral_seqComposeDep_eq_sum`;
- signed posterior-law difference operations and algebra;
- one-branch A7 weak/strict lifting:
  `A7_weak_one_branch_of_rel`, `A7_strict_one_branch_of_strict`;
- slope-cancellation algebra:
  `slopes_eq_of_affine_difference_constant`;
- singleton action-domain posterior/value collapse:
  `branchDist_eq_of_subsingleton`,
  `branchPosterior_eq_prior_of_subsingleton`,
  `posteriorLawIntegralExp_singleton_branch`,
  `samePosteriorLawExp_of_subsingleton_branch`,
  `branchValue_eq_zero_of_subsingleton`,
  `branchValue_channel_eq_zero_of_subsingleton`;
- assembled branch coefficient and nondegenerate positivity:
  `branchCoeffFromParts`, `branchCoeffFromParts_pos`;
- reassembly of the current uniform `BranchAggregationStructure` from the
  decomposed coefficient pieces plus the remaining formula bridge:
  `branchAggregationStructure_of_formula`;
- pre-universal chain structure:
  `BranchChainStructure`;
- reconstruction of that chain structure from scale factorization:
  `branchChainStructure_of_scaleFactorization`;
- internal normalized chain rule from factorization:
  `branchNormalizedValue_seqCompose_of_chain`;
- compatibility forgetful map:
  `branchChainStructure_of_scaleCoherence`.

Live branch-specific interfaces after Stage 13:

- `FiniteAffineLinearPartAssumptions`: classical finite affine-hull linear-part
  interface.
- `FiniteBranchSlicePositiveAffineAssumptions`: classical finite affine
  uniqueness for one branch slice, after A7 supplies same-order comparison.
- `FiniteBranchSlopeBackgroundIndependenceAssumptions`: paper-specific
  background-independence bridge using the affine linear part.
- `FinitePosteriorTangentSpaceSpanningAssumptions`: classical finite
  convex/linear algebra.
- `FiniteLinearFunctionalSameSignScalarAssumptions`: classical finite linear
  algebra.
- `FiniteBranchPathIndependenceAssumptions`: paper-specific A7/tangent
  path-independence bridge.
- `FiniteBranchBoundaryFaceScaleAssumptions`: paper-specific support-face
  full-to-face branch coefficient bridge.
- `FiniteBranchSingletonScaleConventionAssumptions`: representative/singleton
  support convention.
- `FiniteBranchAggregationFormulaAssumptions`: paper-specific final
  formula bridge once coefficients are supplied.
- `FiniteBranchCoeffCocycleAssumptionsFor`: paper-specific full-support
  cocycle statement.
- `FiniteBranchScaleFactorizationAssumptions`: paper-specific
  cocycle-to-scale and boundary/singleton scale factorization interface.

Faithfulness:

- Current downstream Lean uses the uniform continuation-outcome
  `BranchAggregationStructure`. The paper's A7 allows branch-dependent
  continuation outcome types. Stage 13 proves dependent A7 one-branch plumbing,
  but the final structure remains uniform because that is what downstream code
  consumes. A dependent final aggregation structure remains a faithfulness
  enhancement.

### Stage 14 Branch Path-Independence Refinement

Stage 14 split the full-support tangent/path-independence bridge more sharply.
Lean now proves the finite linear-algebra scalar extraction step:

- `FiniteBranchTangentSignPreservationAssumptions` isolates the
  A7/posterior-realization claim that aggregate and branch linear parts have
  the same sign partition on nonzero full-support tangent directions.
- `branch_linear_scalar_exists_of_tangentSign` proves that this sign partition,
  together with `FiniteLinearFunctionalSameSignScalarAssumptions`, gives a
  positive scalar `β` with `L_q η = β L_r η`.
- `branchPathScalarStructure_of_tangentSign` packages those scalars at the
  level of a fixed posterior value representative.
- `FiniteBranchFullSupportSlopeIdentityAssumptions` isolates the remaining
  analytic step identifying the affine branch-slice slope as
  `m(o) * β(q,r)`.
- `branchFullSupportPathIndependence_of_scalar` reassembles a
  representation-level full-support path-independence structure from the
  scalar relation and the slope identity.

Status after Stage 14:

- Internally proved: the same-sign scalar extraction from tangent sign
  preservation.
- Classical-known: `FiniteLinearFunctionalSameSignScalarAssumptions` and the
  finite tangent-space spanning theorem remain acceptable finite
  linear/convex-algebra interfaces.
- Paper-specific: deriving `FiniteBranchTangentSignPreservationAssumptions`
  from A7 plus posterior-law realization, and proving
  `FiniteBranchFullSupportSlopeIdentityAssumptions` from compound posterior-law
  algebra plus affine linear parts.
- Compatibility/live: the old global
  `FiniteBranchPathIndependenceAssumptions` remains live for downstream
  branch-coefficient assembly. It is now known to be stronger than the newly
  proved representation-level scalar theorem because its `branchPathCoeff`
  field is global, while the scalar theorem is naturally tied to the chosen
  posterior value representative.

### Stage 14A Branch Tangent Sign-Preservation Refinement

Stage 14A proved the feasible-channel part of the A7 sign argument:

- `linearPart_difference_pos_iff_value_gt`,
  `linearPart_difference_zero_iff_value_eq`, and
  `linearPart_difference_swap_eq_neg` translate affine linear-part differences
  into value comparisons.
- `block_rel_of_channel_value_ge` and
  `block_strictRel_of_channel_value_gt` translate value weak/strict
  comparisons into primitive block preferences, using the already internal
  block-swap relabeling theorem for strict reverse orientation.
- `branch_feasible_difference_pos_of_branch_pos` proves that a positive branch
  feasible posterior-law difference gives a positive aggregate feasible
  difference.
- `branch_feasible_difference_zero_of_branch_zero` proves that a zero branch
  feasible difference gives a zero aggregate feasible difference.

Stage 14A also split the old tangent sign package:

- `FiniteBranchTangentSignAgreementAssumptions` contains only sign agreement on
  arbitrary nonzero signed tangent directions.
- `FiniteBranchLinearPartNonzeroAssumptions` contains only the nonzero branch
  linear-part witness.
- `branchTangentSignPreservation_of_signAgreement_and_nonzero` reconstructs
  `FiniteBranchTangentSignPreservationAssumptions` from those two components.

Status after Stage 14A:

- Internally proved: sign preservation for feasible one-branch channel
  differences, including the strict-positive and zero cases.
- Still paper-specific: extending feasible sign preservation to arbitrary
  signed tangent directions in the current extensional `PosteriorLawSigned`
  representation.
- Still separate: proving `FiniteBranchLinearPartNonzeroAssumptions` from
  A1/nontriviality and the affine linear-part API.
- Preferred architecture remains representation-level. The old global
  `FiniteBranchPathIndependenceAssumptions` is still a legacy compatibility
  package and should not be forced unless a coherent globalization theorem is
  added.

### Stage 14B Branch Linear-Part Nonzero Witness

Stage 14B proved the A1-aware nonzero branch-linear-functional witness:

- `branch_linear_part_nonzero_of_value_gap` shows that any value gap
  `V_r(E) ≠ V_r(E')` gives a signed posterior-law direction
  `posteriorLawDifferenceExp r E E'` on which the affine linear part is
  nonzero.
- `branch_value_ne_of_strict_experiment_pref` converts strict experiment-pair
  preference into a value gap for any `PosteriorValueRepresentation`.
- `not_subsingleton_of_dist_nondegenerate` converts the branch nondegeneracy
  witness `∃ a b, a ≠ b ∧ 0 < r a ∧ 0 < r b` into `¬ Subsingleton A`.
- `branch_id_uninformativeU_experiment_strict_of_A1` reuses the upstream
  structural Unit/PUnit no-information and block-swap relabeling plumbing to
  turn A1 into strict preference between full revelation and no information.
- `branch_value_gap_of_A1` gives concrete experiments with distinct values at
  every full-support nondegenerate prior.
- `branch_linear_part_nonzero_of_A1` proves the nonzero linear-part witness
  from `TraceAxioms F`, `PosteriorValueRepresentation F`, and
  `FiniteAffineLinearPartAssumptions`.
- `FiniteBranchLinearPartNonzeroFromA1Assumptions` packages this faithful
  A1-aware witness, and `branchLinearPartNonzeroFromA1_of_linearPart`
  reconstructs it internally.

Status after Stage 14B:

- Internally proved: the intended nonzero witness, with the needed
  `TraceAxioms F` hypothesis.
- Design issue exposed: the older
  `FiniteBranchLinearPartNonzeroAssumptions` has no `TraceAxioms F` argument.
  It is therefore stronger than what A1 can prove and remains a legacy
  hax-free compatibility interface unless downstream path-scalar code is
  refactored to use the A1-aware representation-level package.
- A7 faithfulness check passed: primitive A7 and the one-branch lemmas use the
  branch-dependent outcome family `O₂ : O₁ → Type`; the final
  `BranchAggregationStructure` is uniform only as the downstream formula
  specialization, not as a primitive A7 assumption.

### Stage 14C Branch Path Refactor

Stage 14C added an A1-aware representation-level path route:

- `BranchTangentSignPreservationFor` carries tangent sign agreement for a fixed
  `(F, hax, hV, hlin)` and deliberately does not bundle the nonzero witness.
- `branchTangentSignPreservationFor_of_signAgreement` specializes the existing
  sign-agreement interface to that fixed representative.
- `branch_linear_scalar_exists_of_A1_tangentSign` applies the finite same-sign
  scalar theorem using `BranchTangentSignPreservationFor` and the proved
  A1-aware nonzero theorem `branch_linear_part_nonzero_of_A1`.
- `branchPathScalarStructure_of_A1_tangentSign` constructs
  `BranchPathScalarStructure F hV hlin` without the old hax-free
  `FiniteBranchTangentSignPreservationAssumptions`.
- `branchFullSupportPathIndependence_of_A1_scalar` constructs
  `BranchFullSupportPathIndependenceStructure F hV` from sign agreement,
  same-sign scalar extraction, and the still-live full-support slope identity.

Stage 14C also added a representation-level coefficient assembly route:

- `branchCoeffFromRepParts` and `branchCoeffFromRepParts_pos` assemble the
  full-support representation-level path coefficient with the existing boundary
  and singleton coefficient interfaces.
- `FiniteBranchAggregationFormulaFor` is the fixed-representative formula-level
  bridge.
- `branchAggregationStructure_of_formulaFor` reassembles the existing
  `BranchAggregationStructure F` from representation-level path data plus this
  fixed-representative formula bridge.

Status after Stage 14C:

- Preferred path: representation-level and A1-aware.
- Still live: `FiniteBranchTangentSignAgreementAssumptions` and
  `FiniteBranchFullSupportSlopeIdentityAssumptions`.
- Legacy compatibility: `FiniteBranchLinearPartNonzeroAssumptions`,
  `FiniteBranchTangentSignPreservationAssumptions`, and
  `FiniteBranchPathIndependenceAssumptions` remain in the file because older
  formula-level assembly still references the global coefficient package.
- Downstream assembly was partially refactored by adding a parallel
  representation-level route. Existing downstream callers have not yet been
  switched away from `FiniteBranchAggregationAssumptions`.

### Stage 14D Branch Tangent Sign-Agreement Refinement

Stage 14D attacked `FiniteBranchTangentSignAgreementAssumptions` directly.
It found that the legacy interface is too strong in two ways:

- it is hax-free, while the proof uses A7 through `TraceAxioms F`;
- it quantifies over every extensional `PosteriorLawSigned A`, while the paper
  only asserts sign agreement on tangent signed posterior laws with zero total
  mass and zero barycentre.

Stage 14D added the tangent predicate and narrower realization interfaces:

- `PosteriorLawTangent` states zero total mass and zero barycentre.
- `FiniteCommonOutcomeTangentRealizationAssumptions` isolates the padding and
  posterior-realization step needed to realize a tangent signed law as a
  positive scalar multiple of a feasible difference between two continuation
  channels with a common outcome type.
- `FiniteFullSupportBranchReachabilityAssumptions` isolates the finite
  probability fact that a full-support posterior can be reached from a
  full-support prior by a positive-probability branch.
- `BranchTangentSignAgreementOnTangentFor` is the faithful A7-aware,
  representation-level target: sign agreement only on tangent directions.
- `BranchTangentForwardZeroOnTangentFor` is the proved forward/zero half of
  that target.

Internally proved in Stage 14D:

- `posteriorLawDifference_seqComposeDep_one_branch`: if two dependent
  continuation profiles differ only in one branch, the signed posterior-law
  difference of the compound experiments is the branch probability times the
  branch signed posterior-law difference.
- `branch_tangent_forward_zero_of_commonOutcome_realization`: for a
  common-outcome feasible branch direction that reaches posterior `r`, positive
  branch-linear sign and zero branch-linear sign transport to the aggregate
  prior.
- `branchTangentForwardZeroOnTangentFor_of_realization`: common-outcome tangent
  realization plus full-support branch reachability gives the representation-
  level forward/zero package.

Remaining after Stage 14D:

- Reverse positive sign agreement, i.e. deriving
  `0 < L_r η` from `0 < L_q η`, should follow by applying the same forward
  theorem to the swapped direction `-η`, but this still needs the common-outcome
  realization interface to be closed under signed negation.
- Full `BranchTangentSignAgreementOnTangentFor` is not yet reconstructed.
- Legacy `FiniteBranchTangentSignAgreementAssumptions` remains live only as a
  compatibility interface and should not be treated as the faithful statement
  of the paper.

### Stage 14E Tangent Realization and Reachability

Stage 14E attacked the finite-probability geometry isolated in Stage 14D.

Internally proved:

- `outcomePadLeft` and `outcomePadRight`: common-outcome padding of finite
  channels into a disjoint-sum outcome type.
- `posteriorLawIntegral_outcomePadLeft` and
  `posteriorLawIntegral_outcomePadRight`: padded channels preserve
  posterior-law integrals.
- `commonOutcomeTangentRealization_of_tangentSpanning`: the older tangent-space
  spanning interface implies `FiniteCommonOutcomeTangentRealizationAssumptions`.
  Thus common-outcome tangent realization is no longer an independent
  paper-specific bridge once finite tangent spanning is accepted.
- `PosteriorLawTangent_neg`,
  `posteriorLawSignedSMul_neg_ne_zero`, and
  `commonOutcomeTangentRealization_neg`: tangent realization is closed under
  signed negation by swapping the two realizing experiments.
- `branchTangentSignAgreementOnTangentFor_of_forwardZero_and_neg`: the forward
  and zero A7 transport package implies full tangent-domain sign agreement by
  applying the forward positive implication to `-η`.
- `branchTangentSignAgreementOnTangentFor_of_realization_and_reachability`:
  common-outcome tangent realization plus full-support branch reachability
  closes the faithful A7-aware `BranchTangentSignAgreementOnTangentFor`.
- `binaryReachChannel`,
  `outcomeMarginal_binaryReachChannel_true`,
  `branchPosterior_binaryReachChannel_true`, and
  `fullSupportBranchReachability_of_dominated_mass`: if a positive branch mass
  `ε` satisfies `ε * r a ≤ q a` for every action, the explicit two-branch
  channel over `ULift Bool` reaches posterior `r` from prior `q` with positive
  probability.

New narrow remaining interface:

- `FinitePositiveBranchMassDominatedAssumptions`: finite-order choice of
  `ε > 0` with `ε * r(a) ≤ q(a)` for full-support finite `q,r`.
  This is strictly narrower than full branch reachability and is classified as
  classical finite ordered-field/finite-minimum algebra.

Status after Stage 14E:

- `FiniteCommonOutcomeTangentRealizationAssumptions`: reconstructed from
  `FinitePosteriorTangentSpaceSpanningAssumptions`.
- `FiniteFullSupportBranchReachabilityAssumptions`: reconstructed from
  `FinitePositiveBranchMassDominatedAssumptions` plus the internally proved
  binary-channel construction.
- `BranchTangentSignAgreementOnTangentFor`: reconstructed from tangent
  realization and reachability.
- Legacy `FiniteBranchTangentSignAgreementAssumptions` remains too strong as a
  hax-free/all-signed-laws compatibility interface.

### Stage 14F Positive Branch Mass

Stage 14F removed the finite dominated-mass residue from Stage 14E.

Internally proved:

- `exists_positive_lower_bound_fullSupport`: every full-support finite
  distribution has a positive lower bound on all coordinates, obtained as the
  finite minimum of `{q a}`.
- `exists_positive_branch_mass_dominated`: for full-support finite `q,r`, there
  exists `ε > 0` such that `ε * r a ≤ q a` for every action.  The proof takes
  `ε = δ / 2`, where `δ` is the positive coordinate lower bound for `q`, and
  uses `Dist.prob_le_one r a`.
- `positiveBranchMassDominated_of_finite`:
  `FinitePositiveBranchMassDominatedAssumptions` is now internal.
- `fullSupportBranchReachability_of_finite`:
  `FiniteFullSupportBranchReachabilityAssumptions` is now internal via the
  binary reachability channel from Stage 14E.
- `branchTangentSignAgreementOnTangentFor_of_tangentSpanning`:
  finite tangent spanning plus internal full-support branch reachability gives
  the faithful A7-aware tangent-domain sign agreement package.

Status after Stage 14F:

- `FinitePositiveBranchMassDominatedAssumptions`: proved internally.
- `FiniteFullSupportBranchReachabilityAssumptions`: compatibility package,
  reconstructed internally.
- `BranchTangentSignAgreementOnTangentFor`: reconstructed from
  `FinitePosteriorTangentSpaceSpanningAssumptions` plus internal reachability.
- The remaining finite-geometry interface in this sublayer is
  `FinitePosteriorTangentSpaceSpanningAssumptions`.

### Stage 15 Path Core

Stage 15 attacked the remaining full-support path-independence core.

Internally proved:

- `posteriorLawIntegral_const_one` and `posteriorLawIntegralExp_const_one`:
  posterior-law integration preserves the constant-one test function.
- `posteriorLawIntegral_coord` and `posteriorLawIntegralExp_coord`:
  posterior-law integration of coordinate evaluation recovers the prior
  coordinate.
- `posteriorLawDifferenceExp_tangent`: every feasible experiment posterior-law
  difference has zero total mass and zero barycentre.
- `PosteriorLawTangent_add` and `PosteriorLawTangent_smul`: tangent signed laws
  are closed under addition and scalar multiplication.
- `branch_linear_part_nonzero_tangent_of_A1`: A1 gives a nonzero branch-linear
  witness inside the tangent subspace.
- `branch_slice_slope_eq_probability_mul_scalar_of_value_gap`: if a branch
  slice has two continuations with distinct reached-posterior values, the
  affine slope is forced to be `m * beta(q,r)` from the full scalar relation.
- `branchFullSupportSlopeIdentityWithValueGap_of_linearPart`: packages the
  value-gap slope identity as internal algebra.
- `branch_slice_slope_eq_probability_mul_tangent_scalar_of_value_gap`: the same
  value-gap slope identity using only the tangent-subspace scalar relation.
- `branchPathTangentScalarStructure_of_A1_tangentSignOnTangent`: finite tangent
  spanning plus the tangent same-sign scalar interface gives a faithful
  tangent-subspace path scalar structure.

New/refined interfaces:

- `FiniteLinearFunctionalSameSignScalarOnTangentAssumptions`: classical finite
  linear algebra on the tangent subspace.  This is narrower than the older
  all-signed-law same-sign scalar theorem and matches what A7 supplies.  It is
  implemented internally as of the Stage Mathlib same-sign scalar pass by
  `finiteLinearFunctionalSameSignScalarOnTangent_of_direct`.
- `BranchPathTangentScalarStructure`: representation-level scalar relation on
  genuine tangent signed posterior laws only.
- `FiniteBranchFullSupportSlopeIdentityWithValueGapAssumptions`: faithful
  nondegenerate/value-gap slope identity.  It avoids pretending that the slope
  in a value-constant fixed continuation alphabet is identifiable.

Status after Stage 15:

- `FinitePosteriorTangentSpaceSpanningAssumptions` remains external as finite
  convex/probability geometry, but the audit records why it is not provable
  from the current `PosteriorLawSigned` definition alone: `PosteriorLawSigned`
  is the full function type `(Dist A → ℝ) → ℝ`, not a finite signed-measure
  subtype.
- `FiniteBranchFullSupportSlopeIdentityAssumptions` remains a legacy broad
  compatibility field.  Its current statement quantifies over fixed
  continuation alphabets even when no branch value gap is available, so the
  slope is not value-identifiable.  The proved replacement is the
  value-gap/tangent-scalar slope identity above.
- The faithful A1-aware route now goes through
  `BranchTangentSignAgreementOnTangentFor` and
  `BranchPathTangentScalarStructure`.  The old hax-free/global path packages
  remain legacy compatibility packages unless downstream code is migrated to
  the representation-level path objects.

### Stage 16 Branch Aggregation Completion Pass

Stage 16 migrated more of the branch layer to the faithful representation-level
tangent route.

Internally added:

- `branchCoeffFromTangentRepParts` and `branchCoeffFromTangentRepParts_pos`:
  assemble the public branch coefficient from the faithful full-support tangent
  scalar plus the existing boundary and singleton coefficient interfaces.
- `FiniteBranchAggregationFormulaTangentFor`: formula-level bridge for the
  faithful tangent-scalar coefficient assembly.  This bypasses the legacy
  hax-free `FiniteBranchPathIndependenceAssumptions`, but still assumes the
  final sequential formula after the branch pieces are supplied.
- `branchAggregationStructure_of_tangentFormulaFor`: reassembles
  `BranchAggregationStructure F` from the faithful tangent-scalar route.
- `FiniteBranchCoeffCocycleTangentScalarFor`,
  `branchCoeffTangentScalar_cocycle_fullSupport`, and
  `branchCoeffCocycleTangentScalar_of_A1`: prove the full-support cocycle for
  the faithful tangent scalar coefficient itself by comparing scalar relations
  and cancelling an A1-supplied nonzero tangent direction.
- `branchChainStructure_of_tangentFormulaAndScaleFactorization`: exposes the
  pre-universal chain structure through the faithful branch-aggregation route
  once scale factorization is supplied for the resulting
  `BranchAggregationStructure`.

Status after Stage 16:

- The normalised chain-rule theorem `branchNormalizedValue_seqCompose_of_chain`
  applies unchanged to a chain structure produced from the faithful tangent
  route.
- The public full-support cocycle interface
  `FiniteBranchCoeffCocycleAssumptionsFor` is still about
  `BranchAggregationStructure.branchCoeff`.  The proved cocycle is currently
  for `BranchPathTangentScalarStructure.branchPathCoeff`; transporting it to
  the public coefficient requires identifying the branch-aggregation coefficient
  with the faithful tangent scalar in the full-support nondegenerate case.
- `FiniteBranchAggregationFormulaTangentFor` remains a paper-specific
  formula-level bridge.  The local value-gap slope theorem does not by itself
  telescope one-branch changes into the full sequential sum formula, and
  value-constant branch slices are not slope-identifying.
- `FiniteBranchBoundaryFaceScaleAssumptions` remains a paper-specific
  support-face bridge.  Support restriction is internally proved, but the
  full-to-face branch coefficient relation has not been constructed.
- `FiniteBranchSingletonScaleConventionAssumptions` remains an explicit
  singleton/support convention; literal singleton action types have internal
  zero-value lemmas, but singleton support inside an ambient action space still
  uses support-face/convention data.

### Stage 17 Branch Progress

Stage 17 transported more of the faithful tangent route to public branch
interfaces.

Internally added:

- `branchAggregationStructure_of_tangentFormulaFor_branchCoeff_eq`: the public
  branch coefficient of the faithfully reassembled `BranchAggregationStructure`
  is definitionally the assembled tangent/boundary/singleton coefficient.
- `branchAggregationStructure_of_tangentFormulaFor_branchCoeff_fullSupport_eq`:
  on full-support reached posteriors, that public coefficient is exactly the
  faithful tangent scalar coefficient.
- `branchCoeffCocycleFor_of_tangentScalar`: transports the internally proved
  tangent-scalar full-support cocycle to the public
  `FiniteBranchCoeffCocycleAssumptionsFor` interface for the faithfully
  reassembled branch structure.
- `FiniteBranchScaleFactorizationFullSupportAssumptions`,
  `branchFullSupportBaseScale`, and
  `branchScaleFactorizationFullSupport_of_cocycle`: split and prove
  basepoint scale factorization on nondegenerate full-support ambient action
  simplices from the public cocycle.
- `FiniteBranchBoundaryValueTransportAssumptions` and
  `FiniteBranchBoundaryCoefficientTransportAssumptions`: split the boundary
  residue into value-representative support-face transport and the actual
  full-to-face linear-part scalar relation.

Status after Stage 17:

- Public full-support cocycle is reconstructed for the faithful branch
  aggregation structure.
- Full-support scale factorization is reconstructed as a strict sub-result.
- Full `FiniteBranchScaleFactorizationAssumptions` remains live because it also
  covers boundary and singleton reached posteriors.
- `FiniteBranchBoundaryFaceScaleAssumptions` remains a compatibility package,
  now decomposed conceptually into value transport plus boundary coefficient
  transport.
- `FiniteBranchAggregationFormulaTangentFor` remains the main branch formula
  bridge. It still needs affine linear-part sum/telescoping, boundary
  contribution, and value-constant/singleton handling.

### Stage 18 Branch Formula Progress

Stage 18 attacked the faithful branch formula bridge
`FiniteBranchAggregationFormulaTangentFor`.

Internally added:

- `posteriorLawSignedFinsetSum`, `posteriorLawSignedSum`, and their basic
  application/empty/insert lemmas: finite algebra for extensional signed
  posterior laws.
- `linearPart_zero`, `linearPart_finsetSum`, and `linearPart_sum`: linear-part
  algebra over finite signed-law sums.
- `posteriorLawIntegral_uninformativeChannelU_eq_prior` and
  `posteriorLawIntegralExp_uninformativeChannelU_eq_prior`: the uninformative
  experiment induces the point-mass posterior law at the prior.
- `posteriorLawDifference_seqComposeDep_eq_sum_branch_differences`: the
  dependent sequential posterior-law difference from the first-stage experiment
  is exactly the sum of branch probabilities times branch continuation
  posterior-law differences from the no-information baseline.
- `branch_formula_affine_expansion_seqComposeDep`: the affine expansion of the
  dependent sequential value difference via `FiniteAffineLinearPartAssumptions`.
- `branch_formula_linearPart_seqComposeDep_sum`: the dependent sequential value
  difference linear part decomposes as the finite sum of branch linear parts.
- `branch_formula_fullSupport_summand_linearPart_eq`: the full-support
  nondegenerate branch summand equals
  `m(o) * branchPathCoeff q r_o * V_{r_o}(Q^o)`.
- `branch_formula_singleton_summand_zero`: singleton-support branch terms are
  zero regardless of the positive singleton coefficient convention.

New narrow interfaces:

- `FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions`: pure finite
  probability/relabeling bridge transporting the internally proved dependent
  sigma-outcome posterior-law sum identity to the public uniform-outcome
  product channel `P₁ ▷ Q`.
- `FiniteBranchFormulaBoundarySummandAssumptions`: single-boundary-branch
  summand bridge after support-face value and coefficient transport.

Status after Stage 18:

- The dependent affine/sum backbone of the branch formula is internal.
- The full-support value-varying summand is internal.
- The singleton summand is internal modulo the existing singleton coefficient
  convention, which is not value-identifiable.
- The public `FiniteBranchAggregationFormulaTangentFor` remains live because it
  is stated for uniform product outcomes and because boundary summands still
  require support-face representative/coefficient transport.

### Stage 19 Fixed-Output Posterior Algebra

Stage 19 attacked the finite probability/relabeling bridge
`FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions`.

Internally added:

- `outcomeMarginal_seqCompose_apply`: public fixed-output sequential outcome
  marginals factor into first-stage branch mass times continuation marginal at
  the branch posterior.
- `posterior_seqCompose_of_pos`: positive public fixed-output sequential
  outcomes have the continuation posterior of the selected branch.
- `posteriorLawIntegral_seqCompose_eq_sum`: the public `P₁ ▷ Q` posterior law
  is the first-stage marginal mixture of branch posterior laws.
- `posteriorLawDifference_seqCompose_eq_sum_branch_differences`: fixed-output
  posterior-law difference from `P₁` to `P₁ ▷ Q` is the sum of branch
  probabilities times branch continuation differences from the no-information
  baseline.
- `fixedOutcomePosteriorAlgebra_of_finite`: reconstructs
  `FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions` internally.
- `branch_formula_affine_expansion_seqCompose` and
  `branch_formula_linearPart_seqCompose_sum`: fixed-output affine and
  linear-part branch-sum expansions.

Status after Stage 19:

- `FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions` is internal and
  no longer a live external bridge.
- The public fixed-output branch formula has the same affine/sum backbone as
  the dependent version.
- Stage 20 proves zero-probability branch summands vanish, proves singleton
  support branch summands vanish on both the linear-part and coefficient/value
  sides, packages per-branch summand identities, and reconstructs
  `FiniteBranchAggregationFormulaTangentFor` from the remaining boundary
  summand bridge.
- The central live formula residue is now boundary/support-face value and
  coefficient transport, exposed through
  `FiniteBranchFormulaBoundarySummandAssumptions`.  Final public formula
  reassembly is internal once that boundary summand package is supplied.
- Stage 21 adds the faithful hax-aware boundary summand package
  `FiniteBranchFormulaBoundarySummandFor`, proves it from
  `FiniteBranchBoundaryValueTransportAssumptions` and
  `FiniteBranchBoundaryCoefficientTransportAssumptions`, and derives
  `FiniteBranchAggregationFormulaTangentFor` directly from those two boundary
  transport interfaces.  The old hax-free
  `FiniteBranchFormulaBoundarySummandAssumptions` remains a compatibility
  package.
- Stage 21 also splits public scale factorization into internal full-support
  factorization plus explicit boundary and singleton extension packages:
  `FiniteBranchScaleFactorizationBoundaryTransportAssumptions` and
  `FiniteBranchScaleFactorizationSingletonConvention`.

## Classification Table

| Assumption | Classification | Current status |
|---|---|---|
| `FiniteDPIAssumptions` | Classical acceptable external theorem | Standard finite data-processing inequalities for outcome post-processing and action Bayes pushforward completions. Still explicit. |
| `FiniteSamePosteriorLawBlackwellEquivalenceAssumptions` | Classical acceptable finite Blackwell/sufficiency theorem | Same posterior law at a full-support finite prior gives experiment postprocessings/garblings in both directions. This is the remaining classical pre-Lemma-12 Blackwell interface. |
| `FiniteBlackwellPosteriorAssumptions` | Compatibility package, internally reconstructed | No longer live in `SufficiencyExternalAssumptions`. Lean reconstructs it from `FiniteSamePosteriorLawBlackwellEquivalenceAssumptions` plus internal A4/A3/A1 preference-replacement plumbing. |
| `FiniteHersteinMilnorAssumptions` | Classical but needs a better formal statement; currently paper-specific too | Herstein-Milnor is classical, but this record directly supplies the posterior value functional, posterior-law invariance, representation, and zero normalization. |
| `FiniteBranchAggregationAssumptions` | Compatibility monolith, decomposed in Stages 13-23 but still live in the old sufficiency bundle | Stage 13 split its content into affine-linear-part, branch-slice affine uniqueness, background-independence, tangent/path-independence, boundary face-scale, singleton support convention, and formula-level bridge interfaces. Stage 14 further split full-support path independence into tangent sign preservation, same-sign scalar extraction, and full-support slope identity. Lean proves compound posterior-law algebra, one-branch A7 lifting, singleton-domain value collapse, assembled coefficient positivity, same-sign scalar extraction from tangent sign preservation, common-outcome tangent realization from tangent spanning, negation closure, faithful tangent-domain sign agreement from realization plus reachability, binary full-support branch reachability, the positive dominated branch mass lemma, and legacy `branchAggregationStructure_of_formula`. Stage 15 proves feasible differences are tangent, adds the faithful tangent-subspace scalar route, and proves slope identification in the value-gap case. Stage 16 adds the faithful tangent-scalar coefficient assembly, `FiniteBranchAggregationFormulaTangentFor`, and `branchAggregationStructure_of_tangentFormulaFor`. Stage 17 proves public coefficient identification and transports the faithful full-support cocycle to `FiniteBranchCoeffCocycleAssumptionsFor` for the faithfully reassembled structure. Stage 18 proves finite signed-law sum algebra, dependent sequential posterior-law difference decomposition, dependent affine linear-part branch-sum expansion, the full-support summand identity, and singleton zero summands; it splits the remaining formula residue into fixed-outcome posterior algebra and boundary summand interfaces. Stage 19 proves the fixed-output/public `P₁ ▷ Q` posterior-law algebra and reconstructs `FiniteBranchFormulaFixedOutcomePosteriorAlgebraAssumptions` internally. Stage 20 proves zero-probability summand vanishing, singleton-support posterior-law collapse and singleton linear-part summand vanishing, introduces `FiniteBranchFormulaSummandAssumptions`, reconstructs it from `FiniteBranchFormulaBoundarySummandAssumptions` plus the internal zero/full/singleton cases, and reconstructs `FiniteBranchAggregationFormulaTangentFor` from this summand package. Stage 21 adds the hax-aware `FiniteBranchFormulaBoundarySummandFor`, proves the ambient/support-face posterior-law difference pushforward identity, proves `FiniteBranchFormulaBoundarySummandFor` from boundary value and coefficient transport, and reconstructs `FiniteBranchAggregationFormulaTangentFor` directly from these boundary transports. Stage 22 exposes the faithful branch-chain route from explicit residual interfaces. Stage 23 adds `FiniteFaithfulBranchAggregationAssumptions` and `SufficiencyFaithfulBranchAssumptions`, which produce `BranchAggregationStructure`, `BranchChainStructure`, and the normalized chain rule without reconstructing the old hax-free/global monolith. The global `FiniteBranchPathIndependenceAssumptions`, universal `FiniteBranchFullSupportSlopeIdentityAssumptions`, and hax-free `FiniteBranchFormulaBoundarySummandAssumptions` remain legacy compatibility packages. |
| `FiniteScaleCoherenceAssumptions` | Compatibility monolith; Stage 13 isolated the pre-universal chain layer and Stages 16-23 added a faithful tangent route into it | The old package still includes later named results (`facescales` and universal scale coherence). Stage 13 added `BranchChainStructure`, `FiniteBranchCoeffCocycleAssumptionsFor`, `FiniteBranchScaleFactorizationAssumptions`, `branchChainStructure_of_scaleFactorization`, and proved `branchNormalizedValue_seqCompose_of_chain` from factorization. Stage 16 proves full-support cocycle for the faithful tangent scalar coefficient as `branchCoeffTangentScalar_cocycle_fullSupport` and adds `branchChainStructure_of_tangentFormulaAndScaleFactorization`, showing that once the faithful tangent route supplies a public `BranchAggregationStructure` and scale factorization is available, the normalised chain rule applies. Stage 17 transports that cocycle to the public coefficient for the faithful branch structure and proves `branchScaleFactorizationFullSupport_of_cocycle`, the nondegenerate full-support basepoint factorization sub-result. Stage 21 splits full public scale factorization into `FiniteBranchScaleFactorizationBoundaryTransportAssumptions` and `FiniteBranchScaleFactorizationSingletonConvention`, and reconstructs `FiniteBranchScaleFactorizationAssumptions` from full-support factorization plus those two extensions. Stage 23 exposes this through `FiniteFaithfulBranchAggregationAssumptions`, `branchChainStructure_of_faithfulAssumptions`, and `normalizedChainRule_of_faithfulAssumptions`. Universal scale collapse remains outside what is proved. |
| `FiniteCrossPriorBlockAssumptions` | Paper-specific bridge, narrower after Stage 10AE | This now contains `FinitePosteriorLawValueAffineAssumptions`, `ClassicalAffineUtilityUniquenessAssumptions`, `ClassicalSecondCoordinateAffineUniquenessAssumptions`, `ClassicalSecondCoordinateSlopeAffineUniquenessAssumptions`, `FinitePosteriorValueRelabelingAssumptions`, `FiniteSingletonCoefficientGaugeConventionAssumptions`, `FiniteProductLinearCoeffSwapSingletonConventionAssumptions`, `FiniteProductReferenceGaugeTransformAssumptions`, `FiniteCurrentRepresentativesGaugeNormalizedAssumptions`, and `FiniteSingletonInteractionCoefficientConventionAssumptions` applied to the derived pairwise package. `FiniteSingletonSliceAffineAssumptions` is proved internally via `singletonSliceAffine_of_singletonCollapse`. `FiniteProductSliceInterceptAssumptions` is no longer live: Lean derives it from second-coordinate affine uniqueness plus the proved intercept same-order, zero, and public-mix affine facts. `FiniteProductSliceSlopeAssumptions` is no longer live: Lean derives it from second-coordinate slope-affine uniqueness. `FiniteTripleProductValueAssociativityAssumptions` is no longer live: Lean derives it from coherent posterior value relabeling plus structural product associativity relabeling. `FiniteTripleProductCoeffExtractionAssumptions` is no longer live: Lean derives nondegenerate C1, C2, and C3 internally and treats singleton coefficient equations as gauge conventions because singleton coordinate values vanish identically. `FiniteProductLinearCoeffSwapAssumptions` is no longer live: Lean proves product-swap value equality and nondegenerate rho reciprocity internally from value relabeling, and treats singleton swap/rho equations as gauge conventions because singleton coordinate values vanish identically. `FiniteProductPositiveGaugeChoiceAssumptions` is no longer live: Lean derives it from an explicit positive gauge-transform package plus the convention that the current representatives are already the post-gauge representatives. `FiniteProductInteractionAssociativityAssumptions` is no longer live: Lean proves K1-K3 from normalized triple-product expansions and K4 from K1-K3. `FiniteProductInteractionSwapAssumptions` is no longer live: Lean proves nondegenerate interaction symmetry from product-swap value equality and normalized product coefficients. `FiniteSingletonInteractionCoefficientConventionAssumptions` remains live as a Step 5 singleton/gauge convention: Lean proves the singleton interaction term vanishes identically, so the coefficient is not value-identifiable. `FiniteProductInteractionUniversalityAssumptions` is no longer live: Lean derives nondegenerate common kappa from the derived K1-K3 and treats singleton interaction coefficients as this Step 5 convention. `FiniteProductLinearCoeffAssociativityAssumptions` is no longer live: Lean derives it from value-level triple associativity plus the reconstructed coefficient extraction. `FiniteProductGaugeNormalizationAssumptions` is no longer live: Lean derives it from the reconstructed coefficient associativity, swap/rho reciprocity, and derived gauge-choice bridge. `FiniteProductGaugeCoherenceAssumptions` is no longer live: Lean derives it from gauge normalization and the reconstructed interaction universality package. `FiniteCoherentProductQuasiAdditivityAssumptions` is no longer live: Lean derives the PDF Lemma 12 package directly as `coherentnorm_of_decomposed_components`, using pairwise bilinear form, gauge normalization, and interaction universality. Lean proves product associativity/swap relabeling structurally, product-associativity posterior-law integral transport structurally, public-mix posterior-law mixture structurally, derives channel-level `FinitePosteriorValueAffineAssumptions` from law-level value affinity, proves A1 experiment-pair strictness structurally, derives cardinal `FiniteValueNonconstancyAssumptions` from that strictness plus value representation, proves deterministic bijective outcome postprocessing preserves posterior laws, proves the canonical product/public-mix channel postprocessing identities, derives product/public-mix posterior-law compatibility structurally, derives product-slice public-mix affinity from channel-level value public-mix affinity plus that structural theorem, proves the A8 value-order coordinate-independence consequences, proves the first-coordinate product-slice same-order theorem from A8 plus A3/A4/A5 projection/embedding transfer, derives affine-slice uniqueness from the Stage 10H/10L/10M parts, derives the old left-slice affine package from affine-slice uniqueness, derives pairwise bilinear form from the slice-affine pieces, derives the old coherent product formula `V_{q⊗r}(P⊗R)=V_q(P)+V_r(R)+κ V_q(P)V_r(R)` from pairwise bilinear form plus the derived gauge package, then derives product-lift value identities, proves product-block transfer from A3/A4/A5, proves same-prior product comparison from the existing value representation, assembles the unscaled bridge internally, and universal scale still derives the scaled `CrossPriorBlockRepresentation`. |
| `FiniteEntropyRegularityFromAxiomsAssumptions` | Paper-specific bridge, acceptable temporarily but must be proved | Given `TraceAxioms F` and the entropy-reduction representation, supplies nonnegativity and point-mass zero for `Hfun`. |
| `FiniteHfunBlockEmbeddingInvarianceAssumptions` | Paper-specific bridge, acceptable temporarily but must be proved | Embedding a fibre distribution as a block-supported sigma distribution preserves the constructed `Hfun`. |
| `FiniteCoarseRevealEntropyReductionAssumptions` | Paper-specific/boundary bridge, acceptable temporarily but must be proved | Extends the entropy-reduction identity to the coarse-reveal experiment for arbitrary finite sigma distributions; the current entropy-reduction representation is full-support guarded. |
| `FiniteCardinalSupportBoundaryAssumptions` | Paper-specific boundary/cardinal bridge, acceptable temporarily but must be proved | Single boundary-cardinal extension interface. It bundles boundary normalized-value support restriction, boundary `Hfun =` full-revelation value, and restricted-support coarse-reveal value. The older three helper structures are now derived internally from this one live field. |
| `ClassicalFaddeevTheoremAssumptions` | Classical acceptable external theorem/application | Applies Faddeev's entropy characterization to a regular recursive entropy candidate and returns `Hfun = alpha * Shannon` with `0 ≤ alpha`. |
| `FullSupportMIRepExtendsToBoundary` | Internal target/interface, no longer the public external field | It has the faithful `TraceAxioms F` premise. `FullSupportMIRepExtendsToBoundary_of_supportRestriction` is now proved from `FullSupportBlockMI F`, A5-derived support weak comparisons, A1 transitivity, A3 duplicate-environment coherence, A3 finite-block coherence, and pure MI support invariance. |

## Stage 22 Branch Residual Closure

Stage 22 turns the remaining branch boundary layer into explicit, sharply
named interfaces.

### Boundary Representative Transport

`FiniteSupportFaceRepresentativeConventionAssumptions` is the explicit
support-face representative convention:

- it states that the ambient boundary representative at prior `r` agrees with
  the intrinsic representative at `r.restrictToSupport` after restricting the
  channel to the positive support face;
- it is not a same-posterior-law theorem, because it crosses priors;
- `boundaryValueTransport_of_supportFaceRepresentativeConvention`
  repackages it as the historical
  `FiniteBranchBoundaryValueTransportAssumptions`.

Classification: representative/support-face convention.

### Boundary Coefficient And Linear-Part Transport

`FiniteBoundaryCoefficientScaleConventionAssumptions` is the explicit positive
boundary coefficient choice.  `boundaryFaceScale_of_coefficientScaleConvention`
repackages it as `FiniteBranchBoundaryFaceScaleAssumptions`.

`FiniteBoundaryLinearPartTransportAssumptions` is the exact scalar transport
relation for pushing support-face tangent directions into the ambient prior.
`boundaryCoefficientTransport_of_linearPartTransport` repackages it as the
historical `FiniteBranchBoundaryCoefficientTransportAssumptions`.

Classification: support-face coefficient/scale bridge.  It is the remaining
paper-specific/conventional boundary scalar identification, not broad branch
aggregation.

### Faithful Branch Chain Route

Stage 22 adds:

- `faithfulBranchAggregationStructure_of_components`;
- `faithfulBranchFullSupportScale_of_components`;
- `BranchAggregationChainRule_of_faithful_components`.

These expose the faithful pre-universal route:

1. accepted tangent geometry and same-sign finite linear algebra;
2. support-face representative convention;
3. boundary coefficient/scale transport;
4. singleton/degenerate conventions;
5. public `BranchAggregationStructure`;
6. public `BranchChainStructure`;
7. normalized chain rule through `branchNormalizedValue_seqCompose_of_chain`.

The old `FiniteBranchAggregationAssumptions` remains live in
`SufficiencyExternalAssumptions`, `External/Faddeev.lean`,
`External/EntropyReduction.lean`, and the later scale-coherence compatibility
API.  It is now a downstream compatibility monolith rather than the faithful
proof route.

## Stage 23 Branch Downstream Wiring

Stage 23 adds a public faithful branch API:

- `FiniteFaithfulBranchAggregationAssumptions`;
- `branchPathTangentScalarStructure_of_faithfulAssumptions`;
- `branchAggregationStructure_of_faithfulAssumptions`;
- `branchFullSupportScale_of_faithfulAssumptions`;
- `branchChainStructure_of_faithfulAssumptions`;
- `normalizedChainRule_of_faithfulAssumptions`;
- `SufficiencyFaithfulBranchAssumptions`;
- `SufficiencyFaithfulBranchAssumptions.branchAggregationStructure`;
- `SufficiencyFaithfulBranchAssumptions.branchChainStructure`;
- `SufficiencyFaithfulBranchAssumptions.normalizedChainRule`.

This is a bypass, not a reconstruction, of
`FiniteBranchAggregationAssumptions`.  The old monolith cannot be reconstructed
honestly from faithful components because its `of_A7` field has no slots for
the affine linear-part interface, classical tangent geometry, support-face
representative convention, boundary coefficient/scale transport, or singleton
scale conventions.

The old branch monolith remains in `SufficiencyExternalAssumptions.branch` for
the existing final sufficiency theorem.  The faithful API is now available for
downstream code that needs the branch named result itself rather than the old
all-in-one external sufficiency bundle.

## Stage 24 Branch Named Result Statement

Stage 24 exposes the named result "Branch aggregation, cocycle, and normalised
chain rule" as a faithful public Lean package:

- `BranchAggregationCocycleNormalizedChainRuleStructure`;
- `BranchAggregationCocycleNormalizedChainRuleStructure.chain`;
- `BranchAggregationCocycleNormalizedChainRuleStructure.normalizedChainRule`;
- `BranchAggregationCocycleNormalizedChainRule_of_faithful`.

This package contains:

- the reassembled `BranchAggregationStructure`;
- the public full-support branch coefficient cocycle;
- full-support scale factorization;
- boundary/singleton-extended scale factorization;
- the induced `BranchChainStructure`;
- the normalized chain rule.

The theorem depends on exactly the fields of
`FiniteFaithfulBranchAggregationAssumptions`, namely accepted finite tangent
geometry/linear algebra, support-face representative normalization, boundary
coefficient/scale transport, and singleton/degenerate conventions.  It does
not use `FiniteBranchAggregationAssumptions`.

Residual status after Stage 24, revised by the later tangent-spanning
interface audit:

- `FinitePosteriorTangentSpaceSpanningAssumptions` remains compatibility-only
  and false-too-broad for the current extensional type
  `PosteriorLawSigned A = (Dist A → ℝ) → ℝ`; the moment equations do not imply
  linearity in the test function.
- The faithful replacement is the atomic/linear signed-law interface introduced
  in the tangent-spanning interface revision stage.
- `FiniteLinearFunctionalSameSignScalarOnTangentAssumptions` was formerly
  classified here as accepted classical finite linear algebra; it is now
  discharged internally by `finiteLinearFunctionalSameSignScalarOnTangent_of_direct`.
- `FiniteSupportFaceRepresentativeConventionAssumptions` remains an explicit
  support-face representative normalization convention across priors.
- `FiniteBoundaryCoefficientScaleConventionAssumptions`,
  `FiniteBoundaryLinearPartTransportAssumptions`, and
  `FiniteBranchScaleFactorizationBoundaryTransportAssumptions` remain the
  explicit full-to-face boundary coefficient/scale transport layer.
- `FiniteBranchSingletonScaleConventionAssumptions` and
  `FiniteBranchScaleFactorizationSingletonConvention` remain explicit
  singleton/degenerate conventions; singleton formula contributions are zero.
- No broad branch aggregation, path-independence, formula, cocycle, or chain
  rule gap remains on the faithful route.

Recommended citation for the named result in future Lean development:

`BranchAggregationCocycleNormalizedChainRule_of_faithful`

with the normalized chain rule extracted by:

`BranchAggregationCocycleNormalizedChainRuleStructure.normalizedChainRule`.

## Stage 25 Coherent Relabelling And Face Scales

Stage 25 isolates the named result "Coherent relabelling and face scales" from
the later universal-scale collapse.  The faithful Lean route is:

- `FiniteChainScaleRelabelingAssumptionsFor`;
- `FiniteSupportFaceScaleAssumptionsFor`;
- `CoherentRelabelingFaceScalesStructure`;
- `CoherentRelabelingFaceScales_of_faithfulBranch`;
- `branchNormalizedValue_relabel_eq_of_valueRelabeling_and_faceScales`.

`CoherentRelabelingFaceScalesStructure` extends the Stage 24 faithful branch
package:

- `BranchAggregationCocycleNormalizedChainRule_of_faithful`;
- the induced `BranchChainStructure`;
- the normalized chain rule;
- exact scale invariance under finite action relabelling;
- canonical support-face scale compatibility.

The current support-face statement is the canonical inclusion form using
`supportSubtype r`.  The paper states the same equation for arbitrary
injections; deriving that fully in Lean requires an embedding/relabeling
transport layer beyond the current support-face API.  This is a faithfulness
enhancement, not a broad branch or scale gap.

Residual status:

- `FinitePosteriorValueRelabelingAssumptions` remains a coherent
  representative-choice convention for exact cardinal equality under
  simultaneous action/outcome relabelling.
- `FiniteChainScaleRelabelingAssumptionsFor` is the scale-level relabelling
  normalization for the chosen chain scales.
- `FiniteSupportFaceScaleAssumptionsFor` is the canonical support-face scale
  compatibility convention/bridge.
- The Stage 24 faithful branch residuals remain inherited through
  `FiniteFaithfulBranchAggregationAssumptions`: accepted finite tangent
  geometry/linear algebra, support-face representative normalization, boundary
  coefficient/scale transport, and singleton/degenerate conventions.
- `FiniteScaleCoherenceAssumptions` remains a compatibility monolith for later
  sufficiency code because it also packages the next named result, universal
  scale coherence.  It is not the proof status of this Stage 25 result.

No interaction collapse, entropy reduction, Faddeev, Shannon entropy, mutual
information representation, fixed-environment representation, or final theorem
is used by the faithful Stage 25 result.

## Stage 26 Interaction Collapse And Universal Chain Scale

Stage 26 exposes the named result "Interaction collapse and universal chain
scale" through a faithful pre-entropy route:

- `FiniteProductQuasiAdditivityForFaceScales`;
- `FiniteProductRevelationScaleLinkAssumptionsFor`;
- `FiniteTwoGroupingInteractionCollapseAssumptionsFor`;
- `FiniteUniversalScaleSingletonConventionFor`;
- `scale_eq_of_productRevelation_and_interactionCollapse`;
- `scale_universal_of_productRevelation_and_interactionCollapse`;
- `scaleCoherence_of_faceScales_interactionCollapse`;
- `InteractionCollapseUniversalChainScaleStructure`;
- `InteractionCollapseUniversalChainScaleStructure.product_additivity`;
- `InteractionCollapseUniversalScale_of_faithfulFaceScales`.

The output package contains:

- the Stage 25 face-scale result;
- the product quasi-additivity data and its collapsed interaction coefficient;
- a public `ScaleCoherenceStructure`;
- exact product additivity after `kappa = 0`.

Residual status:

- `FiniteProductQuasiAdditivityForFaceScales` is the coherent product
  quasi-additivity input restated against the pre-universal face-scale package.
  It avoids the older circular signature that required `ScaleCoherenceStructure`
  before proving universal scale.
- `FiniteProductRevelationScaleLinkAssumptionsFor` is paper Step 1, the
  product-revelation link between scales and `Z(q) = 1 + kappa H(q)`.
- `FiniteTwoGroupingInteractionCollapseAssumptionsFor` is paper Step 3, the
  two-grouping conclusion that the product interaction coefficient is zero.
- `FiniteUniversalScaleSingletonConventionFor` extends the nondegenerate
  universal-scale conclusion to singleton/degenerate priors.

The algebra from these interfaces to universal scale and exact product
additivity is internal.  `FiniteScaleCoherenceAssumptions` remains a downstream
compatibility monolith only; it is not used by the faithful Stage 26 theorem.

## Stage 27 Product Interaction Cleanup

Stage 27 sharpens the product/interaction residuals in
`TraceableAgency/External/ScaleCoherence.lean`.

New internal theorems and definitions:

- `prodChannel_idChannel_idChannel_eq_idChannel`;
- `fullRevelationValueForFaceScales_ne_zero_of_A1`;
- `fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity`;
- `FiniteProductRevelationSequentialScaleAssumptionsFor`;
- `productRevelationScaleLink_of_sequentialScale`;
- `productScaleZForFaceScales`;
- `FiniteProductGroupingWeightConstantAssumptionsFor`;
- `twoGroupingInteractionCollapse_of_weightConstant`;
- `InteractionCollapseUniversalScale_of_decomposedProductBridges`.

Residual status after Stage 27:

- `FiniteProductQuasiAdditivityForFaceScales` remains a source-ready coherent
  product quasi-additivity theorem against the faithful pre-universal face-scale
  package.  The older coherent-product package in `EntropyReduction.lean` is
  stated against `ScaleCoherenceStructure`, so using it here would be circular.
- `FiniteProductRevelationScaleLinkAssumptionsFor` is no longer the preferred
  residual.  It is reconstructed from
  `FiniteProductRevelationSequentialScaleAssumptionsFor` plus internal product
  full-revelation algebra and A1 nonzero full revelation.
- `FiniteTwoGroupingInteractionCollapseAssumptionsFor` is no longer the
  preferred residual.  It is reconstructed from
  `FiniteProductGroupingWeightConstantAssumptionsFor` plus internal cancellation
  at a fixed nondegenerate reference prior.
- `FiniteUniversalScaleSingletonConventionFor` remains an explicit
  singleton/degenerate convention.

The remaining external product/interaction content is therefore:

- `FiniteProductQuasiAdditivityForFaceScales`;
- `FiniteProductRevelationSequentialScaleAssumptionsFor`;
- `FiniteProductGroupingWeightConstantAssumptionsFor`;
- `FiniteUniversalScaleSingletonConventionFor`.

No entropy reduction theorem, Faddeev theorem, Shannon entropy theorem, mutual
information representation, fixed-environment representation, or final theorem
is used in the Stage 27 cleanup.

## Stage 28 Product Revelation Sequential Scale Cleanup

Stage 28 sharpens the Step 1 sequential full-revelation bridge.

New interface and reassemblers:

- `FiniteSequentialFullRevelationNormalizedChainAssumptionsFor`;
- `productRevelationSequentialScale_of_normalizedChain`;
- `InteractionCollapseUniversalScale_of_normalizedSequentialProduct`.

`FiniteProductRevelationSequentialScaleAssumptionsFor` is no longer the
preferred residual.  It is reconstructed internally by clearing denominators in
the normalized-chain full-revelation identities:

- reveal the first coordinate and then full-reveal the second coordinate in
  every branch;
- reveal the second coordinate and then full-reveal the first coordinate in
  every branch.

The remaining Step 1 content is now exactly the normalized-chain specialization
and the associated channel/face transport identifying the first-stage coordinate
reveal and branch continuation reveals with `fullRevelationValueForFaceScales`.
This is source-ready and narrower than the previous scale-weighted package.

The remaining external product/interaction content after Stage 28 is:

- `FiniteProductQuasiAdditivityForFaceScales`;
- `FiniteSequentialFullRevelationNormalizedChainAssumptionsFor`;
- `FiniteProductGroupingWeightConstantAssumptionsFor`;
- `FiniteUniversalScaleSingletonConventionFor`.

## Stage 29 Sequential Full-Revelation Normalized Chain Cleanup

Stage 29 sharpens the normalized-chain full-revelation bridge.

New internal channel algebra:

- `outcomeMarginal_productFirstRevealChannel_prodDist`;
- `outcomeMarginal_productSecondRevealChannel_prodDist`.

New sharper transport interfaces:

- `FiniteCoordinateRevealValueTransportAssumptionsFor`;
- `FiniteCoordinateRevealContinuationTransportAssumptionsFor`.

New reassemblers:

- `sequentialFullRevelationNormalizedChain_of_coordinateTransports`;
- `InteractionCollapseUniversalScale_of_coordinateRevealTransports`.

`FiniteSequentialFullRevelationNormalizedChainAssumptionsFor` is no longer the
preferred primitive residual.  It is reconstructed from:

1. coordinate-reveal value/relabeling transport:
   first-coordinate reveal value, second-coordinate reveal value, and swapped
   full-revelation value;
2. continuation support-face/scale transport:
   the weighted normalized continuation sum after revealing one coordinate is
   the full-revelation value of the other coordinate divided by its face scale.

The remaining external product/interaction content after Stage 29 is:

- `FiniteProductQuasiAdditivityForFaceScales`;
- `FiniteCoordinateRevealValueTransportAssumptionsFor`;
- `FiniteCoordinateRevealContinuationTransportAssumptionsFor`;
- `FiniteProductGroupingWeightConstantAssumptionsFor`;
- `FiniteUniversalScaleSingletonConventionFor`.

The two coordinate-reveal interfaces are support-face/relabeling transport
bridges, not pure channel algebra.  They are narrower than the previous
normalized-chain bridge and expose exactly where arbitrary coordinate-face
injections, representative choices, and face scales must be connected.

## Stage Mathlib Same-Sign Scalar Implementation

The tangent-domain same-sign scalar interface is now proved internally:

- `posteriorLawSignedSMul_zero_zero`;
- `posteriorLawLinear_zero_of_smul`;
- `finiteLinearFunctionalSameSignScalarOnTangent_of_direct`.

This discharges:

`FiniteLinearFunctionalSameSignScalarOnTangentAssumptions`

by a direct ratio argument on the custom signed-posterior-law operations
`posteriorLawSignedAdd` and `posteriorLawSignedSMul`.  The proof does not use
mathlib linear-map/submodule wrappers and does not depend on branch aggregation,
entropy reduction, Faddeev, Shannon entropy, mutual information, or the final
theorem.

Residual status update:

- `FiniteLinearFunctionalSameSignScalarOnTangentAssumptions` is internal/proved.
- `FinitePosteriorTangentSpaceSpanningAssumptions` is not a valid classical
  theorem as stated for arbitrary extensional functionals.  It is legacy
  compatibility only.
- `FiniteAtomicPosteriorTangentSpanningAssumptions` and
  `FiniteAtomicLinearPosteriorTangentSpanningAssumptions` are the corrected
  source-ready finite posterior-law tangent spanning interfaces.
- The older all-signed-law `FiniteLinearFunctionalSameSignScalarAssumptions`
  remains a legacy/classical compatibility interface for older paths, but the
  faithful tangent route can use
  `finiteLinearFunctionalSameSignScalarOnTangent_of_direct`.

## Tangent-Spanning Interface Revision

The separate tangent-spanning implementation guide found that the old broad
interface:

```lean
FinitePosteriorTangentSpaceSpanningAssumptions
```

cannot be true for the current extensional type
`PosteriorLawSigned A = (Dist A → ℝ) → ℝ`.  Feasible posterior-law differences
are linear in the test function, while arbitrary functionals satisfying only
zero total mass and zero barycentre need not be linear.

Lean now contains the corrected atomic-linear layer:

- `AtomicPosteriorSignedLaw`;
- `AtomicPosteriorSignedLaw.eval`;
- `AtomicPosteriorSignedLaw.totalMass`;
- `AtomicPosteriorSignedLaw.barycenterCoord`;
- `AtomicPosteriorSignedLaw.variationMass`;
- `AtomicPosteriorSignedLaw.positiveWeight`;
- `AtomicPosteriorSignedLaw.negativeWeight`;
- `AtomicPosteriorSignedLaw.positiveMass`;
- `AtomicPosteriorSignedLaw.negativeMass`;
- `PosteriorLawSigned.AtomicLinear`;
- `AtomicPosteriorProbLaw`;
- `AtomicPosteriorProbLaw.eval`;
- `AtomicPosteriorProbLaw.barycenterCoord`;
- `AtomicPosteriorProbLaw.posteriorProbLawChannel`;
- `AtomicPosteriorProbLaw.experimentOfPosteriorProbLaw`;
- `FiniteAtomicPosteriorTangentSpanningAssumptions`;
- `FiniteAtomicLinearPosteriorTangentSpanningAssumptions`;
- `atomicLinearTangentSpanning_of_atomic`.

Internally proved atomic facts:

- atomic evaluation is linear in test functions;
- zero mass and zero barycentre imply `PosteriorLawTangent` for the atomic
  evaluation;
- displayed positive/negative weights are nonnegative and decompose total mass;
- an atomic posterior probability law with barycentre `r` defines a
  row-stochastic experiment at full-support `r`;
- the realized experiment's outcome marginal is the atomic mass.

Remaining infrastructure-heavy work:

- posterior identity for the realized atomic posterior probability experiment;
- posterior-law integral identity for that experiment;
- positive/negative signed-law decomposition with slack to force barycentre
  equal to an arbitrary full-support prior;
- migration of the faithful branch route from the old broad extensional
  spanning interface to the corrected atomic route.

## Stage 30 Coordinate Reveal Transport Cleanup

The Stage 29 coordinate transport residuals were split further.

Internal channel/posterior algebra:

- `posterior_productFirstRevealChannel_prodDist_of_pos`;
- `posterior_productSecondRevealChannel_prodDist_of_pos`.

The value-transport package

```lean
FiniteCoordinateRevealValueTransportAssumptionsFor
```

is reconstructed from:

- `FiniteCoordinateRevealMarginalValueTransportAssumptionsFor`;
- `FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor`.

The continuation-sum package

```lean
FiniteCoordinateRevealContinuationTransportAssumptionsFor
```

is reconstructed from the pointwise coordinate-face interface:

- `FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor`.

The Stage 30 constructor

```lean
InteractionCollapseUniversalScale_of_coordinateTransportPieces
```

uses these sharper pieces instead of the broader Stage 29 coordinate transport
packages.

Remaining product/interaction residuals after Stage 30:

- `FiniteProductQuasiAdditivityForFaceScales`: source-ready coherent product
  quasi-additivity theorem.
- `FiniteCoordinateRevealMarginalValueTransportAssumptionsFor`: coordinate
  product/no-information value transport.
- `FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor`: product
  full-revelation outcome relabeling transport.
- `FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor`: pointwise
  coordinate-face value and scale transport for continuation branches.
- `FiniteProductGroupingWeightConstantAssumptionsFor`: source-ready Step 3
  grouping bridge.
- `FiniteUniversalScaleSingletonConventionFor`: singleton/degenerate
  convention.

## Stage IC Open Residuals Cleanup

This cleanup did not touch the branch/tangent files.  It worked only in the
interaction-collapse / universal-scale layer.

New internal coordinate marginal transport:

- `outcomeMarginal_prod_id_uninformativeChannelU_prodDist`;
- `outcomeMarginal_prod_uninformativeChannelU_id_prodDist`;
- `posterior_prod_id_uninformativeChannelU_prodDist_of_pos`;
- `posterior_prod_uninformativeChannelU_id_prodDist_of_pos`;
- `samePosteriorLawExp_productFirstReveal_prod_id_uninformativeU`;
- `samePosteriorLawExp_productSecondReveal_prod_uninformativeU_id`;
- `coordinateRevealMarginalValueTransport_of_productQuasiAdditivity`;
- `InteractionCollapseUniversalScale_of_productQuasiAndCoordinatePieces`.

The old Stage 30 residual

```lean
FiniteCoordinateRevealMarginalValueTransportAssumptionsFor
```

is now reconstructed internally from `FiniteProductQuasiAdditivityForFaceScales`,
zero normalization of the uninformative channel, and posterior-law transport.
It is no longer a separate external assumption.

Remaining product/interaction residuals after this cleanup:

- `FiniteProductQuasiAdditivityForFaceScales`: source-ready coherent product
  quasi-additivity theorem.  This is an earlier paper named-result bridge, not
  pure finite channel algebra.
- `FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor`: exact
  value relabeling for swapped product full revelation.  The current
  `CoherentRelabelingFaceScalesStructure` carries scale relabeling but not the
  cardinal value relabeling field needed to prove this directly.
- `FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor`: pointwise
  coordinate-face continuation transport.  This is the arbitrary
  coordinate-face value/scale transport enhancement beyond the canonical
  support-face equation currently exposed in Lean.
- `FiniteProductGroupingWeightConstantAssumptionsFor`: source-ready Step 3
  grouping bridge.  The algebra from constant `Z` to `kappa = 0` is internal in
  `twoGroupingInteractionCollapse_of_weightConstant`; the remaining content is
  deriving `Z_eq_one_of_nondegenerate` from the paper's two-grouping equation.
- `FiniteUniversalScaleSingletonConventionFor`: singleton/degenerate scale
  convention.

## Stage IC All-Residuals Cleanup

The all-residuals cleanup further reduced the coordinate-transport surface.

New internal swap/full-revelation transport:

- `outcomeMarginal_productSwapRevealChannel_prodDist`;
- `posterior_productSwapRevealChannel_prodDist_of_pos`;
- `samePosteriorLawExp_productSwapReveal_idChannel_of_fullSupport`;
- `coordinateSwapFullRevelationValueTransport_of_posteriorLaw`.

The old residual

```lean
FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor
```

is now internal/proved.

The pointwise coordinate branch-continuation residual

```lean
FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor
```

is reconstructed from the sharper coordinate support-face pieces:

- `FiniteCoordinateSupportFaceValueTransportAssumptionsFor`;
- `FiniteCoordinateSupportFaceScaleTransportAssumptionsFor`;
- `coordinateRevealBranchContinuationTransport_of_coordinateSupportFaceTransports`.

The current smallest faithful interaction-collapse constructor is:

```lean
InteractionCollapseUniversalScale_of_minimalResiduals
```

Remaining non-convention product/interaction residuals:

- `FiniteProductQuasiAdditivityForFaceScales`: source-ready coherent product
  quasi-additivity theorem against `CoherentRelabelingFaceScalesStructure`.
  The old `FiniteCoherentProductQuasiAdditivityAssumptions` route is packaged
  over `ScaleCoherenceStructure`, so using it here would be circular.
- `FiniteCoordinateSupportFaceValueTransportAssumptionsFor`: coordinate-face
  representative transport from ambient product boundary faces to intrinsic
  coordinate action sets.
- `FiniteCoordinateSupportFaceScaleTransportAssumptionsFor`: coordinate-face
  chain-scale transport from ambient product boundary faces to intrinsic
  coordinate action sets.
- `FiniteProductGroupingWeightConstantAssumptionsFor`: source-ready Step 3
  grouping bridge.  The final algebra from `Z(q)=1` to `kappa=0` remains
  internal in `twoGroupingInteractionCollapse_of_weightConstant`; the remaining
  content is the finite partition/disjoint-union grouping weight equation.

Convention:

- `FiniteUniversalScaleSingletonConventionFor`: singleton/degenerate scale
  convention.

## Stage PQA Face-Scale Product Quasi-Additivity Port

The product quasi-additivity residual for interaction collapse was ported to
the non-circular face-scale component route.

New face-scale product component interfaces:

- `FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor`;
- `FiniteFaceScaleProductGaugeNormalizationAssumptionsFor`;
- `FiniteFaceScaleProductInteractionUniversalityAssumptionsFor`.

New internal reassembler:

- `productQuasiAdditivityForFaceScales_of_components`.

New interaction-collapse constructor:

- `InteractionCollapseUniversalScale_of_productComponents`.

The old Stage 10 coherent-product route remains over
`ScaleCoherenceStructure`; using it upstream of interaction collapse would be
circular.  The face-scale route avoids `ScaleCoherenceStructure` and
`FiniteScaleCoherenceAssumptions` as inputs.

`FiniteProductQuasiAdditivityForFaceScales` is no longer the primitive
residual when the component route is used.  The remaining source-ready product
pieces are:

- face-scale pairwise product bilinearity;
- face-scale gauge normalization;
- face-scale interaction universality.

These are substantive product theorem pieces, not conventions.

## Stage IC Final Residuals Attack

The final interaction-collapse residual pass added a more precise constructor:

```lean
InteractionCollapseUniversalScale_of_finalComponents
```

New decompositions:

- `FiniteFaceScaleProductPairwiseBilinearityAssumptionsFor` is reconstructed
  from:
  - `FiniteFaceScaleProductLeftSliceAffineAssumptionsFor`;
  - `FiniteFaceScaleProductSliceInterceptAssumptionsFor`;
  - `FiniteFaceScaleProductSliceSlopeAssumptionsFor`;
  - `faceScaleProductPairwiseBilinearity_of_sliceAffine`.
- `FiniteFaceScaleProductGaugeNormalizationAssumptionsFor` is reconstructed
  from the explicit convention:
  - `FiniteFaceScaleProductGaugeConventionFor`;
  - `faceScaleProductGaugeNormalization_of_convention`.
- `FiniteFaceScaleProductInteractionUniversalityAssumptionsFor` is
  reconstructed from:
  - `FiniteFaceScaleProductInteractionAssociativityAssumptionsFor`;
  - `FiniteFaceScaleSingletonInteractionConventionFor`;
  - `faceScaleProductInteractionUniversality_of_parts`.
- `FiniteCoordinateSupportFaceValueTransportAssumptionsFor` is reconstructed
  from:
  - `FiniteCoordinateSupportFaceValueConventionFor`;
  - `coordinateSupportFaceValueTransport_of_convention`.
- `FiniteCoordinateSupportFaceScaleTransportAssumptionsFor` is reconstructed
  from:
  - `FiniteCoordinateSupportFaceScaleConventionFor`;
  - `coordinateSupportFaceScaleTransport_of_convention`.

Remaining source-ready theorem pieces:

- `FiniteFaceScaleProductLeftSliceAffineAssumptionsFor`;
- `FiniteFaceScaleProductSliceInterceptAssumptionsFor`;
- `FiniteFaceScaleProductSliceSlopeAssumptionsFor`;
- `FiniteFaceScaleProductInteractionAssociativityAssumptionsFor`;
- `FiniteProductGroupingWeightConstantAssumptionsFor`.

Remaining conventions:

- `FiniteFaceScaleProductGaugeConventionFor`;
- `FiniteFaceScaleSingletonInteractionConventionFor`;
- `FiniteCoordinateSupportFaceValueConventionFor`;
- `FiniteCoordinateSupportFaceScaleConventionFor`;
- `FiniteUniversalScaleSingletonConventionFor`.

No broad interaction-collapse or universal-scale residual remains.  The
remaining theorem pieces are localized product-coordinate, product-interaction,
and finite grouping subclaims.

## Stage IC Multi Residual Closure

The interaction-collapse / universal-chain-scale layer was further decomposed
and reassembled by:

```lean
InteractionCollapseUniversalScale_of_multiClosedComponents
```

This constructor replaces the broader current product inputs with multi-stage
source-ready pieces.

### Newly internal/reconstructed

- `FiniteFaceScaleProductLeftSliceAffineAssumptionsFor` is reconstructed from:
  - `FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor`;
  - `faceScaleProductLeftSliceAffine_of_transform`.
- `FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor` is
  reconstructed from:
  - `FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor`;
  - `FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor`;
  - `FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor`;
  - `FiniteFaceScaleBaseValueNonconstancyAssumptionsFor`;
  - `FiniteFaceScaleSingletonSliceAffineConventionFor`;
  - `ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor`;
  - `faceScaleProductLeftSliceAffineTransform_of_parts`.
- `FiniteFaceScaleBaseValueNonconstancyAssumptionsFor` is internally proved by:
  - `faceScaleBaseValueNonconstancy_of_A1`.
- `FiniteFaceScaleProductSliceInterceptAssumptionsFor` is reconstructed from:
  - `FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor`;
  - `faceScaleProductSliceIntercept_of_positiveLinear`.
- `FiniteFaceScaleProductInterceptPositiveLinearAssumptionsFor` is
  reconstructed from:
  - `FiniteFaceScaleProductInterceptSameOrderAssumptionsFor`;
  - `FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor`;
  - `FiniteFaceScaleProductInterceptZeroAssumptionsFor`;
  - `ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor`;
  - `faceScaleProductInterceptPositiveLinear_of_parts`.
- `FiniteFaceScaleProductSliceSlopeAssumptionsFor` is reconstructed from:
  - `FiniteFaceScaleProductSlopeAffineAssumptionsFor`;
  - `faceScaleProductSliceSlope_of_slopeAffine`.
- `FiniteFaceScaleProductInteractionAssociativityAssumptionsFor` is
  reconstructed from:
  - `FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor`;
  - `FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor`;
  - `faceScaleProductInteractionAssociativity_of_coeffExtraction`.
- `FiniteProductGroupingWeightConstantAssumptionsFor` is reconstructed from:
  - `FiniteProductGroupingReferenceWeightAssumptionsFor`;
  - `productGroupingWeightConstant_of_reference`.

### Remaining source-ready theorem pieces

- `FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor`;
- `FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor`;
- `FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor`;
- `ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor`;
- `FiniteFaceScaleProductInterceptSameOrderAssumptionsFor`;
- `FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor`;
- `FiniteFaceScaleProductInterceptZeroAssumptionsFor`;
- `ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor`;
- `FiniteFaceScaleProductSlopeAffineAssumptionsFor`;
- `FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor`;
- `FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor`;
- `FiniteProductGroupingReferenceWeightAssumptionsFor`.

### Remaining conventions

- `FiniteFaceScaleProductGaugeConventionFor`;
- `FiniteFaceScaleSingletonInteractionConventionFor`;
- `FiniteCoordinateSupportFaceValueConventionFor`;
- `FiniteCoordinateSupportFaceScaleConventionFor`;
- `FiniteUniversalScaleSingletonConventionFor`;
- `FiniteFaceScaleSingletonSliceAffineConventionFor`.

No broad interaction-collapse residual remains.  The remaining items are
localized theorem pieces or explicit gauge/representative/singleton
conventions.

## Main Theorem Dependency

`MainCharacterizationWithMoreover_of_external_assumptions` still proves the
paper theorem only modulo explicit assumptions:

- `SufficiencyExternalAssumptions`, now containing finite Blackwell
  same-posterior-law mutual garbling, Herstein-Milnor, branch aggregation,
  scale coherence, coherent-product cross-prior content, entropy regularity,
  Hfun block-embedding invariance, coarse-reveal entropy reduction, cardinal
  support boundary extension, and classical Faddeev.
- `FiniteDPIAssumptions` for the benchmark direction.

The remaining paper-specific assumptions are not classical imports. They are
named interfaces for future Lean proofs of the paper's bridge lemmas.

## Stage BNE — Non-Convention Externals in the Faithful Branch Route

The two non-convention external fields in `FiniteFaithfulBranchAggregationAssumptions`
are now explicitly documented and classified.

### FiniteAffineLinearPartAssumptions

**Classification: EXTERNAL_MATHEMATICAL_THEOREM**

This packages the integral representation of the affine posterior value functional
`V q` and its extension to the full signed-law tangent space.  Given the Herstein-Milnor
output, there exists a marginal value function `φ_q : Dist A → ℝ` such that
`V q E = posteriorLawIntegral q E.channel φ_q`, and the linear part is
`linearPart q η := η(φ_q)`.  This satisfies all fields of the structure:

- `value_difference`: `V q E - V q E' = posteriorLawDifferenceExp q E E' (φ_q) = linearPart q (μ_E - μ_{E'})`
- `linearPart_ext`: extensionality of η as a functional
- `linearPart_add`, `linearPart_smul`: linearity of η in the signed-law argument

**Paper citation**: Lemma postsep (lines 1000-1196).  The integral form follows
immediately from the affinity of F_q on the finite probability simplex M_q.

**Status**: external assumption awaiting formalization of the Herstein-Milnor
integral representation in Lean.  To internalize, extend `FiniteHersteinMilnorAssumptions`
with a `marginalValue` field and the integral form equation, then construct
`FiniteAffineLinearPartAssumptions` via `linearPart q η := η (marginalValue q)`.

**Note**: `FiniteLinearFunctionalSameSignScalarOnTangentAssumptions` (previously also
external) is now internally proved by `finiteLinearFunctionalSameSignScalarOnTangent_of_direct`.

### FiniteBoundaryLinearPartTransportAssumptions

**Classification: EXTERNAL_MATHEMATICAL_THEOREM**

Given the integral representation `linearPart q ζ = ζ(φ_q)`, this asserts:
```
φ_q ∘ supportIncludeKernel r = boundaryCoeff(q,r) * φ_{r.restrictToSupport}
```
as functions on `supportSubtype r`, for boundary priors `r` (not full support).

This is the restriction of the ambient marginal value function to the positive
support face, which must be a positive scalar multiple of the intrinsic face marginal
value function.  It follows from the boundary branch aggregation formula: the value
of a face-supported continuation experiment at the ambient boundary prior `r` must
equal `boundaryCoeff(q,r)` times the value at the restricted face prior `r.restrictToSupport`.

**Paper citation**: boundary layer of the branch aggregation formula and support
restriction (`lem:supprestrict`).

**Status**: external assumption awaiting connection between the branch aggregation
formula and the integral representation.  It depends on `FiniteAffineLinearPartAssumptions`
being formalized first.

**Note**: this is NOT a convention choice.  The positive boundary coefficient
`boundaryCoeff(q,r)` is separately chosen by `FiniteBoundaryCoefficientScaleConventionAssumptions`
(a convention).  Given that choice, the transport equation is a theorem.

### Unchanged from prior stage

The following fields of `FiniteFaithfulBranchAggregationAssumptions` are unchanged:

| Field | Status |
|-------|--------|
| `tangent_spanning` | **Internally proved** via `atomicLinearTangentSpanning_of_atomic finiteAtomicPosteriorTangentSpanning` |
| `same_sign_scalar` | **Internally proved** via `finiteLinearFunctionalSameSignScalarOnTangent_of_direct` |
| `support_face_rep` | Convention: explicit representative normalization across priors |
| `boundary_coeff_scale` | Convention: free choice of positive `boundaryCoeff(q,r)` |
| `singleton_scale` | Convention: explicit singleton scale for degenerate priors |

Stage 24/25/26 faithful theorems still depend only on `[propext, Classical.choice, Quot.sound]`.

## Stage IC Externals Closure

This stage targeted the twelve localized theorem pieces left by the
interaction-collapse decomposition.  It did not introduce any new local
external interfaces.

### Eliminated previous externals

- `FiniteFaceScaleProductInterceptZeroAssumptionsFor` is internal via
  `faceScaleProductInterceptZero_of_sliceAffine`.  The proof uses the
  left-slice affine identity at the no-information first-coordinate channel and
  `V_eq_zero_of_subsingleton_outcome`.
- `ClassicalFaceScaleAffineUtilityUniquenessAssumptionsFor` is no longer a
  separate face-scale external.  It is reconstructed from the single generic
  source-ready theorem `ClassicalFiniteAffineUtilityUniquenessAssumptions` by
  `classicalFaceScaleAffineUtilityUniqueness_of_finiteAffineUtility`.
- `FiniteFaceScaleTripleProductValueAssociativityAssumptionsFor` is internal
  relative to exact posterior-value relabeling:
  `faceScaleTripleProductValueAssociativity_of_valueRelabeling`.

### Collapsed assumptions

- `ClassicalFiniteAffineUtilityUniquenessAssumptions` is the single classical
  finite affine-utility uniqueness interface replacing the first-coordinate
  face-scale uniqueness package.
- `FinitePosteriorValueRelabelingAssumptions` is the exact relabeling
  representative interface used to derive triple-product value associativity.

### Remaining source-ready theorem pieces

- `FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor`;
- `FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor`;
- `FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor`;
- `FiniteFaceScaleProductInterceptSameOrderAssumptionsFor`;
- `FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor`;
- `ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor`;
- `FiniteFaceScaleProductSlopeAffineAssumptionsFor`;
- `FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor`;
- `FiniteProductGroupingReferenceWeightAssumptionsFor`.

### Remaining conventions

- `FiniteFaceScaleProductGaugeConventionFor`;
- `FiniteFaceScaleSingletonInteractionConventionFor`;
- `FiniteCoordinateSupportFaceValueConventionFor`;
- `FiniteCoordinateSupportFaceScaleConventionFor`;
- `FiniteUniversalScaleSingletonConventionFor`;
- `FiniteFaceScaleSingletonSliceAffineConventionFor`.

### Current constructor

The cleanest interaction-collapse constructor after this closure pass is:

`InteractionCollapseUniversalScale_of_closedLocalTheorems`.

It avoids the old `FiniteScaleCoherenceAssumptions` monolith and does not use
entropy reduction, Faddeev, Shannon entropy, mutual information representation,
the fixed-environment final representation, or the final theorem.

## Stage IC Total Closure

The nine remaining local theorem externals from Stage IC Externals Closure are
no longer exposed by the strict interaction-collapse API.  They are reconstructed
from two family-level theorem assumptions:

- `FiniteFaceScaleProductRepresentationTheoremAssumptionsFor`
- `FiniteProductGroupingEquationAssumptionsFor`

The strict constructor is:

`InteractionCollapseUniversalScale_of_totalClosure`.

It still takes the pre-existing global assumptions:

- `ClassicalFiniteAffineUtilityUniquenessAssumptions`
- `FinitePosteriorValueRelabelingAssumptions`

and the already accepted conventions:

- `FiniteFaceScaleProductGaugeConventionFor`
- `FiniteFaceScaleSingletonInteractionConventionFor`
- `FiniteCoordinateSupportFaceValueConventionFor`
- `FiniteCoordinateSupportFaceScaleConventionFor`
- `FiniteUniversalScaleSingletonConventionFor`
- `FiniteFaceScaleSingletonSliceAffineConventionFor`

### Original local theorem externals reconstructed

- `FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor`
- `FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor`
- `FiniteFaceScaleProductLeftSliceSameOrderAssumptionsFor`
- `FiniteFaceScaleProductInterceptSameOrderAssumptionsFor`
- `FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor`
- `ClassicalFaceScaleSecondCoordinateAffineUniquenessAssumptionsFor`
- `FiniteFaceScaleProductSlopeAffineAssumptionsFor`
- `FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor`
- `FiniteProductGroupingReferenceWeightAssumptionsFor`

### Remaining global theorem assumptions

- `FiniteFaceScaleProductRepresentationTheoremAssumptionsFor`: coherent
  product representation theorem for public-mix affinity, same-order transport,
  second-coordinate intercept/slope affine uniqueness, and triple coefficient
  extraction.
- `FiniteProductGroupingEquationAssumptionsFor`: finite grouping equation
  theorem yielding the reference-weight package for any product quasi-additivity
  structure.

No additional local ad hoc interfaces were introduced.

## Stage IC Full Product Theorems Attempt

The strict request was to prove:

- `FiniteFaceScaleProductRepresentationTheoremAssumptionsFor`
- `FiniteProductGroupingEquationAssumptionsFor`

without replacing them by further theorem-shaped assumptions.

Result: neither theorem is discharged in this run.

Reason:

- `FiniteFaceScaleProductRepresentationTheoremAssumptionsFor` needs upstream
  HM/posterior-law value affinity and A8/product-coordinate same-order
  transport.  `PosteriorValueRepresentation` does not contain public-mix
  affinity, and the old Stage 10 route explicitly introduced
  `FinitePosteriorLawValueAffineAssumptions` downstream in
  `EntropyReduction.lean`.
- `FiniteProductGroupingEquationAssumptionsFor` needs the finite
  partition/disjoint-union grouping equation.  The project currently has the
  algebra after the reference-weight package, but not the finite grouping
  construction that derives it.

No new local IC theorem external was added.  The blocker is recorded in:

`MISSING_AXIOM_CERTIFICATE.md`.

Current strictest constructor remains:

`InteractionCollapseUniversalScale_of_totalClosure`.

## Stage HM Formalization

The Herstein--Milnor bottleneck is now represented by one global finite
mixture-space theorem interface:

- `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions`

It is global, not branch-specific and not IC-specific.  It supplies:

- `FinitePosteriorLawValueAffineAssumptions`
- `FinitePosteriorIntegralRepresentationAssumptions`

New internal reassemblers:

- `finitePosteriorLawValueAffine_of_HM`
- `finitePosteriorIntegralRepresentation_of_HM`
- `finiteAffineLinearPartAssumptions_of_integralRepresentation`
- `finiteAffineLinearPartAssumptions_of_HM`
- `faceScaleBaseValuePublicMixAffinity_of_HM`
- `faceScaleProductCoordinateMixtureAffinity_of_HM`
- `faceScaleProductInterceptPublicMixAffinity_of_HM`

Consequences:

- `FiniteAffineLinearPartAssumptions` is no longer a branch-local HM external
  once the global HM theorem is supplied.
- The IC public-mix fields
  `FiniteFaceScaleBaseValuePublicMixAffinityAssumptionsFor`,
  `FiniteFaceScaleProductCoordinateMixtureAffinityAssumptionsFor`, and
  `FiniteFaceScaleProductInterceptPublicMixAffinityAssumptionsFor` are no
  longer IC-specific theorem externals once the global HM theorem is supplied.

Remaining HM-adjacent residual:

- `FiniteBoundaryLinearPartTransportAssumptions`: after integral
  representation, this is support-face test-function transport, not a basic
  HM existence theorem.

Remaining non-HM product residuals:

- product-coordinate same-order transport;
- triple-product coefficient extraction/product representation components not
  implied by public-mix affinity alone;
- finite product grouping equation.

The full Herstein--Milnor theorem was not proved from first principles in Lean.
The blocker and exact theorem shape are recorded in:

`STAGE_HM_FORMALIZATION_BLOCKER_CERTIFICATE.md`.

## Stage Post-HM Downstream Closure Update

The global Herstein--Milnor interface remains:

- `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions`

New post-HM downstream closures:

- `FiniteSupportFaceMarginalValueTransportConvention` is an explicit
  support-face marginal-value representative normalisation.  It states the
  actual test-function transport left after HM:
  `φ_q` restricted to the support face equals
  `boundaryCoeff(q,r) * φ_{r.restrictToSupport}` as evaluated by
  support-face tangent signed laws.
- `boundaryLinearPartTransport_of_integralRepresentation` reconstructs
  `FiniteBoundaryLinearPartTransportAssumptions` from
  `FinitePosteriorIntegralRepresentationAssumptions` plus that convention.
- `faceScaleProductLeftSliceSameOrder_of_A8` and
  `faceScaleProductInterceptSameOrder_of_A8` close the face-scale
  product-coordinate same-order fields from A8/product-lift order transport
  without using `ScaleCoherenceStructure`.
- `finiteFaceScaleProductRepresentationTheorem_of_HM` reconstructs
  `FiniteFaceScaleProductRepresentationTheoremAssumptionsFor` from HM-provided
  public-mix fields, A8 same-order fields, and the remaining non-HM product
  theorem pieces.

Remaining branch-side post-HM item:

- `FiniteSupportFaceMarginalValueTransportConvention`: classification
  SUPPORT_FACE_REPRESENTATIVE_NORMALISATION.  It is narrower than the old
  generic boundary linear-part theorem and is the exact residual after the HM
  integral representation.

Remaining IC-side theorem pieces:

- product representation is no longer blocked by public-mix affinity or
  product-coordinate same-order.  The remaining product theorem content is
  second-coordinate affine uniqueness/slope affine identification and
  triple-product coefficient extraction.
- `FiniteProductGroupingEquationAssumptionsFor` remains the single finite
  partition/disjoint-union grouping theorem.  HM does not address it.

## Stage Post-HM Final Product Blocks

The final product-block closure pass attacked all three remaining non-HM IC
blocks:

- second-coordinate affine uniqueness / slope identification;
- triple-product coefficient extraction;
- finite grouping equation.

No new local theorem-shaped assumptions were introduced.

Remaining family-level theorem assumptions:

- `FiniteFaceScaleProductRepresentationTheoremAssumptionsFor`: still contains
  the coherent product-coefficient content not discharged by HM/A8, namely
  second-coordinate intercept positive-linearity, slope identification, and
  triple-product coefficient extraction.
- `FiniteProductGroupingEquationAssumptionsFor`: still contains the finite
  partition/disjoint-union grouping equation needed to derive the reference
  weight.

Conventions remain explicit and unchanged:

- `FiniteSupportFaceMarginalValueTransportConvention`;
- `FiniteFaceScaleProductGaugeConventionFor`;
- `FiniteFaceScaleSingletonInteractionConventionFor`;
- `FiniteCoordinateSupportFaceValueConventionFor`;
- `FiniteCoordinateSupportFaceScaleConventionFor`;
- `FiniteUniversalScaleSingletonConventionFor`;
- `FiniteFaceScaleSingletonSliceAffineConventionFor`.

Strictest constructor remains:

- `InteractionCollapseUniversalScale_of_totalClosure`.

## Stage Product Proof Or Counterexample Update

The adversarial product proof audit produced five agent-style audits and a
coordinated verdict:

- `STAGE_PRODUCT_AGENT1_TEX_PROOF_RECONSTRUCTION_AUDIT.md`
- `STAGE_PRODUCT_AGENT2_LEAN_STATEMENT_AUDIT.md`
- `STAGE_PRODUCT_AGENT3_PROOF_ATTEMPT_AUDIT.md`
- `STAGE_PRODUCT_AGENT4_COUNTEREXAMPLE_AUDIT.md`
- `STAGE_PRODUCT_AGENT5_REPAIR_AND_AXIOM_MINIMIZATION_AUDIT.md`
- `STAGE_PRODUCT_COORDINATED_VERDICT.md`

New internal product algebra:

- `faceScaleProductPairBilinear_normalized`
- `faceScaleTripleProductCoeffExtraction_of_valueAssociativity`

New post-HM product wrapper:

- `finiteFaceScaleProductRepresentationTheorem_of_HM_and_coeffExtraction`

Classification changes:

- `FiniteFaceScaleTripleProductCoeffExtractionAssumptionsFor` is no longer an
  IC theorem external when triple-product value associativity is available; it
  is discharged internally by
  `faceScaleTripleProductCoeffExtraction_of_valueAssociativity`.
- `FiniteFaceScaleProductRepresentationTheoremAssumptionsFor` is narrowed:
  HM closes public-mix fields, A8 closes same-order fields, and coefficient
  extraction is internal.  The remaining product content is coherent
  second-coordinate/slope identification over the selected face-scale
  representatives.
- `FiniteProductGroupingEquationAssumptionsFor` remains the exact missing
  finite partition/disjoint-union grouping theorem.  It is not implied by HM,
  A8, product quasi-additivity, or representative conventions alone.

No complete global counterexample was constructed, but the finite-algebra
counterexample audit shows why the remaining slope and grouping conclusions are
not consequences of the weaker local ingredients alone.

## Stage Product Final Two Gaps Update

Final statuses:

- right-slice coefficient-selection / slope identification:
  `MISSING_AXIOM_REQUIRED`;
- finite partition/disjoint-union grouping equation:
  `MISSING_AXIOM_REQUIRED`.

Exact missing product/grouping theorem names:

- `FiniteRightSliceCoefficientSelectionAssumptionsFor`;
- `FiniteProductGroupingEquationAssumptionsFor`.

The slope theorem is not supplied by HM public-mix affinity plus A8 same-order
alone.  A right-slice affine representative can be obtained informally, but
Lean still needs a theorem that its selected positive coefficient is the same
coefficient used by `hslice.leftSliceSlope`, and singleton/value-constant
second-coordinate domains need an explicit selected-slope convention.

The grouping theorem is not supplied by product quasi-additivity or
representative conventions.  The local product algebra permits nonzero
`kappa`, hence nonconstant `Z(q)=1+kappa H(q)`, until the finite
partition/disjoint-union grouping equation is imposed.

No complete global counterexample was constructed.  The identified finite
algebra models are independence diagnostics supporting the missing-axiom
classification.

---

## Final Repair Stage — Relabeling + Grouping (post-Fable)

### 1. Relabeling invariance status

- ORDER level: PROVED from A3/A4/A5/A1 (`relabel_rel_of_axioms`,
  `finiteRelabelingInvariance_of_axioms`, `External/Relabeling.lean`).  Two-sided
  DPI, exactly the paper's argument.  No relabeling axiom missing at order level.
- VALUE level (`FinitePosteriorValueRelabelingAssumptions`, over a bare
  `PosteriorValueRepresentation`): remains an assumption.  Its residual content
  is purely CARDINAL (the relabeling scalar `c = 1`).  Blocked because the only
  cross-prior value bridge requires product quasi-additivity, and using `hprod`
  is circular (`hprod` is built via `faceScaleTripleProductValueAssociativity_of_valueRelabeling`,
  which consumes `hrelV`).  Classification: global cardinal coherence assumption
  for the chosen representatives (order part discharged).

### 2. Two-grouping evaluations E1/E2 status

`FiniteProductTwoGroupingWeightEquationAssumptionsFor`: remains the honest,
faithful, non-vacuous product-grouping primitive.  Blocked from full proof by
the pre-universal grouping recursion (block bridge + branch formula + neutrality
over `sigmaDist`), which is only formalized at the forbidden
`EntropyReductionRepresentation` (universal-scale) layer.

### 3. POS status

`FiniteProductScaleZPositiveAssumptionsFor`: classified as the paper's
positive-slice-slope / positive-scale condition.  Enabling lemma
`faceScaleAffineSliceTransformSlope_pos` proved (`0 < slice slope`).  Not
derivable for a generic abstract `hprod` (abstract `κ`); derivable in principle
for the concrete product-representation `hprod`.

### 4. Exact remaining assumptions (final constructor
`InteractionCollapseUniversalScale_of_fableProductClosure`)

- Global classical: `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions`,
  `ClassicalFiniteAffineUtilityUniquenessAssumptions`.
- Global cardinal coherence: `FinitePosteriorValueRelabelingAssumptions`
  (order part now proved; cardinal part remains).
- Product/grouping primitives: `FiniteProductTwoGroupingWeightEquationAssumptionsFor`
  (E1/E2), `FiniteProductScaleZPositiveAssumptionsFor` (POS).
- Conventions: gauge, singleton-interaction, coordinate-support face
  value/scale, universal-scale singleton, singleton slice-affine.

### 5. Conventions: unchanged (see above list).

### 6. Recommended TeX changes

- State the value-level relabeling as: order invariance (A4/A5 DPI) +
  Corollary permutationinvariance scalar-pinning `c = 1` (Lemma actionbase +
  reference-prior product).  Only the latter is not yet formalizable at the bare
  representation layer.
- State POS as the positive-slice-slope consequence `α(ν) > 0`.
- State the two-grouping evaluations E1/E2 as the named grouping equation, with
  the pre-universal block-bridge grouping recursion as the remaining input.

---

## Targeted Closure Stage (post-Final-Repair)

### 1. Order-level relabeling

PROVED from A3/A4/A5/A1 two-sided DPI (`relabel_rel_of_axioms`,
`finiteRelabelingInvariance_of_axioms`).  Unchanged.

### 2. Value-level relabeling cardinal status

`FinitePosteriorValueRelabelingAssumptions` remains:
`GLOBAL_CARDINAL_NORMALIZATION_REQUIRED`.  Residual = the paper's Corollary
permutationinvariance scalar pinning `c = 1`.  A non-circular derivation path
was identified (swap-free Step-2 slope + strict-product/associator-only value
convention + Lean actionbase + permutationinvariance from product QA) but not
executed; see `STAGE_FINAL_A_CARDINAL_RELABELING_BRIDGE_AUDIT.md`.

### 3. Pre-universal grouping recursion status

The E1/E2 two-grouping target is REPAIRED and DERIVED: 
`finiteProductTwoGroupingWeightEquation_of_weightRecursion` proves E1/E2 from
the sharper `FinitePreUniversalGroupingWeightRecursionAssumptionsFor` — the
paper's weight equation (W) over `sigmaDist` partitions, stated pre-universally.
(W) is now the sole remaining product-grouping primitive:
`PRE_UNIVERSAL_GROUPING_RECURSION_REQUIRED`.  Supporting proved lemmas:
`sigmaDist_fullSupport`, `twoGroupingReassoc` relabeling transport,
reference-prior arithmetic, sigma/product nonsubsingleton lemmas.

### 4. Concrete POS status

PROVED (`productScaleZpositive_of_sliceTransform`), for ANY product
quasi-additivity package given the slice-affine transform: `Z(q)` is identified
with the calibrated slice-transform slope
(`productScaleZForFaceScales_eq_sliceTransformSlope`), which is the positive
multiplier of a positive affine transform
(`faceScaleAffineSliceTransformSlope_pos`).  POS is removed from the final
constructor.

### 5. Exact remaining assumptions
(final constructor `InteractionCollapseUniversalScale_of_targetedFinalClosure`)

- Global classical: `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions`,
  `ClassicalFiniteAffineUtilityUniquenessAssumptions`.
- Global cardinal coherence: `FinitePosteriorValueRelabelingAssumptions`.
- Product/grouping primitive: `FinitePreUniversalGroupingWeightRecursionAssumptionsFor`
  (paper eq. (W)).
- Conventions: gauge, singleton-interaction, coordinate-support face
  value/scale, universal-scale singleton, singleton slice-affine.

### 6. TeX changes needed

- State Lemma actionbase and Corollary permutationinvariance as the named
  cardinal relabeling chain (order DPI ⟹ scalar; product normalisation ⟹
  `c = 1`).
- State the weight equation (W) as a named pre-universal lemma (before
  entropy/Faddeev), noting E1/E2 and POS are consequences (now formalized as
  `finiteProductTwoGroupingWeightEquation_of_weightRecursion` and
  `productScaleZpositive_of_sliceTransform`).

---

## Codex Parallel Cardinal/Recursion Pass

### 1. Value-level relabeling

Status: `GLOBAL_CARDINAL_NORMALIZATION_REQUIRED`.

The order-level relabeling theorem remains proved:
`relabel_rel_of_axioms` / `finiteRelabelingInvariance_of_axioms`.  This pass did
not prove `FinitePosteriorValueRelabelingAssumptions`.  The current public
target quantifies over every bare `PosteriorValueRepresentation F`; that target
is stronger than the TeX product-normalization route, because type-dependent
positive rescalings preserve the bare representation fields but break exact
cross-type cardinal equality.  The faithful theorem to prove next is therefore
for the selected coherent face-scale representatives: actionbase scalar from
order relabeling + HM/affine uniqueness, then Corollary permutationinvariance
`c = 1` from a non-circular product QA.

No `FiniteStrictProductValueConventionFor`, swap-free slope theorem, actionbase
scalar theorem, or permutationinvariance scalar-pinning theorem was added in
this pass.

### 2. Pre-universal grouping recursion

Status: `PRE_UNIVERSAL_GROUPING_RECURSION_REQUIRED`.

The repaired E1/E2 target remains derived in Lean from `(W)` by
`finiteProductTwoGroupingWeightEquation_of_weightRecursion`, and the
family-level grouping equation remains derived by
`finiteProductGroupingEquation_of_weightRecursion`.  This pass did not prove
`FinitePreUniversalGroupingWeightRecursionAssumptionsFor`.

The missing pre-universal bridge is the block-reveal value identity at the
face-scale layer:

```text
V_q(G_partition) = fullRevelationValueForFaceScales hfaces p
```

The assembled coarse-reveal recursion exists downstream in `Faddeev.lean`
through `CrossPriorBlockRepresentation` and `EntropyReductionRepresentation`.
The available unscaled block bridge
`unscaled_cross_prior_block_rep_of_product_parts` is typed against
`ScaleCoherenceStructure F`, which is the later universal-scale conclusion and
cannot be used to prove `(W)` non-circularly.

### 3. POS

Status: `PROVED_IN_LEAN`.

Unchanged from the targeted closure stage.  POS is discharged by
`productScaleZForFaceScales_eq_sliceTransformSlope` and
`productScaleZpositive_of_sliceTransform`.

### 4. Current final constructor and assumptions

The sharpest honest constructor remains:

```text
InteractionCollapseUniversalScale_of_targetedFinalClosure
```

Remaining theorem inputs:

* `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions`;
* `ClassicalFiniteAffineUtilityUniquenessAssumptions`;
* `FinitePosteriorValueRelabelingAssumptions`;
* `forall hprod, FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod`;
* `TraceAxioms F`.

Remaining conventions:

* `FiniteFaceScaleSingletonSliceAffineConventionFor`;
* `FiniteFaceScaleProductGaugeConventionFor`;
* `FiniteFaceScaleSingletonInteractionConventionFor`;
* `FiniteCoordinateSupportFaceValueConventionFor`;
* `FiniteCoordinateSupportFaceScaleConventionFor`;
* `FiniteUniversalScaleSingletonConventionFor`.

### 5. TeX notes

* State `actionbase` as scalar-valued and `permutationinvariance` as the
  product-normalization scalar pinning step.
* State `(W)` as the pre-universal grouping-recursion lemma before
  entropy/Faddeev.
* Keep POS as the positive slice-slope consequence already formalized in Lean.

---

## Selected Relabeling + Pre-Universal GR Pass

### 1. Selected representative relabeling

The old bare target `FinitePosteriorValueRelabelingAssumptions` is recorded as
too strong for the paper's product-normalization proof.  Lean now has the
repaired selected-representative interface:

```lean
FiniteSelectedPosteriorValueRelabelingFor hfaces
```

and selected consequences:

```lean
exactSelectedRelabelingInvariance
fullRevelationValueForFaceScales_relabel_eq_selected
faceScaleTripleProductValueAssociativity_of_selectedRelabeling
```

The selected theorem is not yet proved from actionbase/permutation-invariance.
Residual classification remains:

```text
GLOBAL_CARDINAL_NORMALIZATION_REQUIRED
```

### 2. Pre-universal grouping recursion

Lean now exposes the earlier pre-universal block-reveal and grouping-recursion
targets:

```lean
FinitePreUniversalBlockRevealValueFor hfaces
FinitePreUniversalGroupingGRFor hfaces hprod
```

and proves:

```lean
finitePreUniversalGroupingWeightRecursion_of_GR
```

Thus the current `(W)` input is repaired to the earlier TeX `(GR)` input.
The remaining proof is the pre-universal block-reveal/chain/neutrality assembly
that proves `(GR)`, not the algebraic conversion from `(GR)` to `(W)`.

### 3. Reassembly

New constructor:

```lean
InteractionCollapseUniversalScale_of_preUniversalGR
```

It takes `forall hprod, FinitePreUniversalGroupingGRFor hfaces hprod` instead
of `forall hprod, FinitePreUniversalGroupingWeightRecursionAssumptionsFor
hfaces hprod`.  It still takes `FinitePosteriorValueRelabelingAssumptions`
because the product-representation constructor has not yet been rebuilt using
the selected/swap-free route.

### 4. Files and route hygiene

New files:

```text
TraceableAgency/External/SelectedRelabeling.lean
TraceableAgency/External/PreUniversalGrouping.lean
TraceableAgency/External/PreEntropyClosure.lean
```

`TraceableAgency/External/Faddeev.lean` and
`TraceableAgency/External/EntropyReduction.lean` were not edited.

## Full Pre-Entropy Closure Pass

The selected relabeling target is reduced to the exact TeX cardinal chain:

```lean
FiniteSelectedActionbaseScalarFor hfaces
FiniteSelectedPermutationInvariancePinningFor hfaces
finiteSelectedPosteriorValueRelabeling_of_actionbase_permutationinvariance
```

This is strictly weaker than the old all-representatives
`FinitePosteriorValueRelabelingAssumptions`, but the scalar theorem and scalar
pinning remain global cardinal proof obligations until the swap-free product QA
route is formalized.

The pre-universal grouping target is reduced one step earlier:

```lean
FinitePreUniversalBlockRevealValueFor hfaces
FinitePreUniversalBlockRevealChainRuleFor hfaces hprod
finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
finitePreUniversalGroupingWeightRecursion_of_blockReveal
```

The new constructor:

```lean
InteractionCollapseUniversalScale_of_blockRevealChain
```

takes block reveal plus chain assembly instead of `(GR)`.  It still takes the
old full `hrelV` because product representation is not yet rebuilt from the
selected actionbase/permutation-invariance route.

## Repaired Pre-Entropy Target Clarification

The strict countermodel pass should be read as an overbroad-target diagnosis,
not as a refutation of the TeX proof.

For relabeling, arbitrary `hfaces` can be cardinally rescaled across isomorphic
action fibers.  The repaired target is therefore not "every hfaces has
cardinal relabeling", but selected relabeling for product-normalized
representatives:

```lean
FiniteProductNormalizedSelectedRepresentativesFor hfaces
finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives
```

For grouping, `hfaces + hprod` does not imply the block-reveal value identity.
The repaired missing input is the pre-universal cross-prior blockbridge:

```lean
FinitePreUniversalCrossPriorBlockBridgeFor hfaces
```

The next proof obligation is to derive
`FinitePreUniversalBlockRevealValueFor hfaces` from that bridge plus
neutrality/coarse-reveal and sigma-support algebra, then reuse the existing
`finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality` and downstream
`(W)` conversion.

## Architecture Repair: Pre-Entropy Ready Face Scales

The final architecture repair adds a construction-output object:

```lean
PreEntropyReadyFaceScalesStructure F
```

This replaces the false arbitrary-`hfaces` theorem goals with an explicit
ready structure carrying:

```lean
product_normalized_representatives :
  FiniteProductNormalizedSelectedRepresentativesFor hfaces
cross_prior_blockbridge :
  FinitePreUniversalCrossPriorBlockBridgeFor hfaces
product_quasi_additivity :
  FiniteProductQuasiAdditivityForFaceScales hfaces
block_reveal_chain :
  forall hprod, FinitePreUniversalBlockRevealChainRuleFor hfaces hprod
```

plus the explicit slice/coordinate/singleton conventions needed by the existing
interaction-collapse constructor.

New derived theorem names:

```lean
finitePreUniversalBlockRevealValue_of_crossPriorBlockBridge
finiteProductTwoGroupingWeightEquation_of_weightRecursion_selected
finiteProductGroupingEquation_of_weightRecursion_selected
PreEntropyReadyFaceScalesStructure.selectedRelabeling
PreEntropyReadyFaceScalesStructure.blockRevealValue
PreEntropyReadyFaceScalesStructure.groupingGR
PreEntropyReadyFaceScalesStructure.groupingW
PreEntropyReadyFaceScalesStructure.twoGroupingWeight
PreEntropyReadyFaceScalesStructure.groupingReferenceWeight
InteractionCollapseUniversalScale_of_preEntropyReady
```

The selected two-grouping theorem removes the old all-representatives relabeling
dependency from the `(W) -> E1/E2` step: the only relabeling use there is
full-revelation transport across `twoGroupingReassoc`, so selected exact
relabeling is sufficient.

The block-reveal theorem uses the unscaled cross-prior bridge plus A5
coarse-reveal projection/refinement neutrality.  It does not use the entropy
reduction theorem, Faddeev theorem, Shannon theorem, MI representation,
`EntropyReductionRepresentation`, `FiniteScaleCoherenceAssumptions`, or
`FiniteBranchAggregationAssumptions`.

## Remaining Inputs Closure Audit

The remaining-input audit for
`InteractionCollapseUniversalScale_of_fullPreEntropyClosure` separates global
theorem premises from residual pre-entropy inputs.

Global theorem premises:

| Input | Role |
|---|---|
| `TraceAxioms F` | behavioral theorem premise |
| `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions` | global classical HM representation theorem |
| `ClassicalFiniteAffineUtilityUniquenessAssumptions` | global classical finite affine uniqueness theorem |

Residual inputs:

| Input | Status | Reason | Lean producer or convention justification | TeX location |
|---|---|---|---|---|
| `CoherentRelabelingFaceScalesStructure F` | PROVED_IN_LEAN | named face-scale theorem output | `CoherentRelabelingFaceScales_of_faithfulBranch` | "Coherent relabelling and face scales" |
| `FiniteProductQuasiAdditivityForFaceScales hfaces` | PROVED_IN_LEAN | named coherent product theorem output | `productQuasiAdditivityForFaceScales_of_productRepresentation`; public producer `finiteFaceScaleProductRepresentationTheorem_of_HM_A8_classical_relabeling` | "Coherent product quasi-additivity" |
| `FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces` | PROVED_IN_LEAN | HM/affine uniqueness left-slice theorem output | `faceScaleProductLeftSliceAffineTransform_of_closedLocalTheorems` | "Coherent product quasi-additivity" |
| `FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod` | PROVED_IN_LEAN | product-revelation Step 1 scale link | derived in `InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal` using `productRevelationScaleLink_of_sequentialScale` | "Interaction collapse and universal chain scale", Step 1 |
| `FiniteCoordinateSupportFaceValueConventionFor hfaces` | HARMLESS_CONVENTION | coordinate support-face representative identification | bundled in `PreEntropyRepresentativeGaugeConventions` | support-face restriction and face-scale sections |
| `FiniteCoordinateSupportFaceScaleConventionFor hfaces` | HARMLESS_CONVENTION | coordinate support-face scale identification | bundled in `PreEntropyRepresentativeGaugeConventions` | support-face restriction and face-scale sections |
| `FiniteBlockSupportFaceValueConventionFor hfaces` | HARMLESS_CONVENTION | dependent-sum support-face representative identification | bundled in `PreEntropyRepresentativeGaugeConventions` | block reveal/grouping section |
| `FiniteBlockSupportFaceScaleConventionFor hfaces` | HARMLESS_CONVENTION | dependent-sum support-face scale identification | bundled in `PreEntropyRepresentativeGaugeConventions` | block reveal/grouping section |
| `FiniteProductReferenceZNormalizationFor hfaces hprod` | HARMLESS_CONVENTION | product `Z` reference gauge normalization | bundled in `PreEntropyRepresentativeGaugeConventions` | product gauge normalization |
| `FiniteUniversalScaleSingletonConventionFor hfaces` | HARMLESS_CONVENTION | singleton/null scale normalization | bundled in `PreEntropyRepresentativeGaugeConventions` | singleton scale convention |

Final wrapper:

```lean
InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal
```

No residual input is classified as
`SUBSTANTIVE_EXTRA_ASSUMPTION_WITH_COUNTERMODEL`.

## Stage ER-F Final MI Assembly Classification

Stage F assembles the final mutual-information representation from the
internally constructed Stage E `FaddeevEntropyForm`, the existing full-support
MI bridge, and the existing support-restriction boundary theorem.

Final constructor:

```lean
MIRep_of_fullPreEntropyClosure_minimal_internalUniqueness
```

| Input | Status | Reason | Lean producer or convention justification | TeX location |
|---|---|---|---|---|
| `TraceAxioms F` | THEOREM_PREMISE | behavioral axioms remain the main theorem premise | consumed directly by the pre-entropy and support-restriction route | global axiom statement |
| `ClassicalFaddeevTheoremAssumptions` | REMAINING_CLASSICAL_THEOREM | finite Faddeev characterization is the one remaining Faddeev/Shannon external theorem interface | consumed by `FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness` | Faddeev/Shannon characterization step |
| `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions` | UPSTREAM_PRE_ENTROPY_CLASSICAL_THEOREM | HM representation remains upstream of the pre-entropy construction | consumed by the full pre-entropy closure route before Stage F | HM representation step |
| `CoherentRelabelingFaceScalesStructure F` | UPSTREAM_PRE_ENTROPY_INPUT | face-scale structure already audited as the selected coherent representative input | carried into the Stage E entropy form | coherent face-scale construction |
| `FiniteProductQuasiAdditivityForFaceScales hfaces` | UPSTREAM_PRE_ENTROPY_INPUT | product quasi-additivity already audited upstream | carried into the Stage E entropy form | coherent product quasi-additivity |
| `FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces` | UPSTREAM_PRE_ENTROPY_INPUT | left-slice affine transform input already audited upstream | carried into the Stage E entropy form | product left-slice affine transform |
| `PreEntropyRepresentativeGaugeConventions hfaces hprod` | HARMLESS_CONVENTION | explicit representative/gauge/support convention bundle | carried into the Stage E entropy form | representative/gauge/support convention steps |
| `FiniteCardinalSupportBoundaryAssumptions` | BOUNDARY_ROOT | the single existing root for boundary support facts; no new boundary assumption is added | projections used in Stage D/E, and support-restriction bridge used in Stage F | boundary/support restriction step |

New Stage F producers:

```lean
fullSupportSufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
fullSupportBlockMI_of_fullPreEntropyClosure_minimal_internalUniqueness
fullSupportMIRepExtendsToBoundary_of_fullPreEntropyClosure_minimal_internalUniqueness
sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness
MIRep_of_fullPreEntropyClosure_minimal_internalUniqueness
```

Stage F no longer treats `FullSupportSufficiencyMIPackage`,
`FullSupportBlockMI`, `FullSupportMIRepExtendsToBoundary`,
`SufficiencyMIPackage`, or `MIRep` as external assumptions.  They are produced
in Lean by the constructors listed above.

## Final Certified Assumptions Classification

Final exported theorem:

```lean
MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
```

Final signature summary:

```lean
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
    (hfad : ClassicalFaddeevTheoremAssumptions)
    {F : PrefFamily}
    (hhm : FinalHMInterface)
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventions hhm hax) :
    MIRep F
```

| Input | Status | Reason | Lean producer or convention justification | TeX location |
|---|---|---|---|---|
| `TraceAxioms F` | THEOREM_PREMISE | behavioral axioms remain the main theorem premise | consumed by the final route | global axiom statement |
| `FinalHMInterface` | GLOBAL_CLASSICAL_HM_INTERFACE | data-carrying HM/posterior interface packages Blackwell/posterior sufficiency, representative-producing HM, and HM affine/integral consequences | `posteriorLawSufficiency_of_FinalHMInterface`, `posteriorValueRepresentation_of_FinalHMInterface`, `classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface` | posterior representation/HM step |
| `ClassicalFaddeevTheoremAssumptions` | GLOBAL_CLASSICAL_FADDEEV_INTERFACE | finite Faddeev characterization remains the Faddeev/Shannon interface | consumed by `FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness` | Faddeev characterization step |
| `FinalConstructedRepresentativeConventions hhm hax` | EXPLICIT_REPRESENTATIVE_GAUGE_SUPPORT_CONVENTIONS | branch support-face/boundary choices, singleton normalizations, positive product gauge, relabel/support compatibility, product-normalized selected representative convention, current product gauge, singleton interaction, and pre-entropy/boundary convention bundle | convention package; does not contain `hfaces` or `hprod` as fields | coherent product gauge, support restriction, block bridge, boundary convention steps |
| `CoherentRelabelingFaceScalesStructure F` | ELIMINATED_AS_FINAL_INPUT | constructed internally from HM data, faithful branch conventions, positive gauge, and compatibility equations | `coherentFaceScales_of_FinalHM_positiveGauge` | coherent face-scale construction |
| `FiniteProductQuasiAdditivityForFaceScales hfaces` | ELIMINATED_AS_FINAL_INPUT | constructed internally for the selected product-normalized representative | `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected` | coherent product quasi-additivity |
| `FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces` | ELIMINATED_AS_FINAL_INPUT | produced from HM affine interface and singleton slice convention | `finiteFaceScaleProductLeftSliceAffineTransform_of_HM` | left-slice affine transform |
| `PreEntropyRepresentativeGaugeConventions hfaces hprod` | INTERNAL_CONVENTION_FOR_CONSTRUCTED_OBJECTS | support-face representative, product-reference, and singleton scale choices for the internally constructed `hfaces` and `hprod` | bundled inside `FinalHarmlessConventions`, itself a field of `FinalConstructedRepresentativeConventions` | representative/gauge/support convention steps |
| `FiniteCardinalSupportBoundaryAssumptions` | INTERNAL_SUPPORT_CONVENTION_FOR_CONSTRUCTED_OBJECTS | delete zero-probability actions and use restricted-support representatives/Hfun | bundled inside `FinalHarmlessConventions.support_boundary` | boundary support restriction |

No final theorem input is `hfaces`, `hprod`, the left-slice affine package, the
old broad posterior relabeling package, entropy-reduction packages, Faddeev
entropy form, sufficiency packages, or `MIRep` itself.

## Historical Bad-Gauge Clarification

Earlier audits correctly observed that product normalization cannot be proved
for every arbitrary already-selected `hfaces`.  The support-cardinality gauge

```text
V^lambda_q(P) = lambda(|support(q)|) * I(q,P)
lambda(2) = 1
lambda(4) = 2
```

refutes only that false universal statement.  It is not a countermodel to the
TeX theorem, because the TeX proof chooses a coherent product gauge before using
product quasi-additivity.  The current final theorem follows that corrected
existential/construction order: it reconstructs the normalized representative
and its `hprod` internally, then feeds those constructed objects to the already
closed MI route.

## Final Actual Closure Update — Constructed Normalized Representative

The constructed/existential route is now closed in Lean by:

```lean
MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
```

Final signature summary:

```lean
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
    (hfad : ClassicalFaddeevTheoremAssumptions)
    {F : PrefFamily}
    (hhm : FinalHMInterface)
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventions hhm hax) :
    MIRep F
```

This theorem does not take `hfaces` or `hprod`.

| Construction or input | Status | Reason | Lean declaration |
|---|---|---|---|
| data-carrying HM representative output | PROVED_IN_LEAN | HM data plus Blackwell/posterior interface produces `PosteriorValueRepresentation F` | `posteriorValueRepresentation_of_FinalHMInterface` |
| constructed coherent face scales | PROVED_IN_LEAN_WITH_HARMLESS_CONVENTIONS | faithful branch data and positive gauge rebuild a coherent face-scale representative | `coherentFaceScales_of_FinalHM_positiveGauge` |
| selected value relabeling for normalized representative | PROVED_IN_LEAN_FROM_CONVENTION_PACKAGE | product-normalized selected representatives give selected relabeling | `finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives` |
| product slope affinity | PROVED_IN_LEAN | selected relabeling gives the product swap used in the slope proof | `faceScaleProductSlopeAffine_of_selectedRelabeling` |
| product intercept positive-linearity | PROVED_IN_LEAN | A8 same-order, HM public-mix affinity, and internal affine uniqueness | `productInterceptPositiveLinear_of_FinalHM_positiveGauge` |
| product quasi-additivity for constructed representative | PROVED_IN_LEAN | left slice, intercept, selected slope, selected triple associativity, product gauge, and singleton interaction assemble hprod | `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected` |
| final MI representation | PROVED_IN_LEAN | constructed `hfaces` and `hprod` are fed to the already closed Stage F theorem | `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` |

Remaining explicit non-HM/Faddeev package:

```lean
FinalConstructedRepresentativeConventions hhm hax
```

This bundle contains only representative/gauge/support choices: branch
support-face and boundary choices, singleton normalizations, a positive product
gauge and compatibility equations, product-normalized selected representative
data, current product-gauge normalization, singleton interaction normalization,
and the pre-entropy support/boundary convention bundle.

No substantive non-classical assumption remains outside `TraceAxioms F`,
`FinalHMInterface`, `ClassicalFaddeevTheoremAssumptions`, and
`FinalConstructedRepresentativeConventions hhm hax`.
