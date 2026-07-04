# Boundary-field elimination — scratch progress (NOT ported to source yet)

Goal: eliminate `FiniteCardinalSupportBoundaryAssumptions` (3 fields) — the last
non-gauge convention — by proving each field instead of assuming it.

## Verified in scratch (all compile against the real project):
- **Field 1** (`normalizedValue_support_boundary`): CLOSES given one HM-coherence
  clause `marginalValue_q (incl d) = marginalValue_{q|supp} d`. Proof: value_eq_integral
  (unguarded) + posteriorLawIntegral_restrictToSupport + pointwise Finset.sum_congr.
  The coherence clause is a genuine property of the real HM functional and belongs on
  `FinitePosteriorIntegralRepresentationAssumptions`.
- **Field 2** (`Hfun q = normalizedValue q idChannel` boundary): `rfl` for the concrete
  construction (EntropyReductionRepresentation_of_scale defines Hfun := Hcandidate :=
  normalizedValue · idChannel, unguarded).
- **Field 3 bricks** (this dir):
  - `bf3_sigma.lean`: supp(sigmaDist p q) ⟺ p k > 0 ∧ q k a > 0.
  - `bf3_equiv.lean`: `sigmaSupportEquiv : supportSubtype (sigmaDist p q) ≃ Σ k':supp p, supp (q k')`.
  - `bf3_relabel.lean`: `normalizedValue_relabelAction_of_crossPrior` — normalizedValue is
    action-relabel-invariant for ABSTRACT hcross at full support (via A5 + cross_prior_block_rep).
    KEY: no hfaces dependency, so field 3 CAN be discharged in place.

## Remaining for field 3 (all tools now verified to exist):
transport (s|supp, C|supp) across sigmaSupportEquiv to canonical sigmaDist (p|supp) q'
with coarseRevealChannel, apply coarseReveal_value_eq_Hfun_of_axioms_fullSupport, get Hfun(p|supp).

## Port plan (single atomic change):
1. add coherence clause to FinitePosteriorIntegralRepresentationAssumptions
2. prove fields 1,2,3 as theorems
3. delete FiniteCardinalSupportBoundaryAssumptions; re-thread ~8 consumers in Faddeev.lean
4. rebuild; confirm #print axioms unchanged [propext, Classical.choice, Quot.sound]

---
## UPDATE (this session): field 2 LANDED in source

- Added `hfun_eq_normalizedValue_idChannel_of_scale` in
  `TraceableAgency/External/EntropyReduction.lean` (right after
  `EntropyReductionRepresentation_of_scale`).
- Proves by `rfl`, at ALL priors (no full-support guard, no regularity, no boundary
  assumption): the constructed entropy rep satisfies `Hfun q = normalizedValue q idChannel`.
- This is exactly field 2 of `FiniteCardinalSupportBoundaryAssumptions`
  (`Hfun_boundary_identity`) / `FiniteHfunBoundaryIdentityAssumptions`, now proved
  rather than assumed for the representation the final theorem uses.
- Full build green (8622 jobs). Final theorem axiom footprint unchanged:
  [propext, Classical.choice, Quot.sound].
- NOT yet wired to delete the boundary field: `FaddeevEntropyForm_of_parts` is written
  generically over abstract `hcross` and still pulls `hid` from `hcard`. Rewiring it to
  use the concrete-rep theorem (dropping field 2 from the bundle) is the next step, done
  together with fields 1 and 3 against the concrete construction.

## Corrected analysis (important):
Fields 1 and 3, done properly, need BOTH value- and scale- support-face coherence, which
live in the concrete `CoherentRelabelingFaceScalesStructure` (`support_face_scale_eq`,
+ the new HM `marginalValue_support_face` coherence clause for value), NOT the abstract
`CrossPriorBlockRepresentation` the boundary fields are stated against. So full elimination
= restate the boundary obligations against the concrete construction and prove all three there.
Verified bricks (this dir): sigma support char, sigmaSupportEquiv, normalizedValue action-relabel
invariance for abstract hcross.

---
## SESSION 3: full recipe for fields 1 & 3 PROVEN (bricks compiled), assembly + singleton remain

Root architecture understood. The boundary elimination works via a **boundary-completed
scale wrapper** `scale' q := scale(q.restrictToSupport)` on the collapsed ScaleCoherenceStructure.

VERIFIED IN SCRATCH (compiled, no sorry):
- Numerator coherence: V q (exp P) = V (q|supp)(exp P|supp)  [via new marginalValue_support_face
  clause on FinitePosteriorIntegralRepresentationAssumptions + posteriorLawIntegral_restrictToSupport
  + Finset.sum_congr]. NOW ADDED TO SOURCE (BranchAggregation.lean), build green, currently DORMANT.
- Subsingleton branch of field 1: both sides 0 via branchValue_channel_eq_zero_of_subsingleton.
- scale(q|supp) = scale q for full-support q: fsEquiv + restrict_eq_relabel_fs + scale_relabel_eq.
- branchCoeff q r_o = scale(q|supp)/scale(r_o|supp) [wrapper's branchCoeff_factorization]:
    * full-support r_o: div_self / scale_relabel_eq  ✓
    * nondeg boundary r_o: support_face_scale_eq  ✓
    * singleton r_o: RESIDUE — needs scale r_o = scale(r_o|supp) at singleton, from the singleton
      scale convention (FiniteBranchScaleFactorizationSingletonConvention, already in the concrete
      scale_factorization). Not yet written.
- branchCoeff q r_o = 1 under scale_universal (full-support reached): div_self  ✓

KEY FACTS:
- scale_factorization.branchCoeff_factorization holds for ALL positive branches (incl boundary/
  singleton reached posteriors) as branchCoeff q r_o = scale q / scale r_o. (concrete field)
- support_face_scale_eq: branchCoeff q r = scale q / scale(r|supp), nondeg boundary r. (hfaces)
- fsEquiv lemmas: q.restrictToSupport = relabelDist (fsEquiv q hq) q for full-support q.

REMAINING TO LAND (mechanical, in-source):
1. singleton scale lemma: scale r = scale(r|supp) for singleton-support reached r (from singleton
   scale convention).
2. build boundaryCompleteScale wrapper (ScaleCoherenceStructure) with the 4 fields proved above.
3. instance plumbing for Nonempty (supportSubtype ·) in the scale accessor (statement-level).
4. prove FiniteNormalizedValueSupportBoundaryAssumptions for the wrapper => field 1.
5. field 3 (restricted coarse-reveal): via sigmaSupportEquiv + normalizedValue relabel engine
   (both compiled earlier) reduced to the full-support coarse lemma on q|supp.
6. thread wrapper through crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal and drop
   FiniteCardinalSupportBoundaryAssumptions from the final theorem.

DECISION: numerator-coherence clause is in source but DORMANT. Either complete the wiring
(steps 1-6) or revert the clause to avoid an unused interface strengthening.
