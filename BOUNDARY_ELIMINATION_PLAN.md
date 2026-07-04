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

---
## SESSION 4: fields 1 & 2 LANDED IN SOURCE (kernel-checked). Field 3 remains.

COMMITTED & PUSHED (github dcond/TraceableAgency, commit 64a4b06):
- Field 2: hfun_eq_normalizedValue_idChannel_of_scale (rfl, definitional).
- Field 1 FULLY PROVED and in source (External/EntropyReductionClosure.lean):
    * marginalValue_support_face  — new coherence clause on
      FinitePosteriorIntegralRepresentationAssumptions (genuine HM property).
    * fsSupportEquiv / restrictToSupport_eq_relabel_fullSupport.
    * wrapScale + wrapScale_fullSupport / _boundary_nondeg / _singleton.
    * boundaryCompleteScale : the boundary-completed ScaleCoherenceStructure
      (all 4 fields re-proved; singleton branchCoeff via original, nondeg via
      support_face_scale, full-support unchanged).
    * field1_boundaryComplete : normalizedValue q P = normalizedValue (q|supp)(P|supp)
      at boundary q — the exact FiniteNormalizedValueSupportBoundaryAssumptions content.
  All depend only on [propext, Classical.choice, Quot.sound]; full build green (8622).
- Also verified in scratch (scratch_boundary_elim/w_scale_ALL_VERIFIED.lean):
  wrapCross (boundary-completed CrossPriorBlockRepresentation, transparent transport)
  and field1_interface_wrapper.

REMAINING — field 3 (FiniteRestrictedCoarseRevealValueAssumptions) + final drop of hcard:
Field 3 target: normalizedValue (s|supp)(C|supp) = Hfun(p|supp) for s = sigmaDist p q boundary.
Route (all tools exist, assembly is the work):
  1. dependent reindex: s|supp ≃ sigmaDist (p|supp) (fun k' => (q k'.1)|supp), and
     C|supp transports to coarseRevealChannel over supp(p). (sigmaSupportEquiv is the core,
     already compiled in scratch bf3_equiv.lean; needs the channel-transport lemmas + the
     restricted-fibre sigmaDist identity.)
  2. normalizedValue relabel-invariance engine (compiled in scratch bf3_relabel.lean as
     normalizedValue_relabelAction_of_crossPrior) — NOT yet in source.
  3. apply coarseReveal_value_eq_Hfun_of_axioms_fullSupport to the full-support s|supp.
Then: build the boundary-completed cross-prior rep (wrapCross) through the entropy/Faddeev
spine and discharge all 3 boundary facts, dropping FiniteCardinalSupportBoundaryAssumptions
from the final theorem. NOTE: wrapCross changes Hfun (= normalizedValue·id on wrapped scale),
so the FaddeevEntropyForm/α·Shannon/MIRep chain must be re-derived on wrapCross — a spine
rebuild, the largest remaining chunk.

---
## SESSION 5: ALL THREE FIELDS PROVED + capstone MI route (no cardinal-boundary assumption)

LANDED IN SOURCE & PUSHED (commits be6fd91, 7525054):
- field1_boundaryComplete  (field 1)
- hfun_eq_normalizedValue_idChannel_of_scale  (field 2, rfl)
- field3_restricted_coarse_reveal  (field 3, via sigmaSupportEquiv + samePosteriorLaw collapse
  + normalizedValue_relabelAction_of_crossPrior + full-support coarse lemma)
- wrapCross, boundaryCompleteScale, coarseVal_forCross, satisfiesFaddeevRecursion_forCross,
  FaddeevEntropyForm_forCross, MIRep_forCross, entropyRegularity_forCross,
  MIRep_of_boundaryComplete  — MIRep F with NO FiniteCardinalSupportBoundaryAssumptions,
  given (hblock, hred) + support_face_scale (from hfaces) + HM marginalValue coherence clause.
All [propext, Classical.choice, Quot.sound]; full build green (8622).

FINAL MILE remaining to drop hcard from the EXPORTED theorem
MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions:
The producers Hfun_blockEmbed_of_fullPreEntropyClosure_minimal and
coarseReveal_entropyReduction_of_fullPreEntropyClosure_minimal (and
posteriorLawIntegral_supportRestrict_Hfun_...) currently take hcard, but their proofs use hcard
ONLY via field 1 (normalizedValueSupportBoundary), field 2 (hfunBoundaryIdentity), field 3
(restricted_coarse_reveal) + full-support relabel facts — ALL now proved for wrapCross. So:
  1. reprove Hfun_blockEmbed for wrapCross from field1_boundaryComplete (+ existing relabel facts);
  2. reprove coarseReveal_entropyReduction for wrapCross from field1/field3 + value_entropy_reduction;
  3. package as hblock/hred (∀-hcross structures are not needed — feed the per-cross facts into
     MIRep_of_boundaryComplete after refactoring it to take the two producer facts per-cross,
     mirroring coarseVal_forCross);
  4. new exported theorem MIRep_..._withConventions' taking FinalHarmlessConventions WITHOUT
     support_boundary, building hcross0 = crossPriorBlockRepresentation_of_fullPreEntropyClosure_minimal,
     hsf = hfaces.support_face_scale_eq, hcoh = hhm coherence clause.
This is ~150 lines of mechanical dependent-type proof reusing only already-proved facts; no new
mathematics. The convention's content is fully discharged; this step removes it from the signature.
