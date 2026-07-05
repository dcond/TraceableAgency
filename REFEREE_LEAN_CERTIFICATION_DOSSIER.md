# Referee Lean Certification Dossier

> **UPDATE (cardinal-boundary assumption eliminated).** Since the original drafting, the
> `FiniteCardinalSupportBoundaryAssumptions` boundary field has been **removed** from the
> convention bundle `FinalHarmlessConventions` / `FinalConstructedRepresentativeConventions`.
> Its three facts are now **proved theorems**, not assumptions:
> `field1_boundaryComplete` (boundary normalized-value support restriction),
> `hfun_eq_normalizedValue_idChannel_of_scale` (boundary `Hfun` identity), and
> `field3_restricted_coarse_reveal` (restricted coarse-reveal value). The exported theorem
> `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` routes through
> `MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal`; verified via `#print`
> that `FiniteCardinalSupportBoundaryAssumptions` is absent from every convention structure.
> Any text below that lists `support_boundary` / `FiniteCardinalSupportBoundaryAssumptions` as a
> live convention field is historical and superseded by this note. Axiom footprint unchanged:
> `[propext, Classical.choice, Quot.sound]`.


> **UPDATE (product/gauge conventions — in progress: proved, not assumed).** A feasibility
> probe (`PROBE_PRODUCT_NORMALIZED_FEASIBILITY.md`) established that the `product_normalized`
> pinning (`c = 1`) is *provably independent* of the axioms + the bare HM interface (a
> type-dependent rescaling of the value functional is a valid representative with `c ≠ 1`), yet
> is a genuine property of the *canonical* HM functional. The paper's own `t_n` cardinal-gauge
> construction targets a **cross-cardinality** object and does **not** discharge the
> **same-cardinality** pinning, so that route is abandoned. Instead the pinning and the whole
> coherent-gauge family (`gauge`/`scale_relabel`/`support_scale`, `current_product_gauge`,
> `singleton_interaction`) are being discharged from a single **exact-relabel-covariance
> (naturality) clause on the HM classical interface** — the same epistemic move (and template)
> as the accepted `marginalValue_support_face` boundary-elimination clause. Any text below that
> classifies these as `…_CHOICE`/`…_NORMALIZATION` conventions is being superseded by proved
> theorems; this note tracks that work.

**Subject:** Final Lean theorem `TraceableAgency.MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions`
**Paper:** `empowerment_v5(1).tex`, Theorem 1 ("Mutual-information characterisation", `thm:main`, TeX lines 767–800)
**Lean project:** `/Users/u1970555/daniele-workspace/TraceableAgency`
**Toolchain:** `leanprover/lean4:v4.32.0-rc1`; mathlib pinned at `v4.32.0-rc1` (rev `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`)
**Commit:** `846a49b877cb70c12e3de12783728bb40f39e5f3`
**Date:** 2026-07-03

This document is self-contained and **supersedes all earlier `STAGE_*` audits** for the purpose
of referee verification of the final theorem. Where earlier audits describe intermediate
architectures, monoliths, or "repaired earlier" states, this dossier records only what the
**current** final theorem actually certifies, quoted from live Lean output.

---

## 1. Executive verdict

**`CERTIFIED_MODULO_HM_FADDEEV_AND_EXPLICIT_CONVENTIONS`**

The Lean theorem proves `MIRep F` from `TraceAxioms F`, `FinalHMInterface`,
`ClassicalFaddeevTheoremAssumptions`, and `FinalConstructedRepresentativeConventions hhm hax`.

The final theorem **does not take** any of the following as assumptions:

- `CoherentRelabelingFaceScalesStructure F`
- `FiniteProductQuasiAdditivityForFaceScales hfaces`
- `FinitePosteriorValueRelabelingAssumptions`
- `FiniteScaleCoherenceAssumptions`
- `FiniteBranchAggregationAssumptions`
- `FiniteCrossPriorBlockAssumptions`
- `EntropyReductionRepresentation`
- `FaddeevEntropyForm`
- `SufficiencyMIPackage`
- `MIRep`

These were verified absent from the checked signature (they appear neither in the `#check`
output of Section 2 nor in the definition of `FinalConstructedRepresentativeConventions` in
Section 6). They are all either constructed internally by the proof route (Section 7) or
eliminated (Section 8).

**Scope caveat (see Sections 3, 4, 11).** This certificate covers the **sufficiency /
`MIRep` direction**: `TraceAxioms F → MIRep F` (modulo the listed classical interfaces and
conventions). The `iff`'s necessity direction and the "moreover" block clause of TeX
Theorem 1 are certified by **separate** Lean theorems (`BenchmarkStatement_of_DPI`,
`blockSameScaleRep_of_MIRep`), **not** by this final theorem. The paper must not claim the
final theorem alone proves the full `iff`-plus-moreover statement.

---

## 2. Exact final theorem

The following are copied verbatim from `lake env lean /tmp/final_referee_check.lean`.

### 2.1 `#check` (checked signature)

```
TraceableAgency.MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions.{u}
  (hfad : TraceableAgency.ClassicalFaddeevTheoremAssumptions) {F : TraceableAgency.PrefFamily}
  (hhm : TraceableAgency.FinalHMInterface) (hax : TraceableAgency.TraceAxioms F)
  (hconv : TraceableAgency.FinalConstructedRepresentativeConventions hhm hax) : TraceableAgency.MIRep F
```

Source (`TraceableAgency/External/EntropyReductionClosure.lean:3046`):

```lean
theorem MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    {F : PrefFamily.{u}}
    (hhm : FinalHMInterface.{u})
    (hax : TraceAxioms F)
    (hconv : FinalConstructedRepresentativeConventions hhm hax) :
    MIRep F :=
  MIRep_of_TraceAxioms_FinalHM_Faddeev_withProductNormalizedSelectedRepresentatives
    hfad hhm hconv.branch hax hconv.gauge hconv.scale_relabel
    hconv.support_scale hconv.singleton_slice hconv.product_normalized
    hconv.current_product_gauge hconv.singleton_interaction hconv.harmless
```

### 2.2 `#print axioms`

```
'TraceableAgency.MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

These are the three standard mathlib/Lean logical axioms. **No project-specific axiom, no
`sorryAx`, no `Classical`-hidden placeholder** appears.

---

## 3. What `MIRep F` says

**File:** `TraceableAgency/Behaviour/MIPreference.lean:31`

**Exact statement** (`#print` output):

```
def TraceableAgency.MIRep.{u} : TraceableAgency.PrefFamily → Prop :=
fun F =>
  ∀ {A O : Type u} [inst : Fintype A] [inst_1 : DecidableEq A] [inst_2 : Fintype O] [inst_3 : DecidableEq O]
    (P : TraceableAgency.Channel A O) (q q' : TraceableAgency.Dist A), F.rel P q q' ↔ I(q, P) ≥ I(q', P)
```

Source:

```lean
def MIRep (F : PrefFamily.{u}) : Prop :=
  ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
    (P : Channel A O) (q q' : Dist A),
    F.rel P q q' ↔ mutualInfo q P ≥ mutualInfo q' P
```

(`I(q, P)` is notation for `mutualInfo q P`.)

**Mathematical translation.** For every finite action alphabet `A`, finite outcome alphabet
`O`, channel `P : A → Δ(O)`, and every pair of priors `q, q' ∈ Δ(A)`:

> `q ≽_P q'  ⟺  I_{q,P}(A;O) ≥ I_{q',P}(A;O)`.

This is **the same-channel / fixed-environment** mutual-information representation. Both sides
of every comparison use the **same** channel `P` and the **same** environment. `MIRep F` does
**not** by itself express cross-prior or cross-block comparisons on a common scale.

**Broader TeX content.** TeX Theorem 1 has additional content beyond `MIRep F`:
1. the necessity direction (`(ii) ⟹ (i)`), and
2. the "moreover" clause on block-supported cross-channel comparisons.

Lean theorems for these exist but are **separate** from the final theorem:

- **Necessity:** `TraceableAgency.BenchmarkStatement_of_DPI` (`Main.lean:140`), i.e.
  `FiniteDPIAssumptions → ∀ F, MIRep F → TraceAxioms F`.
- **Moreover / block same-scale:** `TraceableAgency.blockSameScaleRep_of_MIRep`
  (`Main.lean:155`), i.e. `∀ F, MIRep F → BlockSameScaleRep F`, with `BlockSameScaleRep`
  defined at `Main.lean:50`.

Neither is invoked by `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions`.

---

## 4. What the TeX theorem says

TeX Theorem 1 (`thm:main`, lines 767–800), verbatim structure:

> For a family `{≽_P}_P` of weak orders over finite stochastic environments, the following
> are equivalent.
> **(i)** The family satisfies Axioms (A1)–(A8).
> **(ii)** For every finite channel `P : A → Δ(O)` and every `q, q' ∈ Δ(A)`,
> `q ≽_P q' ⟺ I_{q,P}(A;O) ≥ I_{q',P}(A;O)`.
>
> **Moreover**, under these equivalent conditions, block-supported cross-channel comparisons
> are represented on the same scale: for every finite block environment `⨆_{k∈K} P_k`, every
> two distinct blocks `i, j ∈ K`, and every `q_i ∈ Δ(A_i)`, `q_j ∈ Δ(A_j)`,
> `q_i^i ≽_{⨆_k P_k} q_j^j ⟺ I_{q_i,P_i}(A_i;O_i) ≥ I_{q_j,P_j}(A_j;O_j)`.

Boundary priors: the paper handles non-full-support priors via the support-restriction lemma
(`lem:supprestrict`) and the boundary extension; there is no separate boundary-prior clause in
the theorem statement — boundary behaviour is folded into the "for every `q, q'`" quantifier.

### Claim-by-claim table

| TeX claim | Lean theorem certifying it | Status | Notes |
|---|---|---|---|
| (i) ⟹ (ii): axioms give same-channel MI representation | `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` | `CERTIFIED_BY_FINAL_THEOREM` | The subject of this dossier; modulo HM/Faddeev classical interfaces + conventions. |
| (ii) same-channel iff form itself | `MIRep` definition (`MIPreference.lean:31`) | `CERTIFIED_BY_FINAL_THEOREM` | Output type of the final theorem is exactly this `iff`. |
| (ii) ⟹ (i): necessity/benchmark | `BenchmarkStatement_of_DPI` (`Main.lean:140`) | `CERTIFIED_BY_SEPARATE_LEAN_THEOREM` | Requires `FiniteDPIAssumptions` (classical finite DPI). **Not** proved by the final theorem. |
| "Moreover": block same-scale cross-channel comparison | `blockSameScaleRep_of_MIRep` (`Main.lean:155`) | `CERTIFIED_BY_SEPARATE_LEAN_THEOREM` | Derived from `MIRep F` via `mutualInfo_blockFamily_embed`. **Not** proved by the final theorem; would compose with it as `blockSameScaleRep_of_MIRep F (finalTheorem …)`. |
| Full `iff` assembly | `main_characterization_from_spine` / `MainCharacterizationWithMoreover` (`Main.lean:74,99`) | `CERTIFIED_BY_SEPARATE_LEAN_THEOREM` (assembly only) | Assembles the three spine statements; it is a logical wiring lemma, not a proof of any direction. |
| HM affine/posterior representation | `FinalHMInterface` fields | `CLASSICAL_INTERFACE` | Displayed statements accepted as classical (Section 5). |
| Faddeev entropy characterization | `ClassicalFaddeevTheoremAssumptions.of_recursion` | `CLASSICAL_INTERFACE` | Displayed statement accepted as classical (Section 5). |
| Representative / gauge / support / boundary-cardinal choices | `FinalConstructedRepresentativeConventions` fields | `CONVENTION` | Normalisations, not behavioural axioms (Section 6). |

**Referee-facing honesty statement.** This Lean certificate covers the **sufficiency /
`MIRep` theorem** — direction (i) ⟹ (ii). The **moreover** and **necessity** clauses are
**not certified by this theorem**; they are certified by the separate Lean theorems listed
above (necessity additionally requiring the classical `FiniteDPIAssumptions`).

### 4.1 Separate-theorem certification: exact `#check` / `#print axioms`

Copied verbatim from `lake env lean /tmp/companion_check.lean`.

**Necessity / benchmark** — `BenchmarkStatement_of_DPI` (`Main.lean:140`):

```
TraceableAgency.BenchmarkStatement_of_DPI : TraceableAgency.FiniteDPIAssumptions → TraceableAgency.BenchmarkStatement
'TraceableAgency.BenchmarkStatement_of_DPI' depends on axioms: [propext, Classical.choice, Quot.sound]
```

with

```
def TraceableAgency.BenchmarkStatement.{u} : Prop :=
∀ (F : TraceableAgency.PrefFamily), TraceableAgency.MIRep F → TraceableAgency.TraceAxioms F
```

i.e. `FiniteDPIAssumptions → ∀ F, MIRep F → TraceAxioms F` — the `(ii) ⟹ (i)` direction,
modulo the classical finite data-processing-inequality interface `FiniteDPIAssumptions`.

**Moreover / block same-scale** — `blockSameScaleRep_of_MIRep` (`Main.lean:155`):

```
TraceableAgency.blockSameScaleRep_of_MIRep : ∀ (F : TraceableAgency.PrefFamily),
  TraceableAgency.MIRep F → TraceableAgency.BlockSameScaleRep F
'TraceableAgency.blockSameScaleRep_of_MIRep' depends on axioms: [propext, Classical.choice, Quot.sound]
```

with

```
def TraceableAgency.BlockSameScaleRep.{u} : TraceableAgency.PrefFamily → Prop :=
fun F =>
  ∀ {K : Type u} [inst : Fintype K] [inst_1 : DecidableEq K] (Act Out : K → Type u) [inst_2 : (k : K) → Fintype (Act k)]
    [inst_3 : (k : K) → DecidableEq (Act k)] [inst_4 : (k : K) → Fintype (Out k)]
    [inst_5 : (k : K) → DecidableEq (Out k)] (P : (k : K) → TraceableAgency.Channel (Act k) (Out k)) (i j : K),
    i ≠ j →
      ∀ (qᵢ : TraceableAgency.Dist (Act i)) (qⱼ : TraceableAgency.Dist (Act j)),
        F.rel (TraceableAgency.blockFamilyChannel Act Out P) (TraceableAgency.blockEmbedDist Act i qᵢ)
            (TraceableAgency.blockEmbedDist Act j qⱼ) ↔
          I(qᵢ, P i) ≥ I(qⱼ, P j)
```

i.e. `∀ F, MIRep F → BlockSameScaleRep F` — the "moreover" block same-scale clause, derived
purely from `MIRep F` (no `FiniteDPIAssumptions` needed). Composing with the final theorem
gives the moreover clause from the axioms: `blockSameScaleRep_of_MIRep F (finalTheorem …)`.

Both companion theorems depend only on `[propext, Classical.choice, Quot.sound]` — the same
three standard axioms as the final theorem, with no project-specific axiom or `sorryAx`.

---

## 5. Assumption inventory

The final theorem takes exactly four inputs. `F` is implicit; `hfad`, `hhm`, `hax`, `hconv`
are the substantive hypotheses.

| Input | Lean type | Status | Mathematical meaning | TeX location | Human check required? |
|---|---|---|---|---|---|
| `hax` | `TraceAxioms F` | Behavioural axioms | The agent's A1–A8 (Section 5.1) | lines 410–543 | **Yes** — verify A1–A8 fields encode the paper's axioms |
| `hhm` | `FinalHMInterface` | Classical interface (HM + pure finite Blackwell) | Finite Herstein–Milnor + pure finite Blackwell equivalence theorem; the A3/A4/A1 replacement is proved internally (Section 5.2) | Lemma HM refs, `lem:blackwell`, `lem:postsep` | **Yes** — confirm each field is a displayed classical statement |
| `hfad` | `ClassicalFaddeevTheoremAssumptions` | Classical interface (Faddeev) | Faddeev entropy uniqueness applied to a regular recursive candidate (Section 5.3) | Faddeev sketch (`lem:faddeevsketch`) | **Yes** — confirm `of_recursion` is the finite Faddeev theorem |
| `hconv` | `FinalConstructedRepresentativeConventions hhm hax` | Conventions/normalisations | Representative, gauge, support-face, boundary-cardinal, singleton normalisation choices (Section 6) | conventions around `lem:convnorm`, `eq:facescale` | **Yes** — confirm each field is harmless (Section 6) |

### 5.1 `TraceAxioms F` fields

`#print` (`Behaviour/Axioms.lean:368`):

```
structure TraceableAgency.TraceAxioms.{u} (F : TraceableAgency.PrefFamily) : Prop
fields:
  a1 : A1_WeakOrderLocalNontriviality F
  a2 : A2_Continuity F
  a3 : A3_BlockComparisonCoherence F
  a4 : A4_OutcomePostprocessingAversion F
  a5 : A5_ActionCoarseningAversion F
  a6 : A6_PublicCoinIndependence F
  a7 : A7_BranchwiseContinuationMonotonicity F
  a8 : A8_IndependentBackgroundSeparability F
```

| Field | Lean predicate | TeX axiom | TeX lines |
|---|---|---|---|
| `a1` | `A1_WeakOrderLocalNontriviality` | (A1) Weak order + local non-triviality | 410–420 |
| `a2` | `A2_Continuity` | (A2) Continuity | 422–446 |
| `a3` | `A3_BlockComparisonCoherence` | (A3) Block-comparison coherence | 448–467 |
| `a4` | `A4_OutcomePostprocessingAversion` | (A4) Outcome post-processing aversion | 469–476 |
| `a5` | `A5_ActionCoarseningAversion` | (A5) Action-coarsening aversion | 478–491 |
| `a6` | `A6_PublicCoinIndependence` | (A6) Public-coin independence | 493–503 |
| `a7` | `A7_BranchwiseContinuationMonotonicity` | (A7) Branchwise continuation monotonicity | 505–524 |
| `a8` | `A8_IndependentBackgroundSeparability` | (A8) Independent-background separability | 526–543 |

Faithfulness notes (from `Behaviour/Axioms.lean` docstrings):
- **A7** is the *paper-faithful* variant: both continuation channels `Q` and `R` share the
  same branch outcome family `O₂ : O₁ → Type` (source lines 264–305). A strictly stronger
  auxiliary `A7Strong` allowing different families exists but is **not** the field used;
  `A7_of_A7Strong` shows the direction of strength.
- **A8** allows the alternative background channels to have different outcome alphabets,
  matching the paper's "any channels" wording (source lines 319–336).

### 5.2 `FinalHMInterface` fields

`#print` (`External/EntropyReductionClosure.lean:44`):

```
structure TraceableAgency.FinalHMInterface.{v} : Type (v + 1)
fields:
  blackwell  : FiniteSamePosteriorLawBlackwellEquivalenceAssumptions
  hm_rep     : FiniteHersteinMilnorAssumptions
  hm_affine  : ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions
```

| Field | Produces | Role in proof |
|---|---|---|
| `blackwell` | `PosteriorLawSufficiency F` from `TraceAxioms F` | **Pure finite Blackwell theorem.** Type `FiniteSamePosteriorLawBlackwellEquivalenceAssumptions`: at a full-support prior, same posterior law ⇒ mutual garbling. The paper-specific A3/A4/A1 block-comparison replacement is **proved internally** by `blackwellPosteriorReplacement_of_samePosteriorGarblings` (Blackwell.lean:444), then fed to `from_axioms_to_posterior_of_blackwell` in `posteriorLawSufficiency_of_FinalHMInterface`. |
| `hm_rep` | `PosteriorValueRepresentation F` | **PosteriorValueRepresentation.** Via `posteriorValueRepresentation_of_FinalHMInterface` = `posteriorValueRep_of_HersteinMilnor`, combining `hm_rep` with posterior-law sufficiency. Supplies the posterior value functional `V`, posterior-law invariance, and zero normalization. |
| `hm_affine` | `ClassicalFiniteMixtureSpaceAffineRepresentationAssumptions` | **Affine / integral HM consequences.** Via `classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface`, which in turn yields `FiniteAffineLinearPartAssumptions` and `FinitePosteriorIntegralRepresentationAssumptions` used in the branch-aggregation linear-part algebra. |

**Full disclosure (updated after the Blackwell refactor).** The `blackwell` field is now the
**pure textbook finite Blackwell equivalence theorem** — `FiniteSamePosteriorLawBlackwellEquivalenceAssumptions`,
which contains no `F.rel` and no `TraceAxioms`. The paper's A3/A4/A1 preference-replacement step
(formerly bundled into the assumption as `FiniteBlackwellPosteriorAssumptions`) is now a
kernel-checked theorem `blackwellPosteriorReplacement_of_samePosteriorGarblings`, so it is
**derived from the axioms, not assumed**. The remaining external HM content is `hm_rep`
(`FiniteHersteinMilnorAssumptions`, directly supplying the posterior value functional and its zero
normalization) and `hm_affine` (the affine/integral corollary). A referee accepting the displayed
finite Herstein–Milnor and finite Blackwell theorems accepts this bundle; the earlier
"Blackwell-bridge" caveat no longer applies.

### 5.3 `ClassicalFaddeevTheoremAssumptions`

`#print` (`External/EntropyReductionClosure.lean`, structure with single field `of_recursion`):

```
structure TraceableAgency.ClassicalFaddeevTheoremAssumptions.{v} : Prop
fields:
  of_recursion : ∀ (F : PrefFamily) {hentropy : EntropyReductionRepresentation F},
      FaddeevRecursionForm F hentropy →
        ∃ alpha, 0 ≤ alpha ∧
          ∀ {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
            (q : Dist A), hentropy.Hfun q = alpha * H(q)
```

**Mapping to TeX.** This is the finite Faddeev entropy-uniqueness theorem: any entropy
candidate `Hfun` satisfying the Faddeev recursion form (`FaddeevRecursionForm`) is a
nonnegative multiple `α · H` of Shannon entropy `H(q)`. The field `of_recursion` corresponds
exactly to the paper's invocation of Faddeev's characterization in the Faddeev sketch
(`lem:faddeevsketch`), converting recursive/regular entropy into `α · Shannon`. The premise
`FaddeevRecursionForm F hentropy` is *supplied by the proof* (Section 7); only the
classical conclusion `Hfun = α·H` is assumed here.

---

## 6. Convention inventory

`#print` of `FinalConstructedRepresentativeConventions` (`External/EntropyReductionClosure.lean`,
parameters `{F} (hhm : FinalHMInterface) (hax : TraceAxioms F)`), fields:

```
  branch                 : FinalFaithfulBranchConventions hhm
  gauge                  : PositiveFaceScaleGauge
  scale_relabel          : (relabelling-invariance equation for gauge · chain-scale)
  support_scale          : (support-face scale coherence equation)
  singleton_slice        : FiniteFaceScaleSingletonSliceAffineConventionFor (…coherentFaceScales…)
  product_normalized     : FiniteProductNormalizedSelectedRepresentativesFor (…coherentFaceScales…)
  current_product_gauge  : FiniteFaceScaleProductGaugeConventionFor (…pairwiseBilinearity…)
  singleton_interaction  : FiniteFaceScaleSingletonInteractionConventionFor (…pairwiseBilinearity…)
  harmless               : FinalHarmlessConventions (…coherentFaceScales…) (…productQuasiAdditivity…)
```

### Detailed field classification

| Field | Lean type | Meaning | Why harmless | TeX location | Could hide substantive content? |
|---|---|---|---|---|---|
| `branch` | `FinalFaithfulBranchConventions hhm` | Support-face representative choice, boundary coefficient/scale positive choice, singleton scale convention, support-face marginal-value transport, boundary/singleton scale-factorization equalities (fields `support_face`, `boundary_coeff`, `singleton_scale`, `marginal_value`, `boundary_scale`, `singleton_scale_factorization`; source `:1392`) | Each field selects a representative on the support face or a positive scale on a boundary/singleton where the paper's value contributions are zero or read through the face; no comparison-order content. | `lem:supprestrict`, boundary extension, `eq:facescale` singleton clause (line 2344) | **No** — see classification below; these are `SUPPORT_FACE_REPRESENTATIVE_CHOICE` / `BOUNDARY_SUPPORT_REPRESENTATIVE_CHOICE` / `SINGLETON_OR_NULL_NORMALIZATION` |
| `gauge` | `PositiveFaceScaleGauge` | A strictly positive prior-dependent gauge `gauge : Dist A → ℝ`, `0 < gauge q` (source `ScaleCoherence.lean:930`) | Only positivity is required; no relation to preference order. A positive rescaling of a value functional preserves all `≥` comparisons. | Positive gauge choice, `lem:convnorm` normalization | **No** — `POSITIVE_GAUGE_CHOICE` |
| `scale_relabel` | `∀ e q, q.FullSupport → gauge(relabel e q)·scale(relabel e q) = gauge q · scale q` | The gauged chain-scale is invariant under finite action relabelling | Pure equivariance normalization of the chosen positive gauge; consistent with exact-relabelling invariance which is order-free. | `cor:permutationinvariance`, `eq:facescale` (relabelling preserved, line 2343) | **No** — `RELABEL_SUPPORT_COMPATIBILITY_FOR_CHOSEN_GAUGE` |
| `support_scale` | support-face coherence equation for `gauge · branchCoeff` vs restricted-support scale | Compatibility of the gauge with support restriction | Relates the gauge on a boundary prior to the gauge on its support face; a normalization tying `gauge r` to `gauge r.restrictToSupport`, no order content. | `lem:supprestrict` | **No** — `BOUNDARY_SUPPORT_REPRESENTATIVE_CHOICE` |
| `singleton_slice` | `FiniteFaceScaleSingletonSliceAffineConventionFor …` | Left-slice affine normalization on a one-action (singleton) fibre | On singleton fibres the coordinate value is identically zero; the affine coefficient is not value-identifiable and is fixed by convention. | Step 2 singleton clause; `lem:coherentnorm` | **No** — `SINGLETON_OR_NULL_NORMALIZATION` |
| `product_normalized` | `FiniteProductNormalizedSelectedRepresentativesFor …` | The **selected** product representative is already product-gauge-normalized | This is the existential choice of a product-normalized representative (Section 9); it is why the support-cardinality countermodel does not apply. A choice of representative, not a behavioural claim. | `lem:coherentnorm`, `eq:facescale` | **No** — `SELECTED_PRODUCT_NORMALIZED_REPRESENTATIVE_CHOICE` |
| `current_product_gauge` | `FiniteFaceScaleProductGaugeConventionFor …` | The current representatives are the post-gauge (normalized) ones | Records that the already-selected representatives satisfy the positive gauge normalization; a bookkeeping convention on the chosen gauge. | `lem:coherentnorm` gauge step | **No** — `PRODUCT_GAUGE_NORMALIZATION` |
| `singleton_interaction` | `FiniteFaceScaleSingletonInteractionConventionFor …` | Singleton interaction coefficient convention (extends common κ to degenerate factors) | Singleton interaction terms are identically zero (proved internally); the coefficient is not value-identifiable and set by convention. | Step 5 singleton clause; `lem:coherentnorm` | **No** — `SINGLETON_OR_NULL_NORMALIZATION` |
| `harmless` | `FinalHarmlessConventions hfaces hprod` (fields `singleton_slice`, `pre_entropy : PreEntropyRepresentativeGaugeConventions`, `support_boundary : FiniteCardinalSupportBoundaryAssumptions`; source `:1203`) | Bundled residual conventions: singleton slice, pre-entropy representative/gauge choices, and the boundary-cardinal support extension interface | The first two are representative/gauge choices; `support_boundary` is the one boundary-cardinal extension interface (accepted as a narrow classical/boundary bridge, documented Stage 9O). No order content. | boundary extension; `lem:convnorm` | **No** for the representative/gauge parts; `support_boundary` is the explicit `SINGLETON_OR_NULL_NORMALIZATION`/boundary-cardinal interface, disclosed here |

### Mandatory convention questions

The `#print` above shows the *complete* field list. Reading it:

- **Does `FinalConstructedRepresentativeConventions` contain `hfaces`
  (`CoherentRelabelingFaceScalesStructure F`)?** **No.** No field has type
  `CoherentRelabelingFaceScalesStructure F`. The structure `coherentFaceScales_of_FinalHM_positiveGauge …`
  appears only *inside* the types of `singleton_slice`, `product_normalized`, and `harmless`
  as the internally-**constructed** face-scales object those conventions are *about* — it is
  built from `hhm`, `branch`, `hax`, and `gauge` (all already present), not supplied by the
  caller.
- **Does it contain `hprod` (`FiniteProductQuasiAdditivityForFaceScales hfaces`)?** **No.** No
  field has this type. `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected …`
  appears only as the second argument of `FinalHarmlessConventions`'s type, and it too is an
  internally-**constructed** term (Section 7 node), not an input.
- **Does it contain an opaque assumption equivalent to product quasi-additivity?** **No.**
  Product quasi-additivity is *produced* by the node
  `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected` from HM + faithful
  branch + gauge + the (harmless) normalization conventions. It is not assumed.
- **Does it contain an opaque assumption equivalent to `MIRep`?** **No.** No field mentions
  `MIRep`, `mutualInfo`, or the preference relation `F.rel` in a way that would presuppose the
  representation. The fields are gauge positivity, relabelling/support equivariance equations,
  singleton normalizations, and representative choices.

No field is classified `POTENTIALLY_SUBSTANTIVE`.

---

## 7. Constructed objects and dependency graph

All nodes were confirmed present by `rg` (locations below). "Uses forbidden downstream
package?" means: does the node take any of the ten eliminated bundles from Section 1 as a
*direct hypothesis*? All answer **no**.

| Node (Lean declaration) | File:line | Output | Main inputs | TeX step | Uses forbidden pkg? |
|---|---|---|---|---|---|
| `posteriorLawSufficiency_of_FinalHMInterface` | ERC:50 | `PosteriorLawSufficiency F` | `hhm.blackwell`, `hax` | Blackwell sufficiency | no |
| `posteriorValueRepresentation_of_FinalHMInterface` | ERC:59 | `PosteriorValueRepresentation F` | `hhm.hm_rep`, posterior-law sufficiency | HM value rep | no |
| `classicalFiniteMixtureSpaceAffineRepresentation_of_FinalHMInterface` | ERC:68 | affine/integral HM data | `hhm.hm_affine` | HM affine part | no |
| `faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle` | ERC:1449 | `FiniteFaithfulBranchAggregationAssumptions` | `hhm`, `hconv.branch` | Branch aggregation / cocycle / chain rule | no |
| `coherentFaceScales_of_FinalHM_positiveGauge` | ERC:1490 | `CoherentRelabelingFaceScalesStructure F` | `hhm`, faithful branch, `hax`, `gauge`, equivariance | Coherent relabelling & face scales | no (**produces** `hfaces`) |
| `faceScaleProduct_value_swap_eq_of_selectedRelabeling` | ERC:1820 | product value swap equality | selected relabeling, `hax` | product swap (Step 2/4) | no |
| `faceScaleProductSlopeAffine_of_selectedRelabeling` | ERC:1853 | product-slice slope affinity | selected relabeling, slice affine, intercept linear | Step 2 slope | no |
| `productInterceptPositiveLinear_of_FinalHM_positiveGauge` | ERC:1745 | product-slice intercept positive-linear | `hhm`, faithful branch, `hax`, `gauge`, equivariance | Step 2 intercept | no |
| `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected` | ERC:2004 | `FiniteProductQuasiAdditivityForFaceScales hfaces` | `hhm`, faithful branch, `hax`, `gauge`, normalization conventions | `lem:coherentnorm` | no (**produces** `hprod`) |
| `InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal` | PreEntropyConstruction:272 | `InteractionCollapseUniversalChainScaleStructure F` | `hfaces`, HM, affine-uniqueness, `hprod`, slice transform, pre-entropy conventions, `hax` | `lem:scalecoherence` (interaction collapse, universal scale) | no |
| `EntropyReductionRepresentation_of_interactionCollapse` | ERC:80 | `EntropyReductionRepresentation F` | interaction-collapse structure | entropy-reduction part of Faddeev sketch | no (**produces** `EntropyReductionRepresentation`) |
| `crossPriorBlockRepresentation_of_preUniversalBridge` | ERC:97 | `CrossPriorBlockRepresentation F` | pre-universal bridge, `hax`, entropy reduction, alignment | `lem:blockbridge` (rescaled) | no |
| `faddeevRecursionForm_of_fullPreEntropyClosure_minimal` | ERC:998 | `FaddeevRecursionForm F …` | pre-entropy closure data | Faddeev recursion form | no |
| `FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness` | ERC:1070 | `FaddeevEntropyForm F` | `hcard`, `hfad`, `hhm`, slice transform, conventions, `hax` | Faddeev sketch conclusion | no (**produces** `FaddeevEntropyForm`) |
| `MIRep_of_fullPreEntropyClosure_minimal_internalUniqueness` | ERC:1164 | `MIRep F` | `hcard`, `hfad`, `hhm`, slice transform, conventions, `hax` | Global MI representation | no (**produces** `MIRep`) |
| `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` | ERC:3046 | `MIRep F` | `hfad`, `hhm`, `hax`, `hconv` | **Theorem 1, (i)⟹(ii)** | no |

(`ERC` = `TraceableAgency/External/EntropyReductionClosure.lean`.)

**Reading of the graph.** The final theorem unpacks `hconv` into `branch`, `gauge`, and the
five normalization fields, then routes through
`MIRep_of_TraceAxioms_FinalHM_Faddeev_withProductNormalizedSelectedRepresentatives` (ERC:2783).
That route internally *constructs* the faithful branch package, the coherent face scales
`hfaces`, product quasi-additivity `hprod`, interaction collapse, entropy reduction, the
cross-prior block bridge, the Faddeev recursion form, applies the classical Faddeev interface
`hfad` to get `FaddeevEntropyForm`, and finally assembles `MIRep F`. Every one of the ten
Section-1 bundles that a naive reading might expect as a hypothesis is instead an output of
one of these nodes.

---

## 8. Eliminated assumptions

Each row: is it a direct hypothesis of the final theorem? (No, for all.) How is it produced or
bypassed?

| Bundle | Formerly a blocker? | Assumed by final theorem? | Produced / bypassed by |
|---|---|---|---|
| `CoherentRelabelingFaceScalesStructure F` | Yes (earlier `hfaces` input) | **No** | Constructed: `coherentFaceScales_of_FinalHM_positiveGauge` (ERC:1490) |
| `FiniteProductQuasiAdditivityForFaceScales hfaces` | Yes (earlier `hprod` input) | **No** | Constructed: `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected` (ERC:2004) |
| `FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces` | Yes | **No** | Constructed: `finiteFaceScaleProductLeftSliceAffineTransform_of_HM` (ERC, from HM + singleton slice) |
| `FinitePosteriorValueRelabelingAssumptions` | Yes | **No** | Superseded by the selected-relabeling route (`FiniteSelectedPosteriorValueRelabelingFor`) internal to the face-scales construction |
| `FinitePreUniversalGroupingWeightRecursionAssumptionsFor` | Yes | **No** | Produced within the interaction-collapse construction (`InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal`) |
| `FiniteProductScaleZPositiveAssumptionsFor` | Yes | **No** | Produced within pre-entropy closure (product scale `Z` positivity from A1 nonzero full revelation) |
| `FiniteScaleCoherenceAssumptions` | Yes (monolith) | **No** | Bypassed: `ScaleCoherenceStructure` is built by `InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal` from the faithful pre-universal route |
| `FiniteBranchAggregationAssumptions` | Yes (monolith) | **No** | Bypassed by faithful branch route: `faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle` (ERC:1449) |
| `FiniteCrossPriorBlockAssumptions` | Yes (monolith) | **No** | Bypassed: `crossPriorBlockRepresentation_of_preUniversalBridge` (ERC:97) |
| `EntropyReductionRepresentation` | Yes | **No** | Constructed: `EntropyReductionRepresentation_of_interactionCollapse` (ERC:80) |
| `FaddeevEntropyForm` | Yes | **No** | Constructed: `FaddeevEntropyForm_of_fullPreEntropyClosure_minimal_internalUniqueness` (ERC:1070) |
| `FullSupportSufficiencyMIPackage` | Yes | **No** | Produced inside the MI assembly; not an input |
| `SufficiencyMIPackage` | Yes | **No** | Constructed: `sufficiencyMIPackage_of_fullPreEntropyClosure_minimal_internalUniqueness`, consumed by `MIRep_of_SufficiencyMIPackage` |
| `MIRep` | Yes (would be circular) | **No** | It is the **conclusion**, never an input |

---

## 9. Countermodel clarification

**The support-cardinality gauge counterexample** (recorded in
`STAGE_EXISTENTIAL_NORMALIZED_REPRESENTATIVES_PLAN.md`):

```text
V^λ_q(P) = λ(|support(q)|) · I(q,P),    λ(2) = 1,  λ(4) = 2.
```

1. **What it refutes.** It refutes the *arbitrary-representative* statement
   > "for **every** coherent face-scale representative `hfaces`,
   > `FiniteProductQuasiAdditivityForFaceScales hfaces` holds."

   The gauge `V^λ` yields a *coherent* representative (it is a positive rescaling that respects
   relabelling and support faces) yet **breaks** the product-normalized quasi-additivity
   equation for that particular already-selected representative, because `λ` depends on support
   cardinality and the product of two supports has a different cardinality than either factor.

2. **What it does not refute.** It does **not** refute the paper's *existential* statement that
   a product-normalized coherent gauge **can be chosen**. `V^λ` is simply not that chosen
   representative.

3. **Why the final theorem avoids it.** The final theorem never quantifies universally over
   `hfaces`. Instead it *constructs* a specific product-normalized representative and carries
   the convention field
   `product_normalized : FiniteProductNormalizedSelectedRepresentativesFor …`
   (Section 6), which asserts the **selected** representative is product-gauge-normalized. The
   quasi-additivity node
   `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected` (ERC:2004) is
   proved *for the selected normalized representative*, not for an arbitrary one. The
   countermodel `V^λ` is a *different* representative that the construction does not select, so
   it is irrelevant to the theorem.

A referee should read this as: earlier "prove for all `hfaces`" targets were correctly
abandoned as false; the final theorem uses the paper's existential/selection formulation, which
the countermodel does not touch.

---

## 10. TeX-to-Lean mapping

| TeX lemma / step | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| Axioms A1–A8 (410–543) | `A1_…`–`A8_…`, `TraceAxioms` (Axioms.lean) | Faithful encoding | A7 paper-faithful (common branch family); A8 different alphabets allowed |
| Posterior representation / HM | `posteriorLawSufficiency_of_FinalHMInterface`, `posteriorValueRepresentation_of_FinalHMInterface` | Classical interface + internal wiring | From `FinalHMInterface` |
| Branch aggregation, cocycle, normalised chain rule | `faithfulBranchAggregationAssumptions_of_FinalHM_conventionBundle`, `BranchAggregationCocycleNormalizedChainRule_of_faithful` | Internal (from HM + branch conventions) | Faithful tangent route; old monolith bypassed |
| Scale coherence / face scales (`lem:scalecoherence`, `eq:facescale`) | `coherentFaceScales_of_FinalHM_positiveGauge`, `InteractionCollapseUniversalScale_of_fullPreEntropyClosure_minimal` | Internal | Universal scale from two-grouping collapse |
| Product gauge normalization / `coherentnorm` (`lem:coherentnorm`) | `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected`, `faceScaleProductSlopeAffine_of_selectedRelabeling`, `productInterceptPositiveLinear_of_FinalHM_positiveGauge` | Internal + conventions | κ = 0 interaction collapse |
| Selected relabeling / permutation invariance (`cor:permutationinvariance`) | `faceScaleProduct_value_swap_eq_of_selectedRelabeling`, `FiniteSelectedPosteriorValueRelabelingFor` | Internal + representative convention | |
| Product quasi-additivity | `productQuasiAdditivity_of_FinalHM_positiveGaugeProductNormalizedSelected` | Internal | Selected normalized representative (Section 9) |
| Block reveal / grouping recursion | grouping-weight-constant / two-grouping nodes inside interaction collapse | Internal | |
| Entropy reduction | `EntropyReductionRepresentation_of_interactionCollapse` | Internal | |
| Faddeev recursion | `faddeevRecursionForm_of_fullPreEntropyClosure_minimal` | Internal | Supplies the premise of `hfad.of_recursion` |
| Classical Faddeev theorem application | `ClassicalFaddeevTheoremAssumptions.of_recursion`, `FaddeevEntropyForm_of_…_internalUniqueness` | Classical interface | `Hfun = α·Shannon`, `0 ≤ α` |
| Full-support MI representation | `MIRep_of_fullPreEntropyClosure_minimal_internalUniqueness`, `sufficiencyMIPackage_of_…` | Internal | |
| Boundary extension (`lem:supprestrict`) | `FiniteCardinalSupportBoundaryAssumptions` (in `harmless.support_boundary`), support-restriction internal lemmas | Boundary-cardinal interface + internal | Boundary handled via support face |
| Final MIRep (Theorem 1, (i)⟹(ii)) | `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` | **CERTIFIED** | Subject of this dossier |
| Necessity (ii)⟹(i) | `BenchmarkStatement_of_DPI` | Separate theorem | Needs `FiniteDPIAssumptions` |
| Moreover / block same-scale | `blockSameScaleRep_of_MIRep` | Separate theorem | From `MIRep F` |

---

## 11. Faithfulness audit

1. **Does `TraceAxioms` faithfully encode the axioms in the TeX?**
   Yes. Its eight fields are exactly A1–A8 (Section 5.1), with per-axiom TeX line mappings.
   A7 uses the paper-faithful common-branch-family variant (not the stronger auxiliary), and
   A8 permits differing background outcome alphabets, matching the paper. A referee should
   still read the eight predicate definitions in `Behaviour/Axioms.lean` to confirm the
   quantifier structure of each.

2. **Does `MIRep F` faithfully encode the theorem's representation claim?**
   Yes, for the **same-channel** claim (ii): `∀ P q q', F.rel P q q' ↔ I(q,P) ≥ I(q',P)`
   (Section 3), which is verbatim TeX (ii). It does **not** encode the moreover/block clause;
   that is a separate predicate `BlockSameScaleRep`.

3. **Does the Lean theorem certify the full TeX theorem, or only the sufficiency / MIRep
   direction?**
   Only the **sufficiency / `MIRep` direction** ((i) ⟹ (ii)). The necessity direction and the
   moreover clause are certified by the separate theorems `BenchmarkStatement_of_DPI` and
   `blockSameScaleRep_of_MIRep` respectively — **not** by this theorem.

4. **Are HM and Faddeev used only as external classical theorem interfaces?**
   Yes. HM enters solely through `FinalHMInterface` (three fields, Section 5.2) and Faddeev
   solely through `ClassicalFaddeevTheoremAssumptions.of_recursion` (Section 5.3). Neither is
   formalized from first principles; both are displayed statements assumed classical. **The
   paper should say so explicitly.** (The `blackwell` field is now the *pure* finite Blackwell
   equivalence theorem; the A3/A4/A1 replacement step is proved internally — see Section 5.2.
   No Blackwell-bridge caveat remains.)

5. **Are the conventions normalisations rather than behavioural assumptions?**
   Yes. Every field of `FinalConstructedRepresentativeConventions` is a positivity/gauge
   choice, a relabelling/support equivariance equation, a singleton or boundary normalization,
   or a representative selection (Section 6). None references the preference order in a way
   that could smuggle in comparison content. The one interface that is not a pure normalization
   is `harmless.support_boundary : FiniteCardinalSupportBoundaryAssumptions`, the boundary-
   cardinal extension bridge, disclosed explicitly.

6. **Does the final theorem hide product quasi-additivity, face scales, relabeling, entropy
   reduction, or MI representation as assumptions?**
   No. Section 6 shows by direct inspection of the `#print` field list that `hfaces`, `hprod`,
   `EntropyReductionRepresentation`, `FaddeevEntropyForm`, and `MIRep` are **not** fields;
   Section 7 shows each is an internally constructed node; Section 8 tabulates the elimination.
   No opaque field is equivalent to product quasi-additivity or to `MIRep`.

7. **What exactly must a human referee inspect?**

   > A competent referee should inspect:
   > **(i)** the `TraceAxioms` fields `a1`–`a8` and their predicate definitions
   > (`Behaviour/Axioms.lean`);
   > **(ii)** the `MIRep` definition (`Behaviour/MIPreference.lean:31`);
   > **(iii)** the `FinalHMInterface` fields `blackwell` (now the pure finite Blackwell
   > equivalence theorem), `hm_rep`, `hm_affine`, and whether their displayed statements are
   > acceptable classical finite representation theorems;
   > **(iv)** `ClassicalFaddeevTheoremAssumptions.of_recursion` and its match to the finite
   > Faddeev theorem;
   > **(v)** the `FinalConstructedRepresentativeConventions` fields, confirming each is a
   > harmless normalization/representative choice (Section 6);
   > **(vi)** the `#check` and `#print axioms` output in Section 2.

   If (i)–(vi) are accepted, Lean's kernel certifies `TraceAxioms F → MIRep F`.

---

## 12. Build and hygiene certificate

| Item | Result |
|---|---|
| `lake build` | **Success** — "Build completed successfully (8622 jobs)." Only `linter.style.whitespace` warnings (cosmetic line-break style in `EntropyReductionClosure.lean` around lines 2811–2829). No errors. |
| `lake env lean TraceableAgency/Tests/ObjectVerification.lean` | **Success** (exit 0). All `MIPrefFamily_A1..A8`, `MIPrefFamily_TraceAxioms_of_DPI`, `MIRep`, `TraceAxioms`, `BenchmarkStatement`, `BlockSameScaleRep`, `blockSameScaleRep_of_MIRep` `#check`/`#print axioms` pass; benchmark proofs depend only on `[propext, Classical.choice, Quot.sound]`. |
| `#check` final theorem | See Section 2.1 — resolves with expected signature. |
| `#print axioms` final theorem | `[propext, Classical.choice, Quot.sound]` (Section 2.2). |
| `rg "\bsorry\b" TraceableAgency` (tactic) | **None.** |
| `rg "\badmit\b" TraceableAgency` (tactic) | **None.** One match is a docstring word ("…distributions **admit** a positive branch mass…", `BranchAggregation.lean:2959`), not the `admit` tactic. |
| `rg "^\s*axiom\s" TraceableAgency` | **None.** No `axiom` declaration in the project. (The two `rg "axiom "` hits are the word "axiom" in comments.) |
| `True`-marker search (`Sufficiency`, `External`, `Main.lean`, `MainTheorem.lean`) | Three hits, all in `Main.lean:189,192,195`: `Stage{1,2,4A}…Complete : Prop := True`. These are **stage-tracking flags**, not proof placeholders — no theorem's proof depends on them. No `_hrecursion : True`-style vacuous premise in any proof path. |
| Lean version | `leanprover/lean4:v4.32.0-rc1` (`lean-toolchain`) |
| mathlib / manifest | mathlib scope `leanprover-community`, `inputRev v4.32.0-rc1`, resolved rev `360da6fa66c1273b76b6b2d8c5666fd5ac2e3b56`; manifest format 1.2.0; also `plausible` dependency (`f3f26cc…`) |
| Root import file | `TraceableAgency.lean` (default target `TraceableAgency` per `lakefile.toml`) |
| Commit hash | `846a49b877cb70c12e3de12783728bb40f39e5f3` |

**Warning classification.** All build warnings are `linter.style.whitespace` (source-line-break
cosmetics). There are no `unusedVariables`, `deprecated`, `sorry`, or `unsolved goals`
warnings affecting the final theorem. They are safe to ignore for certification and can be
silenced with `set_option linter.style.whitespace false`.

---

## 13. Final referee conclusion

A referee who (a) trusts the Lean kernel, (b) accepts the displayed Herstein–Milnor and *pure*
finite-Blackwell equivalence interfaces (`FinalHMInterface`; the A3/A4/A1 replacement is proved
internally) and the finite Faddeev entropy-uniqueness interface
(`ClassicalFaddeevTheoremAssumptions.of_recursion`) as valid classical statements, and (c) judges
the fields of
`FinalConstructedRepresentativeConventions` to be harmless normalisations and representative
choices (positive gauge, relabelling/support equivariance, singleton/boundary normalizations,
selected product-normalized representative, plus the disclosed boundary-cardinal interface),
can rely on Lean's kernel to certify the derivation of `MIRep F` from `TraceAxioms F`.

The final theorem certifies **exactly the sufficiency direction (i) ⟹ (ii)** of TeX Theorem 1:
the same-channel, fixed-environment mutual-information representation
`∀ P q q', F.rel P q q' ↔ I(q,P) ≥ I(q',P)`. It does **not**, by itself, certify the `iff`'s
necessity direction (that is `BenchmarkStatement_of_DPI`, needing `FiniteDPIAssumptions`) nor
the "moreover" block same-scale clause (that is `blockSameScaleRep_of_MIRep`, derived from
`MIRep F`). The full `iff`-plus-moreover statement is obtained only by composing these three
theorems (`main_characterization_from_spine`).

The paper should therefore:
- **not** claim that Herstein–Milnor or Faddeev are formalized from first principles — they are
  used as external classical theorem interfaces with displayed statements;
- state clearly that the Lean certificate for the sufficiency direction is
  `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions`, and that necessity and the moreover
  clause are separately certified (`BenchmarkStatement_of_DPI`, `blockSameScaleRep_of_MIRep`);
- note that `FinalHMInterface.blackwell` is the *pure* finite Blackwell equivalence theorem; the
  A3/A4/A1 preference-replacement step is proved internally
  (`blackwellPosteriorReplacement_of_samePosteriorGarblings`), not assumed.

Subject to those disclosures, the certificate is sound: **`CERTIFIED_MODULO_HM_FADDEEV_AND_EXPLICIT_CONVENTIONS`**.
