# Certification note: product-gauge-free, boundary-support-free MI route

**Scope of claim.** This note certifies exactly one thing: the exported
sufficiency theorem below reaches `MIRep F` **without** the product-gauge
normalization fields and **without** the cardinal boundary-support assumption
that the older top-level route (`FinalConstructedRepresentativeConventions`)
carried.

It does **not** claim the theorem is convention-free. Three residual interfaces
remain and are disclosed explicitly in §4: `value_relabel`, `support_scale`, and
`harmless.pre_entropy`.

The precise, honest claim is:

> The current Lean certificate is **product-gauge-free** and
> **boundary-support-free**, modulo residual representative / relabelling /
> pre-entropy conventions.

---

## 1. Exact `#check` and `#print axioms`

```
#check @MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductConventions

MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductConventions :
  ClassicalFaddeevTheoremAssumptions →
    ∀ {F : PrefFamily} (hhm : FinalHMInterface) (hax : TraceAxioms F)
      (hres : ResidualConventionsWithoutProductGauge hhm hax), MIRep F
```

```
#print axioms MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductConventions

'TraceableAgency.MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductConventions'
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

`lake build TraceableAgency.External.EntropyReductionClosure` completes
successfully (8612 jobs). The file contains **no** `sorry`, `admit`, or `axiom`
declarations.

---

## 2. Exact fields of `ResidualConventionsWithoutProductGauge`

```
structure ResidualConventionsWithoutProductGauge
    {F : PrefFamily.{u}} (hhm : FinalHMInterface.{u}) (hax : TraceAxioms F) where
  branch        : FinalFaithfulBranchConventions hhm
  gauge         : PositiveFaceScaleGauge.{u}
  scale_relabel : «scale relabel-equivariance equation»
  support_scale : «raw face-scale equation (eq:facescale)»
  value_relabel : FinitePosteriorValueRelabelingAssumptions.{u}
  harmless      : FinalHarmlessConventions «gaugeTransformed rep» «cobGauge QA»
```

where `FinalHarmlessConventions` has exactly two fields:

```
structure FinalHarmlessConventions hfaces hprod : Prop where
  singleton_slice : FiniteFaceScaleSingletonSliceAffineConventionFor hfaces
  pre_entropy     : PreEntropyRepresentativeGaugeConventions hfaces hprod
```

---

## 3. Before / after — fields REMOVED from the top-level bundle

Old top-level bundle: `FinalConstructedRepresentativeConventions hhm hax`.
New top-level bundle: `ResidualConventionsWithoutProductGauge hhm hax`.

| Field in old bundle             | Type                                             | Status in new bundle |
| ------------------------------- | ------------------------------------------------ | -------------------- |
| `product_normalized`            | `FiniteProductNormalizedSelectedRepresentativesFor` | **REMOVED**          |
| `current_product_gauge`         | `FiniteFaceScaleProductGaugeConventionFor`       | **REMOVED**          |
| `singleton_interaction`         | `FiniteFaceScaleSingletonInteractionConventionFor` | **REMOVED**          |
| `FiniteCardinalSupportBoundaryAssumptions` | (boundary-support field, already dropped upstream in the `noCardinal` route) | **REMOVED**          |

How the removed content is now discharged:

* Product quasi-additivity for the working representative is **constructed
  internally** by `productQuasiAdditivity_cobGauge`: the coboundary gauge
  `cobCoherentGauge` (built from the associativity cocycle `coeff_assoc_A`)
  normalizes the left product coefficient, and the right coefficient is
  **proved** `= 1` from the product-swap symmetry. No product-normalization
  convention is assumed.
* `htriple` (triple-product value associativity) and the slope-affinity piece of
  `hpair` are **derived** from `selected_value_relabel` via
  `faceScaleTripleProductValueAssociativity_of_selectedRelabeling` and
  `faceScaleProductSlopeAffine_of_selectedRelabeling`.
* The intercept piece of `hpair` is derived via
  `productInterceptPositiveLinear_of_FinalHM_positiveGauge`.
* The boundary-support content is proved rather than assumed; the route goes
  through `MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal`.

### Relabelling residual weakened (this pass)

The relabelling residual was **narrowed** from the all-representations,
universe-polymorphic `FinitePosteriorValueRelabelingAssumptions` (invariance of
*every* posterior-value representation of *every* preference family) to the
per-representative `FiniteSelectedPosteriorValueRelabelingFor` for *the one*
constructed coherent representative.  Verified by `#print` (`pp.all`): the
fully-elaborated `ResidualConventionsWithoutProductGauge` contains **0**
occurrences of `FinitePosteriorValueRelabelingAssumptions`.  The whole
coboundary-gauge machinery (`cobCoherentGauge`, `productQuasiAdditivity_cobGauge`
and every helper) was re-plumbed to consume the weaker per-representative clause
— every internal use of the relabelling hypothesis was already instantiated at
that representative, and the two gauge-transform associativity uses now go
through `faceScaleTripleProductValueAssociativity_gaugeTransform` (which needs
only `htriple` + the coherent gauge).

Furthermore, `finitePosteriorValueRelabeling_blockedOn_pinning`
(EntropyReductionClosure.lean) formally reduces the *entire* content of
full-support selected relabelling to the single scalar-pinning obligation
`c = 1`: from the classical HM affine representation and the proved,
hypothesis-free finite affine-utility uniqueness theorem, the actionbase scalar
(`V ∘ relabel = c · V`, `c > 0`) and the outcome-relabelling half are both
**derived**.  So the only genuinely residual content of relabelling is the
scalar pinning `c = 1`.

---

## 4. Remaining-assumption table (what `hres` still carries)

| Field           | Interpretation                                              | Status                                   |
| --------------- | ----------------------------------------------------------- | ---------------------------------------- |
| `branch`        | faithful-branch representative-choice bundle                | representative choice                    |
| `gauge`         | positive face-scale gauge                                   | representative choice                    |
| `scale_relabel` | scale relabel-equivariance equation                         | harmless normalization                   |
| `support_scale` | raw face-scale equation `eq:facescale`                      | **RESIDUAL — genuine cross-cardinality content** |
| `selected_value_relabel` | `FiniteSelectedPosteriorValueRelabelingFor` (relabel-coherence of *the* constructed representative) | **RESIDUAL interface (narrowed; reduces to scalar pinning `c = 1`)** |
| `harmless`      | `singleton_slice` + `pre_entropy`                           | `pre_entropy` is **RESIDUAL** |

### Explicit residual-interface disclosure

The following are **residual interfaces**, not proved from `TraceAxioms + HM +
Faddeev` in this route:

1. **`selected_value_relabel`** (`FiniteSelectedPosteriorValueRelabelingFor` for
   the constructed representative). States that *that* posterior-value
   representative is invariant under simultaneous action+outcome relabelling.
   Its actionbase scalar (`c > 0`) and its outcome half are provable from
   HM/axioms; the sole non-derived content is the scalar pinning `c = 1` (see
   `finitePosteriorValueRelabeling_blockedOn_pinning`).  In the paper `c = 1`
   follows from product quasi-additivity, but in the coboundary-gauge route the
   QA is itself built from relabelling, so discharging the pinning that way would
   be **circular** — hence it remains a genuine residual here.  This is strictly
   weaker than the earlier all-representations
   `FinitePosteriorValueRelabelingAssumptions`.
2. **`support_scale`** (the raw face-scale equation `eq:facescale`). This is
   genuine cross-cardinality content, not merely a positive-gauge choice. It
   still requires either a proof or honest disclosure; here it is disclosed.
3. **`harmless.pre_entropy`** (`PreEntropyRepresentativeGaugeConventions`).
   The product-gauge conventions are gone, but the pre-entropy /
   universal-scale representative conventions remain a convention package.

`branch` and `gauge` are representative/gauge choices that are probably
acceptable but ideally should eventually be constructible.

---

## 5. Non-circularity note

The discipline maintained throughout: value identities are established before
interaction collapse, scale identities are collapse inputs. No input to
interaction collapse is derived from the output of interaction collapse. In
particular, `value_relabel` is a value-level coherence clause consumed *before*
collapse; it is not obtained from the universal-scale output.

---

## 6. `support_scale` ELIMINATED (proved, not weakened or blocked)

A further route removes the `support_scale` residual entirely by fixing the
positive face-scale gauge to the **cardinal gauge** `cardinalGauge` (the
cardinality-indexed scale `t_n := cardDefect n 2`).  For that gauge the raw
face-scale equation `eq:facescale` — the whole content of the `support_scale`
field — is a **theorem** (`cardinalGauge_hsupport`), and so is the scale
relabel-equivariance (`cardinalGauge_hrel`).

Exported theorem and bundle:

```
#check @MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductOrSupportScaleConventions

MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductOrSupportScaleConventions :
  ClassicalFaddeevTheoremAssumptions →
    ∀ {F : PrefFamily} (hhm : FinalHMInterface) (hax : TraceAxioms F)
      (hres : ResidualConventionsWithoutProductGaugeOrSupportScale hhm hax),
      MIRep F

#print axioms …
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Fields of `ResidualConventionsWithoutProductGaugeOrSupportScale` (verified by
projection existence/absence and `#print` with `pp.all`):

| Field                    | Status |
| ------------------------ | ------ |
| `branch`                 | present |
| `selected_value_relabel` | present (per-representative relabelling, reduces to scalar pinning `c = 1`) |
| `harmless`               | present (`singleton_slice` + `pre_entropy`) |
| `gauge`                  | **REMOVED** (fixed to `cardinalGauge`) |
| `scale_relabel`          | **REMOVED** (proved: `cardinalGauge_hrel`) |
| `support_scale`          | **REMOVED** (proved: `cardinalGauge_hsupport`) |

The `.support_scale` and `.gauge` projections do not exist on the new bundle
(unknown-constant error), and `FiniteSupportFaceScaleAssumptionsFor` has **0**
occurrences in the fully-elaborated bundle.

How `support_scale` is discharged (`cardinalGauge_hsupport`): with the cardinal
gauge `g q = g r = t_n` cancel on the left; `branchCoeff q r = boundaryCoeff q r`;
the general embedding-defect reduction (`general_defect`) gives
`boundaryCoeff q r · scale(r|supp) = scale q · cardDefect n m`; and the cocycle
`cardDefect n m = t_n / t_m` (`cardDefect_eq_ratio`) with `t_m = g(r|supp)`
closes the equation.  This uses support restriction, the embedding/boundary
extension defect, gauge positivity (`cardScaleT_pos`), and relabelling-support
equivariance — i.e. **Option 1** of the target.

Updated honest claim for this route: **product-gauge-free, boundary-support-free,
and raw-face-scale-free (`support_scale` discharged by the cardinal gauge),
modulo residual per-representative relabelling and pre-entropy conventions.**

---

## 7. `selected_value_relabel` ELIMINATED (proved outright, no gauge, no pinning)

The relabelling residual is removed entirely.  The key fact is that the
posterior-value functional has an **integral representation**
(`FinitePosteriorIntegralRepresentationAssumptions`):
`V q E = ∫ marginalValue q  d(posterior law of (q, E))` (`value_eq_integral`),
and its representing test function is **relabel-natural**
(`marginalValue_relabel`: `marginalValue (relabel q) (relabel d) = marginalValue q d`).
Since the posterior-law integral is relabel-covariant
(`posteriorLawIntegral_relabelChannel`), these compose to

```
V (relabel q) (relabel E) = V q E          (V_relabel_eq_of_integralRepresentation)
```

outright — the value-level relabelling scalar is `1`, with **no gauge, no product
quasi-additivity, and no scalar-pinning assumption**.  (This is the cleanest form
of the earlier `finitePosteriorValueRelabeling_blockedOn_pinning` reduction: the
pinning obligation `c = 1` is discharged by the HM interface's own
`marginalValue_relabel` naturality clause, which was already present for the
`support_scale` (R1) elimination.)

For the cardinal-gauge coherent representative the value functional is
`g(q) · V_HM q E` with `g = cardinalGauge` cardinality-only (relabel-invariant,
`cardinalGauge_gaugeRel`); the gauge factors cancel under a bijection (same
cardinality) and `V_HM` is invariant, so `selectedValueRelabel_of_cardinalGauge`
proves `FiniteSelectedPosteriorValueRelabelingFor` for that representative.

Exported theorem and bundle:

```
#check @MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductSupportOrValueRelabelConventions

MIRep_of_TraceAxioms_FinalHM_Faddeev_noProductSupportOrValueRelabelConventions :
  ClassicalFaddeevTheoremAssumptions →
    ∀ {F : PrefFamily} (hhm : FinalHMInterface) (hax : TraceAxioms F)
      (hres : ResidualConventionsWithoutProductGaugeOrSupportScaleOrValueRelabel hhm hax),
      MIRep F

#print axioms …
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

Fields of `ResidualConventionsWithoutProductGaugeOrSupportScaleOrValueRelabel`:

| Field                    | Status |
| ------------------------ | ------ |
| `branch`                 | present |
| `harmless`               | present (`singleton_slice` + `pre_entropy`) |
| `gauge`                  | **REMOVED** (fixed to `cardinalGauge`) |
| `scale_relabel`          | **REMOVED** (proved: `cardinalGauge_hrel`) |
| `support_scale`          | **REMOVED** (proved: `cardinalGauge_hsupport`) |
| `selected_value_relabel` | **REMOVED** (proved: `selectedValueRelabel_of_cardinalGauge`) |

Verified: the `.selected_value_relabel` projection does not exist on the new
bundle (unknown-constant error), and `FiniteSelectedPosteriorValueRelabelingFor`
has **0** occurrences in the fully-elaborated bundle.

Updated honest claim for this route: **product-gauge-free, boundary-support-free,
support-scale-free, and value-relabel-free, modulo the pre-entropy representative
conventions** (`harmless.pre_entropy`), which remain the sole substantive residual
alongside `branch`.
