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
  `hpair` are **derived** from `value_relabel` via
  `faceScaleTripleProductValueAssociativity_of_valueRelabeling` and
  `faceScaleProductSlopeAffine_of_selectedRelabeling
   (selectedPosteriorValueRelabeling_of_valueRelabeling …)`.
* The intercept piece of `hpair` is derived via
  `productInterceptPositiveLinear_of_FinalHM_positiveGauge`.
* The boundary-support content is proved rather than assumed; the route goes
  through `MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal`.

---

## 4. Remaining-assumption table (what `hres` still carries)

| Field           | Interpretation                                              | Status                                   |
| --------------- | ----------------------------------------------------------- | ---------------------------------------- |
| `branch`        | faithful-branch representative-choice bundle                | representative choice                    |
| `gauge`         | positive face-scale gauge                                   | representative choice                    |
| `scale_relabel` | scale relabel-equivariance equation                         | harmless normalization                   |
| `support_scale` | raw face-scale equation `eq:facescale`                      | **RESIDUAL — genuine cross-cardinality content** |
| `value_relabel` | `FinitePosteriorValueRelabelingAssumptions` (V relabel-coherent) | **RESIDUAL interface** |
| `harmless`      | `singleton_slice` + `pre_entropy`                           | `pre_entropy` is **RESIDUAL** |

### Explicit residual-interface disclosure

The following are **residual interfaces**, not proved from `TraceAxioms + HM +
Faddeev` in this route:

1. **`value_relabel`** (`FinitePosteriorValueRelabelingAssumptions`). States that
   the posterior value representation is coherent under finite relabelling. It is
   mathematically natural and should plausibly follow from relabelling invariance
   / HM uniqueness, but there is currently **no constructor** producing it from
   `hhm + hax`. It feeds both `htriple` and the selected-relabelling package used
   for the slope-affinity piece of `hpair`.
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
