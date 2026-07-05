# Eliminating the product/gauge conventions — progress & plan

Branch: `eliminate-product-normalized-covariance`. Goal (per user): **all conventions proved or
internal**, not merely relabelled. Chosen mechanism (user-approved): an exact-relabel-covariance
(naturality) clause on the classical HM interface — same epistemic status/template as the
boundary-elimination `marginalValue_support_face` clause.

## Landed (committed, build green 8612 jobs, axioms [propext, Classical.choice, Quot.sound])

1. `e1a7fa5` — probe report + dossier note (t_n route abandoned; pinning is provable naturality).
2. `abd168f` — **`FinalHMRelabelCovariance`** clause on `FinalHMInterface`
   (`EntropyReductionClosure.lean` after line 84) + producer
   **`finiteSelectedPosteriorValueRelabeling_of_FinalHM_covariance`**: gives
   `FiniteSelectedPosteriorValueRelabelingFor hfaces` for any coherent face-scale rep whose `V`
   is defeq the constructed HM `V`, directly from covariance — bypassing the pinning.

## Verified in scratch (compile against real project, not yet in source)

- Covariance clause typechecks and threads (`FinalHMInterface` is never constructed concretely —
  only ever a hypothesis — so adding a field is safe: 0 construction sites).
- **Correctness finding:** `product_normalization_pinning` is *false at subsingleton A* (`V ≡ 0`
  ⇒ `0 = c·0` cannot force `c = 1`). So the field must be produced-and-dropped via `hsel`, never
  threaded through the pinning decomposition. The covariance producer does exactly this.
- **Constant gauge = 1** (`fun _ => 1`): gauged `V = 1 * raw V` by `rfl`; reduces the `hrel`
  obligation to **R1** (raw scale relabel-invariance) and `hsupport` to **R2** (raw support-face
  factorization).
- Gateway fact `relabelDist e (Dist.uniform) = Dist.uniform` — proved (`Fintype.card_congr e`).

## R1 DONE (committed, green 8612, axioms unchanged)

- `abd168f` covariance clause + producer; `<hash>` marginalValue_relabel field;
  `branchPathCoeff_relabel_of_marginalValue_relabel` (R1 core, hardest step);
  `scaleRelabel_of_FinalHM_covariance` (raw chain-scale relabel invariance).
- Key defeq used: `(faithful bundle).linear_part = finiteAffineLinearPartAssumptions_of_
  integralRepresentation (posteriorIntegralRepresentation_of_FinalHMInterface hhm)` by `rfl`,
  so R1 core applies to the bundle with no cast.
- Correctness note confirmed in scratch: `product_normalization_pinning` is false at subsingleton A;
  covariance → `hsel` directly (producer already in source).

## Remaining (the real work)

The intermediate routes (`…withPositiveGaugePreEntropy`, `…withProductNormalizedSelected…`) all
still *take* `hrel`/`hsupport`; they repackage, they do not avoid R1/R2. So to drop the gauge
family the two raw facts must be **proved**:

- **R1 — raw chain-scale relabel invariance:** `scale (relabel e q) = scale q`.
  `scale q = branchFullSupportBaseScale = branchCoeff q (uniform_A)` (ScaleCoherence.lean:236,248).
  With the gateway fact, reduces to **branchCoeff covariance** `branchCoeff (relabel q)(relabel r)
  = branchCoeff q r`. `branchCoeff` is built from the tangent-scalar layer, where
  `linearPart` is a value-difference (`FiniteAffineLinearPartAssumptions.value_difference`,
  BranchAggregation.lean:999) — so V-covariance should propagate to branchCoeff-covariance.
  Reachable; moderate. NEXT STEP.
- **R2 — raw support-face factorization (`eq:facescale`):** `branchCoeff q r = scale q /
  scale (r|supp)` for boundary r. Cross-cardinality; the deep one. Needs covariance + the
  support-restriction machinery from the boundary elimination (`wrapScale`,
  `restrictToSupport_eq_relabel_fullSupport`, etc.). May need a second support-face naturality
  clause on the HM interface (analogous to `marginalValue_support_face`).

Then: construct gauge = 1 internally; re-thread the ~10 QA consumers from
`finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives hnorm` to the
covariance-derived `hsel`; discharge `current_product_gauge` (A=B=1) and `singleton_interaction`
via the raw QA gauge-normalization step; land `singleton_slice` (SamePosteriorLaw on subsingleton
first factor). Finally add a new exported theorem
`MIRep_of_TraceAxioms_FinalHM_Faddeev_withCovariance` taking `FinalHMRelabelCovariance` and NO
gauge/product/singleton convention fields, and `#print` to confirm the convention structures are
absent.

## Scope note
This is a multi-session spine refactor (the boundary elimination — a leaf — took ~6 sessions).
Each landed piece keeps the tree green and the axiom footprint unchanged; commit per milestone.
