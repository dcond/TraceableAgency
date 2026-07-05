# Feasibility probe — eliminating `product_normalized` (make-or-break result)

**Verdict: the elimination FAILS as specified.** The make-or-break check the handoff
demanded (define `t_n` / `K_{n,m}` non-circularly and pin `c = 1` by construction) does not
go through, and — more importantly — the `t_n` construction targets the **wrong object** for
the field that actually needs eliminating. `product_normalized`'s hard half
(`product_normalization_pinning`) is the Lean substitute for the paper's *strict-product
convention*, and it is **not eliminable by the proposed cardinal-gauge construction**. The
honest outcome (the handoff's own documented fallback) is to record it as an irreducible
normalization, not an opaque assumption.

No source was changed. Baseline stays green (8622 jobs). This document is the probe report
requested by `HANDOFF_ELIMINATE_PRODUCT_NORMALIZED.md` ("Report the probe result before
committing to the full refactor").

---

## What the field actually is

`product_normalized : FiniteProductNormalizedSelectedRepresentativesFor …` bundles two halves
(`RepairedPreEntropyTargets.lean:37`, `CardinalPermutationInvariance.lean:29,58`):

1. **`actionbase_scalar`** — `∀ eA q, ∃ c > 0, ∀ eO P, V(relabel_eA q)(relabel P) = c·V(q)(P)`.
2. **`product_normalization_pinning`** — that `c` must be `1`.

Both are quantified over a **bijection** `eA : A ≃ B` (so `|A| = |B|`; `relabelDist` preserves
support size). Together they are exactly the paper's **exact relabelling invariance**
(`cor:permutationinvariance`, `empowerment_v5(1).tex:1680`) for the selected representative.

## Finding 1 — `t_n` / `K_{n,m}` do not exist and target a different object

`grep` across `TraceableAgency/External/*.lean`: **no** `t_n`, `K_{n,m}`, embedding-defect, or any
cardinality-indexed (`Fintype.card → ℝ`) gauge machinery exists anywhere. It would be built
from scratch.

More decisively: the paper's `t_n` (`lem:facescales`, tex:2269–2345) is the **cross-cardinality**
embedding defect `K_{n,m}` — the full-to-face scalar for an *injection* `B ↪ A` with `|B| < |A|`.
The Lean pinning field is a **same-cardinality** bijection. A cardinality-indexed rescaling
`ã = t_n·a` acts on a same-cardinality relabel scalar as `t_n / t_n = 1` — a **no-op**. So building
`t_n`:
- cannot *create* the same-cardinality `c = 1` property (it leaves that scalar untouched), and
- is not *needed* for it.

The handoff's `V^λ` countermodel (`λ(2)=1, λ(4)=2`) confirms this: it refutes `K_{n,m} = 1`
(cross-cardinality), **not** the same-cardinality `c = 1`. Indeed `V^λ` *satisfies* the
same-cardinality pinning, because `λ` depends only on support size and relabelling preserves
support size: `V^λ(relabel q)(relabel P) = λ(|supp q|)·I(q,P) = V^λ(q)(P)`, i.e. `c = 1`.

**So the proposed cardinal-gauge construction is orthogonal to the field it was meant to
discharge.** The `t_n` route is a dead end for `product_normalized`.

## Finding 2 — the real role of `product_normalized`: a substitute for strict-product

In the paper, `c = 1` (`cor:permutationinvariance`) is **derived from** coherent product
quasi-additivity (`lem:coherentnorm`), which is proved **without** `c = 1`. The Lean development
**inverts** this: the QA machinery *consumes* `product_normalized`. Precisely, `hsel :=
finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives product_normalized`
feeds the QA layer at exactly two structural places, both **same-cardinality product-reindexing
value-equalities**:

- `faceScaleProduct_value_swap_eq_of_selectedRelabeling` (`EntropyReductionClosure.lean:1835`) —
  uses `hsel` at the `prodComm : A×B ≃ B×A` bijection to get
  `V(q⊗r)(P⊗R) = V(r⊗q)(R⊗P)`. Consumed by `faceScaleProductSlopeAffine_of_selectedRelabeling`.
- `faceScaleTripleProductValueAssociativity_of_selectedRelabeling` (`SelectedRelabeling.lean:117`)
  — uses `hsel` at the `prodAssoc : (A×B)×C ≃ A×(B×C)` bijection to get
  `V((q⊗r)⊗s)(…) = V(q⊗(r⊗s))(…)`.

**Every** product swap/assoc *value-equality* in the codebase is derived from `V_relabel_eq`
(exact relabel invariance); there is no A5/A8-direct value-equality route (confirmed:
`EntropyReduction.lean:4689, 7015`, `ScaleCoherence.lean:3405`, all go through `hrelV`/`hsel`).

The reason is structural: the paper's QA proof gets assoc/comm value-equalities **for free** via
the *strict-product convention* — "finite products are identified by tuple notation, so
`(A×B)×C = A×B×C = A×(B×C)`" (tex:1563). In Lean, `(A×B)×C` and `A×(B×C)` are genuinely
different types, so a product-reindexing equality must be recovered from relabel invariance.
**`product_normalized` is the Lean stand-in for the strict-product tuple-identification
convention.**

## Finding 3 — the easy half is non-circular; the hard half is genuinely circular

- **`actionbase_scalar` (∃ c > 0): derivable, non-circular.** `relabel_rel_action_of_axioms`
  (`Relabeling.lean:507`) gives order-level relabel invariance from A5. `V` and `V∘relabel`
  then represent the same order, so differ by a positive affine transform (HM affine-utility
  uniqueness, `classicalFiniteAffineUtilityUniquenessAssumptions`, `ScaleCoherence.lean:2230`);
  `zero_normalized` kills the additive constant, leaving `c > 0`. Tools all present. (Not landed
  this session — it removes no exported field on its own; see below.)

- **`product_normalization_pinning` (`c = 1`): genuinely circular.** Pinning needs a value-level
  anchor `V(relabel q)(id) = V(q)(id)`, i.e. `H(relabel q) = H(q)`. The only proof of this is
  `fullRevelationValueForFaceScales_relabel_eq_selected` (`SelectedRelabeling.lean:84`), which
  takes `hsel` — the very thing being proved. The alternative anchor is QA (paper route), but
  the Lean QA cocycles need the assoc value-equality (Finding 2), which is itself
  relabel-invariance-strength. **Both routes close the loop.** No non-circular anchor exists.

The `V^λ` argument shows `c = 1` is false for a *general* coherent representative under
*cross*-cardinality maps, so some normalization is unavoidable. For *same*-cardinality
bijections the pinning is morally true (it holds for `V^λ`), but the `CoherentRelabelingFaceScales`
interface does not enforce that a representative is defined uniformly across isomorphic types, so
it cannot be proved from the structure alone — it must be *supplied*, exactly as the paper
*supplies* the strict-product convention.

## Why `c = 1` cannot come from the axioms alone (independence)

`c = 1` (the pinning half) is **provably independent** of `TraceAxioms` + the *bare*
`FinalHMInterface`. Counter-representative: take the honest value functional and multiply it by a
*type-dependent* positive constant — e.g. `5` on one fixed 2-element type `A₀`, `1` on all other
2-element types. This is still a valid `PosteriorValueRepresentation` (positive scaling preserves
order, keeps `zero_normalized`, respects posterior-law within each type), and for a bijection
`A₀ ≃ B` it gives `c = 1/5 ≠ 1`. The `FiniteHersteinMilnorAssumptions` interface (`HersteinMilnor.lean:575`)
relates `V` **only within a single type** (there is no cross-type clause), so it cannot rule this
out. Note `V^λ` does **not** break `c = 1` for bijections (λ depends on support size, which
bijections preserve), so `c = 1` is *true for the honest functional* — it just isn't derivable
from the opaque interface.

## Resolution route chosen: exact-relabel-covariance clause on the HM interface

The one honest way to make the conventions **proved rather than assumed** — without formalizing
the Herstein–Milnor construction itself (which the whole development abstracts as an interface) —
is to add an **exact-relabel-covariance (naturality) clause** to the classical HM interface:
```
V (relabelDist eA q) (relabelChannel eA eO P) = V q P.
```
This is a genuine property of the canonically-constructed HM value functional (the posterior-law
functional is natural in relabellings), of the *same epistemic status* as the
`marginalValue_support_face` coherence clause the completed **boundary elimination** added to the
integral-representation interface (see `BOUNDARY_ELIMINATION_PLAN.md`; accepted as "internal").
It is `FinitePosteriorValueRelabelingAssumptions` (`ScaleCoherence.lean:1435`), already present in
the codebase as an interface, now *provided by the HM data* instead of assumed downstream.

From that single clause, **as theorems** (not conventions):
- `product_normalization_pinning` (`c = 1`) and `actionbase_scalar` (∃ c > 0), via
  `selectedPosteriorValueRelabeling_of_valueRelabeling` — removes `product_normalized`.
- the product swap/assoc value-equalities (`prodComm`/`prodAssoc`), non-circularly.
- `scale_relabel` (raw relabel-invariance of the chain scale) and, with a constructed gauge,
  `support_scale`, `current_product_gauge` (A=B=1), and `singleton_interaction`.

Plus the standalone `singleton_slice` bounded sub-lemma (handoff verdict B).

The `t_n` cardinal-gauge refactor is **abandoned** as a dead end for the reasons above; the
covariance-clause route replaces it and discharges the whole coherent-gauge family.
