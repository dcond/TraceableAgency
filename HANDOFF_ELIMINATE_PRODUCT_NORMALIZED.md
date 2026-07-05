# Handoff — Eliminate the `product_normalized` convention

**Status of the project (as of this handoff).** The Lean development proves the sufficiency
direction of the main theorem, `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions`, on the
standard axioms `[propext, Classical.choice, Quot.sound]`, full build green (8622 jobs), zero
sorries. Repo: `dcond/TraceableAgency` (private), branch `main`.

The **cardinal-boundary convention** (`FiniteCardinalSupportBoundaryAssumptions`) was just
**eliminated** — its content is now proved (`field1_boundaryComplete`,
`hfun_eq_normalizedValue_idChannel_of_scale`, `field3_restricted_coarse_reveal`) and the top-level
theorem routes through `MIRep_of_TraceAxioms_HM_Faddeev_withPreEntropyInputs_noCardinal`. See
`BOUNDARY_ELIMINATION_PLAN.md` for that completed work; it is the template for the pattern
("construct the object, prove its properties, drop the assumption").

This handoff is about the **next** convention to remove.

---

## Objective

Remove `product_normalized` — the field

```lean
  product_normalized :
    FiniteProductNormalizedSelectedRepresentativesFor
      (coherentFaceScales_of_FinalHM_positiveGauge hhm … hax gauge scale_relabel support_scale)
```

from `FinalConstructedRepresentativeConventions`
(`TraceableAgency/External/EntropyReductionClosure.lean`, field at line ~4131), so the exported
theorem `MIRep_of_TraceAxioms_FinalHM_Faddeev_withConventions` no longer carries it — leaving the
proof depending only on the axioms (A1–A8), the classical interfaces (Herstein–Milnor / finite
Blackwell / Faddeev), and genuine gauge normalizations.

`#print` must confirm `FiniteProductNormalizedSelectedRepresentativesFor` (and its subfields
`FiniteSelectedActionbaseScalarFor`, `FiniteSelectedPermutationInvariancePinningFor`) are absent
from every convention structure the final theorem depends on. Axiom footprint unchanged.

---

## What the convention says (verbatim)

`TraceableAgency/External/RepairedPreEntropyTargets.lean:37`:

```lean
structure FiniteProductNormalizedSelectedRepresentativesFor.{v}
    {F : PrefFamily.{v}} (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  actionbase_scalar : FiniteSelectedActionbaseScalarFor hfaces
  product_normalization_pinning : FiniteSelectedPermutationInvariancePinningFor hfaces
```

- **`FiniteSelectedActionbaseScalarFor`** (`CardinalPermutationInvariance.lean:29`): relabelling
  the actions/outcomes rescales the face-scale value functional by **some** positive scalar `c`:
  ```
  ∀ eA q, ∃ c > 0, ∀ eO P,
    V (relabelDist eA q) (relabelChannel eA eO P) = c * V q P
  ```
- **`FiniteSelectedPermutationInvariancePinningFor`** (`CardinalPermutationInvariance.lean:58`):
  that scalar **must be 1** (exact relabelling invariance):
  ```
  ∀ eA q (c > 0), (∀ eO P, V (relabel…) = c * V q P) → c = 1
  ```

Here `V = hfaces.branch_result.branch_agg.value_rep.V` is the Herstein–Milnor face-scale value
functional. These two together are exactly the paper's **exact relabelling invariance**
(`cor:permutationinvariance`).

They are consumed via `finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives`
(`RepairedPreEntropyTargets.lean:48`), which produces `FiniteSelectedPosteriorValueRelabelingFor`,
feeding the product-quasi-additivity / slope machinery. Consumption sites in
`EntropyReductionClosure.lean`: lines ~2074, 2088, 2098, 2106, 4011, 4031, 4151, 4171.

---

## Which half is easy, which is hard

- **`actionbase_scalar` (∃ c > 0) is the easy half.** It is standard Herstein–Milnor: relabelling
  preserves the preference order (proved from A5 by `relabel_rel_action_of_axioms`,
  `TraceableAgency/External/Relabeling.lean:507`), so the two value functionals `V(relabel ·)` and
  `V(·)` represent the same order and agree up to a positive affine transform; the additive part is
  killed by the zero-normalization `V_q(δ_q)=0`. Expect this to be derivable non-circularly.

- **`product_normalization_pinning` (`c = 1`) is the hard half, and the real obstacle.**

---

## The obstruction (verified this session)

Pinning `c = 1` requires comparing the value functional across **two different priors** `q` and
`relabelDist eA q`. Cross-prior value comparison is precisely what `CrossPriorBlockRepresentation`
provides — but that object is built **from** product quasi-additivity, which is built **from**
`product_normalized`. So the tool that would pin `c` is downstream of the convention we're trying
to remove. **This is a genuine circularity**, flagged in the earlier session memory as
`GLOBAL_CARDINAL_NORMALIZATION_REQUIRED`.

Concretely, the natural anchor argument fails circularly:
- Take `actionbase_scalar` at `P = idChannel`, `eO = eA`: `V(relabel q)(relabel id) = c·V(q)(id)`.
- `relabelChannel e e idChannel = idChannel` (up to the equiv) — proved, e.g.
  `SelectedRelabeling.lean:98`, `ScaleCoherence.lean:5568`.
- So if `V(relabel q)(relabel id) = V(q)(id)` (full-revelation relabel invariance), then
  `c·V(q)(id) = V(q)(id)`, and `V(q)(id) ≠ 0` (from A1: `faceScale_idChannel_value_ne_zero_of_A1`,
  `ScaleCoherence.lean:3151`) gives `c = 1`.
- **BUT** the only existing proof of the anchor `V(relabel q)(relabel id) = V(q)(id)` is
  `fullRevelationValueForFaceScales_relabel_eq_selected` (`SelectedRelabeling.lean:84`), which takes
  `hsel : FiniteSelectedPosteriorValueRelabelingFor` — i.e. it already assumes exact relabelling
  invariance. Circular.

**The `V^λ` countermodel confirms it is not derivable for an arbitrary representative.** The gauge
`V^λ_q(P) = λ(|supp q|)·I(q,P)` with `λ(2)=1, λ(4)=2` is a *coherent* face-scale representative for
which `c ≠ 1` (relabelling between action sets of the same cardinality is fine, but the scalar is
not forced to 1 for a badly-chosen gauge). So `c = 1` is **false for a general coherent
representative** — it holds only for the *cardinality-normalized* one. This mirrors the boundary
field: the escape is **construction, not derivation**.

---

## The paper's construction (the target)

`lem:facescales` (`empowerment_v5(1).tex`, lines 2269–2345, esp. 2330–2344) builds the exact-
relabelling-invariant representative by a **cardinality-indexed rescaling**:

> Define `K_{n,ℓ} = K_{n,m} K_{m,ℓ}` (a cocycle in cardinalities). Put `t_n := K_{n,2}`, `t_2 = 1`,
> so `K_{n,m} = t_n / t_m`. Replace every scale on an `n`-point action set by
> `ã_q^A := t_n · a_q^A`. Then the embedding defect `K̃_{n,m} = K_{n,m} · t_m/t_n = 1`.
> "The rescaling is common to all priors on a fixed action set, so it leaves all within-set cocycle
> ratios unchanged; because `t_n` depends only on cardinality, it also preserves exact relabelling
> invariance." Singleton target scales are arbitrary (singleton continuation terms are zero).

So the objective becomes: **construct the cardinal-gauge-normalized face-scale representative** —
rescale `V` (equivalently the face scales) by a factor `t_n` depending only on the action-set
cardinality `n` — for which `c = 1` holds **by construction**, then discharge
`FiniteSelectedPermutationInvariancePinningFor` from that construction.

Note the earlier boundary elimination already introduced a scale-wrapper pattern
(`wrapScale` / `boundaryCompleteScale`, `EntropyReductionClosure.lean`) — the same "wrap the
ScaleCoherenceStructure, re-prove its four fields" mechanics apply, but the wrapping factor here is
`t_n` (cardinality-indexed) rather than a support-face completion.

---

## What is needed (my assessment of the route)

This is a **spine-level refactor of the face-scale layer**, materially larger and riskier than the
boundary elimination (which was a leaf). Concretely:

1. **Define the cardinality cocycle `K_{n,m}` and `t_n`.** The `K_{n,m}` is the embedding defect
   between value functionals on `m`-point and `n`-point action sets. Need: extract it from the
   existing face-scale / product machinery (the "embedding defect" `eq:embeddingdefect` in the
   paper). This requires locating where cross-cardinality embeddings are already handled. `t_n` is
   then a `ℕ → ℝ` (or `Fintype card → ℝ`) defined by `K_{n,2}`. Watch: this is a real construction
   with its own cocycle proof `K_{n,ℓ} = K_{n,m} K_{m,ℓ}`.

2. **Build the rescaled representative** `Ṽ_q^A := t_{|A|} · V_q^A` (a wrapper over the face-scale
   `CoherentRelabelingFaceScalesStructure`, analogous to `boundaryCompleteScale`). Re-prove the
   coherent-relabelling and face-scale fields for the wrapper. Key subtlety the paper flags:
   because `t_n` depends only on cardinality (not the prior), **within-set cocycle ratios are
   unchanged** — so `branchCoeff_factorization`, `scale_universal`, etc. transfer. This is the crux
   that should make the wrapper's fields provable from the originals + `t` being cardinality-only.

3. **Prove `c = 1` for the rescaled representative.** With `Ṽ`, relabelling between same-cardinality
   sets has `t_n/t_n = 1`, so exact invariance holds by construction. This discharges
   `FiniteSelectedPermutationInvariancePinningFor` for `Ṽ` — no cross-prior/`hprod` needed, breaking
   the circularity.

4. **Prove `actionbase_scalar` for `Ṽ`** (the ∃ c > 0 half) — from HM + `relabel_rel_action_of_axioms`
   (A5). Should be independent of the pinning and non-circular.

5. **Thread the rescaled representative** through the product-quasi-additivity / slope / interaction
   layer and the final MI route, dropping `product_normalized` from `FinalConstructedRepresentative-
   Conventions`, exactly as `noCardinal` did for the boundary field. Re-point
   `finiteSelectedPosteriorValueRelabeling_of_productNormalizedRepresentatives` consumers to the
   constructed relabelling invariance.

### Reusable tools already in the codebase
- `relabel_rel_action_of_axioms` (`Relabeling.lean:507`) — relabel invariance of the **preference**
  from A5, no product data. Upstream of everything; the non-circular seed.
- `normalizedValue_relabelAction_of_crossPrior` (`EntropyReductionClosure.lean:2418`) — normalized-
  value relabel invariance (but needs `hcross`; likely circular for this purpose — use with care).
- `finiteSelectedPosteriorValueRelabeling_of_actionbase_permutationinvariance`
  (`CardinalPermutationInvariance.lean:84`) — assembles `FiniteSelectedPosteriorValueRelabelingFor`
  from `actionbase_scalar` + `pinning`. This is the target output; supply the two halves from the
  construction instead of as assumptions.
- `fullRevelationValueForFaceScales_relabel_eq_*`, `faceScale_idChannel_value_ne_zero_of_A1`
  (`ScaleCoherence.lean:3151`), `relabelChannel e e idChannel = idChannel` lemmas — the anchor
  ingredients, once the anchor is proved non-circularly (i.e. from the `t_n` construction).

### Main risks / open questions
- **Does the `t_n` cocycle exist non-circularly?** Step 1 needs the cross-cardinality embedding
  defect `K_{n,m}` to be definable from the face-scale layer *without* the product/cross-prior
  bridge. If it secretly needs `hprod`, the circularity just moves — this is the make-or-break
  check to do first.
- **Cardinality vs type:** Lean action sets are arbitrary `Type u` with `[Fintype]`; `t_n` is
  indexed by `Fintype.card`. Rescaling by `t_{card A}` and proving relabel invariance
  (`card A = card B` under `A ≃ B`) is routine but touches every face-scale field's proof.
- **Singleton handling:** paper sets singleton target scales arbitrarily (continuation terms zero);
  mirror the existing singleton-convention pattern.

### Recommended first step for the next session
Before any refactor, **timebox a feasibility probe**: try to *define* `t_n` / `K_{n,m}` from the
existing face-scale embedding machinery and check it does not require `hprod` or a
`CrossPriorBlockRepresentation`. If `K_{n,m}` is constructible from A5 + HM + the coherent-face-scale
structure alone, the elimination is viable by the boundary-field pattern. If it bottoms out at the
cross-prior bridge, then `product_normalized` is (like a genuine gauge choice) **not eliminable**
without first eliminating product quasi-additivity itself, and the honest outcome is to document it
as an irreducible construction/normalization rather than an opaque assumption.

---

## Session guidance
- The boundary elimination is the working template — read `BOUNDARY_ELIMINATION_PLAN.md` end-to-end
  first; the `wrap*` + `*_ofFacts` + `*_ofCrossFacts` + reorder-to-avoid-forward-reference mechanics
  all recur here.
- Work scratch-first (`/tmp/*.lean` importing `TraceableAgency.External.EntropyReductionClosure`),
  port only compiling blocks, keep the tree green, commit per milestone.
- `#print axioms` after every landed piece; the goal is unchanged footprint
  `[propext, Classical.choice, Quot.sound]`.
- Watch the forward-reference trap: new producers must be defined *before* the theorems that use
  them (the boundary work required relocating a 1100-line block for this reason).
