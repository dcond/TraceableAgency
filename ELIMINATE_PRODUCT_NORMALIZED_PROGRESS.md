# ✅ Tier C cocycle PROVEN (2026-07-05) — support_scale reduction remains

**`cardDefect_cocycle` is DONE (zero sorries, axioms [propext,Classical.choice,Quot.sound], green 8622):**
`cardDefect n m · cardDefect m ℓ = cardDefect n ℓ` (2≤ℓ<m<n). This was the last HARD blocker.
Proved via chaining cardDefect_transport at (n,ℓ)+(n,m) through canonBoundary_nest + supportInclude_nest,
bridging the m-face by canonBoundary_face_uniform + supp≃canonType relabel (marginalValue_relabel) +
transport at (m,ℓ), cancelling the A1-nonzero tangent. All helper bricks in source:
actionPushforward_pure_comp, canonInclKernel_comp, canonBoundary_nest, nestSupportMap,
supportInclude_nest, cardDefect_transport, relabelDist_eq_actionPushforward, cBface_eq_relabel_uniform,
canonIncl_eq_supportInclude, push_nest_eq_relabel.

**Also landed:** cardScaleT (t_n := cardDefect n 2), cardDefect_eq_ratio (cardDefect n m = t_n/t_m
via cocycle), faithful_scale_pos (scale q > 0 all q).

**REMAINING for support_scale (mechanical but Equiv-heavy, ~200 lines):**
1. `alignEquiv r : A ≃ canonType (card A)` [DEFINED, compiles] sending supp r → first-(card supp).
   Need `alignEquiv_lt_of_pos` (support maps below m) — friction: Equiv.sumCompl/sumCongr defeq
   (supportSubtype r vs {a//0<r a}); use `Fintype.equivFinOfCardEq`-style or `change` to align types.
2. General defect lemma: `boundaryCoeff q r = scale q · cardDefect (card A)(card supp r)` for
   nondeg full-support q, nondeg boundary r. Route: relabel A≃canonType n via alignEquiv (boundaryCoeff_
   relabel + scale relabel), giving r' with supp=first-m; q-indep (boundaryCoeff_qIndep) to u_n;
   within-face r-independence (r'|supp vs uniform, same support subtype ≃, via transport same
   pushSignedIncl + branchPathCoeff face-ratio) to cB n m; = cardDefect n m.
3. cardinalGauge q := cardScaleT (card A) / scale q [positive via faithful_scale_pos + t_n>0;
   relabel-inv (hrel) via scale relabel + card]. hsupport: reduces (compute) to the general defect
   lemma + cardDefect_eq_ratio. hgaugeRel for covariance producer: cardScaleT(card A)/scale relabel-inv.
4. Assemble coherentFaceScales_of_FinalHM_positiveGauge with cardinalGauge; new exported theorem
   dropping support_scale; #print verify.

NO COUNTEREXAMPLE — the result is TRUE; its hardest component (cocycle) is proven. Remaining is
Equiv-plumbing-heavy assembly.

---

# Tier C cocycle — ALL BRICKS LANDED, only final assembly remains (2026-07-05)

Committed green (8622), axioms clean. Reusable bricks for the defect cocycle now ALL in source:
- actionPushforward_pure_comp (deterministic pushforward composition)
- canonInclKernel_comp (Fin.castLE inclusions compose)
- canonBoundary_nest (cB n ℓ = pushforward (cB m ℓ) via m↪n)
- nestSupportMap + supportInclude_nest (ℓ-face support includes through m-face)
- cardDefect_transport (η(mV(u_n)∘push_{cB n m}) = cardDefect n m · η(mV((cB n m)|supp)))
- (earlier) canonBoundary_face_uniform/_scale_eq_one, boundaryCoeff_qIndep/_relabel, marginalValue_relabel

**Cocycle assembly (100-150 lines, the ONLY remaining step for support_scale):**
`cardDefect n m · cardDefect m ℓ = cardDefect n ℓ` (2≤ℓ<m<n). Proof:
1. A1 nonzero tangent η on supp(cB n ℓ)≃canonType ℓ (nondeg ℓ≥2).
2. cardDefect_transport at (n,ℓ): η(mV(u_n)∘push_{cB n ℓ}) = cardDefect n ℓ · η(mV((cB n ℓ)|supp)).
3. supportInclude_nest: push_{cB n ℓ} d = push_{cB n m}(pushforward d (pure∘nestSupportMap)).
   So LHS = η'(mV(u_n)∘push_{cB n m}) with η' = nest-pushed η.
4. cardDefect_transport at (n,m) with η': = cardDefect n m · η'(mV((cB n m)|supp)).
5. Bridge: η'(mV((cB n m)|supp)) = cardDefect m ℓ · η(mV((cB n ℓ)|supp)), via
   (cB n m)|supp = uniform-on-supp [canonBoundary_face_uniform], relabel supp(cB n m)≃canonType m,
   boundaryCoeff_relabel + cardDefect_transport at (m,ℓ). [THE delicate 50 lines]
6. Combine 2,4,5; cancel η(mV((cB n ℓ)|supp))≠0 (A1). ⟹ cocycle.

Then MECHANICAL: t_n := cardDefect n 2 (t_2:=1, need cardDefect 2 2... handle base); gauge
q:=t_{card A}/scale q (positive; relabel-inv via R1+card); hrel (=t_{card A}); hsupport (=cocycle
+ q-indep + relabel); assemble coherentFaceScales; exported theorem dropping support_scale.

---

# Tier C in progress — support_scale via t_n cocycle (2026-07-05)

Confirmed AGAIN: support_scale (raw eq:facescale) genuinely needs the t_n cardinal-gauge cocycle
(covariance is about bijections; K(ι) is about inclusions — not forced to 1). It feeds wrapCross in
the boundary-elimination MI spine (line ~4189), so it is load-bearing.

**Exact gauge design (verified sufficient):** `gauge q := t_{card A} / scale q` where
`t_n := cardDefect n 2`. Then g q·scale q = t_{card A} (cardinal), g(r|supp)·scale(r|supp)=t_m,
scale(boundary r)=1, so support_scale ⟺ boundaryCoeff(u_n,r)=t_n/t_m, which via q-indep (R2a) +
boundaryCoeff relabel-inv reduces to cardDefect n m = t_n/t_m = cardDefect n 2 / cardDefect m 2,
i.e. the COCYCLE cardDefect n m · cardDefect m ℓ = cardDefect n ℓ (ℓ≤m≤n).

**Tier C bricks LANDED (green 8622):**
- canonBoundary + apply/pos/nondeg/boundary/support_nonempty/supportEquiv (support ≃ canonType m)
- scale_uniform_eq_one, canonBoundary_face_uniform, canonBoundary_face_scale_eq_one
- cardDefect n m := boundaryCoeff(u_n)(canonBoundary n m) + cardDefect_pos
- **canonBoundary_nest**: cB n l = pushforward (cB m l) (canonInclKernel n m) — GEOMETRIC HEART
- (earlier) boundaryCoeff_qIndep_of_FinalHM, boundaryCoeff_relabel_of_FinalHM, pushSignedIncl+lemmas

**REMAINING (the cocycle — ~150 lines, THE last blocker):**
`cardDefect n m · cardDefect m ℓ = cardDefect n ℓ`. Recipe:
- transport at (u_n, cB n ℓ) with tangent η on supp(cB n ℓ) ≃ canonType ℓ (A1-nonzero, ℓ≥2);
- pushSignedIncl(cB n ℓ) η factors through the m-face via canonBoundary_nest (supp inclusion
  supp(cB n ℓ)→supp(cB n m) exists: first-ℓ ⊂ first-m);
- transport at (u_n, cB n m): linPart(u_n)(push...) = cardDefect n m · linPart((cB n m)|supp)(...);
- (cB n m)|supp = uniform (canonBoundary_face_uniform), pulled to canonType m = u_m;
- transport at (u_m, cB m ℓ): = cardDefect n m · cardDefect m ℓ · linPart((cB m ℓ)|supp) η;
- directly = cardDefect n ℓ · linPart((cB n ℓ)|supp) η; cancel A1-nonzero tangent.
Then: t_n:=cardDefect n 2 (t_2:=1); prove t positive; build gauge q:=t_{card A}/scale q (positive,
relabel-inv via R1+card); prove hrel (=t_{card A} both sides) + hsupport (=cocycle); assemble
coherentFaceScales; new exported theorem dropping support_scale.

Also Tier C: singleton_interaction (Step-5 QA singleton arg; nondeg done), current_product_gauge,
branch.{support_face/boundary_*/singleton_scale}, harmless.pre_entropy family.

---

# ✅ Tier B conventions eliminated (2026-07-05, follow-up)

Beyond `product_normalized`, the following are now ALSO eliminated in the leanest exported route
`MIRep_of_TraceAxioms_FinalHM_Faddeev_withConstGauge` (bundle
`FinalConstructedRepresentativeConventionsConstGauge`), all green 8622, axioms
[propext, Classical.choice, Quot.sound]:

- `singleton_slice` — PROVED as a theorem `finiteFaceScaleSingletonSliceAffine_of_faces` (no
  assumption): subsingleton first factor ⇒ product left-slice value P-invariant
  (samePosteriorLawExp_prodChannel_singleton_fst) + V=0.
- `gauge`, `scale_relabel`, `gauge_relabel` — eliminated by fixing the trivial gauge
  `constGaugeOne (fun _ => 1)`: gauge_relabel is rfl, scale_relabel is
  scaleRelabel_of_FinalHM_covariance (R1).

Convention structure now: `branch, support_scale, hm_covariance, current_product_gauge,
singleton_interaction, harmless` (was 9 fields in the original product-normalized bundle).

Classification of what remains:
- **Tier A (genuine external classical HM interface — accepted boundary):** `hm_covariance`
  (FinalHMRelabelCovariance), `branch.marginal_value` (FiniteSupportFaceMarginalValueTransportConvention
  — flagged in-source as "definite mathematical content, not a convention").
- **Tier C (genuinely need the t_n cardinal-gauge / Step-5 singleton construction):**
  `support_scale` (raw eq:facescale), `singleton_interaction` (pins a Classical.choose interaction
  coeff on subsingletons — needs paper Step-5 QA singleton argument; nondegenerate case already
  proved via faceScaleProductInteractionAssociativity), `current_product_gauge` (product-gauge A=B=1
  normalization), and `branch.{support_face,boundary_coeff,boundary_scale,singleton_scale,...}` +
  `harmless.pre_entropy` (the support-face representative/scale family = the coherent-gauge choice).

---

# ✅ product_normalized ELIMINATED (2026-07-05)

`MIRep_of_TraceAxioms_FinalHM_Faddeev_withCovariance` + `FinalConstructedRepresentativeConventionsCovariance`
drop `product_normalized` (and subfields `FiniteSelectedActionbaseScalarFor` /
`FiniteSelectedPermutationInvariancePinningFor`) entirely. `hsel` is derived from
`hm_covariance` (HM relabel-covariance clause) + `gauge_relabel` (gauge equivariance) via
`finiteSelectedPosteriorValueRelabeling_of_FinalHM_positiveGauge_covariance`. Verified absent via
`#print`/`pp.all`; axioms `[propext, Classical.choice, Quot.sound]`; build green 8622.

**The `t_n` cardinal-gauge cocycle construction was NOT needed** — the gauged value functional
`gauge q · V_HM q E` inherits relabel-invariance directly from HM covariance + gauge equivariance,
so the `c=1` pinning was never required as a convention. (The extensive `t_n`/`canonBoundary`/
`cardDefect` machinery built earlier remains in source as reusable, green, but is unused by the
covariance route; it would only be needed to *also* internalize `support_scale`/`gauge`.)

Remaining named conventions (retained as harmless normalizations, NOT the circular pinning):
`gauge`/`scale_relabel`/`support_scale` (equivariance; internalizing needs the t_n route),
`current_product_gauge`/`singleton_interaction`/`singleton_slice` (product-gauge normalizations;
`singleton_slice` is independently dischargeable via a bounded SamePosteriorLaw lemma — not done).

---

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

## R2 IN PROGRESS — t_n cardinal-gauge construction (user chose full build)

R2 (`support_face_scale`) is provably the cross-cardinality `K(ι)=1` statement — false for the
raw scale, genuinely needs the `t_n` cardinal-gauge. Landed so far (green 8612):
- `pushSignedIncl` + `atomicLinear_pushSignedIncl` + `pushSignedIncl_tangent` (tangent-space map
  `i_ι`; inclusion pushforward preserves atomic-linear + tangent).
- **`boundaryCoeff_qIndep_of_FinalHM`** (R2a, the make-or-break): the embedding defect
  `boundaryCoeff q r / scale q` is q-independent, proved WITHOUT the cross-prior bridge
  (transport + full-support tangent relation on the pushed tangent + A1 cancellation). Confirms
  `t_n` is constructible non-circularly.

Landed brick: `canonType n := ULift (Fin n)`; `scale_uniform_eq_cardScale`: scale(u_A) depends
only on card A.

**CORRECTION (this session):** `cardScale` (scale of uniform-self) is DEGENERATE = 1 for all n≥2
(`scale(u_A) = branchPathCoeff(u_A)(u_A) = 1` by the full-support cocycle q=r=s=u_A). So it is NOT
the cardinal gauge `t_n`. Verified NO gauge shortcut exists (`g := 1/scale` collapses to the false
`boundaryCoeff q r = scale q`). The genuine `t_n = K_{n,2}` cross-cardinality embedding defect and
the nested-inclusion cocycle ARE required — this is the paper's actual argument.

**R2b LANDED so far (all green 8612, committed):**
- `canonInclKernel`, `canonBoundary n m`, `canonBoundary_apply/pos/support_nonempty/nondeg/boundary`,
  `canonBoundarySupportEquiv` (supp ≃ canonType m).
- `scale_uniform_eq_one` (scale(u_A)=1 via cocycle), `canonBoundary_face_uniform` (face = uniform on
  m-support), `canonBoundary_face_scale_eq_one` (face scale = 1 for m≥2).
- `cardDefect n m := boundaryCoeff(u_n)(canonBoundary n m)` (= K_{n,m}, scale factors are 1);
  `cardDefect_pos` (2≤m<n).

**R2b MORE LANDED (green 8612, committed):**
- Global `instNonemptySupportSubtype` instance (unblocked all `Nonempty (supportSubtype)`
  synthesis — was the main mechanical blocker).
- `relabelSupportEquiv`, `restrictToSupport_relabelDist`, `push_relabel_comm` (tangent naturality
  square for the support inclusion).
- **`boundaryCoeff_relabel_of_FinalHM`** (the R1-analogue for the boundary transport — the main
  conceptual risk, now DONE): `boundaryCoeff (relabel e q)(relabel e r) = boundaryCoeff q r`.
  Combined with `scaleRelabel_of_FinalHM_covariance`, the embedding defect is relabel-invariant.

**R2b REMAINING (each verified-tractable, ~4-5 lemmas each; the two hard pieces):**

(A) **General reduction** `defect(q,r) = cardDefect n m` for arbitrary boundary (q,r) with
    card A = n, card supp r = m (2≤m<n), where `defect(q,r) := boundaryCoeff q r · scale(r|supp)/scale q`:
    - via R2a (q-indep) reduce to q = u_n (scale(u_n)=1);
    - **defect relabel-invariance** (R1-analogue): boundaryCoeff(relabel e q)(relabel e r)=boundaryCoeff q r
      using marginalValue_relabel + supportSubtype(relabel e r)≃supportSubtype r;
    - **r-independence on a fixed support face** (transport at same pushed tangent +
      branchPathCoeff(r|supp)(s|supp)); combine to reduce arbitrary r to canonBoundary n m
      (relabel A≃canonType n carrying supp r to first-m).

(B) **Cocycle** `cardDefect n m · cardDefect m ℓ = cardDefect n ℓ` (2≤ℓ<m<n) ⟹ define
    `t_n := cardDefect n 2` (with cardDefect 2 2 handled), `cardDefect n m = t_n/t_m`:
    - `canonInclKernel n m ∘ canonInclKernel m ℓ = canonInclKernel n ℓ` (Fin.castLE_comp);
    - chain the marginalValue transport at (u_n, cB n m) [with an m-face tangent that is the push
      of an ℓ-tangent] and at (u_m, cB m ℓ), bridging `u_n restricted to the m-face = u_m` (both
      uniform on m elements, up to the support equiv — R1 relabel);
    - the two transport scalars multiply to the (u_n, cB n ℓ) scalar; cancel a nonzero ℓ-tangent (A1).

Then **R2c**: gauge `q ↦ 1 / cardDefect (card A) 2` (relabel-invariant, positive);
`hrel` via R1; `hsupport` via (A)+(B); assemble `coherentFaceScales_of_FinalHM_positiveGauge`.

**Corrected R2b build (canonBoundary via pushforward — compiles):**
```
canonInclKernel n m (hmn : m ≤ n) : ActionKernel (canonType m) (canonType n) :=
  fun a => Dist.pure (ULift.up (Fin.castLE hmn a.down))
canonBoundary n m hmn [NeZero m] : Dist (canonType n) :=
  actionPushforward (uniform (canonType m)) (canonInclKernel n m hmn)   -- uniform on first m of n
```
Needed properties of canonBoundary (each a real lemma): support = image of canonType m;
`supportSubtype (canonBoundary n m) ≃ canonType m`; its `restrictToSupport = uniform (canonType m)`;
nondegenerate (m≥2); boundary (m<n). Then:
- `defect n m := boundaryCoeff (u_{canonType n}) (canonBoundary n m) · scale((canonBoundary n m)|supp)`
  (a concrete ℝ; `= boundaryCoeff · cardScale-of-face`).
- **cardinality-well-defined**: arbitrary (q,r) with card A=n, card supp r=m reduces to
  `defect n m` via q-indep (R2a) + defect relabel-invariance + r-indep on the face.
- **nested cocycle** `defect n m · defect m ℓ = defect n ℓ` (canonType ℓ ⊂ canonType m ⊂ canonType n
  via castLE composition; `pushSignedIncl` composes): the hard lemma.
- `t_n := defect n 2` (with `defect 2 2 = 1`); `defect n m = t_n / t_m` from the cocycle.
- gauge `q ↦ 1 / t_{card A}` (relabel-invariant since card-only); `hsupport` follows.

**Precise remaining `hsupport` reduction (worked out, turn-key):**
The cardinal gauge is `gauge q := 1 / cardScale (card A)` (prior-independent, cardinality-only,
positive). With it, the positive-gauge `hsupport` obligation
`(gauge q/gauge r)·branchCoeff q r = (gauge q·scale q)/(gauge(r|supp)·scale(r|supp))`
simplifies (gauge q = gauge r = 1/cardScale n since q,r same type A; gauge(r|supp)=1/cardScale m,
m=card supp r) to:
  `boundaryCoeff q r = (scale q · cardScale m) / (scale(r|supp) · cardScale n)`, n=card A.
By R2a (q-independence) it suffices at `q = u_A` (where scale(u_A)=cardScale n by
`scale_uniform_eq_cardScale`), reducing to the **R2b-core**:
  `boundaryCoeff (u_A) r · scale(r|supp) = cardScale m`   (m = card supp r).

Remaining lemmas for R2b-core:
- **defect relabel-invariance** (R1-analogue for the boundary transport): using
  `marginalValue_relabel` + supportSubtype(relabel e r) ≃ supportSubtype r, show
  `boundaryCoeff (relabel e q)(relabel e r) = boundaryCoeff q r` (and scale(r|supp) transports).
  ⟹ defect depends only on support-*shape* up to relabel.
- **r-independence** on a fixed support face B: for r,s with the same supportSubtype,
  transport gives `boundaryCoeff q r · linearPart(r|supp)η = boundaryCoeff q s · linearPart(s|supp)η`
  (same pushed tangent), and `linearPart(r|supp)η = branchPathCoeff(r|supp)(s|supp)·linearPart(s|supp)η`,
  so `boundaryCoeff q r = boundaryCoeff q s · branchPathCoeff(s|supp)(r|supp)`. Combined with
  `scale(r|supp)=branchPathCoeff... scale(s|supp)` this makes the defect r-independent.
- **reduce to canonical**: relabel `A ≃ canonType n` and pick canonical `r` whose support-face is
  `canonType m` with `r|supp = u_{canonType m}`; then `scale(r|supp)=cardScale m` and the defect
  `boundaryCoeff(u_A) r · scale(r|supp)/cardScale n` evaluates; use q,r-indep + relabel to conclude
  it equals `cardScale m/cardScale n`, giving R2b-core. (This is where the paper's `K(ι)` becomes
  `cardScale`-ratio; the "cocycle" is absorbed into `cardScale` being a single scale value.)
- **R2c**: assemble `cardinalGauge`, prove `hrel` (R1) + `hsupport` (above); build the coherent
  face-scale representative `coherentFaceScales_of_FinalHM_positiveGauge hhm ... cardinalGauge`.
- Then rewiring (below).

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
