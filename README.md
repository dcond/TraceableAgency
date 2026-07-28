# TraceableAgency

Lean 4 formalization of the main characterization theorem for traceable agency preferences over finite stochastic environments.

## Matched Paper

The formalization is pinned to version 7 of the paper:

- [paper source](Paper/empowerment_v7.tex);
- [compiled 50-page PDF](Paper/empowerment_v7.pdf);
- [snapshot hashes and correspondence note](Paper/README.md).

The source snapshot is byte-for-byte identical to the copy used in the
paper-to-Lean review. Later local paper drafts are deliberately not part of
this certificate.

## Main Theorem

The public assembled theorem is:

```lean
TraceableAgency.provedMainCharacterizationWithMoreover
```

with type:

```lean
MainCharacterizationWithMoreover
```

The conclusion expands to:

```lean
∀ F, (TraceAxioms F ↔ MIRep F) ∧ (TraceAxioms F → BlockSameScaleRep F)
```

Here `TraceAxioms F` packages the paper's axioms A1-A6, `MIRep F` is the
mutual-information representation, and `BlockSameScaleRep F` is the block
same-scale "moreover" clause.

## Mathematical Surface

All action and outcome spaces below are finite. A distribution on `A` is a
nonnegative real vector `q : A → ℝ` with `∑ a, q a = 1`. A channel
`P : A → Δ(O)` is a row-stochastic matrix. For a prior `q` and channel `P`,

```text
m(o)   = ∑ a, q(a) P(o | a)
rₒ(a) = q(a) P(o | a) / m(o)       when m(o) > 0.
```

Shannon entropy and mutual information are

```text
H(q)     = -∑ a, q(a) log q(a),     with 0 log 0 = 0
I(q, P)  = H(m) - ∑ a, q(a) H(P(· | a))
         = H(q) - ∑ o, m(o) H(rₒ).
```

A `PrefFamily` assigns to every channel `P` a relation `≽ₚ` on lotteries over
its action space. Cross-channel comparisons are not primitive: `P ⊔ Q` places
two channels in one labelled block environment, and `q⁰`, `r¹` embed lotteries
in its two blocks.

### Behavioral axioms A1-A6

1. **Weak order and local non-triviality.** Every `≽ₚ` is complete and
   transitive. For every full-support `q` on a non-singleton `A`,
   `q⁰ ≻_(Id_A ⊔ U_A) q¹`: full revelation is strictly preferred to the
   one-outcome uninformative channel.

2. **Closed preference graph.** If `Pₙ → P`, `qₙ → q`, and `rₙ → r`
   coordinatewise and `qₙ ≽_(Pₙ) rₙ` for every `n`, then `q ≽ₚ r`.
   Posterior-law continuity is derived, not assumed.

3. **Block-comparison coherence.**

   ```text
   q ≽ₚ q'  ↔  q⁰ ≽_(P ⊔ P) (q')¹

   qᵢⁱ ≽_(⊔ₖ Pₖ) qⱼʲ  ↔  qᵢ⁰ ≽_(Pᵢ ⊔ Pⱼ) qⱼ¹    for i ≠ j.
   ```

4. **Outcome post-processing aversion.** For every stochastic
   `T : O → Δ(O')`,

   ```text
   q⁰ ≽_(P ⊔ PT) q¹.
   ```

5. **Action-coarsening aversion.** For a stochastic
   `S : A → Δ(A')`, let `qS` be the pushed-forward prior. On every positive
   row,

   ```text
   (S^q P)(o | a') =
     (∑ a, q(a) S(a' | a) P(o | a)) / (qS)(a').
   ```

   For every completion `P̂` on zero-probability rows,

   ```text
   q⁰ ≽_(P ⊔ P̂) (qS)¹.
   ```

6. **Branchwise continuation monotonicity.** After a first-stage channel
   `P₁`, if at every reached posterior `rₒ` the continuation `Qᵒ` is weakly
   preferred to `Rᵒ`, then the sequential channel using the `Qᵒ` profile is
   weakly preferred to the one using the `Rᵒ` profile. A strict comparison on
   one positive-probability branch makes the aggregate comparison strict.

Independent-background separability is **not assumed**. Lean derives the
stronger background-inertness equivalence

```text
(P₁ ⊗ R₂) ≽_(q₁⊗q₂) (Q₁ ⊗ R₂)
  ↔
P₁ ≽_(q₁) Q₁,
```

and its symmetric second-coordinate version, from A1 and A3-A6. Consequently
the comparison is independent of the common background `R₂`, so the former v6
A7 follows as a theorem. The Lean proof also covers boundary priors; v7 only
needs the full-support specialization.

The definitions are in
[`TraceableAgency/Behaviour/Axioms.lean`](TraceableAgency/Behaviour/Axioms.lean)
and agree with the A1-A6 section of the included v7 paper.

### Generic finite mathematics is proved internally

The public theorem has no theorem-interface parameter. Finite Blackwell
equivalence, the exact generic Herstein--Milnor schema, and the exact finite
Faddeev entropy characterization used by the paper are all Lean proofs.

#### Finite Blackwell equivalence is proved internally

The posterior law of an experiment `E = (O, P)` at `q` is

```text
μ(q,E) = ∑ o, m(o) δ_(rₒ).
```

At a full-support prior, if two finite experiments have the same posterior
law, Lean proves that they are mutual garblings:

```text
μ(q,E) = μ(q,E')  →
  ∃ T T', E'.P = E.P T ∧ E.P = E'.P T'.
```

The proof explicitly groups outcomes by their posterior, shows that matching
posterior classes have the same marginal mass, and constructs each garbling
row by redistributing that mass proportionally among target outcomes in the
same class. Lean then derives preference substitution, posterior-law
sufficiency, and posterior-law continuity from this theorem and A1-A4.

#### Generic Herstein-Milnor mixture-space theorem is proved internally

Let `X` have separating real coordinates `cₖ` and mixtures satisfying

```text
cₖ(t x + (1-t) y) = t cₖ(x) + (1-t) cₖ(y),   0 < t < 1.
```

If a relation `R` on `X` is complete, transitive, independent,

```text
R(x,y) ↔ R(t x + (1-t) z, t y + (1-t) z),
```

and sequentially closed under coordinatewise convergence, Lean proves the
existence of an affine utility:

```text
R(x,y) ↔ u(x) ≥ u(y)
u(t x + (1-t) y) = t u(x) + (1-t) u(y).
```

The proof is in
[`TraceableAgency/External/GenericHersteinMilnor.lean`](TraceableAgency/External/GenericHersteinMilnor.lean).
It is for this exact schema—not a nearby topological textbook statement. It
constructs closed upper and lower contour cuts on the scalar anchor segment,
uses the stated sequential closure to prove those cuts closed, calibrates every
alternative globally (including alternatives outside the anchor interval),
and proves affinity by a common positive dilution toward the midpoint.
The resulting theorem directly inhabits the formerly assumed
`ClassicalHersteinMilnorMixtureTheoremAssumptions`.

#### Finite Faddeev entropy characterization

For a functional `G` on all nonempty finite probability spaces, assume:

- `G(q) ≥ 0` and `G(δₐ) = 0`;
- invariance under finite relabeling;
- deletion or insertion of zero-probability states does not change `G`;
- `t ↦ G(t,1-t)` is continuous for `0 < t < 1`;
- strong additivity:

  ```text
  G(p ⋉ q) = G(p) + ∑ k, p(k) G(qₖ),
  ```

  where `(p ⋉ q)(k,a) = p(k) qₖ(a)`.

The theorem interface concludes

```text
∃ α ≥ 0, ∀ q, G(q) = α H(q).
```

Lean derives every premise for the entropy functional constructed from A1-A6.
The generic implication itself is now proved in
[`TraceableAgency/External/GenericFaddeev.lean`](TraceableAgency/External/GenericFaddeev.lean).
The proof derives full-support simplex continuity from only the stated binary
continuity and grouping recursion, proves the finite uniform/rational
characterization, passes to arbitrary full-support distributions by rational
approximation, and then removes zero-probability states. It produces the
closed witness
`GenericFaddeev.provedClassicalFaddeevTheoremAssumptions`. The paper-specific
proof then derives `α > 0` from A1's local non-triviality.

The internal finite garbling construction formalizes the relevant result from
Blackwell's
[Equivalent Comparisons of Experiments](https://projecteuclid.org/download/pdf_1/euclid.aoms/1177729032).
Primary references for the internally formalized HM and Faddeev arguments are
Herstein and Milnor's
[An Axiomatic Approach to Measurable Utility](https://doi.org/10.2307/1905540),
and the Faddeev-based characterization in
[Baez, Fritz and Leinster](https://arxiv.org/abs/1106.1791).

### Expanded main result

Lean proves, without an additional mathematical premise, for every preference
family:

```text
A1-A6
  ↔
∀ finite A, O, P : A → Δ(O), q, q' : Δ(A),
  q ≽ₚ q' ↔ I(q,P) ≥ I(q',P).
```

Moreover, comparisons across distinct blocks use the same mutual-information
scale:

```text
qᵢⁱ ≽_(⊔ₖ Pₖ) qⱼʲ
  ↔
I(qᵢ,Pᵢ) ≥ I(qⱼ,Pⱼ).
```

## Audit Boundary

The former `FinalHMInterface` is retained only as an internal compatibility
shell. It has no theorem field and is canonically inhabited by
`provedFinalHMInterface`; its private universe marker carries no mathematical
premise. The generic Herstein--Milnor result is the proved theorem
`genericHersteinMilnorMixtureTheorem`.

Lean constructs the mixture space of experiments modulo equality of posterior
laws, proves that
continuous test-function coordinates separate its points and make public
mixtures affine, transports the derived weak order, independence, and
continuity properties to that quotient, applies the proved generic theorem, and then
derives the normalized cross-alphabet posterior-value package internally.

Posterior-law continuity is not a field: Lean derives it from the ordinal
axioms, primitive A2, and the internally proved finite Blackwell theorem. Lean explicitly
constructs finite continuous barycentric grids
by recursive vertex insertion, then constructs the fixed-alphabet spreads and
merges, proves their channel convergence and Blackwell order relations, and
proves that their limiting posterior laws are exactly the requested limits.
Finite posterior-law extensionality is likewise proved internally by
continuous interpolation on the finite posterior supports.
The affine posterior-integral representation is also internal: Lean proves
finite-mixture affinity, performs the explicit small-atom affine extension at
full-support priors, and reduces boundary priors to their positive-support
faces.

Lean canonically normalizes the selected posterior value by full revelation
and derives exact support restriction,
finite relabelling covariance, and cardinal scale alignment internally.

The former `ClassicalFaddeevTheoremAssumptions` remains as a transparent audit
schema, but its public use is discharged by the closed Lean witness
`GenericFaddeev.provedClassicalFaddeevTheoremAssumptions`. The schema is the
ordinary, preference-free finite Faddeev theorem: a nonnegative functional on finite
distributions that vanishes on point masses, is invariant under finite
relabeling and deletion of zero-probability states, is continuous on the
interior binary simplex, and satisfies strong additivity is a nonnegative
multiple of Shannon entropy. Lean now proves this implication as well as
deriving every hypothesis for the paper's entropy functional. In particular,
binary continuity is derived from primitive A2 using the paper's erasure
calibrators; relabeling is derived from A5; and support-face invariance,
nonnegativity, point-mass normalization, and strong additivity are proved
internally. Both finite data-processing inequalities are also proved
internally from finite entropy concavity and Bayes reversal.

## Requirements

This repository uses the Lean toolchain pinned in:

```text
lean-toolchain
```

and mathlib pinned in:

```text
lake-manifest.json
```

## Verification

Run:

```bash
lake build
./scripts/check_certificate.sh
```

The verification script prints the assembled theorem, its axioms, the expanded
conclusion, the closed Faddeev and HM witnesses, and the key derived
continuity, Blackwell, and canonical-transport results. It also checks that the
Lean source contains no
`sorry`, tactic `admit`, or declaration-level `axiom`.

Expected theorem boundary:

```lean
TraceableAgency.provedMainCharacterizationWithMoreover :
  MainCharacterizationWithMoreover
```

Expected `#print axioms` output:

```text
[propext, Classical.choice, Quot.sound]
```

These are Lean/mathlib foundational dependencies, not unproved mathematical
premises.

## Remaining Formalization Frontier

The project is closed at the mathematical theorem boundary: the main result is
kernel-checked from the paper's A1-A6 definitions with no external theorem
parameter. Finite same-posterior-law Blackwell equivalence, the exact generic
Herstein--Milnor theorem, and the exact finite Faddeev theorem are all
formalized. No adapted-triangulation, posterior-continuity, relabeling,
support, normalization, scale-coherence, data-processing,
representative-selection, or classical-characterization assumption remains at
the public theorem boundary.

Further work would be maintenance rather than completion: shortening the long
internal proof files, eliminating linter warnings, and upstreaming generally
useful finite entropy lemmas.
