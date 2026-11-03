# Trust boundary and explicit conventions

This report separates three questions: whether the deductions are checked,
which mathematical premises and definitions they use, and whether those
statements faithfully express the paper. A kernel check answers the first
question. It cannot replace reading the definitions and theorem statements.

## What is checked

Run the complete audit with the pinned toolchain:

```sh
./scripts/check_trust_boundary.sh
```

This command has no switch that skips the fresh replay. It:

1. Checks the repository byte manifest and the exhaustive source-import list.
2. Verifies the installed Lean version and all nine dependency revisions. It
   hashes the dependency commit/tree objects and every tracked file directly,
   rather than relying only on `git status` or its index cache. The current
   check covers 9,778 tracked files. Aesop's historical, empty `lean_packages/std`
   gitlink is reported explicitly; it supplies no imported source.
3. Rejects project proof holes and the listed unchecked proof mechanisms.
4. Deletes **only this project's generated build outputs**, disables artifact
   cache restoration, then recompiles
   every project source module, including the original proof, material-first
   proof, Sections 3–4, unused helper modules, and vendored proof files.
5. Executes the raw dependency audit described below.
6. Replays the imported declarations with `leanchecker --fresh` in a fresh
   environment at trust level zero.

The GitHub workflow now runs this complete command after its original checks.
The old workflow's skipped fresh replay was not evidence of a complete replay;
the new mandatory step closes that coverage gap. Adding this step locally
does not claim that a remote workflow run has already occurred.

## Raw audit, including private helpers

`TraceableAgency/Audit/TrustBoundaryImports.lean` imports all 272 other project
source modules. The two new audit files are the only inventory exclusions:
the umbrella cannot import itself or the auditor that imports it.
`check_trust_imports.py` includes hidden and Git-ignored Lean sources, excluding
only dependency/build storage under `.lake` and Git metadata under `.git`.
It rejects any omitted new project source file.

`TrustBoundary.lean` identifies declarations by their **defining module**, not
their namespace. The v11 proved-result completion audit found:

| Quantity | Count |
|---|---:|
| Originating project declarations | 9,813 |
| Theorem roots | 6,011 |
| Internal/private theorem roots | 1,670 |
| Theorems in other namespaces | 53 |
| All mathematical roots, including definitions | 9,661 |
| Declarations in their combined raw dependency closure | 51,123 |

The auditor reloads private compiled declaration data with environment
extensions disabled, traverses the actual types and bodies, and reads raw
axiom declarations. It does **not** rely on the cached imported axiom summaries
used by Lean's ordinary axiom-reporting command. Missing declarations fail the
audit rather than becoming unchecked leaves. Opaque bodies and recursor rule
bodies are included. All unused project axiom declarations are rejected too.

The only axioms reached are:

- `propext`: propositional extensionality;
- `Classical.choice`: classical choice;
- `Quot.sound`: quotient soundness.

These are the standard classical Lean foundations, not additional assumptions
about preferences. The audit also explicitly reports the kernel's quotient
primitives: `Quot`, `Quot.mk`, `Quot.lift`, and `Quot.ind`.

There are no project mathematical axiom declarations, no proof holes, and no
unsafe or partial declarations in the mathematical dependency closure.
Four partial traversal/rendering helpers belong only to the audit tools; their
generated implementations are listed in the log and cannot enter a mathematical
proof dependency. The one mathematical `opaque` declaration is an old
Herstein–Milnor interface witness with an explicit checked body. `opaque` here
prevents unfolding during ordinary elaboration; it does not mean postulated.

## What fresh replay does, and why both checks are needed

The pinned checker imports complete private declaration data, starts an empty
kernel environment with trust level zero, and re-adds safe definitions,
theorems, and opaque bodies through the kernel. It also checks the inductive,
constructor, and recursor infrastructure. It uses the **same installed Lean
kernel**, not an independently implemented proof checker.

Fresh replay alone is insufficient to exclude hidden assumptions: it accepts
declared axioms and skips unsafe/partial declarations. That is why the separate
raw audit rejects unexpected axioms and rejects unsafe/partial mathematical
dependencies. In this Lean version, `native_decide`-style proof justification
would introduce a generated axiom outside the whitelist; it is not silently
accepted as mathematics by this certificate.

Lean's elaborator, proof-generating tactics, and audit tools may execute
unsafe/native metaprogram code, including standard Lean implementations. The
claim is that no unsafe or partial declaration enters the mathematical proof
dependencies. Ordinary tactics must produce proof terms accepted by the kernel;
their successful execution alone is not a proof certificate.

The executable audit is tooling, not a theorem proving its own correctness.
Its source is short enough to inspect. Recompiling the audit runs its assertions;
replaying its compiled module alone does not rerun those assertions.

## External mathematics and intermediate assumptions

The proof uses standard Lean/mathlib mathematics **and** an adapted finite
Shannon-characterization proof in `TraceableAgency/Vendor/Shannon`. The latter
comes from Samuel Schlesinger's `shannon-1948-formalization`, with its MIT licence
and adaptation notes retained. It is ordinary local Lean proof code, rebuilt
and checked with the rest. It is not a trusted external oracle or a theorem
assumed from a paper.

The public representation theorem has the exact `Theorem1StatementV10` type.
Its preference premise is `TraceTemperedAxiomsV10`, whose eight fields are
exactly A1–A8. Both the original and material-first endpoints prove that same
statement. Structures called `...Assumptions`, intermediate full-support
conditions, and entropy/affine representation interfaces occur in helper
lemmas; the final proof constructs their required witnesses or derives their
hypotheses before applying them. They are not additional hypotheses of the
public theorem. Later application theorems retain their stated model and
parameter assumptions, as mapped in the Section 3 and Section 4 certificates.

## Conventions and substantive restrictions that remain visible

It would be incorrect to claim that the formalization has **no conventions**.
The conventions and domain restrictions include the following.

- **Finite domain.** The representation theorem fixes a finite payoff alphabet
  with at least two elements, and ranges over arbitrary finite nonempty action
  and record alphabets. Priors admit arbitrary real probabilities, including
  boundary priors. `Fintype`, `Nonempty`, and decidable equality are explicit
  in the types.
- **Actual axiom scope.** A2 permits variation in the channel and both priors
  on fixed alphabets. A7 quantifies over every completion at null processed
  actions. The stated A8 is the binary reached-branch equivalence; its finite
  and strict consequences are derived. Common-scale cross-channel comparisons
  use the paper's block construction, not an extra primitive relation.
- **Null events.** A posterior at a zero-probability observation is assigned
  an arbitrary pure distribution. Reached-branch claims require positive mass;
  null terms receive zero weight. The default is therefore irrelevant in the
  results, not a behavioral assumption about beliefs at impossible events.
- **Entropy and logarithms.** Information is measured with natural logarithms,
  with zero entropy contribution at probability zero. Changing to a base
  `b > 1` rescales the weight: `lambda_natural = lambda_b / log b`.
- **KL support.** Lean's real logarithm is total, so a real-valued sum is not
  automatically the extended-real KL divergence. `finiteKL` is interpreted as
  KL under explicit support inclusion. Optimality theorems prove that relevant
  output support is covered; missing-support binary cases are handled by a
  separate exact condition. No infinite divergence is silently treated as zero.
- **Uniqueness.** An arbitrary common-scale ordinal representation is unique
  up to a strictly increasing transform on its attainable range. Positive
  affine uniqueness requires numerical branch additivity. The formalization
  does not assert affine uniqueness for every ordinal index.
- **Moral-hazard cost.** The finite-consequence implementation uses an independent
  cost lottery depending on the candidate plan `q`. It does not record the
  realized effort cost. Different plans use different augmented channels and
  are compared using the theorem's common-scale block clause.
- **Application premises.** Standalone numerical lemmas state their parameter
  assumptions explicitly. For the axiomatised preference family, positivity of
  the representing information weight follows from the representation theorem.
  Model-specific conditions—distinct binary rows, interior Bernoulli success
  probabilities, uniform team bounds, the chosen prior and utility anchors,
  and elicitation feasibility—remain explicit where needed.

## Residual trust and scope

The assurance is conditional on the installed Lean kernel/runtime behaving
correctly and the declared mathematical definitions being the intended ones.
Dependency source pins and byte checks establish the local source inventory;
they do not independently authenticate the toolchain release binary or prove
that every cached dependency artifact was compiled from that source. Fresh
replay checks the mathematical content of the imported compiled declarations.
This command rebuilds all **project** sources, including the vendored proof;
it does not rebuild all of mathlib from source. It also does not independently
validate the installed compiler, operating system, or hardware.

Finally, the kernel does not read the TeX paper or certify that the choice of
definitions captures its economic meaning. The
[current certificate](FORMALIZATION_CERTIFICATE.md) indexes all 34 numbered
mathematical results in v11, and the [completion report](V11_PROVED_RESULTS.md)
records the added exact statements and the successful 2026-11-03 verification.
Those claim maps and explicit theorem hypotheses make the correspondence
reviewable. The [historical audit](V11_CORRESPONDENCE_AUDIT.md) describes the
pre-completion state; its resolved findings are not current coverage gaps.
Individual unnumbered calculations and explanatory formulations remain outside
the numbered-result claim where identified in the completion report. No kernel
audit turns those unformalized formulations into verified results.
