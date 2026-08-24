# Mechanical formal specification of Theorem 1

> **Generated file — do not edit.** Regenerate with `./scripts/build_theorem1_spec.sh --update`.

This document is generated from the elaborated Lean environment. The extractor follows the types of its two certified roots and the local definition bodies they use, expands structure fields, and never unfolds theorem declarations. External toolchain and dependency declarations are terminal boundary symbols: their implementations are not unfolded.

The Lean blocks are authoritative: every displayed definition includes its elaborated body, structures include their fields, and theorem declarations include their exact signatures; only proof subterms inside definitions are printed as `⋯`. The mathematical blocks are produced by the small, version-controlled notation table in `TraceableAgency/Audit/Theorem1Spec.lean`; each block is locked to the semantic digests of the declarations it translates, so a Lean-side change stops generation until the corresponding mathematics is explicitly reviewed. The complete local closure has a separate lock covering transitive infrastructure and generated helpers. The generated Markdown uses GitHub's native MathJax delimiters, so its mathematical displays render in the repository view.

Every reached project declaration is explicitly classified as paper-facing or infrastructure; generation fails if an unclassified local dependency appears.

In the mathematical displays, computational `DecidableEq` arguments are suppressed. Action, record, block-index, and dependent-fibre alphabets quantified by the axioms are finite and nonempty.

- **Theorem root:** `TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1`
- **Paper-notation root:** `TraceableAgency.mutualInfoLikelihoodRatio_eq_mutualInfo`
- **Pinned toolchain:** [`lean-toolchain`](../lean-toolchain) (`Lean 4.32.1`)
- **Local semantic closure:** 79 declarations
- **Paper-facing declarations:** 56
- **Classified infrastructure declarations:** 16
- **Generated local interfaces:** 7
- **Recursive closure digest:** `8391076054563383822`
- **External boundary:** 101 toolchain/dependency constants (not unfolded)

## Domain and paper notation

### Finite lotteries

**Notation-table digest:** `11226582100683779610`

- **Lean declaration:** [`TraceableAgency.Dist`](../TraceableAgency/Basic/Dist.lean#L24)
- **Semantic digest:** `6364284878344705314`
- **Direct displayed dependencies:** none

```lean
Dist.{u_2} (A : Type u_2) [Fintype A] : Type u_2
Dist.prob.{u_2} {A : Type u_2} [Fintype A] (self : Dist A) : A → ℝ
Dist.nonneg.{u_2} {A : Type u_2} [Fintype A] (self : Dist A) (a : A) :
  0 ≤ self.prob a
Dist.sum_eq_one.{u_2} {A : Type u_2} [Fintype A] (self : Dist A) :
  ∑ a, self.prob a = 1
```

- **Lean declaration:** [`TraceableAgency.Dist.pure`](../TraceableAgency/Basic/Dist.lean#L58)
- **Semantic digest:** `13888325898098135241`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
Dist.pure.{u_1} {A : Type u_1} [Fintype A] [DecidableEq A] (a : A) : Dist A
:=
fun {A} [Fintype A] [DecidableEq A] a ↦
  { prob := fun b ↦ if b = a then 1 else 0, nonneg := ⋯, sum_eq_one := ⋯ }
```

- **Lean declaration:** [`TraceableAgency.Dist.uniform`](../TraceableAgency/Basic/Dist.lean#L117)
- **Semantic digest:** `16300428214286353553`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
Dist.uniform.{u_2} {A : Type u_2} [Fintype A] [Nonempty A] : Dist A
:=
fun {A} [Fintype A] [Nonempty A] ↦
  { prob := fun x ↦ 1 / ↑(Fintype.card A), nonneg := ⋯, sum_eq_one := ⋯ }
```

**Mathematical form**

$$
\Delta(A)=\left\{q:A\to\mathbb R_{\ge0}:\sum_{a\in A}q(a)=1\right\},
\qquad
\delta_a(b)=\mathbf 1_{\{b=a\}},
\qquad
\operatorname{unif}_{A}(a)=\frac1{|A|}.
$$

### Channels and visible-consequence marginal

**Notation-table digest:** `10868161788146472416`

- **Lean declaration:** [`TraceableAgency.Channel`](../TraceableAgency/Basic/Channel.lean#L24)
- **Semantic digest:** `1191561729527487809`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
Channel.{u_5, u_6} (A : Type u_5) (O : Type u_6) [Fintype O] : Type (max u_5 u_6)
:=
fun A O [Fintype O] ↦ A → Dist O
```

- **Lean declaration:** [`TraceableAgency.Channel.outcomeMarginal`](../TraceableAgency/Basic/Channel.lean#L42)
- **Semantic digest:** `17201252334914367550`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`

```lean
Channel.outcomeMarginal.{u_1, u_2} {A : Type u_1} {O : Type u_2} [Fintype A]
  [Fintype O] (P : Channel A O) (q : Dist A) : Dist O
:=
fun {A} {O} [Fintype A] [Fintype O] P q ↦
  { prob := fun o ↦ ∑ a, q.prob a * (P a).prob o, nonneg := ⋯, sum_eq_one := ⋯ }
```

**Mathematical form**

$$
K:A\longrightarrow\Delta(X),
\qquad
p_{qK}(x)=\sum_{a\in A}q(a)K(x\mid a).
$$

### Entropy and mutual information

**Notation-table digest:** `14900683673367227622`

- **Lean declaration:** [`TraceableAgency.entropyTerm`](../TraceableAgency/Info/Entropy.lean#L22)
- **Semantic digest:** `3151315998047640464`
- **Direct displayed dependencies:** none

```lean
entropyTerm (p : ℝ) : ℝ
:=
fun p ↦ if p ≤ 0 then 0 else -p * Real.log p
```

- **Lean declaration:** [`TraceableAgency.entropy`](../TraceableAgency/Info/Entropy.lean#L116)
- **Semantic digest:** `10849261662597361372`
- **Direct displayed dependencies:** `TraceableAgency.Dist`, `TraceableAgency.entropyTerm`

```lean
entropy.{u_1} {A : Type u_1} [Fintype A] (q : Dist A) : ℝ
:=
fun {A} [Fintype A] q ↦ ∑ a, entropyTerm (q.prob a)
```

- **Lean declaration:** [`TraceableAgency.mutualInfo`](../TraceableAgency/Info/MutualInfo.lean#L26)
- **Semantic digest:** `14122231549474269340`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Channel.outcomeMarginal`, `TraceableAgency.Dist`, `TraceableAgency.entropy`

```lean
mutualInfo.{u_1, u_2} {A : Type u_1} {O : Type u_2} [Fintype A] [Fintype O]
  (q : Dist A) (P : Channel A O) : ℝ
:=
fun {A} {O} [Fintype A] [Fintype O] q P ↦ H(P.outcomeMarginal q) - ∑ a, q.prob a * H(P a)
```

- **Lean declaration:** [`TraceableAgency.mutualInfoLikelihoodRatioTerm`](../TraceableAgency/Info/MutualInfo.lean#L34)
- **Semantic digest:** `10349328888319558200`
- **Direct displayed dependencies:** none

```lean
mutualInfoLikelihoodRatioTerm (joint conditional marginal : ℝ) : ℝ
:=
fun joint conditional marginal ↦ if joint = 0 then 0 else joint * Real.log (conditional / marginal)
```

- **Lean declaration:** [`TraceableAgency.mutualInfoLikelihoodRatio`](../TraceableAgency/Info/MutualInfo.lean#L41)
- **Semantic digest:** `8829574675389275588`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Channel.outcomeMarginal`, `TraceableAgency.Dist`, `TraceableAgency.mutualInfoLikelihoodRatioTerm`

```lean
mutualInfoLikelihoodRatio.{u_1, u_2} {A : Type u_1} {O : Type u_2} [Fintype A]
  [Fintype O] (q : Dist A) (P : Channel A O) : ℝ
:=
fun {A} {O} [Fintype A] [Fintype O] q P ↦
  ∑ a,
    ∑ o,
      mutualInfoLikelihoodRatioTerm (q.prob a * (P a).prob o) ((P a).prob o)
        ((P.outcomeMarginal q).prob o)
```

- **Lean declaration:** [`TraceableAgency.mutualInfoLikelihoodRatio_eq_mutualInfo`](../TraceableAgency/Info/MutualInfo.lean#L74)
- **Semantic digest:** `17432204412887586356`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.mutualInfo`, `TraceableAgency.mutualInfoLikelihoodRatio`

```lean
mutualInfoLikelihoodRatio_eq_mutualInfo.{u_1, u_2} {A : Type u_1} {O : Type u_2}
  [Fintype A] [Fintype O] [DecidableEq A] (q : Dist A) (P : Channel A O) :
  mutualInfoLikelihoodRatio q P = I(q, P)
```

**Mathematical form**

$$
h(x)=\begin{cases}0,&x\le0,\\-x\log x,&x>0,\end{cases}
\qquad
H(q)=\sum_a h(q(a)).
$$

$$
I_{qK}(A;X)=H(p_{qK})-\sum_a q(a)H(K(\cdot\mid a))
=\sum_{a,x}\tau\!\left(q(a)K(x\mid a),K(x\mid a),p_{qK}(x)\right),
$$
where
$$
\tau(j,c,m)=\begin{cases}0,&j=0,\\j\log(c/m),&j\ne0.\end{cases}
$$
The last equality is the checked theorem `mutualInfoLikelihoodRatio_eq_mutualInfo`.
Lean's `Real.log` is the natural logarithm; changing to another base greater than one rescales the positive coefficient $\lambda$.

### Preference family and strict part

**Notation-table digest:** `7930570054458820236`

- **Lean declaration:** [`TraceableAgency.Theorem1.FixedPayoffPrefFamily`](../TraceableAgency/Theorem1/Statements.lean#L46)
- **Semantic digest:** `13988103282880620113`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`

```lean
FixedPayoffPrefFamily.{u} (O : Type u) [Fintype O] : Type (u + 1)
FixedPayoffPrefFamily.rel.{u} {O : Type u} [Fintype O]
  (self : Theorem1.FixedPayoffPrefFamily O) {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype R] [DecidableEq R] [Nonempty R] : Channel A (O × R) → Dist A → Dist A → Prop
```

- **Lean declaration:** [`TraceableAgency.Theorem1.FixedPayoffPrefFamily.strictRel`](../TraceableAgency/Theorem1/Statements.lean#L61)
- **Semantic digest:** `6619030650391116158`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`

```lean
FixedPayoffPrefFamily.strictRel.{u} {O : Type u} [Fintype O]
  (F : Theorem1.FixedPayoffPrefFamily O) {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
  [Fintype R] [DecidableEq R] [Nonempty R] (K : Channel A (O × R)) (q p : Dist A) : Prop
:=
fun {O} [Fintype O] F {A R} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype R] [DecidableEq R]
    [Nonempty R] K q p ↦
  F.rel K q p ∧ ¬F.rel K p q
```

**Mathematical form**

$$
q\succeq_K p\;\Longleftrightarrow\;F.\mathrm{rel}(K,q,p),
\qquad
q\succ_Kp\;\Longleftrightarrow\;
q\succeq_Kp\ \wedge\ \neg(p\succeq_Kq).
$$

### Block comparison environments

**Notation-table digest:** `15198310688743706801`

- **Lean declaration:** [`TraceableAgency.Theorem1.commonPayoffBlockChannel`](../TraceableAgency/Theorem1/Statements.lean#L108)
- **Semantic digest:** `9629084559079345179`
- **Direct displayed dependencies:** `TraceableAgency.Channel`

```lean
commonPayoffBlockChannel.{u} {O A B R S : Type u} [Fintype O] [Fintype A]
  [Fintype B] [Fintype R] [Fintype S] [DecidableEq O] [DecidableEq A] [DecidableEq B]
  [DecidableEq R] [DecidableEq S] (K : Channel A (O × R)) (L : Channel B (O × S)) :
  Channel (A ⊕ B) (O × (R ⊕ S))
:=
fun {O A B R S} [Fintype O] [Fintype A] [Fintype B] [Fintype R] [Fintype S] [DecidableEq O]
    [DecidableEq A] [DecidableEq B] [DecidableEq R] [DecidableEq S] K L ↦
  Relabeling.relabelChannel (Equiv.refl (A ⊕ B)) (Theorem1.sumPayoffRecordEquiv O R S) (K ⊔ L)
```

- **Lean declaration:** [`TraceableAgency.Theorem1.leftBlockDist`](../TraceableAgency/Theorem1/Statements.lean#L119)
- **Semantic digest:** `13486490933876578191`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
leftBlockDist.{u} {A B : Type u} [Fintype A] [Fintype B] (q : Dist A) :
  Dist (A ⊕ B)
:=
fun {A B} [Fintype A] [Fintype B] q ↦ q^0
```

- **Lean declaration:** [`TraceableAgency.Theorem1.rightBlockDist`](../TraceableAgency/Theorem1/Statements.lean#L125)
- **Semantic digest:** `1461029901017408751`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
rightBlockDist.{u} {A B : Type u} [Fintype A] [Fintype B] (p : Dist B) :
  Dist (A ⊕ B)
:=
fun {A B} [Fintype A] [Fintype B] p ↦ p^1
```

- **Lean declaration:** [`TraceableAgency.Theorem1.pairWeak`](../TraceableAgency/Theorem1/Statements.lean#L153)
- **Semantic digest:** `1113478632607311243`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.commonPayoffBlockChannel`, `TraceableAgency.Theorem1.leftBlockDist`, `TraceableAgency.Theorem1.rightBlockDist`

```lean
pairWeak.{u} {O A B R S : Type u} [Fintype O] [DecidableEq O] [Fintype A]
  [DecidableEq A] [Nonempty A] [Fintype B] [DecidableEq B] [Nonempty B] [Fintype R] [DecidableEq R]
  [Nonempty R] [Fintype S] [DecidableEq S] [Nonempty S] (F : Theorem1.FixedPayoffPrefFamily O)
  (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) : Prop
:=
fun {O A B R S} [Fintype O] [DecidableEq O] [Fintype A] [DecidableEq A] [Nonempty A] [Fintype B]
    [DecidableEq B] [Nonempty B] [Fintype R] [DecidableEq R] [Nonempty R] [Fintype S]
    [DecidableEq S] [Nonempty S] F q K p L ↦
  F.rel (Theorem1.commonPayoffBlockChannel K L) (Theorem1.leftBlockDist q)
    (Theorem1.rightBlockDist p)
```

- **Lean declaration:** [`TraceableAgency.Theorem1.commonPayoffBlockFamilyChannel`](../TraceableAgency/Theorem1/Statements.lean#L131)
- **Semantic digest:** `747609578282610237`
- **Direct displayed dependencies:** `TraceableAgency.Channel`

```lean
commonPayoffBlockFamilyChannel.{u} {I O : Type u} [Fintype I]
  [DecidableEq I] [Fintype O] [DecidableEq O] (Act Rec : I → Type u) [(i : I) → Fintype (Act i)]
  [(i : I) → DecidableEq (Act i)] [(i : I) → Fintype (Rec i)] [(i : I) → DecidableEq (Rec i)]
  (K : (i : I) → Channel (Act i) (O × Rec i)) : Channel ((i : I) × Act i) (O × (i : I) × Rec i)
:=
fun {I O} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O] Act Rec
    [(i : I) → Fintype (Act i)] [(i : I) → DecidableEq (Act i)] [(i : I) → Fintype (Rec i)]
    [(i : I) → DecidableEq (Rec i)] K ↦
  Relabeling.relabelChannel (Equiv.refl ((i : I) × Act i)) (Theorem1.sigmaPayoffRecordEquiv I O Rec)
    (blockFamilyChannel Act (fun i ↦ O × Rec i) K)
```

- **Lean declaration:** [`TraceableAgency.Theorem1.commonPayoffBlockEmbed`](../TraceableAgency/Theorem1/Statements.lean#L144)
- **Semantic digest:** `1118878693280923882`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
commonPayoffBlockEmbed.{u} {I : Type u} [Fintype I] [DecidableEq I]
  (Act : I → Type u) [(i : I) → Fintype (Act i)] [(i : I) → DecidableEq (Act i)] (i : I)
  (q : Dist (Act i)) : Dist ((i : I) × Act i)
:=
fun {I} [Fintype I] [DecidableEq I] Act [(i : I) → Fintype (Act i)] [(i : I) → DecidableEq (Act i)]
    i q ↦
  blockEmbedDist Act i q
```

**Mathematical form**

$$
(K\sqcup L)(o,(r,0)\mid(a,0))=K(o,r\mid a),
\qquad
(K\sqcup L)(o,(s,1)\mid(b,1))=L(o,s\mid b),
$$
with every cross-block probability equal to zero, and
$$
q^0(a,0)=q(a),\quad q^0(b,1)=0,\qquad
p^1(a,0)=0,\quad p^1(b,1)=p(b),
$$

$$
(q,K)\succeq(p,L)
\;\Longleftrightarrow\;
q^0\succeq_{K\sqcup L}p^1.
$$
For a finite family,
$$
\left(\bigsqcup_{i\in I}K_i\right)(o,(j,r)\mid(i,a))
=\begin{cases}K_i(o,r\mid a),&j=i,\\0,&j\ne i,\end{cases}
\qquad
q_i^i(j,a)=\begin{cases}q_i(a),&j=i,\\0,&j\ne i.\end{cases}
$$

### Pointwise convergence

**Notation-table digest:** `8838656558664373777`

- **Lean declaration:** [`TraceableAgency.DistConverges`](../TraceableAgency/Basic/Convergence.lean#L28)
- **Semantic digest:** `1803301904238722931`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
DistConverges.{u_1} {A : Type u_1} [Fintype A] (qₙ : ℕ → Dist A) (q : Dist A) : Prop
:=
fun {A} [Fintype A] qₙ q ↦
  ∀ (a : A), Filter.Tendsto (fun n ↦ (qₙ n).prob a) Filter.atTop (nhds (q.prob a))
```

- **Lean declaration:** [`TraceableAgency.ChannelConverges`](../TraceableAgency/Basic/Convergence.lean#L288)
- **Semantic digest:** `14404942187009090963`
- **Direct displayed dependencies:** `TraceableAgency.Channel`

```lean
ChannelConverges.{u_2, u_3} {A : Type u_2} {Out : Type u_3} [Fintype Out]
  (Pₙ : ℕ → Channel A Out) (P : Channel A Out) : Prop
:=
fun {A} {Out} [Fintype Out] Pₙ P ↦
  ∀ (a : A) (o : Out), Filter.Tendsto (fun n ↦ (Pₙ n a).prob o) Filter.atTop (nhds ((P a).prob o))
```

**Mathematical form**

$$
q_n\to q\;\Longleftrightarrow\;q_n(a)\to q(a)\ \forall a,
\qquad
K_n\to K\;\Longleftrightarrow\;K_n(x\mid a)\to K(x\mid a)\ \forall(a,x).
$$

### Material-relevance benchmark

**Notation-table digest:** `12813607489999281459`

- **Lean declaration:** [`TraceableAgency.Theorem1.RelevanceBit`](../TraceableAgency/Theorem1/Statements.lean#L401)
- **Semantic digest:** `16265258938010438434`
- **Direct displayed dependencies:** none

```lean
RelevanceBit.{u} : Type u
:=
ULift Bool
```

- **Lean declaration:** [`TraceableAgency.Theorem1.materialRelevanceBenchmarkChannel`](../TraceableAgency/Theorem1/Statements.lean#L465)
- **Semantic digest:** `4440762415976313942`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist.pure`, `TraceableAgency.Theorem1.RelevanceBit`

```lean
materialRelevanceBenchmarkChannel.{u, u_1, u_2} {O : Type u} [Fintype O]
  [DecidableEq O] (oplus ominus : O) : Channel Theorem1.RelevanceBit (O × PUnit)
:=
fun {O} [Fintype O] [DecidableEq O] oplus ominus a ↦
  Dist.pure (if a.down = true then oplus else ominus, PUnit.unit)
```

- **Lean declaration:** [`TraceableAgency.Theorem1.materialRelevanceBetterPrior`](../TraceableAgency/Theorem1/Statements.lean#L472)
- **Semantic digest:** `6745061148468243525`
- **Direct displayed dependencies:** `TraceableAgency.Dist`, `TraceableAgency.Dist.pure`, `TraceableAgency.Theorem1.RelevanceBit`

```lean
materialRelevanceBetterPrior.{u_1} : Dist Theorem1.RelevanceBit
:=
Dist.pure { down := true }
```

- **Lean declaration:** [`TraceableAgency.Theorem1.materialRelevanceWorsePrior`](../TraceableAgency/Theorem1/Statements.lean#L477)
- **Semantic digest:** `1043118926728592562`
- **Direct displayed dependencies:** `TraceableAgency.Dist`, `TraceableAgency.Dist.pure`, `TraceableAgency.Theorem1.RelevanceBit`

```lean
materialRelevanceWorsePrior.{u_1} : Dist Theorem1.RelevanceBit
:=
Dist.pure { down := false }
```

**Mathematical form**

$$
A=\{a^+,a^-\},\qquad
K(o^+,*\mid a^+)=K(o^-,*\mid a^-)=1,
\qquad
q^+=\delta_{a^+},\quad q^-=\delta_{a^-}.
$$

### Trace-relevance benchmark

**Notation-table digest:** `4533690757616686921`

- **Lean declaration:** [`TraceableAgency.Theorem1.traceRelevanceFairPrior`](../TraceableAgency/Theorem1/Statements.lean#L491)
- **Semantic digest:** `4049520815403283770`
- **Direct displayed dependencies:** `TraceableAgency.Dist`, `TraceableAgency.Dist.uniform`, `TraceableAgency.Theorem1.RelevanceBit`

```lean
traceRelevanceFairPrior.{u_1} : Dist Theorem1.RelevanceBit
:=
Dist.uniform
```

- **Lean declaration:** [`TraceableAgency.Theorem1.traceRelevanceBenchmarkChannel`](../TraceableAgency/Theorem1/Statements.lean#L499)
- **Semantic digest:** `8834748976515282156`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Dist.pure`, `TraceableAgency.Theorem1.RelevanceBit`, `TraceableAgency.Theorem1.traceRelevanceFairPrior`

```lean
traceRelevanceBenchmarkChannel.{u, u_1, u_2} {O : Type u} [Fintype O]
  [DecidableEq O] (ostar : O) :
  Channel (Theorem1.RelevanceBit ⊕ Theorem1.RelevanceBit) (O × Theorem1.RelevanceBit)
:=
fun {O} [Fintype O] [DecidableEq O] ostar a ↦
  match a with
  | Sum.inl b => Dist.pure (ostar, b)
  | Sum.inr val =>
    { prob := fun z ↦ if z.1 = ostar then Theorem1.traceRelevanceFairPrior.prob z.2 else 0,
      nonneg := ⋯, sum_eq_one := ⋯ }
```

- **Lean declaration:** [`TraceableAgency.Theorem1.traceRelevanceRevealingPrior`](../TraceableAgency/Theorem1/Statements.lean#L520)
- **Semantic digest:** `14110227135371725258`
- **Direct displayed dependencies:** `TraceableAgency.Dist`, `TraceableAgency.Theorem1.RelevanceBit`, `TraceableAgency.Theorem1.traceRelevanceFairPrior`

```lean
traceRelevanceRevealingPrior.{u_1, u_2} :
  Dist (Theorem1.RelevanceBit ⊕ Theorem1.RelevanceBit)
:=
Theorem1.traceRelevanceFairPrior^0
```

- **Lean declaration:** [`TraceableAgency.Theorem1.traceRelevanceUnrevealingPrior`](../TraceableAgency/Theorem1/Statements.lean#L525)
- **Semantic digest:** `17109369965134876543`
- **Direct displayed dependencies:** `TraceableAgency.Dist`, `TraceableAgency.Theorem1.RelevanceBit`, `TraceableAgency.Theorem1.traceRelevanceFairPrior`

```lean
traceRelevanceUnrevealingPrior.{u_1, u_2} :
  Dist (Theorem1.RelevanceBit ⊕ Theorem1.RelevanceBit)
:=
Theorem1.traceRelevanceFairPrior^1
```

**Mathematical form**

$$
q^{\mathrm{rev}}=\tfrac12(\delta_{a_1}+\delta_{a_2}),
\qquad
q^{\mathrm{unrev}}=\tfrac12(\delta_{a_3}+\delta_{a_4}),
$$

$$
K(o_*,r_i\mid a_i)=1\ (i=1,2),
\qquad
K(o_*,r_j\mid a_i)=\tfrac12\ (i=3,4;\ j=1,2).
$$

### Record processing

**Notation-table digest:** `2162765498741811469`

- **Lean declaration:** [`TraceableAgency.Theorem1.RecordProcessor`](../TraceableAgency/Theorem1/Statements.lean#L200)
- **Semantic digest:** `7503249605775287582`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
RecordProcessor.{u} (O R S : Type u) [Fintype S] : Type u
:=
fun O R S [Fintype S] ↦ O × R → Dist S
```

- **Lean declaration:** [`TraceableAgency.Theorem1.recordPostprocess`](../TraceableAgency/Theorem1/Statements.lean#L225)
- **Semantic digest:** `6842593896207148242`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Theorem1.RecordProcessor`

```lean
recordPostprocess.{u} {O A R S : Type u} [Fintype O] [DecidableEq O]
  [Fintype A] [Fintype R] [Fintype S] [DecidableEq S] (K : Channel A (O × R))
  (T : Theorem1.RecordProcessor O R S) : Channel A (O × S)
:=
fun {O A R S} [Fintype O] [DecidableEq O] [Fintype A] [Fintype R] [Fintype S] [DecidableEq S] K T ↦
  K.postprocess (Theorem1.payoffPreservingRecordKernel T)
```

**Mathematical form**

$$
T:O\times R\longrightarrow\Delta(S),
\qquad
(KT)(o,s\mid a)=\sum_{r\in R}K(o,r\mid a)T(s\mid o,r).
$$
Lean stores only the new-record distribution $T(\cdot\mid o,r)$; `recordPostprocess` copies $o$, so this is exactly a payoff-preserving kernel on $O\times S$.

### Action processing

**Notation-table digest:** `6907658951114823665`

- **Lean declaration:** [`TraceableAgency.Channel.ActionKernel`](../TraceableAgency/Basic/Channel.lean#L98)
- **Semantic digest:** `12581803695258776670`
- **Direct displayed dependencies:** `TraceableAgency.Dist`

```lean
Channel.ActionKernel.{u_5, u_6} (A : Type u_5) (A' : Type u_6) [Fintype A'] :
  Type (max u_5 u_6)
:=
fun A A' [Fintype A'] ↦ A → Dist A'
```

- **Lean declaration:** [`TraceableAgency.Channel.actionPushforward`](../TraceableAgency/Basic/Channel.lean#L101)
- **Semantic digest:** `6157906047038377069`
- **Direct displayed dependencies:** `TraceableAgency.Channel.ActionKernel`, `TraceableAgency.Dist`

```lean
Channel.actionPushforward.{u_1, u_3} {A : Type u_1} {A' : Type u_3} [Fintype A]
  (q : Dist A) [Fintype A'] (S : Channel.ActionKernel A A') : Dist A'
:=
fun {A} {A'} [Fintype A] q [Fintype A'] S ↦
  { prob := fun a' ↦ ∑ a, q.prob a * (S a).prob a', nonneg := ⋯, sum_eq_one := ⋯ }
```

- **Lean declaration:** [`TraceableAgency.Theorem1.IsActionProcessorCompletion`](../TraceableAgency/Theorem1/Statements.lean#L237)
- **Semantic digest:** `17187015432221310934`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Channel.ActionKernel`, `TraceableAgency.Channel.actionPushforward`, `TraceableAgency.Dist`

```lean
IsActionProcessorCompletion.{u} {O A B R : Type u} [Fintype O] [Fintype A]
  [Fintype B] [DecidableEq B] [Fintype R] (K : Channel A (O × R)) (q : Dist A)
  (S : Channel.ActionKernel A B) (Khat : Channel B (O × R)) : Prop
:=
fun {O A B R} [Fintype O] [Fintype A] [Fintype B] [DecidableEq B] [Fintype R] K q S Khat ↦
  ∀ (b : B) (z : O × R),
    (Channel.actionPushforward q S).prob b * (Khat b).prob z =
      ∑ a, q.prob a * (S a).prob b * (K a).prob z
```

**Mathematical form**

$$
S:A\longrightarrow\Delta(B),
\qquad
(qS)(b)=\sum_aq(a)S(b\mid a),
$$

$$
\widehat K\in\mathcal C(q,K,S)
\;\Longleftrightarrow\;
(qS)(b)\widehat K(o,r\mid b)
=\sum_aq(a)S(b\mid a)K(o,r\mid a)
\quad\forall(b,o,r).
$$
If $(qS)(b)=0$, the equation leaves the row $\widehat K(\cdot\mid b)$ unrestricted.

### Compounding and reached-branch posterior

**Notation-table digest:** `2252631408241139898`

- **Lean declaration:** [`TraceableAgency.BranchPositive`](../TraceableAgency/Basic/Sequential.lean#L106)
- **Semantic digest:** `8749280428706923896`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Channel.outcomeMarginal`, `TraceableAgency.Dist`

```lean
BranchPositive.{u} {A O₁ : Type u} [Fintype A] [Fintype O₁] (P₁ : Channel A O₁)
  (q : Dist A) (o₁ : O₁) : Prop
:=
fun {A O₁} [Fintype A] [Fintype O₁] P₁ q o₁ ↦ (P₁.outcomeMarginal q).prob o₁ > 0
```

- **Lean declaration:** [`TraceableAgency.Channel.posterior`](../TraceableAgency/Basic/Channel.lean#L57)
- **Semantic digest:** `11494829257050371606`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Channel.outcomeMarginal`, `TraceableAgency.Dist`, `TraceableAgency.Dist.pure`

```lean
Channel.posterior.{u_1, u_2} {A : Type u_1} {O : Type u_2} [Fintype A] [Fintype O]
  (P : Channel A O) (q : Dist A) [DecidableEq A] [Nonempty A] (o : O) : Dist A
:=
fun {A} {O} [Fintype A] [Fintype O] P q [DecidableEq A] [Nonempty A] o ↦
  if h : (P.outcomeMarginal q).prob o > 0 then
    { prob := fun a ↦ q.prob a * (P a).prob o / (P.outcomeMarginal q).prob o, nonneg := ⋯,
      sum_eq_one := ⋯ }
  else Dist.pure (Classical.arbitrary A)
```

- **Lean declaration:** [`TraceableAgency.branchPosterior`](../TraceableAgency/Basic/Sequential.lean#L110)
- **Semantic digest:** `16045898879070265776`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Channel.posterior`, `TraceableAgency.Dist`

```lean
branchPosterior.{u} {A O₁ : Type u} [Fintype A] [Fintype O₁] [DecidableEq A]
  [Nonempty A] (P₁ : Channel A O₁) (q : Dist A) (o₁ : O₁) : Dist A
:=
fun {A O₁} [Fintype A] [Fintype O₁] [DecidableEq A] [Nonempty A] P₁ q o₁ ↦ P₁.posterior q o₁
```

- **Lean declaration:** [`TraceableAgency.Theorem1.binaryContinuationProfile`](../TraceableAgency/Theorem1/Statements.lean#L405)
- **Semantic digest:** `15720643512007234173`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Theorem1.RelevanceBit`

```lean
binaryContinuationProfile.{u, u_1} {O A R : Type u} [Fintype O] [Fintype A]
  [Fintype R] (K M : Channel A (O × R)) (b : Theorem1.RelevanceBit) : Channel A (O × R)
:=
fun {O A R} [Fintype O] [Fintype A] [Fintype R] K M b ↦ if b.down = true then K else M
```

- **Lean declaration:** [`TraceableAgency.Theorem1.commonPayoffCompound`](../TraceableAgency/Theorem1/Statements.lean#L255)
- **Semantic digest:** `840348379578697617`
- **Direct displayed dependencies:** `TraceableAgency.Channel`

```lean
commonPayoffCompound.{u} {O A Y : Type u} [Fintype O] [DecidableEq O]
  [Fintype A] [Fintype Y] [DecidableEq Y] (Rec : Y → Type u) [(y : Y) → Fintype (Rec y)]
  [(y : Y) → DecidableEq (Rec y)] (P : Channel A Y) (K : (y : Y) → Channel A (O × Rec y)) :
  Channel A (O × (y : Y) × Rec y)
:=
fun {O A Y} [Fintype O] [DecidableEq O] [Fintype A] [Fintype Y] [DecidableEq Y] Rec
    [(y : Y) → Fintype (Rec y)] [(y : Y) → DecidableEq (Rec y)] P K ↦
  Relabeling.relabelChannel (Equiv.refl A) (Theorem1.compoundPayoffRecordEquiv Y O Rec)
    (seqComposeDep P (fun y ↦ O × Rec y) K)
```

- **Lean declaration:** [`TraceableAgency.Theorem1.binaryPayoffCompound`](../TraceableAgency/Theorem1/Statements.lean#L412)
- **Semantic digest:** `16530189085883151794`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Theorem1.RelevanceBit`, `TraceableAgency.Theorem1.binaryContinuationProfile`, `TraceableAgency.Theorem1.commonPayoffCompound`

```lean
binaryPayoffCompound.{u} {O A R : Type u} [Fintype O] [DecidableEq O]
  [Fintype A] [Fintype R] [DecidableEq R] (P : Channel A Theorem1.RelevanceBit)
  (K M : Channel A (O × R)) : Channel A (O × (_ : Theorem1.RelevanceBit) × R)
:=
fun {O A R} [Fintype O] [DecidableEq O] [Fintype A] [Fintype R] [DecidableEq R] P K M ↦
  Theorem1.commonPayoffCompound (fun x ↦ R) P (Theorem1.binaryContinuationProfile K M)
```

**Mathematical form**

$$
\mathcal B=\{1,2\},\qquad K^{1}=K,\quad K^{2}=M,
$$

$$
m_y=\sum_aq(a)P(y\mid a),
\qquad
\operatorname{Reached}(y)\;\Longleftrightarrow\;m_y>0,
\qquad
q_y(a)=\frac{q(a)P(y\mid a)}{m_y}\quad(m_y>0),
$$

$$
\bigl(P\triangleright\{K_y\}\bigr)(o,(y,r)\mid a)
=P(y\mid a)K_y(o,r\mid a).
$$
`RelevanceBit` is Lean's lifted copy of the two-point set $\mathcal B$, with `true` denoting branch $1$. Lean totalizes $q_y$ arbitrarily when $m_y=0$; A8 uses it only under $m_1>0$.

## Behavioral hypotheses A1--A8

### A1 — Weak order

**Notation-table digest:** `1216866732925634990`

- **Lean declaration:** [`TraceableAgency.Theorem1.A1_WeakOrder`](../TraceableAgency/Theorem1/Statements.lean#L270)
- **Semantic digest:** `1465150968597649591`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`

```lean
A1_WeakOrder.{u} {O : Type u} [Fintype O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
:=
fun {O} [Fintype O] F ↦
  ∀ {A R : Type u} [inst_1 : Fintype A] [inst_2 : DecidableEq A] [inst_3 : Nonempty A]
    [inst_4 : Fintype R] [inst_5 : DecidableEq R] [inst_6 : Nonempty R] (K : Channel A (O × R)),
    (∀ (q p : Dist A), F.rel K q p ∨ F.rel K p q) ∧
      ∀ (q p s : Dist A), F.rel K q p → F.rel K p s → F.rel K q s
```

**Mathematical form**

$$
\forall K:\quad
\bigl[\forall q,p,\ q\succeq_Kp\ \vee\ p\succeq_Kq\bigr]
\ \wedge\
\bigl[\forall q,p,s,\ (q\succeq_Kp\wedge p\succeq_Ks)\Rightarrow q\succeq_Ks\bigr].
$$

### A2 — Continuity

**Notation-table digest:** `8713092991046026218`

- **Lean declaration:** [`TraceableAgency.Theorem1.A2_Continuity`](../TraceableAgency/Theorem1/Statements.lean#L283)
- **Semantic digest:** `14939957541921655930`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.ChannelConverges`, `TraceableAgency.Dist`, `TraceableAgency.DistConverges`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`

```lean
A2_Continuity.{u} {O : Type u} [Fintype O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
:=
fun {O} [Fintype O] F ↦
  ∀ {A R : Type u} [inst_1 : Fintype A] [inst_2 : DecidableEq A] [inst_3 : Nonempty A]
    [inst_4 : Fintype R] [inst_5 : DecidableEq R] [inst_6 : Nonempty R]
    (Kseq : ℕ → Channel A (O × R)) (K : Channel A (O × R)) (qseq pseq : ℕ → Dist A) (q p : Dist A),
    ChannelConverges Kseq K →
      DistConverges qseq q →
        DistConverges pseq p → (∀ (n : ℕ), F.rel (Kseq n) (qseq n) (pseq n)) → F.rel K q p
```

**Mathematical form**

$$
K_n\to K,\quad q_n\to q,\quad p_n\to p,
\quad q_n\succeq_{K_n}p_n\ \forall n
\quad\Longrightarrow\quad
q\succeq_Kp.
$$
This sequential formulation is the paper's closed-graph condition on finite-dimensional simplexes.

### A3 — Material relevance

**Notation-table digest:** `16455787697364003011`

- **Lean declaration:** [`TraceableAgency.Theorem1.A3_MaterialRelevance`](../TraceableAgency/Theorem1/Statements.lean#L483)
- **Semantic digest:** `7337469190973383015`
- **Direct displayed dependencies:** `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily.strictRel`, `TraceableAgency.Theorem1.RelevanceBit`, `TraceableAgency.Theorem1.materialRelevanceBenchmarkChannel`, `TraceableAgency.Theorem1.materialRelevanceBetterPrior`, `TraceableAgency.Theorem1.materialRelevanceWorsePrior`

```lean
A3_MaterialRelevance.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
:=
fun {O} [Fintype O] [DecidableEq O] F ↦
  ∃ oplus ominus,
    oplus ≠ ominus ∧
      F.strictRel (Theorem1.materialRelevanceBenchmarkChannel oplus ominus)
        Theorem1.materialRelevanceBetterPrior Theorem1.materialRelevanceWorsePrior
```

**Mathematical form**

$$
\exists o^+\ne o^-:\qquad
q^+\succ_{K^{\mathrm{mat}}(o^+,o^-)}q^-.
$$

### A4 — Trace relevance

**Notation-table digest:** `10995866575715353382`

- **Lean declaration:** [`TraceableAgency.Theorem1.A4_TraceRelevance`](../TraceableAgency/Theorem1/Statements.lean#L532)
- **Semantic digest:** `13496947008377560474`
- **Direct displayed dependencies:** `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily.strictRel`, `TraceableAgency.Theorem1.RelevanceBit`, `TraceableAgency.Theorem1.traceRelevanceBenchmarkChannel`, `TraceableAgency.Theorem1.traceRelevanceRevealingPrior`, `TraceableAgency.Theorem1.traceRelevanceUnrevealingPrior`

```lean
A4_TraceRelevance.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
:=
fun {O} [Fintype O] [DecidableEq O] F ↦
  ∃ ostar,
    F.strictRel (Theorem1.traceRelevanceBenchmarkChannel ostar)
      Theorem1.traceRelevanceRevealingPrior Theorem1.traceRelevanceUnrevealingPrior
```

**Mathematical form**

$$
\exists o_*:\qquad
q^{\mathrm{rev}}\succ_{K^{\mathrm{trace}}(o_*)}q^{\mathrm{unrev}}.
$$

### A5 — Block-comparison coherence

**Notation-table digest:** `17837758072067121139`

- **Lean declaration:** [`TraceableAgency.Theorem1.A5_BlockComparisonCoherence`](../TraceableAgency/Theorem1/Statements.lean#L298)
- **Semantic digest:** `8269551603746333342`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.commonPayoffBlockEmbed`, `TraceableAgency.Theorem1.commonPayoffBlockFamilyChannel`, `TraceableAgency.Theorem1.pairWeak`

```lean
A5_BlockComparisonCoherence.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
A5_BlockComparisonCoherence.duplication.{u} {O : Type u} [Fintype O]
  [DecidableEq O] {F : Theorem1.FixedPayoffPrefFamily O}
  (self : Theorem1.A5_BlockComparisonCoherence F) {A R : Type u} [Fintype A] [DecidableEq A]
  [Nonempty A] [Fintype R] [DecidableEq R] [Nonempty R] (K : Channel A (O × R)) (q p : Dist A) :
  F.rel K q p ↔ Theorem1.pairWeak F q K p K
A5_BlockComparisonCoherence.irrelevant_blocks.{u} {O : Type u} [Fintype O]
  [DecidableEq O] {F : Theorem1.FixedPayoffPrefFamily O}
  (self : Theorem1.A5_BlockComparisonCoherence F) {I : Type u} [Fintype I] [DecidableEq I]
  [Nonempty I] (Act Rec : I → Type u) [(i : I) → Fintype (Act i)] [(i : I) → DecidableEq (Act i)]
  [∀ (i : I), Nonempty (Act i)] [(i : I) → Fintype (Rec i)] [(i : I) → DecidableEq (Rec i)]
  [∀ (i : I), Nonempty (Rec i)] (K : (i : I) → Channel (Act i) (O × Rec i)) (i j : I) (_hij : i ≠ j)
  (qi : Dist (Act i)) (qj : Dist (Act j)) :
  F.rel (Theorem1.commonPayoffBlockFamilyChannel Act Rec K)
      (Theorem1.commonPayoffBlockEmbed Act i qi) (Theorem1.commonPayoffBlockEmbed Act j qj) ↔
    Theorem1.pairWeak F qi (K i) qj (K j)
```

**Mathematical form**

$$
q\succeq_Kp
\;\Longleftrightarrow\;
(q,K)\succeq(p,K),
$$

$$
q_i^i\succeq_{\bigsqcup_{k\in I}K_k}q_j^j
\;\Longleftrightarrow\;
(q_i,K_i)\succeq(q_j,K_j)
\qquad(i\ne j).
$$

### A6 — Record data processing

**Notation-table digest:** `14121598915854886194`

- **Lean declaration:** [`TraceableAgency.Theorem1.A6_RecordDataProcessing`](../TraceableAgency/Theorem1/Statements.lean#L324)
- **Semantic digest:** `9491519550516184277`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.RecordProcessor`, `TraceableAgency.Theorem1.pairWeak`, `TraceableAgency.Theorem1.recordPostprocess`

```lean
A6_RecordDataProcessing.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
:=
fun {O} [Fintype O] [DecidableEq O] F ↦
  ∀ {A R S : Type u} [inst_2 : Fintype A] [inst_3 : DecidableEq A] [inst_4 : Nonempty A]
    [inst_5 : Fintype R] [inst_6 : DecidableEq R] [inst_7 : Nonempty R] [inst_8 : Fintype S]
    [inst_9 : DecidableEq S] [inst_10 : Nonempty S] (K : Channel A (O × R))
    (T : Theorem1.RecordProcessor O R S) (q : Dist A),
    Theorem1.pairWeak F q K q (Theorem1.recordPostprocess K T)
```

**Mathematical form**

$$
(q,K)\succeq(q,KT)
\qquad\text{for every payoff-preserving record processor }T.
$$

### A7 — Action data processing

**Notation-table digest:** `11507377022127669171`

- **Lean declaration:** [`TraceableAgency.Theorem1.A7_ActionDataProcessing`](../TraceableAgency/Theorem1/Statements.lean#L336)
- **Semantic digest:** `11223628019742019799`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Channel.ActionKernel`, `TraceableAgency.Channel.actionPushforward`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.IsActionProcessorCompletion`, `TraceableAgency.Theorem1.pairWeak`

```lean
A7_ActionDataProcessing.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
:=
fun {O} [Fintype O] [DecidableEq O] F ↦
  ∀ {A B R : Type u} [inst_2 : Fintype A] [inst_3 : DecidableEq A] [inst_4 : Nonempty A]
    [inst_5 : Fintype B] [inst_6 : DecidableEq B] [inst_7 : Nonempty B] [inst_8 : Fintype R]
    [inst_9 : DecidableEq R] [inst_10 : Nonempty R] (K : Channel A (O × R)) (q : Dist A)
    (S : Channel.ActionKernel A B) (Khat : Channel B (O × R)),
    Theorem1.IsActionProcessorCompletion K q S Khat →
      Theorem1.pairWeak F q K (Channel.actionPushforward q S) Khat
```

**Mathematical form**

For every $K,q,S$ and every completion $\widehat K$,
$$
\widehat K\in\mathcal C(q,K,S)
\quad\Longrightarrow\quad
(q,K)\succeq(qS,\widehat K).
$$

### A8 — Recordwise sure-thing principle

**Notation-table digest:** `1470273905402432495`

- **Lean declaration:** [`TraceableAgency.Theorem1.A8_RecordwiseSureThing`](../TraceableAgency/Theorem1/Statements.lean#L423)
- **Semantic digest:** `17844348579965632081`
- **Direct displayed dependencies:** `TraceableAgency.BranchPositive`, `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.RelevanceBit`, `TraceableAgency.Theorem1.binaryPayoffCompound`, `TraceableAgency.Theorem1.pairWeak`, `TraceableAgency.branchPosterior`

```lean
A8_RecordwiseSureThing.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
:=
fun {O} [Fintype O] [DecidableEq O] F ↦
  ∀ {A R : Type u} [inst_2 : Fintype A] [inst_3 : DecidableEq A] [inst_4 : Nonempty A]
    [inst_5 : Fintype R] [inst_6 : DecidableEq R] [inst_7 : Nonempty R] (q : Dist A)
    (P : Channel A Theorem1.RelevanceBit) (K L M : Channel A (O × R)),
    BranchPositive P q { down := true } →
      (Theorem1.pairWeak F (branchPosterior P q { down := true }) K
          (branchPosterior P q { down := true }) L ↔
        Theorem1.pairWeak F q (Theorem1.binaryPayoffCompound P K M) q
          (Theorem1.binaryPayoffCompound P L M))
```

**Mathematical form**

$$
m_1>0
\quad\Longrightarrow\quad
\left[
(q_1,K)\succeq(q_1,L)
\;\Longleftrightarrow\;
\bigl(q,P\triangleright(K,M)\bigr)
\succeq
\bigl(q,P\triangleright(L,M)\bigr)
\right].
$$

### The A1--A8 bundle

**Notation-table digest:** `12484844005081508185`

- **Lean declaration:** [`TraceableAgency.Theorem1.TraceTemperedAxiomsV10`](../TraceableAgency/Theorem1/Statements.lean#L563)
- **Semantic digest:** `16614439461526955671`
- **Direct displayed dependencies:** `TraceableAgency.Theorem1.A1_WeakOrder`, `TraceableAgency.Theorem1.A2_Continuity`, `TraceableAgency.Theorem1.A3_MaterialRelevance`, `TraceableAgency.Theorem1.A4_TraceRelevance`, `TraceableAgency.Theorem1.A5_BlockComparisonCoherence`, `TraceableAgency.Theorem1.A6_RecordDataProcessing`, `TraceableAgency.Theorem1.A7_ActionDataProcessing`, `TraceableAgency.Theorem1.A8_RecordwiseSureThing`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`

```lean
TraceTemperedAxiomsV10.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) : Prop
TraceTemperedAxiomsV10.a1.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A1_WeakOrder F
TraceTemperedAxiomsV10.a2.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A2_Continuity F
TraceTemperedAxiomsV10.a3.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A3_MaterialRelevance F
TraceTemperedAxiomsV10.a4.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A4_TraceRelevance F
TraceTemperedAxiomsV10.a5.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A5_BlockComparisonCoherence F
TraceTemperedAxiomsV10.a6.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A6_RecordDataProcessing F
TraceTemperedAxiomsV10.a7.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A7_ActionDataProcessing F
TraceTemperedAxiomsV10.a8.{u} {O : Type u} [Fintype O] [DecidableEq O]
  {F : Theorem1.FixedPayoffPrefFamily O} (self : Theorem1.TraceTemperedAxiomsV10 F) :
  Theorem1.A8_RecordwiseSureThing F
```

**Mathematical form**

$$
\operatorname{TraceTempered}(F)
\;\Longleftrightarrow\;
\mathrm{A1}(F)\wedge\mathrm{A2}(F)\wedge\cdots\wedge\mathrm{A8}(F).
$$

## Representation and Theorem 1

### Nonconstant payoff index

**Notation-table digest:** `6928858777674543698`

- **Lean declaration:** [`TraceableAgency.Theorem1.IsConstantPayoffIndex`](../TraceableAgency/Theorem1/Statements.lean#L459)
- **Semantic digest:** `1124002949444679785`
- **Direct displayed dependencies:** none

```lean
IsConstantPayoffIndex.{u} {O : Type u} (u : O → ℝ) : Prop
:=
fun {O} u ↦ ∃ c, ∀ (o : O), u o = c
```

**Mathematical form**

$$
\operatorname{Constant}(u)
\;\Longleftrightarrow\;
\exists c\in\mathbb R\ \forall o\in O,\ u(o)=c.
$$

### Expected payoff utility

**Notation-table digest:** `16728523515726560004`

- **Lean declaration:** [`TraceableAgency.Theorem1.expectedPayoffUtility`](../TraceableAgency/Theorem1/Statements.lean#L605)
- **Semantic digest:** `8492606770170108885`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`

```lean
expectedPayoffUtility.{u} {O A R : Type u} [Fintype O] [Fintype A]
  [Fintype R] (u : O → ℝ) (q : Dist A) (K : Channel A (O × R)) : ℝ
:=
fun {O A R} [Fintype O] [Fintype A] [Fintype R] u q K ↦ ∑ a, q.prob a * ∑ z, (K a).prob z * u z.1
```

**Mathematical form**

$$
\mathbb E_{qK}[u(O)]
=\sum_{a\in A}q(a)\sum_{(o,r)\in O\times R}K(o,r\mid a)u(o).
$$

### Trace-tempered value

**Notation-table digest:** `9021719702313101286`

- **Lean declaration:** [`TraceableAgency.Theorem1.traceTemperedValue`](../TraceableAgency/Theorem1/Statements.lean#L614)
- **Semantic digest:** `16911926577790640204`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.expectedPayoffUtility`, `TraceableAgency.mutualInfo`

```lean
traceTemperedValue.{u} {O A R : Type u} [Fintype O] [Fintype A] [Fintype R]
  (u : O → ℝ) (lambda : ℝ) (q : Dist A) (K : Channel A (O × R)) : ℝ
:=
fun {O A R} [Fintype O] [Fintype A] [Fintype R] u lambda q K ↦
  Theorem1.expectedPayoffUtility u q K + lambda * I(q, K)
```

**Mathematical form**

$$
V_{u,\lambda}(q,K)
=\mathbb E_{qK}[u(O)]+\lambda I_{qK}(A;(O,R)).
$$

### Within-channel representation

**Notation-table digest:** `9612557011117339497`

- **Lean declaration:** [`TraceableAgency.Theorem1.WithinChannelRepresentation`](../TraceableAgency/Theorem1/Statements.lean#L623)
- **Semantic digest:** `7686164762215987098`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.traceTemperedValue`

```lean
WithinChannelRepresentation.{u} {O : Type u} [Fintype O]
  (F : Theorem1.FixedPayoffPrefFamily O) (u : O → ℝ) (lambda : ℝ) : Prop
:=
fun {O} [Fintype O] F u lambda ↦
  ∀ {A R : Type u} [inst_1 : Fintype A] [inst_2 : DecidableEq A] [inst_3 : Nonempty A]
    [inst_4 : Fintype R] [inst_5 : DecidableEq R] [inst_6 : Nonempty R] (K : Channel A (O × R))
    (q p : Dist A),
    F.rel K q p ↔
      Theorem1.traceTemperedValue u lambda q K ≥ Theorem1.traceTemperedValue u lambda p K
```

**Mathematical form**

$$
\forall A,R,K,q,p:\qquad
q\succeq_Kp
\;\Longleftrightarrow\;
V_{u,\lambda}(q,K)\ge V_{u,\lambda}(p,K).
$$

### Same-witness block representation

**Notation-table digest:** `9108239023875280547`

- **Lean declaration:** [`TraceableAgency.Theorem1.SameWitnessBlockRepresentation`](../TraceableAgency/Theorem1/Statements.lean#L636)
- **Semantic digest:** `5078930150581620154`
- **Direct displayed dependencies:** `TraceableAgency.Channel`, `TraceableAgency.Dist`, `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.commonPayoffBlockEmbed`, `TraceableAgency.Theorem1.commonPayoffBlockFamilyChannel`, `TraceableAgency.Theorem1.traceTemperedValue`

```lean
SameWitnessBlockRepresentation.{u} {O : Type u} [Fintype O] [DecidableEq O]
  (F : Theorem1.FixedPayoffPrefFamily O) (u : O → ℝ) (lambda : ℝ) : Prop
:=
fun {O} [Fintype O] [DecidableEq O] F u lambda ↦
  ∀ {I : Type u} [inst_2 : Fintype I] [inst_3 : DecidableEq I] [inst_4 : Nonempty I]
    (Act Rec : I → Type u) [inst_5 : (i : I) → Fintype (Act i)]
    [inst_6 : (i : I) → DecidableEq (Act i)] [inst_7 : ∀ (i : I), Nonempty (Act i)]
    [inst_8 : (i : I) → Fintype (Rec i)] [inst_9 : (i : I) → DecidableEq (Rec i)]
    [inst_10 : ∀ (i : I), Nonempty (Rec i)] (K : (i : I) → Channel (Act i) (O × Rec i)) (i j : I),
    i ≠ j →
      ∀ (qi : Dist (Act i)) (qj : Dist (Act j)),
        F.rel (Theorem1.commonPayoffBlockFamilyChannel Act Rec K)
            (Theorem1.commonPayoffBlockEmbed Act i qi) (Theorem1.commonPayoffBlockEmbed Act j qj) ↔
          Theorem1.traceTemperedValue u lambda qi (K i) ≥
            Theorem1.traceTemperedValue u lambda qj (K j)
```

**Mathematical form**

$$
\forall i\ne j:\qquad
q_i^i\succeq_{\bigsqcup_{k\in I}K_k}q_j^j
\;\Longleftrightarrow\;
V_{u,\lambda}(q_i,K_i)\ge V_{u,\lambda}(q_j,K_j).
$$

### Exact Theorem 1 proposition

**Notation-table digest:** `16466454770381399877`

- **Lean declaration:** [`TraceableAgency.Theorem1.Theorem1StatementV10`](../TraceableAgency/Theorem1/Statements.lean#L659)
- **Semantic digest:** `14278482988949351309`
- **Direct displayed dependencies:** `TraceableAgency.Theorem1.FixedPayoffPrefFamily`, `TraceableAgency.Theorem1.IsConstantPayoffIndex`, `TraceableAgency.Theorem1.SameWitnessBlockRepresentation`, `TraceableAgency.Theorem1.TraceTemperedAxiomsV10`, `TraceableAgency.Theorem1.WithinChannelRepresentation`

```lean
Theorem1StatementV10.{u} : Prop
:=
∀ (O : Type u) [inst : Fintype O] [inst_1 : DecidableEq O],
  2 ≤ Fintype.card O →
    ∀ (F : Theorem1.FixedPayoffPrefFamily O),
      (Theorem1.TraceTemperedAxiomsV10 F ↔
          ∃ u lambda,
            ¬Theorem1.IsConstantPayoffIndex u ∧
              0 < lambda ∧ Theorem1.WithinChannelRepresentation F u lambda) ∧
        (Theorem1.TraceTemperedAxiomsV10 F →
          ∃ u lambda,
            ¬Theorem1.IsConstantPayoffIndex u ∧
              0 < lambda ∧
                Theorem1.WithinChannelRepresentation F u lambda ∧
                  Theorem1.SameWitnessBlockRepresentation F u lambda)
```

- **Lean declaration:** [`TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1`](../TraceableAgency/Theorem1/Proof.lean#L24)
- **Semantic digest:** `15893867817468804230`
- **Direct displayed dependencies:** `TraceableAgency.Theorem1.Theorem1StatementV10`

```lean
TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1.{u} :
  Theorem1.Theorem1StatementV10
```

**Mathematical form**

For every finite payoff alphabet $O$ with $|O|\ge2$, and every preference family $F$,
$$
\operatorname{TraceTempered}(F)
\;\Longleftrightarrow\;
\exists u:O\to\mathbb R,\ \exists\lambda>0:\quad
\neg\operatorname{Constant}(u)
\ \wedge\
\operatorname{WithinRep}(F,u,\lambda).
$$
Moreover, under $\operatorname{TraceTempered}(F)$, there exist witnesses $u,\lambda$ satisfying the same conditions and both
$\operatorname{WithinRep}(F,u,\lambda)$ and
$\operatorname{SameWitnessBlockRep}(F,u,\lambda)$.

## Mechanical closure boundary

The following project declarations are reached recursively but are intentionally suppressed from the mathematical narrative because they implement relabelling, tagged sums, block embeddings, stochastic-matrix multiplication, or proof plumbing. Their presence is recorded so the boundary cannot change silently.

- [`TraceableAgency.blockEmbedProb`](../TraceableAgency/Basic/Blocks.lean#L223) — digest `6729830563138558743`
- [`TraceableAgency.blockEmbedDist`](../TraceableAgency/Basic/Blocks.lean#L231) — digest `3017623100414520112`
- [`TraceableAgency.Relabeling.relabelDist`](../TraceableAgency/Basic/Relabeling.lean#L22) — digest `13341639695179977356`
- [`TraceableAgency.Relabeling.relabelChannel`](../TraceableAgency/Basic/Relabeling.lean#L53) — digest `1477451035549381788`
- [`TraceableAgency.Theorem1.sigmaPayoffRecordEquiv`](../TraceableAgency/Theorem1/Statements.lean#L93) — digest `11640830431178070124`
- [`TraceableAgency.blockFamilyProb`](../TraceableAgency/Basic/Blocks.lean#L185) — digest `3200125330769597397`
- [`TraceableAgency.blockFamilyChannel`](../TraceableAgency/Basic/Blocks.lean#L195) — digest `4835000864612080323`
- [`TraceableAgency.inlDist`](../TraceableAgency/Basic/Blocks.lean#L59) — digest `7654861251413294358`
- [`TraceableAgency.inrDist`](../TraceableAgency/Basic/Blocks.lean#L73) — digest `384734842618295813`
- [`TraceableAgency.Theorem1.sumPayoffRecordEquiv`](../TraceableAgency/Theorem1/Statements.lean#L74) — digest `7403256905891189482`
- [`TraceableAgency.blockChannel`](../TraceableAgency/Basic/Blocks.lean#L28) — digest `6037056846512664890`
- [`TraceableAgency.Channel.postprocess`](../TraceableAgency/Basic/Channel.lean#L89) — digest `10592634098425469289`
- [`TraceableAgency.Theorem1.payoffPreservingRecordKernel`](../TraceableAgency/Theorem1/Statements.lean#L205) — digest `6311034054595265474`
- [`TraceableAgency.Theorem1.compoundPayoffRecordEquiv`](../TraceableAgency/Theorem1/Statements.lean#L249) — digest `15927897305599562700`
- [`TraceableAgency.seqComposeDepProb`](../TraceableAgency/Basic/Sequential.lean#L64) — digest `12038917831625314240`
- [`TraceableAgency.seqComposeDep`](../TraceableAgency/Basic/Sequential.lean#L73) — digest `212269108301297199`

### Generated local interfaces

Constructors, recursors, projections, and compiler-generated helpers are not part of the paper narrative, but their exact names and semantic digests remain in the mechanical audit.

- `TraceableAgency.Dist.mk` — digest `66304387525365865`
- `TraceableAgency.Dist.prob` — digest `5051023992170546215`
- `TraceableAgency.Theorem1.FixedPayoffPrefFamily.rel` — digest `3828116497522547698`
- `TraceableAgency.Theorem1.sumPayoffRecordEquiv.match_1` — digest `9882830250930794083`
- `TraceableAgency.Theorem1.sumPayoffRecordEquiv.match_3` — digest `7555000022113894980`
- `TraceableAgency.Theorem1.traceRelevanceBenchmarkChannel.match_1` — digest `1489070832350639079`
- `TraceableAgency.blockChannel.match_1` — digest `7799100506272077844`
