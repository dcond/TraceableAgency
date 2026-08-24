/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.Proof
import Lean.DeclarationRange
import Lean.DocString
import Lean.Elab.Print
import Lean.Util.FoldConsts

/-!
# Mechanical Theorem 1 specification generator

This generator starts at the public Theorem 1 declaration and the certified
identity connecting the paper's likelihood-ratio formula to Lean's entropy
definition of mutual information.  It follows their types and the bodies of
definitions used by those types, but never unfolds a theorem declaration.
Project definitions outside the paper-facing vocabulary and every external
dependency declaration are retained only as named boundary items.

The generated mathematical display is deliberately small and fail-closed: it
is a version-controlled notation layer for the finite paper vocabulary, not a
general Lean-to-LaTeX translator.  The exact elaborated Lean declaration is
printed beside every displayed formula.
-/

open Lean Elab Command System

namespace TraceableAgency.Audit.Theorem1Spec

private def rootDeclaration : Name :=
  `TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1

private def paperNotationRoot : Name :=
  `TraceableAgency.mutualInfoLikelihoodRatio_eq_mutualInfo

private def semanticRoots : List Name := [rootDeclaration, paperNotationRoot]

structure WalkState where
  gray : NameSet := {}
  black : NameSet := {}
  order : Array Name := #[]
  externalLeaves : NameSet := {}
  autoDecls : NameSet := {}
  generatedInterfaces : NameSet := {}

abbrev WalkM := StateT WalkState CoreM

def moduleNameOf? (env : Environment) (decl : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? decl
  env.header.moduleNames[idx.toNat]?

def isProjectDecl (env : Environment) (decl : Name) : Bool :=
  match moduleNameOf? env decl with
  | none => false
  | some modName =>
      modName == `TraceableAgency ||
        modName.toString.startsWith "TraceableAgency."

def isProofConstant (env : Environment) (decl : Name) : Bool :=
  (env.find? decl).any (·.isTheorem)

def addSemanticConsts (env : Environment) (s : NameSet) (e : Expr) : NameSet :=
  e.foldConsts s fun n acc =>
    if isProofConstant env n then acc else acc.insert n

/-- Expressions that determine the statement-facing meaning of a declaration.
The public theorem contributes only its type.  Definition bodies contribute,
but theorem constants occurring in proof fields are removed by
`addSemanticConsts`. -/
def visibleExprs (env : Environment) (decl : Name)
    (info : ConstantInfo) : List Expr :=
  let typeOnly := [info.type]
  match info with
  | .defnInfo d =>
      if (env.getProjectionFnInfo? decl).isSome then typeOnly
      else d.value :: typeOnly
  | .inductInfo iv =>
      iv.ctors.foldl (init := typeOnly) fun es ctor =>
        match env.find? ctor with
        | some ctorInfo => ctorInfo.type :: es
        | none => es
  | .thmInfo _ => typeOnly
  | .opaqueInfo _ => typeOnly
  | .axiomInfo _ => typeOnly
  | .quotInfo _ => typeOnly
  | .ctorInfo _ => typeOnly
  | .recInfo _ => typeOnly

def semanticConstants (env : Environment) (decl : Name) : NameSet :=
  match env.find? decl with
  | none => {}
  | some info =>
      (visibleExprs env decl info).foldl (addSemanticConsts env) {}

def directProjectDeps (env : Environment) (decl : Name) : List Name :=
  (semanticConstants env decl).toList
    |>.filter (fun n => n != decl && isProjectDecl env n)
    |>.mergeSort (fun a b => a.toString < b.toString)

def directExternalLeaves (env : Environment) (decl : Name) : List Name :=
  (semanticConstants env decl).toList
    |>.filter (fun n => !isProjectDecl env n)
    |>.mergeSort (fun a b => a.toString < b.toString)

partial def visit (env : Environment) (decl : Name) : WalkM Unit := do
  let st ← get
  if st.black.contains decl then return
  if st.gray.contains decl then
    throwError "cycle in Theorem 1 specification dependency graph at {decl}"
  modify fun s => { s with gray := s.gray.insert decl }
  for ext in directExternalLeaves env decl do
    modify fun s => { s with externalLeaves := s.externalLeaves.insert ext }
  for dep in directProjectDeps env decl do
    visit env dep
  modify fun s =>
    let gray := s.gray.erase decl
    let black := s.black.insert decl
    let info? := env.find? decl
    let generated :=
      (env.getProjectionFnInfo? decl).isSome ||
        info?.any (fun info =>
          match info with
          | .ctorInfo _ | .recInfo _ => true
          | _ => false)
    let s := { s with gray := gray }
    let s := { s with black := black }
    if generated then
      { s with generatedInterfaces := s.generatedInterfaces.insert decl }
    else if env.isAutoDecl decl then
      { s with autoDecls := s.autoDecls.insert decl }
    else
      { s with order := s.order.push decl }

def collectClosure : CoreM WalkState := do
  let env ← getEnv
  let mut st : WalkState := {}
  for root in semanticRoots do
    unless isProjectDecl env root do
      throwError "specification root is not in a TraceableAgency module: {root}"
    let (_, next) ← (visit env root).run st
    st := next
  return st

inductive Section where
  | domain
  | axioms
  | representation
  deriving BEq

def Section.title : Section → String
  | .domain => "Domain and paper notation"
  | .axioms => "Behavioral hypotheses A1--A8"
  | .representation => "Representation and Theorem 1"

structure PaperEntry where
  part : Section
  title : String
  declarations : List Name
  math : String

private def paperEntries : List PaperEntry :=
  [ { part := .domain
      title := "Finite lotteries"
      declarations :=
        [ `TraceableAgency.Dist
        , `TraceableAgency.Dist.pure
        , `TraceableAgency.Dist.uniform
        ]
      math := r#"\[
\Delta(A)=\left\{q:A\to\mathbb R_{\ge0}:\sum_{a\in A}q(a)=1\right\},
\qquad
\delta_a(b)=\mathbf 1_{\{b=a\}},
\qquad
\operatorname{unif}_{A}(a)=\frac1{|A|}.
\]"# }
  , { part := .domain
      title := "Channels and visible-consequence marginal"
      declarations :=
        [ `TraceableAgency.Channel
        , `TraceableAgency.Channel.outcomeMarginal
        ]
      math := r#"\[
K:A\longrightarrow\Delta(X),
\qquad
p_{qK}(x)=\sum_{a\in A}q(a)K(x\mid a).
\]"# }
  , { part := .domain
      title := "Entropy and mutual information"
      declarations :=
        [ `TraceableAgency.entropyTerm
        , `TraceableAgency.entropy
        , `TraceableAgency.mutualInfo
        , `TraceableAgency.mutualInfoLikelihoodRatioTerm
        , `TraceableAgency.mutualInfoLikelihoodRatio
        , `TraceableAgency.mutualInfoLikelihoodRatio_eq_mutualInfo
        ]
      math := r#"\[
h(x)=\begin{cases}0,&x\le0,\\-x\log x,&x>0,\end{cases}
\qquad
H(q)=\sum_a h(q(a)).
\]
\[
I_{qK}(A;X)=H(p_{qK})-\sum_a q(a)H(K(\cdot\mid a))
=\sum_{a,x}\tau\!\left(q(a)K(x\mid a),K(x\mid a),p_{qK}(x)\right),
\]
where
\[
\tau(j,c,m)=\begin{cases}0,&j=0,\\j\log(c/m),&j\ne0.\end{cases}
\]
The last equality is the checked theorem `mutualInfoLikelihoodRatio_eq_mutualInfo`.
Lean's `Real.log` is the natural logarithm; changing to another base greater than one rescales the positive coefficient \(\lambda\)."# }
  , { part := .domain
      title := "Preference family and strict part"
      declarations :=
        [ `TraceableAgency.Theorem1.FixedPayoffPrefFamily
        , `TraceableAgency.Theorem1.FixedPayoffPrefFamily.strictRel
        ]
      math := r#"\[
q\succeq_K p\;\Longleftrightarrow\;F.\mathrm{rel}(K,q,p),
\qquad
q\succ_Kp\;\Longleftrightarrow\;
q\succeq_Kp\ \wedge\ \neg(p\succeq_Kq).
\]"# }
  , { part := .domain
      title := "Block comparison environments"
      declarations :=
        [ `TraceableAgency.Theorem1.commonPayoffBlockChannel
        , `TraceableAgency.Theorem1.leftBlockDist
        , `TraceableAgency.Theorem1.rightBlockDist
        , `TraceableAgency.Theorem1.pairWeak
        , `TraceableAgency.Theorem1.commonPayoffBlockFamilyChannel
        , `TraceableAgency.Theorem1.commonPayoffBlockEmbed
        ]
      math := r#"\[
(K\sqcup L)(o,(r,0)\mid(a,0))=K(o,r\mid a),
\qquad
(K\sqcup L)(o,(s,1)\mid(b,1))=L(o,s\mid b),
\]
with every cross-block probability equal to zero, and
\[
q^0(a,0)=q(a),\quad q^0(b,1)=0,\qquad
p^1(a,0)=0,\quad p^1(b,1)=p(b),
\]
\[
(q,K)\succeq(p,L)
\;\Longleftrightarrow\;
q^0\succeq_{K\sqcup L}p^1.
\]
For a finite family,
\[
\left(\bigsqcup_{i\in I}K_i\right)(o,(j,r)\mid(i,a))
=\begin{cases}K_i(o,r\mid a),&j=i,\\0,&j\ne i,\end{cases}
\qquad
q_i^i(j,a)=\begin{cases}q_i(a),&j=i,\\0,&j\ne i.\end{cases}
\]"# }
  , { part := .domain
      title := "Pointwise convergence"
      declarations :=
        [ `TraceableAgency.DistConverges
        , `TraceableAgency.ChannelConverges
        ]
      math := r#"\[
q_n\to q\;\Longleftrightarrow\;q_n(a)\to q(a)\ \forall a,
\qquad
K_n\to K\;\Longleftrightarrow\;K_n(x\mid a)\to K(x\mid a)\ \forall(a,x).
\]"# }
  , { part := .domain
      title := "Material-relevance benchmark"
      declarations :=
        [ `TraceableAgency.Theorem1.RelevanceBit
        , `TraceableAgency.Theorem1.materialRelevanceBenchmarkChannel
        , `TraceableAgency.Theorem1.materialRelevanceBetterPrior
        , `TraceableAgency.Theorem1.materialRelevanceWorsePrior
        ]
      math := r#"\[
A=\{a^+,a^-\},\qquad
K(o^+,*\mid a^+)=K(o^-,*\mid a^-)=1,
\qquad
q^+=\delta_{a^+},\quad q^-=\delta_{a^-}.
\]"# }
  , { part := .domain
      title := "Trace-relevance benchmark"
      declarations :=
        [ `TraceableAgency.Theorem1.traceRelevanceFairPrior
        , `TraceableAgency.Theorem1.traceRelevanceBenchmarkChannel
        , `TraceableAgency.Theorem1.traceRelevanceRevealingPrior
        , `TraceableAgency.Theorem1.traceRelevanceUnrevealingPrior
        ]
      math := r#"\[
q^{\mathrm{rev}}=\tfrac12(\delta_{a_1}+\delta_{a_2}),
\qquad
q^{\mathrm{unrev}}=\tfrac12(\delta_{a_3}+\delta_{a_4}),
\]
\[
K(o_*,r_i\mid a_i)=1\ (i=1,2),
\qquad
K(o_*,r_j\mid a_i)=\tfrac12\ (i=3,4;\ j=1,2).
\]"# }
  , { part := .domain
      title := "Record processing"
      declarations :=
        [ `TraceableAgency.Theorem1.RecordProcessor
        , `TraceableAgency.Theorem1.recordPostprocess
        ]
      math := r#"\[
T:O\times R\longrightarrow\Delta(S),
\qquad
(KT)(o,s\mid a)=\sum_{r\in R}K(o,r\mid a)T(s\mid o,r).
\]
Lean stores only the new-record distribution \(T(\cdot\mid o,r)\); `recordPostprocess` copies \(o\), so this is exactly a payoff-preserving kernel on \(O\times S\)."# }
  , { part := .domain
      title := "Action processing"
      declarations :=
        [ `TraceableAgency.Channel.ActionKernel
        , `TraceableAgency.Channel.actionPushforward
        , `TraceableAgency.Theorem1.IsActionProcessorCompletion
        ]
      math := r#"\[
S:A\longrightarrow\Delta(B),
\qquad
(qS)(b)=\sum_aq(a)S(b\mid a),
\]
\[
\widehat K\in\mathcal C(q,K,S)
\;\Longleftrightarrow\;
(qS)(b)\widehat K(o,r\mid b)
=\sum_aq(a)S(b\mid a)K(o,r\mid a)
\quad\forall(b,o,r).
\]
If \((qS)(b)=0\), the equation leaves the row \(\widehat K(\cdot\mid b)\) unrestricted."# }
  , { part := .domain
      title := "Compounding and reached-branch posterior"
      declarations :=
        [ `TraceableAgency.BranchPositive
        , `TraceableAgency.Channel.posterior
        , `TraceableAgency.branchPosterior
        , `TraceableAgency.Theorem1.binaryContinuationProfile
        , `TraceableAgency.Theorem1.commonPayoffCompound
        , `TraceableAgency.Theorem1.binaryPayoffCompound
        ]
      math := r#"\[
\mathcal B=\{1,2\},\qquad K^{1}=K,\quad K^{2}=M,
\]
\[
m_y=\sum_aq(a)P(y\mid a),
\qquad
\operatorname{Reached}(y)\;\Longleftrightarrow\;m_y>0,
\qquad
q_y(a)=\frac{q(a)P(y\mid a)}{m_y}\quad(m_y>0),
\]
\[
\bigl(P\triangleright\{K_y\}\bigr)(o,(y,r)\mid a)
=P(y\mid a)K_y(o,r\mid a).
\]
`RelevanceBit` is Lean's lifted copy of the two-point set \(\mathcal B\), with `true` denoting branch \(1\). Lean totalizes \(q_y\) arbitrarily when \(m_y=0\); A8 uses it only under \(m_1>0\)."# }
  , { part := .axioms
      title := "A1 — Weak order"
      declarations := [ `TraceableAgency.Theorem1.A1_WeakOrder ]
      math := r#"\[
\forall K:\quad
\bigl[\forall q,p,\ q\succeq_Kp\ \vee\ p\succeq_Kq\bigr]
\ \wedge\
\bigl[\forall q,p,s,\ (q\succeq_Kp\wedge p\succeq_Ks)\Rightarrow q\succeq_Ks\bigr].
\]"# }
  , { part := .axioms
      title := "A2 — Continuity"
      declarations := [ `TraceableAgency.Theorem1.A2_Continuity ]
      math := r#"\[
K_n\to K,\quad q_n\to q,\quad p_n\to p,
\quad q_n\succeq_{K_n}p_n\ \forall n
\quad\Longrightarrow\quad
q\succeq_Kp.
\]
This sequential formulation is the paper's closed-graph condition on finite-dimensional simplexes."# }
  , { part := .axioms
      title := "A3 — Material relevance"
      declarations := [ `TraceableAgency.Theorem1.A3_MaterialRelevance ]
      math := r#"\[
\exists o^+\ne o^-:\qquad
q^+\succ_{K^{\mathrm{mat}}(o^+,o^-)}q^-.
\]"# }
  , { part := .axioms
      title := "A4 — Trace relevance"
      declarations := [ `TraceableAgency.Theorem1.A4_TraceRelevance ]
      math := r#"\[
\exists o_*:\qquad
q^{\mathrm{rev}}\succ_{K^{\mathrm{trace}}(o_*)}q^{\mathrm{unrev}}.
\]"# }
  , { part := .axioms
      title := "A5 — Block-comparison coherence"
      declarations := [ `TraceableAgency.Theorem1.A5_BlockComparisonCoherence ]
      math := r#"\[
q\succeq_Kp
\;\Longleftrightarrow\;
(q,K)\succeq(p,K),
\]
\[
q_i^i\succeq_{\bigsqcup_{k\in I}K_k}q_j^j
\;\Longleftrightarrow\;
(q_i,K_i)\succeq(q_j,K_j)
\qquad(i\ne j).
\]"# }
  , { part := .axioms
      title := "A6 — Record data processing"
      declarations := [ `TraceableAgency.Theorem1.A6_RecordDataProcessing ]
      math := r#"\[
(q,K)\succeq(q,KT)
\qquad\text{for every payoff-preserving record processor }T.
\]"# }
  , { part := .axioms
      title := "A7 — Action data processing"
      declarations := [ `TraceableAgency.Theorem1.A7_ActionDataProcessing ]
      math := r#"For every \(K,q,S\) and every completion \(\widehat K\),
\[
\widehat K\in\mathcal C(q,K,S)
\quad\Longrightarrow\quad
(q,K)\succeq(qS,\widehat K).
\]"# }
  , { part := .axioms
      title := "A8 — Recordwise sure-thing principle"
      declarations := [ `TraceableAgency.Theorem1.A8_RecordwiseSureThing ]
      math := r#"\[
m_1>0
\quad\Longrightarrow\quad
\left[
(q_1,K)\succeq(q_1,L)
\;\Longleftrightarrow\;
\bigl(q,P\triangleright(K,M)\bigr)
\succeq
\bigl(q,P\triangleright(L,M)\bigr)
\right].
\]"# }
  , { part := .axioms
      title := "The A1--A8 bundle"
      declarations := [ `TraceableAgency.Theorem1.TraceTemperedAxiomsV10 ]
      math := r#"\[
\operatorname{TraceTempered}(F)
\;\Longleftrightarrow\;
\mathrm{A1}(F)\wedge\mathrm{A2}(F)\wedge\cdots\wedge\mathrm{A8}(F).
\]"# }
  , { part := .representation
      title := "Nonconstant payoff index"
      declarations := [ `TraceableAgency.Theorem1.IsConstantPayoffIndex ]
      math := r#"\[
\operatorname{Constant}(u)
\;\Longleftrightarrow\;
\exists c\in\mathbb R\ \forall o\in O,\ u(o)=c.
\]"# }
  , { part := .representation
      title := "Expected payoff utility"
      declarations := [ `TraceableAgency.Theorem1.expectedPayoffUtility ]
      math := r#"\[
\mathbb E_{qK}[u(O)]
=\sum_{a\in A}q(a)\sum_{(o,r)\in O\times R}K(o,r\mid a)u(o).
\]"# }
  , { part := .representation
      title := "Trace-tempered value"
      declarations := [ `TraceableAgency.Theorem1.traceTemperedValue ]
      math := r#"\[
V_{u,\lambda}(q,K)
=\mathbb E_{qK}[u(O)]+\lambda I_{qK}(A;(O,R)).
\]"# }
  , { part := .representation
      title := "Within-channel representation"
      declarations := [ `TraceableAgency.Theorem1.WithinChannelRepresentation ]
      math := r#"\[
\forall A,R,K,q,p:\qquad
q\succeq_Kp
\;\Longleftrightarrow\;
V_{u,\lambda}(q,K)\ge V_{u,\lambda}(p,K).
\]"# }
  , { part := .representation
      title := "Same-witness block representation"
      declarations := [ `TraceableAgency.Theorem1.SameWitnessBlockRepresentation ]
      math := r#"\[
\forall i\ne j:\qquad
q_i^i\succeq_{\bigsqcup_{k\in I}K_k}q_j^j
\;\Longleftrightarrow\;
V_{u,\lambda}(q_i,K_i)\ge V_{u,\lambda}(q_j,K_j).
\]"# }
  , { part := .representation
      title := "Exact Theorem 1 proposition"
      declarations :=
        [ `TraceableAgency.Theorem1.Theorem1StatementV10
        , `TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1
        ]
      math := r#"For every finite payoff alphabet \(O\) with \(|O|\ge2\), and every preference family \(F\),
\[
\operatorname{TraceTempered}(F)
\;\Longleftrightarrow\;
\exists u:O\to\mathbb R,\ \exists\lambda>0:\quad
\neg\operatorname{Constant}(u)
\ \wedge\
\operatorname{WithinRep}(F,u,\lambda).
\]
Moreover, under \(\operatorname{TraceTempered}(F)\), there exist witnesses \(u,\lambda\) satisfying the same conditions and both
\(\operatorname{WithinRep}(F,u,\lambda)\) and
\(\operatorname{SameWitnessBlockRep}(F,u,\lambda)\)."# }
  ]

/-- Locks each handwritten mathematical block to the elaborated semantics of
the declarations it translates.  A Lean-side change therefore requires an
explicit review of that block before this digest can be updated. -/
private def expectedPaperEntryDigests : List UInt64 :=
  [ 11226582100683779610
  , 10868161788146472416
  , 14900683673367227622
  , 7930570054458820236
  , 15198310688743706801
  , 8838656558664373777
  , 12813607489999281459
  , 4533690757616686921
  , 2162765498741811469
  , 6907658951114823665
  , 2252631408241139898
  , 1216866732925634990
  , 8713092991046026218
  , 16455787697364003011
  , 10995866575715353382
  , 17837758072067121139
  , 14121598915854886194
  , 11507377022127669171
  , 1470273905402432495
  , 12484844005081508185
  , 6928858777674543698
  , 16728523515726560004
  , 9021719702313101286
  , 9612557011117339497
  , 9108239023875280547
  , 16466454770381399877
  ]

/-- Pins the entire project-local closure, including classified infrastructure
and generated helpers, so `--update` cannot silently absorb a transitive
semantic change. -/
private def expectedClosureDigest : UInt64 := 8391076054563383822

private def displayedDeclarations : NameSet :=
  paperEntries.foldl (init := {}) fun seen entry =>
    entry.declarations.foldl (init := seen) fun seen decl => seen.insert decl

/-- Project-local implementation declarations deliberately kept outside the
paper-facing narrative.  This explicit boundary makes the generator
fail-closed when a new local dependency enters Theorem 1's semantic closure. -/
private def infrastructureDeclarations : NameSet :=
  [ `TraceableAgency.blockEmbedProb
  , `TraceableAgency.blockEmbedDist
  , `TraceableAgency.Relabeling.relabelDist
  , `TraceableAgency.Relabeling.relabelChannel
  , `TraceableAgency.Theorem1.sigmaPayoffRecordEquiv
  , `TraceableAgency.blockFamilyProb
  , `TraceableAgency.blockFamilyChannel
  , `TraceableAgency.inlDist
  , `TraceableAgency.inrDist
  , `TraceableAgency.Theorem1.sumPayoffRecordEquiv
  , `TraceableAgency.blockChannel
  , `TraceableAgency.Channel.postprocess
  , `TraceableAgency.Theorem1.payoffPreservingRecordKernel
  , `TraceableAgency.Theorem1.compoundPayoffRecordEquiv
  , `TraceableAgency.seqComposeDepProb
  , `TraceableAgency.seqComposeDep
  ].foldl (init := {}) fun seen decl => seen.insert decl

private def readableOptions (o : Options) : Options :=
  o.setBool `pp.universes false
    |>.setBool `pp.explicit false
    |>.setBool `pp.all false
    |>.setBool `pp.fullNames false
    |>.setBool `pp.proofs false
    |>.setBool `pp.unicode true
    |>.setBool `pp.unicode.fun true

def ppExprReadable (e : Expr) (width := 100) : CoreM String := do
  let fmt ← Meta.MetaM.run' <| withOptions readableOptions do Meta.ppExpr e
  return fmt.pretty width

def ppSignatureReadable (decl : Name) (width := 100) : CoreM String := do
  let fmt ← Meta.MetaM.run' <| withOptions readableOptions do
    PrettyPrinter.ppSignature decl
  return fmt.fmt.pretty width

private def shortenLean (s : String) : String :=
  s.replace "TraceableAgency.Theorem1." ""
    |>.replace "TraceableAgency." ""

private def semanticDigest (env : Environment) (decl : Name) : UInt64 :=
  match env.find? decl with
  | none => 0
  | some info =>
      (visibleExprs env decl info).foldl
        (fun h e => mixHash h (hash e)) (hash decl)

private def paperEntryDigest (env : Environment) (entry : PaperEntry) : UInt64 :=
  entry.declarations.foldl
    (fun digest decl => mixHash digest (semanticDigest env decl)) (hash entry.title)

private def sortedNames (names : NameSet) : List Name :=
  names.toList.mergeSort (fun a b => a.toString < b.toString)

private def declarationListDigest (env : Environment) (names : List Name) : UInt64 :=
  names.foldl (fun digest decl => mixHash digest (semanticDigest env decl)) 0

private def closureDigest (env : Environment) (closure : WalkState) : UInt64 :=
  declarationListDigest env (sortedNames closure.black)

private def sourcePath (moduleName : Name) : String :=
  if moduleName == `TraceableAgency then "TraceableAgency.lean"
  else moduleName.toString.replace "." "/" ++ ".lean"

private def sourceLink (decl : Name) : CoreM String := do
  let env ← getEnv
  let some moduleName := moduleNameOf? env decl
    | throwError "missing defining module for project declaration: {decl}"
  let path := sourcePath moduleName
  let some ranges ← findDeclarationRanges? decl
    | throwError "missing source range for project declaration: {decl}"
  let line := ranges.selectionRange.pos.line
  return s!"[`{decl}`](../{path}#L{line})"

private def structureFieldSignatures (decl : Name) : CoreM (List String) := do
  let env ← getEnv
  let some info := getStructureInfo? env decl | return []
  let mut result := []
  for fieldName in info.fieldNames do
    let some fieldInfo := info.fieldInfo.find? (·.fieldName == fieldName) | continue
    result := result ++ [shortenLean (← ppSignatureReadable fieldInfo.projFn)]
  return result

private def declarationBody? (decl : Name) : CoreM (Option String) := do
  let env ← getEnv
  match env.find? decl with
  | some (.defnInfo d) => return some (shortenLean (← ppExprReadable d.value))
  | _ => return none

/-- Translate the notation table's conventional LaTeX delimiters to the
native MathJax delimiters supported in Markdown files on GitHub. -/
private def githubMath (s : String) : String :=
  s.replace "\\]\n\\[" "$$\n\n$$"
    |>.replace "\\[" "$$"
    |>.replace "\\]" "$$"
    |>.replace "\\(" "$"
    |>.replace "\\)" "$"

private def renderDeclaration (decl : Name) : CoreM String := do
  let env ← getEnv
  let source ← sourceLink decl
  let signature := shortenLean (← ppSignatureReadable decl)
  let fields ← structureFieldSignatures decl
  let body? ← declarationBody? decl
  let deps := directProjectDeps env decl
    |>.filter (fun n => displayedDeclarations.contains n)
    |>.map (fun n => s!"`{n}`")
  let depsText := if deps.isEmpty then "none" else String.intercalate ", " deps
  let mut out := s!"- **Lean declaration:** {source}\n"
  out := out ++ s!"- **Semantic digest:** `{semanticDigest env decl}`\n"
  out := out ++ s!"- **Direct displayed dependencies:** {depsText}\n\n"
  out := out ++ "```lean\n" ++ signature
  for field in fields do
    out := out ++ "\n" ++ field
  if let some body := body? then
    out := out ++ "\n:=\n" ++ body
  out := out ++ "\n```\n\n"
  return out

private def validateEntries (closure : WalkState) : CoreM Unit := do
  let env ← getEnv
  let actualClosureDigest := closureDigest env closure
  unless actualClosureDigest == expectedClosureDigest do
    throwError "recursive local closure needs review: expected digest {expectedClosureDigest}, found {actualClosureDigest}"
  unless expectedPaperEntryDigests.length == paperEntries.length do
    throwError "notation-lock count does not match the paper-entry count"
  for (entry, expected) in paperEntries.zip expectedPaperEntryDigests do
    let actual := paperEntryDigest env entry
    unless actual == expected do
      throwError "notation table for '{entry.title}' needs review: expected digest {expected}, found {actual}"
  let closureSet : NameSet := closure.order.foldl (init := {}) fun s n => s.insert n
  for entry in paperEntries do
    for decl in entry.declarations do
      unless closureSet.contains decl do
        throwError "paper declaration is not in the recursive Theorem 1 closure: {decl}"
      unless isProjectDecl env decl do
        throwError "paper declaration is not project-local: {decl}"
  for decl in closure.order do
    if (env.find? decl).any fun info =>
        match info with
        | .opaqueInfo _ => true
        | _ => false then
      throwError "reachable project-local opaque declaration has no inspectable body: {decl}"
    unless displayedDeclarations.contains decl || infrastructureDeclarations.contains decl do
      throwError "unclassified project declaration in Theorem 1 semantic closure: {decl}"
  for decl in infrastructureDeclarations.toList do
    unless closureSet.contains decl do
      throwError "classified infrastructure declaration is no longer in Theorem 1 closure: {decl}"

private def renderSpecification : CoreM String := do
  let closure ← collectClosure
  validateEntries closure
  let mut out := "# Mechanical formal specification of Theorem 1\n\n"
  out := out ++ "> **Generated file — do not edit.** Regenerate with "
  out := out ++ "`./scripts/build_theorem1_spec.sh --update`.\n\n"
  out := out ++ "This document is generated from the elaborated Lean environment. "
  out := out ++ "The extractor follows the types of its two certified roots and the local definition bodies they use, "
  out := out ++ "expands structure fields, and never unfolds theorem declarations. External toolchain and dependency "
  out := out ++ "declarations are terminal boundary symbols: their implementations are not unfolded.\n\n"
  out := out ++ "The Lean blocks are authoritative: every displayed definition includes its elaborated body, "
  out := out ++ "structures include their fields, and theorem declarations include their exact signatures; only proof subterms "
  out := out ++ "inside definitions are printed as `⋯`. The mathematical blocks are produced by the small, "
  out := out ++ "version-controlled notation table in `TraceableAgency/Audit/Theorem1Spec.lean`; "
  out := out ++ "each block is locked to the semantic digests of the declarations it translates, so a Lean-side change "
  out := out ++ "stops generation until the corresponding mathematics is explicitly reviewed. The complete local closure "
  out := out ++ "has a separate lock covering transitive infrastructure and generated helpers. The generated Markdown uses "
  out := out ++ "GitHub's native MathJax delimiters, so its mathematical displays render in the repository view.\n\n"
  out := out ++ "Every reached project declaration is explicitly classified as paper-facing or infrastructure; "
  out := out ++ "generation fails if an unclassified local dependency appears.\n\n"
  out := out ++ "In the mathematical displays, computational `DecidableEq` arguments are suppressed. "
  out := out ++ "Action, record, block-index, and dependent-fibre alphabets quantified by the axioms are finite and nonempty.\n\n"
  out := out ++ s!"- **Theorem root:** `{rootDeclaration}`\n"
  out := out ++ s!"- **Paper-notation root:** `{paperNotationRoot}`\n"
  out := out ++ "- **Pinned toolchain:** [`lean-toolchain`](../lean-toolchain) (`Lean 4.32.1`)\n"
  out := out ++ s!"- **Local semantic closure:** {closure.black.toList.length} declarations\n"
  out := out ++ s!"- **Paper-facing declarations:** {displayedDeclarations.toList.length}\n"
  out := out ++ s!"- **Classified infrastructure declarations:** {infrastructureDeclarations.toList.length}\n"
  out := out ++ s!"- **Generated local interfaces:** {closure.generatedInterfaces.toList.length + closure.autoDecls.toList.length}\n"
  out := out ++ s!"- **Recursive closure digest:** `{closureDigest (← getEnv) closure}`\n"
  out := out ++ s!"- **External boundary:** {closure.externalLeaves.size} toolchain/dependency constants (not unfolded)\n\n"

  for part in [Section.domain, Section.axioms, Section.representation] do
    out := out ++ s!"## {part.title}\n\n"
    for entry in paperEntries do
      if entry.part == part then
        out := out ++ s!"### {entry.title}\n\n"
        out := out ++ s!"**Notation-table digest:** `{paperEntryDigest (← getEnv) entry}`\n\n"
        for decl in entry.declarations do
          out := out ++ (← renderDeclaration decl)
        out := out ++ "**Mathematical form**\n\n" ++ githubMath entry.math ++ "\n\n"

  let suppressed := closure.order.filter fun n => !displayedDeclarations.contains n
  out := out ++ "## Mechanical closure boundary\n\n"
  out := out ++ "The following project declarations are reached recursively but are intentionally "
  out := out ++ "suppressed from the mathematical narrative because they implement relabelling, "
  out := out ++ "tagged sums, block embeddings, stochastic-matrix multiplication, or proof plumbing. "
  out := out ++ "Their presence is recorded so the boundary cannot change silently.\n\n"
  for decl in suppressed do
    out := out ++ s!"- {← sourceLink decl} — digest `{semanticDigest (← getEnv) decl}`\n"
  out := out ++ "\n### Generated local interfaces\n\n"
  out := out ++ "Constructors, recursors, projections, and compiler-generated helpers are not part of the paper narrative, "
  out := out ++ "but their exact names and semantic digests remain in the mechanical audit.\n\n"
  let generated := sortedNames closure.generatedInterfaces ++ sortedNames closure.autoDecls
  for decl in generated do
    out := out ++ s!"- `{decl}` — digest `{semanticDigest (← getEnv) decl}`\n"
  return out

run_cmd do
  let spec ← liftCoreM renderSpecification
  liftIO <| IO.print spec

end TraceableAgency.Audit.Theorem1Spec
