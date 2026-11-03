import TraceableAgency.Theorem1.MaterialCalibration.Proof
import TraceableAgency.Theorem1.MaterialCalibration.Audit

/-!
# Dependency audit of the complete material-first representation

The audit traverses proof bodies, not imports. Generic Shannon/Faddeev and
information identities are permitted; the old preference-to-information
calibration and representation route is excluded.
-/

open Lean Elab Command

namespace TraceableAgency.Theorem1.MaterialCalibration.RepresentationAudit

open Audit

def forbiddenRepresentationModulePrefixes : List String :=
  Audit.forbiddenModulePrefixes.filter fun modulePrefix =>
    modulePrefix != "TraceableAgency.PureTrace.Support.GenericFaddeev"

def forbiddenRepresentationNameFragments : List String :=
  [ "globalTraceLambda"
  , "traceLambdaAtPrior"
  , "pureTraceRepresentation"
  , "provedPureTraceSufficiency"
  , "provedPureTraceCharacterization"
  , "inducedPureRepresentation"
  , "constantPayoff_blockRepresentation"
  , "supportBranchInsertionScale_eq_branchMass_of_nontrivialSupport"
  , "positiveBranchPayoffIncrement_of_nontrivialSupport"
  , "positiveBranchPayoffIncrementFormula"
  ]

/-- Exact generic declarations housed in the old mixed-purpose Faddeev file.
These are binary vectors, the abstract Faddeev hypothesis interface, and
finite probability calculations for revealing a partition. Their proof-body
closures remain audited; no preference or scale theorem is exempted. -/
def allowedGenericDeclarations : List Name :=
  Audit.allowedSharedHelperDeclarations ++
    [ ``TraceableAgency.faddeevBinaryDistInterior
    , ``TraceableAgency.faddeevBinaryDistInterior_fullSupport
    , ``TraceableAgency.FiniteFaddeevStandardHypotheses
    , ``TraceableAgency.SatisfiesFiniteFaddeevRecursion
    , ``TraceableAgency.coarseRevealChannel
    , ``TraceableAgency.coarseProjectKernel
    , ``TraceableAgency.coarseRefineKernel
    , ``TraceableAgency.outcomeMarginal_coarseReveal_sigmaDist
    , ``TraceableAgency.actionPushforward_sigmaDist_coarseProject
    , ``TraceableAgency.actionPushforward_coarseRefine
    , ``TraceableAgency.coarseReveal_isBayesPushforwardCompletion_project
    , ``TraceableAgency.coarseReveal_isBayesPushforwardCompletion_refine
    , ``TraceableAgency.posterior_coarseReveal_sigmaDist_of_pos
    , ``TraceableAgency.posteriorLawIntegral_coarseReveal_sigmaDist_Hfun_of_blockEmbed
    ]

def forbiddenRepresentationReasons (env : Environment) (name : Name) : List String :=
  let fromName :=
    if name.toString.startsWith "TraceableAgency" then
      forbiddenRepresentationNameFragments.filter fun fragment =>
        name.toString.contains fragment
    else []
  let fromModule :=
    if allowedGenericDeclarations.any (fun helper => helper.isPrefixOf name) then []
    else match declarationModule? env name with
      | none => []
      | some moduleName =>
          forbiddenRepresentationModulePrefixes.filter fun modulePrefix =>
            moduleName.toString.startsWith modulePrefix
  fromName ++ fromModule

def auditedRepresentationRoots : List Name :=
  [ ``TraceableAgency.Theorem1.MaterialCalibration.materialEntropy_binary_continuous
  , ``TraceableAgency.Theorem1.MaterialCalibration.materialTraceValue_eq_entropy_sub_expected
  , ``TraceableAgency.Theorem1.MaterialCalibration.materialEntropy_sigmaDist
  , ``TraceableAgency.Theorem1.MaterialCalibration.materialEntropy_faddeev_hypotheses
  , ``TraceableAgency.Theorem1.MaterialCalibration.exists_pos_materialEntropy_eq_entropy
  , ``TraceableAgency.Theorem1.MaterialCalibration.materialNormalizedValueFormula_of_constantRecordValueFormula
  , ``TraceableAgency.Theorem1.MaterialCalibration.traceTemperedBridgeAxioms_imply_representation_and_block_material
  , ``TraceableAgency.Theorem1.MaterialCalibration.theorem1StatementV10_material
  , ``TraceTemperedChoiceVerification.trace_tempered_choice_v10_theorem1_material
  ]

run_cmd do
  let env ← getEnv
  -- A shared transitive closure scans every requested root while avoiding
  -- repeated traversal of the generic Shannon theorem's analytic library.
  let closure := declarationClosure env auditedRepresentationRoots
  let forbidden := closure.toList.filter fun name =>
    !(forbiddenRepresentationReasons env name).isEmpty
  let projectCount := (closure.toList.filter fun name =>
    name.toString.startsWith "TraceableAgency").length
  logInfo m!"MATERIAL_REPRESENTATION_DEPENDENCIES roots={auditedRepresentationRoots.length} closure={closure.size} project={projectCount} forbidden={forbidden.length}"
  unless forbidden.isEmpty do
    for name in forbidden do
      logError m!"FORBIDDEN_MATERIAL_REPRESENTATION_DEPENDENCY {name}: {forbiddenRepresentationReasons env name}"
    throwError "material-first representation dependency audit failed"
  for root in auditedRepresentationRoots do
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.toList.filter fun name =>
      !(allowedKernelAxioms.contains name)
    logInfo m!"MATERIAL_REPRESENTATION_AXIOMS root={root} axioms={axioms.toList} unexpected={unexpected.length}"
    unless unexpected.isEmpty do
      for name in unexpected do
        logError m!"UNEXPECTED_MATERIAL_REPRESENTATION_AXIOM root={root} axiom={name}"
      throwError m!"material-first representation kernel axiom audit failed at {root}"

end TraceableAgency.Theorem1.MaterialCalibration.RepresentationAudit
