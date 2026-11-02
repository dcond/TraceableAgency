/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MaterialCalibration.Public
import TraceableAgency.Theorem1.MaterialCalibration.BranchComparison
import TraceableAgency.Theorem1.MaterialCalibration.PayoffSeparation
import Lean.Util.FoldConsts
import Lean.Util.CollectAxioms

/-!
# Audit of material-first branch calibration

The checks below recursively traverse the types and proof bodies of the new
calibration endpoints.  They check actual declaration dependencies, rather
than module imports: generic block and affine tools may live in modules that
also contain unrelated information results.

The build fails if a calibration endpoint uses an information/entropy
declaration, one of the old trace-calibration modules, or a kernel axiom
outside the explicit Lean/Mathlib foundation whitelist.
-/

open Lean Elab Command

namespace TraceableAgency.Theorem1.MaterialCalibration.Audit

partial def declarationClosure
    (env : Environment) (todo : List Name) (seen : NameSet := {}) : NameSet :=
  match todo with
  | [] => seen
  | name :: rest =>
      if seen.contains name then
        declarationClosure env rest seen
      else
        let seen := seen.insert name
        match env.find? name with
        | none => declarationClosure env rest seen
        | some info =>
            declarationClosure env
              (info.getUsedConstantsAsSet.toList ++ rest) seen

def declarationModule? (env : Environment) (name : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? name
  env.header.moduleNames[idx.toNat]?

/-- These are the old calibration/identification routes, not generic affine
or finite-channel helper modules. Prefix matching also covers submodules. -/
def forbiddenModulePrefixes : List String :=
  [ "TraceableAgency.Theorem1.BranchScaleIdentification"
  , "TraceableAgency.Theorem1.GlobalTraceScale"
  , "TraceableAgency.Theorem1.ConstantTraceAnchorGeneral"
  , "TraceableAgency.Theorem1.TraceScaleTools"
  , "TraceableAgency.Theorem1.PureMIAffine"
  , "TraceableAgency.Theorem1.PositiveBranchIncrement"
  , "TraceableAgency.Theorem1.FullSupportValueAssembly"
  , "TraceableAgency.Theorem1.RepresentationAssembly"
  , "TraceableAgency.Theorem1.TheoremClosure"
  , "TraceableAgency.Theorem1.Proof"
  , "TraceableAgency.PureTrace.Support.ScaleCoherence"
  , "TraceableAgency.PureTrace.Support.EntropyReduction"
  , "TraceableAgency.PureTrace.Support.FullPreEntropyClosure"
  , "TraceableAgency.PureTrace.Support.PreEntropyConstruction"
  , "TraceableAgency.PureTrace.Support.PreEntropyReady"
  , "TraceableAgency.PureTrace.Support.GenericFaddeev"
  , "TraceableAgency.PureTrace.Support.Faddeev"
  , "TraceableAgency.PureTrace.Theorem"
  ]

/-- Name checks additionally exclude information definitions and the old
representation endpoints in modules that also supply permissible helpers. -/
def forbiddenProjectNameFragments : List String :=
  [ "mutualInfo"
  , "entropy"
  , "Entropy"
  , "Faddeev"
  , "globalTraceLambda"
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

/-- Two existing generic helpers happen to be stored in old information
modules: the relevance bridge uses deterministic pushforward composition,
and payoff-lottery mixing uses the binary vector `(t, 1-t)`. Only their
module-origin checks (including generated proof constants) are exempted;
their entire proof-body dependency closures are still inspected. Neither
helper contains an information or value functional. -/
def allowedSharedHelperDeclarations : List Name :=
  [ ``TraceableAgency.actionPushforward_pure_comp
  , ``TraceableAgency.faddeevBinaryDist
  ]

def forbiddenReasons (env : Environment) (name : Name) : List String :=
  let fromName :=
    if name.toString.startsWith "TraceableAgency" then
      forbiddenProjectNameFragments.filter fun fragment =>
        name.toString.contains fragment
    else []
  let fromModule :=
    if allowedSharedHelperDeclarations.any (fun helper => helper.isPrefixOf name) then []
    else match declarationModule? env name with
      | none => []
      | some moduleName =>
          forbiddenModulePrefixes.filter fun modulePrefix =>
            moduleName.toString.startsWith modulePrefix
  fromName ++ fromModule

def allowedKernelAxioms : List Name :=
  [ ``propext, ``Classical.choice, ``Quot.sound ]

def auditedRoots : List Name :=
  [ ``TraceableAgency.Theorem1.MaterialCalibration.revealMaterialUnit_eq_one
  , ``TraceableAgency.Theorem1.MaterialCalibration.supportBranchInsertionScale_eq_branchMass_material
  , ``TraceableAgency.Theorem1.MaterialCalibration.normalizedMarkedUtility_supportInsertion_difference_material
  , ``TraceableAgency.Theorem1.MaterialCalibration.branchCalibration_of_axioms
  , ``TraceableAgency.Theorem1.MaterialCalibration.normalizedMarkedUtility_compound_oneBranch_difference_material
  , ``TraceableAgency.Theorem1.MaterialCalibration.normalizedMarkedUtility_payoffBranch_difference_from_low_material
  ]

run_cmd do
  let env ← getEnv
  for root in auditedRoots do
    let closure := declarationClosure env [root]
    let forbidden := closure.toList.filter fun name =>
      !(forbiddenReasons env name).isEmpty
    let projectCount := (closure.toList.filter fun name =>
      name.toString.startsWith "TraceableAgency").length
    logInfo m!"MATERIAL_CALIBRATION_DEPENDENCIES root={root} closure={closure.size} project={projectCount} forbidden={forbidden.length}"
    unless forbidden.isEmpty do
      for name in forbidden do
        logError m!"FORBIDDEN_MATERIAL_CALIBRATION_DEPENDENCY {name}: {forbiddenReasons env name}"
      throwError m!"material-first dependency audit failed at {root}"
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.toList.filter fun name =>
      !(allowedKernelAxioms.contains name)
    logInfo m!"MATERIAL_CALIBRATION_AXIOMS root={root} axioms={axioms.toList} unexpected={unexpected.length}"
    unless unexpected.isEmpty do
      for name in unexpected do
        logError m!"UNEXPECTED_MATERIAL_CALIBRATION_AXIOM root={root} axiom={name}"
      throwError m!"material-first kernel axiom audit failed at {root}"

end TraceableAgency.Theorem1.MaterialCalibration.Audit

#print axioms TraceableAgency.Theorem1.MaterialCalibration.revealMaterialUnit_eq_one
#print axioms TraceableAgency.Theorem1.MaterialCalibration.supportBranchInsertionScale_eq_branchMass_material
#print axioms TraceableAgency.Theorem1.MaterialCalibration.normalizedMarkedUtility_supportInsertion_difference_material
#print axioms TraceableAgency.Theorem1.MaterialCalibration.branchCalibration_of_axioms
#print axioms TraceableAgency.Theorem1.MaterialCalibration.normalizedMarkedUtility_compound_oneBranch_difference_material
#print axioms TraceableAgency.Theorem1.MaterialCalibration.normalizedMarkedUtility_payoffBranch_difference_from_low_material
