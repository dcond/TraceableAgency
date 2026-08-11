/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.Proof
import Lean.Util.FoldConsts

/-!
# Transitive dependency audit for the paper-faithful route

This compile-time audit recursively follows the types and bodies of the public
pure-trace theorem, the public main characterization, and Theorem 1.  The build
fails if any declaration on those paths uses the superseded global
posterior-continuity / posterior-integral / `FinalHMInterface` route or the old
all-representatives relabelling assumption.
-/

open Lean Elab Command

namespace TraceableAgency.Audit.Dependencies

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

def forbiddenNameFragments : List String :=
  [ "PosteriorIntegralRepresentation"
  , "posteriorIntegralRepresentation"
  , "finitePosteriorIntegralRepresentation_of_finite"
  , "marginalValue"
  , "PosteriorLawContinuity"
  , "posteriorLawContinuity"
  , "FinalHMInterface"
  , "provedFinalHMInterface"
  , "FinitePosteriorValueRelabelingAssumptions"
  ]

def forbiddenMatches (name : Name) : List String :=
  forbiddenNameFragments.filter fun fragment =>
    name.toString.contains fragment

def auditedRoots : List Name :=
  [ ``TraceableAgency.pureTraceRepresentation_of_conditions
  , ``TraceableAgency.provedPureTraceSufficiency
  , ``TraceableAgency.provedPureTraceCharacterization
  , ``TraceableAgency.Theorem1.trace_tempered_choice_v3_theorem1
  ]

run_cmd do
  let env ← getEnv
  for root in auditedRoots do
    let closure := declarationClosure env [root]
    let forbidden := closure.toList.filter fun name =>
      !(forbiddenMatches name).isEmpty
    logInfo m!"DEPENDENCY_AUDIT root={root} closure={closure.size} forbidden={forbidden.length}"
    unless forbidden.isEmpty do
      for name in forbidden do
        logError m!"FORBIDDEN_DEPENDENCY {name}: {forbiddenMatches name}"
      throwError m!"paper-faithful dependency audit failed at {root}"

end TraceableAgency.Audit.Dependencies
