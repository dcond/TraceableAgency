/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Main
import TraceableAgency.External.GenericFaddeev
import TraceableAgency.External.EntropyReductionClosure

/-!
# Main Theorem Assembly and Audit Boundary

This file exposes the convention-free main characterization.  The exact finite
Faddeev theorem needed by the proof is now proved in
`TraceableAgency.External.GenericFaddeev`; there is no remaining external
mathematical theorem parameter at the public boundary.

The exact generic Herstein--Milnor theorem for sequentially closed independent
weak orders and interior mixtures is proved in
`TraceableAgency.External.GenericHersteinMilnor`.
Finite same-posterior-law Blackwell equivalence is proved internally by an
explicit posterior-class matching kernel.
Posterior-law continuity is derived in Lean from the ordinal axioms A1--A4
(including primitive A2); the continuous barycentric grid and spread/merge
approximation are constructed explicitly in Lean. Finite posterior-law extensionality is
also proved internally by interpolation on the finite supports. The representative's
support restriction, relabelling covariance, and cardinal scale alignment are
also derived internally after canonical full-revelation normalization.  No
support/relabel convention or constructed-representative package occurs at the
public theorem boundary. Both finite data-processing inequalities are proved
internally from concavity of Shannon entropy.
-/

set_option linter.style.header false

namespace TraceableAgency

universe u

/-- Sufficiency from the auditable finite classical theorem boundary. -/
theorem SufficiencyStatement_of_FinalHM
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u}) :
    SufficiencyStatement.{u} := by
  intro F hax
  exact MIRep_of_TraceAxioms_FinalHM_Faddeev hfad hhm hax

/-- The trace axioms characterize mutual-information preferences. -/
theorem MainCharacterization_of_FinalHM
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u}) :
    MainCharacterization.{u} := by
  intro F
  constructor
  · exact (SufficiencyStatement_of_FinalHM hfad hhm) F
  · exact BenchmarkStatement_of_MIRep F

/-- Full characterization, including the block same-scale moreover clause.

The assumptions contain no posterior continuity premise and no normalization,
support-face, relabelling, or representative-coherence convention. -/
theorem MainCharacterizationWithMoreover_of_FinalHM
    (hfad : ClassicalFaddeevTheoremAssumptions.{u})
    (hhm : FinalHMInterface.{u}) :
    MainCharacterizationWithMoreover.{u} := by
  apply main_characterization_from_spine
  · exact SufficiencyStatement_of_FinalHM hfad hhm
  · exact BenchmarkStatement_of_MIRep
  · exact blockScaleStatement_from_sufficiency
      (SufficiencyStatement_of_FinalHM hfad hhm)
      blockScaleFromMIRepStatement

/-- Compatibility theorem with Herstein--Milnor discharged internally and the
Faddeev audit schema supplied explicitly. The closed public theorem below
supplies its proved inhabitant. -/
theorem SufficiencyStatement_of_Faddeev
    (hfad : ClassicalFaddeevTheoremAssumptions.{u}) :
    SufficiencyStatement.{u} :=
  SufficiencyStatement_of_FinalHM hfad provedFinalHMInterface

/-- Main characterization with the exact generic HM schema proved in Lean. -/
theorem MainCharacterization_of_Faddeev
    (hfad : ClassicalFaddeevTheoremAssumptions.{u}) :
    MainCharacterization.{u} :=
  MainCharacterization_of_FinalHM hfad provedFinalHMInterface

/-- Public convention-free characterization, including the moreover clause.
Its sole external mathematical input is Faddeev's entropy theorem. -/
theorem MainCharacterizationWithMoreover_of_Faddeev
    (hfad : ClassicalFaddeevTheoremAssumptions.{u}) :
    MainCharacterizationWithMoreover.{u} :=
  MainCharacterizationWithMoreover_of_FinalHM hfad provedFinalHMInterface

/-! ## Closed public theorem surface -/

/-- The axioms imply mutual-information representation, with both generic
mathematical interfaces discharged by Lean proofs. -/
theorem provedSufficiencyStatement :
    SufficiencyStatement.{u} :=
  SufficiencyStatement_of_Faddeev
    GenericFaddeev.provedClassicalFaddeevTheoremAssumptions

/-- The paper's main equivalence, with no theorem-interface parameter. -/
theorem provedMainCharacterization :
    MainCharacterization.{u} :=
  MainCharacterization_of_Faddeev
    GenericFaddeev.provedClassicalFaddeevTheoremAssumptions

/-- The paper's complete main theorem, including the same-scale block clause,
with no convention and no external mathematical theorem parameter. -/
theorem provedMainCharacterizationWithMoreover :
    MainCharacterizationWithMoreover.{u} :=
  MainCharacterizationWithMoreover_of_Faddeev
    GenericFaddeev.provedClassicalFaddeevTheoremAssumptions

end TraceableAgency
