/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Statement
import TraceableAgency.PureTrace.Support.GenericFaddeev
import TraceableAgency.PureTrace.Proof.Final

/-!
# Pure-trace theorem

The public endpoint closes the finite Herstein--Milnor and Faddeev ingredients
inside Lean.  Its only hypotheses are the six pure-trace conditions induced by
the main paper axioms.
-/

namespace TraceableAgency

universe u

/-! ## Kernel-closed endpoints -/

/-- The induced pure-trace conditions imply mutual-information representation. -/
theorem provedPureTraceSufficiency :
    PureTraceSufficiency.{u} :=
  pureTraceSufficiency_of_faddeev
    GenericFaddeev.provedClassicalFaddeevTheoremAssumptions

/-- Equivalence between the induced conditions and mutual-information representation. -/
theorem provedPureTraceEquivalence :
    PureTraceCharacterization.{u} := by
  intro F
  exact ⟨provedPureTraceSufficiency F, pureTraceNecessity_of_representation F⟩

/-- Pure-trace characterization including common-scale finite-block comparisons. -/
theorem provedPureTraceCharacterization :
    PureTraceCharacterizationWithBlocks.{u} :=
  pureTraceCharacterization_from_components
    provedPureTraceSufficiency
    pureTraceNecessity_of_representation
    (pureTraceBlockConclusion_from_sufficiency
      provedPureTraceSufficiency
      pureTraceBlocksFromRepresentation_proved)

end TraceableAgency
