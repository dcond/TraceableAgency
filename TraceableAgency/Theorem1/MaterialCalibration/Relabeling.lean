/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.CommonMarkedScale
import TraceableAgency.Theorem1.BranchInsertion

/-!
# Exact material-normalized values under relabeling

These identities use the common payoff normalization and two-way action
processing. They do not use the pure-trace representation or a numerical
branch-weight theorem.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A B R S : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype B] [DecidableEq B] [Nonempty B]
variable [Fintype R] [DecidableEq R] [Nonempty R]
variable [Fintype S] [DecidableEq S] [Nonempty S]

/-- Action relabeling preserves the common material-normalized value. -/
theorem normalizedMarkedUtility_actionEquiv
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (e : A ≃ B) (q : Dist A) (hq : q.FullSupport)
    (K : Channel A (O × R)) :
    normalizedMarkedUtility F h (Relabeling.relabelDist e q)
        (Relabeling.relabelDist_fullSupport e q hq)
        (markedExperimentOfChannel
          (Relabeling.relabelChannel e (Equiv.refl (O × R)) K)) =
      normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) := by
  let q' := Relabeling.relabelDist e q
  let K' := Relabeling.relabelChannel e (Equiv.refl (O × R)) K
  have hq' : q'.FullSupport := Relabeling.relabelDist_fullSupport e q hq
  have hf : pairWeak F q K q' K' := by
    have hh := h.a5 K q (Relabeling.actionEquivKernel e) K'
      (actionCompletion_isExact K q (Relabeling.actionEquivKernel e) K'
        (Relabeling.relabelChannel_isBayesPushforwardCompletion e K q))
    simpa [q', K', Relabeling.actionPushforward_equiv] using hh
  have hb : pairWeak F q' K' q K := by
    have hh := h.a5 K' q' (Relabeling.actionEquivKernel e.symm) K
      (actionCompletion_isExact K' q' (Relabeling.actionEquivKernel e.symm) K
        (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion e K q))
    simpa [q', K', Relabeling.actionPushforward_equiv,
      Relabeling.relabelDist_symm] using hh
  have hfv := (pairWeak_markedExperiments_iff_normalizedMarkedUtility
    F h q q' hq hq' (markedExperimentOfChannel K)
      (markedExperimentOfChannel K')).mp hf
  have hbv := (pairWeak_markedExperiments_iff_normalizedMarkedUtility
    F h q' q hq' hq (markedExperimentOfChannel K')
      (markedExperimentOfChannel K)).mp hb
  exact le_antisymm hfv hbv

/-- A bijective record rewrite preserves the marked terminal law and value. -/
theorem normalizedMarkedUtility_recordEquiv
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (e : R ≃ S) (q : Dist A) (hq : q.FullSupport)
    (K : Channel A (O × R)) :
    normalizedMarkedUtility F h q hq
        (markedExperimentOfChannel
          (Relabeling.relabelChannel (Equiv.refl A)
            (Equiv.prodCongr (Equiv.refl O) e) K)) =
      normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) := by
  apply normalizedMarkedUtility_respects_sameMarkedTerminalLaw
  intro phi
  exact markedChannelIntegral_relabelRecord e q K phi

/-- Simultaneously renaming actions and records preserves normalized value. -/
theorem normalizedMarkedUtility_actionRecordEquiv
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (eA : A ≃ B) (eR : R ≃ S) (q : Dist A) (hq : q.FullSupport)
    (K : Channel A (O × R)) :
    normalizedMarkedUtility F h (Relabeling.relabelDist eA q)
        (Relabeling.relabelDist_fullSupport eA q hq)
        (markedExperimentOfChannel
          (Relabeling.relabelChannel eA
            (Equiv.prodCongr (Equiv.refl O) eR) K)) =
      normalizedMarkedUtility F h q hq (markedExperimentOfChannel K) := by
  rw [← Relabeling.relabelChannel_action_then_outcome]
  rw [normalizedMarkedUtility_recordEquiv, normalizedMarkedUtility_actionEquiv]

/-- Uniform priors are unchanged by a permutation of their action alphabet. -/
theorem materialCalibration_relabelDist_uniform (e : A ≃ A) :
    Relabeling.relabelDist e (Dist.uniform (A := A)) = Dist.uniform := by
  ext a
  rfl

end TraceableAgency.Theorem1
