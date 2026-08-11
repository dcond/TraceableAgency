/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.BranchInsertion
import TraceableAgency.Theorem1.Benchmark

/-!
# Mutual information of branch insertion

The information chain rule makes the numerical weight of an inserted
continuation explicit: its conditional mutual information is multiplied by
the probability of reaching the distinguished branch.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]

theorem mutualInfo_branchInsertionContinuation_target
    (r : TraceableAgency.Dist A) (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O A) :
    mutualInfo r (branchInsertionContinuation target o0 E target) =
      @mutualInfo A (O × E.RecordType) inferInstance
        (@instFintypeProd O E.RecordType inferInstance E.recordFintype)
        r E.K := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  unfold branchInsertionContinuation
  simp only [eq_self, dite_true]
  rw [mutualInfo_relabelOutcome]

theorem mutualInfo_branchInsertionContinuation_of_ne
    (r : TraceableAgency.Dist A) (target : Y) (o0 : O)
    (E : MarkedTerminalExperiment O A) (y : Y) (hy : y ≠ target) :
    mutualInfo r (branchInsertionContinuation target o0 E y) = 0 := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  unfold branchInsertionContinuation
  simp only [dif_neg hy]
  rw [mutualInfo_relabelOutcome,
    mutualInfo_uninformativeAtPayoff]

/-- Exact chain-rule formula for one inserted marked continuation. -/
theorem mutualInfo_branchInsertionExperiment
    (q : TraceableAgency.Dist A) (P : Channel A Y)
    (target : Y) (o0 : O) (E : MarkedTerminalExperiment O A) :
    @mutualInfo A (O × (branchInsertionExperiment P target o0 E).RecordType)
        inferInstance
        (@instFintypeProd O
          (branchInsertionExperiment P target o0 E).RecordType
          inferInstance (branchInsertionExperiment P target o0 E).recordFintype)
        q (branchInsertionExperiment P target o0 E).K =
      mutualInfo q P +
        Channel.outcomeMarginal P q target *
          @mutualInfo A (O × E.RecordType) inferInstance
            (@instFintypeProd O E.RecordType inferInstance E.recordFintype)
            (branchPosterior P q target) E.K := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  change mutualInfo q
      (commonPayoffCompound (branchInsertionRecord target E) P
        (branchInsertionContinuation target o0 E)) = _
  rw [mutualInfo_commonCompound]
  congr 1
  rw [Finset.sum_eq_single target]
  · rw [mutualInfo_branchInsertionContinuation_target]
  · intro y _hy hyt
    rw [mutualInfo_branchInsertionContinuation_of_ne
      (branchPosterior P q y) target o0 E y hyt, mul_zero]
  · simp

end TraceableAgency.Theorem1
