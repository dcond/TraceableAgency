/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Channel

/-!
# Preference Families

The primitive behavioural datum: for each finite channel P : A → Δ(O),
a weak order ≽_P on Δ(A).

IMPORTANT: The primitive is a preference over lotteries inside a fixed
environment, NOT a preference over pairs (q, P). Cross-environment
comparisons are encoded through block environments.
-/

namespace TraceableAgency

universe u

/-- A family of preference relations, one for each finite channel.

    For each finite channel P : A → Δ(O), the relation `rel P q q'` means
    "lottery q displays at least as much traceability as q' in environment P".

    The relation is defined polymorphically over all finite types A and O. -/
structure PrefFamily where
  rel : ∀ {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O],
        Channel A O → Dist A → Dist A → Prop

namespace PrefFamily

variable (F : PrefFamily.{u})
variable {A O : Type u} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]

/-- Strict preference: q ≻_P q' means q ≽_P q' and not q' ≽_P q -/
def strictRel (P : Channel A O) (q q' : Dist A) : Prop :=
  F.rel P q q' ∧ ¬ F.rel P q' q

/-- Indifference: q ~_P q' means q ≽_P q' and q' ≽_P q -/
def indiffRel (P : Channel A O) (q q' : Dist A) : Prop :=
  F.rel P q q' ∧ F.rel P q' q

/-- A preference relation is complete on Δ(A). -/
def IsComplete (P : Channel A O) : Prop :=
  ∀ q q' : Dist A, F.rel P q q' ∨ F.rel P q' q

/-- A preference relation is transitive on Δ(A). -/
def IsTransitive (P : Channel A O) : Prop :=
  ∀ q q' q'' : Dist A, F.rel P q q' → F.rel P q' q'' → F.rel P q q''

/-- A preference relation is a weak order (complete and transitive). -/
def IsWeakOrder (P : Channel A O) : Prop :=
  F.IsComplete P ∧ F.IsTransitive P

end PrefFamily

end TraceableAgency
