/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence
import TraceableAgency.PureTrace.Support.SupportRestriction
import TraceableAgency.PureTrace.Support.Relabeling
import TraceableAgency.Info.Identities

namespace TraceableAgency

universe u

/-!
## Normalized Value and Entropy Candidate

Helpers for working with the rescaled value functional V̂ = V/a.
-/

/-- Normalized value V̂_q(P) = V_q(P) / a_q.
    Paper notation: V̂_q(μ_{q,P}) or F̂_q(μ_{q,P}). -/
noncomputable def normalizedValue
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) : ℝ :=
  hs.branch_agg.value_rep.V q (experimentOfChannel P) / hs.scale q

/-- Simp lemma for normalized value. -/
@[simp]
theorem normalizedValue_def
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A O : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    normalizedValue hs q P =
      hs.branch_agg.value_rep.V q (experimentOfChannel P) / hs.scale q := rfl

/-- Candidate entropy function H(q) := V̂_q(Id_A).
    Paper definition: H(q) := F̂_q(χ_q) where χ_q is full-revelation.
    Since Id_A : A → Δ(A) induces χ_q as its posterior law, we use Id_A directly. -/
noncomputable def Hcandidate
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  normalizedValue hs q Channel.idChannel

/-- Simp lemma for entropy candidate. -/
@[simp]
theorem Hcandidate_def
    {F : PrefFamily.{u}}
    (hs : ScaleCoherenceStructure F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) :
    Hcandidate hs q =
      hs.branch_agg.value_rep.V q (experimentOfChannel Channel.idChannel) / hs.scale q := rfl

end TraceableAgency
