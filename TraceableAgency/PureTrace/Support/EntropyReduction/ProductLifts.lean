/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.EntropyReduction.Compatibility

namespace TraceableAgency

universe u

/-!
**Product lifts for the unscaled cross-prior blockbridge**

Paper Lemma blockbridge first compares `(q, P)` and `(r, Q)` after lifting both
to the product prior `q ⊗ r`, using `P ⊗ U_B` and `U_A ⊗ Q`.  These definitions
name that product-lifted comparison.
-/

/-- Product lift of a left-side channel: `P ⊗ U_B`. -/
noncomputable def leftProductLiftChannel
    {A B O : Type u} [Fintype A] [Fintype B] [Fintype O]
    (P : Channel A O) : Channel (A × B) (O × PUnit.{u + 1}) :=
  prodChannel P (Channel.uninformativeChannelU B)

/-- Product lift of a right-side channel: `U_A ⊗ Q`. -/
noncomputable def rightProductLiftChannel
    {A B Y : Type u} [Fintype A] [Fintype B] [Fintype Y]
    (Q : Channel B Y) : Channel (A × B) (PUnit.{u + 1} × Y) :=
  prodChannel (Channel.uninformativeChannelU A) Q

/-- Same-prior product-lifted block comparison at the product prior `q ⊗ r`. -/
def ProductLiftedComparison
    (F : PrefFamily.{u})
    {A B O Y : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype O] [DecidableEq O]
    [Fintype Y] [DecidableEq Y]
    (q : Dist A) (r : Dist B) (P : Channel A O) (Q : Channel B Y) : Prop :=
  ExperimentPairPref F
    (experimentOfChannel (leftProductLiftChannel (B := B) P))
    (experimentOfChannel (rightProductLiftChannel (A := A) Q))
    (prodDist q r) (prodDist q r)

end TraceableAgency
