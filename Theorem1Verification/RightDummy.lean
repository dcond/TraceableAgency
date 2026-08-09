/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Theorem1Verification.PairOrder
import Theorem1Verification.SupportDummy

/-!
# Right-coordinate independent dummy lifts

The product block bridge needs both alternatives on the same ordered product
alphabet `A × B`.  `SupportDummy` supplies the left-coordinate lift.  Here the
right alternative ignores `A`; its neutrality is derived by an explicit action
swap and A5 in both directions.
-/

set_option linter.style.header false

namespace TraceTemperedChoiceVerification

open TraceableAgency

universe u

/-- Lift a channel on `B` to `A × B` by ignoring the left coordinate. -/
noncomputable def rightIndependentDummyChannel
    {O A B R : Type u} [Fintype O] [Fintype R]
    (L : Channel B (O × R)) : Channel (A × B) (O × R) :=
  fun ab ↦ L ab.2

/-- Relabelling an ordinary dummy lift by product commutation is the right
dummy lift. -/
theorem relabel_independentDummyChannel_prodComm
    {O A B R : Type u}
    [Fintype O] [Fintype A] [Fintype B] [Fintype R]
    (L : Channel B (O × R)) :
    Relabeling.relabelChannel (Equiv.prodComm B A)
        (Equiv.refl (O × R))
        (independentDummyChannel (B := A) L) =
      rightIndependentDummyChannel (A := A) L := by
  ext ab z
  rfl

/-- Product commutation also swaps the independent product prior. -/
theorem relabel_prodDist_prodComm
    {A B : Type u} [Fintype A] [Fintype B]
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    Relabeling.relabelDist (Equiv.prodComm B A) (prodDist p q) =
      prodDist q p := by
  ext ab
  rcases ab with ⟨a, b⟩
  simp [Relabeling.relabelDist, prodDist_apply_pair, mul_comm]

/-- An action equivalence makes an alternative weakly equivalent to its
relabelled copy, in both orientations. -/
theorem actionRelabel_pairWeak_neutrality
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h5 : A5_ActionDataProcessing F)
    (e : A ≃ B) (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) :
    let K' := Relabeling.relabelChannel e (Equiv.refl (O × R)) K
    let q' := Relabeling.relabelDist e q
    pairWeak F q K q' K' ∧ pairWeak F q' K' q K := by
  dsimp
  let K' := Relabeling.relabelChannel e (Equiv.refl (O × R)) K
  let q' := Relabeling.relabelDist e q
  constructor
  · have hh := h5 K q (Relabeling.actionEquivKernel e) K'
      (actionCompletion_isExact K q (Relabeling.actionEquivKernel e) K'
        (Relabeling.relabelChannel_isBayesPushforwardCompletion e K q))
    simpa [K', q', Relabeling.actionPushforward_equiv] using hh
  · have hh := h5 K' q' (Relabeling.actionEquivKernel e.symm) K
      (actionCompletion_isExact K' q'
        (Relabeling.actionEquivKernel e.symm) K
        (by
          simpa [K', q'] using
            (Relabeling.relabelChannel_symm_isBayesPushforwardCompletion
              e K q)))
    simpa [K', q', Relabeling.actionPushforward_equiv,
      Relabeling.relabelDist_symm] using hh

/-- A right-coordinate dummy lift is weakly equivalent to the original
alternative in both directions. -/
theorem rightIndependentDummy_pairWeak_neutrality
    {O A B R : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (L : Channel B (O × R))
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    pairWeak F p L (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) ∧
      pairWeak F (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) p L := by
  let Lleft := independentDummyChannel (B := A) L
  let pleft := prodDist p q
  let Lright := rightIndependentDummyChannel (A := A) L
  let pright := prodDist q p
  have hleft := independentDummy_pairWeak_neutrality F h L p q
  have hswap := actionRelabel_pairWeak_neutrality F h.a5
    (Equiv.prodComm B A) Lleft pleft
  have hL : Relabeling.relabelChannel (Equiv.prodComm B A)
      (Equiv.refl (O × R)) Lleft = Lright := by
    exact relabel_independentDummyChannel_prodComm L
  have hp : Relabeling.relabelDist (Equiv.prodComm B A) pleft = pright := by
    exact relabel_prodDist_prodComm q p
  rw [hL, hp] at hswap
  exact
    ⟨pairWeak_transitive F h p L pleft Lleft pright Lright
        hleft.1 hswap.1,
      pairWeak_transitive F h pright Lright pleft Lleft p L
        hswap.2 hleft.2⟩

/-- Replacing both compared objects by their left/right lifts to the same
ordered product alphabet preserves the comparison. -/
theorem pairWeak_iff_commonProductLifts
    {O A B R S : Type u}
    [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (q : TraceableAgency.Dist A) (K : Channel A (O × R))
    (p : TraceableAgency.Dist B) (L : Channel B (O × S)) :
    pairWeak F q K p L ↔
      pairWeak F (prodDist q p)
          (independentDummyChannel (B := B) K)
        (prodDist q p)
          (rightIndependentDummyChannel (A := A) L) := by
  have hK := independentDummy_pairWeak_neutrality F h K q p
  have hL := rightIndependentDummy_pairWeak_neutrality F h L q p
  constructor
  · intro hKL
    exact pairWeak_transitive F h (prodDist q p)
      (independentDummyChannel (B := B) K) q K (prodDist q p)
      (rightIndependentDummyChannel (A := A) L)
      hK.2 (pairWeak_transitive F h q K p L (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) hKL hL.1)
  · intro hlift
    exact pairWeak_transitive F h q K (prodDist q p)
      (independentDummyChannel (B := B) K) p L
      hK.1 (pairWeak_transitive F h (prodDist q p)
        (independentDummyChannel (B := B) K) (prodDist q p)
        (rightIndependentDummyChannel (A := A) L) p L hlift hL.2)

/-! ## Numerical information identities for the product bridge -/

theorem outcomeMarginal_independentDummyChannel
    {O A B R : Type u}
    [Fintype O] [Fintype A] [Fintype B] [Fintype R]
    (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    Channel.outcomeMarginal (independentDummyChannel (B := B) K)
        (prodDist q p) = Channel.outcomeMarginal K q := by
  ext z
  simp only [Channel.outcomeMarginal_apply, independentDummyChannel]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∑ b, prodDist q p (a, b) * K a z) =
        q a * K a z * ∑ b, p b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [prodDist_apply_pair]
      ring
    _ = q a * K a z := by rw [p.sum_eq_one, mul_one]

theorem mutualInfo_independentDummyChannel
    {O A B R : Type u}
    [Fintype O] [Fintype A] [Fintype B] [Fintype R]
    (K : Channel A (O × R))
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    mutualInfo (prodDist q p) (independentDummyChannel (B := B) K) =
      mutualInfo q K := by
  unfold mutualInfo
  rw [outcomeMarginal_independentDummyChannel]
  congr 1
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _ha
  calc
    (∑ b, prodDist q p (a, b) * entropy (independentDummyChannel K (a, b))) =
        q a * entropy (K a) * ∑ b, p b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _hb
      simp only [prodDist_apply_pair, independentDummyChannel]
      ring
    _ = q a * entropy (K a) := by rw [p.sum_eq_one, mul_one]

theorem outcomeMarginal_rightIndependentDummyChannel
    {O A B R : Type u}
    [Fintype O] [Fintype A] [Fintype B] [Fintype R]
    (L : Channel B (O × R))
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    Channel.outcomeMarginal (rightIndependentDummyChannel (A := A) L)
        (prodDist q p) = Channel.outcomeMarginal L p := by
  ext z
  simp only [Channel.outcomeMarginal_apply, rightIndependentDummyChannel]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  calc
    (∑ a, prodDist q p (a, b) * L b z) =
        (∑ a, q a) * (p b * L b z) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [prodDist_apply_pair]
      ring
    _ = p b * L b z := by rw [q.sum_eq_one, one_mul]

theorem mutualInfo_rightIndependentDummyChannel
    {O A B R : Type u}
    [Fintype O] [Fintype A] [Fintype B] [Fintype R]
    (L : Channel B (O × R))
    (q : TraceableAgency.Dist A) (p : TraceableAgency.Dist B) :
    mutualInfo (prodDist q p) (rightIndependentDummyChannel (A := A) L) =
      mutualInfo p L := by
  unfold mutualInfo
  rw [outcomeMarginal_rightIndependentDummyChannel]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _hb
  calc
    (∑ a, prodDist q p (a, b) * entropy (rightIndependentDummyChannel L (a, b))) =
        (∑ a, q a) * (p b * entropy (L b)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _ha
      simp only [prodDist_apply_pair, rightIndependentDummyChannel]
      ring
    _ = p b * entropy (L b) := by rw [q.sum_eq_one, one_mul]

end TraceTemperedChoiceVerification
