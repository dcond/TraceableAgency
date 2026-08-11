/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.PureTrace.Support.ScaleCoherence.UniversalScale

namespace TraceableAgency

universe u

/-!
### Stage 27 product-interaction cleanup

The product-revelation scale link and the final two-grouping collapse are
split below into smaller pieces.  The full-revelation product value identity
and the final cancellation from constant `Z` to `kappa = 0` are internal.  The
remaining external content is the sequential-revelation scale equation and the
paper's weight-constant conclusion from the grouping equation.
-/

/-- Product of two full-revelation channels is the full-revelation channel on
the product action type. -/
theorem prodChannel_idChannel_idChannel_eq_idChannel
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    prodChannel (Channel.idChannel : Channel A A)
        (Channel.idChannel : Channel B B) =
      (Channel.idChannel : Channel (A × B) (A × B)) := by
  funext a
  ext o
  rcases a with ⟨a, b⟩
  rcases o with ⟨a', b'⟩
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      simp [prodChannel, Channel.idChannel]
    · simp [prodChannel, Channel.idChannel, Dist.pure_apply, hb]
  · simp [prodChannel, Channel.idChannel, Dist.pure_apply, ha]

/-- Reveal the first coordinate of a product action. -/
noncomputable def productFirstRevealChannel
    {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] :
    Channel (A × B) A :=
  fun ab => Dist.pure ab.1

/-- Reveal the second coordinate of a product action. -/
noncomputable def productSecondRevealChannel
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B] :
    Channel (A × B) B :=
  fun ab => Dist.pure ab.2

/-- Full revelation of a product action with swapped outcome labels. -/
noncomputable def productSwapRevealChannel
    {A B : Type u} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    Channel (A × B) (B × A) :=
  fun ab => Dist.pure (ab.2, ab.1)

/-- Revealing the first coordinate and then the second coordinate is exactly
full revelation of the product action. -/
theorem productFirstThenSecondReveal_eq_idChannel
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    (productFirstRevealChannel (A := A) (B := B) ▷
        (fun _ => productSecondRevealChannel (A := A) (B := B))) =
      (Channel.idChannel : Channel (A × B) (A × B)) := by
  funext ab
  ext o
  rcases ab with ⟨a, b⟩
  rcases o with ⟨a', b'⟩
  by_cases ha : a' = a
  · subst ha
    by_cases hb : b' = b
    · subst hb
      simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, Channel.idChannel]
    · simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, Channel.idChannel, hb]
  · simp [seqCompose_apply, productFirstRevealChannel,
      productSecondRevealChannel, Channel.idChannel, Dist.pure_apply, ha]

/-- Revealing the second coordinate and then the first coordinate is full
revelation with the two outcome coordinates swapped. -/
theorem productSecondThenFirstReveal_eq_swapReveal
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B] :
    (productSecondRevealChannel (A := A) (B := B) ▷
        (fun _ => productFirstRevealChannel (A := A) (B := B))) =
      productSwapRevealChannel (A := A) (B := B) := by
  funext ab
  ext o
  rcases ab with ⟨a, b⟩
  rcases o with ⟨b', a'⟩
  by_cases hb : b' = b
  · subst hb
    by_cases ha : a' = a
    · subst ha
      simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, productSwapRevealChannel]
    · simp [seqCompose_apply, productFirstRevealChannel,
        productSecondRevealChannel, productSwapRevealChannel,
        ha]
  · simp [seqCompose_apply, productFirstRevealChannel,
      productSecondRevealChannel, productSwapRevealChannel,
      Dist.pure_apply, hb]

/-- Positive posterior under the identity channel is the revealed pure action. -/
theorem posterior_idChannel_eq_pure_of_pos
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (a : A) (ha : 0 < q a) :
    Channel.posterior (Channel.idChannel : Channel A A) q a =
      Dist.pure a := by
  ext b
  have hm : (Channel.outcomeMarginal (Channel.idChannel : Channel A A) q) a = q a := by
    rw [outcomeMarginal_idChannel']
  unfold Channel.posterior
  rw [dif_pos (by rw [hm]; exact ha)]
  by_cases h : b = a
  · subst h
    simp only [Channel.idChannel, Dist.pure_apply_self, mul_one]
    rw [hm]
    field_simp [ne_of_gt ha]
  · have hsym : a ≠ b := fun h' => h h'.symm
    simp [Channel.idChannel, Dist.pure_apply_ne _ _ h,
      Dist.pure_apply_ne _ _ hsym]

/-- The swapped full-revelation marginal under a product prior is the swapped
product prior. -/
theorem outcomeMarginal_productSwapRevealChannel_prodDist
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B)) (prodDist q r) =
      prodDist r q := by
  ext ba
  rcases ba with ⟨b, a⟩
  calc
    Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B)) (prodDist q r) (b, a)
        =
      q a * r b := by
        rw [Channel.outcomeMarginal_apply]
        rw [Fintype.sum_eq_single (a, b)]
        · simp [productSwapRevealChannel, prodDist_apply_pair]
        · intro ab hab
          rcases ab with ⟨a', b'⟩
          have hpair : (b, a) ≠ (b', a') := by
            intro hba
            apply hab
            exact Prod.ext (Prod.ext_iff.mp hba |>.2.symm)
              (Prod.ext_iff.mp hba |>.1.symm)
          simp [productSwapRevealChannel, prodDist_apply_pair,
            Dist.pure_apply_ne _ _ hpair]
    _ = prodDist r q (b, a) := by
        rw [prodDist_apply_pair]
        ring

/-- Positive posterior under swapped product full revelation is the pure
product action with coordinates unswapped. -/
theorem posterior_productSwapRevealChannel_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) (b : B)
    (ha : 0 < q a) (hb : 0 < r b) :
    Channel.posterior
        (productSwapRevealChannel (A := A) (B := B))
        (prodDist q r) (b, a) =
      Dist.pure (a, b) := by
  ext ab
  rcases ab with ⟨a', b'⟩
  have hm :
      (Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B))
        (prodDist q r)) (b, a) = q a * r b := by
    rw [outcomeMarginal_productSwapRevealChannel_prodDist]
    rw [prodDist_apply_pair]
    ring
  have hmpos :
      (Channel.outcomeMarginal
        (productSwapRevealChannel (A := A) (B := B))
        (prodDist q r)) (b, a) > 0 := by
    rw [hm]
    exact mul_pos ha hb
  unfold Channel.posterior
  rw [dif_pos hmpos]
  by_cases h : a' = a ∧ b' = b
  · rcases h with ⟨ha', hb'⟩
    subst ha'
    subst hb'
    simp only [prodDist_apply_pair, productSwapRevealChannel,
      Dist.pure_apply_self, mul_one]
    rw [hm]
    field_simp [ne_of_gt (mul_pos ha hb)]
  · have hswap : (b, a) ≠ (b', a') := by
      intro hba
      apply h
      exact ⟨Prod.ext_iff.mp hba |>.2.symm,
        Prod.ext_iff.mp hba |>.1.symm⟩
    have hpure : (a', b') ≠ (a, b) := by
      intro hp
      apply h
      exact ⟨Prod.ext_iff.mp hp |>.1, Prod.ext_iff.mp hp |>.2⟩
    simp [productSwapRevealChannel, prodDist_apply_pair, hswap,
      Dist.pure_apply_ne _ _ hpure]

/-- Swapped product full revelation and ordinary product full revelation induce
the same posterior law under a full-support product prior. -/
theorem samePosteriorLawExp_productSwapReveal_idChannel_of_fullSupport
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel (productSwapRevealChannel (A := A) (B := B)))
      (experimentOfChannel (Channel.idChannel : Channel (A × B) (A × B))) := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  rw [outcomeMarginal_productSwapRevealChannel_prodDist,
    outcomeMarginal_idChannel']
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  calc
    ∑ b : B, ∑ a : A,
        (r b * q a) *
          φ (Channel.posterior
            (productSwapRevealChannel (A := A) (B := B))
            (prodDist q r) (b, a))
        =
      ∑ b : B, ∑ a : A,
        (q a * r b) * φ (Dist.pure (a, b)) := by
          apply Finset.sum_congr rfl
          intro b _
          apply Finset.sum_congr rfl
          intro a _
          rw [posterior_productSwapRevealChannel_prodDist_of_pos
            q r a b (hq a) (hr b)]
          ring_nf
    _ =
      ∑ a : A, ∑ b : B,
        (q a * r b) * φ (Dist.pure (a, b)) := by
          rw [Finset.sum_comm]
    _ =
      ∑ a : A, ∑ b : B,
        (q a * r b) *
          φ (Channel.posterior
            (Channel.idChannel : Channel (A × B) (A × B))
            (prodDist q r) (a, b)) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro b _
          have hp : 0 < prodDist q r (a, b) := by
            exact mul_pos (hq a) (hr b)
          rw [posterior_idChannel_eq_pure_of_pos (prodDist q r) (a, b) hp]

/-- The marginal of the first-coordinate reveal under a product prior is the
first prior. -/
theorem outcomeMarginal_productFirstRevealChannel_prodDist
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    Channel.outcomeMarginal
        (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) =
      q := by
  ext a
  rw [Channel.outcomeMarginal_apply]
  simp only [productFirstRevealChannel, prodDist_apply_pair,
    Fintype.sum_prod_type]
  calc
    ∑ x : A, ∑ y : B, q x * r y * (Dist.pure x) a
        = ∑ x : A, q x * (Dist.pure x) a * ∑ y : B, r y := by
          apply Finset.sum_congr rfl
          intro x _
          calc
            ∑ y : B, q x * r y * (Dist.pure x) a
                = ∑ y : B, (q x * (Dist.pure x) a) * r y := by
                  apply Finset.sum_congr rfl
                  intro y _
                  ring
            _ = q x * (Dist.pure x) a * ∑ y : B, r y := by
                  rw [Finset.mul_sum]
    _ = ∑ x : A, q x * (Dist.pure x) a := by
          rw [r.sum_eq_one]
          simp
    _ = q a := by
          simp [Dist.pure_apply]

/-- The marginal of the second-coordinate reveal under a product prior is the
second prior. -/
theorem outcomeMarginal_productSecondRevealChannel_prodDist
    {A B : Type u}
    [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    Channel.outcomeMarginal
        (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) =
      r := by
  ext b
  rw [Channel.outcomeMarginal_apply]
  simp only [productSecondRevealChannel, prodDist_apply_pair,
    Fintype.sum_prod_type]
  calc
    ∑ x : A, ∑ y : B, q x * r y * (Dist.pure y) b
        = ∑ y : B, (∑ x : A, q x) * r y * (Dist.pure y) b := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro y _
          calc
            ∑ x : A, q x * r y * (Dist.pure y) b
                = ∑ x : A, q x * (r y * (Dist.pure y) b) := by
                  apply Finset.sum_congr rfl
                  intro x _
                  ring
            _ = (∑ x : A, q x) * (r y * (Dist.pure y) b) := by
                  rw [Finset.sum_mul]
            _ = (∑ x : A, q x) * r y * (Dist.pure y) b := by
                  ring
    _ = ∑ y : B, r y * (Dist.pure y) b := by
          rw [q.sum_eq_one]
          simp
    _ = r b := by
          simp [Dist.pure_apply]

/-- Posterior after revealing the first coordinate of a product prior. -/
theorem posterior_productFirstRevealChannel_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) (ha : 0 < q a) :
    Channel.posterior
        (productFirstRevealChannel (A := A) (B := B)) (prodDist q r) a =
      prodDist (Dist.pure a) r := by
  ext ab
  rcases ab with ⟨a', b⟩
  have hmarg_pos :
      (Channel.outcomeMarginal
        (productFirstRevealChannel (A := A) (B := B)) (prodDist q r)) a > 0 := by
    simpa [outcomeMarginal_productFirstRevealChannel_prodDist] using ha
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : a' = a
  · subst h
    simp [productFirstRevealChannel, prodDist_apply_pair,
      outcomeMarginal_productFirstRevealChannel_prodDist, ne_of_gt ha]
  · have hsym : a ≠ a' := fun h' => h h'.symm
    simp [productFirstRevealChannel, prodDist_apply_pair,
      Dist.pure_apply_ne _ _ h, Dist.pure_apply_ne _ _ hsym,
      outcomeMarginal_productFirstRevealChannel_prodDist]

/-- Posterior after revealing the second coordinate of a product prior. -/
theorem posterior_productSecondRevealChannel_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (b : B) (hb : 0 < r b) :
    Channel.posterior
        (productSecondRevealChannel (A := A) (B := B)) (prodDist q r) b =
      prodDist q (Dist.pure b) := by
  ext ab
  rcases ab with ⟨a, b'⟩
  have hmarg_pos :
      (Channel.outcomeMarginal
        (productSecondRevealChannel (A := A) (B := B)) (prodDist q r)) b > 0 := by
    simpa [outcomeMarginal_productSecondRevealChannel_prodDist] using hb
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : b' = b
  · subst h
    simp [productSecondRevealChannel, prodDist_apply_pair,
      outcomeMarginal_productSecondRevealChannel_prodDist, ne_of_gt hb]
  · have hsym : b ≠ b' := fun h' => h h'.symm
    simp [productSecondRevealChannel, prodDist_apply_pair,
      Dist.pure_apply_ne _ _ h, Dist.pure_apply_ne _ _ hsym,
      outcomeMarginal_productSecondRevealChannel_prodDist]

/-- Product of first-coordinate full revelation with no information on the
second coordinate has first marginal `q`. -/
theorem outcomeMarginal_prod_id_uninformativeChannelU_prodDist
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) :
    Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r) (a, PUnit.unit) = q a := by
  have h := congrArg (fun d : Dist (A × PUnit.{u+1}) => d (a, PUnit.unit))
    (outcomeMarginal_prod q r
      (Channel.idChannel : Channel A A)
      (Channel.uninformativeChannelU B))
  calc
    Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r) (a, PUnit.unit)
        =
      (Channel.outcomeMarginal (Channel.idChannel : Channel A A) q) a *
        (Channel.outcomeMarginal (Channel.uninformativeChannelU B) r) PUnit.unit := by
          simpa [prodDist_apply_pair] using h
    _ = q a * 1 := by
          rw [outcomeMarginal_idChannel']
          have hU :
              (Channel.outcomeMarginal (Channel.uninformativeChannelU B) r)
                  PUnit.unit = 1 := by
            simp [Channel.outcomeMarginal, Channel.uninformativeChannelU,
              r.sum_eq_one]
          rw [hU]
    _ = q a := by ring

/-- Product of no information on the first coordinate with second-coordinate
full revelation has second marginal `r`. -/
theorem outcomeMarginal_prod_uninformativeChannelU_id_prodDist
    {A B : Type u}
    [Fintype A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (b : B) :
    Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r) (PUnit.unit, b) = r b := by
  have h := congrArg (fun d : Dist (PUnit.{u+1} × B) => d (PUnit.unit, b))
    (outcomeMarginal_prod q r
      (Channel.uninformativeChannelU A)
      (Channel.idChannel : Channel B B))
  calc
    Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r) (PUnit.unit, b)
        =
      (Channel.outcomeMarginal (Channel.uninformativeChannelU A) q) PUnit.unit *
        (Channel.outcomeMarginal (Channel.idChannel : Channel B B) r) b := by
          simpa [prodDist_apply_pair] using h
    _ = 1 * r b := by
          rw [outcomeMarginal_idChannel']
          have hU :
              (Channel.outcomeMarginal (Channel.uninformativeChannelU A) q)
                  PUnit.unit = 1 := by
            simp [Channel.outcomeMarginal, Channel.uninformativeChannelU,
              q.sum_eq_one]
          rw [hU]
    _ = r b := by ring

/-- Posterior for first-coordinate full revelation with no information on the
second coordinate. -/
theorem posterior_prod_id_uninformativeChannelU_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (a : A) (ha : 0 < q a) :
    Channel.posterior
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r) (a, PUnit.unit) =
      prodDist (Dist.pure a) r := by
  ext ab
  rcases ab with ⟨a', b⟩
  have hmarg_eq :
      (Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r)) (a, PUnit.unit) = q a :=
    outcomeMarginal_prod_id_uninformativeChannelU_prodDist q r a
  have hmarg_pos :
      (Channel.outcomeMarginal
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))
        (prodDist q r)) (a, PUnit.unit) > 0 := by
    rw [hmarg_eq]
    exact ha
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : a' = a
  · subst a'
    simp only [prodDist_apply_pair, prodChannel_apply_pair, Channel.idChannel,
      Channel.uninformativeChannelU, Dist.pure_apply_self, mul_one, one_mul]
    change q a * r b /
        (Channel.outcomeMarginal
          (prodChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU B))
          (prodDist q r)) (a, PUnit.unit) = r b
    rw [hmarg_eq]
    field_simp [ne_of_gt ha]
  · have hsym : a ≠ a' := fun h' => h h'.symm
    simp [prodChannel_apply_pair, Channel.idChannel, Channel.uninformativeChannelU,
      prodDist_apply_pair, Dist.pure_apply_ne _ _ h,
      Dist.pure_apply_ne _ _ hsym]

/-- Posterior for no information on the first coordinate with second-coordinate
full revelation. -/
theorem posterior_prod_uninformativeChannelU_id_prodDist_of_pos
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (b : B) (hb : 0 < r b) :
    Channel.posterior
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r) (PUnit.unit, b) =
      prodDist q (Dist.pure b) := by
  ext ab
  rcases ab with ⟨a, b'⟩
  have hmarg_eq :
      (Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r)) (PUnit.unit, b) = r b :=
    outcomeMarginal_prod_uninformativeChannelU_id_prodDist q r b
  have hmarg_pos :
      (Channel.outcomeMarginal
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))
        (prodDist q r)) (PUnit.unit, b) > 0 := by
    rw [hmarg_eq]
    exact hb
  unfold Channel.posterior
  rw [dif_pos hmarg_pos]
  by_cases h : b' = b
  · subst b'
    simp only [prodDist_apply_pair, prodChannel_apply_pair, Channel.idChannel,
      Channel.uninformativeChannelU, Dist.pure_apply_self, mul_one]
    change q a * r b /
        (Channel.outcomeMarginal
          (prodChannel (Channel.uninformativeChannelU A)
            (Channel.idChannel : Channel B B))
          (prodDist q r)) (PUnit.unit, b) = q a
    rw [hmarg_eq]
    field_simp [ne_of_gt hb]
  · have hsym : b ≠ b' := fun h' => h h'.symm
    simp [prodChannel_apply_pair, Channel.idChannel, Channel.uninformativeChannelU,
      prodDist_apply_pair, Dist.pure_apply_ne _ _ h,
      Dist.pure_apply_ne _ _ hsym]

/-- Revealing the first coordinate has the same posterior law as full
revelation of the first coordinate together with no information on the second. -/
theorem samePosteriorLawExp_productFirstReveal_prod_id_uninformativeU
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel
        (productFirstRevealChannel (A := A) (B := B)))
      (experimentOfChannel
        (prodChannel (Channel.idChannel : Channel A A)
          (Channel.uninformativeChannelU B))) := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro a _
  rw [outcomeMarginal_productFirstRevealChannel_prodDist,
    outcomeMarginal_prod_id_uninformativeChannelU_prodDist]
  by_cases ha : 0 < q a
  · rw [posterior_productFirstRevealChannel_prodDist_of_pos q r a ha,
      posterior_prod_id_uninformativeChannelU_prodDist_of_pos q r a ha]
  · have hzero : q a = 0 := le_antisymm (le_of_not_gt ha) (q.nonneg a)
    simp [hzero]

/-- Revealing the second coordinate has the same posterior law as no
information on the first coordinate together with full revelation of the second. -/
theorem samePosteriorLawExp_productSecondReveal_prod_uninformativeU_id
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) :
    SamePosteriorLawExp (prodDist q r)
      (experimentOfChannel
        (productSecondRevealChannel (A := A) (B := B)))
      (experimentOfChannel
        (prodChannel (Channel.uninformativeChannelU A)
          (Channel.idChannel : Channel B B))) := by
  intro φ _hcont
  rw [posteriorLawIntegralExp_experimentOfChannel,
    posteriorLawIntegralExp_experimentOfChannel]
  unfold posteriorLawIntegral
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  apply Finset.sum_congr rfl
  intro b _
  rw [outcomeMarginal_productSecondRevealChannel_prodDist,
    outcomeMarginal_prod_uninformativeChannelU_id_prodDist]
  by_cases hb : 0 < r b
  · rw [posterior_productSecondRevealChannel_prodDist_of_pos q r b hb,
      posterior_prod_uninformativeChannelU_id_prodDist_of_pos q r b hb]
  · have hzero : r b = 0 := le_antisymm (le_of_not_gt hb) (r.nonneg b)
    simp [hzero]

/-- A1 gives nonzero full-revelation value for a full-support non-singleton
prior in the faithful face-scale representative. -/
theorem fullRevelationValueForFaceScales_ne_zero_of_A1
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) (hq : q.FullSupport) (hA : ¬ Subsingleton A) :
    fullRevelationValueForFaceScales hfaces q ≠ 0 := by
  have hstrict :=
    branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
  have hne :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.idChannel : Channel A A)) ≠
        hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) :=
    branch_value_ne_of_strict_experiment_pref
      F hfaces.branch_result.branch_agg.value_rep q hq
      (experimentOfChannel (Channel.idChannel : Channel A A))
      (experimentOfChannel (Channel.uninformativeChannelU A))
      hstrict.1 hstrict.2
  have hzero :
      hfaces.branch_result.branch_agg.value_rep.V q
          (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
    hfaces.branch_result.branch_agg.value_rep.zero_normalized q hq
  intro hH
  exact hne (by
    unfold fullRevelationValueForFaceScales at hH
    rw [hH, hzero])

/-- Base-value nonconstancy for the face-scale product-slice affine
decomposition is internal from A1 and zero-normalisation. -/
theorem faceScaleBaseValueNonconstancy_of_A1
    {F : PrefFamily.{u}} (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteFaceScaleBaseValueNonconstancyAssumptionsFor hfaces where
  base_value_nonconstant := by
    intro hax A _ _ _ q hq hA
    have hstrict :=
      branch_id_uninformativeU_experiment_strict_of_A1 F hax q hq hA
    exact
      branch_value_ne_of_strict_experiment_pref
        F hfaces.branch_result.branch_agg.value_rep q hq
        (experimentOfChannel (Channel.idChannel : Channel A A))
        (experimentOfChannel (Channel.uninformativeChannelU A))
        hstrict.1 hstrict.2

/-- Product quasi-additivity internally gives the full-revelation value
identity `H(q ⊗ r) = H(q) + H(r) + kappa H(q)H(r)`. -/
theorem fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    fullRevelationValueForFaceScales hfaces (prodDist q r) =
      fullRevelationValueForFaceScales hfaces q +
      fullRevelationValueForFaceScales hfaces r +
      hprod.kappa hax *
        fullRevelationValueForFaceScales hfaces q *
        fullRevelationValueForFaceScales hfaces r := by
  have hqa :=
    hprod.product_quasi_add hax q r hq hr
      (Channel.idChannel : Channel A A)
      (Channel.idChannel : Channel B B)
  simpa [fullRevelationValueForFaceScales,
    prodChannel_idChannel_idChannel_eq_idChannel] using hqa

/-- Sharper product-revelation bridge: sequential full revelation gives the
scale-weighted value equation.  Product quasi-additivity supplies the other
side of the comparison internally. -/
structure FiniteProductRevelationSequentialScaleAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  sequential_reveal_left :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale r *
          (fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces q) =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces r
  sequential_reveal_right :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.scale_factorization.scale q *
          (fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces r) =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces q

/-- Source-ready normalized-chain form of the sequential full-revelation
calculation in Step 1 of `Interaction collapse and universal chain scale`.

This is narrower than `FiniteProductRevelationSequentialScaleAssumptionsFor`:
it asserts exactly the normalized chain-rule specialization before clearing
denominators.  The remaining content is the channel/face transport identifying
the first-stage coordinate reveal and every continuation reveal with the
corresponding full-revelation values. -/
structure FiniteSequentialFullRevelationNormalizedChainAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  normalized_chain_left :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r
  normalized_chain_right :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r) =
        fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q

/-- Coordinate-reveal value transport for the sequential full-revelation
calculation.

This isolates the value/relabeling part of Step 1: revealing only one
coordinate of a product prior has the same representative value as full
revelation of that coordinate, and swapped full revelation has the same value
as ordinary full revelation of the product. -/
structure FiniteCoordinateRevealValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productFirstRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces q
  second_reveal_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productSecondRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces r
  swap_full_revelation_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
          (productSwapRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces (prodDist q r)

/-- The first two coordinate-reveal value identities, separated from the
swapped full-revelation outcome-relabeling identity.

This is narrower than `FiniteCoordinateRevealValueTransportAssumptionsFor`:
the remaining content is exactly the product/no-information value transport for
revealing one coordinate of a product prior. -/
structure FiniteCoordinateRevealMarginalValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productFirstRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces q
  second_reveal_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productSecondRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces r

/-- Swapped product full revelation has the same value as ordinary product
full revelation.

This isolates the outcome-relabeling part of coordinate value transport. -/
structure FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  swap_full_revelation_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      hfaces.branch_result.branch_agg.value_rep.V (prodDist q r)
          (experimentOfChannel
            (productSwapRevealChannel (A := A) (B := B))) =
        fullRevelationValueForFaceScales hfaces (prodDist q r)

/-- Swapped product full revelation has the same value as ordinary product full
revelation because it induces the same posterior law under a full-support
product prior. -/
theorem coordinateSwapFullRevelationValueTransport_of_posteriorLaw
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) :
    FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces where
  swap_full_revelation_value := by
    intro _hax A B _ _ _ _ _ _ q r hq hr _hA _hB
    let hV := hfaces.branch_result.branch_agg.value_rep
    have hsame :=
      samePosteriorLawExp_productSwapReveal_idChannel_of_fullSupport
        q r hq hr
    have hval :
        hV.V (prodDist q r)
            (experimentOfChannel
              (productSwapRevealChannel (A := A) (B := B))) =
          hV.V (prodDist q r)
            (experimentOfChannel
              (Channel.idChannel : Channel (A × B) (A × B))) :=
      hV.respects_same_posterior_law (prodDist q r)
        (experimentOfChannel
          (productSwapRevealChannel (A := A) (B := B)))
        (experimentOfChannel
          (Channel.idChannel : Channel (A × B) (A × B)))
        hsame
    exact hval

/-- Reassemble the Stage 29 coordinate value-transport package from its two
sharper pieces. -/
theorem coordinateRevealValueTransport_of_marginal_and_swap
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hmarg :
      FiniteCoordinateRevealMarginalValueTransportAssumptionsFor hfaces)
    (hswap :
      FiniteCoordinateSwapFullRevelationValueTransportAssumptionsFor hfaces) :
    FiniteCoordinateRevealValueTransportAssumptionsFor hfaces where
  first_reveal_value := hmarg.first_reveal_value
  second_reveal_value := hmarg.second_reveal_value
  swap_full_revelation_value := hswap.swap_full_revelation_value

/-- Product quasi-additivity, together with zero normalization for the
uninformative channel and posterior-law transport, proves the marginal
coordinate-reveal value identities.  Thus the Stage 30 marginal-value transport
residual is not an independent product bridge. -/
theorem coordinateRevealMarginalValueTransport_of_productQuasiAdditivity
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) :
    FiniteCoordinateRevealMarginalValueTransportAssumptionsFor hfaces where
  first_reveal_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr _hA _hB
    let hV := hfaces.branch_result.branch_agg.value_rep
    have hsameVal :
        hV.V (prodDist q r)
            (experimentOfChannel
              (productFirstRevealChannel (A := A) (B := B))) =
          hV.V (prodDist q r)
            (experimentOfChannel
              (prodChannel (Channel.idChannel : Channel A A)
                (Channel.uninformativeChannelU B))) :=
      hV.respects_same_posterior_law (prodDist q r)
        (experimentOfChannel
          (productFirstRevealChannel (A := A) (B := B)))
        (experimentOfChannel
          (prodChannel (Channel.idChannel : Channel A A)
            (Channel.uninformativeChannelU B)))
        (samePosteriorLawExp_productFirstReveal_prod_id_uninformativeU q r)
    have hqa :=
      hprod.product_quasi_add hax q r hq hr
        (Channel.idChannel : Channel A A)
        (Channel.uninformativeChannelU B)
    have hzero :
        hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) = 0 :=
      hV.zero_normalized r hr
    calc
      hV.V (prodDist q r)
          (experimentOfChannel
            (productFirstRevealChannel (A := A) (B := B)))
          =
        hV.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.idChannel : Channel A A)
              (Channel.uninformativeChannelU B))) := hsameVal
      _ =
        hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) +
          hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) +
          hprod.kappa hax *
            hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) *
            hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) := hqa
      _ = fullRevelationValueForFaceScales hfaces q := by
        change
          hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) +
              hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) +
            hprod.kappa hax *
              hV.V q (experimentOfChannel (Channel.idChannel : Channel A A)) *
              hV.V r (experimentOfChannel (Channel.uninformativeChannelU B)) =
            hV.V q (experimentOfChannel (Channel.idChannel : Channel A A))
        rw [hzero]
        ring
  second_reveal_value := by
    intro hax A B _ _ _ _ _ _ q r hq hr _hA _hB
    let hV := hfaces.branch_result.branch_agg.value_rep
    have hsameVal :
        hV.V (prodDist q r)
            (experimentOfChannel
              (productSecondRevealChannel (A := A) (B := B))) =
          hV.V (prodDist q r)
            (experimentOfChannel
              (prodChannel (Channel.uninformativeChannelU A)
                (Channel.idChannel : Channel B B))) :=
      hV.respects_same_posterior_law (prodDist q r)
        (experimentOfChannel
          (productSecondRevealChannel (A := A) (B := B)))
        (experimentOfChannel
          (prodChannel (Channel.uninformativeChannelU A)
            (Channel.idChannel : Channel B B)))
        (samePosteriorLawExp_productSecondReveal_prod_uninformativeU_id q r)
    have hqa :=
      hprod.product_quasi_add hax q r hq hr
        (Channel.uninformativeChannelU A)
        (Channel.idChannel : Channel B B)
    have hzero :
        hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) = 0 :=
      hV.zero_normalized q hq
    calc
      hV.V (prodDist q r)
          (experimentOfChannel
            (productSecondRevealChannel (A := A) (B := B)))
          =
        hV.V (prodDist q r)
          (experimentOfChannel
            (prodChannel (Channel.uninformativeChannelU A)
              (Channel.idChannel : Channel B B))) := hsameVal
      _ =
        hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) +
          hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) +
          hprod.kappa hax *
            hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) *
            hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) := hqa
      _ = fullRevelationValueForFaceScales hfaces r := by
        change
          hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) +
              hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) +
            hprod.kappa hax *
              hV.V q (experimentOfChannel (Channel.uninformativeChannelU A)) *
              hV.V r (experimentOfChannel (Channel.idChannel : Channel B B)) =
            hV.V r (experimentOfChannel (Channel.idChannel : Channel B B))
        rw [hzero]
        ring

/-- Continuation transport for the sequential full-revelation calculation.

After revealing one coordinate, every continuation branch lives on a coordinate
face such as `{a} × B`.  This interface isolates the support-face/relabeling
and scale transport needed to identify the weighted normalized continuation
sum with the full-revelation value of the other coordinate. -/
structure FiniteCoordinateRevealContinuationTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_continuation_sum :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      ∑ a : A,
          (Channel.outcomeMarginal
            (productFirstRevealChannel (A := A) (B := B))
            (prodDist q r)) a *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r) a)
            (productSecondRevealChannel (A := A) (B := B))
        =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r
  second_reveal_continuation_sum :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B),
      ∑ b : B,
          (Channel.outcomeMarginal
            (productSecondRevealChannel (A := A) (B := B))
            (prodDist q r)) b *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r) b)
            (productFirstRevealChannel (A := A) (B := B))
        =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q

/-- Pointwise coordinate-face continuation transport.

This is narrower than the weighted-sum package: it asks for the normalized
continuation value on each coordinate face.  The weighted identities then
follow by the internally proved coordinate-reveal marginal identities and the
fact that the marginals sum to one. -/
structure FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_reveal_branch :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      branchNormalizedValue hfaces.chain
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (productSecondRevealChannel (A := A) (B := B))
      =
      fullRevelationValueForFaceScales hfaces r /
        hfaces.branch_result.scale_factorization.scale r
  second_reveal_branch :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      branchNormalizedValue hfaces.chain
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (productFirstRevealChannel (A := A) (B := B))
      =
      fullRevelationValueForFaceScales hfaces q /
        hfaces.branch_result.scale_factorization.scale q

/-- Coordinate support-face value transport.

After one coordinate of a product prior is revealed, the continuation problem
lives on the coordinate face `{a} × B` or `A × {b}`.  This interface isolates
the cardinal representative choice identifying that ambient boundary-face
continuation value with the intrinsic full-revelation value on the unrevealed
coordinate. -/
structure FiniteCoordinateSupportFaceValueTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (experimentOfChannel
          (productSecondRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces r
  second_coordinate_face_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (experimentOfChannel
          (productFirstRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces q

/-- Coordinate support-face scale transport.

This is the scale counterpart of
`FiniteCoordinateSupportFaceValueTransportAssumptionsFor`: it identifies the
chain scale selected on the ambient coordinate face with the intrinsic scale on
the unrevealed coordinate. -/
structure FiniteCoordinateSupportFaceScaleTransportAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_scale :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a) =
      hfaces.branch_result.scale_factorization.scale r
  second_coordinate_face_scale :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b) =
      hfaces.branch_result.scale_factorization.scale q

/-- Coordinate continuation value read on the support face of the boundary
posterior.

This is the support-read version of
`FiniteCoordinateSupportFaceValueTransportAssumptionsFor`.  After revealing one
coordinate of a full-support product prior, the posterior is a boundary prior
on the ambient product type.  The paper reads the continuation on its positive
support face before identifying that face with the unrevealed coordinate. -/
structure FiniteCoordinateSupportFaceValueSupportReadFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_value_support :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productSecondRevealChannel (A := A) (B := B))
            (Channel.posterior
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r) a))) =
      fullRevelationValueForFaceScales hfaces r
  second_coordinate_face_value_support :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b).restrictToSupport
        (experimentOfChannel
          (Channel.restrictToSupport
            (productFirstRevealChannel (A := A) (B := B))
            (Channel.posterior
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r) b))) =
      fullRevelationValueForFaceScales hfaces q

/-- Coordinate continuation scale read on the support face of the boundary
posterior.  This is the support-read counterpart of
`FiniteCoordinateSupportFaceScaleTransportAssumptionsFor`. -/
structure FiniteCoordinateSupportFaceScaleSupportReadFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_scale_support :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a).restrictToSupport =
      hfaces.branch_result.scale_factorization.scale r
  second_coordinate_face_scale_support :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b).restrictToSupport =
      hfaces.branch_result.scale_factorization.scale q

/-- Coordinate support-face value normalization.

This names the representative choice identifying the ambient product boundary
face after a coordinate reveal with the intrinsic unrevealed coordinate
problem. -/
structure FiniteCoordinateSupportFaceValueIdentificationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a)
        (experimentOfChannel
          (productSecondRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces r
  second_coordinate_face_value :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.branch_agg.value_rep.V
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b)
        (experimentOfChannel
          (productFirstRevealChannel (A := A) (B := B))) =
      fullRevelationValueForFaceScales hfaces q

/-- Coordinate support-face scale normalization. -/
structure FiniteCoordinateSupportFaceScaleIdentificationFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F) : Prop where
  first_coordinate_face_scale :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (a : A),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productFirstRevealChannel (A := A) (B := B))
          (prodDist q r) a) =
      hfaces.branch_result.scale_factorization.scale r
  second_coordinate_face_scale :
    ∀ (_hax : PureTraceConditions F)
      {A B : Type v}
      [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype B] [DecidableEq B] [Nonempty B]
      (q : Dist A) (r : Dist B) (_hq : q.FullSupport) (_hr : r.FullSupport)
      (_hA : ¬ Subsingleton A) (_hB : ¬ Subsingleton B)
      (b : B),
      hfaces.branch_result.scale_factorization.scale
        (Channel.posterior
          (productSecondRevealChannel (A := A) (B := B))
          (prodDist q r) b) =
      hfaces.branch_result.scale_factorization.scale q

/-- Reconstruct value transport from the explicit coordinate support-face
representative normalization. -/
theorem coordinateSupportFaceValueTransport_of_identification
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hident : FiniteCoordinateSupportFaceValueIdentificationFor hfaces) :
    FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces where
  first_coordinate_face_value :=
    hident.first_coordinate_face_value
  second_coordinate_face_value :=
    hident.second_coordinate_face_value

/-- Reconstruct scale transport from the explicit coordinate support-face
scale normalization. -/
theorem coordinateSupportFaceScaleTransport_of_identification
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hident : FiniteCoordinateSupportFaceScaleIdentificationFor hfaces) :
    FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces where
  first_coordinate_face_scale :=
    hident.first_coordinate_face_scale
  second_coordinate_face_scale :=
    hident.second_coordinate_face_scale

/-- Reconstruct pointwise coordinate-branch continuation transport from the
two exact coordinate support-face transports: value representatives and chain
scales. -/
theorem coordinateRevealBranchContinuationTransport_of_coordinateSupportFaceTransports
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hvalue :
      FiniteCoordinateSupportFaceValueTransportAssumptionsFor hfaces)
    (hscale :
      FiniteCoordinateSupportFaceScaleTransportAssumptionsFor hfaces) :
    FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces where
  first_reveal_branch := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB a
    have hv :=
      hvalue.first_coordinate_face_value hax q r hq hr hA hB a
    have hs :=
      hscale.first_coordinate_face_scale hax q r hq hr hA hB a
    simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
      BranchAggregationCocycleNormalizedChainRuleStructure.chain,
      branchChainStructure_of_scaleFactorization, hv, hs]
  second_reveal_branch := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB b
    have hv :=
      hvalue.second_coordinate_face_value hax q r hq hr hA hB b
    have hs :=
      hscale.second_coordinate_face_scale hax q r hq hr hA hB b
    simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
      BranchAggregationCocycleNormalizedChainRuleStructure.chain,
      branchChainStructure_of_scaleFactorization, hv, hs]

/-- Reassemble the Stage 29 continuation-sum transport package from pointwise
coordinate-face continuation transport. -/
theorem coordinateRevealContinuationTransport_of_branchTransport
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hbranch :
      FiniteCoordinateRevealBranchContinuationTransportAssumptionsFor hfaces) :
    FiniteCoordinateRevealContinuationTransportAssumptionsFor hfaces where
  first_reveal_continuation_sum := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    calc
      ∑ a : A,
          (Channel.outcomeMarginal
            (productFirstRevealChannel (A := A) (B := B))
            (prodDist q r)) a *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r) a)
            (productSecondRevealChannel (A := A) (B := B))
          =
        ∑ a : A,
          q a *
          (fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r) := by
            apply Finset.sum_congr rfl
            intro a _
            rw [outcomeMarginal_productFirstRevealChannel_prodDist]
            rw [hbranch.first_reveal_branch hax q r hq hr hA hB a]
      _ =
        fullRevelationValueForFaceScales hfaces r /
          hfaces.branch_result.scale_factorization.scale r := by
            rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  second_reveal_continuation_sum := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    calc
      ∑ b : B,
          (Channel.outcomeMarginal
            (productSecondRevealChannel (A := A) (B := B))
            (prodDist q r)) b *
          branchNormalizedValue hfaces.chain
            (Channel.posterior
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r) b)
            (productFirstRevealChannel (A := A) (B := B))
          =
        ∑ b : B,
          r b *
          (fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [outcomeMarginal_productSecondRevealChannel_prodDist]
            rw [hbranch.second_reveal_branch hax q r hq hr hA hB b]
      _ =
        fullRevelationValueForFaceScales hfaces q /
          hfaces.branch_result.scale_factorization.scale q := by
            rw [← Finset.sum_mul, r.sum_eq_one, one_mul]

/-- The normalized sequential full-revelation bridge follows from coordinate
reveal value transport, continuation support-face transport, and the already
proved normalized chain rule. -/
theorem sequentialFullRevelationNormalizedChain_of_coordinateTransports
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hvalue : FiniteCoordinateRevealValueTransportAssumptionsFor hfaces)
    (hcont :
      FiniteCoordinateRevealContinuationTransportAssumptionsFor hfaces) :
    FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces where
  normalized_chain_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hchain :=
      hfaces.normalizedChainRule (prodDist q r) hprod_full
        (productFirstRevealChannel (A := A) (B := B))
        (fun _ => productSecondRevealChannel (A := A) (B := B))
    have hseq_left :
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              (fun _ => productSecondRevealChannel (A := A) (B := B))) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productFirstThenSecondReveal_eq_idChannel]
      rfl
    have hfirst :
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
        BranchAggregationCocycleNormalizedChainRuleStructure.chain,
        branchChainStructure_of_scaleFactorization,
        fullRevelationValueForFaceScales,
        hvalue.first_reveal_value hax q r hq hr hA hB]
    have hcontsum :=
      hcont.first_reveal_continuation_sum hax q r hq hr hA hB
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productFirstRevealChannel (A := A) (B := B)) ▷
              (fun _ => productSecondRevealChannel (A := A) (B := B))) :=
            hseq_left.symm
      _ =
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productFirstRevealChannel (A := A) (B := B)) +
          ∑ a : A,
            (Channel.outcomeMarginal
              (productFirstRevealChannel (A := A) (B := B))
              (prodDist q r)) a *
            branchNormalizedValue hfaces.chain
              (Channel.posterior
                (productFirstRevealChannel (A := A) (B := B))
                (prodDist q r) a)
              (productSecondRevealChannel (A := A) (B := B)) := hchain
      _ =
        fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale r := by
            rw [hfirst, hcontsum]
  normalized_chain_right := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hchain :=
      hfaces.normalizedChainRule (prodDist q r) hprod_full
        (productSecondRevealChannel (A := A) (B := B))
        (fun _ => productFirstRevealChannel (A := A) (B := B))
    have hseq_right :
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              (fun _ => productFirstRevealChannel (A := A) (B := B))) =
          fullRevelationValueForFaceScales hfaces (prodDist q r) /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      rw [productSecondThenFirstReveal_eq_swapReveal]
      simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
        BranchAggregationCocycleNormalizedChainRuleStructure.chain,
        branchChainStructure_of_scaleFactorization,
        fullRevelationValueForFaceScales,
        hvalue.swap_full_revelation_value hax q r hq hr hA hB]
    have hsecond :
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) =
          fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) := by
      simp [branchNormalizedValue, CoherentRelabelingFaceScalesStructure.chain,
        BranchAggregationCocycleNormalizedChainRuleStructure.chain,
        branchChainStructure_of_scaleFactorization,
        fullRevelationValueForFaceScales,
        hvalue.second_reveal_value hax q r hq hr hA hB]
    have hcontsum :=
      hcont.second_reveal_continuation_sum hax q r hq hr hA hB
    calc
      fullRevelationValueForFaceScales hfaces (prodDist q r) /
          hfaces.branch_result.scale_factorization.scale (prodDist q r)
          =
        branchNormalizedValue hfaces.chain (prodDist q r)
            ((productSecondRevealChannel (A := A) (B := B)) ▷
              (fun _ => productFirstRevealChannel (A := A) (B := B))) :=
            hseq_right.symm
      _ =
        branchNormalizedValue hfaces.chain (prodDist q r)
            (productSecondRevealChannel (A := A) (B := B)) +
          ∑ b : B,
            (Channel.outcomeMarginal
              (productSecondRevealChannel (A := A) (B := B))
              (prodDist q r)) b *
            branchNormalizedValue hfaces.chain
              (Channel.posterior
                (productSecondRevealChannel (A := A) (B := B))
                (prodDist q r) b)
              (productFirstRevealChannel (A := A) (B := B)) := hchain
      _ =
        fullRevelationValueForFaceScales hfaces r /
            hfaces.branch_result.scale_factorization.scale (prodDist q r) +
          fullRevelationValueForFaceScales hfaces q /
            hfaces.branch_result.scale_factorization.scale q := by
            rw [hsecond, hcontsum]

/-- Clearing denominators in the normalized sequential full-revelation
equations gives the existing scale-weighted Step 1 package. -/
theorem productRevelationSequentialScale_of_normalizedChain
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hnorm :
      FiniteSequentialFullRevelationNormalizedChainAssumptionsFor hfaces) :
    FiniteProductRevelationSequentialScaleAssumptionsFor hfaces where
  sequential_reveal_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hnorm_left :=
      hnorm.normalized_chain_left hax q r hq hr hA hB
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hsp_pos :
        0 <
          hfaces.branch_result.scale_factorization.scale (prodDist q r) :=
      hfaces.branch_result.scale_factorization.scale_pos
        (prodDist q r) hprod_full
    have hsr_pos :
        0 < hfaces.branch_result.scale_factorization.scale r :=
      hfaces.branch_result.scale_factorization.scale_pos r hr
    have hsp_ne :
        hfaces.branch_result.scale_factorization.scale (prodDist q r) ≠ 0 :=
      ne_of_gt hsp_pos
    have hsr_ne :
        hfaces.branch_result.scale_factorization.scale r ≠ 0 :=
      ne_of_gt hsr_pos
    field_simp [hsp_ne, hsr_ne] at hnorm_left
    ring_nf at hnorm_left ⊢
    linarith
  sequential_reveal_right := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hnorm_right :=
      hnorm.normalized_chain_right hax q r hq hr hA hB
    have hprod_full : (prodDist q r).FullSupport :=
      prodDist_fullSupport q r hq hr
    have hsp_pos :
        0 <
          hfaces.branch_result.scale_factorization.scale (prodDist q r) :=
      hfaces.branch_result.scale_factorization.scale_pos
        (prodDist q r) hprod_full
    have hsq_pos :
        0 < hfaces.branch_result.scale_factorization.scale q :=
      hfaces.branch_result.scale_factorization.scale_pos q hq
    have hsp_ne :
        hfaces.branch_result.scale_factorization.scale (prodDist q r) ≠ 0 :=
      ne_of_gt hsp_pos
    have hsq_ne :
        hfaces.branch_result.scale_factorization.scale q ≠ 0 :=
      ne_of_gt hsq_pos
    field_simp [hsp_ne, hsq_ne] at hnorm_right
    ring_nf at hnorm_right ⊢
    linarith

/-- Reconstruct the old product-revelation scale-link package from the
sequential-revelation scale equations plus the internal full-revelation product
identity and A1 nonzero full revelation. -/
theorem productRevelationScaleLink_of_sequentialScale
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hseq : FiniteProductRevelationSequentialScaleAssumptionsFor hfaces) :
    FiniteProductRevelationScaleLinkAssumptionsFor hfaces hprod where
  scale_product_left := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hprodH :=
      fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
        hfaces hprod hax q r hq hr
    have hseq_left :=
      hseq.sequential_reveal_left hax q r hq hr hA hB
    have hHr_ne :
        fullRevelationValueForFaceScales hfaces r ≠ 0 :=
      fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax r hr hB
    have hdiff :
        fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces q =
          (1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces q) *
            fullRevelationValueForFaceScales hfaces r := by
      rw [hprodH]
      ring
    rw [hdiff] at hseq_left
    have hmul :
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces q) *
            hfaces.branch_result.scale_factorization.scale r) *
          fullRevelationValueForFaceScales hfaces r =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces r := by
      calc
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces q) *
            hfaces.branch_result.scale_factorization.scale r) *
          fullRevelationValueForFaceScales hfaces r
            =
          hfaces.branch_result.scale_factorization.scale r *
            ((1 + hprod.kappa hax *
                fullRevelationValueForFaceScales hfaces q) *
              fullRevelationValueForFaceScales hfaces r) := by ring
        _ =
          hfaces.branch_result.scale_factorization.scale (prodDist q r) *
            fullRevelationValueForFaceScales hfaces r := hseq_left
    exact (mul_right_cancel₀ hHr_ne hmul).symm
  scale_product_right := by
    intro hax A B _ _ _ _ _ _ q r hq hr hA hB
    have hprodH :=
      fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
        hfaces hprod hax q r hq hr
    have hseq_right :=
      hseq.sequential_reveal_right hax q r hq hr hA hB
    have hHq_ne :
        fullRevelationValueForFaceScales hfaces q ≠ 0 :=
      fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax q hq hA
    have hdiff :
        fullRevelationValueForFaceScales hfaces (prodDist q r) -
            fullRevelationValueForFaceScales hfaces r =
          (1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces r) *
            fullRevelationValueForFaceScales hfaces q := by
      rw [hprodH]
      ring
    rw [hdiff] at hseq_right
    have hmul :
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces r) *
            hfaces.branch_result.scale_factorization.scale q) *
          fullRevelationValueForFaceScales hfaces q =
        hfaces.branch_result.scale_factorization.scale (prodDist q r) *
          fullRevelationValueForFaceScales hfaces q := by
      calc
        ((1 + hprod.kappa hax *
              fullRevelationValueForFaceScales hfaces r) *
            hfaces.branch_result.scale_factorization.scale q) *
          fullRevelationValueForFaceScales hfaces q
            =
          hfaces.branch_result.scale_factorization.scale q *
            ((1 + hprod.kappa hax *
                fullRevelationValueForFaceScales hfaces r) *
              fullRevelationValueForFaceScales hfaces q) := by ring
        _ =
          hfaces.branch_result.scale_factorization.scale (prodDist q r) *
            fullRevelationValueForFaceScales hfaces q := hseq_right
    exact (mul_right_cancel₀ hHq_ne hmul).symm

/-- `Z(q) = 1 + kappa * H(q)` for the product-interaction proof. -/
noncomputable def productScaleZForFaceScales
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : PureTraceConditions F)
    {A : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    (q : Dist A) : ℝ :=
  1 + hprod.kappa hax * fullRevelationValueForFaceScales hfaces q

/-- The product `Z`-weight is multiplicative: `Z(q ⊗ r) = Z(q) · Z(r)`.

This is the Lean form of the paper's identity (M) `w(u⊗v)=w(u)w(v)` (Lemma
scalecoherence, Step 3, eq. wmult), obtained directly from the internal
full-revelation product identity `H(q⊗r)=H(q)+H(r)+κH(q)H(r)`.  It is proved
here with no extra assumptions — but note it holds for EVERY value of `κ`, so
multiplicativity alone does not force `κ = 0`; that requires the full
partition/disjoint-union grouping equation. -/
theorem productScaleZForFaceScales_prod_eq
    {F : PrefFamily.{u}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (hax : PureTraceConditions F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (q : Dist A) (r : Dist B) (hq : q.FullSupport) (hr : r.FullSupport) :
    productScaleZForFaceScales hfaces hprod hax (prodDist q r) =
      productScaleZForFaceScales hfaces hprod hax q *
        productScaleZForFaceScales hfaces hprod hax r := by
  have hH :=
    fullRevelationValueForFaceScales_prod_eq_of_productQuasiAdditivity
      hfaces hprod hax q r hq hr
  unfold productScaleZForFaceScales
  rw [hH]
  ring

/-- The two-grouping algebra core (paper Lemma scalecoherence, Step 3).

Comparing the two evaluations (E1) `s·(x²+y²)/2` and (E2) `s·((x+y)/2)²` of the
same disjoint-union weight `w(T)` with `s = w(p) > 0` forces `(x−y)² = 0`, hence
`x = y`.  This is the pure real-analysis heart of the argument and is
independent of any representation detail. -/
theorem twoGrouping_eq_of_evaluations
    {s x y : ℝ} (hs : 0 < s)
    (hE : s * ((x ^ 2 + y ^ 2) / 2) = s * (((x + y) / 2) ^ 2)) :
    x = y := by
  have hsq : (x - y) ^ 2 = 0 := by
    have h := mul_left_cancel₀ (ne_of_gt hs) hE
    nlinarith [h]
  have : x - y = 0 := by nlinarith [sq_nonneg (x - y), hsq]
  linarith

/-- Full-revelation value `H` is invariant under action relabeling, from exact
posterior-value relabeling of the selected representatives.  This is the Lean
form of the paper's Corollary permutationinvariance restricted to full
revelation, and it is what lets the two-grouping regroup a disjoint union along
different partitions. -/
theorem fullRevelationValueForFaceScales_relabel_eq
    (hrelV : FinitePosteriorValueRelabelingAssumptions.{u})
    {F : PrefFamily.{u}} (hax : PureTraceConditions F)
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    {A B : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (e : A ≃ B) (q : Dist A) :
    fullRevelationValueForFaceScales hfaces (Relabeling.relabelDist e q) =
      fullRevelationValueForFaceScales hfaces q := by
  have hrel :=
    hrelV.V_relabel_eq F hax hfaces.branch_result.branch_agg.value_rep
      e e q (Channel.idChannel : Channel A A)
  have hid :
      Relabeling.relabelChannel e e (Channel.idChannel : Channel A A) =
        (Channel.idChannel : Channel B B) := by
    funext b
    ext b'
    rw [Relabeling.relabelChannel_apply]
    simp only [Channel.idChannel]
    by_cases hbb : b' = b
    · subst hbb
      rw [Dist.pure_apply_self, Dist.pure_apply_self]
    · rw [Dist.pure_apply_ne (e.symm b) (e.symm b')
          (fun h => hbb (e.symm.injective h)),
        Dist.pure_apply_ne b b' hbb]
  rw [hid] at hrel
  simpa [fullRevelationValueForFaceScales] using hrel

/-- The fixed nondegenerate reference action type used to cancel the common
interaction coefficient. -/
abbrev universalScaleReferenceType : Type u := ULift.{u, 0} Bool

/-- The fixed full-support reference prior for the two-grouping cleanup. -/
noncomputable def universalScaleReferencePrior : Dist universalScaleReferenceType :=
  Dist.uniform

theorem universalScaleReferencePrior_fullSupport :
    universalScaleReferencePrior.FullSupport :=
  Dist.uniform_fullSupport (A := universalScaleReferenceType)

theorem universalScaleReference_not_subsingleton :
    ¬ Subsingleton universalScaleReferenceType := by
  intro hsub
  have htf : (true : Bool) = false := by
    exact congrArg ULift.down
      (Subsingleton.elim
        (ULift.up true : universalScaleReferenceType)
        (ULift.up false : universalScaleReferenceType))
  cases htf

/-- Sharper two-grouping bridge: the grouping equation forces the induced
`Z`-weight to be one at every nondegenerate full-support prior.  The remaining
cancellation from this fact to `kappa = 0` is internal. -/
structure FiniteProductGroupingWeightConstantAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  Z_eq_one_of_nondegenerate :
    ∀ (hax : PureTraceConditions F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport) (_hA : ¬ Subsingleton A),
      productScaleZForFaceScales hfaces hprod hax q = 1

/-- Product `Z`-weight positivity (paper eq. POS `1 + κ F_r(ν) > 0`), phrased at
full revelation.  This is the positive-slice-slope consequence of coherent
product quasi-additivity, needed so that `w = 1/Z` is a well-defined positive
weight in the two-grouping argument. -/
structure FiniteProductScaleZPositiveAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  Z_pos :
    ∀ (hax : PureTraceConditions F)
      {A : Type v} [Fintype A] [DecidableEq A] [Nonempty A]
      (q : Dist A) (_hq : q.FullSupport),
      0 < productScaleZForFaceScales hfaces hprod hax q

/-- The `Z`-weight is the calibrated first-coordinate slice slope.

Comparing coherent product quasi-additivity with the slice-affine decomposition
at the two calibrated first-coordinate points `U` (no information) and `id`
(full revelation), over a nondegenerate reference first coordinate, identifies

`faceScaleAffineSliceTransformSlope haff hax q₀ q id = 1 + κ·H(q) = Z(q)`.

This is the cardinal identification behind the paper's POS condition. -/
theorem productScaleZForFaceScales_eq_sliceTransformSlope
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces)
    (hax : PureTraceConditions F)
    {A₀ A : Type u}
    [Fintype A₀] [DecidableEq A₀] [Nonempty A₀]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (q₀ : Dist A₀) (q : Dist A)
    (hq₀ : q₀.FullSupport) (hq : q.FullSupport)
    (hA₀ : ¬ Subsingleton A₀) :
    productScaleZForFaceScales hfaces hprod hax q =
      faceScaleAffineSliceTransformSlope haff hax q₀ q
        (Channel.idChannel : Channel A A) := by
  classical
  set V := hfaces.branch_result.branch_agg.value_rep with hV
  set hslice := faceScaleProductLeftSliceAffine_of_transform haff with hhslice
  have hH₀_ne :
      fullRevelationValueForFaceScales hfaces q₀ ≠ 0 :=
    fullRevelationValueForFaceScales_ne_zero_of_A1 hfaces hax q₀ hq₀ hA₀
  -- Slice-affine at the two calibrated first-coordinate points.
  have hU :=
    hslice.left_slice_affine hax q₀ q hq₀ hq
      (Channel.uninformativeChannelU A₀)
      (Channel.idChannel : Channel A A)
  have hId :=
    hslice.left_slice_affine hax q₀ q hq₀ hq
      (Channel.idChannel : Channel A₀ A₀)
      (Channel.idChannel : Channel A A)
  -- Product quasi-additivity at the same two points.
  have hqaU :=
    hprod.product_quasi_add hax q₀ q hq₀ hq
      (Channel.uninformativeChannelU A₀)
      (Channel.idChannel : Channel A A)
  have hqaId :=
    hprod.product_quasi_add hax q₀ q hq₀ hq
      (Channel.idChannel : Channel A₀ A₀)
      (Channel.idChannel : Channel A A)
  have hzero₀ :
      V.V q₀ (experimentOfChannel (Channel.uninformativeChannelU A₀)) = 0 :=
    V.zero_normalized q₀ hq₀
  -- Intercept identification: intercept = H(q).
  rw [hzero₀] at hU hqaU
  rw [mul_zero, zero_add] at hU
  rw [mul_zero, zero_mul, add_zero, zero_add] at hqaU
  have hintercept :
      hslice.leftSliceIntercept hax q₀ q (Channel.idChannel : Channel A A) =
        fullRevelationValueForFaceScales hfaces q := by
    have := hU.symm.trans hqaU
    simpa [fullRevelationValueForFaceScales] using this
  -- Slope identification: slope·H(q₀) = H(q₀)·(1 + κ·H(q)).
  have hkey :
      hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) *
          fullRevelationValueForFaceScales hfaces q₀ =
        (1 + hprod.kappa hax * fullRevelationValueForFaceScales hfaces q) *
          fullRevelationValueForFaceScales hfaces q₀ := by
    have hchain := hId.symm.trans hqaId
    rw [hintercept] at hchain
    have hchain' :
        hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) *
            fullRevelationValueForFaceScales hfaces q₀ =
          fullRevelationValueForFaceScales hfaces q₀ +
            hprod.kappa hax * fullRevelationValueForFaceScales hfaces q₀ *
              fullRevelationValueForFaceScales hfaces q := by
      have := hchain
      simp only [fullRevelationValueForFaceScales] at this ⊢
      linarith
    rw [hchain']
    ring
  have hslope_eq :
      hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) =
        1 + hprod.kappa hax * fullRevelationValueForFaceScales hfaces q :=
    mul_right_cancel₀ hH₀_ne hkey
  have hslope_def :
      hslice.leftSliceSlope hax q₀ q (Channel.idChannel : Channel A A) =
        faceScaleAffineSliceTransformSlope haff hax q₀ q
          (Channel.idChannel : Channel A A) := rfl
  rw [productScaleZForFaceScales, ← hslope_eq, hslope_def]

/-- **Concrete POS, proved.**  `Z(q) = 1 + κ·H(q) > 0` for every full-support
prior, for ANY coherent product quasi-additivity package, given the slice-affine
transform.  The abstract `κ` is pinned by the value function through
quasi-additivity: `Z(q)` IS the calibrated slice slope, which is the positive
multiplier of a positive affine transform
(`faceScaleAffineSliceTransformSlope_pos`).  This discharges the paper's POS
condition (eq. QAslope) with no extra assumption. -/
theorem productScaleZpositive_of_sliceTransform
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces)
    (haff :
      FiniteFaceScaleProductLeftSliceAffineTransformAssumptionsFor hfaces) :
    FiniteProductScaleZPositiveAssumptionsFor hfaces hprod where
  Z_pos := by
    intro hax A _ _ _ q hq
    rw [productScaleZForFaceScales_eq_sliceTransformSlope hprod haff hax
      universalScaleReferencePrior q
      universalScaleReferencePrior_fullSupport hq
      universalScaleReference_not_subsingleton]
    exact faceScaleAffineSliceTransformSlope_pos haff hax
      universalScaleReferencePrior q
      universalScaleReferencePrior_fullSupport hq
      (Channel.idChannel : Channel A A)

/-- **Pre-universal grouping weight recursion — the paper's weight equation (W).**

For a finite partition presented as a dependent sigma family (`sigmaDist p f`,
with block probabilities `p` and within-block conditionals `f`), the inverse
`Z`-weight `w = Z⁻¹` satisfies

`w(sigmaDist p f) = w(p) · Σₖ pₖ · w(fₖ)`.

This is paper eq. (W) (Lemma scalecoherence, Step 2, derived there from the
grouping recursion (GR), which in turn comes from the block bridge, the branch
formula, and undetectable-distinctions neutrality — all strictly BEFORE
universal scale, entropy reduction, or Faddeev).  It is stated at the
pre-universal face-scale layer, for the face-scale `Z(·) = 1 + κ·H(·)` only.

Nondegeneracy side conditions: the sigma total, the coarse prior, and every
positive-probability block conditional are nondegenerate full-support; blocks
with `pₖ = 0` do not constrain the equation (their `w` term is multiplied by
`pₖ = 0`), so the recursion is quantified over full-support `p`.

This is strictly earlier and strictly more primitive than the two-grouping
evaluations E1/E2, which are DERIVED from it below
(`finiteProductTwoGroupingWeightEquation_of_weightRecursion`). -/
structure FinitePreUniversalGroupingWeightRecursionAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  weight_recursion :
    ∀ (hax : PureTraceConditions F)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (f : ∀ k, Dist (Act k))
      (_hp : p.FullSupport)
      (_hf : ∀ k, (f k).FullSupport)
      (_hsigma : (sigmaDist p f).FullSupport)
      (_hKnd : ¬ Subsingleton K)
      (_hAnd : ∀ k, ¬ Subsingleton (Act k)),
      (productScaleZForFaceScales hfaces hprod hax (sigmaDist p f))⁻¹ =
        (productScaleZForFaceScales hfaces hprod hax p)⁻¹ *
          ∑ k, p k *
            (productScaleZForFaceScales hfaces hprod hax (f k))⁻¹
  reference_Z_eq_one :
    ∀ (hax : PureTraceConditions F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- **Repaired grouping target — the paper's two-grouping equation (W)/(E1)/(E2).**

This replaces the opaque `FiniteProductGroupingReferenceWeightAssumptionsFor`
conclusion with the *cause* the paper actually uses: the labelled
disjoint-union `T = ½(u⊗u)⁰ ⊔ ½(v⊗v)¹` admits two groupings, whose weight
equation (paper eqs. (E1)/(E2), Lemma scalecoherence Step 3) evaluate `w(T)` two
ways.  Concretely, writing `w(·) = 1/Z(·)`, for every pair of nondegenerate
full-support priors there is a common positive top-block weight `wp > 0` with

* (E1) `w(T) = wp · (x² + y²)/2`, and
* (E2) `w(T) = wp · ((x + y)/2)²`,

where `x = w(u)`, `y = w(v)`.  A reference normalization fixes `Z` at the
reference prior to one.

This is faithful to the paper's named grouping equation and strictly more
primitive than the reference-weight conclusion: the entire nontrivial
cancellation `(x − y)² = 0 ⟹ Z(u) = Z(v) ⟹ Z ≡ 1 ⟹ κ = 0` is proved from it
below.  The remaining content is exactly the block-bridge grouping recursion
supplying the two evaluations, which is the genuine pre-universal input that is
not yet formalized at this layer. -/
structure FiniteProductTwoGroupingWeightEquationAssumptionsFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  two_grouping_evaluations :
    ∀ (hax : PureTraceConditions F)
      {U V : Type v}
      [Fintype U] [DecidableEq U] [Nonempty U]
      [Fintype V] [DecidableEq V] [Nonempty V]
      (u : Dist U) (v : Dist V) (_hu : u.FullSupport) (_hv : v.FullSupport)
      (_hU : ¬ Subsingleton U) (_hV : ¬ Subsingleton V),
      ∃ wT wp : ℝ, 0 < wp ∧
        wT = wp *
            (((productScaleZForFaceScales hfaces hprod hax u)⁻¹ ^ 2 +
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹ ^ 2) / 2) ∧
        wT = wp *
            ((((productScaleZForFaceScales hfaces hprod hax u)⁻¹ +
              (productScaleZForFaceScales hfaces hprod hax v)⁻¹) / 2) ^ 2)
  reference_Z_eq_one :
    ∀ (hax : PureTraceConditions F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/-- **Two-grouping cancellation.**  The paper's Step-3 conclusion `w(u) = w(v)`
for nondegenerate full-support priors, from the two evaluations of `w(T)`. -/
theorem productScaleZ_inv_eq_of_twoGrouping
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hax : PureTraceConditions F)
    {U V : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (u : Dist U) (v : Dist V) (hu : u.FullSupport) (hv : v.FullSupport)
    (hU : ¬ Subsingleton U) (hV : ¬ Subsingleton V) :
    (productScaleZForFaceScales hfaces hprod hax u)⁻¹ =
      (productScaleZForFaceScales hfaces hprod hax v)⁻¹ := by
  obtain ⟨wT, wp, hwp, hE1, hE2⟩ :=
    hgroup.two_grouping_evaluations hax u v hu hv hU hV
  exact twoGrouping_eq_of_evaluations hwp (hE1.symm.trans hE2)

/-- Product `Z` is constant across nondegenerate full-support priors, from the
two-grouping cancellation and `Z`-positivity. -/
theorem productScaleZ_eq_of_twoGrouping
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hgroup :
      FiniteProductTwoGroupingWeightEquationAssumptionsFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod)
    (hax : PureTraceConditions F)
    {U V : Type u}
    [Fintype U] [DecidableEq U] [Nonempty U]
    [Fintype V] [DecidableEq V] [Nonempty V]
    (u : Dist U) (v : Dist V) (hu : u.FullSupport) (hv : v.FullSupport)
    (hU : ¬ Subsingleton U) (hV : ¬ Subsingleton V) :
    productScaleZForFaceScales hfaces hprod hax u =
      productScaleZForFaceScales hfaces hprod hax v := by
  have hinv := productScaleZ_inv_eq_of_twoGrouping hgroup hax u v hu hv hU hV
  have hZu := hpos.Z_pos hax u hu
  have hZv := hpos.Z_pos hax v hv
  -- x⁻¹ = y⁻¹ with x,y > 0 gives x = y.
  have := congrArg (fun t => t⁻¹) hinv
  simpa [inv_inv] using this

end TraceableAgency
