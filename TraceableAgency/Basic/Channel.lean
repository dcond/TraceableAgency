/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import Mathlib.Algebra.BigOperators.Field
import TraceableAgency.Basic.Dist

/-!
# Finite Channels

Finite channels P : A → Dist O as row-stochastic matrices.
Includes joint laws, marginals, posteriors, and basic channel operations.
-/

namespace TraceableAgency

universe u

variable {A O A' O' : Type*}
variable [Fintype A] [Fintype O]

/-- A finite channel from actions A to outcomes O. -/
abbrev Channel (A O : Type*) [Fintype O] := A → Dist O

namespace Channel

variable (P : Channel A O) (q : Dist A)

/-- Joint law J_{q,P}(a,o) = q(a) * P(o|a). -/
def joint (a : A) (o : O) : ℝ := q a * P a o

theorem joint_nonneg (a : A) (o : O) : 0 ≤ joint P q a o :=
  mul_nonneg (q.nonneg a) ((P a).nonneg o)

theorem joint_sum_eq_one : ∑ a, ∑ o, joint P q a o = 1 := by
  unfold joint
  simp_rw [← Finset.mul_sum, (P _).sum_eq_one, mul_one]
  exact q.sum_eq_one

/-- Outcome marginal m_{q,P}(o) = Σ_a q(a) * P(o|a). -/
noncomputable def outcomeMarginal : Dist O where
  prob := fun o => ∑ a, q a * P a o
  nonneg := fun o => Finset.sum_nonneg (fun a _ => mul_nonneg (q.nonneg a) ((P a).nonneg o))
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (P _).sum_eq_one, mul_one]
    exact q.sum_eq_one

@[simp]
theorem outcomeMarginal_apply (o : O) : (outcomeMarginal P q) o = ∑ a, q a * P a o := rfl

variable [DecidableEq A] [Nonempty A]

/-- Posterior r_o^{q,P}(a) = q(a) * P(o|a) / m_{q,P}(o) when m_{q,P}(o) > 0.
    This is a partial definition; returns a default when marginal is zero. -/
noncomputable def posterior (o : O) : Dist A :=
  if h : (outcomeMarginal P q) o > 0 then
    ⟨fun a => q a * P a o / (outcomeMarginal P q) o,
     fun a => div_nonneg (mul_nonneg (q.nonneg a) ((P a).nonneg o)) (le_of_lt h),
     by
       rw [← Finset.sum_div]
       simp only [outcomeMarginal_apply]
       exact div_self (ne_of_gt h)⟩
  else Dist.pure (Classical.arbitrary A)

/-- Predicate: outcome o has positive probability under (q, P). -/
def OutcomePositive (o : O) : Prop := (outcomeMarginal P q) o > 0

variable [DecidableEq O]

/-- The identity channel (full revelation): Id_A : A → Δ(A). -/
def idChannel : Channel A A := fun a => Dist.pure a

/-- The uninformative channel U_A : A → Δ({*}). -/
def uninformativeChannel (A : Type*) [Fintype A] : Channel A Unit :=
  fun _ => ⟨fun _ => 1, fun _ => by norm_num, by simp⟩

/-- The uninformative channel U_A : A → Δ(PUnit.{u+1}) in universe u.
    This universe-polymorphic version is needed when the outcome type must
    live in the same universe as the action type A : Type u. -/
def uninformativeChannelU (A : Type u) [Fintype A] : Channel A PUnit.{u+1} :=
  fun _ =>
    { prob := fun _ => 1
      nonneg := fun _ => by norm_num
      sum_eq_one := by simp [Finset.univ_unique, Finset.sum_singleton] }

/-- Outcome post-processing: (PT)(o'|a) = Σ_o P(o|a) * T(o'|o). -/
noncomputable def postprocess [Fintype O'] (T : Channel O O') : Channel A O' :=
  fun a => ⟨fun o' => ∑ o, P a o * T o o',
    fun o' => Finset.sum_nonneg (fun o _ => mul_nonneg ((P a).nonneg o) ((T o).nonneg o')),
    by
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, (T _).sum_eq_one, mul_one]
      exact (P a).sum_eq_one⟩

/-- Stochastic kernel for action coarsening S : A → Δ(A'). -/
abbrev ActionKernel (A A' : Type*) [Fintype A'] := A → Dist A'

/-- Action pushforward: (qS)(a') = Σ_a q(a) * S(a'|a). -/
noncomputable def actionPushforward [Fintype A'] (S : ActionKernel A A') : Dist A' where
  prob := fun a' => ∑ a, q a * S a a'
  nonneg := fun a' => Finset.sum_nonneg (fun a _ => mul_nonneg (q.nonneg a) ((S a).nonneg a'))
  sum_eq_one := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (S _).sum_eq_one, mul_one]
    exact q.sum_eq_one

/-- Posterior pushforward: (rS)(a') = Σ_a r(a) * S(a'|a). -/
noncomputable def posteriorPushforward [Fintype A'] (r : Dist A) (S : ActionKernel A A') : Dist A' :=
  actionPushforward r S

/--
Predicate for a Bayesian pushforward completion.
Given S : A → Δ(A'), prior q, channel P, a completion P_hat : A' → Dist O is valid if
for every a' with (qS)(a') > 0:
  P_hat(o|a') = Σ_a q(a) * S(a'|a) * P(o|a) / (qS)(a')

This is the paper's S^q P, which is only defined on rows with positive (qS)(a') mass.
Zero-probability rows can be completed arbitrarily.
-/
def IsBayesPushforwardCompletion [Fintype A'] [DecidableEq A']
    (S : ActionKernel A A') (P_hat : Channel A' O) : Prop :=
  let qS := actionPushforward q S
  ∀ a', qS a' > 0 →
    ∀ o, P_hat a' o = (∑ a, q a * S a a' * P a o) / qS a'

end Channel

end TraceableAgency
