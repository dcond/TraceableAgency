/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Info.Identities
import Mathlib.Analysis.Convex.Jensen

/-!
# Finite data processing

The two data-processing inequalities used by the benchmark direction are
proved here from finite entropy concavity.  No information-theoretic theorem
is assumed.
-/

namespace TraceableAgency

universe u

/-- A finite probability distribution witnesses that its carrier is
nonempty. -/
theorem finiteDist_carrier_nonempty {X : Type u} [Fintype X] (p : Dist X) :
    Nonempty X := by
  classical
  by_cases hX : Nonempty X
  · exact hX
  · letI : IsEmpty X := not_nonempty_iff.mp hX
    have hsum := p.sum_eq_one
    simp at hsum

/-- Shannon entropy is concave under an arbitrary finite mixture. -/
theorem sum_weighted_entropy_le_entropy_actionPushforward
    {I X : Type u}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (w : Dist I) (K : I → Dist X) :
    (∑ i : I, w i * H(K i)) ≤ H(Channel.actionPushforward w K) := by
  classical
  unfold entropy
  calc
    (∑ i : I, w i * ∑ x : X, entropyTerm (K i x)) =
        ∑ x : X, ∑ i : I, w i * entropyTerm (K i x) := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
    _ ≤ ∑ x : X,
        entropyTerm ((Channel.actionPushforward w K) x) := by
      apply Finset.sum_le_sum
      intro x _
      have hterm :
          ∀ i : I, entropyTerm (K i x) = Real.negMulLog (K i x) :=
        fun i => entropyTerm_eq_negMulLog ((K i).nonneg x)
      simp_rw [hterm]
      rw [entropyTerm_eq_negMulLog
        ((Channel.actionPushforward w K).nonneg x)]
      have hjensen :=
        Real.concaveOn_negMulLog.le_map_sum
          (t := (Finset.univ : Finset I))
          (w := fun i => w i)
          (p := fun i => K i x)
          (fun i _ => w.nonneg i)
          (by simpa using w.sum_eq_one)
          (fun i _ => (K i).nonneg x)
      simpa [Channel.actionPushforward, smul_eq_mul] using hjensen
    _ = ∑ x : X,
        entropyTerm ((Channel.actionPushforward w K) x) := rfl

/-!
## Action-side data processing
-/

/-- Conditional weights of the original action given a positive-mass
coarsened action. -/
noncomputable def actionBayesWeights
    {A A' : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype A'] [DecidableEq A']
    (q : Dist A) (S : Channel.ActionKernel A A')
    (a' : A') (ha' : 0 < Channel.actionPushforward q S a') :
    Dist A where
  prob := fun a => q a * S a a' / Channel.actionPushforward q S a'
  nonneg := fun a => div_nonneg
    (mul_nonneg (q.nonneg a) ((S a).nonneg a'))
    (le_of_lt ha')
  sum_eq_one := by
    rw [← Finset.sum_div]
    change (Channel.actionPushforward q S a') /
        (Channel.actionPushforward q S a') = 1
    exact div_self (ne_of_gt ha')

/-- At a positive coarsened-action row, a Bayesian completion is exactly the
mixture of the original outcome rows with the conditional Bayes weights. -/
theorem bayesCompletion_row_eq_actionPushforward
    {A A' O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype A'] [DecidableEq A']
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A)
    (S : Channel.ActionKernel A A') (P_hat : Channel A' O)
    (hcompl : Channel.IsBayesPushforwardCompletion P q S P_hat)
    (a' : A') (ha' : 0 < Channel.actionPushforward q S a') :
    P_hat a' =
      Channel.actionPushforward (actionBayesWeights q S a' ha') P := by
  ext o
  rw [hcompl a' ha' o]
  change (∑ a : A, q a * S a a' * P a o) /
      Channel.actionPushforward q S a' =
    ∑ a : A,
      (q a * S a a' / Channel.actionPushforward q S a') * P a o
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  field_simp [ne_of_gt ha']

/-- Entropy in each coarsened-action row dominates the appropriately weighted
entropies of the original rows. -/
theorem action_bayes_row_entropy
    {A A' O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype A'] [DecidableEq A']
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A)
    (S : Channel.ActionKernel A A') (P_hat : Channel A' O)
    (hcompl : Channel.IsBayesPushforwardCompletion P q S P_hat)
    (a' : A') :
    (∑ a : A, q a * S a a' * H(P a)) ≤
      Channel.actionPushforward q S a' * H(P_hat a') := by
  classical
  by_cases ha' : 0 < Channel.actionPushforward q S a'
  · have hconcave :=
      sum_weighted_entropy_le_entropy_actionPushforward
        (actionBayesWeights q S a' ha') P
    rw [← bayesCompletion_row_eq_actionPushforward P q S P_hat hcompl a' ha']
      at hconcave
    have hscale :
        Channel.actionPushforward q S a' *
            (∑ a : A, actionBayesWeights q S a' ha' a * H(P a)) =
          ∑ a : A, q a * S a a' * H(P a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      change Channel.actionPushforward q S a' *
          ((q a * S a a' / Channel.actionPushforward q S a') * H(P a)) =
        q a * S a a' * H(P a)
      field_simp [ne_of_gt ha']
    rw [← hscale]
    exact mul_le_mul_of_nonneg_left hconcave (le_of_lt ha')
  · have ha'zero : Channel.actionPushforward q S a' = 0 :=
      le_antisymm (le_of_not_gt ha')
        ((Channel.actionPushforward q S).nonneg a')
    have hcoeff : ∀ a : A, q a * S a a' = 0 := by
      intro a
      have hle :
          q a * S a a' ≤ ∑ b : A, q b * S b a' :=
        Finset.single_le_sum
          (fun b _ => mul_nonneg (q.nonneg b) ((S b).nonneg a'))
          (Finset.mem_univ a)
      change q a * S a a' ≤ Channel.actionPushforward q S a' at hle
      exact le_antisymm (by simpa [ha'zero] using hle)
        (mul_nonneg (q.nonneg a) ((S a).nonneg a'))
    simp [ha'zero, hcoeff]

/-- A Bayesian action pushforward preserves the outcome marginal. -/
theorem outcomeMarginal_bayesPushforwardCompletion
    {A A' O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype A'] [DecidableEq A']
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A)
    (S : Channel.ActionKernel A A') (P_hat : Channel A' O)
    (hcompl : Channel.IsBayesPushforwardCompletion P q S P_hat) :
    Channel.outcomeMarginal P_hat (Channel.actionPushforward q S) =
      Channel.outcomeMarginal P q := by
  classical
  ext o
  simp only [Channel.outcomeMarginal_apply]
  have hrow :
      ∀ a' : A',
        Channel.actionPushforward q S a' * P_hat a' o =
          ∑ a : A, q a * S a a' * P a o := by
    intro a'
    by_cases ha' : 0 < Channel.actionPushforward q S a'
    · rw [hcompl a' ha' o]
      field_simp [ne_of_gt ha']
    · have ha'zero : Channel.actionPushforward q S a' = 0 :=
        le_antisymm (le_of_not_gt ha')
          ((Channel.actionPushforward q S).nonneg a')
      have hcoeff : ∀ a : A, q a * S a a' = 0 := by
        intro a
        have hle :
            q a * S a a' ≤ ∑ b : A, q b * S b a' :=
          Finset.single_le_sum
            (fun b _ => mul_nonneg (q.nonneg b) ((S b).nonneg a'))
            (Finset.mem_univ a)
        change q a * S a a' ≤ Channel.actionPushforward q S a' at hle
        exact le_antisymm (by simpa [ha'zero] using hle)
          (mul_nonneg (q.nonneg a) ((S a).nonneg a'))
      simp [ha'zero, hcoeff]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    (∑ x : A', q a * S a x * P a o) =
        (q a * P a o) * ∑ x : A', S a x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = q a * P a o := by rw [(S a).sum_eq_one, mul_one]

/-- Finite data processing for Bayesian action coarsening. -/
theorem mutualInfo_action_bayes_pushforward_le
    {A A' O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype A'] [DecidableEq A']
    [Fintype O] [DecidableEq O]
    (P : Channel A O) (q : Dist A)
    (S : Channel.ActionKernel A A') (P_hat : Channel A' O)
    (hcompl : Channel.IsBayesPushforwardCompletion P q S P_hat) :
    mutualInfo (Channel.actionPushforward q S) P_hat ≤ mutualInfo q P := by
  classical
  unfold mutualInfo
  rw [outcomeMarginal_bayesPushforwardCompletion P q S P_hat hcompl]
  apply sub_le_sub_left
  calc
    (∑ a : A, q a * H(P a)) =
        ∑ a' : A', ∑ a : A, q a * S a a' * H(P a) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      calc
        q a * H(P a) =
            (q a * H(P a)) * ∑ a' : A', S a a' := by
          rw [(S a).sum_eq_one, mul_one]
        _ = ∑ a' : A', q a * S a a' * H(P a) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a' _
          ring
    _ ≤ ∑ a' : A',
        Channel.actionPushforward q S a' * H(P_hat a') :=
      Finset.sum_le_sum fun a' _ =>
        action_bayes_row_entropy P q S P_hat hcompl a'

/-!
## Outcome-side data processing by Bayes reversal
-/

/-- The outcome marginal after a post-processing is the stochastic
pushforward of the original outcome marginal. -/
theorem outcomeMarginal_postprocess_eq_actionPushforward
    {A O O' : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    [Fintype O'] [DecidableEq O']
    (q : Dist A) (P : Channel A O) (T : Channel O O') :
    Channel.outcomeMarginal (Channel.postprocess P T) q =
      Channel.actionPushforward (Channel.outcomeMarginal P q) T := by
  classical
  ext o'
  simp only [Channel.outcomeMarginal_apply, Channel.postprocess]
  change (∑ a : A, q a * ∑ o : O, P a o * T o o') =
    ∑ o : O, (∑ a : A, q a * P a o) * T o o'
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  calc
    (∑ a : A, q a * (P a o * T o o')) =
        ∑ a : A, (q a * P a o) * T o o' := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = (∑ a : A, q a * P a o) * T o o' := by
      rw [Finset.sum_mul]

/-- The Bayes-reversed channel has the original prior as its outcome
marginal. -/
theorem outcomeMarginal_posteriorChannel
    {A O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    Channel.outcomeMarginal (fun o => Channel.posterior P q o)
        (Channel.outcomeMarginal P q) = q := by
  classical
  ext a
  simp only [Channel.outcomeMarginal_apply]
  change (∑ o : O,
    Channel.outcomeMarginal P q o * Channel.posterior P q o a) = q a
  simp_rw [posterior_mul_marginal q P]
  rw [← Finset.mul_sum, (P a).sum_eq_one, mul_one]

/-- Mutual information is symmetric when the joint law is written using the
Bayes-reversed channel. -/
theorem mutualInfo_bayes_reverse
    {A O : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    (q : Dist A) (P : Channel A O) :
    mutualInfo (Channel.outcomeMarginal P q)
        (fun o => Channel.posterior P q o) =
      mutualInfo q P := by
  rw [mutualInfo_entropyReduction q P]
  unfold mutualInfo
  rw [outcomeMarginal_posteriorChannel]

/-- Reversing a post-processed experiment gives exactly a Bayesian action
pushforward completion of the original reversed experiment. -/
theorem posteriorChannel_isBayesPushforwardCompletion_postprocess
    {A O O' : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype O] [DecidableEq O]
    [Fintype O'] [DecidableEq O']
    (q : Dist A) (P : Channel A O) (T : Channel O O') :
    Channel.IsBayesPushforwardCompletion
      (fun o => Channel.posterior P q o)
      (Channel.outcomeMarginal P q) T
      (fun o' => Channel.posterior (Channel.postprocess P T) q o') := by
  classical
  intro o' ho' a
  have hmarg :
      Channel.actionPushforward (Channel.outcomeMarginal P q) T o' =
        Channel.outcomeMarginal (Channel.postprocess P T) q o' := by
    rw [outcomeMarginal_postprocess_eq_actionPushforward]
  have hpos :
      0 < Channel.outcomeMarginal (Channel.postprocess P T) q o' := by
    rwa [← hmarg]
  have hleft :
      Channel.posterior (Channel.postprocess P T) q o' a =
        q a * Channel.postprocess P T a o' /
          Channel.outcomeMarginal (Channel.postprocess P T) q o' := by
    unfold Channel.posterior
    rw [dif_pos hpos]
  rw [hleft]
  change
    q a * Channel.postprocess P T a o' /
        Channel.outcomeMarginal (Channel.postprocess P T) q o' =
    (∑ o : O,
      Channel.outcomeMarginal P q o * T o o' *
        Channel.posterior P q o a) /
      Channel.actionPushforward (Channel.outcomeMarginal P q) T o'
  rw [hmarg]
  congr 1
  simp only [Channel.postprocess]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  have hbayes := posterior_mul_marginal q P o a
  calc
    q a * (P a o * T o o') =
        (Channel.outcomeMarginal P q o *
          Channel.posterior P q o a) * T o o' := by
      rw [← mul_assoc, ← hbayes]
    _ = Channel.outcomeMarginal P q o * T o o' *
        Channel.posterior P q o a := by ring

/-- Finite data processing for outcome post-processing. -/
theorem mutualInfo_outcome_postprocess_le
    {A O O' : Type u}
    [Fintype A] [DecidableEq A]
    [Fintype O] [DecidableEq O]
    [Fintype O'] [DecidableEq O']
    (q : Dist A) (P : Channel A O) (T : Channel O O') :
    mutualInfo q (Channel.postprocess P T) ≤ mutualInfo q P := by
  letI : Nonempty A := finiteDist_carrier_nonempty q
  letI : Nonempty O :=
    finiteDist_carrier_nonempty
      (P (Classical.choice (inferInstance : Nonempty A)))
  have haction :=
    mutualInfo_action_bayes_pushforward_le
      (fun o => Channel.posterior P q o)
      (Channel.outcomeMarginal P q) T
      (fun o' => Channel.posterior (Channel.postprocess P T) q o')
      (posteriorChannel_isBayesPushforwardCompletion_postprocess q P T)
  rw [← outcomeMarginal_postprocess_eq_actionPushforward q P T]
    at haction
  simpa only [mutualInfo_bayes_reverse] using haction

end TraceableAgency
