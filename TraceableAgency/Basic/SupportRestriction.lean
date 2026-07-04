/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Basic.Convergence
import TraceableAgency.Info.MutualInfo

/-!
# Support Restriction

Pure finite-probability support restriction machinery.

This file only proves algebraic/probabilistic facts: deleting zero-probability
action rows preserves the restricted prior's full support, outcome marginals,
conditional entropy sums, and mutual information. Preference invariance under
support restriction is paper-specific and is not proved here.
-/

set_option linter.style.header false

namespace TraceableAgency

variable {A O : Type*}
variable [Fintype A]

/-- The positive support of a finite distribution as a finite subtype. -/
def supportSubtype (q : Dist A) : Type _ := { a : A // q a > 0 }

noncomputable instance (q : Dist A) : Fintype (supportSubtype q) := by
  classical
  unfold supportSubtype
  infer_instance

instance [DecidableEq A] (q : Dist A) : DecidableEq (supportSubtype q) := by
  unfold supportSubtype
  infer_instance

/-- A distribution has at least one positive-probability action. -/
theorem supportSubtype_nonempty (q : Dist A) : Nonempty (supportSubtype q) := by
  classical
  by_contra hnone
  have hzero : ∀ a : A, q a = 0 := by
    intro a
    have hnpos : ¬ q a > 0 := by
      intro hpos
      exact hnone ⟨⟨a, hpos⟩⟩
    exact le_antisymm (le_of_not_gt hnpos) (q.nonneg a)
  have hsum_zero : (∑ a : A, q a) = 0 := by
    simp [hzero]
  linarith [q.sum_eq_one]

/-- Sums over the positive support agree with ambient sums for functions that
    vanish on zero-probability actions. -/
theorem sum_supportSubtype_eq_sum_of_zero
    (q : Dist A) (f : A → ℝ)
    (hzero : ∀ a : A, q a = 0 → f a = 0) :
    (∑ a : supportSubtype q, f a.1) = ∑ a : A, f a := by
  classical
  let s : Finset A := Finset.univ.filter (fun a => q a > 0)
  have hsub :
      (∑ a ∈ s, f a) = ∑ a : supportSubtype q, f a.1 := by
    refine Finset.sum_subtype (s := s) ?_ f
    intro a
    simp [s]
  rw [← hsub]
  unfold s
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hpos : q a > 0
  · simp [hpos]
  · have hq0 : q a = 0 := le_antisymm (le_of_not_gt hpos) (q.nonneg a)
    simp [hpos, hzero a hq0]

/-- The sum of probabilities over the positive support is the original total mass. -/
theorem sum_supportSubtype_eq_sum (q : Dist A) :
    (∑ a : supportSubtype q, q a.1) = ∑ a : A, q a :=
  sum_supportSubtype_eq_sum_of_zero q (fun a => q a) (fun _ hq0 => hq0)

namespace Dist

/-- Restrict a distribution to its positive support. -/
noncomputable def restrictToSupport (q : Dist A) : Dist (supportSubtype q) where
  prob := fun a => q a.1
  nonneg := fun a => q.nonneg a.1
  sum_eq_one := by
    rw [sum_supportSubtype_eq_sum, q.sum_eq_one]

@[simp]
theorem restrictToSupport_apply (q : Dist A) (a : supportSubtype q) :
    q.restrictToSupport a = q a.1 := rfl

/-- The support-restricted prior has full support on its support subtype. -/
theorem restrictToSupport_fullSupport (q : Dist A) :
    q.restrictToSupport.FullSupport := by
  intro a
  exact a.2

end Dist

namespace Channel

variable [Fintype O]

/-- Restrict a channel to rows in the positive support of a prior. -/
noncomputable def restrictToSupport (P : Channel A O) (q : Dist A) :
    Channel (supportSubtype q) O :=
  fun a => P a.1

@[simp]
theorem restrictToSupport_apply (P : Channel A O) (q : Dist A) (a : supportSubtype q) :
    restrictToSupport P q a = P a.1 := rfl

/-- Restricting to the prior support preserves the outcome marginal. -/
theorem outcomeMarginal_restrictToSupport (P : Channel A O) (q : Dist A) :
    outcomeMarginal (restrictToSupport P q) q.restrictToSupport =
      outcomeMarginal P q := by
  ext o
  simp only [outcomeMarginal_apply, restrictToSupport_apply, Dist.restrictToSupport_apply]
  exact sum_supportSubtype_eq_sum_of_zero q
    (fun a => q a * P a o)
    (fun a hq0 => by simp [hq0])

end Channel

/-- Restricting to the prior support preserves the conditional entropy sum in
    the noise-form definition of mutual information. -/
theorem condEntropySum_restrictToSupport [Fintype O]
    (P : Channel A O) (q : Dist A) :
    (∑ a : supportSubtype q,
      q.restrictToSupport a * H(Channel.restrictToSupport P q a)) =
    ∑ a : A, q a * H(P a) := by
  simp only [Dist.restrictToSupport_apply, Channel.restrictToSupport_apply]
  exact sum_supportSubtype_eq_sum_of_zero q
    (fun a => q a * H(P a))
    (fun a hq0 => by simp [hq0])

/-- Deleting zero-probability action rows preserves mutual information. -/
theorem mutualInfo_restrictToSupport [Fintype O]
    (P : Channel A O) (q : Dist A) :
    mutualInfo q.restrictToSupport (Channel.restrictToSupport P q) =
      mutualInfo q P := by
  unfold mutualInfo
  rw [Channel.outcomeMarginal_restrictToSupport, condEntropySum_restrictToSupport]

/-!
## Support projection and inclusion kernels

These kernels are the finite stochastic maps used by A5 in the paper's support
restriction argument.  The inclusion embeds a support face back into the ambient
action set.  The projection maps positive-support actions to themselves and
collapses zero-probability actions to an arbitrary support element.
-/

variable [DecidableEq A]

/-- A chosen positive-support element. This is only used to define the arbitrary
projection value on zero-probability ambient actions. -/
noncomputable def supportDefault (q : Dist A) : supportSubtype q :=
  Classical.choice (supportSubtype_nonempty q)

/-- Deterministic projection from the ambient action set to the positive support. -/
noncomputable def supportProject (q : Dist A) (a : A) : supportSubtype q :=
  if h : q a > 0 then ⟨a, h⟩ else supportDefault q

omit [DecidableEq A] in
@[simp]
theorem supportProject_of_pos (q : Dist A) {a : A} (h : q a > 0) :
    supportProject q a = ⟨a, h⟩ := by
  unfold supportProject
  simp [h]

omit [DecidableEq A] in
@[simp]
theorem supportProject_coe (q : Dist A) (a : supportSubtype q) :
    supportProject q a.1 = a := by
  unfold supportProject
  simp [a.2]

/-- Inclusion kernel from the positive support face into the ambient action set. -/
noncomputable def supportIncludeKernel (q : Dist A) :
    Channel.ActionKernel (supportSubtype q) A :=
  fun a => Dist.pure a.1

/-- Projection kernel from the ambient action set onto the positive support face. -/
noncomputable def supportProjectKernel (q : Dist A) :
    Channel.ActionKernel A (supportSubtype q) :=
  fun a => Dist.pure (supportProject q a)

/-- Pushing the support-restricted prior forward by inclusion recovers the
ambient prior. -/
theorem actionPushforward_restrict_include (q : Dist A) :
    Channel.actionPushforward q.restrictToSupport (supportIncludeKernel q) = q := by
  ext a
  change (∑ c : supportSubtype q, q.restrictToSupport c * (supportIncludeKernel q c) a) = q a
  unfold supportIncludeKernel
  by_cases hpos : q a > 0
  · let b : supportSubtype q := ⟨a, hpos⟩
    rw [Fintype.sum_eq_single b]
    · simp [b, Dist.restrictToSupport_apply]
    · intro c hcne
      have hne : a ≠ c.1 := by
        intro ha
        apply hcne
        exact Subtype.ext ha.symm
      simp [Dist.restrictToSupport_apply, Dist.pure_apply_ne _ _ hne]
  · have hq0 : q a = 0 := le_antisymm (le_of_not_gt hpos) (q.nonneg a)
    trans 0
    · apply Finset.sum_eq_zero
      intro c _
      have hne : a ≠ c.1 := by
        intro ha
        exact hpos (ha ▸ c.2)
      simp [Dist.restrictToSupport_apply, Dist.pure_apply_ne _ _ hne]
    · exact hq0.symm

/-- Pushing the ambient prior forward by the support projection gives the
support-restricted prior. -/
theorem actionPushforward_project (q : Dist A) :
    Channel.actionPushforward q (supportProjectKernel q) = q.restrictToSupport := by
  ext b
  change (∑ a : A, q a * (supportProjectKernel q a) b) = q.restrictToSupport b
  unfold supportProjectKernel
  rw [Fintype.sum_eq_single b.1]
  · simp [Dist.restrictToSupport_apply, supportProject_coe]
  · intro a hane
    by_cases hpos : q a > 0
    · have hne : b ≠ supportProject q a := by
        intro hb
        apply hane
        have hval := congrArg Subtype.val hb
        simpa [supportProject_of_pos q hpos] using hval.symm
      simp [Dist.pure_apply_ne _ _ hne]
    · have hq0 : q a = 0 := le_antisymm (le_of_not_gt hpos) (q.nonneg a)
      simp [hq0]

/-- Restricting a channel to the positive support is the Bayesian pushforward
completion of the ambient channel under support projection. -/
theorem restrictToSupport_isBayesPushforwardCompletion [Fintype O]
    (P : Channel A O) (q : Dist A) :
    Channel.IsBayesPushforwardCompletion
      P q (supportProjectKernel q) (Channel.restrictToSupport P q) := by
  intro b hb o
  have hpush := congrArg (fun d : Dist (supportSubtype q) => d b)
    (actionPushforward_project q)
  have hnum :
      (∑ a : A, q a * (Dist.pure (supportProject q a) b) * P a o) =
        q b.1 * P b.1 o := by
    rw [Fintype.sum_eq_single b.1]
    · simp [supportProject_coe]
    · intro a hane
      by_cases hpos : q a > 0
      · have hne : b ≠ supportProject q a := by
          intro hb'
          apply hane
          have hval := congrArg Subtype.val hb'
          simpa [supportProject_of_pos q hpos] using hval.symm
        simp [Dist.pure_apply_ne _ _ hne]
      · have hq0 : q a = 0 := le_antisymm (le_of_not_gt hpos) (q.nonneg a)
        simp [hq0]
  change P b.1 o =
    (∑ a : A, q a * (Dist.pure (supportProject q a) b) * P a o) /
      (Channel.actionPushforward q (supportProjectKernel q)) b
  rw [hnum, hpush, Dist.restrictToSupport_apply]
  exact (mul_div_cancel_left₀ (P b.1 o) (ne_of_gt b.2)).symm

/-- The ambient channel is a Bayesian pushforward completion of its support
restriction under the inclusion kernel.  Rows outside the support have zero
pushed prior, so the completion imposes no constraints there. -/
theorem ambient_isBayesPushforwardCompletion_of_restrict [Fintype O]
    (P : Channel A O) (q : Dist A) :
    Channel.IsBayesPushforwardCompletion
      (Channel.restrictToSupport P q)
      q.restrictToSupport
      (supportIncludeKernel q)
      P := by
  intro a ha o
  have hpush := congrArg (fun d : Dist A => d a)
    (actionPushforward_restrict_include q)
  have hqa : q a > 0 := by
    rw [hpush] at ha
    exact ha
  let b : supportSubtype q := ⟨a, hqa⟩
  have hnum :
      (∑ c : supportSubtype q,
          q.restrictToSupport c * (Dist.pure c.1 a) *
            Channel.restrictToSupport P q c o) =
        q a * P a o := by
    rw [Fintype.sum_eq_single b]
    · simp [b, Dist.restrictToSupport_apply]
    · intro c hcne
      have hne : a ≠ c.1 := by
        intro ha'
        apply hcne
        exact Subtype.ext ha'.symm
      simp [Dist.restrictToSupport_apply, Dist.pure_apply_ne _ _ hne]
  change P a o =
    (∑ c : supportSubtype q,
        q.restrictToSupport c * (Dist.pure c.1 a) *
          Channel.restrictToSupport P q c o) /
      (Channel.actionPushforward q.restrictToSupport (supportIncludeKernel q)) a
  rw [hnum, hpush]
  exact (mul_div_cancel_left₀ (P a o) (ne_of_gt hqa)).symm

/-- At a positive outcome, the posterior of the support-restricted channel,
pushed back into the ambient action set by support inclusion, is the ambient
posterior. -/
theorem posterior_restrictToSupport_include_of_pos [Fintype O] [DecidableEq O]
    [Nonempty A]
    (P : Channel A O) (q : Dist A) [Nonempty (supportSubtype q)] (o : O)
    (hpos : (Channel.outcomeMarginal P q) o > 0) :
    Channel.actionPushforward
        (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)
        (supportIncludeKernel q) =
      Channel.posterior P q o := by
  classical
  have hmarg := congrArg (fun d : Dist O => d o)
    (Channel.outcomeMarginal_restrictToSupport P q)
  have hpos_restrict :
      (Channel.outcomeMarginal (Channel.restrictToSupport P q) q.restrictToSupport) o > 0 := by
    rw [hmarg]
    exact hpos
  ext a
  change
      (∑ b : supportSubtype q,
          Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o b *
            supportIncludeKernel q b a) =
        Channel.posterior P q o a
  by_cases hqa : q a > 0
  · let b : supportSubtype q := ⟨a, hqa⟩
    have hsum :
        (∑ c : supportSubtype q,
            Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o c *
              supportIncludeKernel q c a) =
          Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o b := by
      rw [Fintype.sum_eq_single b]
      · simp [supportIncludeKernel, b]
      · intro c hcne
        have hne : a ≠ c.1 := by
          intro ha
          apply hcne
          exact Subtype.ext ha.symm
        simp [supportIncludeKernel, Dist.pure_apply_ne _ _ hne]
    rw [hsum]
    rw [Channel.posterior, dif_pos hpos_restrict, Channel.posterior, dif_pos hpos]
    simp [b, Channel.restrictToSupport, Dist.restrictToSupport_apply]
    have hden :
        (∑ x : supportSubtype q, q x.1 * P x.1 o) =
          ∑ a : A, q a * P a o :=
      sum_supportSubtype_eq_sum_of_zero q
        (fun a => q a * P a o)
        (fun a hqa0 => by simp [hqa0])
    rw [hden]
  · have hqa0 : q a = 0 := le_antisymm (le_of_not_gt hqa) (q.nonneg a)
    have hsum :
        (∑ b : supportSubtype q,
            Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o b *
              supportIncludeKernel q b a) = 0 := by
      apply Finset.sum_eq_zero
      intro b _
      have hne : a ≠ b.1 := by
        intro ha
        exact hqa (ha ▸ b.2)
      simp [supportIncludeKernel, Dist.pure_apply_ne _ _ hne]
    rw [hsum]
    rw [Channel.posterior, dif_pos hpos]
    simp [hqa0]

/-- Posterior-law reduction for support restriction, stated extensionally
through posterior-law integrals. Deleting zero-prior rows and then pushing the
restricted posterior back into the ambient action set gives the original
posterior law. -/
theorem posteriorLawIntegral_restrictToSupport [Fintype O] [DecidableEq O]
    [Nonempty A]
    (P : Channel A O) (q : Dist A) [Nonempty (supportSubtype q)] (φ : Dist A → ℝ) :
    posteriorLawIntegral q P φ =
      posteriorLawIntegral q.restrictToSupport (Channel.restrictToSupport P q)
        (fun d => φ (Channel.actionPushforward d (supportIncludeKernel q))) := by
  classical
  unfold posteriorLawIntegral
  apply Finset.sum_congr rfl
  intro o _
  have hmarg := congrArg (fun d : Dist O => d o)
    (Channel.outcomeMarginal_restrictToSupport P q)
  by_cases hpos : (Channel.outcomeMarginal P q) o > 0
  · have hpost := posterior_restrictToSupport_include_of_pos P q o hpos
    rw [hmarg]
    have hφ :
        φ (Channel.actionPushforward
            (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)
            (supportIncludeKernel q)) =
          φ (Channel.posterior P q o) := by
      rw [hpost]
    change (Channel.outcomeMarginal P q) o * φ (Channel.posterior P q o) =
      (Channel.outcomeMarginal P q) o *
        φ (Channel.actionPushforward
          (Channel.posterior (Channel.restrictToSupport P q) q.restrictToSupport o)
          (supportIncludeKernel q))
    rw [hφ]
  · have hzero : (Channel.outcomeMarginal P q) o = 0 :=
      le_antisymm (le_of_not_gt hpos) ((Channel.outcomeMarginal P q).nonneg o)
    have hzero_restrict :
        (Channel.outcomeMarginal (Channel.restrictToSupport P q) q.restrictToSupport) o = 0 := by
      rw [hmarg, hzero]
    rw [hzero, hzero_restrict]
    simp

end TraceableAgency
