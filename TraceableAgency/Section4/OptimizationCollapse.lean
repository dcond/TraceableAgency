import TraceableAgency.Section4.OptimizationBasic

/-! # Collapsing actions with identical rows and rewards

A surjective class map makes the class lottery the only relevant choice.
For material rewards, identical channel rows automatically have equal rewards.
-/
namespace TraceableAgency.Section4
open TraceableAgency Theorem1
universe u

noncomputable def collapsePrior {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (q : Dist A) : Dist B :=
  Channel.actionPushforward q (fun a => Dist.pure (f a))

 theorem sum_collapsePrior {A B : Type u} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (q : Dist A) (g : B → ℝ) :
    (∑ b, collapsePrior f q b * g b) = ∑ a, q a * g (f a) := by
  classical
  change (∑ b, (∑ a, q a * Dist.pure (f a) b) * g b) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp [Dist.pure_apply]

 theorem outcomeMarginal_collapse {A B Z : Type u}
    [Fintype A] [Fintype B] [DecidableEq B] [Fintype Z]
    (f : A → B) (q : Dist A) (L : Channel B Z) :
    Channel.outcomeMarginal L (collapsePrior f q) =
      Channel.outcomeMarginal (fun a => L (f a)) q := by
  ext z
  exact sum_collapsePrior f q (fun b => L b z)

 theorem rowRewardValue_collapse {A B Z : Type u}
    [Fintype A] [Fintype B] [DecidableEq B] [Fintype Z]
    (f : A → B) (s : B → ℝ) (lambda : ℝ) (q : Dist A) (L : Channel B Z) :
    rowRewardValue s lambda (collapsePrior f q) L =
      rowRewardValue (fun a => s (f a)) lambda q (fun a => L (f a)) := by
  rw [rowRewardValue_entropy, rowRewardValue_entropy, outcomeMarginal_collapse,
    sum_collapsePrior]

 theorem collapsePrior_comp {A B C : Type u}
    [Fintype A] [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (f : B → C) (g : A → B) (q : Dist A) :
    collapsePrior f (collapsePrior g q) = collapsePrior (fun a => f (g a)) q := by
  ext c
  exact sum_collapsePrior g q (fun b => Dist.pure (f b) c)

@[simp] theorem collapsePrior_id {A : Type u} [Fintype A] [DecidableEq A]
    (q : Dist A) : collapsePrior (fun a : A => a) q = q := by
  ext a
  simp [collapsePrior, Channel.actionPushforward, Dist.pure_apply]

 theorem collapsePrior_surjective {A B : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (f : A → B) (hf : Function.Surjective f) : Function.Surjective (collapsePrior f) := by
  classical
  obtain ⟨g,hg⟩ := hf.hasRightInverse
  intro p
  refine ⟨collapsePrior g p, ?_⟩
  rw [collapsePrior_comp]
  have he : (fun b => f (g b)) = fun b => b := funext hg
  rw [he, collapsePrior_id]

/-- All splits of a class mass among identical rows have the same value;
optimality is exactly optimality of the collapsed class lottery. -/
 theorem optimal_collapse_iff {A B Z : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] [Fintype Z]
    (f : A → B) (hf : Function.Surjective f) (s : B → ℝ)
    (lambda : ℝ) (L : Channel B Z) (q : Dist A) :
    IsOptimal (fun a => s (f a)) lambda (fun a => L (f a)) q ↔
      IsOptimal s lambda L (collapsePrior f q) := by
  constructor
  · intro h p
    obtain ⟨p',hp'⟩ := collapsePrior_surjective f hf p
    rw [← hp', rowRewardValue_collapse, rowRewardValue_collapse]
    exact h p'
  · intro h p
    simpa only [rowRewardValue_collapse] using h (collapsePrior f p)

/-- For the paper's material reward, the channel factorization alone is enough. -/
 theorem material_optimal_collapse_iff {A B O R : Type u}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype O] [Fintype R]
    (f : A → B) (hf : Function.Surjective f) (v : O → ℝ)
    (lambda : ℝ) (L : Channel B (O × R)) (q : Dist A) :
    IsOptimal (fun a => ∑ z, L (f a) z * v z.1) lambda (fun a => L (f a)) q ↔
      IsOptimal (fun b => ∑ z, L b z * v z.1) lambda L (collapsePrior f q) :=
  optimal_collapse_iff f hf (fun b => ∑ z, L b z * v z.1) lambda L q

/-- If all channel rows and rewards coincide, every lottery has the same value. -/
 theorem rowRewardValue_constant_channel {A Z : Type u} [Fintype A] [Fintype Z]
    (c lambda : ℝ) (q : Dist A) (p : Dist Z) :
    rowRewardValue (fun _ => c) lambda q (fun _ => p) = c := by
  have hm : Channel.outcomeMarginal (fun _ : A => p) q = p := by
    ext z
    simp only [Channel.outcomeMarginal_apply, ← Finset.sum_mul, q.sum_eq_one, one_mul]
  rw [rowRewardValue_entropy, hm]
  rw [← Finset.sum_mul, q.sum_eq_one, one_mul]
  ring

 theorem constant_channel_all_optimal {A Z : Type u} [Fintype A] [Fintype Z]
    (c lambda : ℝ) (p : Dist Z) (q : Dist A) :
    IsOptimal (fun _ => c) lambda (fun _ => p) q := by
  intro t
  rw [rowRewardValue_constant_channel, rowRewardValue_constant_channel]

 theorem material_value_constant_channel {A O R : Type u}
    [Fintype A] [Fintype O] [Fintype R]
    (v : O → ℝ) (lambda : ℝ) (q : Dist A) (p : Dist (O × R)) :
    traceTemperedValue v lambda q (fun _ => p) = ∑ z, p z * v z.1 := by
  rw [← rowRewardValue_material]
  exact rowRewardValue_constant_channel _ _ q p

end TraceableAgency.Section4
