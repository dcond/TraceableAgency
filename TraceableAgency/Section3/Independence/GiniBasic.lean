import TraceableAgency.Section3.Independence.Basic
import TraceableAgency.PureTrace.Support.EntropyReduction.SliceAffine

/-! # The Gini posterior-reduction score

The rational formula has zero contribution at null outputs because division
by zero in the real field is zero. Its equivalence with expected posterior
Gini reduction is proved below, including all boundary priors.
-/

namespace TraceableAgency.Section3.Independence

open TraceableAgency Theorem1

universe u

noncomputable def squareMass {A : Type u} [Fintype A] (q : Dist A) : ℝ :=
  ∑ a, (q a)^2

noncomputable def gini {A : Type u} [Fintype A] (q : Dist A) : ℝ :=
  1 - squareMass q

noncomputable def giniInformation {A Z : Type u} [Fintype A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) : ℝ :=
  (∑ z, (∑ a, (q a * K a z)^2) / (Channel.outcomeMarginal K q) z) - squareMass q

noncomputable def giniFamily {O : Type u} [Fintype O] (v : O → ℝ) :
    FixedPayoffPrefFamily O :=
  scoreFamily (fun q K => expectedPayoffUtility v q K + giniInformation q K)

theorem squareMass_nonneg {A : Type u} [Fintype A] (q : Dist A) : 0 ≤ squareMass q :=
  Finset.sum_nonneg fun a _ => sq_nonneg _

theorem squareMass_le_one {A : Type u} [Fintype A] (q : Dist A) : squareMass q ≤ 1 := by
  calc
    squareMass q ≤ ∑ a, q a := Finset.sum_le_sum fun a _ => by
      have hn := q.nonneg a
      have hu := q.prob_le_one a
      nlinarith
    _ = 1 := q.sum_eq_one

theorem giniInformation_eq_posterior {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) :
    giniInformation q K = posteriorLawIntegral q K squareMass - squareMass q := by
  classical
  unfold giniInformation posteriorLawIntegral
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  by_cases hp : 0 < (Channel.outcomeMarginal K q) z
  · simp only [Channel.posterior, dif_pos hp, squareMass]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    field_simp
  · have hz : (Channel.outcomeMarginal K q) z = 0 :=
      le_antisymm (le_of_not_gt hp) ((Channel.outcomeMarginal K q).nonneg z)
    rw [hz]
    simp only [div_zero, zero_mul]

theorem giniInformation_eq_gini_reduction {A Z : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype Z]
    (q : Dist A) (K : Channel A Z) :
    giniInformation q K = gini q - posteriorLawIntegral q K gini := by
  rw [giniInformation_eq_posterior]
  unfold gini posteriorLawIntegral
  simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  rw [(Channel.outcomeMarginal K q).sum_eq_one]
  ring

end TraceableAgency.Section3.Independence
