import TraceableAgency.Theorem1.MarkedHM
import TraceableAgency.Theorem1.Benchmark
import TraceableAgency.Section3.UniquenessBasic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Attainable values of the trace-tempered index

Finite public erasure experiments attain every nonnegative information value.
The construction uses no preference assumptions.
-/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1

universe u

variable {O A : Type u} [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

noncomputable def markedValue (v : O → ℝ) (lam : ℝ) (q : Dist A)
    (E : MarkedTerminalExperiment O A) : ℝ := by
  letI := E.recordFintype
  exact traceTemperedValue v lam q E.K

theorem markedValue_publicMix (v : O → ℝ) (lam : ℝ) (q : Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E G : MarkedTerminalExperiment O A) :
    markedValue v lam q (markedPublicMixExperiment t ht0 ht1 E G) =
      t * markedValue v lam q E + (1 - t) * markedValue v lam q G := by
  letI := E.recordFintype
  letI := E.recordDecEq
  letI := E.recordNonempty
  letI := G.recordFintype
  letI := G.recordDecEq
  letI := G.recordNonempty
  unfold markedValue traceTemperedValue
  change expectedUtilityAlong v Prod.fst q
      (Relabeling.relabelChannel (Equiv.refl A)
        (sumPayoffRecordEquiv O E.RecordType G.RecordType)
        (publicMixChannel t ht0 ht1 E.K G.K)) + _ = _
  rw [expectedUtilityAlong_relabelOutcome, mutualInfo_relabelOutcome,
    mutualInfo_publicMixChannel]
  have hmat : expectedUtilityAlong v
      (fun z => ((sumPayoffRecordEquiv O E.RecordType G.RecordType) z).1)
      q (publicMixChannel t ht0 ht1 E.K G.K) =
      t * expectedPayoffUtility v q E.K +
        (1-t) * expectedPayoffUtility v q G.K := by
    have hpay : (fun z => ((sumPayoffRecordEquiv O E.RecordType G.RecordType) z).1) =
        sumVisiblePayoff := by
      funext z
      cases z <;> rfl
    rw [hpay]
    unfold expectedUtilityAlong expectedPayoffUtility
    simp only [Fintype.sum_sum_type, publicMixChannel, sumVisiblePayoff]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    congr 1
    funext a
    ring
  rw [hmat]
  ring

theorem entropy_uniform_eq_log_card {B : Type u} [Fintype B] [Nonempty B] :
    entropy (Dist.uniform (A := B)) = Real.log (Fintype.card B) := by
  have hc : (0 : ℝ) < Fintype.card B := Nat.cast_pos.mpr Fintype.card_pos
  unfold entropy
  simp_rw [Dist.uniform_apply, entropyTerm_eq_neg_mul_log (one_div_pos.mpr hc)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_div, Real.log_inv]
  field_simp

noncomputable def revealExperiment (o : O) : MarkedTerminalExperiment O A where
  RecordType := A
  recordFintype := inferInstance
  recordDecEq := inferInstance
  recordNonempty := inferInstance
  channel := fullRevealAtPayoff o

noncomputable def silentExperiment (o : O) : MarkedTerminalExperiment O A where
  RecordType := PUnit.{u+1}
  recordFintype := inferInstance
  recordDecEq := inferInstance
  recordNonempty := inferInstance
  channel := uninformativeAtPayoff o

@[simp] theorem markedValue_reveal (v : O → ℝ) (lam : ℝ) (q : Dist A) (o : O) :
    markedValue v lam q (revealExperiment o) = v o + lam * entropy q :=
  traceTemperedValue_fullRevealAtPayoff v lam q o

@[simp] theorem markedValue_silent (v : O → ℝ) (lam : ℝ) (q : Dist A) (o : O) :
    markedValue v lam q (silentExperiment o) = v o :=
  traceTemperedValue_uninformativeAtPayoff v lam q o

theorem exists_markedValue_eq_add (v : O → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (o : O) {x : ℝ} (hx : 0 ≤ x) :
    ∃ n : ℕ, ∃ E : MarkedTerminalExperiment O (ULift.{u} (Fin (n+1))),
      markedValue v lam Dist.uniform E = v o + x := by
  by_cases hx0 : x = 0
  · refine ⟨0, silentExperiment o, ?_⟩
    simp [hx0]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp (x / lam))
  have hnpos : (0 : ℝ) < (n+1 : ℕ) := by positivity
  have hnexp : Real.exp (x / lam) < (n+1 : ℕ) := by exact_mod_cast lt_trans hn (by exact_mod_cast Nat.lt_succ_self n)
  have hlog : x / lam < Real.log (n+1 : ℕ) := (Real.lt_log_iff_exp_lt hnpos).2 hnexp
  let B := ULift.{u} (Fin (n+1))
  have hentropy : entropy (Dist.uniform (A := B)) = Real.log (n+1 : ℕ) := by
    simpa [B] using (entropy_uniform_eq_log_card (B := B))
  have hlarge : x < lam * entropy (Dist.uniform (A := B)) := by
    rw [hentropy]
    simpa [mul_comm] using (div_lt_iff₀ hlam).mp hlog
  let t := x / (lam * entropy (Dist.uniform (A := B)))
  have hden : 0 < lam * entropy (Dist.uniform (A := B)) := lt_trans hxpos hlarge
  have ht0 : 0 < t := div_pos hxpos hden
  have ht1 : t < 1 := (div_lt_one hden).2 hlarge
  refine ⟨n, markedPublicMixExperiment t ht0 ht1 (revealExperiment o)
    (silentExperiment o), ?_⟩
  rw [markedValue_publicMix, markedValue_reveal, markedValue_silent]
  calc
    _ = v o + t * (lam * entropy (Dist.uniform (A := B))) := by ring
    _ = v o + x := by rw [div_mul_cancel₀ _ (ne_of_gt hden)]

theorem lower_bound_value (v : O → ℝ) {lam m : ℝ} (hlam : 0 ≤ lam)
    (hm : ∀ o, m ≤ v o) {R : Type u} [Fintype R]
    (q : Dist A) (K : Channel A (O × R)) :
    m ≤ traceTemperedValue v lam q K := by
  have hmat : m ≤ expectedPayoffUtility v q K := by
    rw [expectedPayoffUtility_eq_marginal]
    calc
      m = ∑ z : O × R, (Channel.outcomeMarginal K q) z * m := by
        rw [← Finset.sum_mul, (Channel.outcomeMarginal K q).sum_eq_one, one_mul]
      _ ≤ ∑ z : O × R, (Channel.outcomeMarginal K q) z * v z.1 :=
        Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hm z.1)
          ((Channel.outcomeMarginal K q).nonneg z)
  have hmi : 0 ≤ mutualInfo q K := by
    classical
    exact sub_nonneg.mpr (sum_weighted_entropy_le_entropy_actionPushforward q K)
  exact le_trans hmat (le_add_of_nonneg_right (mul_nonneg hlam hmi))

/-- Every nonnegative increment above any constant material payoff is attained
by a finite experiment on the original domain. -/
theorem exists_valueIndex_eq_add (v : O → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (o : O) {x : ℝ} (hx : 0 ≤ x) :
    ∃ E : FiniteExperiment O, valueIndex v lam E = v o + x := by
  obtain ⟨n, E, hE⟩ := exists_markedValue_eq_add v hlam o hx
  letI := E.recordFintype
  letI := E.recordDecEq
  letI := E.recordNonempty
  exact ⟨.ofChannel Dist.uniform E.K, hE⟩

theorem minPayoff_le_valueIndex [Nonempty O] (v : O → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (E : FiniteExperiment O) :
    minPayoff v ≤ valueIndex v lam E :=
  lower_bound_value v hlam (minPayoff_le v) E.prior E.channel

theorem valueIndex_range [Nonempty O] (v : O → ℝ) {lam : ℝ} (hlam : 0 < lam) :
    Set.range (valueIndex v lam) = Set.Ici (minPayoff v) := by
  ext w
  constructor
  · rintro ⟨E, rfl⟩
    exact minPayoff_le_valueIndex v hlam.le E
  · intro hw
    obtain ⟨E, hE⟩ := exists_valueIndex_eq_add v hlam (minimumOutcome v)
      (sub_nonneg.mpr hw)
    exact ⟨E, by simpa [minPayoff] using hE⟩

end TraceableAgency.Section3
