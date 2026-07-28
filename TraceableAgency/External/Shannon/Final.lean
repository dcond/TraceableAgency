import TraceableAgency.External.Shannon.Approx

/-!
# Shannon.Entropy.Final

Final theorem layer.

Combines the rational characterization and continuity extension to prove:
- natural-log uniqueness (`entropyNat_unique`);
- base-parametric uniqueness (`entropyBase_unique`).
-/
namespace Shannon

noncomputable section
open Filter
open scoped Topology

/-! ## Final Characterization Theorems -/

/-! ### Theorem Index

- `entropyNat_unique`
- `entropyBase_unique`
-/

/--
Uniqueness in natural-log units:
every `H` satisfying the axiom bundle agrees with Shannon entropy up to the
positive multiplicative constant `K H`.
-/
theorem entropyNat_unique
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α]
    (p : ProbDist α) (hpfull : ∀ a, 0 < p a) :
    H p = -K H * ∑ a, p a * Real.log (p a) := by
  have hseq :
      ∀ N : ℕ, H (approxProb p N) = K H * entropyNat (approxProb p N) := by
    intro N
    have hN := entropyNat_approxProb H hH p N
    simpa [entropyNat, mul_assoc, mul_left_comm, mul_comm] using hN
  have hleft :
      Tendsto (fun N : ℕ => H (approxProb p N)) atTop (𝓝 (H p)) := by
    exact hH.sequentiallyContinuous_fullSupport p hpfull
      (fun N => approxProb p N)
      (fun N a => by
        rw [approxProb_apply]
        exact div_pos (by exact_mod_cast approxCount_pos p N a)
          (by exact_mod_cast approxTotal_pos p N))
      (tendsto_approxProb p)
  have hright :
      Tendsto (fun N : ℕ => K H * entropyNat (approxProb p N)) atTop (𝓝 (K H * entropyNat p)) := by
    have hcont : Continuous (fun q : ProbDist α => K H * entropyNat q) :=
      continuous_const.mul continuous_entropyNat
    exact hcont.continuousAt.tendsto.comp (tendsto_approxProb p)
  have hright' :
      Tendsto (fun N : ℕ => H (approxProb p N)) atTop (𝓝 (K H * entropyNat p)) := by
    convert hright using 1
    funext N
    exact hseq N
  have hlim : H p = K H * entropyNat p := tendsto_nhds_unique hleft hright'
  simpa [entropyNat, mul_assoc, mul_left_comm, mul_comm] using hlim

end

end Shannon
