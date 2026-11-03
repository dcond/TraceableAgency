import TraceableAgency.Section3.Independence.GiniBasic

/-! # Structural identities for the Gini counterexample -/

namespace TraceableAgency.Section3.Independence

open TraceableAgency Theorem1

universe u

 theorem giniInformation_relabelOutcome
    {A Z Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Z] [DecidableEq Z] [Fintype Y] [DecidableEq Y]
    (e : Z ≃ Y) (q : Dist A) (K : Channel A Z) :
    giniInformation q (Relabeling.relabelChannel (Equiv.refl A) e K) =
      giniInformation q K := by
  rw [giniInformation_eq_posterior, giniInformation_eq_posterior]
  have h := posteriorLawIntegral_relabelChannel (Equiv.refl A) e q K squareMass
  simpa only [Relabeling.relabelDist_refl] using congrArg (fun z => z - squareMass q) h

 theorem giniInformation_block_inl
    {A B X Y : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (q : Dist A) (K : Channel A X) (L : Channel B Y) :
    giniInformation (inlDist q) (blockChannel K L) = giniInformation q K := by
  unfold giniInformation squareMass
  simp only [Fintype.sum_sum_type, inlDist_apply_inl, inlDist_apply_inr,
    blockChannel_apply_inl_inl, blockChannel_apply_inl_inr,
    blockChannel_apply_inr_inl, blockChannel_apply_inr_inr,
    outcomeMarginal_block_inl_inl, outcomeMarginal_block_inl_inr,
    zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    zero_div, div_zero, add_zero, zero_add]

 theorem giniInformation_block_inr
    {A B X Y : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (q : Dist B) (K : Channel A X) (L : Channel B Y) :
    giniInformation (inrDist q) (blockChannel K L) = giniInformation q L := by
  unfold giniInformation squareMass
  simp only [Fintype.sum_sum_type, inrDist_apply_inl, inrDist_apply_inr,
    blockChannel_apply_inl_inl, blockChannel_apply_inl_inr,
    blockChannel_apply_inr_inl, blockChannel_apply_inr_inr,
    outcomeMarginal_block_inr_inl, outcomeMarginal_block_inr_inr,
    zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    zero_div, div_zero, add_zero, zero_add]

 theorem squareMass_blockEmbed
    {I : Type u} [Fintype I] [DecidableEq I]
    (Act : I → Type u) [∀i, Fintype (Act i)] [∀i, DecidableEq (Act i)]
    (i : I) (q : Dist (Act i)) : squareMass (blockEmbedDist Act i q) = squareMass q := by
  unfold squareMass
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · simp only [blockEmbedDist_apply_same]
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro a _
    rw [blockEmbedDist_apply_ne Act hji q a]
    norm_num
  · simp

 theorem giniInformation_blockFamily_embed
    {I : Type u} [Fintype I] [DecidableEq I]
    (Act Out : I → Type u)
    [∀i, Fintype (Act i)] [∀i, DecidableEq (Act i)]
    [∀i, Fintype (Out i)] [∀i, DecidableEq (Out i)]
    (K : ∀ i, Channel (Act i) (Out i)) (i : I) (q : Dist (Act i)) :
    giniInformation (blockEmbedDist Act i q) (blockFamilyChannel Act Out K) =
      giniInformation q (K i) := by
  unfold giniInformation
  rw [squareMass_blockEmbed]
  congr 1
  rw [Fintype.sum_sigma, Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro z _
    rw [outcomeMarginal_blockFamily_embed_same]
    congr 1
    rw [Fintype.sum_sigma, Finset.sum_eq_single i]
    · simp only [blockEmbedDist_apply_same, blockFamilyChannel_apply_same]
    · intro j _ hji
      apply Finset.sum_eq_zero
      intro a _
      rw [blockEmbedDist_apply_ne Act hji q a]
      simp
    · simp
  · intro j _ hji
    apply Finset.sum_eq_zero
    intro z _
    rw [outcomeMarginal_blockFamily_embed_ne Act Out K hji]
    exact div_zero _
  · simp

 theorem giniInformation_commonBlock_left
    {O A B R S : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (q : Dist A) (K : Channel A (O × R)) (L : Channel B (O × S)) :
    giniInformation (leftBlockDist q) (commonPayoffBlockChannel K L) = giniInformation q K := by
  rw [commonPayoffBlockChannel, giniInformation_relabelOutcome]
  exact giniInformation_block_inl q K L

 theorem giniInformation_commonBlock_right
    {O A B R S : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
    (p : Dist B) (K : Channel A (O × R)) (L : Channel B (O × S)) :
    giniInformation (rightBlockDist p) (commonPayoffBlockChannel K L) = giniInformation p L := by
  rw [commonPayoffBlockChannel, giniInformation_relabelOutcome]
  exact giniInformation_block_inr p K L

 theorem giniInformation_commonBlockFamily_embed
    {O I : Type u} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (Act Rec : I → Type u)
    [∀i, Fintype (Act i)] [∀i, DecidableEq (Act i)] [∀i, Nonempty (Act i)]
    [∀i, Fintype (Rec i)] [∀i, DecidableEq (Rec i)] [∀i, Nonempty (Rec i)]
    (K : ∀ i, Channel (Act i) (O × Rec i)) (i : I) (q : Dist (Act i)) :
    giniInformation (commonPayoffBlockEmbed Act i q)
      (commonPayoffBlockFamilyChannel Act Rec K) = giniInformation q (K i) := by
  rw [commonPayoffBlockFamilyChannel, giniInformation_relabelOutcome]
  exact giniInformation_blockFamily_embed Act (fun i => O × Rec i) K i q

 theorem giniInformation_seqComposeDep
    {A Y : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y]
    (Rec : Y → Type u) [∀y, Fintype (Rec y)] [∀y, DecidableEq (Rec y)]
    (q : Dist A) (P : Channel A Y) (K : ∀y, Channel A (Rec y)) :
    giniInformation q (seqComposeDep P Rec K) = giniInformation q P +
      ∑ y, (Channel.outcomeMarginal P q) y *
        giniInformation (Channel.posterior P q y) (K y) := by
  simp_rw [giniInformation_eq_posterior]
  rw [posteriorLawIntegral_seqComposeDep_eq_sum]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  unfold posteriorLawIntegral
  ring

 theorem giniInformation_commonCompound
    {O A Y : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀y, Fintype (Rec y)] [∀y, DecidableEq (Rec y)] [∀y, Nonempty (Rec y)]
    (q : Dist A) (P : Channel A Y) (K : ∀ y, Channel A (O × Rec y)) :
    giniInformation q (commonPayoffCompound Rec P K) = giniInformation q P +
      ∑ y, (Channel.outcomeMarginal P q) y *
        giniInformation (branchPosterior P q y) (K y) := by
  rw [commonPayoffCompound, giniInformation_relabelOutcome, giniInformation_seqComposeDep]
  rfl

 theorem giniFamily_pairWeak
    {O : Type u} [Fintype O] [DecidableEq O] (v : O → ℝ)
    {A B R S : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    [Fintype R] [DecidableEq R] [Nonempty R]
    [Fintype S] [DecidableEq S] [Nonempty S]
    (q : Dist A) (K : Channel A (O × R)) (p : Dist B) (L : Channel B (O × S)) :
    pairWeak (giniFamily v) q K p L ↔
      expectedPayoffUtility v q K + giniInformation q K ≥
        expectedPayoffUtility v p L + giniInformation p L := by
  unfold pairWeak giniFamily scoreFamily
  dsimp only
  rw [expectedPayoffUtility_commonBlock_left, expectedPayoffUtility_commonBlock_right,
    giniInformation_commonBlock_left, giniInformation_commonBlock_right]

 theorem giniFamily_a5
    {O : Type u} [Fintype O] [DecidableEq O] (v : O → ℝ) :
    A5_BlockComparisonCoherence (giniFamily v) := by
  constructor
  · intro A R _ _ _ _ _ _ K q p
    rw [giniFamily_pairWeak]
    rfl
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    rw [giniFamily_pairWeak]
    change _ + _ ≥ _ + _ ↔ _
    rw [expectedPayoffUtility_commonBlockFamily_embed, expectedPayoffUtility_commonBlockFamily_embed,
      giniInformation_commonBlockFamily_embed, giniInformation_commonBlockFamily_embed]

 theorem giniScore_commonCompound
    {O A Y : Type u} [Fintype O] [DecidableEq O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (Rec : Y → Type u)
    [∀y, Fintype (Rec y)] [∀y, DecidableEq (Rec y)] [∀y, Nonempty (Rec y)]
    (v : O → ℝ) (q : Dist A) (P : Channel A Y) (K : ∀y, Channel A (O × Rec y)) :
    expectedPayoffUtility v q (commonPayoffCompound Rec P K) +
      giniInformation q (commonPayoffCompound Rec P K) = giniInformation q P +
      ∑ y, (Channel.outcomeMarginal P q) y *
        (expectedPayoffUtility v (branchPosterior P q y) (K y) +
          giniInformation (branchPosterior P q y) (K y)) := by
  rw [expectedPayoffUtility_commonCompound, giniInformation_commonCompound]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

 theorem giniFamily_a8
    {O : Type u} [Fintype O] [DecidableEq O] (v : O → ℝ) :
    A8_RecordwiseSureThing (giniFamily v) := by
  intro A R _ _ _ _ _ _ q P K L M hy
  rw [giniFamily_pairWeak, giniFamily_pairWeak]
  simp only [binaryPayoffCompound, giniScore_commonCompound]
  have hsum (f : RelevanceBit.{u} → ℝ) :
      ∑ b, f b = f (ULift.up true) + f (ULift.up false) := by
    rw [← (Equiv.ulift (α := Bool)).symm.sum_comp f]
    simp [Fintype.sum_bool, Equiv.ulift]
  simp only [hsum, binaryContinuationProfile, if_true, Bool.false_eq_true, if_false,
    ge_iff_le, add_le_add_iff_left, add_le_add_iff_right]
  exact (mul_le_mul_iff_right₀ hy).symm

end TraceableAgency.Section3.Independence
