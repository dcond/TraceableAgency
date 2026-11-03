import TraceableAgency.Theorem1.FiniteBranchExtension

/-! # Exact one-branch biconditionals from binary A8

The reverse weak implication follows from completeness and strict preservation.
No relevance or continuity axiom is needed.
-/
namespace TraceableAgency.Theorem1
open TraceableAgency
universe u

variable {O A Y : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype Y] [DecidableEq Y] [Nonempty Y]
variable (Rec : Y → Type u)
variable [∀ y, Fintype (Rec y)] [∀ y, DecidableEq (Rec y)]
variable [∀ y, Nonempty (Rec y)]
variable (F : FixedPayoffPrefFamily O)
variable (h1 : A1_WeakOrder F) (h5 : A5_BlockComparisonCoherence F)
variable (h6 : A6_RecordDataProcessing F) (h7 : A7_ActionDataProcessing F)
variable (h8 : A8_RecordwiseSureThing F)
variable (P : Channel A Y) (Q L : ∀ y, Channel A (O × Rec y))
variable (q : Dist A) (target : Y)
variable (htarget : BranchPositive P q target)
variable (hoff : ∀ y, y ≠ target → Q y = L y)

include h1 h5 h6 h7 h8 htarget hoff

theorem pairWeak_oneBranchCompound_iff_v11 :
    pairWeak F q (commonPayoffCompound Rec P Q)
      q (commonPayoffCompound Rec P L) ↔
    pairWeak F (branchPosterior P q target) (Q target)
      (branchPosterior P q target) (L target) := by
  constructor
  · intro hwhole
    by_contra hlocal
    have hreverse := (pairWeak_complete_of_structural F h1 h5 h6 h7
      (branchPosterior P q target) (Q target)
      (branchPosterior P q target) (L target)).resolve_left hlocal
    have hstrict := (pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7
      (branchPosterior P q target) (L target)
      (branchPosterior P q target) (Q target)).mpr ⟨hreverse, hlocal⟩
    have hwholeStrict := pairStrict_oneBranchCompound_of_recordwiseSureThing
      Rec F h1 h5 h6 h7 h8 P L Q q target htarget
      (fun y hy ↦ (hoff y hy).symm) hstrict
    exact ((pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7
      q (commonPayoffCompound Rec P L)
      q (commonPayoffCompound Rec P Q)).mp hwholeStrict).2 hwhole
  · exact pairWeak_oneBranchCompound_of_recordwiseSureThing
      Rec F h1 h5 h6 h7 h8 P Q L q target htarget hoff

theorem pairStrict_oneBranchCompound_iff_v11 :
    pairStrict F q (commonPayoffCompound Rec P Q)
      q (commonPayoffCompound Rec P L) ↔
    pairStrict F (branchPosterior P q target) (Q target)
      (branchPosterior P q target) (L target) := by
  rw [pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7,
    pairStrict_iff_pairWeak_not_swap F h1 h5 h6 h7,
    pairWeak_oneBranchCompound_iff_v11 Rec F h1 h5 h6 h7 h8 P Q L q target htarget hoff,
    pairWeak_oneBranchCompound_iff_v11 Rec F h1 h5 h6 h7 h8 P L Q q target htarget
      (fun y hy ↦ (hoff y hy).symm)]

end TraceableAgency.Theorem1
