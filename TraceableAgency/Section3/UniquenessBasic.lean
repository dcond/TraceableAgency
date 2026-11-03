import TraceableAgency.Theorem1.Benchmark

/-! # Common-scale numerical indices on the complete finite domain -/

namespace TraceableAgency.Section3

open TraceableAgency Theorem1

universe u

/-- A finite lottery--channel pair, including its finite alphabets. -/
structure FiniteExperiment (O : Type u) [Fintype O] where
  Act : Type u
  Rec : Type u
  [actFintype : Fintype Act]
  [actDecidableEq : DecidableEq Act]
  [actNonempty : Nonempty Act]
  [recFintype : Fintype Rec]
  [recDecidableEq : DecidableEq Rec]
  [recNonempty : Nonempty Rec]
  prior : Dist Act
  channel : Channel Act (O × Rec)

attribute [instance] FiniteExperiment.actFintype FiniteExperiment.actDecidableEq
  FiniteExperiment.actNonempty FiniteExperiment.recFintype
  FiniteExperiment.recDecidableEq FiniteExperiment.recNonempty

/-- A real index defined on every finite lottery--channel pair. -/
abbrev CommonIndex (O : Type u) [Fintype O] := FiniteExperiment O → ℝ

noncomputable abbrev FiniteExperiment.ofChannel
    {O A R : Type u} [Fintype O]
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (K : Channel A (O × R)) : FiniteExperiment O :=
  ⟨A, R, q, K⟩

noncomputable def valueIndex
    {O : Type u} [Fintype O] (u : O → ℝ) (lambda : ℝ) : CommonIndex O :=
  fun E => traceTemperedValue u lambda E.prior E.channel

/-- The paper's within-channel and arbitrary finite-block requirements,
with the same real index in both clauses. -/
def CommonScaleRepresentation
    {O : Type u} [Fintype O] [DecidableEq O]
    (F : FixedPayoffPrefFamily O) (W : CommonIndex O) : Prop :=
  (∀ {A R : Type u} [Fintype A] [DecidableEq A] [Nonempty A]
      [Fintype R] [DecidableEq R] [Nonempty R]
      (K : Channel A (O × R)) (q p : Dist A),
    F.rel K q p ↔ W (.ofChannel q K) ≥ W (.ofChannel p K)) ∧
  (∀ {I : Type u} [Fintype I] [DecidableEq I] [Nonempty I]
      (Act Rec : I → Type u)
      [∀ i, Fintype (Act i)] [∀ i, DecidableEq (Act i)] [∀ i, Nonempty (Act i)]
      [∀ i, Fintype (Rec i)] [∀ i, DecidableEq (Rec i)] [∀ i, Nonempty (Rec i)]
      (K : ∀ i, Channel (Act i) (O × Rec i))
      (i j : I) (_ : i ≠ j) (qi : Dist (Act i)) (qj : Dist (Act j)),
    F.rel (commonPayoffBlockFamilyChannel Act Rec K)
      (commonPayoffBlockEmbed Act i qi) (commonPayoffBlockEmbed Act j qj) ↔
      W (.ofChannel qi (K i)) ≥ W (.ofChannel qj (K j)))

/-- Numerical branch additivity; the zero-mass summands vanish. The common
continuation alphabet is exactly the one in Section 3 of the paper. -/
def BranchAdditiveIndex
    {O : Type u} [Fintype O] [DecidableEq O] (W : CommonIndex O) : Prop :=
  ∀ {A Y R : Type u}
    [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype R] [DecidableEq R] [Nonempty R]
    (q : Dist A) (P : Channel A Y) (K L : Y → Channel A (O × R)),
  W (.ofChannel q (commonPayoffCompound (fun _ : Y => R) P K)) -
    W (.ofChannel q (commonPayoffCompound (fun _ : Y => R) P L)) =
    ∑ y, (Channel.outcomeMarginal P q) y *
      (W (.ofChannel (branchPosterior P q y) (K y)) -
        W (.ofChannel (branchPosterior P q y) (L y)))

noncomputable def minimumOutcome
    {O : Type u} [Fintype O] [Nonempty O] (u : O → ℝ) : O :=
  Classical.choose (Finset.exists_min_image Finset.univ u Finset.univ_nonempty)

noncomputable def minPayoff
    {O : Type u} [Fintype O] [Nonempty O] (u : O → ℝ) : ℝ :=
  u (minimumOutcome u)

theorem minPayoff_le
    {O : Type u} [Fintype O] [Nonempty O] (u : O → ℝ) (o : O) :
    minPayoff u ≤ u o :=
  (Classical.choose_spec
    (Finset.exists_min_image Finset.univ u Finset.univ_nonempty)).2 o (Finset.mem_univ o)

theorem commonScale_valueIndex
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda) :
    CommonScaleRepresentation F (valueIndex u lambda) :=
  ⟨hrep, sameWitnessBlockRepresentation_of_representation hrep⟩

theorem commonScale_order_iff
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {W : CommonIndex O}
    {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda)
    (hW : CommonScaleRepresentation F W) (E D : FiniteExperiment O) :
    W E ≤ W D ↔ valueIndex u lambda E ≤ valueIndex u lambda D := by
  let X : RelevanceBit → FiniteExperiment O := fun b => if b.down then D else E
  let Act : RelevanceBit → Type u := fun b => (X b).Act
  let Rec : RelevanceBit → Type u := fun b => (X b).Rec
  let K : ∀ b, Channel (Act b) (O × Rec b) := fun b => (X b).channel
  have hne : (ULift.up true : RelevanceBit.{u}) ≠ ULift.up false := by decide
  have h1 := hW.2 Act Rec K (ULift.up true) (ULift.up false) hne D.prior E.prior
  have h2 := (commonScale_valueIndex hrep).2 Act Rec K
    (ULift.up true) (ULift.up false) hne D.prior E.prior
  exact h1.symm.trans h2

theorem commonScale_iff_order
    {O : Type u} [Fintype O] [DecidableEq O]
    {F : FixedPayoffPrefFamily O} {W : CommonIndex O}
    {u : O → ℝ} {lambda : ℝ}
    (hrep : WithinChannelRepresentation F u lambda) :
    CommonScaleRepresentation F W ↔
      ∀ E D, W E ≤ W D ↔ valueIndex u lambda E ≤ valueIndex u lambda D := by
  refine ⟨fun h E D => commonScale_order_iff hrep h E D, ?_⟩
  intro h
  constructor
  · intro A R _ _ _ _ _ _ K q p
    exact (hrep K q p).trans (h (.ofChannel p K) (.ofChannel q K)).symm
  · intro I _ _ _ Act Rec _ _ _ _ _ _ K i j hij qi qj
    exact (sameWitnessBlockRepresentation_of_representation hrep Act Rec K i j hij qi qj).trans
      (h (.ofChannel qj (K j)) (.ofChannel qi (K i))).symm

theorem branchAdditive_valueIndex
    {O : Type u} [Fintype O] [DecidableEq O]
    (u : O → ℝ) (lambda : ℝ) : BranchAdditiveIndex (valueIndex u lambda) := by
  intro A Y R _ _ _ _ _ _ _ _ _ q P K L
  dsimp only [valueIndex, FiniteExperiment.ofChannel]
  rw [traceTemperedValue_commonCompound, traceTemperedValue_commonCompound]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

end TraceableAgency.Section3
