/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.MarkedHM
import TraceableAgency.Theorem1.SupportDummy

/-!
# Extending marked experiments from a prior's support

A channel on the positive-support face is extended to the ambient action
alphabet through the canonical support projection.  At the original prior,
the marked terminal law is exactly the source law with each posterior pushed
forward by deterministic support inclusion.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-! ## Channel and experiment extension -/

/-- Extend a channel from the positive-support face to the ambient action
alphabet.  Rows outside the support are filled using the canonical support
projection; those rows are null under the prior. -/
noncomputable def supportExtendChannel
    {Y : Type u} [Fintype Y]
    (r : TraceableAgency.Dist A)
    (K : Channel (supportSubtype r) Y) : Channel A Y :=
  fun a ↦ K (supportProject r a)

@[simp]
theorem restrictToSupport_supportExtendChannel
    {Y : Type u} [Fintype Y]
    (r : TraceableAgency.Dist A)
    (K : Channel (supportSubtype r) Y) :
    Channel.restrictToSupport (supportExtendChannel r K) r = K := by
  funext a
  simp [Channel.restrictToSupport, supportExtendChannel,
    supportProject_coe]

/-- Bundle a support-face marked experiment after extension to the ambient
action alphabet. -/
noncomputable def supportExtendMarkedExperiment
    (r : TraceableAgency.Dist A)
    (E : MarkedTerminalExperiment O (supportSubtype r)) :
    MarkedTerminalExperiment O A where
  RecordType := E.RecordType
  recordFintype := E.recordFintype
  recordDecEq := E.recordDecEq
  recordNonempty := E.recordNonempty
  channel := by
    letI : Fintype E.RecordType := E.recordFintype
    exact supportExtendChannel r E.K

/-- Push a posterior on the support face into the ambient simplex. -/
noncomputable def supportPushforwardPosterior
    (r : TraceableAgency.Dist A)
    (d : TraceableAgency.Dist (supportSubtype r)) :
    TraceableAgency.Dist A :=
  Channel.actionPushforward d (supportIncludeKernel r)

/-! ## Exact marked-law transport -/

/-- Exact marked-terminal integral identity for support extension. -/
theorem markedTerminalIntegral_supportExtend
    (r : TraceableAgency.Dist A)
    (E : MarkedTerminalExperiment O (supportSubtype r))
    (phi : O × TraceableAgency.Dist A → ℝ) :
    markedTerminalIntegral r (supportExtendMarkedExperiment r E) phi =
      markedTerminalIntegral r.restrictToSupport E
        (fun op ↦ phi (op.1, supportPushforwardPosterior r op.2)) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  change
    (∑ z : O × E.RecordType,
      Channel.outcomeMarginal (supportExtendChannel r E.K) r z *
        phi (z.1, Channel.posterior (supportExtendChannel r E.K) r z)) =
      ∑ z : O × E.RecordType,
        Channel.outcomeMarginal E.K r.restrictToSupport z *
          phi (z.1, supportPushforwardPosterior r
            (Channel.posterior E.K r.restrictToSupport z))
  apply Finset.sum_congr rfl
  intro z _hz
  let P : Channel A (O × E.RecordType) := supportExtendChannel r E.K
  have hrestrict : Channel.restrictToSupport P r = E.K := by
    exact restrictToSupport_supportExtendChannel r E.K
  have hmarg := congrArg
    (fun d : TraceableAgency.Dist (O × E.RecordType) ↦ d z)
    (Channel.outcomeMarginal_restrictToSupport P r)
  rw [hrestrict] at hmarg
  by_cases hpos : Channel.outcomeMarginal P r z > 0
  · have hpost := posterior_restrictToSupport_include_of_pos P r z hpos
    rw [hrestrict] at hpost
    change Channel.outcomeMarginal P r z *
        phi (z.1, Channel.posterior P r z) =
      Channel.outcomeMarginal E.K r.restrictToSupport z *
        phi (z.1, supportPushforwardPosterior r
          (Channel.posterior E.K r.restrictToSupport z))
    rw [← hmarg, ← hpost]
    rfl
  · have hambientZero : Channel.outcomeMarginal P r z = 0 :=
      le_antisymm (le_of_not_gt hpos)
        ((Channel.outcomeMarginal P r).nonneg z)
    have hsupportZero :
        Channel.outcomeMarginal E.K r.restrictToSupport z = 0 := by
      rw [hmarg, hambientZero]
    change Channel.outcomeMarginal P r z * _ =
      Channel.outcomeMarginal E.K r.restrictToSupport z * _
    rw [hambientZero, hsupportZero, zero_mul, zero_mul]

/-- Marked-terminal-law equality on the support face is preserved by ambient
extension. -/
theorem sameMarkedTerminalLaw_supportExtend
    (r : TraceableAgency.Dist A)
    {E G : MarkedTerminalExperiment O (supportSubtype r)}
    (hsame : SameMarkedTerminalLaw r.restrictToSupport E G) :
    SameMarkedTerminalLaw r
      (supportExtendMarkedExperiment r E)
      (supportExtendMarkedExperiment r G) := by
  intro phi
  rw [markedTerminalIntegral_supportExtend,
    markedTerminalIntegral_supportExtend]
  exact hsame
    (fun op ↦ phi (op.1, supportPushforwardPosterior r op.2))

/-! ## Quotient map and affinity -/

/-- Extend a marked terminal law from the full-support face to the ambient
boundary prior. -/
noncomputable def supportExtendMarkedMixtureMap
    (r : TraceableAgency.Dist A) :
    MarkedTerminalMixtureSpace
        (O := O) (A := supportSubtype r) r.restrictToSupport →
      MarkedTerminalMixtureSpace (O := O) (A := A) r :=
  Quotient.map (supportExtendMarkedExperiment r)
    (fun {_ _} hsame ↦ sameMarkedTerminalLaw_supportExtend r hsame)

@[simp]
theorem supportExtendMarkedMixtureMap_mk
    (r : TraceableAgency.Dist A)
    (E : MarkedTerminalExperiment O (supportSubtype r)) :
    supportExtendMarkedMixtureMap r
        (⟦E⟧ : MarkedTerminalMixtureSpace
          (O := O) (A := supportSubtype r) r.restrictToSupport) =
      (⟦supportExtendMarkedExperiment r E⟧ :
        MarkedTerminalMixtureSpace (O := O) (A := A) r) := by
  rfl

/-- Extending a public mixture and publicly mixing the extensions give the
same ambient marked terminal law. -/
theorem sameMarkedTerminalLaw_supportExtend_publicMix
    (r : TraceableAgency.Dist A)
    (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (E G : MarkedTerminalExperiment O (supportSubtype r)) :
    SameMarkedTerminalLaw r
      (supportExtendMarkedExperiment r
        (markedPublicMixExperiment t ht0 ht1 E G))
      (markedPublicMixExperiment t ht0 ht1
        (supportExtendMarkedExperiment r E)
        (supportExtendMarkedExperiment r G)) := by
  intro phi
  rw [markedTerminalIntegral_supportExtend,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_publicMix,
    markedTerminalIntegral_supportExtend,
    markedTerminalIntegral_supportExtend]

/-- The support-extension quotient map commutes with the abstract public
mixture operation. -/
theorem supportExtendMarkedMixtureMap_affine
    (r : TraceableAgency.Dist A)
    (t : Set.Ioo (0 : ℝ) 1)
    (x y : MarkedTerminalMixtureSpace
      (O := O) (A := supportSubtype r) r.restrictToSupport) :
    supportExtendMarkedMixtureMap r
        ((markedTerminalAbstractConvexMixtureSpace r.restrictToSupport).mix
          t x y) =
      (markedTerminalAbstractConvexMixtureSpace r).mix t
        (supportExtendMarkedMixtureMap r x)
        (supportExtendMarkedMixtureMap r y) := by
  induction x using Quotient.inductionOn with
  | _ E =>
    induction y using Quotient.inductionOn with
    | _ G =>
      apply Quotient.sound
      exact sameMarkedTerminalLaw_supportExtend_publicMix
        r t.1 t.2.1 t.2.2 E G

/-! ## Exact boundary-order transport -/

/-- Pair comparison on the full-support face is exactly the ambient boundary
comparison of the support-extended experiments. -/
theorem markedPairWeak_supportExtend_iff
    (F : FixedPayoffPrefFamily O) (h : TraceTemperedAxioms F)
    (r : TraceableAgency.Dist A)
    (E G : MarkedTerminalExperiment O (supportSubtype r)) :
    MarkedPairWeak F r.restrictToSupport E r.restrictToSupport G ↔
      MarkedPairWeak F r (supportExtendMarkedExperiment r E) r
        (supportExtendMarkedExperiment r G) := by
  classical
  letI : Fintype E.RecordType := E.recordFintype
  letI : DecidableEq E.RecordType := E.recordDecEq
  letI : Nonempty E.RecordType := E.recordNonempty
  letI : Fintype G.RecordType := G.recordFintype
  letI : DecidableEq G.RecordType := G.recordDecEq
  letI : Nonempty G.RecordType := G.recordNonempty
  change pairWeak F r.restrictToSupport E.K r.restrictToSupport G.K ↔
    pairWeak F r (supportExtendChannel r E.K) r
      (supportExtendChannel r G.K)
  symm
  calc
    pairWeak F r (supportExtendChannel r E.K) r
        (supportExtendChannel r G.K) ↔
      pairWeak F r.restrictToSupport
          (Channel.restrictToSupport (supportExtendChannel r E.K) r)
        r.restrictToSupport
          (Channel.restrictToSupport (supportExtendChannel r G.K) r) :=
      pairWeak_iff_supportRestriction F h r
        (supportExtendChannel r E.K) r (supportExtendChannel r G.K)
    _ ↔ pairWeak F r.restrictToSupport E.K r.restrictToSupport G.K := by
      rw [restrictToSupport_supportExtendChannel,
        restrictToSupport_supportExtendChannel]

end TraceableAgency.Theorem1
