/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TraceableAgency.Theorem1.NormalizedMarked

/-!
# Affine values of marked-law directions

An equality between positive multiples of differences of marked terminal laws
implies the same equality between differences of any affine marked-law value.
Crossed public mixtures prove this directly, without extending the value to an
ambient space of signed measures.  In particular, the result applies to the
material-normalized marked value before any identification with information.
-/

namespace TraceableAgency.Theorem1

open TraceableAgency

universe u

variable {O A : Type u}
variable [Fintype O] [DecidableEq O]
variable [Fintype A] [DecidableEq A] [Nonempty A]

/-- Equal positively scaled marked-law differences have equal positively
scaled affine-value differences.  The only numerical hypotheses are affinity
under a public coin and dependence on the marked terminal law. -/
theorem markedAffineValue_scaled_difference
    (q : TraceableAgency.Dist A)
    (V : MarkedTerminalExperiment O A → ℝ)
    (hlaw : ∀ E G, SameMarkedTerminalLaw q E G → V E = V G)
    (haff : ∀ (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
        (E G : MarkedTerminalExperiment O A),
      V (markedPublicMixExperiment t ht0 ht1 E G) =
        t * V E + (1 - t) * V G)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (E E' G G' : MarkedTerminalExperiment O A)
    (hdir : ∀ phi : O × TraceableAgency.Dist A → ℝ,
      c * (markedTerminalIntegral q E phi - markedTerminalIntegral q E' phi) =
        d * (markedTerminalIntegral q G phi - markedTerminalIntegral q G' phi)) :
    c * (V E - V E') = d * (V G - V G') := by
  have hsum : 0 < c + d := add_pos hc hd
  have hsumne : c + d ≠ 0 := ne_of_gt hsum
  have ht0 : 0 < c / (c + d) := div_pos hc hsum
  have ht1 : c / (c + d) < 1 := (div_lt_one hsum).2 (by linarith)
  have hcomp : 1 - c / (c + d) = d / (c + d) := by
    field_simp
    ring
  have hsame : SameMarkedTerminalLaw q
      (markedPublicMixExperiment (c / (c + d)) ht0 ht1 E G')
      (markedPublicMixExperiment (c / (c + d)) ht0 ht1 E' G) := by
    intro phi
    rw [markedTerminalIntegral_publicMix, markedTerminalIntegral_publicMix, hcomp]
    have hphi := hdir phi
    field_simp
    nlinarith
  have hvalue := hlaw _ _ hsame
  rw [haff, haff, hcomp] at hvalue
  field_simp at hvalue
  nlinarith

/-- The material-normalized marked value respects positive scaling of
differences of marked laws.  No entropy or trace-scale formula is used. -/
theorem normalizedMarkedUtility_scaled_difference
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d)
    (E E' G G' : MarkedTerminalExperiment O A)
    (hdir : ∀ phi : O × TraceableAgency.Dist A → ℝ,
      c * (markedTerminalIntegral q E phi - markedTerminalIntegral q E' phi) =
        d * (markedTerminalIntegral q G phi - markedTerminalIntegral q G' phi)) :
    c * (normalizedMarkedUtility F h q hq E -
        normalizedMarkedUtility F h q hq E') =
      d * (normalizedMarkedUtility F h q hq G -
        normalizedMarkedUtility F h q hq G') := by
  exact markedAffineValue_scaled_difference q
    (normalizedMarkedUtility F h q hq)
    (normalizedMarkedUtility_respects_sameMarkedTerminalLaw F h q hq)
    (normalizedMarkedUtility_publicMix F h q hq)
    c d hc hd E E' G G' hdir

/-- The unscaled version is useful for changing a background while retaining
the same marked-law difference on the distinguished branch. -/
theorem normalizedMarkedUtility_difference_of_integral_difference
    (F : FixedPayoffPrefFamily O) {traceAnchor : O}
    (h : TraceTemperedBridgeAxioms F traceAnchor)
    (q : TraceableAgency.Dist A) (hq : q.FullSupport)
    (E E' G G' : MarkedTerminalExperiment O A)
    (hdir : ∀ phi : O × TraceableAgency.Dist A → ℝ,
      markedTerminalIntegral q E phi - markedTerminalIntegral q E' phi =
        markedTerminalIntegral q G phi - markedTerminalIntegral q G' phi) :
    normalizedMarkedUtility F h q hq E -
        normalizedMarkedUtility F h q hq E' =
      normalizedMarkedUtility F h q hq G -
        normalizedMarkedUtility F h q hq G' := by
  simpa using normalizedMarkedUtility_scaled_difference F h q hq
    1 1 (by norm_num) (by norm_num) E E' G G' (by simpa using hdir)

end TraceableAgency.Theorem1
