/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.Info.Entropy
import TraceableAgency.Basic.Channel

/-!
# Mutual Information

Mutual information I(A;O) = H(O) - Σ_a q(a) * H(P(·|a))
                          = H(q) - E[H(posterior)]

This is the information about the action A contained in the outcome O.
-/

namespace TraceableAgency

variable {A O : Type*} [Fintype A] [Fintype O]

/-- Mutual information I_{q,P}(A;O) using the noise form:
    I = H(outcome marginal) - Σ_a q(a) * H(P(·|a))

    This equals H(q) - E[H(posterior)] by standard identities. -/
noncomputable def mutualInfo (q : Dist A) (P : Channel A O) : ℝ :=
  H(Channel.outcomeMarginal P q) - ∑ a, q a * H(P a)

notation "I(" q ", " P ")" => mutualInfo q P

end TraceableAgency
