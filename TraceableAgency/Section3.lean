import TraceableAgency.Section3.Uniqueness
import TraceableAgency.Section3.Signs.Converse
import TraceableAgency.Section3.Independence
import TraceableAgency.Section3.Independence.Gini

/-!
# Section 3 of the v11 paper

This entry point adds uniqueness, the sign trichotomy, and independence of
A1--A8 to the material-first representation theorem. It also verifies the
three named counterexample families in the paper's discussion: conditional
record-noise costs, Gini posterior reduction, and information satiation.

The original representation proof and its public entry point are preserved.
See `Certificate/SECTION3_VERIFICATION.md` for the claim map and reproduction.
-/
