# Vendored finite Shannon characterization

These Lean files are adapted from Samuel Schlesinger's
[`shannon-1948-formalization`](https://github.com/SamuelSchlesinger/shannon-1948-formalization)
(`shannon-entropy` on Reservoir), released under the MIT licence reproduced in
`LICENSE`.

The local adaptation:

- updates imports and a few proof scripts for this repository's Lean/mathlib
  version;
- restricts the final continuity use to full-support probability vectors,
  which is the only case needed by the rational approximation argument;
- is used only as a generic finite-mathematics layer by
  `TraceableAgency.External.GenericFaddeev`.

The characterization proof remains ordinary Lean theorem code: it introduces
no axioms, opaque constants, or project-specific conventions.
