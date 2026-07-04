/-
Copyright (c) 2026 Daniele Condorelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniele Condorelli
-/
import TraceableAgency.External.PreUniversalGrouping

/-!
# Pre-Universal Block-Reveal Bridge

This file isolates the exact pre-universal ingredients needed to derive the TeX
grouping recursion `(GR)` at the face-scale layer.  It does not import or use
the downstream Faddeev/entropy-reduction theorem packages.
-/

namespace TraceableAgency

universe u

/--
Branch/chain assembly for appending full revelation after the block-reveal
channel over a `sigmaDist` partition.

This is strictly earlier than `(GR)`: it still contains the actual selected
value of the block-reveal channel.  Combining it with
`FinitePreUniversalBlockRevealValueFor` replaces that value by `H(p)`.
-/
structure FinitePreUniversalBlockRevealChainRuleFor.{v}
    {F : PrefFamily.{v}}
    (hfaces : CoherentRelabelingFaceScalesStructure F)
    (hprod : FiniteProductQuasiAdditivityForFaceScales hfaces) : Prop where
  block_reveal_chain :
    ∀ (hax : TraceAxioms F)
      {K : Type v} [Fintype K] [DecidableEq K] [Nonempty K]
      (Act : K → Type v)
      [∀ k, Fintype (Act k)] [∀ k, DecidableEq (Act k)]
      [∀ k, Nonempty (Act k)]
      [Nonempty ((k : K) × Act k)]
      (p : Dist K) (f : ∀ k, Dist (Act k))
      (_hp : p.FullSupport)
      (_hf : ∀ k, (f k).FullSupport)
      (_hsigma : (sigmaDist p f).FullSupport)
      (_hKnd : ¬ Subsingleton K)
      (_hAnd : ∀ k, ¬ Subsingleton (Act k)),
      fullRevelationValueForFaceScales hfaces (sigmaDist p f) =
        hfaces.branch_result.branch_agg.value_rep.V (sigmaDist p f)
          (experimentOfChannel
            (preUniversalCoarseRevealChannel (K := K) Act)) +
        productScaleZForFaceScales hfaces hprod hax (sigmaDist p f) *
          ∑ k, p k *
            (fullRevelationValueForFaceScales hfaces (f k) /
              productScaleZForFaceScales hfaces hprod hax (f k))
  reference_Z_eq_one :
    ∀ (hax : TraceAxioms F),
      productScaleZForFaceScales hfaces hprod hax
        universalScaleReferencePrior = 1

/--
Derive the TeX grouping recursion `(GR)` from the pre-universal block-reveal
value identity and the block-reveal branch/chain assembly.
-/
theorem finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hblock : FinitePreUniversalBlockRevealValueFor hfaces)
    (hchain : FinitePreUniversalBlockRevealChainRuleFor hfaces hprod) :
    FinitePreUniversalGroupingGRFor hfaces hprod where
  grouping_GR := by
    intro hax K _ _ _ Act _ _ _ _ p f hp hf hsigma hKnd hAnd
    rw [hchain.block_reveal_chain hax Act p f hp hf hsigma hKnd hAnd]
    rw [hblock.block_reveal_value_eq_fullRevelationValue
      hax Act p f hp hf hsigma]
  reference_Z_eq_one := hchain.reference_Z_eq_one

/--
The existing weight recursion `(W)` follows from the earlier block-reveal and
chain obligations, together with the already-proved POS package.
-/
theorem finitePreUniversalGroupingWeightRecursion_of_blockReveal
    {F : PrefFamily.{u}}
    {hfaces : CoherentRelabelingFaceScalesStructure F}
    {hprod : FiniteProductQuasiAdditivityForFaceScales hfaces}
    (hblock : FinitePreUniversalBlockRevealValueFor hfaces)
    (hchain : FinitePreUniversalBlockRevealChainRuleFor hfaces hprod)
    (hpos : FiniteProductScaleZPositiveAssumptionsFor hfaces hprod) :
    FinitePreUniversalGroupingWeightRecursionAssumptionsFor hfaces hprod :=
  finitePreUniversalGroupingWeightRecursion_of_GR
    (finitePreUniversalGroupingGR_of_blockReveal_chain_neutrality
      hblock hchain)
    hpos

end TraceableAgency
