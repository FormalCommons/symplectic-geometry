/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Immersion

/-!
# The derivative of an immersion in its normal-form charts

Let `f : M → N` be a `C^n` immersion at `x`, with `n ≠ 0`. Read in its normal-form charts `φ` on
`M` and `ψ` on `N`, `f` is the inclusion `u ↦ L (u, 0)` of `E` into `E''`, through a linear
equivalence `L : E × F ≃ E''`. Differentiating this identity gives `dψ ∘ df = L (·, 0) ∘ dφ` at
every point of the source of `φ`.

The proof follows Tau Ceti's `Manifold.IsSubmersionAtOfComplement.mfderiv_extend_comp_mfderiv`,
in `TauCeti/Geometry/Manifold/Submersion/Basic.lean`, its analogue for submersions.

## Main results

* `Manifold.IsImmersionAtOfComplement.mfderiv_extend_comp_mfderiv`: the derivative of an
  immersion in its normal-form charts.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 4 (the rank theorem).
-/

public section

open Set Function Filter Manifold
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 E'' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : M → N} {x : M}

namespace Manifold.IsImmersionAtOfComplement

variable (h : IsImmersionAtOfComplement F I J n f x)
include h

/-- **The derivative of an immersion in its normal-form charts.** On the source of the domain
chart `φ`, the derivative of `f` followed by the derivative of the codomain chart `ψ` is the
derivative of `φ` followed by the inclusion `u ↦ L (u, 0)`, where `L = h.equiv`. -/
theorem mfderiv_extend_comp_mfderiv (hn : n ≠ 0) {y : M} (hy : y ∈ h.domChart.source) :
    (mfderiv J 𝓘(𝕜, E'') (h.codChart.extend J) (f y)).comp (mfderiv I J f y) =
      ((h.equiv : E × F →L[𝕜] E'').comp (ContinuousLinearMap.inl 𝕜 E F)).comp
        (mfderiv I 𝓘(𝕜, E) (h.domChart.extend I) y) := by
  have hfy : f y ∈ h.codChart.source := h.source_subset_preimage_source hy
  have hψ : MDifferentiableAt J 𝓘(𝕜, E'') (h.codChart.extend J) (f y) :=
    (h.codChart.contMDiffAt_extend h.codChart_mem_maximalAtlas hfy).mdifferentiableAt hn
  have hφ : MDifferentiableAt I 𝓘(𝕜, E) (h.domChart.extend I) y :=
    (h.domChart.contMDiffAt_extend h.domChart_mem_maximalAtlas hy).mdifferentiableAt hn
  have hf : MDifferentiableAt I J f y :=
    ((h.contMDiffOn y hy).contMDiffAt (h.domChart.open_source.mem_nhds hy)).mdifferentiableAt hn
  -- On the source of `φ`, `ψ ∘ f` is `L (·, 0) ∘ φ`.
  have heq : h.codChart.extend J ∘ f =ᶠ[𝓝 y]
      ((h.equiv : E × F →L[𝕜] E'').comp (ContinuousLinearMap.inl 𝕜 E F)) ∘
        h.domChart.extend I := by
    refine eventually_of_mem (h.domChart.open_source.mem_nhds hy) fun z hz ↦ ?_
    have hz' : z ∈ (h.domChart.extend I).source := by rwa [OpenPartialHomeomorph.extend_source]
    have := h.writtenInCharts ((h.domChart.extend I).map_source hz')
    simpa only [comp_apply, (h.domChart.extend I).left_inv hz', ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearEquiv.coe_coe] using this
  exact hasMFDerivAt_unique (hψ.hasMFDerivAt.comp y hf.hasMFDerivAt)
    ((ContinuousLinearMap.hasMFDerivAt _).comp y hφ.hasMFDerivAt |>.congr_of_eventuallyEq_abuse
      heq)

end Manifold.IsImmersionAtOfComplement
