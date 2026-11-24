/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.PullbackGroupoid
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.Basic

/-!
# Immersions, smooth embeddings and tangent images for a pulled-back atlas

Let `e : M' ≃ₜ M` be a homeomorphism onto a charted space `M`, and give `M'` the atlas
`e.pullbackChartedSpace` carried over from `M`. Then `e` is a diffeomorphism
(`Homeomorph.pullbackDiffeomorph`), so precomposing a map `f : M → N` with `e` keeps it an
immersion or a smooth embedding, and does not change the range of its differential.

These lemmas state this directly for `e` and the pulled-back atlas, without naming the
diffeomorphism, in the way Tau Ceti's `Homeomorph.contMDiffAt_comp_pullbackChartedSpace_iff`
does for smoothness. They are Tau Ceti's `TauCeti.isImmersion_comp_diffeomorph`,
`TauCeti.isSmoothEmbedding_comp_diffeomorph` and `Diffeomorph.range_mfderiv_comp_diffeomorph`
applied to `e.pullbackDiffeomorph`. Tau Ceti repeats the same steps inline, for instance in the
private diffeomorphisms of its `Geometry/Symplectic/Hamiltonian/Reduction/ReducedSpace.lean`.

## Main results

* `Homeomorph.isImmersion_comp_pullbackChartedSpace`: `f ∘ e` is an immersion when `f` is.
* `Homeomorph.isSmoothEmbedding_comp_pullbackChartedSpace`: `f ∘ e` is a smooth embedding when
  `f` is.
* `Homeomorph.range_mfderiv_comp_pullbackChartedSpace`: the differential of `f ∘ e` at `x` has
  the same range as that of `f` at `e x`.

## References

* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 1, for immersions and
  embeddings and their behaviour under composition.
-/

public section

open Manifold
open scoped Manifold ContDiff

namespace Homeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H : Type*} [TopologicalSpace H] {G : Type*} [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*} [TopologicalSpace M']
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : ℕ∞ω} {f : M → N}

/-- For the atlas on `M'` pulled back along a homeomorphism `e : M' ≃ₜ M` from a `C^n` manifold
`M`, precomposing a `C^n` immersion `f : M → N` with `e` gives a `C^n` immersion. -/
theorem isImmersion_comp_pullbackChartedSpace (e : M' ≃ₜ M) [IsManifold I n M]
    (h : IsImmersion I J n f) :
    letI := e.pullbackChartedSpace (H := H)
    IsImmersion I J n (f ∘ e) := by
  let := e.pullbackChartedSpace (H := H)
  have := e.pullback_isManifold I n
  simpa only [coe_pullbackDiffeomorph] using
    TauCeti.isImmersion_comp_diffeomorph (e.pullbackDiffeomorph I n) h

/-- For the atlas on `M'` pulled back along a homeomorphism `e : M' ≃ₜ M` from a `C^n` manifold
`M`, precomposing a `C^n` smooth embedding `f : M → N` with `e` gives a `C^n` smooth
embedding. -/
theorem isSmoothEmbedding_comp_pullbackChartedSpace (e : M' ≃ₜ M) [IsManifold I n M]
    (h : IsSmoothEmbedding I J n f) :
    letI := e.pullbackChartedSpace (H := H)
    IsSmoothEmbedding I J n (f ∘ e) := by
  let := e.pullbackChartedSpace (H := H)
  have := e.pullback_isManifold I n
  simpa only [coe_pullbackDiffeomorph] using
    TauCeti.isSmoothEmbedding_comp_diffeomorph (e.pullbackDiffeomorph I n) h

/-- For the atlas on `M'` pulled back along a homeomorphism `e : M' ≃ₜ M`, the differential of
`f ∘ e` at `x` has the same range as the differential of `f` at `e x`, for any map `f : M → N`. -/
theorem range_mfderiv_comp_pullbackChartedSpace (e : M' ≃ₜ M) (f : M → N) (x : M') :
    letI := e.pullbackChartedSpace (H := H)
    LinearMap.range (mfderiv I J (f ∘ e) x).toLinearMap =
      LinearMap.range (mfderiv I J f (e x)).toLinearMap := by
  let := e.pullbackChartedSpace (H := H)
  have h := (e.pullbackDiffeomorph I 1).range_mfderiv_comp_diffeomorph (K := J) one_ne_zero f x
  rwa [coe_pullbackDiffeomorph] at h

end Homeomorph

end
