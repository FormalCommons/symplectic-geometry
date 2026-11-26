/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic
import SymplecticGeometry.Geometry.Manifold.ContMDiff.Indicator
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Injective
import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# Pushing a function forward along a smooth embedding

Let `Φ : N → M` be a smooth embedding and `χ` a function on `N`. Reading `χ` through the inverse
of `Φ` on its range, and extending by `0` off the range, gives the function
`(range Φ).indicator (χ ∘ invFunOn Φ univ)` on `M`. It takes the value `χ z` at `Φ z`, and
vanishes off the image of the support of `χ`.

When `N` is boundaryless and has the same finite dimension as `M`, `Φ` is a local
diffeomorphism (`TauCeti.SmoothEmbedding.isLocalDiffeomorph`), so its range is open and its
inverse is smooth there (`IsLocalDiffeomorphOn.contMDiffOn_invFunOn`). If moreover `χ` is
supported in a set `K` whose image `Φ '' K` is closed in `M`, the extension by zero is smooth
(`ContMDiffOn.contMDiff_indicator`). Unlike
`PartialDiffeomorph.contMDiff_indicator_comp_symm`, no compactness of the support is needed.

## Main results

* `TauCeti.SmoothEmbedding.indicator_range_comp_invFunOn_apply_self`: the value at `Φ z`.
* `TauCeti.SmoothEmbedding.support_indicator_range_comp_invFunOn_subset`: the support.
* `TauCeti.SmoothEmbedding.contMDiff_indicator_range_comp_invFunOn`: smoothness.
-/

public section

open Set Function
open scoped Manifold

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [RCLike 𝕜] {E E' H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N] [Nonempty N]
  {n : WithTop ℕ∞} (Φ : SmoothEmbedding J I n N M)

/-- The function `χ ∘ Φ⁻¹`, extended by `0` off the range of `Φ`, takes the value `χ z` at
`Φ z`. -/
theorem indicator_range_comp_invFunOn_apply_self {F : Type*} [Zero F] (χ : N → F) (z : N) :
    (range Φ).indicator (χ ∘ invFunOn Φ univ) (Φ z) = χ z := by
  rw [indicator_of_mem (mem_range_self z), comp_apply,
    Φ.isSmoothEmbedding.isEmbedding.injective.injOn.leftInvOn_invFunOn (mem_univ z)]

/-- The function `χ ∘ Φ⁻¹`, extended by `0` off the range of `Φ`, is supported in the image
under `Φ` of the support of `χ`. -/
theorem support_indicator_range_comp_invFunOn_subset {F : Type*} [Zero F] (χ : N → F) :
    support ((range Φ).indicator (χ ∘ invFunOn Φ univ)) ⊆ Φ '' support χ := by
  intro x hx
  obtain ⟨z, rfl⟩ : x ∈ range Φ := by
    by_contra h
    exact hx (indicator_of_notMem h _)
  rw [mem_support, indicator_range_comp_invFunOn_apply_self] at hx
  exact mem_image_of_mem _ hx

/-- Let `Φ : N → M` be a `C^n` embedding, `1 ≤ n`, of a boundaryless manifold into a manifold of
the same finite dimension. If `χ : N → F` is `C^n` and supported in a set `K` with `Φ '' K`
closed, then `χ ∘ Φ⁻¹`, extended by `0` off the range of `Φ`, is `C^n` on `M`. -/
theorem contMDiff_indicator_range_comp_invFunOn [FiniteDimensional 𝕜 E] [IsManifold J n N]
    [IsManifold I n M] [BoundarylessManifold J N]
    (hd : Module.finrank 𝕜 E' = Module.finrank 𝕜 E) (hn : 1 ≤ n)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {χ : N → F}
    (hχ : ContMDiff J 𝓘(𝕜, F) n χ) {K : Set N} (hK : IsClosed (Φ '' K))
    (hχK : support χ ⊆ K) :
    ContMDiff I 𝓘(𝕜, F) n ((range Φ).indicator (χ ∘ invFunOn Φ univ)) := by
  have hloc := Φ.isLocalDiffeomorph hd hn
  have hinj : InjOn Φ univ := Φ.isSmoothEmbedding.isEmbedding.injective.injOn
  have hinv := (hloc.isLocalDiffeomorphOn univ).contMDiffOn_invFunOn isOpen_univ hinj
  rw [image_univ] at hinv
  refine (hχ.comp_contMDiffOn hinv).contMDiff_indicator hloc.isOpen_range hK
    (image_subset_range _ _) ?_
  rintro _ ⟨z, rfl⟩ hz
  rw [comp_apply, hinj.leftInvOn_invFunOn (mem_univ z)]
  exact notMem_support.1 fun h ↦ hz (mem_image_of_mem _ (hχK h))

end TauCeti.SmoothEmbedding

end
