/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.Immersion.Basic

/-!
# Right slices of a product are smooth embeddings

If the preferred chart of `N` at `c` sends `c` to `0`, the slice `x ↦ (c, x)` of `N × M` is a
`C^n` smooth embedding. This is the companion of Tau Ceti's
`TauCeti.isSmoothEmbedding_prodMkLeft_of_extChartAt_eq_zero`, for the slice `x ↦ (x, c)`, and it
combines Tau Ceti's immersion `TauCeti.isImmersion_prodMkRight_of_extChartAt_eq_zero` with
Mathlib's topological embedding `isEmbedding_prodMkRight`.

## Main results

* `TauCeti.isSmoothEmbedding_prodMkRight_of_extChartAt_eq_zero`: the slice `x ↦ (c, x)` of a
  product is a smooth embedding when the chart at `c` sends `c` to `0`.
-/

public section

open scoped Manifold

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 E' G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  {n : WithTop ℕ∞}

/-- **Slices of a product.** If the preferred chart of `N` at `c` sends `c` to `0`, then the slice
`x ↦ (c, x)` of the product `N × M` is a `C^n` smooth embedding. -/
theorem isSmoothEmbedding_prodMkRight_of_extChartAt_eq_zero [IsManifold I n M] [IsManifold J n N]
    {c : N} (hc : extChartAt J c c = 0) :
    Manifold.IsSmoothEmbedding I (J.prod I) n (Prod.mk c : M → N × M) :=
  ⟨isImmersion_prodMkRight_of_extChartAt_eq_zero hc, isEmbedding_prodMkRight c⟩

end TauCeti

end
