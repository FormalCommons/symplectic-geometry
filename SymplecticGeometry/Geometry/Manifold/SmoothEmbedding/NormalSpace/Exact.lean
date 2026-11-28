/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.Basic
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic

/-!
# The dimension of a normal space

For a smooth embedding `f : M → N` and a point `x` of `M`, the differential
`T_x M → T_{f x} N` and Tau Ceti's normal class map `T_{f x} N → ν_x` form the short exact
sequence `0 → T_x M → T_{f x} N → ν_x → 0`: this is Tau Ceti's
`Manifold.IsImmersion.exact_mfderiv_normalClass`, with `Manifold.IsImmersion.mfderiv_injective`
and `Manifold.IsImmersion.normalClass_surjective`, applied to `f.isImmersion`. This file gives the
dimension of the normal spaces in the form that Tau Ceti's normal bundle charts use.

## Main results

* `TauCeti.SmoothEmbedding.finrank_normalSpace_eq`: under the dimension condition
  `dim P = dim F - dim E` of Tau Ceti's normal bundle charts, the normal spaces have the dimension
  of the model fibre `P`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}

/-- If a space `P` has dimension `dim F - dim E`, as the model fibre of Tau Ceti's normal bundle
charts does, then each normal space of a smooth embedding has the dimension of `P`. -/
theorem finrank_normalSpace_eq {P : Type*} [AddCommGroup P] [Module 𝕜 P] [FiniteDimensional 𝕜 F]
    (f : SmoothEmbedding I J n M N) (hn : n ≠ 0)
    (hdim : Module.finrank 𝕜 P = Module.finrank 𝕜 F - Module.finrank 𝕜 E) (x : M) :
    Module.finrank 𝕜 (f.isImmersion.NormalSpace x hn) = Module.finrank 𝕜 P := by
  rw [f.isImmersion.finrank_normalSpace x hn, hdim, TauCeti.finrank_tangentSpace,
    TauCeti.finrank_tangentSpace]

end TauCeti.SmoothEmbedding

end
