/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Basic

/-!
# The exact sequence of a normal space

For a smooth embedding `f : M → N` and a point `x` of `M`, the differential
`T_x M → T_{f x} N` and Tau Ceti's normal class map `T_{f x} N → ν_x` form an exact sequence.
With the injectivity of the differential (Mathlib's
`Manifold.IsImmersion.mfderiv_injective`) and the surjectivity of the normal class map
(`TauCeti.SmoothEmbedding.normalClass_surjective`), it is the short exact sequence
`0 → T_x M → T_{f x} N → ν_x → 0`.

## Main results

* `TauCeti.SmoothEmbedding.exact_mfderiv_normalClass`: the differential and the normal class map
  are exact, in the form of `Function.Exact`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F H G M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] [TopologicalSpace G] {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace G N] {n : ℕ∞ω}

/-- The differential of a smooth embedding at `x` and its normal class map form an exact
sequence `T_x M → T_{f x} N → ν_x`. -/
theorem exact_mfderiv_normalClass (f : SmoothEmbedding I J n M N) (x : M) (hn : n ≠ 0) :
    Function.Exact (mfderiv I J f x).toLinearMap (f.normalClass x hn) :=
  LinearMap.exact_iff.2 (f.normalClass_ker x hn)

end TauCeti.SmoothEmbedding

end
