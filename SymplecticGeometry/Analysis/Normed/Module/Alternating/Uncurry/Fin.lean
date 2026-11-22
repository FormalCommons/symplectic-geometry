/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin
public import SymplecticGeometry.Topology.Algebra.Module.FiniteDimension

/-!
# Expanding `alternatizeUncurryFin` in a basis

For a basis `b` of a finite-dimensional space `E`, a continuous linear map
`f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F` is `∑ i, b.coord i • f (b i)`
(`Module.Basis.sum_coord_smulRight`). Since Mathlib's
`ContinuousAlternatingMap.alternatizeUncurryFin` is linear, it follows that
`alternatizeUncurryFin f` is the sum of the alternatizations of the rank-one terms
`b.coord i • f (b i)`. This is how the symbol of the exterior derivative at a first-order term is
reduced to its symbol at a single covector.

## Main results

* `ContinuousAlternatingMap.alternatizeUncurryFin_eq_sum_coord_smulRight`: the expansion.
-/

public section

namespace ContinuousAlternatingMap

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [Fintype ι]

/-- For a basis `b`, `alternatizeUncurryFin f` is the sum over `i` of the alternatizations of
`b.coord i • f (b i)`, as `f = ∑ i, b.coord i • f (b i)`. -/
theorem alternatizeUncurryFin_eq_sum_coord_smulRight (b : Module.Basis ι 𝕜 E) {n : ℕ}
    (f : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) :
    alternatizeUncurryFin f = ∑ i, alternatizeUncurryFin
      ((LinearMap.toContinuousLinearMap (b.coord i)).smulRight (f (b i))) := by
  conv_lhs => rw [← b.sum_coord_smulRight f]
  rw [← alternatizeUncurryFinCLM_apply, _root_.map_sum]
  simp only [alternatizeUncurryFinCLM_apply]

end ContinuousAlternatingMap

end
