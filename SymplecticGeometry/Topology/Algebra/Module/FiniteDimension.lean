/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Continuous linear maps on a space with a finite basis

For a basis `b` of a finite-dimensional topological vector space `E` over a complete nontrivially
normed field `𝕜`, the coordinate functionals `b.coord i` are continuous, and every continuous
linear map `f : E →L[𝕜] F` is the finite sum `∑ i, b.coord i • f (b i)` of rank-one maps. This
is the continuous form of `Module.Basis.sum_repr`, beside Mathlib's `Module.Basis.constrL`.

## Main results

* `Module.Basis.sum_coord_smulRight`: `f = ∑ i, (b.coord i).smulRight (f (b i))`.
-/

public section

namespace Module.Basis

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [T2Space E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] [Fintype ι]

/-- A continuous linear map on a space with a finite basis `b` is the sum over `i` of the
rank-one maps `v ↦ b.coord i v • f (b i)`. -/
theorem sum_coord_smulRight (b : Basis ι 𝕜 E) (f : E →L[𝕜] F) :
    ∑ i, (LinearMap.toContinuousLinearMap (b.coord i)).smulRight (f (b i)) = f := by
  ext v
  simp only [FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.smulRight_apply,
    LinearMap.coe_toContinuousLinearMap', coord_apply]
  simp_rw [← map_smul, ← map_sum, b.sum_repr]

end Module.Basis

end
