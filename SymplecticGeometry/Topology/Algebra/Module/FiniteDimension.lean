/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
import SymplecticGeometry.LinearAlgebra.FiniteDimensional.Submodule

/-!
# Continuous linear maps on finite-dimensional spaces

For a basis `b` of a finite-dimensional topological vector space `E` over a complete nontrivially
normed field `𝕜`, the coordinate functionals `b.coord i` are continuous, and every continuous
linear map `f : E →L[𝕜] F` is the finite sum `∑ i, b.coord i • f (b i)` of rank-one maps. This
is the continuous form of `Module.Basis.sum_repr`, beside Mathlib's `Module.Basis.constrL`.

A subspace `S` of a finite-dimensional space `E` has a complement that is the image of an
injective continuous linear map out of any finite-dimensional Hausdorff space `F` with
`dim F + dim S = dim E`: an injective linear map onto a complement of `S`
(`Submodule.exists_linearMap_injective_range_eq`) is continuous.

## Main results

* `Module.Basis.sum_coord_smulRight`: `f = ∑ i, (b.coord i).smulRight (f (b i))`.
* `Submodule.exists_continuousLinearMap_injective_isCompl_range`: an injective continuous linear
  map `F →L[𝕜] E` whose range is a complement of `S`, when `dim F + dim S = dim E`.
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

open Module

namespace Submodule

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousSMul 𝕜 F] [T2Space F] [FiniteDimensional 𝕜 F]

/-- A subspace `S` of a finite-dimensional space `E` has a complement that is the range of an
injective continuous linear map `L : F →L[𝕜] E`, for any finite-dimensional Hausdorff space `F`
with `dim F + dim S = dim E`. -/
theorem exists_continuousLinearMap_injective_isCompl_range (S : Submodule 𝕜 E)
    (h : finrank 𝕜 F + finrank 𝕜 S = finrank 𝕜 E) :
    ∃ L : F →L[𝕜] E, Function.Injective L ∧ IsCompl S (LinearMap.range (L : F →ₗ[𝕜] E)) := by
  obtain ⟨C, hC⟩ := S.exists_isCompl
  have hd : finrank 𝕜 F = finrank 𝕜 C := by
    have := finrank_add_eq_of_isCompl hC
    omega
  obtain ⟨L, hL, hr⟩ := C.exists_linearMap_injective_range_eq hd
  exact ⟨LinearMap.toContinuousLinearMap L, by simpa using hL, by
    rwa [LinearMap.coe_toContinuousLinearMap, hr]⟩

end Submodule

end
