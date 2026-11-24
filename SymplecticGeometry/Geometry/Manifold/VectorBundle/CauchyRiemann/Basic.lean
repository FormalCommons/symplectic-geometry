/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic

/-!
# The kernel of the `(0,1)`-projection

For an almost complex structure `j` on `M` and a complex vector bundle `V`, Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart` sends a `V`-valued one-form `η` at `x` to
`v ↦ ½ (η v + i • η (j v))`. This file adds that its kernel consists of the one-forms that are
complex linear for `j`: `η (j v) = i • η v` for every `v`
(`TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_zero_iff`). This complements Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_self_iff`, which describes its image.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_zero_iff`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  {j : SmoothAlmostComplexStructure I M}

/-- The `(0,1)`-part of a `V`-valued one-form `η` vanishes exactly when `η` is complex linear for
`j`: `η (j v) = i • η v` for every tangent vector `v`. -/
theorem zeroOnePart_eq_zero_iff {x : M} {η : TangentSpace I x →L[ℝ] V x} :
    j.zeroOnePart η = 0 ↔ ∀ v, η (j x v) = Complex.I • η v := by
  rw [← ContinuousLinearMap.coe_inj, toLinearMap_zeroOnePart, ContinuousLinearMap.toLinearMap_zero,
    ← isComplexLinear_iff_complexAntilinearPart_eq_zero Complex.toLinearMap_I_comp_toLinearMap_I]
  exact ⟨fun h v ↦ h.apply v, fun h ↦ isComplexLinear_of_apply h⟩

end TauCeti.SmoothAlmostComplexStructure
