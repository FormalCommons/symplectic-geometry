/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
import Mathlib.Geometry.Manifold.Notation
import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic

/-!
# The kernel of the `(0,1)`-projection

For an almost complex structure `j` on `M` and a complex vector bundle `V`, Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart` sends a `V`-valued one-form `η` at `x` to
`v ↦ ½ (η v + i • η (j v))`. This file adds that its kernel consists of the one-forms that are
complex linear for `j`: `η (j v) = i • η v` for every `v`
(`TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_zero_iff`). This complements Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_self_iff`, which describes its image.

For a complex linear real Cauchy–Riemann operator `D` on `V` and a section `σ` with `σ x ≠ 0` and
`D σ x = 0`, a function `f : M → ℂ` that is real differentiable at `x` has `D (f • σ) x = 0`
exactly when `f` is pseudoholomorphic at `x` from `j` to the standard structure of `ℂ`
(`TauCeti.IsRealCauchyRiemannOperator.apply_smul_eq_zero_iff_isPseudoholomorphicAt`). Tau Ceti's
`TauCeti.IsRealCauchyRiemannOperator.apply_smul_eq_zero_iff` proves this when `j` is the
structure of a complex manifold, with complex differentiability as the conclusion; the proof
here follows it.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_zero_iff`.
* `TauCeti.IsRealCauchyRiemannOperator.apply_smul_eq_zero_iff_isPseudoholomorphicAt`.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
-/

public section

open Bundle
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

namespace TauCeti.IsRealCauchyRiemannOperator

open SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]
  [VectorBundle ℂ F V] [VectorBundle ℝ F V]
  {j : SmoothAlmostComplexStructure I M}
  {D : (Π x : M, V x) → Π x : M, TangentSpace I x →L[ℝ] V x}

/-- Let `D` be a complex linear real Cauchy–Riemann operator for `j`, and `σ` a section that is
differentiable at `x`, nonzero there, and with `D σ x = 0`. For `f : M → ℂ` real differentiable
at `x`, `D (f • σ) x = 0` exactly when `f` is pseudoholomorphic at `x` from `j` to the standard
complex structure of `ℂ`. -/
theorem apply_smul_eq_zero_iff_isPseudoholomorphicAt
    (hD : IsRealCauchyRiemannOperator F j D) (hDℂ : IsComplexLinearOperator F D)
    {σ : Π x : M, V x} {f : M → ℂ} {x : M}
    (hσ : MDifferentiableAt I (I.prod 𝓘(ℝ, F)) (T% σ) x) (hσ0 : σ x ≠ 0) (hDσ : D σ x = 0)
    (hf : MDifferentiableAt I 𝓘(ℝ, ℂ) f x) :
    D (f • σ) x = 0 ↔ IsPseudoholomorphicAt j (ofComplexManifold ℂ ℂ) f x := by
  rw [hD.leibniz_complex hDℂ hσ hf, hDσ, smul_zero, zero_add,
    zeroOnePart_smulRight_eq_zero_iff _ hσ0,
    ← dbarFunction_eq_zero_iff_isPseudoholomorphicAt _ hf, dbarFunction_eq_zero_iff]
  simp only [smul_eq_mul]

end TauCeti.IsRealCauchyRiemannOperator

end
