/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.Complex.Module.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic
public import SymplecticGeometry.Analysis.Normed.Operator.ComplexLinearPart
public import Mathlib.Topology.VectorBundle.Riemannian
import SymplecticGeometry.Geometry.Manifold.VectorBundle.CauchyRiemann.Basic

/-!
# The `(1,0)`-part of a one-form

For an almost complex structure `j` on `M` and a complex vector bundle `V`, Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart` sends a `V`-valued one-form `η` at `x` to its
`(0,1)`-part `v ↦ ½ (η v + i • η (j v))`, the complex-antilinear part of `η`. This file adds the
complementary `(1,0)`-part `v ↦ ½ (η v - i • η (j v))`
(`TauCeti.SmoothAlmostComplexStructure.oneZeroPart`), the complex-linear part of `η`
(`TauCeti.SmoothAlmostComplexStructure.toLinearMap_oneZeroPart`), and the decomposition
`η = η^{1,0} + η^{0,1}`
(`TauCeti.SmoothAlmostComplexStructure.oneZeroPart_add_zeroOnePart`), which follows from Tau
Ceti's `TauCeti.complexLinearPart_add_complexAntilinearPart`. The definition `oneZeroPart` and
the lemmas `oneZeroPart_apply` and `toLinearMap_oneZeroPart` are adapted from Tau Ceti's
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart`, `zeroOnePart_apply` and
`toLinearMap_zeroOnePart`, with the sign of the `i • η (j v)` term changed from `+` to `-`.

For a covariant derivative `D` on `V` and a section `s`, the one-form `η = D s x` gives
`∂ s(x) = j.oneZeroPart (D s x)` and `∂̄ s(x) = j.zeroOnePart (D s x)`, and the decomposition reads
`∂ s(x) + ∂̄ s(x) = D s(x)`. Nothing here depends on `D`, so the statements are about one-forms.

Both parts are also written as Tau Ceti's `TauCeti.complexLinearPart` and
`TauCeti.complexAntilinearPart` for the pointwise structures `j.almostComplexStructureAt x` and
`TauCeti.AlmostComplexStructure.ofComplexModule (V x)`, turned into continuous maps by
`LinearMap.toContinuousLinearMap`
(`TauCeti.SmoothAlmostComplexStructure.oneZeroPart_eq_toContinuousLinearMap_complexLinearPart`,
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_toContinuousLinearMap_complexAntilinearPart`).
For a Riemannian metric on `M` and normed fibres, the two parts are also the continuous
operators `TauCeti.complexLinearPartContinuousLinearMap` and
`TauCeti.complexAntilinearPartContinuousLinearMap` for `j.toEndomorphism x` and
`Complex.smulIEquiv (V x)`, evaluated at `η`
(`TauCeti.SmoothAlmostComplexStructure.oneZeroPart_eq_complexLinearPartContinuousLinearMap`,
`TauCeti.SmoothAlmostComplexStructure.zeroOnePart_eq_complexAntilinearPartContinuousLinearMap`),
which is how the hypotheses of the zero set results of
`SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ZeroSet` are stated.

## Main definitions

* `TauCeti.SmoothAlmostComplexStructure.oneZeroPart`: the `(1,0)`-part of a one-form.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.oneZeroPart_add_zeroOnePart`: `η^{1,0} + η^{0,1} = η`.
* `TauCeti.SmoothAlmostComplexStructure.zeroOnePart_oneZeroPart`: the `(1,0)`-part has no
  `(0,1)`-part.

## References

* [D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*][McDuffSalamon2012],
  Appendix C.1.
* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothAlmostComplexStructure

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℂ (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [∀ x, IsScalarTower ℝ ℂ (V x)] [∀ x, ContinuousSMul ℂ (V x)]

variable (j : SmoothAlmostComplexStructure I M) {x : M}

/-- The `(1,0)`-part `η^{1,0} v = ½ (η v - i • η (j v))` of a `V`-valued one-form `η`. -/
noncomputable def oneZeroPart (η : TangentSpace I x →L[ℝ] V x) : TangentSpace I x →L[ℝ] V x :=
  (2⁻¹ : ℝ) • (η - Complex.I • η.comp (j.toEndomorphism x))

theorem oneZeroPart_apply (η : TangentSpace I x →L[ℝ] V x) (v : TangentSpace I x) :
    j.oneZeroPart η v = (2⁻¹ : ℝ) • (η v - Complex.I • η (j x v)) :=
  (rfl)

/-- The `(1,0)`-part of a one-form is its complex-linear part `TauCeti.complexLinearPart` for `j`
and multiplication by `i`. -/
theorem toLinearMap_oneZeroPart (η : TangentSpace I x →L[ℝ] V x) :
    (j.oneZeroPart η).toLinearMap = complexLinearPart (j.toEndomorphism x).toLinearMap
      (DistribSMul.toLinearMap ℝ (V x) Complex.I) η.toLinearMap := by
  ext v
  simp [oneZeroPart_apply, complexLinearPart_apply]

/-- A one-form is the sum of its `(1,0)`-part and its `(0,1)`-part. -/
@[simp]
theorem oneZeroPart_add_zeroOnePart (η : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart η + j.zeroOnePart η = η := by
  rw [← ContinuousLinearMap.coe_inj, ContinuousLinearMap.toLinearMap_add, toLinearMap_oneZeroPart,
    toLinearMap_zeroOnePart, complexLinearPart_add_complexAntilinearPart]

/-- The `(1,0)`-part of a one-form is what remains after removing its `(0,1)`-part. -/
theorem oneZeroPart_eq_sub_zeroOnePart (η : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart η = η - j.zeroOnePart η :=
  eq_sub_of_add_eq (j.oneZeroPart_add_zeroOnePart η)

/-- The `(1,0)`-part of a one-form is complex linear for `j`. -/
theorem oneZeroPart_apply_almostComplexStructure (η : TangentSpace I x →L[ℝ] V x)
    (v : TangentSpace I x) :
    j.oneZeroPart η (j x v) = Complex.I • j.oneZeroPart η v := by
  simpa only [← toLinearMap_oneZeroPart, almostComplexStructureAt_toLinearMap,
    ContinuousLinearMap.coe_coe, DistribSMul.toLinearMap_apply] using
    (isComplexLinear_complexLinearPart (j.almostComplexStructureAt x).square_neg
      Complex.toLinearMap_I_comp_toLinearMap_I η.toLinearMap).apply v

/-- The `(1,0)`-part of a one-form has zero `(0,1)`-part. -/
@[simp]
theorem zeroOnePart_oneZeroPart (η : TangentSpace I x →L[ℝ] V x) :
    j.zeroOnePart (j.oneZeroPart η) = 0 :=
  zeroOnePart_eq_zero_iff.2 (j.oneZeroPart_apply_almostComplexStructure η)

/-- The `(0,1)`-part of a one-form has zero `(1,0)`-part. -/
@[simp]
theorem oneZeroPart_zeroOnePart (η : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart (j.zeroOnePart η) = 0 := by
  rw [oneZeroPart_eq_sub_zeroOnePart, zeroOnePart_zeroOnePart, sub_self]

/-- The `(1,0)`-part of the `(1,0)`-part of a one-form is its `(1,0)`-part. -/
@[simp]
theorem oneZeroPart_oneZeroPart (η : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart (j.oneZeroPart η) = j.oneZeroPart η := by
  rw [oneZeroPart_eq_sub_zeroOnePart (η := j.oneZeroPart η), zeroOnePart_oneZeroPart, sub_zero]

/-- A one-form has zero `(1,0)`-part exactly when it is a `(0,1)`-form. -/
theorem oneZeroPart_eq_zero_iff {η : TangentSpace I x →L[ℝ] V x} :
    j.oneZeroPart η = 0 ↔ j.IsZeroOneForm η := by
  rw [oneZeroPart_eq_sub_zeroOnePart, sub_eq_zero, eq_comm, zeroOnePart_eq_self_iff]

/-- A one-form is its own `(1,0)`-part exactly when it is complex linear for `j`:
`η (j v) = i • η v` for every tangent vector `v`. -/
theorem oneZeroPart_eq_self_iff {η : TangentSpace I x →L[ℝ] V x} :
    j.oneZeroPart η = η ↔ ∀ v, η (j x v) = Complex.I • η v := by
  rw [oneZeroPart_eq_sub_zeroOnePart, sub_eq_self, zeroOnePart_eq_zero_iff]

@[simp]
theorem oneZeroPart_add (η η' : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart (η + η') = j.oneZeroPart η + j.oneZeroPart η' := by
  simp only [oneZeroPart_eq_sub_zeroOnePart, zeroOnePart_add]
  abel

@[simp]
theorem oneZeroPart_zero : j.oneZeroPart (0 : TangentSpace I x →L[ℝ] V x) = 0 := by
  simp [oneZeroPart_eq_sub_zeroOnePart]

/-- The `(1,0)`-projection commutes with finite sums. -/
theorem oneZeroPart_sum {κ : Type*} (s : Finset κ) (η : κ → TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart (∑ i ∈ s, η i) = ∑ i ∈ s, j.oneZeroPart (η i) := by
  simp only [oneZeroPart_eq_sub_zeroOnePart, zeroOnePart_sum, Finset.sum_sub_distrib]

theorem oneZeroPart_smul (c : ℝ) (η : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart (c • η) = c • j.oneZeroPart η := by
  simp only [oneZeroPart_eq_sub_zeroOnePart, zeroOnePart_smul, smul_sub]

theorem oneZeroPart_complex_smul (c : ℂ) (η : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart (c • η) = c • j.oneZeroPart η := by
  simp only [oneZeroPart_eq_sub_zeroOnePart, zeroOnePart_complex_smul, smul_sub]

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The `(1,0)`-part of a one-form is Tau Ceti's complex-linear part for the pointwise structures
`j.almostComplexStructureAt x` on the tangent space and multiplication by `i` on `V x`, made
continuous by `LinearMap.toContinuousLinearMap`. -/
theorem oneZeroPart_eq_toContinuousLinearMap_complexLinearPart
    (η : TangentSpace I x →L[ℝ] V x) :
    j.oneZeroPart η = LinearMap.toContinuousLinearMap (complexLinearPart
      (j.almostComplexStructureAt x).toLinearMap
      (AlmostComplexStructure.ofComplexModule (V x)).toLinearMap η.toLinearMap) := by
  ext v
  simp [oneZeroPart_apply, complexLinearPart_apply]

/-- The `(0,1)`-part of a one-form is Tau Ceti's complex-antilinear part for the pointwise
structures `j.almostComplexStructureAt x` on the tangent space and multiplication by `i` on
`V x`, made continuous by `LinearMap.toContinuousLinearMap`. -/
theorem zeroOnePart_eq_toContinuousLinearMap_complexAntilinearPart
    (η : TangentSpace I x →L[ℝ] V x) :
    j.zeroOnePart η = LinearMap.toContinuousLinearMap (complexAntilinearPart
      (j.almostComplexStructureAt x).toLinearMap
      (AlmostComplexStructure.ofComplexModule (V x)).toLinearMap η.toLinearMap) := by
  ext v
  simp [zeroOnePart_apply, complexAntilinearPart_apply]

end FiniteDimensional

section Normed

open Bundle

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {W : M → Type*} [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [∀ x, NormedSpace ℂ (W x)] [∀ x, IsScalarTower ℝ ℂ (W x)]

/-- For a Riemannian metric on `M` and normed fibres, the `(1,0)`-part of a one-form is the
operator `TauCeti.complexLinearPartContinuousLinearMap` for `j.toEndomorphism x` and
multiplication by `i`, evaluated at the one-form. -/
theorem oneZeroPart_eq_complexLinearPartContinuousLinearMap (η : TangentSpace I x →L[ℝ] W x) :
    j.oneZeroPart η = complexLinearPartContinuousLinearMap (j.toEndomorphism x)
      (Complex.smulIEquiv (W x) : W x →L[ℝ] W x) η := by
  ext v
  simp [oneZeroPart_apply, complexLinearPart_apply]

/-- For a Riemannian metric on `M` and normed fibres, the `(0,1)`-part of a one-form is the
operator `TauCeti.complexAntilinearPartContinuousLinearMap` for `j.toEndomorphism x` and
multiplication by `i`, evaluated at the one-form. -/
theorem zeroOnePart_eq_complexAntilinearPartContinuousLinearMap
    (η : TangentSpace I x →L[ℝ] W x) :
    j.zeroOnePart η = complexAntilinearPartContinuousLinearMap (j.toEndomorphism x)
      (Complex.smulIEquiv (W x) : W x →L[ℝ] W x) η := by
  ext v
  simp [zeroOnePart_apply, complexAntilinearPart_apply]

end Normed

end TauCeti.SmoothAlmostComplexStructure
