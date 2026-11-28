/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.ModelDbar
public import SymplecticGeometry.Analysis.Complex.Euclidean.Space
public import TauCeti.Analysis.Complex.Wirtinger.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CauchyRiemann.Trivial.Basic
public import TauCeti.LinearAlgebra.Complex.LinearPart
import SymplecticGeometry.Topology.Algebra.Module.ComplexSmulI
import SymplecticGeometry.Analysis.Calculus.FDeriv.Equiv
import SymplecticGeometry.LinearAlgebra.Complex.LinearPart
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The flat `∂̄` and `∂` on `StdSpace ι`

For a complex function `f` on the standard space `StdSpace ι = ℂⁿ`, the flat `∂̄`
`SymplecticGeometry.flatDbar f z` is the complex-antilinear part of `df_z` for the constant
structure `J₀ = stdComplexStructure ι` and multiplication by `i` on `ℂ`, that is
`SymplecticGeometry.flatDbarWith` for the constant field `J₀`. This file gives its API and
compares it with Tau Ceti's `∂̄` on functions and with Tau Ceti's Wirtinger derivatives. Its
`(1,0)` counterpart, the flat `∂` `SymplecticGeometry.flatDel`, is the complex-linear part of
`df_z` for the same structures; it gets the same API and is compared with Tau Ceti's `∂` on
functions.

## Main definitions

* `SymplecticGeometry.flatDbar`: the flat `∂̄`, `v ↦ ½ (df_z v + i df_z (J₀ v))`.
* `SymplecticGeometry.flatDel`: the flat `∂`, `v ↦ ½ (df_z v - i df_z (J₀ v))`; with the flat `∂̄`
  it adds up to `df_z` (`SymplecticGeometry.flatDel_add_flatDbar`).

## Main results

* `SymplecticGeometry.dbarFunction_eq_flatDbar_comp`,
  `SymplecticGeometry.flatDbar_apply_eq_dbarFunction`: the flat `∂̄` is Tau Ceti's `∂̄` on
  functions, `TauCeti.SmoothAlmostComplexStructure.dbarFunction`, for the constant structure
  `J₀.constSmooth`; `SymplecticGeometry.flatDbar_eq_zero_iff`: it vanishes at `z` exactly when
  `df_z` is complex linear for `J₀`.
* `SymplecticGeometry.contDiffAt_flatDbar`, `SymplecticGeometry.contDiff_flatDbar`: the flat `∂̄`
  of a `C^(n + 1)` function is `C^n`.
* `SymplecticGeometry.flatDbar_add`, `SymplecticGeometry.flatDbar_neg`,
  `SymplecticGeometry.flatDbar_smul`, `SymplecticGeometry.flatDbar_mul`: it is additive, commutes
  with negation and complex scalars and satisfies the Leibniz rule;
  `SymplecticGeometry.flatDbar_congr_of_eventuallyEq`: its value at `z` depends only on the germ
  of `f` at `z`, and `SymplecticGeometry.flatDbar_eventuallyEq` says the same of its germ;
  `SymplecticGeometry.flatDbar_complexToRealEuclideanCoord`: the flat `∂̄` of a complex coordinate
  vanishes.
* `SymplecticGeometry.delFunction_eq_flatDel_comp`,
  `SymplecticGeometry.flatDel_apply_eq_delFunction`: the flat `∂` is Tau Ceti's `∂` on functions,
  `TauCeti.SmoothAlmostComplexStructure.delFunction`, for `J₀.constSmooth`;
  `SymplecticGeometry.flatDel_add`, `SymplecticGeometry.flatDel_smul`,
  `SymplecticGeometry.flatDel_mul`: it is additive, commutes with complex scalars and satisfies
  the Leibniz rule.
* `SymplecticGeometry.conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply`,
  `SymplecticGeometry.wirtingerDeriv_comp_complexToRealEuclideanIsometry_apply`: read through the
  real isometry `e = TauCeti.complexToRealEuclideanIsometry ι : ℂⁿ → StdSpace ι`, which carries
  multiplication by `i` to `J₀`, the flat `∂̄` and the flat `∂` of `f` are Tau Ceti's Wirtinger
  derivatives `TauCeti.conjWirtingerDeriv` and `TauCeti.wirtingerDeriv` of `f ∘ e`. Their norms
  agree
  (`SymplecticGeometry.norm_conjWirtingerDeriv_comp_complexToRealEuclideanIsometry`,
  `SymplecticGeometry.norm_wirtingerDeriv_comp_complexToRealEuclideanIsometry`), and so do those
  of the derivatives of the two `∂̄` in a fixed direction
  (`SymplecticGeometry.norm_fderiv_conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply`).

## Implementation notes

The flat `∂̄` is defined on `StdSpace ι` itself rather than as Tau Ceti's `dbarFunction`, whose
values are forms on the tangent spaces `TangentSpace 𝓘(ℝ, StdSpace ι) z`, a family of types
depending on `z`, so that its jets can be taken with `jetNormAt`. The two agree by
`dbarFunction_eq_flatDbar_comp`, and the vanishing criterion of the flat `∂̄` is read off from Tau
Ceti's `dbarFunction_eq_zero_iff`. Its additivity, the commutation with negation and scalars, the
Leibniz rule and the dependence on germs are the constant-`J₀` cases of the lemmas
`flatDbarWith_add`, `flatDbarWith_neg`, `flatDbarWith_smul`, `flatDbarWith_mul`,
`flatDbarWith_congr_of_eventuallyEq` and `flatDbarWith_eventuallyEq` for a field of structures.
In the same way the flat `∂` agrees with Tau Ceti's `delFunction` by
`delFunction_eq_flatDel_comp`, and its additivity and Leibniz rule come from `delFunction_add`
and `delFunction_smul`.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002]
-/

public section

open TauCeti
open scoped Topology

namespace SymplecticGeometry

variable {ι : Type*} [Fintype ι]

/-- The **flat `∂̄`** of a complex function `f` on `StdSpace ι` at `z`: the flat `∂̄`
`SymplecticGeometry.flatDbarWith` for the constant structure `J₀ = stdComplexStructure ι`, that
is the complex-antilinear part of `df_z` for `J₀` and multiplication by `i` on `ℂ`,
`v ↦ ½ (df_z v + i df_z (J₀ v))`. -/
noncomputable def flatDbar (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  flatDbarWith (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) f z

theorem flatDbar_def (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar f z =
      flatDbarWith (fun _ ↦ LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)
        f z :=
  (rfl)

/-- The flat `∂̄` of `f` at `z` is the operator `TauCeti.complexAntilinearPartContinuousLinearMap`
for `J₀` and multiplication by `i`, applied to `df_z`. -/
theorem flatDbar_eq (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar f z = complexAntilinearPartContinuousLinearMap
      (LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)
      (Complex.smulIEquiv ℂ : ℂ →L[ℝ] ℂ) (fderiv ℝ f z) := by
  rw [flatDbar_def, flatDbarWith_def]

theorem flatDbar_apply (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    flatDbar f z v =
      (2⁻¹ : ℝ) • (fderiv ℝ f z v + Complex.I * fderiv ℝ f z (stdComplexStructure ι v)) := by
  rw [flatDbar_def, flatDbarWith_apply, LinearMap.coe_toContinuousLinearMap']

/-- The flat `∂̄` of `f` is `C^n` at a point where `f` is `C^(n + 1)`. -/
theorem contDiffAt_flatDbar {n : ℕ∞} {f : StdSpace ι → ℂ} {z : StdSpace ι}
    (hf : ContDiffAt ℝ (n + 1) f z) : ContDiffAt ℝ n (flatDbar f) z := by
  rw [show flatDbar f = _ from funext (flatDbar_def f)]
  exact contDiffAt_flatDbarWith contDiffAt_const hf

/-- The flat `∂̄` of a `C^(n + 1)` function is `C^n`. -/
theorem contDiff_flatDbar {n : ℕ∞} {f : StdSpace ι → ℂ} (hf : ContDiff ℝ (n + 1) f) :
    ContDiff ℝ n (flatDbar f) :=
  contDiff_iff_contDiffAt.2 fun _ ↦ contDiffAt_flatDbar hf.contDiffAt

/-- The **flat `∂̄` is Tau Ceti's `∂̄` on functions**: for the constant smooth almost complex
structure `J₀` on `StdSpace ι`, `TauCeti.SmoothAlmostComplexStructure.dbarFunction f z` is the flat
`∂̄` of `f` at `z`, read on the tangent space at `z` through `NormedSpace.fromTangentSpace z`. -/
theorem dbarFunction_eq_flatDbar_comp (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    (stdComplexStructure ι).constSmooth.dbarFunction f z =
      flatDbar f z ∘L (NormedSpace.fromTangentSpace (𝕜 := ℝ) z : _ →L[ℝ] StdSpace ι) := by
  ext v
  simp [SmoothAlmostComplexStructure.dbarFunction_apply, mvfderiv_eq_fderiv, flatDbar_apply]

/-- The flat `∂̄` of `f` at `z`, applied to `v`, is Tau Ceti's `∂̄` on functions for the constant
structure `J₀`, applied to `v` read as a tangent vector at `z`. -/
theorem flatDbar_apply_eq_dbarFunction (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    flatDbar f z v = (stdComplexStructure ι).constSmooth.dbarFunction f z
      ((NormedSpace.fromTangentSpace z).symm v) := by
  rw [dbarFunction_eq_flatDbar_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- The flat `∂̄` of `f` vanishes at `z` exactly when `df_z` is complex linear for `J₀`:
`df_z (J₀ v) = i df_z v` for all `v`. -/
theorem flatDbar_eq_zero_iff (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar f z = 0 ↔
      ∀ v, fderiv ℝ f z (stdComplexStructure ι v) = Complex.I * fderiv ℝ f z v := by
  have h := (stdComplexStructure ι).constSmooth.dbarFunction_eq_zero_iff f z
  simp only [mvfderiv_eq_fderiv, smul_eq_mul, ContinuousLinearMap.comp_apply,
    dbarFunction_eq_flatDbar_comp, ContinuousLinearMap.ext_iff] at h
  rw [ContinuousLinearMap.ext_iff]
  refine h.trans (forall_congr' fun v ↦ ?_)
  -- `v` lies in the type synonym `TangentSpace _ z`, so the lemmas take it explicitly.
  simp only [ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace_apply,
    AlmostComplexStructure.constSmooth_apply _ z v,
    NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) z ((stdComplexStructure ι).toLinearMap v)]

/-- The flat `∂̄` is additive on functions differentiable at `z`. -/
theorem flatDbar_add {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : flatDbar (f + g) z = flatDbar f z + flatDbar g z := by
  simp only [flatDbar_def, flatDbarWith_add hf hg]

@[simp]
theorem flatDbar_neg (f : StdSpace ι → ℂ) (z : StdSpace ι) : flatDbar (-f) z = -flatDbar f z := by
  simp only [flatDbar_def, flatDbarWith_neg]

/-- The flat `∂̄` commutes with complex scalars. -/
@[simp]
theorem flatDbar_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar (c • f) z = c • flatDbar f z := by
  simp only [flatDbar_def, flatDbarWith_smul]

@[simp]
theorem flatDbar_zero (z : StdSpace ι) : flatDbar (0 : StdSpace ι → ℂ) z = 0 := by
  simp only [flatDbar_def, flatDbarWith_zero]

/-- The **Leibniz rule** for the flat `∂̄`: for `f` and `g` differentiable at `z`, the flat `∂̄`
of `f * g` at `z` is `f z` times the flat `∂̄` of `g` plus `g z` times the flat `∂̄` of `f`. -/
theorem flatDbar_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    flatDbar (fun y ↦ f y * g y) z = f z • flatDbar g z + g z • flatDbar f z := by
  simp only [flatDbar_def, flatDbarWith_mul hf hg]

/-- The flat `∂̄` at `z` depends only on the germ of `f` at `z`. -/
theorem flatDbar_congr_of_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι}
    (h : f =ᶠ[𝓝 z] g) : flatDbar f z = flatDbar g z := by
  simp only [flatDbar_def, flatDbarWith_congr_of_eventuallyEq h]

/-- If `f` and `g` agree near `z`, then so do their flat `∂̄`. -/
theorem flatDbar_eventuallyEq {f g : StdSpace ι → ℂ} {z : StdSpace ι} (h : f =ᶠ[𝓝 z] g) :
    flatDbar f =ᶠ[𝓝 z] flatDbar g :=
  (flatDbarWith_eventuallyEq h).mono fun w hw ↦ by rw [flatDbar_def, flatDbar_def]; exact hw

/-- The flat `∂̄` of the complex coordinate `z_j` vanishes: it is complex linear for `J₀`. -/
@[simp]
theorem flatDbar_complexToRealEuclideanCoord (j : ι) :
    flatDbar (complexToRealEuclideanCoord ι j) = 0 := by
  ext z v : 2
  rw [flatDbar_eq, (complexToRealEuclideanCoord ι j).fderiv,
    complexAntilinearPartContinuousLinearMap_apply_apply, LinearMap.coe_toContinuousLinearMap,
    Complex.coe_smulIEquiv_eq_ofComplexModule,
    (isComplexLinear_complexToRealEuclideanCoord j).complexAntilinearPart_eq_zero
      (AlmostComplexStructure.ofComplexModule ℂ).square_neg]
  simp

/-! ### The flat `∂` -/

/-- The **flat `∂`** of a complex function `f` on `StdSpace ι` at `z`: the operator
`TauCeti.complexLinearPartContinuousLinearMap` for `J₀ = stdComplexStructure ι` and
multiplication by `i` on `ℂ`, applied to `df_z`, that is `v ↦ ½ (df_z v - i df_z (J₀ v))`. It
is the `(1,0)` counterpart of the flat `∂̄` `SymplecticGeometry.flatDbar`. -/
noncomputable def flatDel (f : StdSpace ι → ℂ) (z : StdSpace ι) : StdSpace ι →L[ℝ] ℂ :=
  complexLinearPartContinuousLinearMap
    (LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)
    (Complex.smulIEquiv ℂ : ℂ →L[ℝ] ℂ) (fderiv ℝ f z)

theorem flatDel_def (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDel f z = complexLinearPartContinuousLinearMap
      (LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap)
      (Complex.smulIEquiv ℂ : ℂ →L[ℝ] ℂ) (fderiv ℝ f z) :=
  (rfl)

/-- As a real-linear map, the flat `∂` of `f` at `z` is Tau Ceti's complex-linear part
`TauCeti.complexLinearPart` of `df_z`, for `J₀` and multiplication by `i`. -/
theorem coe_flatDel (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    (flatDel f z : StdSpace ι →ₗ[ℝ] ℂ) =
      complexLinearPart (stdComplexStructure ι).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        (fderiv ℝ f z : StdSpace ι →ₗ[ℝ] ℂ) := by
  rw [flatDel_def, coe_complexLinearPartContinuousLinearMap_apply,
    LinearMap.coe_toContinuousLinearMap, Complex.coe_smulIEquiv_eq_ofComplexModule]

theorem flatDel_apply (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    flatDel f z v =
      (2⁻¹ : ℝ) • (fderiv ℝ f z v - Complex.I * fderiv ℝ f z (stdComplexStructure ι v)) := by
  rw [flatDel_def, complexLinearPartContinuousLinearMap_apply_apply, complexLinearPart_apply]
  simp

/-- The differential of `f` at `z` is the sum of its flat `∂` and its flat `∂̄`. -/
theorem flatDel_add_flatDbar (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDel f z + flatDbar f z = fderiv ℝ f z := by
  rw [flatDel_def, flatDbar_eq,
    complexLinearPartContinuousLinearMap_add_complexAntilinearPartContinuousLinearMap_apply]

/-- The flat `∂` commutes with complex scalars. -/
@[simp]
theorem flatDel_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDel (c • f) z = c • flatDel f z := by
  apply ContinuousLinearMap.coe_injective
  rw [coe_flatDel, ContinuousLinearMap.toLinearMap_smul, coe_flatDel, fderiv_const_smul_field,
    Pi.smul_apply, ContinuousLinearMap.toLinearMap_smul, complexLinearPart_complex_smul]

/-- The **flat `∂` is Tau Ceti's `∂` on functions**: for the constant smooth almost complex
structure `J₀` on `StdSpace ι`, `TauCeti.SmoothAlmostComplexStructure.delFunction f z` is the flat
`∂` of `f` at `z`, read on the tangent space at `z` through `NormedSpace.fromTangentSpace z`. -/
theorem delFunction_eq_flatDel_comp (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    (stdComplexStructure ι).constSmooth.delFunction f z =
      flatDel f z ∘L (NormedSpace.fromTangentSpace (𝕜 := ℝ) z : _ →L[ℝ] StdSpace ι) := by
  ext v
  simp [SmoothAlmostComplexStructure.delFunction_apply, mvfderiv_eq_fderiv, flatDel_apply]

/-- The flat `∂` of `f` at `z`, applied to `v`, is Tau Ceti's `∂` on functions for the constant
structure `J₀`, applied to `v` read as a tangent vector at `z`. -/
theorem flatDel_apply_eq_delFunction (f : StdSpace ι → ℂ) (z v : StdSpace ι) :
    flatDel f z v = (stdComplexStructure ι).constSmooth.delFunction f z
      ((NormedSpace.fromTangentSpace z).symm v) := by
  rw [delFunction_eq_flatDel_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- The flat `∂` is additive on functions differentiable at `z`. -/
theorem flatDel_add {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : flatDel (f + g) z = flatDel f z + flatDel g z := by
  ext v
  simp [flatDel_apply_eq_delFunction, SmoothAlmostComplexStructure.delFunction_add _
    (mdifferentiableAt_iff_differentiableAt.2 hf) (mdifferentiableAt_iff_differentiableAt.2 hg)]

@[simp]
theorem flatDel_zero (z : StdSpace ι) : flatDel (0 : StdSpace ι → ℂ) z = 0 := by
  ext v
  simp [flatDel_apply_eq_delFunction]

/-- The **Leibniz rule** for the flat `∂`: for `f` and `g` differentiable at `z`, the flat `∂`
of `f * g` at `z` is `f z` times the flat `∂` of `g` plus `g z` times the flat `∂` of `f`. -/
theorem flatDel_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    flatDel (fun y ↦ f y * g y) z = f z • flatDel g z + g z • flatDel f z := by
  have h := (stdComplexStructure ι).constSmooth.delFunction_smul
    (mdifferentiableAt_iff_differentiableAt.2 hf) (mdifferentiableAt_iff_differentiableAt.2 hg)
  simp only [smul_eq_mul] at h
  ext v
  simp [flatDel_apply_eq_delFunction, ← Pi.mul_def, h, mul_comm]

/-! ### The flat operators against the Wirtinger derivatives

Read through the real isometry `e = complexToRealEuclideanIsometry ι` from `ℂⁿ` to
`StdSpace ι`, which carries multiplication by `i` to `J₀`, a function `f` on `StdSpace ι` becomes
the function `f ∘ e` on `EuclideanSpace ℂ ι`, and its flat `∂̄` and flat `∂` become
Tau Ceti's Wirtinger derivatives of `f ∘ e`, with the same norms. -/

section Wirtinger

/-- **The flat `∂̄` is the conjugate Wirtinger derivative**: for the isometry
`e = complexToRealEuclideanIsometry ι`, the conjugate Wirtinger derivative of `f ∘ e` at `u`,
applied to `v`, is the flat `∂̄` of `f` at `e u`, applied to `e v`. -/
theorem conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply (f : StdSpace ι → ℂ)
    (u v : EuclideanSpace ℂ ι) :
    conjWirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u v =
      flatDbar f (complexToRealEuclideanIsometry ι u) (complexToRealEuclideanIsometry ι v) := by
  rw [conjWirtingerDeriv_apply, flatDbar_apply, LinearIsometryEquiv.comp_right_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    stdComplexStructure_complexToRealEuclideanIsometry]
  simp [Complex.real_smul, mul_add]

/-- For the isometry `e = complexToRealEuclideanIsometry ι`, the conjugate Wirtinger derivative
of `f ∘ e` at `u` has the norm of the flat `∂̄` of `f` at `e u`. -/
theorem norm_conjWirtingerDeriv_comp_complexToRealEuclideanIsometry (f : StdSpace ι → ℂ)
    (u : EuclideanSpace ℂ ι) :
    ‖conjWirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u‖ =
      ‖flatDbar f (complexToRealEuclideanIsometry ι u)‖ := by
  have h : ContinuousLinearMap.restrictScalarsₛₗLI
      (conjWirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u) =
      flatDbar f (complexToRealEuclideanIsometry ι u) ∘L
        ((complexToRealEuclideanIsometry ι).toContinuousLinearEquiv :
          EuclideanSpace ℂ ι →L[ℝ] StdSpace ι) := by
    ext v
    simp [ContinuousLinearMap.restrictScalarsₛₗLI_apply,
      conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply]
  rw [← ContinuousLinearMap.restrictScalarsₛₗLI.norm_map, h]
  exact (flatDbar f _).opNorm_comp_linearIsometryEquiv _

/-- For the isometry `e = complexToRealEuclideanIsometry ι` and a direction `b`, the derivative
at `u` of `y ↦ ∂̄(f ∘ e)(y) b`, the conjugate Wirtinger derivative, has the norm of the
derivative at `e u` of `z ↦ flatDbar f z (e b)`. -/
theorem norm_fderiv_conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply
    (f : StdSpace ι → ℂ) (u b : EuclideanSpace ℂ ι) :
    ‖fderiv ℝ (fun y ↦ conjWirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) y b) u‖ =
      ‖fderiv ℝ (fun z ↦ flatDbar f z (complexToRealEuclideanIsometry ι b))
        (complexToRealEuclideanIsometry ι u)‖ := by
  simp_rw [conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply]
  simpa only [norm_iteratedFDeriv_one, Function.comp_def] using
    (complexToRealEuclideanIsometry ι).norm_iteratedFDeriv_comp_right
      (fun z ↦ flatDbar f z (complexToRealEuclideanIsometry ι b)) u 1

/-- **The flat `∂` is the Wirtinger derivative**: for the isometry
`e = complexToRealEuclideanIsometry ι`, the Wirtinger derivative of `f ∘ e` at `u`, applied to
`v`, is the flat `∂` of `f` at `e u`, applied to `e v`. -/
theorem wirtingerDeriv_comp_complexToRealEuclideanIsometry_apply (f : StdSpace ι → ℂ)
    (u v : EuclideanSpace ℂ ι) :
    wirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u v =
      flatDel f (complexToRealEuclideanIsometry ι u) (complexToRealEuclideanIsometry ι v) := by
  rw [wirtingerDeriv_apply, flatDel_apply, LinearIsometryEquiv.comp_right_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    stdComplexStructure_complexToRealEuclideanIsometry]
  simp [Complex.real_smul, mul_sub]

/-- For the isometry `e = complexToRealEuclideanIsometry ι`, the Wirtinger derivative of `f ∘ e`
at `u` has the norm of the flat `∂` of `f` at `e u`. -/
theorem norm_wirtingerDeriv_comp_complexToRealEuclideanIsometry (f : StdSpace ι → ℂ)
    (u : EuclideanSpace ℂ ι) :
    ‖wirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u‖ =
      ‖flatDel f (complexToRealEuclideanIsometry ι u)‖ := by
  have h : (wirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u).restrictScalars ℝ =
      flatDel f (complexToRealEuclideanIsometry ι u) ∘L
        ((complexToRealEuclideanIsometry ι).toContinuousLinearEquiv :
          EuclideanSpace ℂ ι →L[ℝ] StdSpace ι) := by
    ext v
    simp [wirtingerDeriv_comp_complexToRealEuclideanIsometry_apply]
  rw [← (wirtingerDeriv _ u).norm_restrictScalars (𝕜' := ℝ), h]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

end Wirtinger

end SymplecticGeometry

end
