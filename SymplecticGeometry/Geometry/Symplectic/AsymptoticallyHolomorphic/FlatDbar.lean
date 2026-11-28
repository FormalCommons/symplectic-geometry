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
import SymplecticGeometry.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The flat `∂̄` on `StdSpace ι`

For a complex function `f` on the standard space `StdSpace ι = ℂⁿ`, the flat `∂̄`
`SymplecticGeometry.flatDbar f z` is the complex-antilinear part of `df_z` for the constant
structure `J₀ = stdComplexStructure ι` and multiplication by `i` on `ℂ`, that is
`SymplecticGeometry.flatDbarWith` for the constant field `J₀`. This file gives its API and
compares it with Tau Ceti's `∂̄` on functions and with Tau Ceti's Wirtinger derivatives.

## Main definitions

* `SymplecticGeometry.flatDbar`: the flat `∂̄`, `v ↦ ½ (df_z v + i df_z (J₀ v))`.

## Main results

* `SymplecticGeometry.dbarFunction_eq_flatDbar_comp`,
  `SymplecticGeometry.flatDbar_apply_eq_dbarFunction`: the flat `∂̄` is Tau Ceti's `∂̄` on
  functions, `TauCeti.SmoothAlmostComplexStructure.dbarFunction`, for the constant structure
  `J₀.constSmooth`; `SymplecticGeometry.flatDbar_eq_zero_iff`: it vanishes at `z` exactly when
  `df_z` is complex linear for `J₀`.
* `SymplecticGeometry.contDiffAt_flatDbar`, `SymplecticGeometry.contDiff_flatDbar`: the flat `∂̄`
  of a `C^(n + 1)` function is `C^n`.
* `SymplecticGeometry.flatDbar_add`, `SymplecticGeometry.flatDbar_smul`,
  `SymplecticGeometry.flatDbar_mul`: it is additive, commutes with complex scalars and satisfies
  the Leibniz rule; `SymplecticGeometry.flatDbar_complexToRealEuclideanCoord`: the flat `∂̄` of a
  complex coordinate vanishes.
* `SymplecticGeometry.conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply`,
  `SymplecticGeometry.wirtingerDeriv_comp_complexToRealEuclideanIsometry_apply`: read through the
  real isometry `e = TauCeti.complexToRealEuclideanIsometry ι : ℂⁿ → StdSpace ι`, which carries
  multiplication by `i` to `J₀`, the flat `∂̄` of `f` and the complex-linear part of `df` for `J₀`
  are Tau Ceti's Wirtinger derivatives `TauCeti.conjWirtingerDeriv` and `TauCeti.wirtingerDeriv`
  of `f ∘ e`. Their norms agree
  (`SymplecticGeometry.norm_conjWirtingerDeriv_comp_complexToRealEuclideanIsometry`,
  `SymplecticGeometry.norm_wirtingerDeriv_comp_complexToRealEuclideanIsometry`), and so do those
  of the derivatives of the two `∂̄` in a fixed direction
  (`SymplecticGeometry.norm_fderiv_conjWirtingerDeriv_comp_complexToRealEuclideanIsometry_apply`).

## Implementation notes

The flat `∂̄` is defined on `StdSpace ι` itself rather than as Tau Ceti's `dbarFunction`, whose
values are forms on the tangent spaces `TangentSpace 𝓘(ℝ, StdSpace ι) z`, a family of types
depending on `z`, so that its jets can be taken with `jetNormAt`. The two agree by
`dbarFunction_eq_flatDbar_comp`, and the additivity, the commutation with scalars, the Leibniz rule
and the vanishing criterion of the flat `∂̄` are read off from Tau Ceti's `dbarFunction_add`,
`dbarFunction_const_smul`, `dbarFunction_smul` and `dbarFunction_eq_zero_iff`.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996]
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002]
-/

public section

open TauCeti

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
    flatDbar f z = complexAntilinearPartContinuousLinearMap (stdComplexStructure ι).toLinearMap
      (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap (fderiv ℝ f z) := by
  rw [flatDbar_def, flatDbarWith_def, LinearMap.coe_toContinuousLinearMap]

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
  ext v
  simp [flatDbar_apply_eq_dbarFunction, SmoothAlmostComplexStructure.dbarFunction_add _
    (mdifferentiableAt_iff_differentiableAt.2 hf) (mdifferentiableAt_iff_differentiableAt.2 hg)]

/-- The flat `∂̄` commutes with complex scalars. -/
@[simp]
theorem flatDbar_smul (c : ℂ) (f : StdSpace ι → ℂ) (z : StdSpace ι) :
    flatDbar (c • f) z = c • flatDbar f z := by
  ext v
  simp [flatDbar_apply_eq_dbarFunction]

@[simp]
theorem flatDbar_zero (z : StdSpace ι) : flatDbar (0 : StdSpace ι → ℂ) z = 0 := by
  ext v
  simp [flatDbar_apply_eq_dbarFunction]

/-- The **Leibniz rule** for the flat `∂̄`: for `f` and `g` differentiable at `z`, the flat `∂̄`
of `f * g` at `z` is `f z` times the flat `∂̄` of `g` plus `g z` times the flat `∂̄` of `f`. -/
theorem flatDbar_mul {f g : StdSpace ι → ℂ} {z : StdSpace ι} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    flatDbar (fun y ↦ f y * g y) z = f z • flatDbar g z + g z • flatDbar f z := by
  have h := (stdComplexStructure ι).constSmooth.dbarFunction_smul
    (mdifferentiableAt_iff_differentiableAt.2 hf) (mdifferentiableAt_iff_differentiableAt.2 hg)
  simp only [smul_eq_mul] at h
  ext v
  simp [flatDbar_apply_eq_dbarFunction, ← Pi.mul_def, h, mul_comm]

/-- The flat `∂̄` of the complex coordinate `z_j` vanishes: it is complex linear for `J₀`. -/
@[simp]
theorem flatDbar_complexToRealEuclideanCoord (j : ι) :
    flatDbar (complexToRealEuclideanCoord ι j) = 0 := by
  ext z v : 2
  rw [flatDbar_eq, (complexToRealEuclideanCoord ι j).fderiv,
    complexAntilinearPartContinuousLinearMap_apply_apply,
    (isComplexLinear_complexToRealEuclideanCoord j).complexAntilinearPart_eq_zero
      (AlmostComplexStructure.ofComplexModule ℂ).square_neg]
  simp

/-! ### The flat operators against the Wirtinger derivatives

Read through the real isometry `e = complexToRealEuclideanIsometry ι` from `ℂⁿ` to
`StdSpace ι`, which carries multiplication by `i` to `J₀`, a function `f` on `StdSpace ι` becomes
the function `f ∘ e` on `EuclideanSpace ℂ ι`, and its flat `∂̄` and complex-linear part for `J₀`
become Tau Ceti's Wirtinger derivatives of `f ∘ e`, with the same norms. -/

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

/-- **The complex-linear part for `J₀` is the Wirtinger derivative**: for the isometry
`e = complexToRealEuclideanIsometry ι`, the Wirtinger derivative of `f ∘ e` at `u`, applied to
`v`, is the complex-linear part `TauCeti.complexLinearPart`, for `J₀` and multiplication by `i`,
of `df` at `e u`, applied to `e v`. -/
theorem wirtingerDeriv_comp_complexToRealEuclideanIsometry_apply (f : StdSpace ι → ℂ)
    (u v : EuclideanSpace ℂ ι) :
    wirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u v =
      complexLinearPart (stdComplexStructure ι).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        (fderiv ℝ f (complexToRealEuclideanIsometry ι u) : StdSpace ι →ₗ[ℝ] ℂ)
        (complexToRealEuclideanIsometry ι v) := by
  rw [wirtingerDeriv_apply, complexLinearPart_apply, LinearIsometryEquiv.comp_right_fderiv,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  simp [AlmostComplexStructure.ofComplexModule_apply, Complex.real_smul]

/-- For the isometry `e = complexToRealEuclideanIsometry ι`, the Wirtinger derivative of `f ∘ e`
at `u` has the norm of the complex-linear part, for `J₀` and multiplication by `i`, of `df` at
`e u`. -/
theorem norm_wirtingerDeriv_comp_complexToRealEuclideanIsometry (f : StdSpace ι → ℂ)
    (u : EuclideanSpace ℂ ι) :
    ‖wirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u‖ =
      ‖LinearMap.toContinuousLinearMap (complexLinearPart (stdComplexStructure ι).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        (fderiv ℝ f (complexToRealEuclideanIsometry ι u) : StdSpace ι →ₗ[ℝ] ℂ))‖ := by
  have h : (wirtingerDeriv (f ∘ complexToRealEuclideanIsometry ι) u).restrictScalars ℝ =
      LinearMap.toContinuousLinearMap (complexLinearPart (stdComplexStructure ι).toLinearMap
        (AlmostComplexStructure.ofComplexModule ℂ).toLinearMap
        (fderiv ℝ f (complexToRealEuclideanIsometry ι u) : StdSpace ι →ₗ[ℝ] ℂ)) ∘L
        ((complexToRealEuclideanIsometry ι).toContinuousLinearEquiv :
          EuclideanSpace ℂ ι →L[ℝ] StdSpace ι) := by
    ext v
    simp [wirtingerDeriv_comp_complexToRealEuclideanIsometry_apply]
  rw [← (wirtingerDeriv _ u).norm_restrictScalars (𝕜' := ℝ), h]
  exact ContinuousLinearMap.opNorm_comp_linearIsometryEquiv _ _

end Wirtinger

end SymplecticGeometry

end
