/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Basic
import SymplecticGeometry.Geometry.Manifold.DifferentialForm.FiberIntegral.Product.Coefficient
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Restriction
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# The base derivative of the fibre integral over an open subset of a normed space

Let `U` be an open subset of a normed space `E`, with the model `𝓘(ℝ, E)`, let `F` be a manifold
of dimension `m` over `J` with an orientation `o`, and let `α` be a smooth form of degree `r + m`
on `U × F`. Fix vectors `u₁, …, uᵣ ∈ E`, a point `b ∈ U` and a direction `a ∈ E`, and write
`D y` for the derivative at `b`, in the direction `a`, of `b' ↦ prodFiberIntegrand α b' u y`.
This file shows that `D` is a smooth `m`-form on `F`
(`SymplecticGeometry.isSmoothForm_mfderiv_prodFiberIntegrand`) and, for `F` compact, that
`b' ↦ ∫_F prodFiberIntegrand α b' u` is differentiable at `b`
(`SymplecticGeometry.mdifferentiableAt_integralTopForm_prodFiberIntegrand`) with derivative
`∫_F D` in the direction `a`
(`SymplecticGeometry.mfderiv_integralTopForm_prodFiberIntegrand_apply`): the derivative in the
base passes under the integral over the fibre. This holds for every `r` and `m`.

These are the results of `FiberIntegral/Product/Coefficient.lean` on smooth families of forms
over `U` (`TauCeti.isSmoothForm_mfderiv_family_apply`, `TauCeti.mfderiv_integralTopForm_apply`)
and `TauCeti.contMDiff_integralTopForm`, applied to the integrands along the constant vectors
`u`. Those are jointly smooth (`SymplecticGeometry.contMDiff_prodFiberIntegrand_const`) by
`SymplecticGeometry.contMDiff_prodFiberIntegrand`, since a
constant vector field on `E` is smooth (`TauCeti.contMDiff_tangentBundle_mk_const`) and so is its
restriction to `U` (`TauCeti.Manifold.contMDiffAt_tangentBundle_opens_iff`).

This is the step of Bott–Tu, §6, that differentiates the fibre integral in the base.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §6.
-/

public section

noncomputable section

open Bundle TopologicalSpace
open scoped Manifold ContDiff

namespace SymplecticGeometry

open TauCeti

variable {E E' H' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace F] [ChartedSpace H' F] [IsManifold J ∞ F]
  {U : Opens E} {r m : ℕ}

/-- **The integrand along constant vectors is jointly smooth.** Let `α` be a `C^n` form of degree
`r + m` on `U × F`. For `u₁, …, uᵣ ∈ E`, the integrands `prodFiberIntegrand α b u`, as `b` runs
over `U`, form a `C^n` section of the bundle of `m`-forms on `F` along `(b, y) ↦ y`. -/
theorem contMDiff_prodFiberIntegrand_const {n : WithTop ℕ∞}
    {α : RoughForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m)} (hα : IsSmoothForm (𝓘(ℝ, E).prod J) n α)
    (u : Fin r → E) :
    ContMDiff (𝓘(ℝ, E).prod J) (J.prod 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)) n
      (fun q : U × F ↦ TotalSpace.mk' (E' [⋀^Fin m]→L[ℝ] ℝ)
        (E := fun y : F ↦ TangentSpace J y [⋀^Fin m]→L[ℝ] Trivial F ℝ y) q.2
        (prodFiberIntegrand α q.1 u q.2)) :=
  contMDiff_prodFiberIntegrand (g := id) hα contMDiff_id fun i b ↦
    Manifold.contMDiffAt_tangentBundle_opens_iff.2
      ((contMDiff_tangentBundle_mk_const (u i) (b : E)).comp b contMDiff_subtypeVal.contMDiffAt)

/-- **The base derivative of the integrand is a smooth form.** Let `F` be Hausdorff and
σ-compact, with an orientation `o`, and let `α` be a smooth form of degree `r + m` on `U × F`.
For `b ∈ U` and `a, u₁, …, uᵣ ∈ E`, the `m`-form on `F` whose value at `y` is the derivative at
`b`, in the direction `a`, of `b' ↦ prodFiberIntegrand α b' u y` is smooth. -/
theorem isSmoothForm_mfderiv_prodFiberIntegrand [T2Space F] [SigmaCompactSpace F]
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) (b : U) (a : E) :
    IsSmoothForm J ∞ (fun y ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
        (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α.val b' u y) b a) :=
  isSmoothForm_mfderiv_family_apply o (contMDiff_prodFiberIntegrand_const α.isSmoothForm u) b a

section Integral

variable [T2Space F] [CompactSpace F]

/-- **The fibre integral of the integrand is differentiable in the base.** Let `F` be compact
and Hausdorff, with an orientation `o`, and let `α` be a smooth form of degree `r + m` on `U × F`.
For `u₁, …, uᵣ ∈ E`, the function `b' ↦ ∫_F prodFiberIntegrand α b' u` on `U` is differentiable
at every `b ∈ U`. -/
theorem mdifferentiableAt_integralTopForm_prodFiberIntegrand
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) (b : U) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ)
      (fun b' : U ↦ integralTopForm o (prodFiberIntegrand α.val b' u)) b :=
  (contMDiff_integralTopForm o (contMDiff_prodFiberIntegrand_const α.isSmoothForm u)
    b).mdifferentiableAt (by simp)

/-- **Differentiation of the fibre integral under the integral sign.** Let `F` be compact and
Hausdorff, with an orientation `o`, and let `α` be a smooth form of degree `r + m` on `U × F`.
For `b ∈ U` and `a, u₁, …, uᵣ ∈ E`, the derivative at `b`, in the direction `a`, of
`b' ↦ ∫_F prodFiberIntegrand α b' u` is the integral over `F` of the `m`-form whose value at `y`
is the derivative at `b`, in the direction `a`, of `b' ↦ prodFiberIntegrand α b' u y`. -/
theorem mfderiv_integralTopForm_prodFiberIntegrand_apply
    (o : Manifold.Orientation J F (Fin m)) (α : SmoothForm (𝓘(ℝ, E).prod J) (U × F) ℝ (r + m))
    (u : Fin r → E) (b : U) (a : E) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ) (fun b' : U ↦ integralTopForm o (prodFiberIntegrand α.val b' u)) b a =
      integralTopForm o (fun y ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from
        mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E' [⋀^Fin m]→L[ℝ] ℝ)
          (fun b' : U ↦ show E' [⋀^Fin m]→L[ℝ] ℝ from prodFiberIntegrand α.val b' u y) b a) :=
  mfderiv_integralTopForm_apply (by simp) o (contMDiff_prodFiberIntegrand_const α.isSmoothForm u)
    b a

end Integral

end SymplecticGeometry

end
