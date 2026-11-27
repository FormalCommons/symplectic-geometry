/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import TauCeti.LinearAlgebra.TotallyReal.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Totally real tangent images

This file gives `TauCeti.IsTotallyReal.range_mfderiv_comp`: if the tangent image of a map `f`
at `g y` is totally real for an endomorphism `J`, then so is the tangent image of `f ∘ g` at `y`,
for any `g` differentiable at `y`. The tangent image of `f ∘ g` lies in that of `f`, by the chain
rule `mfderiv_comp`, and total reality passes to subspaces by Tau Ceti's
`TauCeti.IsTotallyReal.mono`. For instance, the restriction of a totally real disc to its
boundary sphere is totally real.
-/

public section

namespace TauCeti.IsTotallyReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ H₁ H₂ H₃ M₁ M₂ M₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  [TopologicalSpace H₁] [TopologicalSpace H₂] [TopologicalSpace H₃]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂} {I₃ : ModelWithCorners 𝕜 E₃ H₃}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]

/-- **Total reality passes to precomposites.** If `g` is differentiable at `y`, `f` is
differentiable at `g y`, and the tangent image of `f` at `g y` is totally real for an endomorphism
`J` of the tangent space of `M₃` at `f (g y)`, then the tangent image of `f ∘ g` at `y` is totally
real for `J`: it lies in that of `f`. -/
theorem range_mfderiv_comp {g : M₁ → M₂} {f : M₂ → M₃} {y : M₁}
    {J : TangentSpace I₃ (f (g y)) →ₗ[𝕜] TangentSpace I₃ (f (g y))}
    (h : IsTotallyReal J (LinearMap.range (mfderiv I₂ I₃ f (g y)).toLinearMap))
    (hf : MDifferentiableAt I₂ I₃ f (g y)) (hg : MDifferentiableAt I₁ I₂ g y) :
    IsTotallyReal J (LinearMap.range (mfderiv I₁ I₃ (f ∘ g) y).toLinearMap) :=
  h.mono (by rw [mfderiv_comp y hf hg]; exact LinearMap.range_comp_le_range _ _)

end TauCeti.IsTotallyReal

end
