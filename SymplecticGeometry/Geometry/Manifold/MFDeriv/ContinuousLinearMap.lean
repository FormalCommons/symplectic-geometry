/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.ContinuousLinearMap

/-!
# Derivative of a scalar multiple at a zero of the vector factor

Let `u : M → F` be a map from a manifold to a normed space, differentiable at a point `x` where it
vanishes, and let `g` be a function, continuous at `x`, with values in a normed algebra `𝕜'` that
acts on `F`. Then a map agreeing with `g • u` near `x` is differentiable at `x`, with derivative
`g x • du(x)`: the variation of `g` is multiplied by `u x = 0`, so `g` need not be differentiable.

## Main results

* `TauCeti.mdifferentiableAt_of_eventuallyEq_smul`: such a map is differentiable at `x`;
* `TauCeti.mvfderiv_eq_smul_of_eventuallyEq_smul`: its derivative at `x` is `g x • mvfderiv I u x`.

Both are the scalar case of Tau Ceti's `TauCeti.mdifferentiableAt_of_eventuallyEq_clm_apply` and
`TauCeti.mvfderiv_eq_comp_of_eventuallyEq_clm_apply`, applied to multiplication by `g y`, the
family of continuous linear maps `y ↦ ContinuousLinearMap.lsmul 𝕜 𝕜' (g y)`, and derived from them.
-/

public section

open Filter
open scoped Manifold Topology

variable {𝕜 E H M F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {𝕜' : Type*} [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Module 𝕜' F] [IsBoundedSMul 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]
  {f u : M → F} {g : M → 𝕜'} {x : M}

namespace TauCeti

/-- At a zero of `u`, a map agreeing near `x` with `g • u` is differentiable at `x` when `u` is,
for a function `g` that is only continuous at `x`. -/
theorem mdifferentiableAt_of_eventuallyEq_smul (hf : (fun y ↦ g y • u y) =ᶠ[𝓝 x] f)
    (hg : ContinuousAt g x) (hu : MDifferentiableAt I 𝓘(𝕜, F) u x) (hu0 : u x = 0) :
    MDifferentiableAt I 𝓘(𝕜, F) f x :=
  mdifferentiableAt_of_eventuallyEq_clm_apply (c := fun y ↦ ContinuousLinearMap.lsmul 𝕜 𝕜' (g y))
    (by simpa only [ContinuousLinearMap.lsmul_apply] using hf)
    ((ContinuousLinearMap.lsmul 𝕜 𝕜').continuous.continuousAt.comp hg) hu hu0

/-- At a zero of `u`, a map agreeing near `x` with `g • u` has derivative `g x` times that of `u`,
for a function `g` that is only continuous at `x`. -/
theorem mvfderiv_eq_smul_of_eventuallyEq_smul (hf : (fun y ↦ g y • u y) =ᶠ[𝓝 x] f)
    (hg : ContinuousAt g x) (hu : MDifferentiableAt I 𝓘(𝕜, F) u x) (hu0 : u x = 0) :
    mvfderiv I f x = g x • mvfderiv I u x := by
  rw [mvfderiv_eq_comp_of_eventuallyEq_clm_apply
    (c := fun y ↦ ContinuousLinearMap.lsmul 𝕜 𝕜' (g y))
    (by simpa only [ContinuousLinearMap.lsmul_apply] using hf)
    ((ContinuousLinearMap.lsmul 𝕜 𝕜').continuous.continuousAt.comp hg) hu hu0]
  ext v
  -- `simp` does not see `lsmul_apply` here: the vector lives in a tangent space of `F`.
  exact ContinuousLinearMap.lsmul_apply 𝕜 𝕜' (g x) (mvfderiv I u x v)

end TauCeti

end
