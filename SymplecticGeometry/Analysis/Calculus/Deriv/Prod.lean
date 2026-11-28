/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The derivative in the first variable of a function of two variables

* `DifferentiableAt.hasDerivAt_slice_left_of_eventuallyEq`: if `g : 𝕜 × E → F` is
  differentiable at `x` and agrees near `x` with `Function.uncurry f`, then the slice
  `t ↦ g (t, x.2)` has derivative `deriv (fun t ↦ f t x.2) x.1` at `x.1`. This lets a globally
  differentiable representative `g` of a family `f` stand in for it in derivative computations
  in the first variable. Tau Ceti's `TauCeti.hasDerivAt_slice_left` gives the derivative of the
  slice of `g` itself, as `fderiv 𝕜 g x (1, 0)`.
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `g : 𝕜 × E → F` is differentiable at `x` and agrees with `Function.uncurry f` near `x`,
then `t ↦ g (t, x.2)` has derivative `deriv (fun t ↦ f t x.2) x.1` at `x.1`. -/
theorem DifferentiableAt.hasDerivAt_slice_left_of_eventuallyEq {g : 𝕜 × E → F}
    {f : 𝕜 → E → F} {x : 𝕜 × E} (hg : DifferentiableAt 𝕜 g x)
    (hgf : g =ᶠ[𝓝 x] Function.uncurry f) :
    HasDerivAt (fun t ↦ g (t, x.2)) (deriv (fun t ↦ f t x.2) x.1) x.1 := by
  have hc : Continuous fun t : 𝕜 ↦ (t, x.2) := by fun_prop
  have hd : DifferentiableAt 𝕜 (fun t ↦ g (t, x.2)) x.1 :=
    hg.comp x.1 (differentiableAt_id.prodMk (differentiableAt_const _))
  have hslice : (fun t ↦ g (t, x.2)) =ᶠ[𝓝 x.1] fun t ↦ f t x.2 :=
    hgf.comp_tendsto (hc.tendsto' x.1 x rfl)
  rw [← hslice.deriv_eq]
  exact hd.hasDerivAt
