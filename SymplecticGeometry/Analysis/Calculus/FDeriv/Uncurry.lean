/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# The derivative of a family that starts at the identity

Let `Ψ : E → 𝕜 → E` be a family of points with `Ψ x 0 = x` for `x` near `y`, such as a local
flow, where `Ψ x t` is the point reached from `x` at time `t`. If `(x, t) ↦ Ψ x t` is
differentiable at `(y, 0)` and the curve `t ↦ Ψ y t` has velocity `v` at time `0`, then its
derivative there is `(u, σ) ↦ u + σ • v` (`DifferentiableAt.hasFDerivAt_uncurry_zero`). Its
restriction to `E × {0}` is the derivative of the identity, and its restriction to `{0} × 𝕜` is
that of the curve.
-/

public section

open Filter Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {Ψ : E → 𝕜 → E} {y v : E}

/-- Let `Ψ x t` be a family of points with `Ψ x 0 = x` for `x` near `y`. If `(x, t) ↦ Ψ x t` is
differentiable at `(y, 0)` and the curve `t ↦ Ψ y t` has derivative `v` at `0`, then the
derivative of `(x, t) ↦ Ψ x t` at `(y, 0)` is `(u, σ) ↦ u + σ • v`. -/
theorem DifferentiableAt.hasFDerivAt_uncurry_zero
    (hd : DifferentiableAt 𝕜 (fun p : E × 𝕜 ↦ Ψ p.1 p.2) (y, 0))
    (hΨ0 : ∀ᶠ x in 𝓝 y, Ψ x 0 = x) (hv : HasDerivAt (Ψ y) v 0) :
    HasFDerivAt (fun p : E × 𝕜 ↦ Ψ p.1 p.2)
      (ContinuousLinearMap.fst 𝕜 E 𝕜 + (ContinuousLinearMap.snd 𝕜 E 𝕜).smulRight v) (y, 0) := by
  have hD := hd.hasFDerivAt
  refine hD.congr_fderiv (ContinuousLinearMap.prod_ext ?_ ?_)
  · have h := hD.comp y (hasFDerivAt_prodMk_left (𝕜 := 𝕜) y (0 : 𝕜))
    rw [h.unique ((hasFDerivAt_id y).congr_of_eventuallyEq hΨ0)]
    ext u
    simp
  · have h := hD.comp (0 : 𝕜) (hasFDerivAt_prodMk_right (𝕜 := 𝕜) y (0 : 𝕜))
    rw [h.unique hv.hasFDerivAt]
    ext
    simp
