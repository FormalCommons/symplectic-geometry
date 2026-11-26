/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Inequalities between vanishing derivatives at second order

Let `D : E → E →L[ℝ] ℝ` (typically the derivative of a function) and `Y : E → E` (a vector
field) both vanish at `x₀` and be differentiable there, with derivatives `B` and `A`. Both
sides of an inequality `K * (D u e) ^ 2 ≤ D u (Y u)`, for `u` near `x₀`, vanish to second order
at `x₀`; dividing by `s ^ 2` along `u = x₀ + s • v` and letting `s → 0`
gives `K * (B v e) ^ 2 ≤ B v (A v)`
(`HasFDerivAt.mul_sq_apply_le_apply_apply_of_eventually`).

This is the step by which a gradient-like inequality at a nondegenerate critical point passes to
the linearizations of the function and of the field there. The proof differentiates along the
lines `s ↦ x₀ + s • v` and passes to the limit in the slopes, as Tau Ceti's
`HasFDerivAt.norm_apply_le_mul_norm_apply` does for an inequality between norms.
-/

public section

open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **An inequality between vanishing derivatives, at second order.** Let `D : E → E →L[ℝ] ℝ` and
`Y : E → E` vanish at `x₀`, with derivatives `B` and `A` there. If
`K * (D u e) ^ 2 ≤ D u (Y u)` for every `u` near `x₀`, then `K * (B v e) ^ 2 ≤ B v (A v)` for
every `v`. -/
theorem HasFDerivAt.mul_sq_apply_le_apply_apply_of_eventually {D : E → E →L[ℝ] ℝ} {Y : E → E}
    {x₀ : E} {B : E →L[ℝ] E →L[ℝ] ℝ} {A : E →L[ℝ] E} (hD : HasFDerivAt D B x₀) (hD₀ : D x₀ = 0)
    (hY : HasFDerivAt Y A x₀) (hY₀ : Y x₀ = 0) {K : ℝ} {e : E}
    (h : ∀ᶠ u in 𝓝 x₀, K * D u e ^ 2 ≤ D u (Y u)) (v : E) :
    K * B v e ^ 2 ≤ B v (A v) := by
  have hℓ : HasDerivAt (fun s : ℝ ↦ x₀ + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x₀
  have hℓ₀ : x₀ + (0 : ℝ) • v = x₀ := by simp
  -- The slopes `s⁻¹ • D (x₀ + s • v)` and `s⁻¹ • Y (x₀ + s • v)` tend to `B v` and `A v`.
  have hDℓ := (hD.comp_hasDerivAt_of_eq 0 hℓ hℓ₀.symm).tendsto_slope_zero
  have hYℓ := (hY.comp_hasDerivAt_of_eq 0 hℓ hℓ₀.symm).tendsto_slope_zero
  simp only [Function.comp_apply, zero_add, hℓ₀, hD₀, hY₀, sub_zero] at hDℓ hYℓ
  have hlim₁ : Tendsto (fun t : ℝ ↦ K * (t⁻¹ • D (x₀ + t • v)) e ^ 2) (𝓝[≠] 0)
      (𝓝 (K * B v e ^ 2)) :=
    (((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto _).comp hDℓ).pow 2 |>.const_mul K
  have hlim₂ : Tendsto (fun t : ℝ ↦ (t⁻¹ • D (x₀ + t • v)) (t⁻¹ • Y (x₀ + t • v))) (𝓝[≠] 0)
      (𝓝 (B v (A v))) :=
    (isBoundedBilinearMap_apply.continuous.tendsto _).comp (hDℓ.prodMk_nhds hYℓ)
  refine le_of_tendsto_of_tendsto hlim₁ hlim₂ ?_
  have hℓt : Tendsto (fun s : ℝ ↦ x₀ + s • v) (𝓝[≠] 0) (𝓝 x₀) := by
    have := hℓ.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
    rwa [hℓ₀] at this
  filter_upwards [hℓt.eventually h] with t ht
  simp only [smul_apply, smul_eq_mul, map_smul]
  nlinarith [mul_le_mul_of_nonneg_left ht (sq_nonneg t⁻¹)]

end
