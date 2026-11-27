/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.Convex

/-!
# Interpolating two maps by a scalar function

For maps `s₁ s₂ : E → F` and a scalar function `c : E → ℝ`, this file studies the map
`y ↦ s₁ y + c y • (s₂ y - s₁ y)`, which equals `s₁` where `c = 0` and `s₂` where `c = 1`. Such
maps glue two local solutions by a cutoff, as in the proof of holonomic approximation in
[EliashbergMishachev2002], Chapter 3.

## Main results

* `HasFDerivAt.add_smul_sub`: the derivative of the interpolated map is
  `s₁' + c x • (s₂' - s₁') + c'.smulRight (s₂ x - s₁ x)`.
* `SymplecticGeometry.norm_add_smul_sub_sub_le_max`: for `0 ≤ t ≤ 1`, the point `u + t • (v - u)`
  is at most as far from `w` as the farther of `u` and `v`.
* `SymplecticGeometry.norm_fderiv_add_smul_sub_sub_le`: where `0 ≤ c x ≤ 1` and
  `‖fderiv ℝ c x‖ ≤ L`, the derivative of the interpolated map is as close to a given `A` as the
  farther of the derivatives of `s₁` and `s₂`, up to `L * ‖s₂ x - s₁ x‖`.
* `SymplecticGeometry.norm_fderiv_add_smul_sub_sub_apply_le`: the same bound on each vector `w`,
  with the error `L * ‖w‖ * ‖s₂ x - s₁ x‖`.
* `SymplecticGeometry.norm_fderiv_add_comp_smul_sub_sub_le`: the case `c = χ ∘ ℓ` of a cutoff
  `χ : ℝ → ℝ` in a linear coordinate `ℓ`, with the error `L * ‖ℓ‖ * ‖s₂ x - s₁ x‖`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The derivative of the map `y ↦ s₁ y + c y • (s₂ y - s₁ y)` that interpolates between `s₁`
and `s₂` by the scalar function `c`. -/
theorem HasFDerivAt.add_smul_sub {s₁ s₂ : E → F} {s₁' s₂' : E →L[ℝ] F} {c : E → ℝ}
    {c' : E →L[ℝ] ℝ} {x : E} (h₁ : HasFDerivAt s₁ s₁' x) (h₂ : HasFDerivAt s₂ s₂' x)
    (hc : HasFDerivAt c c' x) :
    HasFDerivAt (fun y ↦ s₁ y + c y • (s₂ y - s₁ y))
      (s₁' + c x • (s₂' - s₁') + c'.smulRight (s₂ x - s₁ x)) x :=
  (h₁.add (hc.smul (h₂.sub h₁))).congr_fderiv (add_assoc _ _ _).symm

namespace SymplecticGeometry

/-- For `0 ≤ t ≤ 1`, the point `u + t • (v - u)` of the segment from `u` to `v` is at most as far
from `w` as the farther of `u` and `v`. -/
theorem norm_add_smul_sub_sub_le_max (u v w : F) {t : ℝ} (h₀ : 0 ≤ t) (h₁ : t ≤ 1) :
    ‖u + t • (v - u) - w‖ ≤ max ‖u - w‖ ‖v - w‖ := by
  have h := (convexOn_norm (convex_univ (𝕜 := ℝ) (E := F))).le_on_segment' trivial trivial
    (sub_nonneg.2 h₁) h₀ (sub_add_cancel 1 t) (x := u - w) (y := v - w)
  convert h using 2
  simp only [sub_smul, one_smul, smul_sub]
  abel

/-- If `0 ≤ c x ≤ 1` and `‖fderiv ℝ c x‖ ≤ L`, then the derivative at `x` of
`y ↦ s₁ y + c y • (s₂ y - s₁ y)` is at distance from `A` at most the larger of the distances of
`fderiv ℝ s₁ x` and `fderiv ℝ s₂ x` from `A`, plus `L * ‖s₂ x - s₁ x‖`. -/
theorem norm_fderiv_add_smul_sub_sub_le {s₁ s₂ : E → F} {c : E → ℝ} (A : E →L[ℝ] F) {x : E}
    {L : ℝ} (h₁ : DifferentiableAt ℝ s₁ x) (h₂ : DifferentiableAt ℝ s₂ x)
    (hc : DifferentiableAt ℝ c x) (hc₀ : 0 ≤ c x) (hc₁ : c x ≤ 1) (hL : ‖fderiv ℝ c x‖ ≤ L) :
    ‖fderiv ℝ (fun y ↦ s₁ y + c y • (s₂ y - s₁ y)) x - A‖ ≤
      max ‖fderiv ℝ s₁ x - A‖ ‖fderiv ℝ s₂ x - A‖ + L * ‖s₂ x - s₁ x‖ := by
  rw [(h₁.hasFDerivAt.add_smul_sub h₂.hasFDerivAt hc.hasFDerivAt).fderiv, add_sub_right_comm]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_add_smul_sub_sub_le_max _ _ _ hc₀ hc₁
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    gcongr

/-- The value on a vector `w` of `norm_fderiv_add_smul_sub_sub_le`: if `0 ≤ c x ≤ 1` and
`‖fderiv ℝ c x‖ ≤ L`, then the derivative at `x` of `y ↦ s₁ y + c y • (s₂ y - s₁ y)`, minus `A`,
has norm on `w` at most the larger of the norms on `w` of `fderiv ℝ s₁ x - A` and
`fderiv ℝ s₂ x - A`, plus `L * ‖w‖ * ‖s₂ x - s₁ x‖`. -/
theorem norm_fderiv_add_smul_sub_sub_apply_le {s₁ s₂ : E → F} {c : E → ℝ} (A : E →L[ℝ] F)
    {x : E} {L : ℝ} (h₁ : DifferentiableAt ℝ s₁ x) (h₂ : DifferentiableAt ℝ s₂ x)
    (hc : DifferentiableAt ℝ c x) (hc₀ : 0 ≤ c x) (hc₁ : c x ≤ 1) (hL : ‖fderiv ℝ c x‖ ≤ L)
    (w : E) :
    ‖(fderiv ℝ (fun y ↦ s₁ y + c y • (s₂ y - s₁ y)) x - A) w‖ ≤
      max ‖(fderiv ℝ s₁ x - A) w‖ ‖(fderiv ℝ s₂ x - A) w‖ + L * ‖w‖ * ‖s₂ x - s₁ x‖ := by
  rw [(h₁.hasFDerivAt.add_smul_sub h₂.hasFDerivAt hc.hasFDerivAt).fderiv]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [add_sub_right_comm]
  refine (norm_add_le _ _).trans (add_le_add (norm_add_smul_sub_sub_le_max _ _ _ hc₀ hc₁) ?_)
  rw [norm_smul]
  gcongr
  exact ((fderiv ℝ c x).le_opNorm w).trans (by gcongr)

/-- The case of `norm_fderiv_add_smul_sub_sub_le` where the scalar function is a cutoff `χ` in a
linear coordinate `ℓ`: if `0 ≤ χ (ℓ x) ≤ 1` and `|deriv χ (ℓ x)| ≤ L`, then the derivative at `x`
of `y ↦ s₁ y + χ (ℓ y) • (s₂ y - s₁ y)` is at distance from `A` at most the larger of the
distances of `fderiv ℝ s₁ x` and `fderiv ℝ s₂ x` from `A`, plus `L * ‖ℓ‖ * ‖s₂ x - s₁ x‖`. -/
theorem norm_fderiv_add_comp_smul_sub_sub_le {s₁ s₂ : E → F} {χ : ℝ → ℝ} (ℓ : E →L[ℝ] ℝ)
    (A : E →L[ℝ] F) {x : E} {L : ℝ} (h₁ : DifferentiableAt ℝ s₁ x)
    (h₂ : DifferentiableAt ℝ s₂ x) (hχ : DifferentiableAt ℝ χ (ℓ x)) (hχ₀ : 0 ≤ χ (ℓ x))
    (hχ₁ : χ (ℓ x) ≤ 1) (hL : |deriv χ (ℓ x)| ≤ L) :
    ‖fderiv ℝ (fun y ↦ s₁ y + χ (ℓ y) • (s₂ y - s₁ y)) x - A‖ ≤
      max ‖fderiv ℝ s₁ x - A‖ ‖fderiv ℝ s₂ x - A‖ + L * ‖ℓ‖ * ‖s₂ x - s₁ x‖ := by
  have hc : HasFDerivAt (fun y ↦ χ (ℓ y)) (deriv χ (ℓ x) • ℓ) x :=
    hχ.hasDerivAt.comp_hasFDerivAt x ℓ.hasFDerivAt
  refine norm_fderiv_add_smul_sub_sub_le A h₁ h₂ hc.differentiableAt hχ₀ hχ₁ ?_
  rw [hc.fderiv, norm_smul, Real.norm_eq_abs]
  gcongr

end SymplecticGeometry

end
