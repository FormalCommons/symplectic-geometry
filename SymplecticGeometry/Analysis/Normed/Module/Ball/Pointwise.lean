/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Scaling balls and spheres about the origin

A complement to Mathlib's `Mathlib.Analysis.Normed.Module.Ball.Pointwise`: in a normed space
over a normed field, scaling by `c⁻¹` sends the ball of radius `‖c‖ * r` about `0` onto the ball
of radius `r` about `0`, stated pointwise; and in a real normed space, scaling by `r⁻¹` sends the
sphere of radius `r > 0` about `0` into the unit sphere. Over a nontrivially normed field, only `0`
has all its multiples in one closed ball about `0`. It is kept in the root namespace, next to
Mathlib's `smul_ball`, so that it can move upstream unchanged.

## Main results

* `inv_smul_mem_ball_zero_iff`: for `c ≠ 0`, `c⁻¹ • z` lies in `ball 0 r` exactly when `z` lies in
  `ball 0 (‖c‖ * r)`.
* `inv_smul_mem_sphere_one_of_norm_eq`: for `0 < r` and `‖z‖ = r`, `r⁻¹ • z` lies in
  `sphere 0 1`.
* `eq_zero_of_forall_smul_mem_closedBall`: a vector whose multiples all lie in `closedBall 0 r`
  is `0`.
-/

public section

open Metric

variable {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- For `c ≠ 0`, the point `c⁻¹ • z` lies in the ball of radius `r` about `0` if and only if `z`
lies in the ball of radius `‖c‖ * r` about `0`. -/
theorem inv_smul_mem_ball_zero_iff {c : 𝕜} (hc : c ≠ 0) {z : E} {r : ℝ} :
    c⁻¹ • z ∈ ball (0 : E) r ↔ z ∈ ball (0 : E) (‖c‖ * r) := by
  simp [norm_smul, inv_mul_lt_iff₀ (norm_pos_iff.2 hc)]

/-- In a real normed space, for `0 < r` and `‖z‖ = r`, the point `r⁻¹ • z` lies on the unit
sphere about `0`. -/
theorem inv_smul_mem_sphere_one_of_norm_eq {F : Type*} [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] {r : ℝ} (hr : 0 < r) {z : F} (hz : ‖z‖ = r) :
    r⁻¹ • z ∈ sphere (0 : F) 1 := by
  rw [mem_sphere_zero_iff_norm, norm_smul, hz, Real.norm_eq_abs, abs_inv, abs_of_pos hr,
    inv_mul_cancel₀ hr.ne']

/-- Over a nontrivially normed field, a vector all of whose multiples lie in one closed ball about
`0` is `0`. -/
theorem eq_zero_of_forall_smul_mem_closedBall {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] {z : F} {r : ℝ}
    (h : ∀ c : 𝕜, c • z ∈ closedBall (0 : F) r) : z = 0 := by
  by_contra hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 (r / ‖z‖)
  have hmem := h c
  rw [mem_closedBall_zero_iff, norm_smul] at hmem
  exact (div_lt_iff₀ hpos).1 hc |>.not_ge hmem

end
