/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Rescaling a nonzero vector to a given norm

For a nonzero vector `x` of a real normed space and `ρ > 0`, the vector `(ρ / ‖x‖) • x` lies on
the sphere of radius `ρ`, and `x` is recovered from it by the factor `‖x‖ / ρ`
(`norm_div_norm_smul_and_norm_div_smul_div_norm_smul`). So `x` lies on the ray through a point of
that sphere. This is Mathlib's `norm_smul_inv_norm'` together with `inv_smul_smul₀`, in the form
in which the scalars are real quotients.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For `ρ > 0` and `x ≠ 0`, the vector `(ρ / ‖x‖) • x` has norm `ρ`, and rescaling it by
`‖x‖ / ρ` gives back `x`. -/
theorem norm_div_norm_smul_and_norm_div_smul_div_norm_smul {ρ : ℝ} (hρ : 0 < ρ) {x : E}
    (hx : x ≠ 0) : ‖(ρ / ‖x‖) • x‖ = ρ ∧ (‖x‖ / ρ) • (ρ / ‖x‖) • x = x := by
  refine ⟨?_, ?_⟩
  · simpa [div_eq_mul_inv] using norm_smul_inv_norm' (𝕜 := ℝ) hρ.le hx
  · rw [← inv_div, inv_smul_smul₀ (div_pos hρ (norm_pos_iff.2 hx)).ne']

end
