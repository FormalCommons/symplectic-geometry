/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Sublevel sets of a positive definite bilinear form

On a finite-dimensional real normed space, a bilinear form `B` whose quadratic form
`x ↦ B x x` is positive definite controls the norm: `‖x‖ ^ 2 ≤ R * B x x` for some `R ≥ 0`
(`LinearMap.BilinForm.exists_norm_sq_le_mul_apply_self`). Hence its sublevel sets
`{x | B x x ≤ c}` are compact (`LinearMap.BilinForm.isCompact_setOf_apply_self_le`).
-/

public section

namespace LinearMap.BilinForm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {B : LinearMap.BilinForm ℝ E}

/-- On a finite-dimensional real normed space, the quadratic form `x ↦ B x x` of a bilinear form
is continuous. -/
theorem continuous_apply_self (B : LinearMap.BilinForm ℝ E) : Continuous fun x ↦ B x x := by
  have := (LinearMap.toContinuousBilinearMap B).continuous₂.comp
    (continuous_id.prodMk continuous_id)
  simpa only [Function.comp_def, Function.uncurry_apply_pair, id_eq,
    LinearMap.toContinuousBilinearMap_apply] using this

/-- On a finite-dimensional real normed space, a positive definite form `B` bounds the square of
the norm: `‖x‖ ^ 2 ≤ R * B x x` for some `R ≥ 0` and all `x`. -/
theorem exists_norm_sq_le_mul_apply_self (hB : B.toQuadraticMap.PosDef) :
    ∃ R, 0 ≤ R ∧ ∀ x, ‖x‖ ^ 2 ≤ R * B x x := by
  -- `1 / B` is bounded on the unit sphere, where `B` is positive.
  obtain ⟨R, hR⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn
    (f := fun x ↦ (B x x)⁻¹) <| B.continuous_apply_self.continuousOn.inv₀ fun x hx ↦
      (hB x (ne_zero_of_mem_unit_sphere ⟨x, hx⟩)).ne'
  refine ⟨max R 0, le_max_right R 0, fun x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have hpos : 0 < B (‖x‖⁻¹ • x) (‖x‖⁻¹ • x) := hB _ (ne_zero_of_mem_unit_sphere ⟨_, hu⟩)
  have h1 : 1 ≤ max R 0 * B (‖x‖⁻¹ • x) (‖x‖⁻¹ • x) := by
    have := ((le_abs_self _).trans (hR _ hu)).trans (le_max_left R 0)
    rwa [inv_le_iff_one_le_mul₀ hpos] at this
  have hx2 : B (‖x‖⁻¹ • x) (‖x‖⁻¹ • x) * ‖x‖ ^ 2 = B x x := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
  calc ‖x‖ ^ 2 = 1 * ‖x‖ ^ 2 := (one_mul _).symm
    _ ≤ max R 0 * B (‖x‖⁻¹ • x) (‖x‖⁻¹ • x) * ‖x‖ ^ 2 := by gcongr
    _ = max R 0 * B x x := by rw [mul_assoc, hx2]

/-- On a finite-dimensional real normed space, the sublevel sets `{x | B x x ≤ c}` of a positive
definite form `B` are compact. -/
theorem isCompact_setOf_apply_self_le (hB : B.toQuadraticMap.PosDef) (c : ℝ) :
    IsCompact {x | B x x ≤ c} := by
  obtain ⟨R, hR0, hR⟩ := exists_norm_sq_le_mul_apply_self hB
  refine (isCompact_closedBall (0 : E) √(R * c)).of_isClosed_subset
    (isClosed_le B.continuous_apply_self continuous_const) fun x (hx : B x x ≤ c) ↦ ?_
  rw [mem_closedBall_zero_iff]
  exact (le_abs_self _).trans (Real.abs_le_sqrt ((hR x).trans (mul_le_mul_of_nonneg_left hx hR0)))

end LinearMap.BilinForm
