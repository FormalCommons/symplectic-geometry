/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global

/-!
# The unit sphere is collared in the closed unit ball

In a real normed space `E`, the closed unit ball with its centre removed is homeomorphic to
`S × [0, 1)`, `S` the unit sphere, through `(z, t) ↦ (1 - t) • z`
(`homeomorphUnitSphereProdIco`). So the inclusion of the unit sphere into the
closed unit ball is collared in the sense of Tau Ceti (`TauCeti.IsCollared`). In any
pseudometric space, the open ball is the complement of the sphere in the closed ball, as ranges
of inclusions (`Metric.range_inclusion_ball_eq_compl`). Together these put the closed unit ball
in the setting of Tau Ceti's relative fundamental class.

On the outer side of the sphere, for `δ > 0`, the annulus `1 ≤ ‖w‖ < 1 + δ` is homeomorphic to
`S × [0, 1)` through `(z, t) ↦ (1 + δ t) • z` (`homeomorphUnitSphereProdIcoAnnulus`). This
collars the boundary circle of a disc removed from a surface.

## Main results

* `homeomorphUnitSphereProdIco`: the homeomorphism from `S × [0, 1)` onto the
  closed unit ball minus its centre.
* `homeomorphUnitSphereProdIcoAnnulus`: the homeomorphism from `S × [0, 1)` onto the annulus
  `1 ≤ ‖w‖ < 1 + δ` outside the unit sphere.
* `Metric.isCollared_inclusion_sphere_closedBall`: the unit sphere is collared in
  the closed unit ball.
* `Metric.range_inclusion_ball_eq_compl`: the open ball is the complement of the sphere in the
  closed ball.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 3.3 (collar
  neighbourhoods of the boundary of a manifold).
-/

public section

noncomputable section

open Set Topology Metric

namespace Metric

/-- In a pseudometric space, the open ball is the complement of the sphere in the closed ball. -/
theorem range_inclusion_ball_eq_compl {α : Type*} [PseudoMetricSpace α] (x : α) (r : ℝ) :
    range (inclusion (ball_subset_closedBall : ball x r ⊆ closedBall x r)) =
      (range (inclusion (sphere_subset_closedBall : sphere x r ⊆ closedBall x r)))ᶜ := by
  ext w
  have hw := mem_closedBall.1 w.property
  simp only [range_inclusion, mem_ofPred_eq, mem_compl_iff, mem_ball, mem_sphere]
  exact ⟨ne_of_lt, fun h ↦ lt_of_le_of_ne hw h⟩

end Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball with its centre removed is `S × [0, 1)`, `S` the unit sphere, through
`(z, t) ↦ (1 - t) • z`. -/
def homeomorphUnitSphereProdIco :
    sphere (0 : E) 1 × Ico (0 : ℝ) 1 ≃ₜ ({w | (w : E) ≠ 0} : Set (closedBall (0 : E) 1)) where
  toFun p := ⟨⟨(1 - (p.2 : ℝ)) • (p.1 : E), by
      rw [mem_closedBall_zero_iff, norm_smul, norm_eq_of_mem_sphere p.1, mul_one,
        Real.norm_of_nonneg (by linarith [p.2.property.2])]
      linarith [p.2.property.1]⟩, by
    simp only [mem_ofPred_eq, ne_eq, smul_eq_zero, not_or]
    exact ⟨by linarith [p.2.property.2], ne_zero_of_mem_unit_sphere p.1⟩⟩
  invFun w := (⟨‖(w.val : E)‖⁻¹ • (w.val : E), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 w.property)]⟩,
    ⟨1 - ‖(w.val : E)‖, by linarith [mem_closedBall_zero_iff.1 w.val.property],
      by linarith [norm_pos_iff.2 w.property]⟩)
  left_inv p := by
    have ht : 0 < 1 - (p.2 : ℝ) := by linarith [p.2.property.2]
    have hn : ‖(1 - (p.2 : ℝ)) • (p.1 : E)‖ = 1 - p.2 := by
      rw [norm_smul, norm_eq_of_mem_sphere p.1, mul_one, Real.norm_of_nonneg ht.le]
    ext
    · simp only [hn, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    · simp only [hn, sub_sub_cancel]
  right_inv w := by
    ext
    simp only [sub_sub_cancel, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 w.property), one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hn : Continuous fun w : ({w | (w : E) ≠ 0} : Set (closedBall (0 : E) 1)) ↦
        ‖(w.val : E)‖ := by fun_prop
    exact (((hn.inv₀ fun w ↦ norm_ne_zero_iff.2 w.property).smul (by fun_prop)).subtype_mk _).prodMk
      ((continuous_const.sub hn).subtype_mk _)

@[simp]
theorem coe_homeomorphUnitSphereProdIco_apply (p : sphere (0 : E) 1 × Ico (0 : ℝ) 1) :
    ((homeomorphUnitSphereProdIco p : closedBall (0 : E) 1) : E) = (1 - (p.2 : ℝ)) • (p.1 : E) :=
  (rfl)

@[simp]
theorem coe_homeomorphUnitSphereProdIco_symm_apply_fst
    (w : ({w | (w : E) ≠ 0} : Set (closedBall (0 : E) 1))) :
    ((homeomorphUnitSphereProdIco.symm w).1 : E) = ‖(w.val : E)‖⁻¹ • (w.val : E) :=
  (rfl)

@[simp]
theorem coe_homeomorphUnitSphereProdIco_symm_apply_snd
    (w : ({w | (w : E) ≠ 0} : Set (closedBall (0 : E) 1))) :
    ((homeomorphUnitSphereProdIco.symm w).2 : ℝ) = 1 - ‖(w.val : E)‖ :=
  (rfl)

/-- The annulus `1 ≤ ‖w‖ < 1 + δ` outside the unit sphere is `S × [0, 1)`, `S` the unit sphere,
through `(z, t) ↦ (1 + δ t) • z`, for `δ > 0`. -/
def homeomorphUnitSphereProdIcoAnnulus {δ : ℝ} (hδ : 0 < δ) :
    sphere (0 : E) 1 × Ico (0 : ℝ) 1 ≃ₜ {w : E | 1 ≤ ‖w‖ ∧ ‖w‖ < 1 + δ} where
  toFun p := ⟨(1 + δ * p.2) • (p.1 : E), by
    have h0 : 0 ≤ δ * p.2 := mul_nonneg hδ.le p.2.property.1
    rw [mem_ofPred_eq, norm_smul, norm_eq_of_mem_sphere p.1, mul_one,
      Real.norm_of_nonneg (by linarith)]
    constructor <;> nlinarith [p.2.property.2]⟩
  invFun w := (⟨‖(w : E)‖⁻¹ • (w : E), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (by linarith [w.property.1])]⟩,
    ⟨(‖(w : E)‖ - 1) / δ, div_nonneg (by linarith [w.property.1]) hδ.le,
      (div_lt_one hδ).2 (by linarith [w.property.2])⟩)
  left_inv p := by
    have ht : 0 < 1 + δ * p.2 := by nlinarith [p.2.property.1]
    have hn : ‖(1 + δ * p.2) • (p.1 : E)‖ = 1 + δ * p.2 := by
      rw [norm_smul, norm_eq_of_mem_sphere p.1, mul_one, Real.norm_of_nonneg ht.le]
    ext
    · simp only [hn, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    · simp only [hn, add_sub_cancel_left, mul_div_cancel_left₀ _ hδ.ne']
  right_inv w := by
    ext
    simp only [mul_div_cancel₀ _ hδ.ne', add_sub_cancel, smul_smul,
      mul_inv_cancel₀ (show ‖(w : E)‖ ≠ 0 by linarith [w.property.1]), one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hn : Continuous fun w : {w : E | 1 ≤ ‖w‖ ∧ ‖w‖ < 1 + δ} ↦ ‖(w : E)‖ := by fun_prop
    exact (((hn.inv₀ fun w ↦ by linarith [w.property.1]).smul (by fun_prop)).subtype_mk _).prodMk
      (((hn.sub continuous_const).div_const δ).subtype_mk _)

@[simp]
theorem coe_homeomorphUnitSphereProdIcoAnnulus_apply {δ : ℝ} (hδ : 0 < δ)
    (p : sphere (0 : E) 1 × Ico (0 : ℝ) 1) :
    (homeomorphUnitSphereProdIcoAnnulus hδ p : E) = (1 + δ * p.2) • (p.1 : E) :=
  (rfl)

@[simp]
theorem coe_homeomorphUnitSphereProdIcoAnnulus_symm_apply_fst {δ : ℝ} (hδ : 0 < δ)
    (w : {w : E | 1 ≤ ‖w‖ ∧ ‖w‖ < 1 + δ}) :
    (((homeomorphUnitSphereProdIcoAnnulus hδ).symm w).1 : E) = ‖(w : E)‖⁻¹ • (w : E) :=
  (rfl)

@[simp]
theorem coe_homeomorphUnitSphereProdIcoAnnulus_symm_apply_snd {δ : ℝ} (hδ : 0 < δ)
    (w : {w : E | 1 ≤ ‖w‖ ∧ ‖w‖ < 1 + δ}) :
    (((homeomorphUnitSphereProdIcoAnnulus hδ).symm w).2 : ℝ) = (‖(w : E)‖ - 1) / δ :=
  (rfl)

namespace Metric

/-- **The unit sphere is collared in the closed unit ball**, by `(z, t) ↦ (1 - t) • z`. -/
theorem isCollared_inclusion_sphere_closedBall :
    TauCeti.IsCollared
      (inclusion (sphere_subset_closedBall : sphere (0 : E) 1 ⊆ closedBall 0 1)) :=
  TauCeti.isCollared_iff.2 ⟨fun p ↦ (homeomorphUnitSphereProdIco p).val,
    ⟨(isOpen_compl_singleton.preimage continuous_subtypeVal).isOpenEmbedding_subtypeVal.comp
      homeomorphUnitSphereProdIco.isOpenEmbedding, fun z ↦ by
        ext
        simp⟩⟩

end Metric
