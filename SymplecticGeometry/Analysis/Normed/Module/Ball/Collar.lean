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

In a real normed space `E`, with `S` the unit sphere, the map `(z, t) ↦ (1 + c t) • z` is a
homeomorphism of `S × [0, 1)` onto the shell `{w | (‖w‖ - 1) / c ∈ [0, 1)}`, for every `c ≠ 0`
with `-1 ≤ c` (`homeomorphUnitSphereProdIco`). It is Mathlib's polar coordinates
`homeomorphUnitSphereProd` restricted to a range of radii, written out directly.

For `c = -1` the shell is the closed unit ball minus its centre, so the inclusion of the unit
sphere into the closed unit ball is collared in the sense of Tau Ceti (`TauCeti.IsCollared`). In
any pseudometric space, the open ball is the complement of the sphere in the closed ball, as
ranges of inclusions (`Metric.range_inclusion_ball_eq_compl`). Together these put the closed unit
ball in the setting of Tau Ceti's relative fundamental class.

For `c = δ > 0` the shell is the annulus `1 ≤ ‖w‖ < 1 + δ` outside the unit sphere. This collars
the boundary circle of a disc removed from a surface.

## Main results

* `homeomorphUnitSphereProdIco`: the homeomorphism from `S × [0, 1)` onto the shell
  `(‖w‖ - 1) / c ∈ [0, 1)` around the unit sphere.
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {c : ℝ}

/-- For `-1 ≤ c` and `t ∈ [0, 1)`, the radius `1 + c t` is positive. -/
private lemma one_add_mul_pos (hc : -1 ≤ c) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : 0 < 1 + c * t := by
  nlinarith [ht.1, ht.2]

omit [NormedSpace ℝ E] in
/-- A point of the shell `(‖w‖ - 1) / c ∈ [0, 1)`, for `-1 ≤ c` and `c ≠ 0`, is not the
centre. -/
private lemma norm_pos_of_div_mem_Ico (hc : -1 ≤ c) (hc₀ : c ≠ 0) {w : E}
    (hw : (‖w‖ - 1) / c ∈ Ico (0 : ℝ) 1) : 0 < ‖w‖ := by
  have h := one_add_mul_pos hc hw
  rwa [mul_div_cancel₀ _ hc₀, add_sub_cancel] at h

/-- The shell `(‖w‖ - 1) / c ∈ [0, 1)` around the unit sphere is `S × [0, 1)`, `S` the unit
sphere, through `(z, t) ↦ (1 + c t) • z`, for `-1 ≤ c` and `c ≠ 0`. For `c = -1` the shell is
the closed unit ball minus its centre; for `c > 0` it is the annulus `1 ≤ ‖w‖ < 1 + c`. -/
def homeomorphUnitSphereProdIco (hc : -1 ≤ c) (hc₀ : c ≠ 0) :
    sphere (0 : E) 1 × Ico (0 : ℝ) 1 ≃ₜ {w : E | (‖w‖ - 1) / c ∈ Ico (0 : ℝ) 1} where
  toFun p := ⟨(1 + c * p.2) • (p.1 : E), by
    rw [mem_ofPred_eq, norm_smul, norm_eq_of_mem_sphere p.1, mul_one,
      Real.norm_of_nonneg (one_add_mul_pos hc p.2.property).le, add_sub_cancel_left,
      mul_div_cancel_left₀ _ hc₀]
    exact p.2.property⟩
  invFun w := (⟨‖(w : E)‖⁻¹ • (w : E), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ (norm_pos_of_div_mem_Ico hc hc₀ w.property).ne']⟩,
    ⟨(‖(w : E)‖ - 1) / c, w.property⟩)
  left_inv p := by
    have ht := one_add_mul_pos hc p.2.property
    have hn : ‖(1 + c * p.2) • (p.1 : E)‖ = 1 + c * p.2 := by
      rw [norm_smul, norm_eq_of_mem_sphere p.1, mul_one, Real.norm_of_nonneg ht.le]
    ext
    · simp only [hn, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
    · simp only [hn, add_sub_cancel_left, mul_div_cancel_left₀ _ hc₀]
  right_inv w := by
    ext
    simp only [mul_div_cancel₀ _ hc₀, add_sub_cancel, smul_smul,
      mul_inv_cancel₀ (norm_pos_of_div_mem_Ico hc hc₀ w.property).ne', one_smul]
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hn : Continuous fun w : {w : E | (‖w‖ - 1) / c ∈ Ico (0 : ℝ) 1} ↦ ‖(w : E)‖ := by
      fun_prop
    exact (((hn.inv₀ fun w ↦ (norm_pos_of_div_mem_Ico hc hc₀ w.property).ne').smul
      (by fun_prop)).subtype_mk _).prodMk (((hn.sub continuous_const).div_const c).subtype_mk _)

@[simp]
theorem coe_homeomorphUnitSphereProdIco_apply (hc : -1 ≤ c) (hc₀ : c ≠ 0)
    (p : sphere (0 : E) 1 × Ico (0 : ℝ) 1) :
    (homeomorphUnitSphereProdIco hc hc₀ p : E) = (1 + c * p.2) • (p.1 : E) :=
  (rfl)

@[simp]
theorem coe_homeomorphUnitSphereProdIco_symm_apply_fst (hc : -1 ≤ c) (hc₀ : c ≠ 0)
    (w : {w : E | (‖w‖ - 1) / c ∈ Ico (0 : ℝ) 1}) :
    (((homeomorphUnitSphereProdIco hc hc₀).symm w).1 : E) = ‖(w : E)‖⁻¹ • (w : E) :=
  (rfl)

@[simp]
theorem coe_homeomorphUnitSphereProdIco_symm_apply_snd (hc : -1 ≤ c) (hc₀ : c ≠ 0)
    (w : {w : E | (‖w‖ - 1) / c ∈ Ico (0 : ℝ) 1}) :
    (((homeomorphUnitSphereProdIco hc hc₀).symm w).2 : ℝ) = (‖(w : E)‖ - 1) / c :=
  (rfl)

namespace Metric

/-- **The unit sphere is collared in the closed unit ball**, by `(z, t) ↦ (1 - t) • z`. -/
theorem isCollared_inclusion_sphere_closedBall :
    TauCeti.IsCollared
      (inclusion (sphere_subset_closedBall : sphere (0 : E) 1 ⊆ closedBall 0 1)) := by
  have hc₀ : (-1 : ℝ) ≠ 0 := by norm_num
  have hsub : {w : E | (‖w‖ - 1) / -1 ∈ Ico (0 : ℝ) 1} ⊆ closedBall 0 1 := fun w hw ↦ by
    have := hw.1
    rwa [div_neg, div_one, neg_nonneg, sub_nonpos, ← mem_closedBall_zero_iff] at this
  have hopen : IsOpen (((↑) : closedBall (0 : E) 1 → E) ⁻¹'
      {w | (‖w‖ - 1) / -1 ∈ Ico (0 : ℝ) 1}) := by
    convert (isOpen_compl_singleton (x := (0 : E))).preimage continuous_subtypeVal using 1
    ext w
    simp only [mem_preimage, mem_ofPred_eq, div_neg, div_one, neg_sub, mem_Ico, sub_nonneg,
      sub_lt_self_iff, norm_pos_iff, mem_compl_iff, mem_singleton_iff,
      mem_closedBall_zero_iff.1 w.property, true_and]
  refine TauCeti.isCollared_iff.2 ⟨inclusion hsub ∘ homeomorphUnitSphereProdIco le_rfl hc₀,
    (IsOpenEmbedding.inclusion hsub hopen).comp (homeomorphUnitSphereProdIco _ _).isOpenEmbedding,
    fun z ↦ ?_⟩
  ext
  simp

end Metric
