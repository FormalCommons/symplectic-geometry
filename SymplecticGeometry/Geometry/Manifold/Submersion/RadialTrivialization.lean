/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.Constructions
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import SymplecticGeometry.Analysis.SpecialFunctions.SmoothTransition

/-!
# Local triviality of proper submersions by transport along rays

A proper submersion `f : P → B` is locally trivial: over a small ball of a chart of `B` around
`b₀`, transport by an Ehresmann connection along the rays from the centre `b₀` identifies each
fibre with the fibre over `b₀`. This file is the home of that construction, and starts with the
smooth family of rays along which the transport runs.

A ray `t ↦ c + t • (y - c)` of a chart, for `t ∈ [0, 1]`, is not a smooth curve on all of `ℝ`
that stays in the chart, while parallel transport is set up for smooth curves `ℝ → B`. So the
rays are reparametrized by a fixed smooth bounded function `SymplecticGeometry.rayParam : ℝ → ℝ`,
equal to the identity on `Set.Icc 0 1` and with values in `(-1, 2)`, chosen with
`SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`.

For `b₀ : B` with chart point `c = extChartAt J b₀ b₀` and a radius `r` such that the ball of
radius `2 * r` around `c` lies in the chart target, `chartBall J b₀ r` is the open set of points
of the chart source whose chart point lies in the ball of radius `r` around `c`, and
`chartRay J b₀ (b, u)` is `(extChartAt J b₀).symm (c + rayParam u • (extChartAt J b₀ b - c))`.
On `chartBall J b₀ r × ℝ` this family is smooth (`contMDiff_chartRay_chartBall`), its curves
stay in the chart source (`chartRay_mem_source`), where they read as affine rays
(`extChartAt_chartRay`); they start at `b₀` (`chartRay_zero`), end at `b` (`chartRay_one`) and
follow the ray on `[0, 1]` (`chartRay_of_mem_Icc`).

`chartBall` and `chartRay` adapt Tau Ceti's `OpenPartialHomeomorph.chartBall` and the straight
lines of `OpenPartialHomeomorph.chartBallHomotopy`, from an open partial homeomorphism and
continuous maps to the extended chart `extChartAt J b₀` and smooth maps.

## Main definitions

* `SymplecticGeometry.rayParam`: a smooth bounded function `ℝ → ℝ` that is the identity on
  `[0, 1]`.
* `SymplecticGeometry.chartBall`: the preimage, in the chart source at `b₀`, of a ball around
  the chart point of `b₀`, as an open set of `B`.
* `SymplecticGeometry.chartRay`: the family of reparametrized rays of the chart at `b₀`.

## Main results

* `SymplecticGeometry.contMDiff_chartRay_chartBall`: the family of rays is smooth on
  `chartBall J b₀ r × ℝ`.
* `SymplecticGeometry.exists_pos_ball_two_mul_subset_extChartAt_target`: radii for which it is
  defined exist.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §6.1,
  Exercise 6.1.1.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace SymplecticGeometry

/-! ### The reparametrization of the rays -/

/-- A smooth function `ℝ → ℝ` that is the identity on `[0, 1]` and takes its values in
`(-1, 2)`, chosen by `SymplecticGeometry.exists_contDiff_eqOn_id_Icc_mem_Ioo`. -/
def rayParam : ℝ → ℝ :=
  (exists_contDiff_eqOn_id_Icc_mem_Ioo (zero_le_one' ℝ) one_pos).choose

private theorem rayParam_spec :
    ContDiff ℝ ∞ rayParam ∧ EqOn rayParam id (Icc 0 1) ∧
      (∀ t, rayParam t ∈ Ioo (0 - 1) (1 + 1)) ∧
      ∀ t ∉ Ioo (0 - 1 : ℝ) (1 + 1), rayParam t = (0 + 1) / 2 :=
  (exists_contDiff_eqOn_id_Icc_mem_Ioo (zero_le_one' ℝ) one_pos).choose_spec

theorem contDiff_rayParam {n : ℕ∞} : ContDiff ℝ n rayParam :=
  rayParam_spec.1.of_le (WithTop.coe_le_coe.2 le_top)

theorem rayParam_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : rayParam t = t :=
  rayParam_spec.2.1 ht

@[simp]
theorem rayParam_zero : rayParam 0 = 0 := rayParam_of_mem_Icc (left_mem_Icc.2 zero_le_one)

@[simp]
theorem rayParam_one : rayParam 1 = 1 := rayParam_of_mem_Icc (right_mem_Icc.2 zero_le_one)

theorem abs_rayParam_le (t : ℝ) : |rayParam t| ≤ 2 := by
  obtain ⟨h₁, h₂⟩ := rayParam_spec.2.2.1 t
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-! ### The rays of a chart -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
  {B : Type*} [TopologicalSpace B] [ChartedSpace G B]

/-- The points of the chart source at `b₀` whose chart point lies in the ball of radius `r`
around the chart point of `b₀`, as an open set of `B`. -/
def chartBall (b₀ : B) (r : ℝ) : TopologicalSpace.Opens B :=
  ⟨(extChartAt J b₀).source ∩ extChartAt J b₀ ⁻¹' Metric.ball (extChartAt J b₀ b₀) r,
    isOpen_extChartAt_preimage' b₀ Metric.isOpen_ball⟩

theorem mem_chartBall_iff {b₀ b : B} {r : ℝ} :
    b ∈ chartBall J b₀ r ↔
      b ∈ (extChartAt J b₀).source ∧ extChartAt J b₀ b ∈ Metric.ball (extChartAt J b₀ b₀) r :=
  Iff.rfl

theorem mem_chartBall_self (b₀ : B) {r : ℝ} (hr : 0 < r) : b₀ ∈ chartBall J b₀ r :=
  (mem_chartBall_iff J).2 ⟨mem_extChartAt_source b₀, Metric.mem_ball_self hr⟩

theorem chartBall_mem_nhds (b₀ : B) {r : ℝ} (hr : 0 < r) : (chartBall J b₀ r : Set B) ∈ 𝓝 b₀ :=
  (chartBall J b₀ r).isOpen.mem_nhds (mem_chartBall_self J b₀ hr)

/-- The family of rays of the chart at `b₀`, reparametrized by `SymplecticGeometry.rayParam`:
the curve `u ↦ chartRay J b₀ (b, u)` is `(extChartAt J b₀).symm (c + rayParam u • (y - c))`,
where `c` and `y` are the chart points of `b₀` and `b`. -/
def chartRay (b₀ : B) (p : B × ℝ) : B :=
  (extChartAt J b₀).symm
    (extChartAt J b₀ b₀ + rayParam p.2 • (extChartAt J b₀ p.1 - extChartAt J b₀ b₀))

theorem chartRay_def (b₀ : B) (p : B × ℝ) :
    chartRay J b₀ p = (extChartAt J b₀).symm
      (extChartAt J b₀ b₀ + rayParam p.2 • (extChartAt J b₀ p.1 - extChartAt J b₀ b₀)) :=
  (rfl)

@[simp]
theorem chartRay_zero (b₀ b : B) : chartRay J b₀ (b, 0) = b₀ := by
  rw [chartRay_def, rayParam_zero, zero_smul, add_zero, extChartAt_to_inv]

theorem chartRay_one {b₀ b : B} (hb : b ∈ (extChartAt J b₀).source) :
    chartRay J b₀ (b, 1) = b := by
  rw [chartRay_def, rayParam_one, one_smul, add_sub_cancel, (extChartAt J b₀).left_inv hb]

/-- On `[0, 1]`, the curves of `chartRay J b₀` are the rays of the chart at `b₀`. -/
theorem chartRay_of_mem_Icc (b₀ b : B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    chartRay J b₀ (b, t) = (extChartAt J b₀).symm
      (extChartAt J b₀ b₀ + t • (extChartAt J b₀ b - extChartAt J b₀ b₀)) := by
  rw [chartRay_def, rayParam_of_mem_Icc ht]

/-- If the ball of radius `2 * r` around the chart point `c` of `b₀` lies in the chart target,
then for `b ∈ chartBall J b₀ r` and every `u`, the point `c + rayParam u • (y - c)`, where `y` is
the chart point of `b`, lies in the chart target. -/
theorem add_rayParam_smul_sub_mem_extChartAt_target {b₀ b : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target)
    (hb : b ∈ chartBall J b₀ r) (u : ℝ) :
    extChartAt J b₀ b₀ + rayParam u • (extChartAt J b₀ b - extChartAt J b₀ b₀) ∈
      (extChartAt J b₀).target := by
  apply hr
  have hb' := ((mem_chartBall_iff J).1 hb).2
  rw [Metric.mem_ball, dist_eq_norm] at hb' ⊢
  rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  calc |rayParam u| * ‖extChartAt J b₀ b - extChartAt J b₀ b₀‖
      ≤ 2 * ‖extChartAt J b₀ b - extChartAt J b₀ b₀‖ := by
        gcongr; exact abs_rayParam_le u
    _ < 2 * r := by linarith

/-- If the ball of radius `2 * r` around the chart point of `b₀` lies in the chart target, then
for `b ∈ chartBall J b₀ r` the curve `u ↦ chartRay J b₀ (b, u)` stays in the chart source. -/
theorem chartRay_mem_source {b₀ b : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target)
    (hb : b ∈ chartBall J b₀ r) (u : ℝ) :
    chartRay J b₀ (b, u) ∈ (extChartAt J b₀).source := by
  rw [chartRay_def]
  exact (extChartAt J b₀).map_target (add_rayParam_smul_sub_mem_extChartAt_target J hr hb u)

/-- If the ball of radius `2 * r` around the chart point `c` of `b₀` lies in the chart target,
then for `b ∈ chartBall J b₀ r`, with chart point `y`, the chart reading of the curve
`u ↦ chartRay J b₀ (b, u)` is `u ↦ c + rayParam u • (y - c)`. -/
theorem extChartAt_chartRay {b₀ b : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target)
    (hb : b ∈ chartBall J b₀ r) (u : ℝ) :
    extChartAt J b₀ (chartRay J b₀ (b, u)) =
      extChartAt J b₀ b₀ + rayParam u • (extChartAt J b₀ b - extChartAt J b₀ b₀) := by
  rw [chartRay_def]
  exact (extChartAt J b₀).right_inv (add_rayParam_smul_sub_mem_extChartAt_target J hr hb u)

/-- In a boundaryless manifold, there are radii `r > 0` for which the ball of radius `2 * r`
around the chart point of `b₀` lies in the chart target. -/
theorem exists_pos_ball_two_mul_subset_extChartAt_target [J.Boundaryless] (b₀ : B) :
    ∃ r > 0, Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_extChartAt_target (I := J) b₀) _
    (mem_extChartAt_target b₀)
  exact ⟨ε / 2, half_pos hε, by rwa [mul_div_cancel₀ ε two_ne_zero]⟩

variable [IsManifold J ∞ B]

/-- The family of rays of the chart at `b₀` is smooth on `chartBall J b₀ r × ℝ`, if the ball of
radius `2 * r` around the chart point of `b₀` lies in the chart target. -/
theorem contMDiffOn_chartRay {b₀ : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target) :
    ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) J ∞ (chartRay J b₀) ((chartBall J b₀ r : Set B) ×ˢ univ) := by
  have hφ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ rayParam := contDiff_rayParam.contMDiff
  have hsrc : MapsTo Prod.fst ((chartBall J b₀ r : Set B) ×ˢ (univ : Set ℝ))
      (chartAt G b₀).source := fun p hp ↦ by
    rw [← extChartAt_source J]; exact ((mem_chartBall_iff J).1 hp.1).1
  have hchart : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun p : B × ℝ ↦ extChartAt J b₀ p.1)
      ((chartBall J b₀ r : Set B) ×ˢ univ) :=
    (contMDiffOn_extChartAt (n := ∞)).comp contMDiff_fst.contMDiffOn hsrc
  have hin : ContMDiffOn (J.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, F) ∞ (fun p : B × ℝ ↦
      extChartAt J b₀ b₀ + rayParam p.2 • (extChartAt J b₀ p.1 - extChartAt J b₀ b₀))
      ((chartBall J b₀ r : Set B) ×ˢ univ) :=
    contMDiffOn_const.add ((hφ.comp contMDiff_snd).contMDiffOn.smul
      (hchart.sub contMDiffOn_const))
  exact (contMDiffOn_extChartAt_symm b₀).comp hin
    fun p hp ↦ add_rayParam_smul_sub_mem_extChartAt_target J hr hp.1 p.2

/-- **The family of rays of a chart is smooth.** If the ball of radius `2 * r` around the chart
point of `b₀` lies in the chart target, then `(b, u) ↦ chartRay J b₀ (b, u)` is smooth on
`chartBall J b₀ r × ℝ`, with `chartBall J b₀ r` an open submanifold of `B`. -/
theorem contMDiff_chartRay_chartBall {b₀ : B} {r : ℝ}
    (hr : Metric.ball (extChartAt J b₀ b₀) (2 * r) ⊆ (extChartAt J b₀).target) :
    ContMDiff (J.prod 𝓘(ℝ, ℝ)) J ∞ (fun p : chartBall J b₀ r × ℝ ↦ chartRay J b₀ (p.1, p.2)) :=
  (contMDiffOn_chartRay J hr).comp_contMDiff
    ((contMDiff_subtypeVal.comp contMDiff_fst).prodMk contMDiff_snd)
    fun p ↦ ⟨p.1.property, mem_univ _⟩

end SymplecticGeometry

end
