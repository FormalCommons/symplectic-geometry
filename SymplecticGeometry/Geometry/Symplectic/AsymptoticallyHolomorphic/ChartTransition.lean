/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Transitions between rescaled unitary charts

Let `D` be rescaled unitary charts (`SymplecticGeometry.RescaledUnitaryCharts`). For a power `k`
and two points `x` and `y`, the transition `D.chartTransition k x y` is the map
`D.chart k x ∘ (D.chart k y)⁻¹` from the chart centred at `y` to the chart centred at `x`, as a
partial homeomorphism of `StdSpace ι`. This file proves what the defining properties of `D` give
for it, for `k ≥ k₀`:
* for `y` in the source of `D.chart k x`, its source contains `0` and it sends `0` to
  `D.chart k x y`, which is `z` for `y = (D.chart k x)⁻¹ z`;
* its derivative preserves `stdForm ι`, since both charts pull `stdForm ι` back to `2π k σ`
  (`SymplecticGeometry.RescaledUnitaryCharts.stdForm_fderiv_chartTransition`, from
  `PartialDiffeomorph.apply_fderiv_symm_trans_eq_of_mvfderiv`);
* since its derivative intertwines `J` read in the chart at `y` with `J` read in the chart at
  `x` (`TauCeti.SmoothAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`), its
  derivative at `w` is an isometry from the bilinear form `ω₀(·, J_y(w) ·)` to the
  bilinear form `ω₀(·, J_x(τ w) ·)`, `J_y` and `J_x` being `J` read in the two charts
  (`SymplecticGeometry.RescaledUnitaryCharts.stdForm_fderiv_chartTransition_chartPushforward`);
* with the comparison of `2π k σ(v, J v)` with the norm in the charts
  (`SymplecticGeometry.RescaledUnitaryCharts.exists_forall_isComparisonRadius`), there is a radius
  `ρ₁ > 0` such that the derivative at `0` of the transition from the chart at
  `(D.chart k x)⁻¹ z` to the chart at `x` has norm at most `√2` for all `k ≥ k₀`, all `x` and all
  `z` in the ball of radius `ρ₁ * √k`
  (`SymplecticGeometry.RescaledUnitaryCharts.exists_forall_norm_fderiv_chartTransition_zero_le`).

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped Manifold ContDiff
open TauCeti Metric Bundle MulOpposite

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]

namespace RescaledUnitaryCharts

variable {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-- The transition `D.chart k x ∘ (D.chart k y)⁻¹` from the chart centred at `y` to the chart
centred at `x`, for the power `k`. -/
noncomputable def chartTransition (k : ℕ) (x y : M) :
    OpenPartialHomeomorph (StdSpace ι) (StdSpace ι) :=
  (D.chart k y).toOpenPartialHomeomorph.symm.trans (D.chart k x).toOpenPartialHomeomorph

/-- The transition is the inverse of the chart at `y` followed by the chart at `x`. -/
theorem chartTransition_def (k : ℕ) (x y : M) :
    D.chartTransition k x y =
      (D.chart k y).toOpenPartialHomeomorph.symm.trans (D.chart k x).toOpenPartialHomeomorph :=
  (rfl)

/-- The transition sends `w` to the image under the chart at `x` of `(D.chart k y)⁻¹ w`. -/
@[simp]
theorem chartTransition_apply (k : ℕ) (x y : M) (w : StdSpace ι) :
    D.chartTransition k x y w = D.chart k x ((D.chart k y).symm w) :=
  (rfl)

/-- The source of the transition: the points of the target of the chart at `y` whose image under
its inverse lies in the source of the chart at `x`. -/
theorem mem_chartTransition_source_iff {k : ℕ} {x y : M} {w : StdSpace ι} :
    w ∈ (D.chartTransition k x y).source ↔
      w ∈ (D.chart k y).target ∧ (D.chart k y).symm w ∈ (D.chart k x).source := by
  simp [chartTransition_def]

/-- For `y` in the source of the chart centred at `x`, the centre `0` of the chart at `y` lies in
the source of the transition from the chart at `y` to the chart at `x`. -/
theorem zero_mem_chartTransition_source {k : ℕ} (hk : k₀ ≤ k) {x y : M}
    (hy : y ∈ (D.chart k x).source) : 0 ∈ (D.chartTransition k x y).source := by
  rw [mem_chartTransition_source_iff, D.chart_symm_zero hk]
  refine ⟨?_, hy⟩
  rw [← D.apply_self hk y]
  exact (D.chart k y).map_source (D.mem_source hk y)

/-- The transition from the chart centred at `y` to the chart centred at `x` sends `0` to the
image of `y` in the chart at `x`. -/
theorem chartTransition_zero {k : ℕ} (hk : k₀ ≤ k) (x y : M) :
    D.chartTransition k x y 0 = D.chart k x y := by
  rw [chartTransition_apply, D.chart_symm_zero hk]

/-- For `z` in the target of the chart centred at `x`, the transition from the chart at
`(D.chart k x)⁻¹ z` to the chart at `x` sends `0` to `z`. -/
theorem chartTransition_symm_zero {k : ℕ} (hk : k₀ ≤ k) {x : M} {z : StdSpace ι}
    (hz : z ∈ (D.chart k x).target) :
    D.chartTransition k x ((D.chart k x).symm z) 0 = z :=
  (D.chartTransition_zero hk x _).trans ((D.chart k x).right_inv hz)

/-- **Transitions preserve the standard form.** For `k ≥ k₀`, the derivative of the transition
from the chart centred at `y` to the chart centred at `x`, at a point of its source, preserves
`stdForm ι`. Both charts pull `stdForm ι` back to `2π k σ`. -/
theorem stdForm_fderiv_chartTransition {k : ℕ} (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) (u v : StdSpace ι) :
    stdForm ι (fderiv ℝ (D.chartTransition k x y) w u) (fderiv ℝ (D.chartTransition k x y) w v) =
      stdForm ι u v := by
  rw [chartTransition_def] at hw ⊢
  have hw' : w ∈ (D.chart k y).target ∧ (D.chart k y).symm w ∈ (D.chart k x).source := by
    simpa using hw
  refine (D.chart k y).apply_fderiv_symm_trans_eq_of_mvfderiv (D.chart k x) (by simp)
    (stdForm ι · ·) hw (fun u v ↦ ?_) u v
  exact (D.eval₂_eq hk x _ hw'.2 u v).symm.trans
    (D.eval₂_eq hk y _ ((D.chart k y).map_target hw'.1) u v)

/-- **Transitions are isometries of the metrics read in the charts.** For `k ≥ k₀` and `w` in the
source of the transition `τ` from the chart centred at `y` to the chart centred at `x`, the
derivative `T` of `τ` at `w` satisfies `ω₀(T u, J_x(τ w) (T v)) = ω₀(u, J_y(w) v)`, where `J_x`
and `J_y` are `J` read in the two charts: `T` pulls the bilinear form `ω₀(·, J_x(τ w) ·)` back to
`ω₀(·, J_y(w) ·)`. -/
theorem stdForm_fderiv_chartTransition_chartPushforward {k : ℕ} (hk : k₀ ≤ k) {x y : M}
    {w : StdSpace ι} (hw : w ∈ (D.chartTransition k x y).source) (u v : StdSpace ι) :
    stdForm ι (fderiv ℝ (D.chartTransition k x y) w u)
        (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph (D.chartTransition k x y w)
          (fderiv ℝ (D.chartTransition k x y) w v)) =
      stdForm ι u (J.chartPushforward (D.chart k y).toOpenPartialHomeomorph w v) := by
  have h := DFunLike.congr_fun (J.chartPushforward_symm_trans_comp_fderiv (D.chart k y)
    (D.chart k x) (by rwa [chartTransition_def] at hw)) v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← chartTransition_def] at h
  rw [h, D.stdForm_fderiv_chartTransition hk hw]

/-- At the centre `x` of the chart `D.chart k x`, for `k ≥ k₀`, the quadratic form
`2π k σ(v, J v)` of a tangent vector `v` at `x` is `‖u‖ ^ 2`, for `u` the image of `v` under the
derivative of the chart. -/
theorem eval₂_apply_self_eq_norm_sq {k : ℕ} (hk : k₀ ≤ k) (x : M) (v : TangentSpace I x) :
    2 * Real.pi * k * σ.eval₂ x v (J x v) = ‖mvfderiv I (D.chart k x) x v‖ ^ 2 := by
  rw [D.eval₂_eq hk x x (D.mem_source hk x), mvfderiv_apply_eq_mfderiv_apply (v := J x v),
    J.mfderiv_apply_eq_chartPushforward_apply _ (D.mem_source hk x),
    ← mvfderiv_apply_eq_mfderiv_apply, D.apply_self hk, D.chartPushforward_zero hk,
    stdForm_apply_stdComplexStructure, real_inner_self_eq_norm_sq]

/-- **The derivative at the centre of a transition, on a comparison radius.** Let `k ≥ k₀`, let
`ρ₁` be a comparison radius for the chart centred at `x` (`IsComparisonRadius`), and let `y` be a
point of the source of that chart whose image lies in the ball of radius `ρ₁ * √k`. Then the
derivative at `0` of the transition from the chart centred at `y` to the chart centred at `x` has
norm at most `√2`. -/
theorem norm_fderiv_chartTransition_zero_le {ρ₁ : ℝ} {k : ℕ} (hk : k₀ ≤ k) {x : M}
    (hcmp : D.IsComparisonRadius k x ρ₁) {y : M} (hy : y ∈ (D.chart k x).source)
    (hyB : D.chart k x y ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    ‖fderiv ℝ (D.chartTransition k x y) 0‖ ≤ √2 := by
  have h0 := D.zero_mem_chartTransition_source hk hy
  have h0y : (0 : StdSpace ι) ∈ (D.chart k y).target := (D.mem_chartTransition_source_iff.1 h0).1
  have hy0 : (D.chart k y).symm 0 = y := D.chart_symm_zero hk y
  -- The derivative of the chart at `y`, at its centre `y`, and the chain rule there.
  have hinv := (D.chart k y).mfderiv_apply_mfderiv_symm_apply (by simp) h0y
  have hT := (D.chart k y).mvfderiv_eq_fderiv_symm_trans_comp (D.chart k x) (by simp)
    (by rwa [chartTransition_def] at h0)
  rw [← chartTransition_def] at hT
  rw [hy0] at hinv hT
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  -- The tangent vector `v` at `y` that the chart at `y` sends to `u`.
  set v : TangentSpace I y := mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm 0 u
  have hu : mvfderiv I (D.chart k y) y v = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact hinv u
  -- In the chart at `x`, the image of `v` is `T u`, for `T` the derivative of the transition.
  have hTu : mvfderiv I (D.chart k x) y v = fderiv ℝ (D.chartTransition k x y) 0 u := by
    rw [hT, ContinuousLinearMap.comp_apply, hu]
  have hcmpy := (hcmp.mem_Icc hy hyB v).1
  rw [D.eval₂_apply_self_eq_norm_sq hk y v, hu, hTu] at hcmpy
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt zero_le_two]
  linarith

/-- **A uniform bound on the derivatives of the transitions at the centre.** For rescaled unitary
charts with radius `ρ₀ > 0`, there is a radius `ρ₁` with `0 < ρ₁ ≤ ρ₀` such that for every
`k ≥ k₀`, every point `x` and every `z` in the ball of radius `ρ₁ * √k`, the derivative at `0` of
the transition from the chart centred at `(D.chart k x)⁻¹ z` to the chart centred at `x` has norm
at most `√2`. -/
theorem exists_forall_norm_fderiv_chartTransition_zero_le (hρ₀ : 0 < ρ₀) :
    ∃ ρ₁, 0 < ρ₁ ∧ ρ₁ ≤ ρ₀ ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M), ∀ z ∈ ball (0 : StdSpace ι) (ρ₁ * √k),
      ‖fderiv ℝ (D.chartTransition k x ((D.chart k x).symm z)) 0‖ ≤ √2 := by
  obtain ⟨ρ₁, hρ₁, hρ₁₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  refine ⟨ρ₁, hρ₁, hρ₁₀, fun {k} hk x z hz ↦ ?_⟩
  have hzt : z ∈ (D.chart k x).target :=
    (ball_subset_ball (by gcongr)).trans (D.ball_subset_target hk x) hz
  refine D.norm_fderiv_chartTransition_zero_le hk (hcmp hk x)
    ((D.chart k x).map_target hzt) ?_
  convert hz using 2
  exact (D.chart k x).right_inv hzt

end RescaledUnitaryCharts

end SymplecticGeometry

end
