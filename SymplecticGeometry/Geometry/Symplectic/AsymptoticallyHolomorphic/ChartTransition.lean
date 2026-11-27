/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset

/-!
# Transitions between rescaled unitary charts

Let `D` be rescaled unitary charts (`SymplecticGeometry.RescaledUnitaryCharts`). For a power `k`
and two points `x` and `y`, the transition `D.chartTransition k x y` is the map
`D.chart k x ∘ (D.chart k y)⁻¹` from the chart centred at `y` to the chart centred at `x`, as a
partial homeomorphism of `StdSpace ι`. This file proves what the defining properties of `D` give
for it, for `k ≥ k₀`:
* it is smooth on its source, which is open; for `y` in the source of `D.chart k x`, its source
  contains `0` and it sends `0` to `D.chart k x y`, which is `z` for `y = (D.chart k x)⁻¹ z`;
  of `D.chart k x`, its source contains `0` and it sends `0` to `z`;
* its derivative preserves `stdForm ι`, since both charts pull `stdForm ι` back to `2π k σ`
  (`SymplecticGeometry.RescaledUnitaryCharts.stdForm_fderiv_chartTransition`);
* its derivative intertwines `J` read in the chart at `y` with `J` read in the chart at `x`
  (`SymplecticGeometry.RescaledUnitaryCharts.chartPushforward_comp_fderiv_chartTransition`), by
  Tau Ceti's change of chart rule
  `TauCeti.ContMDiffAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`;
* hence its derivative at `w` is an isometry from the bilinear form `ω₀(·, J_y(w) ·)` to the
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

/-- The transition between two charts is smooth on its source. -/
theorem contDiffOn_chartTransition (k : ℕ) (x y : M) :
    ContDiffOn ℝ ∞ (D.chartTransition k x y) (D.chartTransition k x y).source := by
  have hs : (D.chartTransition k x y).source =
      ((D.chart k y).symm.trans (D.chart k x)).source := by
    ext w
    simp [mem_chartTransition_source_iff]
  have hf : ⇑(D.chartTransition k x y) = ⇑((D.chart k y).symm.trans (D.chart k x)) := by
    funext w
    simp
  rw [hs, hf]
  exact contMDiffOn_iff_contDiffOn.1 ((D.chart k y).symm.trans (D.chart k x)).contMDiffOn

/-- The transition between two charts is differentiable at each point of its source. -/
theorem differentiableAt_chartTransition {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    DifferentiableAt ℝ (D.chartTransition k x y) w :=
  ((D.contDiffOn_chartTransition k x y).differentiableOn (by simp) w hw).differentiableAt
    ((D.chartTransition k x y).open_source.mem_nhds hw)

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

/-- The derivative of a chart at a point `(D.chart k y)⁻¹ w` of the source of the transition is
the derivative of the transition at `w` after the derivative of the chart at `y`. -/
theorem mvfderiv_chart_eq_fderiv_chartTransition_comp {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    mvfderiv I (D.chart k x) ((D.chart k y).symm w) =
      (fderiv ℝ (D.chartTransition k x y) w).comp
        (mvfderiv I (D.chart k y) ((D.chart k y).symm w)) := by
  have hw' := D.mem_chartTransition_source_iff.1 hw
  exact (D.chart k y).toOpenPartialHomeomorph.mvfderiv_eq_fderiv_symm_trans_comp hw
    ((D.chart k y).mdifferentiableAt (by simp) ((D.chart k y).map_target hw'.1))
    (D.differentiableAt_chartTransition hw)

/-- **Transitions preserve the standard form.** For `k ≥ k₀`, the derivative of the transition
from the chart centred at `y` to the chart centred at `x`, at a point of its source, preserves
`stdForm ι`. Both charts pull `stdForm ι` back to `2π k σ`. -/
theorem stdForm_fderiv_chartTransition {k : ℕ} (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) (u v : StdSpace ι) :
    stdForm ι (fderiv ℝ (D.chartTransition k x y) w u) (fderiv ℝ (D.chartTransition k x y) w v) =
      stdForm ι u v := by
  have hw' := D.mem_chartTransition_source_iff.1 hw
  set p := (D.chart k y).symm w
  have hpy : p ∈ (D.chart k y).source := (D.chart k y).map_target hw'.1
  -- The preimages of `u` and `v` under the derivative of the chart at `y`.
  have hinv (u : StdSpace ι) :
      mvfderiv I (D.chart k y) p (mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm w u) = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact (D.chart k y).mfderiv_apply_mfderiv_symm_apply (by simp) hw'.1 u
  have hT (u : StdSpace ι) : fderiv ℝ (D.chartTransition k x y) w u =
      mvfderiv I (D.chart k x) p (mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm w u) := by
    rw [D.mvfderiv_chart_eq_fderiv_chartTransition_comp hw, ContinuousLinearMap.comp_apply,
      hinv]
  rw [hT, hT, ← D.eval₂_eq hk x p hw'.2, D.eval₂_eq hk y p hpy, hinv, hinv]

/-- **Transitions intertwine the structures read in the charts.** For `w` in the source of the
transition `τ` from the chart centred at `y` to the chart centred at `x`, the derivative of `τ`
at `w` carries `J` read in the chart at `y` at `w` to `J` read in the chart at `x` at `τ w`. -/
theorem chartPushforward_comp_fderiv_chartTransition {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph (D.chartTransition k x y w)).comp
        (fderiv ℝ (D.chartTransition k x y) w) =
      (fderiv ℝ (D.chartTransition k x y) w).comp
        (J.chartPushforward (D.chart k y).toOpenPartialHomeomorph w) := by
  have hw' := D.mem_chartTransition_source_iff.1 hw
  have h := (J.toContMDiff ⊤).chartPushforward_symm_trans_comp_fderiv hw
    ((D.chart k y).mdifferentiableAt (by simp) ((D.chart k y).map_target hw'.1))
    (by
      rw [PartialDiffeomorph.coe_toOpenPartialHomeomorph_symm]
      exact (D.chart k x).symm.mdifferentiableAt (by simp)
        ((D.chart k x).map_source hw'.2))
    (D.differentiableAt_chartTransition hw)
  rwa [SmoothAlmostComplexStructure.toContMDiff_chartPushforward,
    SmoothAlmostComplexStructure.toContMDiff_chartPushforward] at h

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
  have h := DFunLike.congr_fun (D.chartPushforward_comp_fderiv_chartTransition hw) v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at h
  rw [h, D.stdForm_fderiv_chartTransition hk hw]

/-- **The derivative at the centre of a transition, on a comparison radius.** Let `k ≥ k₀`, let
`ρ₁ ≤ ρ₀` be a comparison radius for the chart centred at `x` (`IsComparisonRadius`), and let `y`
be a point of the source of that chart whose image lies in the ball of radius `ρ₁ * √k`. Then the
derivative at `0` of the transition from the chart centred at `y` to the chart centred at `x` has
norm at most `√2`. -/
theorem norm_fderiv_chartTransition_zero_le {ρ₁ : ℝ} (hρ₁₀ : ρ₁ ≤ ρ₀) {k : ℕ} (hk : k₀ ≤ k)
    {x : M} (hcmp : D.IsComparisonRadius k x ρ₁) {y : M} (hy : y ∈ (D.chart k x).source)
    (hyB : D.chart k x y ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    ‖fderiv ℝ (D.chartTransition k x y) 0‖ ≤ √2 := by
  have h0 := D.zero_mem_chartTransition_source hk hy
  have h0y : (0 : StdSpace ι) ∈ (D.chart k y).target := (D.mem_chartTransition_source_iff.1 h0).1
  have hy0 : (D.chart k y).symm 0 = y := D.chart_symm_zero hk y
  have hρk : 0 < ρ₀ * √k :=
    ((norm_nonneg _).trans_lt (mem_ball_zero_iff.1 hyB)).trans_le (by gcongr)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u ↦ ?_
  -- The tangent vector `v` at `p = y` that the chart at `y` sends to `u`.
  set p := (D.chart k y).symm 0
  set v := mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm 0 u
  have hu : mvfderiv I (D.chart k y) p v = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact (D.chart k y).mfderiv_apply_mfderiv_symm_apply (by simp) h0y u
  -- In the chart at `x`, the image of `v` is `T u`, for `T` the derivative of the transition.
  have hTu : mvfderiv I (D.chart k x) p v = fderiv ℝ (D.chartTransition k x y) 0 u := by
    rw [D.mvfderiv_chart_eq_fderiv_chartTransition_comp h0, ContinuousLinearMap.comp_apply, hu]
  -- In the chart at `y`, whose centre is `p = y`, the quadratic form of `v` is `‖u‖ ^ 2`.
  have hpy : D.chart k y p = 0 := by rw [hy0, D.apply_self hk]
  have hcen := D.abs_eval₂_apply_sub_norm_sq_le hk y
    (by convert D.mem_source hk y using 1)
    (by rw [hpy]; exact mem_ball_self hρk) v
  rw [hpy, norm_zero, mul_zero, zero_mul, hu, abs_nonpos_iff, sub_eq_zero] at hcen
  have hcmpy := (hcmp.mem_Icc (by convert hy using 1)
    (by convert hyB using 2) v).1
  rw [hcen, hTu] at hcmpy
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
  refine D.norm_fderiv_chartTransition_zero_le hρ₁₀ hk (hcmp hk x)
    ((D.chart k x).map_target hzt) ?_
  convert hz using 2
  exact (D.chart k x).right_inv hzt

end RescaledUnitaryCharts

end SymplecticGeometry

end
