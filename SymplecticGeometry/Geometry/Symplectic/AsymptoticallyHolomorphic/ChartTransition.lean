/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
import SymplecticGeometry.Geometry.Symplectic.Manifold.Rescale
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Transitions between rescaled unitary charts

Let `D` be rescaled unitary charts (`SymplecticGeometry.RescaledUnitaryCharts`). For a power `k`
and two points `x` and `y`, the transition `D.chartTransition k x y` is the map
`D.chart k x ∘ (D.chart k y)⁻¹` from the chart centred at `y` to the chart centred at `x`, as a
partial homeomorphism of `StdSpace ι`. This file proves what the defining properties of `D` give
for it, for `k ≥ k₀`:
* it is differentiable at each point of its source
  (`SymplecticGeometry.RescaledUnitaryCharts.differentiableAt_chartTransition`, from
  `PartialDiffeomorph.differentiableAt_symm_trans`), for every `k`;
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
* the field `D.associatedBilinFormInChart k x` of bilinear forms `ω₀(·, J_x ·)` on the chart
  centred at `x`, the image of `J_x` under a fixed continuous linear map, is smooth on the target
  of the chart
  (`SymplecticGeometry.RescaledUnitaryCharts.contDiffOn_associatedBilinFormInChart`, from
  `TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward`), and the derivatives of the
  transitions pull it back from one chart to the other
  (`RescaledUnitaryCharts.associatedBilinFormInChart_chartTransition_bilinearComp`, in the
  namespace `SymplecticGeometry`);
* the fixed map `A ↦ ω₀(·, A ·)` does not increase norms
  (`SymplecticGeometry.norm_precompR_stdForm_flip_apply_le`, of
  `SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic`), so for `k ≥ k₀` and `w` in the
  ball of radius `ρ₀ * √k` the bounds on `J` read in the charts pass to the forms: `‖g_{k,x}(w)‖` is
  at most `‖J₀‖ + |D.bound 1| * ρ₀`
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_associatedBilinFormInChart_le_of_mem_ball`), and
  its `r`-th derivative for `r ≥ 1` is at most `D.bound r * (√k)⁻¹`
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_iteratedFDeriv_associatedBilinFormInChart_le`,
  from Mathlib's `ContinuousLinearMap.iteratedFDeriv_comp_left`); neither `D.bound r` nor `ρ₀`
  depends on `k` or `x`;
* if `σ` is compatible with `J`, then so is `ω₀` with `J` read in the chart at each point of its
  target, since the chart pulls `ω₀` back to `2π k σ`
  (`SymplecticGeometry.RescaledUnitaryCharts.stdForm_compatible_chartPushforwardAt`, from
  `TauCeti.SmoothAlmostComplexStructure.compatible_chartPushforwardAt` and
  `TauCeti.SmoothTwoForm.Compatible.smul`); the forms `g_{k,x}(w)` are then symmetric and positive
  definite there;
* since `J_x(w)² = -1`, each `g_{k,x}(w)` on the target is invertible as a map to the dual, with
  inverse `φ ↦ -ω₀♭⁻¹ (φ ∘ J_x(w))`, `ω₀♭ : u ↦ ω₀(u, ·)`
  (`SymplecticGeometry.RescaledUnitaryCharts.inverse_associatedBilinFormInChart`, from
  `SymplecticGeometry.inverse_precompR_stdForm_flip_apply`); so the field of inverses is `J` read
  in the chart followed by the fixed continuous linear map
  `SymplecticGeometry.stdFormCompRightInverseL`, which does not increase norms, and it satisfies
  the same bounds on the ball as `g_{k,x}`
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_inverse_associatedBilinFormInChart_le_of_mem_ball`
  and, in the same namespace, `norm_iteratedFDeriv_inverse_associatedBilinFormInChart_le`); both
  bounds on derivatives come from one bound for any such map
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_iteratedFDeriv_comp_chartPushforward_le`);
* with the comparison of `2π k σ(v, J v)` with the norm in the charts
  (`SymplecticGeometry.RescaledUnitaryCharts.exists_forall_isComparisonRadius`), there is a radius
  `ρ₁ > 0` such that the derivative at `0` of the transition from the chart at
  `(D.chart k x)⁻¹ z` to the chart at `x` has norm at most `√2` for all `k ≥ k₀`, all `x` and all
  `z` in the ball of radius `ρ₁ * √k`
  (`SymplecticGeometry.RescaledUnitaryCharts.exists_forall_norm_fderiv_chartTransition_zero_le`);
* the set `D.chartTransitionDomain k x y` of points of the ball `B` of radius `ρ₀ * √k` in the
  source of the transition that it sends into `B` is open, and for `k ≥ k₀` and
  `y = (D.chart k x)⁻¹ z` with `z ∈ B` it contains `0`
  (`SymplecticGeometry.RescaledUnitaryCharts.zero_mem_chartTransitionDomain`);
* the inverses of the two charts agree at `w` and at `τ w`, and so do their differentials, on
  `v` and on `dτ_w v`
  (`SymplecticGeometry.RescaledUnitaryCharts.mfderiv_chart_symm_chartTransition`, from Tau Ceti's
  `OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans`).

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped Manifold ContDiff
open TauCeti Metric MulOpposite

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (Bundle.TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
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

/-- The transition from the chart centred at `y` to the chart centred at `x` is differentiable at
each point of its source. -/
theorem differentiableAt_chartTransition {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    DifferentiableAt ℝ (D.chartTransition k x y) w := by
  rw [chartTransition_def] at hw ⊢
  exact (D.chart k y).differentiableAt_symm_trans (D.chart k x) (by simp) hw

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

/-- **Transitions preserve the forms `ω₀(·, J ·)` read in the charts.** For `k ≥ k₀` and `w` in
the source of the transition `τ` from the chart centred at `y` to the chart centred at `x`, the
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

/-! ### The forms `ω₀(·, J ·)` read in the charts -/

/-- The bilinear form `g_{k,x}(w) = ω₀(·, J_x(w) ·)` at a point `w` of the chart centred at `x`
for the power `k`, where `J_x` is `J` read in that chart: the image of `J_x(w)` under the fixed
continuous linear map `A ↦ ω₀(·, A ·)`. It is symmetric and positive definite only where `J` is
compatible with `σ`, which the charts do not assume. The definition is total; its value at a
point `w` outside `(D.chart k x).target` is junk. -/
noncomputable def associatedBilinFormInChart (k : ℕ) (x : M) (w : StdSpace ι) :
    StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℝ :=
  (ContinuousLinearMap.precompR (StdSpace ι)
      (stdForm ι).toBilinForm.toContinuousBilinearMap).flip
    (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w)

/-- The form `g_{k,x}(w)` is `J_x(w)` composed with `A ↦ ω₀(·, A ·)`. -/
theorem associatedBilinFormInChart_def (k : ℕ) (x : M) (w : StdSpace ι) :
    D.associatedBilinFormInChart k x w =
      (ContinuousLinearMap.precompR (StdSpace ι)
          (stdForm ι).toBilinForm.toContinuousBilinearMap).flip
        (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w) :=
  (rfl)

/-- `g_{k,x}(w)(u, v) = ω₀(u, J_x(w) v)`. -/
@[simp]
theorem associatedBilinFormInChart_apply (k : ℕ) (x : M) (w u v : StdSpace ι) :
    D.associatedBilinFormInChart k x w u v =
      stdForm ι u (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w v) := by
  simp [associatedBilinFormInChart_def, LinearMap.toContinuousBilinearMap_apply]

/-- On a boundaryless manifold, the field of forms `g_{k,x}` is smooth on the target of the chart
centred at `x`. -/
theorem contDiffOn_associatedBilinFormInChart [I.Boundaryless] (k : ℕ) (x : M) :
    ContDiffOn ℝ ∞ (D.associatedBilinFormInChart k x) (D.chart k x).target :=
  (ContinuousLinearMap.contDiff _).comp_contDiffOn
    (J.contDiffOn_chartPushforward (D.chart k x).contMDiffOn (D.chart k x).symm.contMDiffOn)

/-- **Transitions carry the forms read in the charts to each other.** For `k ≥ k₀` and `w` in
the source of the transition `τ` from the chart centred at `y` to the chart centred at `x`, the
derivative `T` of `τ` at `w` pulls `g_{k,x}(τ w)` back to `g_{k,y}(w)`. -/
theorem associatedBilinFormInChart_chartTransition_bilinearComp {k : ℕ} (hk : k₀ ≤ k)
    {x y : M} {w : StdSpace ι} (hw : w ∈ (D.chartTransition k x y).source) :
    (D.associatedBilinFormInChart k x (D.chartTransition k x y w)).bilinearComp
        (fderiv ℝ (D.chartTransition k x y) w) (fderiv ℝ (D.chartTransition k x y) w) =
      D.associatedBilinFormInChart k y w := by
  ext u v
  simpa using D.stdForm_fderiv_chartTransition_chartPushforward hk hw u v

/-- The norm of the form `g_{k,x}(w)` is at most the norm of `J_x(w)`, `J` read in the chart
centred at `x`. -/
theorem norm_associatedBilinFormInChart_le (k : ℕ) (x : M) (w : StdSpace ι) :
    ‖D.associatedBilinFormInChart k x w‖ ≤
      ‖J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w‖ := by
  rw [associatedBilinFormInChart_def]
  exact norm_precompR_stdForm_flip_apply_le _

/-- For `k ≥ k₀` and `w` in the ball of radius `ρ₀ * √k`, `J` read in the chart centred at `x`
has norm at most `‖J₀‖ + |D.bound 1| * ρ₀` at `w`. -/
theorem norm_chartPushforward_le_of_mem_ball {k : ℕ} (hk : k₀ ≤ k) (x : M)
    {w : StdSpace ι} (hw : w ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    ‖J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w‖ ≤
      ‖LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap‖ +
        |D.bound 1| * ρ₀ := by
  have hk0 : 0 < √k := (Real.sqrt_nonneg _).lt_of_ne fun h ↦ by
    simpa [← h] using pos_of_mem_ball hw
  have ht : (√k)⁻¹ * ‖w‖ ≤ ρ₀ :=
    (inv_mul_le_iff₀ hk0).2 (by linarith [mem_ball_zero_iff.1 hw])
  refine (norm_le_norm_add_norm_sub' _ (LinearMap.toContinuousLinearMap
      (stdComplexStructure ι).toLinearMap)).trans (add_le_add_right ?_ _)
  calc _ ≤ D.bound 1 * (√k)⁻¹ * ‖w‖ := D.jStruct_sub_le hk x w hw
    _ = D.bound 1 * ((√k)⁻¹ * ‖w‖) := mul_assoc _ _ _
    _ ≤ |D.bound 1| * ((√k)⁻¹ * ‖w‖) := by gcongr; exact le_abs_self _
    _ ≤ |D.bound 1| * ρ₀ := by gcongr

/-- **A uniform bound on the forms read in the charts.** For `k ≥ k₀` and `w` in the ball of
radius `ρ₀ * √k`, the form `g_{k,x}(w)` has norm at most `‖J₀‖ + |D.bound 1| * ρ₀`, a constant
that depends neither on `k`, nor on `x`, nor on `w`. -/
theorem norm_associatedBilinFormInChart_le_of_mem_ball {k : ℕ} (hk : k₀ ≤ k) (x : M)
    {w : StdSpace ι} (hw : w ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    ‖D.associatedBilinFormInChart k x w‖ ≤
      ‖LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap‖ +
        |D.bound 1| * ρ₀ :=
  (D.norm_associatedBilinFormInChart_le k x w).trans
    (D.norm_chartPushforward_le_of_mem_ball hk x hw)

/-- On a boundaryless manifold, for `k ≥ k₀`, `r ≥ 1` and `w` in the ball of radius `ρ₀ * √k`,
the `r`-th iterated derivative at `w` of `J` read in the chart centred at `x`, followed by a
continuous linear map `L` with `‖L A‖ ≤ ‖A‖` for all `A`, has norm at most `D.bound r * (√k)⁻¹`. -/
theorem norm_iteratedFDeriv_comp_chartPushforward_le [I.Boundaryless] {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {L : (StdSpace ι →L[ℝ] StdSpace ι) →L[ℝ] F}
    (hL : ∀ A, ‖L A‖ ≤ ‖A‖) {k : ℕ} (hk : k₀ ≤ k) {r : ℕ} (hr : r ≠ 0) (x : M)
    {w : StdSpace ι} (hw : w ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    ‖iteratedFDeriv ℝ r (L ∘ J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) w‖ ≤
      D.bound r * (√k)⁻¹ := by
  have hJ : ContDiffAt ℝ ∞ (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) w :=
    (J.contDiffOn_chartPushforward (D.chart k x).contMDiffOn
      (D.chart k x).symm.contMDiffOn).contDiffAt
      ((D.chart k x).open_target.mem_nhds (D.ball_subset_target hk x hw))
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left _ hJ (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.opNorm_le_bound (norm_nonneg _) fun m ↦ ?_).trans
    (D.iteratedFDeriv_jStruct_le hk hr x w hw)
  rw [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply]
  exact (hL _).trans (ContinuousMultilinearMap.le_opNorm _ m)

/-- **Uniform bounds on the derivatives of the forms read in the charts.** On a boundaryless
manifold, for `k ≥ k₀`, `r ≥ 1` and `w` in the ball of radius `ρ₀ * √k`, the `r`-th iterated
derivative of the field of forms `g_{k,x}` at `w` has norm at most `D.bound r * (√k)⁻¹`: the
field is `J` read in the chart followed by a fixed continuous linear map that does not increase
norms. -/
theorem norm_iteratedFDeriv_associatedBilinFormInChart_le [I.Boundaryless] {k : ℕ}
    (hk : k₀ ≤ k) {r : ℕ} (hr : r ≠ 0) (x : M) {w : StdSpace ι}
    (hw : w ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    ‖iteratedFDeriv ℝ r (D.associatedBilinFormInChart k x) w‖ ≤ D.bound r * (√k)⁻¹ := by
  have hfun : D.associatedBilinFormInChart k x =
      (ContinuousLinearMap.precompR (StdSpace ι)
          (stdForm ι).toBilinForm.toContinuousBilinearMap).flip ∘
        J.chartPushforward (D.chart k x).toOpenPartialHomeomorph :=
    funext (D.associatedBilinFormInChart_def k x)
  rw [hfun]
  exact D.norm_iteratedFDeriv_comp_chartPushforward_le norm_precompR_stdForm_flip_apply_le hk hr x
    hw

/-! ### Compatibility, symmetry and the inverse of the forms read in the charts -/

/-- At a point `w` of the target of the chart centred at `x`, for `k ≥ k₀`, `ω₀` is compatible
with `J` read in the chart at `w`, provided that `σ` is compatible with `J`: the chart pulls `ω₀`
back to `2π k σ`. -/
theorem stdForm_compatible_chartPushforwardAt (hJ : σ.Compatible J) {k : ℕ} (hk : k₀ ≤ k)
    (x : M) {w : StdSpace ι} (hw : w ∈ (D.chart k x).target) :
    (stdForm ι).Compatible (J.chartPushforwardAt (D.chart k x) hw) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · -- For `k = 0` the chart pulls `ω₀` back to `0`, so `StdSpace ι` is trivial.
    have hsurj := ((D.chart 0 x).bijective_mvfderiv (by simp) (D.mem_source hk x)).surjective
    have h0 (a : StdSpace ι) : a = 0 := by
      refine (stdForm ι).eq_of_forall_apply_eq fun b ↦ ?_
      obtain ⟨v, rfl⟩ := hsurj a
      obtain ⟨u, rfl⟩ := hsurj b
      rw [← D.eval₂_eq hk x x (D.mem_source hk x), Nat.cast_zero, mul_zero, zero_mul]
      exact (LinearMap.map_zero₂ _ _).symm
    exact .of_tames ((SymplecticForm.invariant_iff _ _).2 fun a b ↦ by rw [h0 a, h0 b]; simp)
      fun a ha ↦ absurd (h0 a) ha
  · refine J.compatible_chartPushforwardAt (hJ.smul (2 * Real.pi * k) (by positivity))
      (D.chart k x) (fun y hy u v ↦ ?_) hw
    rw [SmoothForm.eval₂_smul, smul_eq_mul]
    exact D.eval₂_eq hk x y hy u v

/-- **The forms read in the charts are symmetric.** If `σ` is compatible with `J`, then for
`k ≥ k₀` and `w` in the target of the chart centred at `x`, `g_{k,x}(w)(u, v) = g_{k,x}(w)(v, u)`.
-/
theorem associatedBilinFormInChart_apply_swap (hJ : σ.Compatible J) {k : ℕ} (hk : k₀ ≤ k)
    (x : M) {w : StdSpace ι} (hw : w ∈ (D.chart k x).target) (u v : StdSpace ι) :
    D.associatedBilinFormInChart k x w u v = D.associatedBilinFormInChart k x w v u := by
  simpa [SmoothAlmostComplexStructure.chartPushforwardAt_apply] using
    (D.stdForm_compatible_chartPushforwardAt hJ hk x hw).associatedBilinForm_apply_swap u v

/-- **The forms read in the charts are positive definite.** If `σ` is compatible with `J`, then
for `k ≥ k₀`, `w` in the target of the chart centred at `x` and `u ≠ 0`, `g_{k,x}(w)(u, u) > 0`. -/
theorem associatedBilinFormInChart_apply_self_pos (hJ : σ.Compatible J) {k : ℕ} (hk : k₀ ≤ k)
    (x : M) {w : StdSpace ι} (hw : w ∈ (D.chart k x).target) {u : StdSpace ι} (hu : u ≠ 0) :
    0 < D.associatedBilinFormInChart k x w u u := by
  simpa [SmoothAlmostComplexStructure.chartPushforwardAt_apply] using
    (D.stdForm_compatible_chartPushforwardAt hJ hk x hw).associated_pos hu

/-- **The forms read in the charts are nondegenerate.** At a point `w` of the target of the chart
centred at `x`, the form `g_{k,x}(w)`, as a map from `StdSpace ι` to its dual, is invertible. This
only uses `J_x(w)² = -1`, not the compatibility of `J` with `σ`. -/
theorem isInvertible_associatedBilinFormInChart {k : ℕ} {x : M} {w : StdSpace ι}
    (hw : w ∈ (D.chart k x).target) : (D.associatedBilinFormInChart k x w).IsInvertible := by
  rw [associatedBilinFormInChart_def]
  exact isInvertible_precompR_stdForm_flip_apply
    (J.chartPushforward_apply_chartPushforward_apply _ hw)

/-- **The inverse of the forms read in the charts.** At a point `w` of the target of the chart
centred at `x`, the inverse of `g_{k,x}(w)` is `stdFormCompRightInverseL ι` applied to `J_x(w)`: it
sends a linear form `φ` to `-Ω⁻¹ (φ ∘ J_x(w))`, `Ω` being `ω₀` as a map to the dual. -/
theorem inverse_associatedBilinFormInChart {k : ℕ} {x : M} {w : StdSpace ι}
    (hw : w ∈ (D.chart k x).target) :
    (D.associatedBilinFormInChart k x w).inverse =
      stdFormCompRightInverseL ι (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w) := by
  rw [associatedBilinFormInChart_def]
  exact inverse_precompR_stdForm_flip_apply (J.chartPushforward_apply_chartPushforward_apply _ hw)

/-- The norm of the inverse of `g_{k,x}(w)`, at a point `w` of the target of the chart centred
at `x`, is at most the norm of `J_x(w)`. -/
theorem norm_inverse_associatedBilinFormInChart_le {k : ℕ} {x : M} {w : StdSpace ι}
    (hw : w ∈ (D.chart k x).target) :
    ‖(D.associatedBilinFormInChart k x w).inverse‖ ≤
      ‖J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w‖ := by
  rw [D.inverse_associatedBilinFormInChart hw]
  exact norm_stdFormCompRightInverseL_apply_le _

/-- **A uniform bound on the inverses of the forms read in the charts.** For `k ≥ k₀` and `w` in
the ball of radius `ρ₀ * √k`, the inverse of `g_{k,x}(w)` has norm at most
`‖J₀‖ + |D.bound 1| * ρ₀`, a constant that depends neither on `k`, nor on `x`, nor on `w`. -/
theorem norm_inverse_associatedBilinFormInChart_le_of_mem_ball {k : ℕ} (hk : k₀ ≤ k) (x : M)
    {w : StdSpace ι} (hw : w ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    ‖(D.associatedBilinFormInChart k x w).inverse‖ ≤
      ‖LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap‖ +
        |D.bound 1| * ρ₀ :=
  (D.norm_inverse_associatedBilinFormInChart_le (D.ball_subset_target hk x hw)).trans
    (D.norm_chartPushforward_le_of_mem_ball hk x hw)

/-- **Uniform bounds on the derivatives of the inverses of the forms read in the charts.** On a
boundaryless manifold, for `k ≥ k₀`, `r ≥ 1` and `w` in the ball of radius `ρ₀ * √k`, the `r`-th
iterated derivative of `w ↦ g_{k,x}(w)⁻¹` at `w` has norm at most `D.bound r * (√k)⁻¹`: on the
target of the chart, this field is `J` read in the chart followed by
`stdFormCompRightInverseL ι`, which does not increase norms. -/
theorem norm_iteratedFDeriv_inverse_associatedBilinFormInChart_le [I.Boundaryless] {k : ℕ}
    (hk : k₀ ≤ k) {r : ℕ} (hr : r ≠ 0) (x : M) {w : StdSpace ι}
    (hw : w ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    ‖iteratedFDeriv ℝ r (fun w ↦ (D.associatedBilinFormInChart k x w).inverse) w‖ ≤
      D.bound r * (√k)⁻¹ := by
  have hfun : (fun w ↦ (D.associatedBilinFormInChart k x w).inverse) =ᶠ[nhds w]
      stdFormCompRightInverseL ι ∘ J.chartPushforward (D.chart k x).toOpenPartialHomeomorph :=
    Filter.eventually_of_mem
      ((D.chart k x).open_target.mem_nhds (D.ball_subset_target hk x hw))
      fun _ hw' ↦ D.inverse_associatedBilinFormInChart hw'
  rw [(hfun.iteratedFDeriv ℝ r).eq_of_nhds]
  exact D.norm_iteratedFDeriv_comp_chartPushforward_le norm_stdFormCompRightInverseL_apply_le hk hr
    x hw

/-! ### The derivatives of the transitions at the centre -/

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

/-! ### The domain of the transition between the balls -/

/-- The points `w` of the ball `B` of radius `ρ₀ * √k` that lie in the source of the transition
`τ` from the chart centred at `y` to the chart centred at `x` and that `τ` sends into `B`. -/
noncomputable def chartTransitionDomain (k : ℕ) (x y : M) : Set (StdSpace ι) :=
  ball 0 (ρ₀ * √k) ∩
    ((D.chartTransition k x y).source ∩ D.chartTransition k x y ⁻¹' ball 0 (ρ₀ * √k))

theorem mem_chartTransitionDomain_iff {k : ℕ} {x y : M} {w : StdSpace ι} :
    w ∈ D.chartTransitionDomain k x y ↔
      w ∈ ball 0 (ρ₀ * √k) ∧ w ∈ (D.chartTransition k x y).source ∧
        D.chartTransition k x y w ∈ ball 0 (ρ₀ * √k) :=
  Iff.rfl

theorem chartTransitionDomain_subset_ball (k : ℕ) (x y : M) :
    D.chartTransitionDomain k x y ⊆ ball 0 (ρ₀ * √k) :=
  fun _ hw ↦ hw.1

theorem chartTransitionDomain_subset_source (k : ℕ) (x y : M) :
    D.chartTransitionDomain k x y ⊆ (D.chartTransition k x y).source :=
  fun _ hw ↦ hw.2.1

theorem isOpen_chartTransitionDomain (k : ℕ) (x y : M) :
    IsOpen (D.chartTransitionDomain k x y) :=
  isOpen_ball.inter ((D.chartTransition k x y).isOpen_inter_preimage isOpen_ball)

/-- For `k ≥ k₀` and `z` in the ball of radius `ρ₀ * √k`, the domain of the transition from the
chart centred at `(D.chart k x)⁻¹ z` to the chart centred at `x` contains `0`. -/
theorem zero_mem_chartTransitionDomain {k : ℕ} (hk : k₀ ≤ k) (x : M) {z : StdSpace ι}
    (hz : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    0 ∈ D.chartTransitionDomain k x ((D.chart k x).symm z) := by
  have hzt : z ∈ (D.chart k x).target := D.ball_subset_target hk x hz
  refine ⟨mem_ball_self (pos_of_mem_ball hz), D.zero_mem_chartTransition_source hk
    ((D.chart k x).map_target hzt), ?_⟩
  rwa [Set.mem_preimage, D.chartTransition_symm_zero hk hzt]

/-- A point of the source of the transition from the chart centred at `y` to the chart centred
at `x` has the same image under the inverses of the two charts, read at `w` and at `τ w`. -/
theorem chart_symm_chartTransition {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    (D.chart k x).symm (D.chartTransition k x y w) = (D.chart k y).symm w := by
  rw [chartTransition_apply]
  exact (D.chart k x).left_inv (D.mem_chartTransition_source_iff.1 hw).2

/-- The derivative form of `chart_symm_chartTransition`: for `w` in the source of the transition
`τ` from the chart centred at `y` to the chart centred at `x`, the differential of the inverse of
the chart at `x` at `τ w` sends `dτ_w v` to the image of `v` under the differential of the
inverse of the chart at `y` at `w`. -/
theorem mfderiv_chart_symm_chartTransition {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) (v : StdSpace ι) :
    mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k x).symm (D.chartTransition k x y w)
        (fderiv ℝ (D.chartTransition k x y) w v) =
      mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm w v := by
  have hτ : D.chartTransition k x y w ∈ (D.chart k x).target := by
    rw [chartTransition_apply]
    exact (D.chart k x).map_source (D.mem_chartTransition_source_iff.1 hw).2
  have hd := D.differentiableAt_chartTransition hw
  rw [chartTransition_def] at hw hτ hd ⊢
  have h := OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans hw
    ((D.chart k x).symm.mdifferentiableAt (by simp) (by simpa using hτ)) hd
  -- `exact` rather than `rw`: the two sides differ by the identification of `StdSpace ι` with
  -- its tangent spaces, and by `ContinuousLinearMap.comp_apply`.
  exact (DFunLike.congr_fun h v).symm

end RescaledUnitaryCharts

end SymplecticGeometry

end
