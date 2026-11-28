/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.JetNorm
public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.RescaledChart
public import SymplecticGeometry.Geometry.Symplectic.Manifold.AlmostComplex.Chart
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Christoffel.Basic
import SymplecticGeometry.Analysis.Calculus.ContDiff.Bounds
import SymplecticGeometry.Analysis.Calculus.FDeriv.Koszul
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.FirstOrderSystem
import SymplecticGeometry.Analysis.Calculus.IteratedFDeriv.Christoffel
import SymplecticGeometry.Geometry.Symplectic.Manifold.Rescale
import SymplecticGeometry.Geometry.Symplectic.SymplecticTransport
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# Transitions between rescaled unitary charts

Let `D` be rescaled unitary charts (`SymplecticGeometry.RescaledUnitaryCharts`). For a power `k`
and two points `x` and `y`, the transition `D.chartTransition k x y` is the map
`D.chart k x ∘ (D.chart k y)⁻¹` from the chart centred at `y` to the chart centred at `x`, as a
partial homeomorphism of `StdSpace ι`. This file proves what the defining properties of `D` give
for it, for `k ≥ k₀`:
* it is differentiable and smooth at each point of its source, and smooth on its source
  (`SymplecticGeometry.RescaledUnitaryCharts.differentiableAt_chartTransition`,
  `SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_chartTransition` and
  `SymplecticGeometry.RescaledUnitaryCharts.contDiffOn_chartTransition`, from
  `PartialDiffeomorph.differentiableAt_symm_trans` and `PartialDiffeomorph.contDiffOn_symm_trans`),
  for every `k`;
* for `y` in the source of `D.chart k x`, its source contains `0` and it sends `0` to
  `D.chart k x y`, which is `z` for `y = (D.chart k x)⁻¹ z`;
* its derivative preserves `stdForm ι`, since both charts pull `stdForm ι` back to `2π k σ`
  (`SymplecticGeometry.RescaledUnitaryCharts.stdForm_fderiv_chartTransition`, from
  `PartialDiffeomorph.apply_fderiv_symm_trans_eq_of_mvfderiv`);
* since its derivative intertwines `J` read in the chart at `y` with `J` read in the chart at
  `x` (`SymplecticGeometry.RescaledUnitaryCharts.isComplexLinear_fderiv_chartTransition`, from
  `TauCeti.SmoothAlmostComplexStructure.chartPushforward_symm_trans_comp_fderiv`), its
  derivative at `w` is an isometry from the bilinear form `ω₀(·, J_y(w) ·)` to the
  bilinear form `ω₀(·, J_x(τ w) ·)`, `J_y` and `J_x` being `J` read in the two charts
  (`SymplecticGeometry.RescaledUnitaryCharts.stdForm_fderiv_chartTransition_chartPushforward`);
* the field `D.associatedBilinFormInChart k x` of bilinear forms `ω₀(·, J_x ·)` on the chart
  centred at `x`, the image of `J_x` under `SymplecticGeometry.stdFormCompRightL ι`, is smooth
  on the target of the chart
  (`SymplecticGeometry.RescaledUnitaryCharts.contDiffOn_associatedBilinFormInChart`, from
  `TauCeti.SmoothAlmostComplexStructure.contDiffOn_chartPushforward`), and the derivatives of the
  transitions pull it back from one chart to the other
  (`RescaledUnitaryCharts.associatedBilinFormInChart_chartTransition_bilinearComp`, in the
  namespace `SymplecticGeometry`);
* the map `stdFormCompRightL ι`, `A ↦ ω₀(·, A ·)`, does not increase norms
  (`SymplecticGeometry.norm_stdFormCompRightL_apply_le`, of
  `SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic`), so for `k ≥ k₀` and `w` in the
  ball of radius `ρ₀ * √k` the bounds on `J` read in the charts pass to the forms: `‖g_{k,x}(w)‖` is
  at most `‖J₀‖ + |D.bound 1| * ρ₀`
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_associatedBilinFormInChart_le_of_mem_ball`), and
  its `r`-th derivative for `r ≥ 1` is at most `D.bound r * (√k)⁻¹`
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_iteratedFDeriv_associatedBilinFormInChart_le`,
  from `ContinuousLinearMap.norm_iteratedFDeriv_comp_left_le_of_forall_norm_le`); neither
  `D.bound r` nor `ρ₀` depends on `k` or `x`;
* with these bounds, for each order `r` the `r`-jet norm of `J_x - J₀` at `w` in that ball, for
  `J₀ = stdComplexStructure ι`, is at most a constant independent of `k` and `x` times
  `(√k)⁻¹ * (1 + ‖w‖)`
  (`SymplecticGeometry.RescaledUnitaryCharts.exists_jetNormAt_chartPushforward_sub_le`, from
  `SymplecticGeometry.jetNormAt_le_of_norm_iteratedFDeriv_succ_le`);
* if `σ` is compatible with `J`, then so is `ω₀` with `J` read in the chart at each point of its
  target, since the chart pulls `ω₀` back to `2π k σ`
  (`SymplecticGeometry.RescaledUnitaryCharts.stdForm_compatible_pushforwardAt`, from
  `TauCeti.SmoothTwoForm.Compatible.compatible_pushforwardAt` and
  `TauCeti.SmoothTwoForm.Compatible.smul`); the forms `g_{k,x}(w)` are then symmetric and positive
  definite there;
* since `J_x(w)² = -1`, each `g_{k,x}(w)` on the target is invertible as a map to the dual, with
  inverse `φ ↦ -ω₀♭⁻¹ (φ ∘ J_x(w))`, `ω₀♭ : u ↦ ω₀(u, ·)`
  (`SymplecticGeometry.RescaledUnitaryCharts.inverse_associatedBilinFormInChart`, from
  `SymplecticGeometry.inverse_stdFormCompRightL_apply`); so the field of inverses is `J` read
  in the chart followed by the fixed continuous linear map
  `SymplecticGeometry.stdFormCompRightInverseL`, which does not increase norms, and it satisfies
  the same bounds on the ball as `g_{k,x}`
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_inverse_associatedBilinFormInChart_le_of_mem_ball`
  and, in the same namespace, `norm_iteratedFDeriv_inverse_associatedBilinFormInChart_le`); both
  bounds on derivatives come from one bound for any such map
  (`SymplecticGeometry.RescaledUnitaryCharts.norm_iteratedFDeriv_comp_chartPushforward_le`);
* the Christoffel symbols of the second kind `Γ_{k,x}` of `g_{k,x}`, Tau Ceti's
  `TauCeti.Manifold.christoffelSecondKind`, are smooth on the target of the chart
  (`RescaledUnitaryCharts.contDiffOn_christoffelSecondKind_associatedBilinFormInChart`, in the
  namespace `SymplecticGeometry`, from `TauCeti.Manifold.contDiffOn_christoffelSecondKind`), as
  are `g_{k,x}` and the field of its inverses (in the same namespace,
  `contDiffAt_associatedBilinFormInChart` and `contDiffOn_inverse_associatedBilinFormInChart`);
  and for each `r` there is a constant `C`, independent of `k` and `x`, with
  `‖Dʲ Γ_{k,x}(w)‖ ≤ C * (√k)⁻¹` for `j ≤ r`, `k ≥ k₀` and `w` in the ball of radius `ρ₀ * √k`
  (in the same namespace,
  `exists_norm_iteratedFDeriv_christoffelSecondKind_associatedBilinFormInChart_le`). This is
  the Leibniz bound
  `SymplecticGeometry.norm_iteratedFDeriv_christoffelSecondKind_le_of_forall_le` applied to the
  bounds above on `g_{k,x}` and on its inverses; every term carries a derivative of `g_{k,x}` of
  positive order, hence the factor `(√k)⁻¹`;
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
  `OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans`);
* the derivative of a transition is bijective at each point of its source
  (`SymplecticGeometry.RescaledUnitaryCharts.bijective_fderiv_chartTransition`, from
  `TauCeti.SymplecticForm.bijective_of_forall_apply_eq_or_forall_apply_eq_neg`), so, if `σ` is
  compatible with `J`, the Koszul formula writes its second derivative through its first and the
  Christoffel symbols of the forms read in the two charts
  (`SymplecticGeometry.RescaledUnitaryCharts.fderiv_fderiv_chartTransition`); then `(τ, Dτ)`
  solves a first-order system, and the uniform bounds above on the Christoffel symbols bound
  every derivative of the transition at each point `w` of `D.chartTransitionDomain k x y` by a
  constant that depends only on the order and on a bound for `‖Dτ(w)‖`
  (in the namespace `SymplecticGeometry.RescaledUnitaryCharts`,
  `exists_forall_norm_iteratedFDeriv_chartTransition_le`, from
  `SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le_of_fderiv_fderiv_eq`);
* in the other direction, the transition from the chart at `x` to the chart at
  `(D.chart k x)⁻¹ z` sends `z` to `0`, its domain contains `z`, and its derivative at `z` has
  norm at most `√2` on a comparison radius, since `2π k σ(v, J v)` is the square of the norm in
  the chart at the centre (in the same namespace, `chartTransition_chart_symm_apply_self`,
  `mem_chartTransitionDomain_chart_symm` and `norm_fderiv_chartTransition_chart_symm_le`). Both
  bounds by `√2` come from one comparison of the charts
  (`norm_fderiv_chartTransition_le_of_norm_mvfderiv_le`).

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

/-- The transition from the chart centred at `y` to the chart centred at `x` is smooth on its
source: it is `C^n` there for every `n : ℕ∞`. -/
theorem contDiffOn_chartTransition {n : ℕ∞} {k : ℕ} {x y : M} :
    ContDiffOn ℝ n (D.chartTransition k x y) (D.chartTransition k x y).source := by
  rw [chartTransition_def]
  exact ((D.chart k y).contDiffOn_symm_trans (D.chart k x)).of_le (by exact_mod_cast le_top)

/-- The transition from the chart centred at `y` to the chart centred at `x` is smooth at each
point of its source: it is `C^n` there for every `n : ℕ∞`. -/
theorem contDiffAt_chartTransition {n : ℕ∞} {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    ContDiffAt ℝ n (D.chartTransition k x y) w :=
  D.contDiffOn_chartTransition.contDiffAt ((D.chartTransition k x y).open_source.mem_nhds hw)

/-- For `y` in the source of the chart centred at `x`, the centre `0` of the chart at `y` lies in
the source of the transition from the chart at `y` to the chart at `x`. -/
theorem zero_mem_chartTransition_source {k : ℕ} (hk : k₀ ≤ k) {x y : M}
    (hy : y ∈ (D.chart k x).source) : 0 ∈ (D.chartTransition k x y).source := by
  rw [mem_chartTransition_source_iff, D.chart_symm_zero hk]
  exact ⟨D.zero_mem_chart_target hk y, hy⟩

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

/-- **Transitions are complex linear for `J` read in the charts.** At a point `w` of the source
of the transition `τ` from the chart centred at `y` to the chart centred at `x`, the derivative of
`τ` at `w` is complex linear for `J_y(w)` and `J_x(τ w)`, where `J_y` and `J_x` are `J` read in
the two charts. -/
theorem isComplexLinear_fderiv_chartTransition {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    IsComplexLinear
      (J.chartPushforward (D.chart k y).toOpenPartialHomeomorph w : StdSpace ι →ₗ[ℝ] StdSpace ι)
      (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph (D.chartTransition k x y w) :
        StdSpace ι →ₗ[ℝ] StdSpace ι)
      (fderiv ℝ (D.chartTransition k x y) w : StdSpace ι →ₗ[ℝ] StdSpace ι) := by
  have h := J.chartPushforward_symm_trans_comp_fderiv (D.chart k y) (D.chart k x)
    (by rwa [chartTransition_def] at hw)
  rw [← chartTransition_def] at h
  exact isComplexLinear_of_apply fun v ↦ (DFunLike.congr_fun h v).symm

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
  have h := (D.isComplexLinear_fderiv_chartTransition hw).apply v
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h, D.stdForm_fderiv_chartTransition hk hw]

/-! ### The forms `ω₀(·, J ·)` read in the charts -/

/-- The bilinear form `g_{k,x}(w) = ω₀(·, J_x(w) ·)` at a point `w` of the chart centred at `x`
for the power `k`, where `J_x` is `J` read in that chart: the image of `J_x(w)` under the fixed
continuous linear map `stdFormCompRightL ι`, `A ↦ ω₀(·, A ·)`. It is symmetric and positive
definite only where `J` is compatible with `σ`, which the charts do not assume. The definition is
total; its value at a point `w` outside `(D.chart k x).target` is junk. -/
noncomputable def associatedBilinFormInChart (k : ℕ) (x : M) (w : StdSpace ι) :
    StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] ℝ :=
  stdFormCompRightL ι (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w)

/-- The form `g_{k,x}(w)` is the image of `J_x(w)` under `A ↦ ω₀(·, A ·)`. -/
theorem associatedBilinFormInChart_def (k : ℕ) (x : M) (w : StdSpace ι) :
    D.associatedBilinFormInChart k x w =
      stdFormCompRightL ι (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w) :=
  (rfl)

/-- `g_{k,x}(w)(u, v) = ω₀(u, J_x(w) v)`. -/
@[simp]
theorem associatedBilinFormInChart_apply (k : ℕ) (x : M) (w u v : StdSpace ι) :
    D.associatedBilinFormInChart k x w u v =
      stdForm ι u (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w v) := by
  rw [associatedBilinFormInChart_def, stdFormCompRightL_apply]

/-- On a boundaryless manifold, the field of forms `g_{k,x}` is smooth on the target of the chart
centred at `x`. -/
theorem contDiffOn_associatedBilinFormInChart [I.Boundaryless] (k : ℕ) (x : M) :
    ContDiffOn ℝ ∞ (D.associatedBilinFormInChart k x) (D.chart k x).target :=
  (ContinuousLinearMap.contDiff _).comp_contDiffOn
    (J.contDiffOn_chartPushforward_toOpenPartialHomeomorph (D.chart k x))

/-- On a boundaryless manifold, the field of forms `g_{k,x}` is smooth at each point of the target
of the chart centred at `x`. -/
theorem contDiffAt_associatedBilinFormInChart [I.Boundaryless] {k : ℕ} {x : M} {w : StdSpace ι}
    (hw : w ∈ (D.chart k x).target) :
    ContDiffAt ℝ ∞ (D.associatedBilinFormInChart k x) w :=
  (D.contDiffOn_associatedBilinFormInChart k x).contDiffAt
    ((D.chart k x).open_target.mem_nhds hw)

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
  exact norm_stdFormCompRightL_apply_le _

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
    J.contDiffAt_chartPushforward (D.chart k x) (D.ball_subset_target hk x hw)
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ r (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) w‖ :=
        L.norm_iteratedFDeriv_comp_left_le_of_forall_norm_le zero_le_one
          (fun A ↦ (hL A).trans_eq (one_mul _).symm) hJ (by exact_mod_cast le_top)
    _ ≤ D.bound r * (√k)⁻¹ := by
        rw [one_mul]
        exact D.iteratedFDeriv_jStruct_le hk hr x w hw

/-- **Jets of `J` read in the charts against `J₀`.** On a boundaryless manifold, for every order
`r` there is a constant `C ≥ 0`, independent of `k ≥ k₀` and of the centre `x`, such that at every
point `z` of the ball of radius `ρ₀ * √k`, the `r`-jet norm at `z` of `J_{k,x} - J₀`, for `J_{k,x}`
the structure `J` read in the chart centred at `x` and `J₀ = stdComplexStructure ι`, is at most
`C * (√k)⁻¹ * (1 + ‖z‖)`. -/
theorem exists_jetNormAt_chartPushforward_sub_le [I.Boundaryless] (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M) {z : StdSpace ι}, z ∈ ball 0 (ρ₀ * √k) →
      jetNormAt ℝ r (fun w ↦ J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w -
          LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) z ≤
        C * (√k)⁻¹ * (1 + ‖z‖) := by
  set S : ℝ := ∑ j ∈ Finset.range r, |D.bound (j + 1)|
  have : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  refine ⟨|D.bound 1| + r * S, by positivity, fun {k} hk x z hz ↦ ?_⟩
  have hJJ : ContDiffAt ℝ ∞ (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph) z :=
    J.contDiffAt_chartPushforward (D.chart k x) (D.ball_subset_target hk x hz)
  have hS : ∀ j < r, ‖iteratedFDeriv ℝ (j + 1) (fun w ↦
      J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w -
        LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap) z‖ ≤
      S * (√k)⁻¹ := by
    intro j hj
    rw [fun_iteratedFDeriv_sub_apply (hJJ.of_le (by exact_mod_cast le_top)) contDiffAt_const,
      iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
    refine (D.iteratedFDeriv_jStruct_le hk j.succ_ne_zero x z hz).trans ?_
    gcongr
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j ↦ |D.bound (j + 1)|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 hj))
  refine (jetNormAt_le_of_norm_iteratedFDeriv_succ_le hS).trans ?_
  have h1 := D.jStruct_sub_le hk x z hz
  have hb : D.bound 1 * (√k)⁻¹ * ‖z‖ ≤ |D.bound 1| * (√k)⁻¹ * ‖z‖ := by
    gcongr; exact le_abs_self _
  have : 0 ≤ (√k)⁻¹ := by positivity
  have : 0 ≤ |D.bound 1| * (√k)⁻¹ := by positivity
  have : 0 ≤ (r : ℝ) * S * (√k)⁻¹ * ‖z‖ := by positivity
  nlinarith

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
      stdFormCompRightL ι ∘ J.chartPushforward (D.chart k x).toOpenPartialHomeomorph :=
    funext (D.associatedBilinFormInChart_def k x)
  rw [hfun]
  exact D.norm_iteratedFDeriv_comp_chartPushforward_le norm_stdFormCompRightL_apply_le hk hr x
    hw

/-! ### Compatibility, symmetry and the inverse of the forms read in the charts -/

/-- At a point `w` of the target of the chart centred at `x`, for `k ≥ k₀`, `ω₀` is compatible
with `J` read in the chart at `w`, provided that `σ` is compatible with `J`: the chart pulls `ω₀`
back to `2π k σ`. -/
theorem stdForm_compatible_pushforwardAt (hJ : σ.Compatible J) {k : ℕ} (hk : k₀ ≤ k)
    (x : M) {w : StdSpace ι} (hw : w ∈ (D.chart k x).target) :
    (stdForm ι).Compatible ((D.chart k x).pushforwardAt J hw) := by
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
  · refine (hJ.smul (2 * Real.pi * k) (by positivity)).compatible_pushforwardAt
      (D.chart k x) (fun y hy u v ↦ ?_) hw
    rw [SmoothForm.eval₂_smul, smul_eq_mul]
    exact D.eval₂_eq hk x y hy u v

/-- **The forms read in the charts are symmetric.** If `σ` is compatible with `J`, then for
`k ≥ k₀` and `w` in the target of the chart centred at `x`, `g_{k,x}(w)(u, v) = g_{k,x}(w)(v, u)`.
-/
theorem associatedBilinFormInChart_apply_swap (hJ : σ.Compatible J) {k : ℕ} (hk : k₀ ≤ k)
    (x : M) {w : StdSpace ι} (hw : w ∈ (D.chart k x).target) (u v : StdSpace ι) :
    D.associatedBilinFormInChart k x w u v = D.associatedBilinFormInChart k x w v u := by
  simp only [associatedBilinFormInChart_apply,
    ← PartialDiffeomorph.pushforwardAt_apply_eq_chartPushforward_apply _ J hw]
  exact (D.stdForm_compatible_pushforwardAt hJ hk x hw).associatedBilinForm_apply_swap u v

/-- **The forms read in the charts are positive definite.** If `σ` is compatible with `J`, then
for `k ≥ k₀`, `w` in the target of the chart centred at `x` and `u ≠ 0`, `g_{k,x}(w)(u, u) > 0`. -/
theorem associatedBilinFormInChart_apply_self_pos (hJ : σ.Compatible J) {k : ℕ} (hk : k₀ ≤ k)
    (x : M) {w : StdSpace ι} (hw : w ∈ (D.chart k x).target) {u : StdSpace ι} (hu : u ≠ 0) :
    0 < D.associatedBilinFormInChart k x w u u := by
  rw [associatedBilinFormInChart_apply,
    ← PartialDiffeomorph.pushforwardAt_apply_eq_chartPushforward_apply _ J hw]
  exact (D.stdForm_compatible_pushforwardAt hJ hk x hw).tames u hu

/-- **The forms read in the charts are nondegenerate.** At a point `w` of the target of the chart
centred at `x`, the form `g_{k,x}(w)`, as a map from `StdSpace ι` to its dual, is invertible. This
only uses `J_x(w)² = -1`, not the compatibility of `J` with `σ`. -/
theorem isInvertible_associatedBilinFormInChart {k : ℕ} {x : M} {w : StdSpace ι}
    (hw : w ∈ (D.chart k x).target) : (D.associatedBilinFormInChart k x w).IsInvertible := by
  rw [associatedBilinFormInChart_def]
  exact isInvertible_stdFormCompRightL_apply fun u ↦ by
    rw [J.chartPushforward_toOpenPartialHomeomorph]
    exact (D.chart k x).pushforwardEndomorphism_apply_pushforwardEndomorphism J hw u

/-- **The inverse of the forms read in the charts.** At a point `w` of the target of the chart
centred at `x`, the inverse of `g_{k,x}(w)` is `stdFormCompRightInverseL ι` applied to `J_x(w)`: it
sends a linear form `φ` to `-Ω⁻¹ (φ ∘ J_x(w))`, `Ω` being `ω₀` as a map to the dual. -/
theorem inverse_associatedBilinFormInChart {k : ℕ} {x : M} {w : StdSpace ι}
    (hw : w ∈ (D.chart k x).target) :
    (D.associatedBilinFormInChart k x w).inverse =
      stdFormCompRightInverseL ι (J.chartPushforward (D.chart k x).toOpenPartialHomeomorph w) := by
  rw [associatedBilinFormInChart_def]
  exact inverse_stdFormCompRightL_apply fun u ↦ by
    rw [J.chartPushforward_toOpenPartialHomeomorph]
    exact (D.chart k x).pushforwardEndomorphism_apply_pushforwardEndomorphism J hw u

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

/-! ### The Christoffel symbols of the forms read in the charts -/

/-- **The Christoffel symbols of the forms read in the charts are smooth.** On a boundaryless
manifold, the Christoffel symbols of the second kind of the field of forms `g_{k,x}` are smooth on
the target of the chart centred at `x`, where `g_{k,x}` is smooth and invertible. -/
theorem contDiffOn_christoffelSecondKind_associatedBilinFormInChart [I.Boundaryless] (k : ℕ)
    (x : M) :
    ContDiffOn ℝ ∞ (Manifold.christoffelSecondKind (D.associatedBilinFormInChart k x))
      (D.chart k x).target :=
  Manifold.contDiffOn_christoffelSecondKind (D.chart k x).open_target
    (D.contDiffOn_associatedBilinFormInChart k x) (by simp) fun _ hw ↦
      ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.1
        (D.isInvertible_associatedBilinFormInChart hw)

/-- On a boundaryless manifold, the field `w ↦ g_{k,x}(w)⁻¹` of inverses is smooth on the target
of the chart centred at `x`. -/
theorem contDiffOn_inverse_associatedBilinFormInChart [I.Boundaryless] (k : ℕ) (x : M) :
    ContDiffOn ℝ ∞ (fun w ↦ (D.associatedBilinFormInChart k x w).inverse) (D.chart k x).target :=
  fun _ hw ↦ ((D.isInvertible_associatedBilinFormInChart hw).contDiffAt_map_inverse.comp _
    (D.contDiffAt_associatedBilinFormInChart hw)).contDiffWithinAt

/-- **Uniform bounds on the Christoffel symbols of the forms read in the charts.** On a
boundaryless manifold, for each `r` there is a constant `C` such that for all `j ≤ r`, all
`k ≥ k₀`, all `x` and all `w` in the ball of radius `ρ₀ * √k`, the `j`-th iterated derivative at
`w` of the Christoffel symbols of the second kind of `g_{k,x}` has norm at most `C * (√k)⁻¹`. The
factor `(√k)⁻¹` is there for `j = 0` too, since the Christoffel symbols are linear in the first
derivative of the forms. -/
theorem exists_norm_iteratedFDeriv_christoffelSecondKind_associatedBilinFormInChart_le
    [I.Boundaryless] (r : ℕ) :
    ∃ C : ℝ, ∀ j ≤ r, ∀ k, k₀ ≤ k → ∀ (x : M), ∀ w ∈ ball (0 : StdSpace ι) (ρ₀ * √k),
      ‖iteratedFDeriv ℝ j (Manifold.christoffelSecondKind (D.associatedBilinFormInChart k x)) w‖ ≤
        C * (√k)⁻¹ := by
  -- A bound on the `i`-th derivative of the inverses, valid on the balls for all `k ≥ 1`.
  let A : ℕ → ℝ := fun i ↦ if i = 0 then
    |‖LinearMap.toContinuousLinearMap (stdComplexStructure ι).toLinearMap‖ + |D.bound 1| * ρ₀|
    else |D.bound i|
  have hA0 (i : ℕ) : 0 ≤ A i := by simp only [A]; split_ifs <;> positivity
  let M₁ := ∑ i ∈ Finset.range (r + 1), A i
  let M₂ := ∑ m ∈ Finset.range (r + 1), |D.bound (m + 1)|
  refine ⟨christoffelSecondKindOfJetBilinNorm (StdSpace ι) * 2 ^ r * M₁ * M₂,
    fun j hj k hk x w hw ↦ ?_⟩
  have hwt := D.ball_subset_target hk x hw
  have hk0 : 0 < √k := (Real.sqrt_nonneg _).lt_of_ne fun h ↦ by
    simpa [← h] using pos_of_mem_ball hw
  have hk1 : (√k)⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 ?_)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h ↦ by simp [h] at hk0
  have hinv {i : ℕ} (hi : i ≤ j) :
      ‖iteratedFDeriv ℝ i (fun w ↦ (D.associatedBilinFormInChart k x w).inverse) w‖ ≤ M₁ := by
    refine le_trans ?_ (Finset.single_le_sum (fun i _ ↦ hA0 i)
      (Finset.mem_range.2 (Nat.lt_succ_of_le (hi.trans hj))))
    rcases eq_or_ne i 0 with rfl | hi0
    · rw [norm_iteratedFDeriv_zero]
      exact (D.norm_inverse_associatedBilinFormInChart_le_of_mem_ball hk x hw).trans
        (by simp [A, le_abs_self])
    · simp only [A, hi0, ite_false]
      calc _ ≤ D.bound i * (√k)⁻¹ :=
            D.norm_iteratedFDeriv_inverse_associatedBilinFormInChart_le hk hi0 x hw
        _ ≤ |D.bound i| * 1 := by gcongr; exact le_abs_self _
        _ = |D.bound i| := mul_one _
  have hder {m : ℕ} (hm : m ≤ j) :
      ‖iteratedFDeriv ℝ (m + 1) (D.associatedBilinFormInChart k x) w‖ ≤ M₂ * (√k)⁻¹ := by
    refine (D.norm_iteratedFDeriv_associatedBilinFormInChart_le hk m.succ_ne_zero x hw).trans ?_
    gcongr
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun m ↦ |D.bound (m + 1)|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le (hm.trans hj))))
  calc _ ≤ christoffelSecondKindOfJetBilinNorm (StdSpace ι) * 2 ^ j * M₁ * (M₂ * (√k)⁻¹) :=
        norm_iteratedFDeriv_christoffelSecondKind_le_of_forall_le
          (D.contDiffAt_associatedBilinFormInChart hwt)
          ((D.contDiffOn_inverse_associatedBilinFormInChart k x).contDiffAt
            ((D.chart k x).open_target.mem_nhds hwt)) (by exact_mod_cast le_top)
          (fun _ hi ↦ hinv hi) fun _ hm ↦ hder hm
    _ ≤ christoffelSecondKindOfJetBilinNorm (StdSpace ι) * 2 ^ r * M₁ * (M₂ * (√k)⁻¹) := by
        have hM₁ : 0 ≤ M₁ := Finset.sum_nonneg fun i _ ↦ hA0 i
        have hM₂ : 0 ≤ M₂ := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ one_le_two hj) (christoffelSecondKindOfJetBilinNorm_nonneg _)) hM₁)
          (mul_nonneg hM₂ (inv_nonneg.2 hk0.le))
    _ = _ := by ring

/-! ### The derivatives of the transitions at the centre -/

/-- At the centre `x` of the chart `D.chart k x`, for `k ≥ k₀`, the quadratic form
`2π k σ(v, J v)` of a tangent vector `v` at `x` is `‖u‖ ^ 2`, for `u` the image of `v` under the
derivative of the chart. -/
theorem eval₂_apply_self_eq_norm_sq {k : ℕ} (hk : k₀ ≤ k) (x : M) (v : TangentSpace I x) :
    2 * Real.pi * k * σ.eval₂ x v (J x v) = ‖mvfderiv I (D.chart k x) x v‖ ^ 2 := by
  have h : mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x (J x v) =
      J.chartPushforward (D.chart k x).toOpenPartialHomeomorph (D.chart k x x)
        (mfderiv I 𝓘(ℝ, StdSpace ι) (D.chart k x) x v) := by
    rw [J.chartPushforward_toOpenPartialHomeomorph]
    exact ((D.chart k x).pushforwardEndomorphism_mfderiv_apply J (D.mem_source hk x) v).symm
  rw [D.eval₂_eq hk x x (D.mem_source hk x), mvfderiv_apply_eq_mfderiv_apply (v := J x v), h,
    ← mvfderiv_apply_eq_mfderiv_apply, D.apply_self hk, D.chartPushforward_zero hk,
    stdForm_apply_stdComplexStructure, real_inner_self_eq_norm_sq]

/-- **The derivative of a transition, from a comparison of the two charts.** Let `w` be a point
of the source of the transition `τ` from the chart centred at `y` to the chart centred at `x`, and
let `c ≥ 0`. If, for every tangent vector `v` at `(D.chart k y)⁻¹ w`, the image of `v` under the
derivative of the chart at `x` has norm at most `c` times that of its image under the derivative
of the chart at `y`, then `‖Dτ(w)‖ ≤ c`. -/
theorem norm_fderiv_chartTransition_le_of_norm_mvfderiv_le {k : ℕ} {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v : TangentSpace I ((D.chart k y).symm w),
      ‖mvfderiv I (D.chart k x) ((D.chart k y).symm w) v‖ ≤
        c * ‖mvfderiv I (D.chart k y) ((D.chart k y).symm w) v‖) :
    ‖fderiv ℝ (D.chartTransition k x y) w‖ ≤ c := by
  have hwt : w ∈ (D.chart k y).target := (D.mem_chartTransition_source_iff.1 hw).1
  -- The derivative of the inverse of the chart at `y`, at `w`, and the chain rule there.
  have hinv := (D.chart k y).mfderiv_apply_mfderiv_symm_apply (by simp) hwt
  have hT := (D.chart k y).mvfderiv_eq_fderiv_symm_trans_comp (D.chart k x) (by simp)
    (by rwa [chartTransition_def] at hw)
  rw [← chartTransition_def] at hT
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun u ↦ ?_
  -- The tangent vector `v` that the chart at `y` sends to `u`; the chart at `x` sends it to the
  -- image of `u` under the derivative of the transition.
  set v : TangentSpace I ((D.chart k y).symm w) :=
    mfderiv 𝓘(ℝ, StdSpace ι) I (D.chart k y).symm w u
  have hu : mvfderiv I (D.chart k y) ((D.chart k y).symm w) v = u := by
    rw [mvfderiv_apply_eq_mfderiv_apply]
    exact hinv u
  have hTu : mvfderiv I (D.chart k x) ((D.chart k y).symm w) v =
      fderiv ℝ (D.chartTransition k x y) w u := by
    rw [hT, ContinuousLinearMap.comp_apply, hu]
  simpa only [hu, hTu] using h v

/-- **The derivative at the centre of a transition, on a comparison radius.** Let `k ≥ k₀`, let
`ρ₁` be a comparison radius for the chart centred at `x` (`IsComparisonRadius`), and let `y` be a
point of the source of that chart whose image lies in the ball of radius `ρ₁ * √k`. Then the
derivative at `0` of the transition from the chart centred at `y` to the chart centred at `x` has
norm at most `√2`. -/
theorem norm_fderiv_chartTransition_zero_le {ρ₁ : ℝ} {k : ℕ} (hk : k₀ ≤ k) {x : M}
    (hcmp : D.IsComparisonRadius k x ρ₁) {y : M} (hy : y ∈ (D.chart k x).source)
    (hyB : D.chart k x y ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    ‖fderiv ℝ (D.chartTransition k x y) 0‖ ≤ √2 := by
  refine D.norm_fderiv_chartTransition_le_of_norm_mvfderiv_le
    (D.zero_mem_chartTransition_source hk hy) (by positivity) ?_
  rw [D.chart_symm_zero hk y]
  intro v
  -- At the centre `y`, `2π k σ(v, J v)` is the squared norm in the chart at `y`.
  have hcmpy := (hcmp.mem_Icc hy hyB v).1
  rw [D.eval₂_apply_self_eq_norm_sq hk y v] at hcmpy
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

/-! ### Uniform bounds on the derivatives of the transitions -/

/-- For `k ≥ k₀`, the derivative of the transition from the chart centred at `y` to the chart
centred at `x`, at a point of its source, is bijective, since it preserves the symplectic form
`stdForm ι` of the finite-dimensional space `StdSpace ι`. -/
theorem bijective_fderiv_chartTransition {k : ℕ} (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι}
    (hw : w ∈ (D.chartTransition k x y).source) :
    Function.Bijective (fderiv ℝ (D.chartTransition k x y) w) :=
  (stdForm ι).bijective_of_forall_apply_eq_or_forall_apply_eq_neg
    (Ψ := (fderiv ℝ (D.chartTransition k x y) w : StdSpace ι →ₗ[ℝ] StdSpace ι))
    (.inl (D.stdForm_fderiv_chartTransition hk hw))

/-- **The second derivative of a transition.** On a boundaryless manifold, if `σ` is compatible
with `J`, then for `k ≥ k₀` and `w` in the source of the transition `τ` from the chart centred at
`y` to the chart centred at `x`, `D²τ(w) = Dτ(w) ∘ Γ_y(w) - Γ_x(τ w) ∘ (Dτ(w) × Dτ(w))`, where
`Γ_y` and `Γ_x` are the Christoffel symbols of the second kind of the forms `g_{k,y}` and
`g_{k,x}` read in the two charts. This is the Koszul formula
`SymplecticGeometry.fderiv_fderiv_eq_sub_christoffelSecondKind`, for the map `τ` that carries
`g_{k,y}` to `g_{k,x}`; compatibility makes `g_{k,x}` symmetric. -/
theorem fderiv_fderiv_chartTransition [I.Boundaryless] (hJ : σ.Compatible J) {k : ℕ}
    (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι} (hw : w ∈ (D.chartTransition k x y).source) :
    fderiv ℝ (fderiv ℝ (D.chartTransition k x y)) w =
      ContinuousLinearMap.compL ℝ _ _ _ (fderiv ℝ (D.chartTransition k x y) w) ∘L
          Manifold.christoffelSecondKind (D.associatedBilinFormInChart k y) w -
        (Manifold.christoffelSecondKind (D.associatedBilinFormInChart k x)
          (D.chartTransition k x y w)).bilinearComp (fderiv ℝ (D.chartTransition k x y) w)
          (fderiv ℝ (D.chartTransition k x y) w) := by
  have hwy : w ∈ (D.chart k y).target := (D.mem_chartTransition_source_iff.1 hw).1
  have hτx : D.chartTransition k x y w ∈ (D.chart k x).target := by
    rw [chartTransition_apply]
    exact (D.chart k x).map_source (D.mem_chartTransition_source_iff.1 hw).2
  refine fderiv_fderiv_eq_sub_christoffelSecondKind (D.chartTransition k x y).open_source
    D.contDiffOn_chartTransition (fun w' hw' u v ↦ ?_) hw
    (D.bijective_fderiv_chartTransition hk hw).2
    (ContinuousLinearMap.isInvertible_iff_nondegenerate_toBilinForm.1
      (D.isInvertible_associatedBilinFormInChart hwy))
    ((D.contDiffAt_associatedBilinFormInChart hτx).differentiableAt (by simp)) ?_
  · exact DFunLike.congr_fun (DFunLike.congr_fun
      (D.associatedBilinFormInChart_chartTransition_bilinearComp hk hw') u) v
  · filter_upwards [(D.chart k x).open_target.mem_nhds hτx] with w' hw'
    exact ContinuousLinearMap.isSymm_toBilinForm_iff.2
      (D.associatedBilinFormInChart_apply_swap hJ hk x hw')

/-- The right side of the Koszul formula for the transitions, as a function of the Christoffel
symbols `G` and `G'` of the source and target forms and of the derivative `L`:
`(G, G', L) ↦ L ∘ G - G' ∘ (L × L)`. -/
private noncomputable def koszulRHS
    (q : (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι) ×
      (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι) × (StdSpace ι →L[ℝ] StdSpace ι)) :
    StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι :=
  ContinuousLinearMap.compL ℝ _ _ _ q.2.2 ∘L q.1 -
    (ContinuousLinearMap.compL ℝ _ _ _).flip q.2.2 ∘L (q.2.1 ∘L q.2.2)

/-- The map `koszulRHS` is `(G, G', L) ↦ L ∘ G - G'.bilinearComp L L`. -/
private theorem koszulRHS_apply
    (q : (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι) ×
      (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι) × (StdSpace ι →L[ℝ] StdSpace ι)) :
    koszulRHS q =
      ContinuousLinearMap.compL ℝ _ _ _ q.2.2 ∘L q.1 - q.2.1.bilinearComp q.2.2 q.2.2 := by
  refine ContinuousLinearMap.ext fun u ↦ ContinuousLinearMap.ext fun v ↦ ?_
  simp [koszulRHS]

/-- The map `koszulRHS` is smooth: it is a polynomial in its arguments. -/
private theorem contDiff_koszulRHS : ContDiff ℝ ∞ (koszulRHS (ι := ι)) := by
  unfold koszulRHS
  fun_prop

/-- **Uniform bounds on the derivatives of the transitions.** On a boundaryless manifold, if `σ` is
compatible with `J`, then for every order `r` and every bound `B` there is a constant `C` with the
following property: for all `k ≥ k₀`, all points `x` and `y` and every `w` in
`D.chartTransitionDomain k x y` at which the derivative of the transition `τ` from the chart
centred at `y` to the chart centred at `x` has norm at most `B`, the `j`-th iterated derivative of
`τ` at `w` has norm at most `C` for all `1 ≤ j ≤ r`.

The pair `(τ, Dτ)` solves a first-order system by `fderiv_fderiv_chartTransition`, and the
Christoffel symbols of the forms read in the charts have uniformly bounded derivatives on the
balls of radius `ρ₀ * √k`
(`exists_norm_iteratedFDeriv_christoffelSecondKind_associatedBilinFormInChart_le`), so
`SymplecticGeometry.exists_forall_norm_iteratedFDeriv_le_of_fderiv_fderiv_eq` applies. -/
theorem exists_forall_norm_iteratedFDeriv_chartTransition_le [I.Boundaryless]
    (hJ : σ.Compatible J) (r : ℕ) (B : ℝ) :
    ∃ C : ℝ, ∀ {k : ℕ}, k₀ ≤ k → ∀ {x y : M} {w : StdSpace ι},
      w ∈ D.chartTransitionDomain k x y → ‖fderiv ℝ (D.chartTransition k x y) w‖ ≤ B →
      ∀ j, 1 ≤ j → j ≤ r → ‖iteratedFDeriv ℝ j (D.chartTransition k x y) w‖ ≤ C := by
  obtain ⟨CΓ, hCΓ⟩ :=
    D.exists_norm_iteratedFDeriv_christoffelSecondKind_associatedBilinFormInChart_le r
  have : ProperSpace (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι) :=
    FiniteDimensional.proper_real (StdSpace ι →L[ℝ] StdSpace ι →L[ℝ] StdSpace ι)
  have : ProperSpace (StdSpace ι →L[ℝ] StdSpace ι) :=
    FiniteDimensional.proper_real (StdSpace ι →L[ℝ] StdSpace ι)
  set R := max |CΓ| B
  -- Sets of norm at most `R` rather than closed balls: the closed ball's centre `0` cannot be
  -- matched with the zero that `mem_closedBall_zero_iff` expects in these spaces of maps.
  have hRc {V : Type _} [NormedAddCommGroup V] [ProperSpace V] : IsCompact {G : V | ‖G‖ ≤ R} :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_le continuous_norm continuous_const)
      (isBounded_iff_forall_norm_le.2 ⟨R, fun _ h ↦ h⟩)
  obtain ⟨K, hK⟩ := exists_forall_norm_iteratedFDeriv_le_of_fderiv_fderiv_eq (r := r)
    ((contDiff_koszulRHS (ι := ι)).of_le (by simp))
    (hRc.prod (hRc.prod hRc)) R
  refine ⟨K, fun {k} hk x y w hw hB j hj₁ hj ↦ ?_⟩
  obtain ⟨hwB, hws, hτB⟩ := D.mem_chartTransitionDomain_iff.1 hw
  have hwt : w ∈ (D.chart k y).target := (D.mem_chartTransition_source_iff.1 hws).1
  have hτt : D.chartTransition k x y w ∈ (D.chart k x).target := by
    rw [chartTransition_apply]
    exact (D.chart k x).map_source (D.mem_chartTransition_source_iff.1 hws).2
  have hk0 : 0 < √k := (Real.sqrt_nonneg _).lt_of_ne fun h ↦ by
    simpa [← h] using pos_of_mem_ball hwB
  have hk1 : (√k)⁻¹ ≤ 1 := by
    refine inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 ?_)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h ↦ by simp [h] at hk0
  have hΓ (x' : M) {w : StdSpace ι} (hw : w ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) (i : ℕ)
      (hi : i ≤ r) :
      ‖iteratedFDeriv ℝ i (Manifold.christoffelSecondKind (D.associatedBilinFormInChart k x'))
        w‖ ≤ R :=
    calc _ ≤ CΓ * (√k)⁻¹ := hCΓ i hi k hk x' w hw
      _ ≤ |CΓ| * 1 := by gcongr; exact le_abs_self _
      _ ≤ R := by rw [mul_one]; exact le_max_left _ _
  refine hK (τ := D.chartTransition k x y)
    (a := Manifold.christoffelSecondKind (D.associatedBilinFormInChart k y))
    (b := Manifold.christoffelSecondKind (D.associatedBilinFormInChart k x)) (w₀ := w)
    (D.contDiffAt_chartTransition hws)
    (((D.contDiffOn_christoffelSecondKind_associatedBilinFormInChart k y).contDiffAt
      ((D.chart k y).open_target.mem_nhds hwt)).of_le (by simp))
    (((D.contDiffOn_christoffelSecondKind_associatedBilinFormInChart k x).contDiffAt
      ((D.chart k x).open_target.mem_nhds hτt)).of_le (by simp))
    ?_ ?_ (fun i _ hi ↦ hΓ y hwB i hi) (fun i _ hi ↦ hΓ x hτB i hi) j hj₁ (by omega)
  · filter_upwards [(D.chartTransition k x y).open_source.mem_nhds hws] with w hw
    rw [koszulRHS_apply]
    exact D.fderiv_fderiv_chartTransition hJ hk hw
  · refine Set.mk_mem_prod ?_ (Set.mk_mem_prod ?_ ?_)
    · simpa using hΓ y hwB 0 (Nat.zero_le _)
    · simpa using hΓ x hτB 0 (Nat.zero_le _)
    · exact hB.trans (le_max_right _ _)

/-! ### The transitions back to the chart centred at a point of the ball -/

/-- For `k ≥ k₀`, the transition from the chart centred at `x` to the chart centred at
`(D.chart k x)⁻¹ z` sends `z` to `0`. -/
theorem chartTransition_chart_symm_apply_self {k : ℕ} (hk : k₀ ≤ k) (x : M) (z : StdSpace ι) :
    D.chartTransition k ((D.chart k x).symm z) x z = 0 := by
  rw [chartTransition_apply]
  exact D.apply_self hk _

/-- For `k ≥ k₀` and `z` in the ball of radius `ρ₀ * √k`, the domain of the transition from the
chart centred at `x` to the chart centred at `(D.chart k x)⁻¹ z` contains `z`. -/
theorem mem_chartTransitionDomain_chart_symm {k : ℕ} (hk : k₀ ≤ k) (x : M) {z : StdSpace ι}
    (hz : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) :
    z ∈ D.chartTransitionDomain k ((D.chart k x).symm z) x := by
  refine ⟨hz, D.mem_chartTransition_source_iff.2
    ⟨D.ball_subset_target hk x hz, D.mem_source hk _⟩, ?_⟩
  rw [Set.mem_preimage, D.chartTransition_chart_symm_apply_self hk]
  exact mem_ball_self (pos_of_mem_ball hz)

/-- **The derivative of a transition back to the centre, on a comparison radius.** Let `k ≥ k₀`,
let `ρ₁` be a comparison radius for the chart centred at `x` (`IsComparisonRadius`), and let `z`
be a point of the target of that chart in the ball of radius `ρ₁ * √k`. Then the derivative at
`z` of the transition from the chart centred at `x` to the chart centred at `(D.chart k x)⁻¹ z`
has norm at most `√2`. -/
theorem norm_fderiv_chartTransition_chart_symm_le {ρ₁ : ℝ} {k : ℕ} (hk : k₀ ≤ k) {x : M}
    (hcmp : D.IsComparisonRadius k x ρ₁) {z : StdSpace ι} (hzt : z ∈ (D.chart k x).target)
    (hz : z ∈ ball (0 : StdSpace ι) (ρ₁ * √k)) :
    ‖fderiv ℝ (D.chartTransition k ((D.chart k x).symm z) x) z‖ ≤ √2 := by
  set y := (D.chart k x).symm z
  have hy : y ∈ (D.chart k x).source := (D.chart k x).map_target hzt
  have hzs : z ∈ (D.chartTransition k y x).source :=
    D.mem_chartTransition_source_iff.2 ⟨hzt, D.mem_source hk y⟩
  refine D.norm_fderiv_chartTransition_le_of_norm_mvfderiv_le hzs (by positivity) fun v ↦ ?_
  -- At the centre `y`, `2π k σ(v, J v)` is the squared norm in the chart at `y`.
  have hyz : D.chart k x y = z := (D.chart k x).right_inv hzt
  have hcmpy := (hcmp.mem_Icc hy (by rwa [hyz]) v).2
  rw [D.eval₂_apply_self_eq_norm_sq hk y v] at hcmpy
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, Real.sq_sqrt zero_le_two]
  nlinarith [sq_nonneg ‖mvfderiv I (D.chart k x) y v‖]

end RescaledUnitaryCharts

end SymplecticGeometry

end
