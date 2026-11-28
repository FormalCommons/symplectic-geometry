/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.FrameChange
import TauCeti.Analysis.Calculus.ContDiff.Differentiable

/-!
# Jet norms under a change of rescaled unitary chart

Let `D` be rescaled unitary charts, `k ≥ k₀` a power, `x` a point and `y = (D.chart k x)⁻¹ z` the
point with coordinate `z` in the chart centred at `x`. The jet norm `D.jetNorm k r s y` of a
section `s` of `PowerBundle P k` is read in the chart centred at `y`. This file bounds it by the
jet norm at `z` of the reading of `s` in the chart centred at `x`, times a polynomial in the
rescaled distance `d_k(x, y) = √(2π k) · d_g(x, y)`, uniformly in `k`, `x` and `z` in a ball of
radius `ρ * √k`.

Near `0`, the reading in the chart at `y` is `e · (f ∘ τ)`, for `f` the reading in the chart at
`x`, `τ` the transition from the chart at `y` to the chart at `x` and `e` the change of frame
(`SymplecticGeometry.RescaledUnitaryCharts.reading_eq_frameChange_mul`). The Leibniz bound
`SymplecticGeometry.jetNormAt_fun_smul_le` and the Faà di Bruno bound
`SymplecticGeometry.jetNormAt_comp_le` reduce the jet norm of this product, at any point `w` of
the domain of `τ`, to those of `e` and `τ` at `w`
(`SymplecticGeometry.RescaledUnitaryCharts.jetNormAt_reading_le_frameChange_mul`). Where
`‖Dτ(w)‖` is bounded, both are at most polynomials in `‖w‖` and `‖τ w‖`, by
`RescaledUnitaryCharts.exists_forall_jetNormAt_frameChange_le` and
`RescaledUnitaryCharts.exists_forall_norm_iteratedFDeriv_chartTransition_le` with
`SymplecticGeometry.jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le`; these bounds
are gathered in
`RescaledUnitaryCharts.exists_forall_jetNormAt_chartChange_le_of_norm_fderiv_le`.
At `w = 0`, where `‖Dτ(0)‖ ≤ √2` and `τ 0 = z`, they are polynomials in `‖z‖`, and
`‖z‖ ≤ √2 * d_k(x, y)`
(`RescaledUnitaryCharts.norm_le_sqrt_two_mul_rescaledDist_symm`) turns the
bound into a polynomial in `d_k(x, y)`. The bounds at `0` that both results below use, on the
jets of `e`, of `dτ` and of a map composed with `τ`, are gathered in
`SymplecticGeometry.RescaledUnitaryCharts.exists_forall_jetNormAt_chartChange_le`.

The same holds for the `∂̄` reading `D.dbarReading k y s` of `s`, whose jet norm at `0` is
`D.dbarJetNorm k r s y`. Near each point `w` of the domain it is `e • ((g ∘ τ) ∘L dτ)`, for `g`
the `∂̄` reading in the chart at `x`
(`SymplecticGeometry.RescaledUnitaryCharts.dbarReading_eventuallyEq_frameChange_smul_comp`), and
the bilinear bound `SymplecticGeometry.jetNormAt_bilinear_le` takes care of the composition with
`dτ` (`SymplecticGeometry.RescaledUnitaryCharts.jetNormAt_dbarReading_le_frameChange_mul`). The
jets of `dτ` are bounded by those of `τ` of orders `1` to `r + 1`, with no factor `‖z‖`
(`SymplecticGeometry.jetNormAt_fderiv_le_of_norm_iteratedFDeriv_succ_le`). The exponent is again
`2 * r`.

The file also goes the other way, which is what is needed to control one function on a whole
ball of the chart at `x`: the jet norm at `z` of the reading of `s` in the chart at `x` is
bounded by the jet norm of `s` at `y`. Near `z`, that reading is `e' · (f_y ∘ τ')`, for `f_y`
the reading in the chart at `y`, `τ'` the transition from the chart at `x` to the chart at `y`,
which sends `z` to `0`, and `e'` the change of frame between these charts. The same pointwise
bounds apply at `w = z`, where `‖Dτ'(z)‖ ≤ √2`
(`RescaledUnitaryCharts.norm_fderiv_chartTransition_chart_symm_le`). Since `τ' z = 0`, the
Faà di Bruno bound for `f_y ∘ τ'` has no factor `‖z‖`, and only the change of frame brings one,
so the exponent is `r`. Smoothness moves the same way, and for an asymptotically holomorphic
sequence the bounds at the centres become bounds on balls of fixed radius.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.jetNormAt_reading_le_frameChange_mul` and
  `SymplecticGeometry.RescaledUnitaryCharts.jetNormAt_dbarReading_le_frameChange_mul`: at a point
  `w` of the domain of the transition, the jet norm of the reading (and of the `∂̄` reading) in
  one chart is bounded by those of the change of frame, of the reading in the other chart
  composed with the transition (and of the derivative of the transition).
* `RescaledUnitaryCharts.exists_forall_jetNormAt_chartChange_le_of_norm_fderiv_le`: the bounds at
  such a point `w` on the jets of the change of frame, of the derivative of the transition and of
  a map composed with the transition, where the derivative of the transition is bounded.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_jetNormAt_chartChange_le`: the bounds
  at `0` on the jets of the change of frame, of the derivative of the transition and of a map
  composed with the transition, and `(1 + ‖z‖) ^ (2 * r) ≤ 2 ^ r * (1 + d_k(x, y)) ^ (2 * r)`.
* `SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`: for every `r`,
  `D.jetNorm k r s y ≤ C * (1 + d_k(x, y)) ^ (2 * r) * jetNormAt ℝ r (D.reading k x s) z`.
* `SymplecticGeometry.RescaledUnitaryCharts.dbarJetNorm_le_of_chart_change`: for every `r`,
  `D.dbarJetNorm k r s y ≤ C * (1 + d_k(x, y)) ^ (2 * r) * jetNormAt ℝ r (D.dbarReading k x s) z`.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_jetNormAt_chartChange_chart_symm_le`:
  the bounds at `z` on the jets of the change of frame and of the transition back to the chart
  at `y`.
* `SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_reading_of_chart_change` and
  `SymplecticGeometry.RescaledUnitaryCharts.contDiffAt_dbarReading_of_chart_change`: if the
  reading (and the `∂̄` reading) of `s` in the chart at `y` is `C^n` at `0`, then so is the
  reading (and the `∂̄` reading) in the chart at `x` at `z`.
* `SymplecticGeometry.RescaledUnitaryCharts.jetNormAt_reading_le_of_chart_change`: for every `r`,
  `jetNormAt ℝ r (D.reading k x s) z ≤ C * (1 + d_k(x, y)) ^ r * D.jetNorm k r s y`.
* `SymplecticGeometry.RescaledUnitaryCharts.jetNormAt_dbarReading_le_of_chart_change`: for every
  `r`, `jetNormAt ℝ r (D.dbarReading k x s) z ≤ C * (1 + d_k(x, y)) ^ r * D.dbarJetNorm k r s y`.
* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_jetNormAt_le_jetNorm_of_mem_ball`: for a
  fixed radius `R` and large `k`, smoothness and `r`-jet norms of the readings (and `∂̄` readings)
  of any section at a point `z` of the ball of radius `R` of the chart at `x` are controlled, up
  to a constant independent of `k`, `x`, `z` and the section, by those at `(D.chart k x)⁻¹ z`.
* `SymplecticGeometry.RescaledUnitaryCharts.IsAsymptoticallyHolomorphic.exists_forall_jetNormAt_le`:
  for an asymptotically holomorphic sequence and a fixed radius `R`, there is `C ≥ 0` such that
  for large `k` the readings and `∂̄` readings are smooth on the ball of radius `R` of every
  chart, with `r`-jet norms at most `C` and `C * k ^ (-1/2)`.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped Manifold ContDiff Topology Nat
open TauCeti Metric Bundle

namespace SymplecticGeometry

namespace RescaledUnitaryCharts

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ι : Type*} [Fintype ι]
  {P : M → Type*} [TopologicalSpace (TotalSpace Circle P)] [∀ x, TopologicalSpace (P x)]
  [FiberBundle Circle P] [∀ x, MulAction Circleᵐᵒᵖ (P x)] [PrincipalBundle Circle P]
  [ContMDiffFiberBundle ∞ Circle P I (𝓡 1)]
  {σ : SmoothTwoForm I M} {J : SmoothAlmostComplexStructure I M}
  {α : SmoothForm (I.prod (𝓡 1)) (ManifoldTotalSpace Circle P) ℝ 1} {k₀ : ℕ} {ρ₀ : ℝ}
  (D : RescaledUnitaryCharts P σ J α ι k₀ ρ₀)

/-! ### At a point of the domain of a transition -/

/-- **The jet of a reading under a change of chart, at a point.** Let `k ≥ k₀`, `τ` the transition
from the chart centred at `y` to the chart centred at `x`, `e` the change of frame between them and
`w` a point of `D.chartTransitionDomain k x y`. For a section `s` of `PowerBundle P k` whose
reading `f` in the chart at `x` is `C^r` at `τ w`, the `r`-jet norm at `w` of the reading of `s` in
the chart at `y` is at most `2 ^ r` times the product of the `r`-jet norms of `e` and of `f ∘ τ`
at `w`. -/
theorem jetNormAt_reading_le_frameChange_mul {k : ℕ} (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι}
    (hw : w ∈ D.chartTransitionDomain k x y) {r : ℕ} {s : Π y, PowerBundle P k y}
    (hs : ContDiffAt ℝ r (D.reading k x s) (D.chartTransition k x y w)) :
    jetNormAt ℝ r (D.reading k y s) w ≤ 2 ^ r * jetNormAt ℝ r (D.frameChange k x y) w *
      jetNormAt ℝ r (D.reading k x s ∘ D.chartTransition k x y) w := by
  have hws := D.chartTransitionDomain_subset_source k x y hw
  -- Near `w`, the reading at `y` is `e • (f ∘ τ)`.
  have heq : D.reading k y s =ᶠ[𝓝 w] fun w' ↦
      D.frameChange k x y w' • (D.reading k x s ∘ D.chartTransition k x y) w' := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      D.reading_eventuallyEq_frameChange_mul hws s
  rw [jetNormAt_congr_of_eventuallyEq r heq]
  exact jetNormAt_fun_smul_le (D.contDiffAt_frameChange hk hw)
    (hs.comp w (D.contDiffAt_chartTransition hws))

/-- **The jet of a `∂̄` reading under a change of chart, at a point.** Let `α` be a connection
form, `k ≥ k₀`, `τ` the transition from the chart centred at `y` to the chart centred at `x`, `e`
the change of frame between them and `w` a point of `D.chartTransitionDomain k x y`. For a section
`s` of `PowerBundle P k` whose reading in the chart at `x` is differentiable near `τ w` and whose
`∂̄` reading `g` in that chart is `C^r` at `τ w`, the `r`-jet norm at `w` of the `∂̄` reading of `s`
in the chart at `y` is at most `4 ^ r` times the product of the `r`-jet norms of `e`, of `g ∘ τ`
and of `dτ` at `w`. -/
theorem jetNormAt_dbarReading_le_frameChange_mul (hα : IsCircleConnectionForm α) {k : ℕ}
    (hk : k₀ ≤ k) {x y : M} {w : StdSpace ι} (hw : w ∈ D.chartTransitionDomain k x y) {r : ℕ}
    {s : Π y, PowerBundle P k y}
    (hs : ∀ᶠ u in 𝓝 (D.chartTransition k x y w), DifferentiableAt ℝ (D.reading k x s) u)
    (hds : ContDiffAt ℝ r (D.dbarReading k x s) (D.chartTransition k x y w)) :
    jetNormAt ℝ r (D.dbarReading k y s) w ≤ 4 ^ r * jetNormAt ℝ r (D.frameChange k x y) w *
      jetNormAt ℝ r (D.dbarReading k x s ∘ D.chartTransition k x y) w *
      jetNormAt ℝ r (fderiv ℝ (D.chartTransition k x y)) w := by
  set τ := D.chartTransition k x y
  set g := D.dbarReading k x s
  have hτ : ContDiffAt ℝ (r + 1) τ w :=
    D.contDiffAt_chartTransition (D.chartTransitionDomain_subset_source k x y hw)
  have hgτ : ContDiffAt ℝ r (g ∘ τ) w := hds.comp w (hτ.of_le (by simp))
  have hdτ : ContDiffAt ℝ r (fderiv ℝ τ) w := hτ.fderiv_right le_rfl
  have hjgτ := jetNormAt_nonneg (𝕜 := ℝ) r (g ∘ τ) w
  have hjdτ := jetNormAt_nonneg (𝕜 := ℝ) r (fderiv ℝ τ) w
  -- Near `w`, the `∂̄` reading at `y` is `e • ((g ∘ τ) ∘L dτ)`.
  have heq : D.dbarReading k y s =ᶠ[𝓝 w] fun w' ↦ D.frameChange k x y w' •
      ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ ((g ∘ τ) w') (fderiv ℝ τ w') := by
    simpa only [ContinuousLinearMap.compL_apply, Function.comp_apply] using
      D.dbarReading_eventuallyEq_frameChange_smul_comp hα hk hw hs
  -- The jet of `(g ∘ τ) ∘L dτ`, a bilinear combination of `g ∘ τ` and `dτ`.
  have hgτd : jetNormAt ℝ r (fun w' ↦ ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ
      ((g ∘ τ) w') (fderiv ℝ τ w')) w ≤
        2 ^ r * jetNormAt ℝ r (g ∘ τ) w * jetNormAt ℝ r (fderiv ℝ τ) w := by
    refine (jetNormAt_bilinear_le _ hgτ hdτ).trans ?_
    have hB := ContinuousLinearMap.norm_compL_le ℝ (StdSpace ι) (StdSpace ι) ℂ
    calc _ ≤ 2 ^ r * 1 * jetNormAt ℝ r (g ∘ τ) w * jetNormAt ℝ r (fderiv ℝ τ) w := by gcongr
      _ = _ := by rw [mul_one]
  have hcomp : ContDiffAt ℝ r (fun w' ↦ ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ
      ((g ∘ τ) w') (fderiv ℝ τ w')) w := by
    simpa only [ContinuousLinearMap.compL_apply] using hgτ.clm_comp hdτ
  rw [jetNormAt_congr_of_eventuallyEq r heq]
  calc _ ≤ 2 ^ r * jetNormAt ℝ r (D.frameChange k x y) w * jetNormAt ℝ r (fun w' ↦
        ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ ((g ∘ τ) w') (fderiv ℝ τ w')) w :=
        jetNormAt_fun_smul_le (D.contDiffAt_frameChange hk hw) hcomp
    _ ≤ 2 ^ r * jetNormAt ℝ r (D.frameChange k x y) w *
        (2 ^ r * jetNormAt ℝ r (g ∘ τ) w * jetNormAt ℝ r (fderiv ℝ τ) w) :=
        mul_le_mul_of_nonneg_left hgτd (mul_nonneg (by positivity) (jetNormAt_nonneg _ _ _))
    _ = _ := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        ring

/-- **Bounds at a point for a change of chart.** On a boundaryless manifold, let `σ` be
compatible with `J` and let `α` be a connection form. For every order `r` and every bound `B`
there is a constant `C ≥ 0` with the following property. Let `k ≥ k₀`, `x` and `y` points, `τ`
the transition from the chart centred at `y` to the chart centred at `x`, `e` the change of frame
between them, and `w` a point of `D.chartTransitionDomain k x y` with `‖Dτ(w)‖ ≤ B`. Then the
`r`-jet norm of `e` at `w` is at most `C * (1 + ‖w‖ + ‖τ w‖) ^ r`, that of `dτ` at `w` is at most
`C`, and that of `g ∘ τ` at `w` is at most `C * (1 + ‖τ w‖) ^ r` times that of `g` at `τ w`, for
every `g` that is `C^r` at `τ w`. -/
theorem exists_forall_jetNormAt_chartChange_le_of_norm_fderiv_le [I.Boundaryless]
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (r : ℕ) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ {x y : M} {w : StdSpace ι},
      w ∈ D.chartTransitionDomain k x y → ‖fderiv ℝ (D.chartTransition k x y) w‖ ≤ B →
        jetNormAt ℝ r (D.frameChange k x y) w ≤
          C * (1 + ‖w‖ + ‖D.chartTransition k x y w‖) ^ r ∧
        jetNormAt ℝ r (fderiv ℝ (D.chartTransition k x y)) w ≤ C ∧
        (∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : StdSpace ι → F},
          ContDiffAt ℝ r g (D.chartTransition k x y w) →
          jetNormAt ℝ r (g ∘ D.chartTransition k x y) w ≤
            C * jetNormAt ℝ r g (D.chartTransition k x y w) *
              (1 + ‖D.chartTransition k x y w‖) ^ r) := by
  -- One bound `Cτ` for the derivatives of orders `1` to `r + 1` of the transition serves the
  -- change of frame and the jets of `τ` and of `dτ`.
  obtain ⟨Cτ, hCτ0, hCτ⟩ := D.exists_forall_norm_iteratedFDeriv_chartTransition_le hJ (r + 1) B
  obtain ⟨Ce, hCe0, hCe⟩ := D.exists_forall_jetNormAt_frameChange_le hα r Cτ
  set A : ℝ := 1 + r * Cτ
  have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  set C : ℝ := Ce + (r + 1)! * A ^ r + (r + 1) * Cτ
  have hCA : 0 ≤ ((r + 1)! : ℝ) * A ^ r := by positivity
  refine ⟨C, by positivity, fun {k} hk x y w hw hB ↦ ?_⟩
  set τ := D.chartTransition k x y
  have hCτw := hCτ hk hw hB
  have hτr : ContDiffAt ℝ r τ w :=
    D.contDiffAt_chartTransition (D.chartTransitionDomain_subset_source k x y hw)
  refine ⟨?_, ?_, fun {F} _ _ {g} hg ↦ ?_⟩
  · -- The change of frame.
    exact (hCe hk hw hCτw).trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  · -- The derivative of the transition.
    exact (jetNormAt_fderiv_le_of_norm_iteratedFDeriv_succ_le fun j hj ↦
      hCτw (j + 1) (by omega) (by omega)).trans (by linarith)
  · -- Faà di Bruno for `g ∘ τ`, with `max 1 (jetNormAt ℝ r τ w) ≤ A * (1 + ‖τ w‖)`.
    have hjτ : max 1 (jetNormAt ℝ r τ w) ≤ A * (1 + ‖τ w‖) :=
      max_le (by nlinarith [norm_nonneg (τ w)])
        ((jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le fun j hj ↦
          hCτw (j + 1) (by omega) (by omega)))
    have hjg := jetNormAt_nonneg (𝕜 := ℝ) r g (τ w)
    refine (jetNormAt_comp_le hg hτr).trans ?_
    calc _ ≤ (r + 1)! * jetNormAt ℝ r g (τ w) * (A * (1 + ‖τ w‖)) ^ r :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjτ r) (by positivity)
      _ = (r + 1)! * A ^ r * jetNormAt ℝ r g (τ w) * (1 + ‖τ w‖) ^ r := by rw [mul_pow]; ring
      _ ≤ C * jetNormAt ℝ r g (τ w) * (1 + ‖τ w‖) ^ r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hjg)
            (by positivity)

/-! ### From the chart at the centre to the chart at a point of the ball -/

/-- **Bounds at the centre for a change of chart.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`, there is a radius `ρ` with
`0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C ≥ 0` with the following
property. Let `k ≥ k₀`, `x` a point, `z` in the ball of radius `ρ * √k`, `y = (D.chart k x)⁻¹ z`,
`τ` the transition from the chart centred at `y` to the chart centred at `x` and `e` the change
of frame between them. Then `0` lies in `D.chartTransitionDomain k x y`, `τ 0 = z`, `e` is `C^r`
at `0`, the `r`-jet norm of `e` at `0` is at most `C * (1 + ‖z‖) ^ r`, that of `dτ` at `0` is at
most `C`, that of `g ∘ τ` at `0` is at most `C * (1 + ‖z‖) ^ r` times that of `g` at `z` for every
`g` that is `C^r` at `z`, and `(1 + ‖z‖) ^ (2 * r) ≤ 2 ^ r * (1 + d_k(x, y)) ^ (2 * r)`, for
`d_k(x, y) = √(2π k) · d_g(x, y)` the rescaled Riemannian distance
`rescaledDist I k x y`. -/
theorem exists_forall_jetNormAt_chartChange_le [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k),
        0 ∈ D.chartTransitionDomain k x ((D.chart k x).symm z) ∧
        D.chartTransition k x ((D.chart k x).symm z) 0 = z ∧
        ContDiffAt ℝ r (D.frameChange k x ((D.chart k x).symm z)) 0 ∧
        jetNormAt ℝ r (D.frameChange k x ((D.chart k x).symm z)) 0 ≤ C * (1 + ‖z‖) ^ r ∧
        jetNormAt ℝ r (fderiv ℝ (D.chartTransition k x ((D.chart k x).symm z))) 0 ≤ C ∧
        (∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : StdSpace ι → F},
          ContDiffAt ℝ r g z →
          jetNormAt ℝ r (g ∘ D.chartTransition k x ((D.chart k x).symm z)) 0 ≤
            C * jetNormAt ℝ r g z * (1 + ‖z‖) ^ r) ∧
        (1 + ‖z‖) ^ (2 * r) ≤
          2 ^ r * (1 + rescaledDist I k x ((D.chart k x).symm z)) ^ (2 * r) := by
  obtain ⟨ρ₁, hρ₁, -, hT⟩ := D.exists_forall_norm_fderiv_chartTransition_zero_le hρ₀
  obtain ⟨ρ₃, hρ₃, hρ₃₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  refine ⟨min ρ₁ ρ₃, lt_min hρ₁ hρ₃, (min_le_right _ _).trans hρ₃₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := D.exists_forall_jetNormAt_chartChange_le_of_norm_fderiv_le hJ hα r √2
  refine ⟨C, hC, fun {k} hk x z hz ↦ ?_⟩
  have hball {ρ' : ℝ} (h : min ρ₁ ρ₃ ≤ ρ') : z ∈ ball (0 : StdSpace ι) (ρ' * √k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)) hz
  have hz₁ := hball (min_le_left _ _)
  have hz₃ := hball (min_le_right _ _)
  have hz₀ := hball ((min_le_right _ _).trans hρ₃₀)
  set y := (D.chart k x).symm z
  set d := rescaledDist I k x y
  have hτ0 : D.chartTransition k x y 0 = z :=
    D.chartTransition_symm_zero hk (D.ball_subset_target hk x hz₀)
  have h0W := D.zero_mem_chartTransitionDomain hk x hz₀
  obtain ⟨he, hdτ, hcomp⟩ := hB hk h0W (hT hk x z hz₁)
  rw [hτ0, norm_zero, add_zero] at he
  rw [hτ0] at hcomp
  refine ⟨h0W, hτ0, D.contDiffAt_frameChange hk h0W, he, hdτ, fun hg ↦ hcomp hg, ?_⟩
  -- The rescaled distance bounds `‖z‖`: `1 + ‖z‖ ≤ √2 * (1 + d)`.
  have hz0 : 0 ≤ 1 + ‖z‖ := by positivity
  have hd : 1 + ‖z‖ ≤ √2 * (1 + d) := by
    have h := D.norm_le_sqrt_two_mul_rescaledDist_symm hg hρ₃₀ hk x
      (hcmp hk x) hz₃
    nlinarith [Real.one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 2)]
  have hd2 : (1 + ‖z‖) ^ 2 ≤ 2 * (1 + d) ^ 2 :=
    calc (1 + ‖z‖) ^ 2 ≤ (√2 * (1 + d)) ^ 2 := pow_le_pow_left₀ hz0 hd 2
      _ = 2 * (1 + d) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
  calc (1 + ‖z‖) ^ (2 * r) = ((1 + ‖z‖) ^ 2) ^ r := pow_mul _ _ _
    _ ≤ (2 * (1 + d) ^ 2) ^ r := pow_le_pow_left₀ (by positivity) hd2 r
    _ = 2 ^ r * (1 + d) ^ (2 * r) := by rw [mul_pow, pow_mul]

/-- **Jet norms under a change of chart.** Let `M` be a Hausdorff boundaryless manifold, let `σ`
be compatible with `J`, and let `M` carry a Riemannian metric whose inner product is
`⟪u, w⟫ = σ(u, J w)`, the metric `g_J` of the pair. Let `α` be a connection form and `ρ₀ > 0`.
There is a radius `ρ` with `0 < ρ ≤ ρ₀` such that for every order `r` there is a constant
`C ≥ 0` with the following property. For all `k ≥ k₀`, all points `x`, all `z` in the ball of radius
`ρ * √k`, and every section `s` of `PowerBundle P k` whose reading in the chart centred at `x` is
`C^r` at `z`, the `r`-jet norm of `s` at `y = (D.chart k x)⁻¹ z` is at most
`C * (1 + d_k(x, y)) ^ (2 * r)` times the `r`-jet norm at `z` of the reading of `s` in the chart
centred at `x`. Here `d_k(x, y)` is the real number `√(2π k) · d_g(x, y)`, the rescaled
Riemannian distance `rescaledDist I k x y`. -/
theorem jetNorm_le_of_chart_change [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k), ∀ {s : Π y, PowerBundle P k y},
        ContDiffAt ℝ r (D.reading k x s) z →
        D.jetNorm k r s ((D.chart k x).symm z) ≤
          C * (1 + rescaledDist I k x ((D.chart k x).symm z)) ^ (2 * r) *
            jetNormAt ℝ r (D.reading k x s) z := by
  obtain ⟨ρ, hρ, hρρ₀, hB⟩ := D.exists_forall_jetNormAt_chartChange_le hg hJ hα hρ₀
  refine ⟨ρ, hρ, hρρ₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := hB r
  refine ⟨4 ^ r * C ^ 2, by positivity, fun {k} hk x z hz {s} hs ↦ ?_⟩
  obtain ⟨h0W, hτ0, -, he, -, hcomp, hd⟩ := hB hk x z hz
  set y := (D.chart k x).symm z
  set f := D.reading k x s
  set d := rescaledDist I k x y
  have hjf := jetNormAt_nonneg (𝕜 := ℝ) r f z
  calc D.jetNorm k r s y ≤ 2 ^ r * jetNormAt ℝ r (D.frameChange k x y) 0 *
        jetNormAt ℝ r (f ∘ D.chartTransition k x y) 0 := by
        rw [jetNorm_def]
        exact D.jetNormAt_reading_le_frameChange_mul hk h0W (by rwa [hτ0])
    _ ≤ 2 ^ r * (C * (1 + ‖z‖) ^ r) * (C * jetNormAt ℝ r f z * (1 + ‖z‖) ^ r) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) (hcomp hs)
          (jetNormAt_nonneg _ _ _) (by positivity)
    _ = 2 ^ r * C ^ 2 * (1 + ‖z‖) ^ (2 * r) * jetNormAt ℝ r f z := by ring
    _ ≤ 2 ^ r * C ^ 2 * (2 ^ r * (1 + d) ^ (2 * r)) * jetNormAt ℝ r f z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) hjf
    _ = 4 ^ r * C ^ 2 * (1 + d) ^ (2 * r) * jetNormAt ℝ r f z := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        ring

/-- **Jet norms of `∂̄` under a change of chart.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`, there is a radius `ρ` with
`0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C ≥ 0` with the following property.
For all `k ≥ k₀`, all points `x`, all `z` in the ball of radius `ρ * √k`, and every section `s` of
`PowerBundle P k` whose reading in the chart centred at `x` is differentiable near `z` and whose
`∂̄` reading in that chart is `C^r` at `z`, the `r`-jet norm of the `∂̄` reading of `s` at
`y = (D.chart k x)⁻¹ z` is at most `C * (1 + d_k(x, y)) ^ (2 * r)` times the `r`-jet norm at `z`
of the `∂̄` reading of `s` in the chart centred at `x`. Here `d_k(x, y)` is the real number
`√(2π k) · d_g(x, y)`, the rescaled Riemannian distance `rescaledDist I k x y`. -/
theorem dbarJetNorm_le_of_chart_change [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k), ∀ {s : Π y, PowerBundle P k y},
        (∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (D.reading k x s) w) →
        ContDiffAt ℝ r (D.dbarReading k x s) z →
        D.dbarJetNorm k r s ((D.chart k x).symm z) ≤
          C * (1 + rescaledDist I k x ((D.chart k x).symm z)) ^ (2 * r) *
            jetNormAt ℝ r (D.dbarReading k x s) z := by
  obtain ⟨ρ, hρ, hρρ₀, hB⟩ := D.exists_forall_jetNormAt_chartChange_le hg hJ hα hρ₀
  refine ⟨ρ, hρ, hρρ₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := hB r
  refine ⟨8 ^ r * C ^ 3, by positivity, fun {k} hk x z hz {s} hs hds ↦ ?_⟩
  obtain ⟨h0W, hτ0, -, he, hjdτ, hcomp, hd⟩ := hB hk x z hz
  set y := (D.chart k x).symm z
  set g := D.dbarReading k x s
  set d := rescaledDist I k x y
  have hjg := jetNormAt_nonneg (𝕜 := ℝ) r g z
  have hjgτ := jetNormAt_nonneg (𝕜 := ℝ) r (g ∘ D.chartTransition k x y) 0
  have hjdτ0 := jetNormAt_nonneg (𝕜 := ℝ) r (fderiv ℝ (D.chartTransition k x y)) 0
  have hgτ := hcomp hds
  calc D.dbarJetNorm k r s y ≤ 4 ^ r * jetNormAt ℝ r (D.frameChange k x y) 0 *
        jetNormAt ℝ r (g ∘ D.chartTransition k x y) 0 *
        jetNormAt ℝ r (fderiv ℝ (D.chartTransition k x y)) 0 := by
        rw [dbarJetNorm_def]
        exact D.jetNormAt_dbarReading_le_frameChange_mul hα hk h0W (by rwa [hτ0]) (by rwa [hτ0])
    _ ≤ 4 ^ r * (C * (1 + ‖z‖) ^ r) * (C * jetNormAt ℝ r g z * (1 + ‖z‖) ^ r) * C := by
        gcongr
    _ = 4 ^ r * C ^ 3 * (1 + ‖z‖) ^ (2 * r) * jetNormAt ℝ r g z := by ring
    _ ≤ 4 ^ r * C ^ 3 * (2 ^ r * (1 + d) ^ (2 * r)) * jetNormAt ℝ r g z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) hjg
    _ = 8 ^ r * C ^ 3 * (1 + d) ^ (2 * r) * jetNormAt ℝ r g z := by
        rw [show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
        ring

/-! ### From the chart at a point of the ball back to the chart at the centre -/

/-- **Bounds at a point of the ball for a change of chart back to the centre.** Under the
hypotheses of `SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`, there is a
radius `ρ` with `0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C ≥ 0` with the
following property. Let `k ≥ k₀`, `x` a point, `z` in the ball of radius `ρ * √k`,
`y = (D.chart k x)⁻¹ z`, `τ` the transition from the chart centred at `x` to the chart centred at
`y` and `e` the change of frame between them. Then `z` lies in `D.chartTransitionDomain k y x`,
`τ z = 0`, the `r`-jet norm of `e` at `z` is at most `C * (1 + d_k(x, y)) ^ r`, that of `dτ` at
`z` is at most `C`, and that of `g ∘ τ` at `z` is at most `C` times that of `g` at `0` for every
`g` that is `C^r` at `0`. Here `d_k(x, y) = √(2π k) · d_g(x, y)` is the rescaled Riemannian
distance `rescaledDist I k x y`. -/
theorem exists_forall_jetNormAt_chartChange_chart_symm_le [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k),
        z ∈ D.chartTransitionDomain k ((D.chart k x).symm z) x ∧
        D.chartTransition k ((D.chart k x).symm z) x z = 0 ∧
        jetNormAt ℝ r (D.frameChange k ((D.chart k x).symm z) x) z ≤
          C * (1 + rescaledDist I k x ((D.chart k x).symm z)) ^ r ∧
        jetNormAt ℝ r (fderiv ℝ (D.chartTransition k ((D.chart k x).symm z) x)) z ≤ C ∧
        (∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : StdSpace ι → F},
          ContDiffAt ℝ r g 0 →
          jetNormAt ℝ r (g ∘ D.chartTransition k ((D.chart k x).symm z) x) z ≤
            C * jetNormAt ℝ r g 0) := by
  obtain ⟨ρ₁, hρ₁, hρ₁₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  refine ⟨ρ₁, hρ₁, hρ₁₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := D.exists_forall_jetNormAt_chartChange_le_of_norm_fderiv_le hJ hα r √2
  have h2C : C ≤ 2 ^ r * C := le_mul_of_one_le_left hC (one_le_pow₀ one_le_two)
  refine ⟨2 ^ r * C, by positivity, fun {k} hk x z hz ↦ ?_⟩
  have hz₀ : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k) := ball_subset_ball (by gcongr) hz
  set y := (D.chart k x).symm z
  set d := rescaledDist I k x y
  have hτz : D.chartTransition k y x z = 0 := D.chartTransition_chart_symm_apply_self hk x z
  have hzW := D.mem_chartTransitionDomain_chart_symm hk x hz₀
  obtain ⟨he, hdτ, hcomp⟩ := hB hk hzW (D.norm_fderiv_chartTransition_chart_symm_le hk
    (hcmp hk x) (D.ball_subset_target hk x hz₀) hz)
  rw [hτz, norm_zero, add_zero] at he
  rw [hτz, norm_zero, add_zero, one_pow] at hcomp
  refine ⟨hzW, hτz, ?_, hdτ.trans h2C, fun hg ↦
    (hcomp hg).trans (by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_right h2C (jetNormAt_nonneg _ _ _))⟩
  -- The change of frame, with `1 + ‖z‖ ≤ √2 * (1 + d) ≤ 2 * (1 + d)`.
  have hd : 1 + ‖z‖ ≤ 2 * (1 + d) := by
    have h := D.norm_le_sqrt_two_mul_rescaledDist_symm hg hρ₁₀ hk x
      (hcmp hk x) hz
    have h2 : √2 ≤ 2 := by
      rw [Real.sqrt_le_left (by norm_num)]
      norm_num
    have hd0 : 0 ≤ d := rescaledDist_nonneg I k x y
    nlinarith [Real.one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 2)]
  calc jetNormAt ℝ r (D.frameChange k y x) z ≤ C * (1 + ‖z‖) ^ r := he
    _ ≤ C * (2 * (1 + d)) ^ r := by gcongr
    _ = 2 ^ r * C * (1 + d) ^ r := by rw [mul_pow]; ring

/-- **Smoothness moves back to the centre.** For `k ≥ k₀`, a point `x`, `z` in the ball of radius
`ρ₀ * √k` and a section `s` of `PowerBundle P k`, if the reading of `s` in the chart centred at
`(D.chart k x)⁻¹ z` is `C^n` at `0`, then the reading of `s` in the chart centred at `x` is `C^n`
at `z`. -/
theorem contDiffAt_reading_of_chart_change {n : ℕ∞} {k : ℕ} (hk : k₀ ≤ k) (x : M)
    {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k)) {s : Π y, PowerBundle P k y}
    (hs : ContDiffAt ℝ n (D.reading k ((D.chart k x).symm z) s) 0) :
    ContDiffAt ℝ n (D.reading k x s) z := by
  have hzW := D.mem_chartTransitionDomain_chart_symm hk x hz
  have hzs := D.chartTransitionDomain_subset_source k _ x hzW
  have hs' : ContDiffAt ℝ n (D.reading k ((D.chart k x).symm z) s)
      (D.chartTransition k ((D.chart k x).symm z) x z) := by
    rwa [D.chartTransition_chart_symm_apply_self hk]
  exact ((D.contDiffAt_frameChange hk hzW).mul
    (hs'.comp z (D.contDiffAt_chartTransition hzs))).congr_of_eventuallyEq
    (D.reading_eventuallyEq_frameChange_mul hzs s)

/-- **Smoothness of `∂̄` moves back to the centre.** Let `α` be a connection form, `k ≥ k₀`, `x` a
point, `z` in the ball of radius `ρ₀ * √k` and `s` a section of `PowerBundle P k` whose reading in
the chart centred at `y = (D.chart k x)⁻¹ z` is differentiable near `0`. If the `∂̄` reading of `s`
in the chart centred at `y` is `C^n` at `0`, then the `∂̄` reading of `s` in the chart centred at
`x` is `C^n` at `z`. -/
theorem contDiffAt_dbarReading_of_chart_change (hα : IsCircleConnectionForm α) {n : ℕ∞} {k : ℕ}
    (hk : k₀ ≤ k) (x : M) {z : StdSpace ι} (hz : z ∈ ball (0 : StdSpace ι) (ρ₀ * √k))
    {s : Π y, PowerBundle P k y}
    (hs : ∀ᶠ w in 𝓝 0, DifferentiableAt ℝ (D.reading k ((D.chart k x).symm z) s) w)
    (hds : ContDiffAt ℝ n (D.dbarReading k ((D.chart k x).symm z) s) 0) :
    ContDiffAt ℝ n (D.dbarReading k x s) z := by
  set y := (D.chart k x).symm z
  set τ := D.chartTransition k y x
  have hzW := D.mem_chartTransitionDomain_chart_symm hk x hz
  have hzs := D.chartTransitionDomain_subset_source k y x hzW
  have hτz : τ z = 0 := D.chartTransition_chart_symm_apply_self hk x z
  have hτ : ContDiffAt ℝ (n + 1 : ℕ∞) τ z := D.contDiffAt_chartTransition hzs
  have hτn : ContDiffAt ℝ n τ z := hτ.of_le (by exact_mod_cast le_self_add)
  have hdτ : ContDiffAt ℝ n (fderiv ℝ τ) z := hτ.fderiv_right (by exact_mod_cast le_rfl)
  have hds' : ContDiffAt ℝ n (D.dbarReading k y s) (τ z) := by rwa [hτz]
  exact ((D.contDiffAt_frameChange hk hzW).smul
    ((hds'.comp z hτn).clm_comp hdτ)).congr_of_eventuallyEq
    (D.dbarReading_eventuallyEq_frameChange_smul_comp hα hk hzW (by rwa [hτz]))

/-- **Jet norms of a reading off the centre.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`, there is a radius `ρ` with
`0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C ≥ 0` with the following
property.
For all `k ≥ k₀`, all points `x`, all `z` in the ball of radius `ρ * √k`, and every section `s` of
`PowerBundle P k` whose reading in the chart centred at `y = (D.chart k x)⁻¹ z` is `C^r` at `0`,
the `r`-jet norm at `z` of the reading of `s` in the chart centred at `x` is at most
`C * (1 + d_k(x, y)) ^ r` times the `r`-jet norm of `s` at `y`. Here `d_k(x, y)` is the real
number `√(2π k) · d_g(x, y)`, the rescaled Riemannian distance `rescaledDist I k x y`. -/
theorem jetNormAt_reading_le_of_chart_change [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k), ∀ {s : Π y, PowerBundle P k y},
        ContDiffAt ℝ r (D.reading k ((D.chart k x).symm z) s) 0 →
        jetNormAt ℝ r (D.reading k x s) z ≤
          C * (1 + rescaledDist I k x ((D.chart k x).symm z)) ^ r *
            D.jetNorm k r s ((D.chart k x).symm z) := by
  obtain ⟨ρ, hρ, hρρ₀, hB⟩ := D.exists_forall_jetNormAt_chartChange_chart_symm_le hg hJ hα hρ₀
  refine ⟨ρ, hρ, hρρ₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := hB r
  refine ⟨2 ^ r * C ^ 2, by positivity, fun {k} hk x z hz {s} hs ↦ ?_⟩
  obtain ⟨hzW, hτz, he, -, hcomp⟩ := hB hk x z hz
  set y := (D.chart k x).symm z
  set f := D.reading k y s
  set d := rescaledDist I k x y
  have hd0 : 0 ≤ d := rescaledDist_nonneg I k x y
  calc jetNormAt ℝ r (D.reading k x s) z ≤ 2 ^ r * jetNormAt ℝ r (D.frameChange k y x) z *
        jetNormAt ℝ r (f ∘ D.chartTransition k y x) z :=
        D.jetNormAt_reading_le_frameChange_mul hk hzW (by rwa [hτz])
    _ ≤ 2 ^ r * (C * (1 + d) ^ r) * (C * jetNormAt ℝ r f 0) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) (hcomp hs)
          (jetNormAt_nonneg _ _ _) (by positivity)
    _ = 2 ^ r * C ^ 2 * (1 + d) ^ r * D.jetNorm k r s y := by rw [jetNorm_def]; ring

/-- **Jet norms of a `∂̄` reading off the centre.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`, there is a radius `ρ` with
`0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C ≥ 0` with the following
property.
For all `k ≥ k₀`, all points `x`, all `z` in the ball of radius `ρ * √k`, and every section `s` of
`PowerBundle P k` whose reading in the chart centred at `y = (D.chart k x)⁻¹ z` is differentiable
near `0` and whose `∂̄` reading in that chart is `C^r` at `0`, the `r`-jet norm at `z` of the `∂̄`
reading of `s` in the chart centred at `x` is at most `C * (1 + d_k(x, y)) ^ r` times the `r`-jet
norm of `∂̄ s` at `y`. Here `d_k(x, y)` is the real number `√(2π k) · d_g(x, y)`, the rescaled
Riemannian distance `rescaledDist I k x y`. -/
theorem jetNormAt_dbarReading_le_of_chart_change [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k), ∀ {s : Π y, PowerBundle P k y},
        (∀ᶠ w in 𝓝 0, DifferentiableAt ℝ (D.reading k ((D.chart k x).symm z) s) w) →
        ContDiffAt ℝ r (D.dbarReading k ((D.chart k x).symm z) s) 0 →
        jetNormAt ℝ r (D.dbarReading k x s) z ≤
          C * (1 + rescaledDist I k x ((D.chart k x).symm z)) ^ r *
            D.dbarJetNorm k r s ((D.chart k x).symm z) := by
  obtain ⟨ρ, hρ, hρρ₀, hB⟩ := D.exists_forall_jetNormAt_chartChange_chart_symm_le hg hJ hα hρ₀
  refine ⟨ρ, hρ, hρρ₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := hB r
  refine ⟨4 ^ r * C ^ 3, by positivity, fun {k} hk x z hz {s} hs hds ↦ ?_⟩
  obtain ⟨hzW, hτz, he, hjdτ, hcomp⟩ := hB hk x z hz
  set y := (D.chart k x).symm z
  set g := D.dbarReading k y s
  set d := rescaledDist I k x y
  have hd0 : 0 ≤ d := rescaledDist_nonneg I k x y
  have hjg := jetNormAt_nonneg (𝕜 := ℝ) r g 0
  have hjgτ := jetNormAt_nonneg (𝕜 := ℝ) r (g ∘ D.chartTransition k y x) z
  have hjdτ0 := jetNormAt_nonneg (𝕜 := ℝ) r (fderiv ℝ (D.chartTransition k y x)) z
  have hgτ := hcomp hds
  calc jetNormAt ℝ r (D.dbarReading k x s) z ≤ 4 ^ r * jetNormAt ℝ r (D.frameChange k y x) z *
        jetNormAt ℝ r (g ∘ D.chartTransition k y x) z *
        jetNormAt ℝ r (fderiv ℝ (D.chartTransition k y x)) z :=
        D.jetNormAt_dbarReading_le_frameChange_mul hα hk hzW (by rwa [hτz]) (by rwa [hτz])
    _ ≤ 4 ^ r * (C * (1 + d) ^ r) * (C * jetNormAt ℝ r g 0) * C := by gcongr
    _ = 4 ^ r * C ^ 3 * (1 + d) ^ r * D.dbarJetNorm k r s y := by rw [dbarJetNorm_def]; ring

/-- **Chart changes on a ball of fixed radius.** Let `M` be a Hausdorff boundaryless manifold, let
`σ` be compatible with `J`, let `M` carry the metric `g_J` of the pair, let `α` be a connection
form and `ρ₀ > 0`. For every radius `R` and every order `r` there is a constant `C ≥ 0` such that,
for all large `k`, all points `x`, all `z` in the ball of radius `R` and every section `s` of
`PowerBundle P k`, with `y = (D.chart k x)⁻¹ z`:
* if the reading of `s` in the chart centred at `y` is `C^n` at `0`, then the reading in the chart
  centred at `x` is `C^n` at `z`, and likewise for the `∂̄` readings when the reading in the chart
  at `y` is differentiable near `0`;
* if the reading of `s` in the chart at `y` is `C^r` at `0`, then the `r`-jet norm at `z` of the
  reading in the chart at `x` is at most `C` times the `r`-jet norm of `s` at `y`;
* if moreover the reading in the chart at `y` is differentiable near `0` and its `∂̄` reading is
  `C^r` at `0`, then the same holds for the `∂̄` readings and the `r`-jet norm of `∂̄ s` at `y`. -/
theorem exists_forall_jetNormAt_le_jetNorm_of_mem_ball [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) (R : ℝ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in Filter.atTop, ∀ (x : M), ∀ z ∈ ball (0 : StdSpace ι) R,
      ∀ (s : Π y, PowerBundle P k y),
      (∀ {n : ℕ∞}, ContDiffAt ℝ n (D.reading k ((D.chart k x).symm z) s) 0 →
        ContDiffAt ℝ n (D.reading k x s) z) ∧
      (∀ {n : ℕ∞}, (∀ᶠ w in 𝓝 0, DifferentiableAt ℝ (D.reading k ((D.chart k x).symm z) s) w) →
        ContDiffAt ℝ n (D.dbarReading k ((D.chart k x).symm z) s) 0 →
        ContDiffAt ℝ n (D.dbarReading k x s) z) ∧
      (ContDiffAt ℝ r (D.reading k ((D.chart k x).symm z) s) 0 →
        jetNormAt ℝ r (D.reading k x s) z ≤ C * D.jetNorm k r s ((D.chart k x).symm z)) ∧
      ((∀ᶠ w in 𝓝 0, DifferentiableAt ℝ (D.reading k ((D.chart k x).symm z) s) w) →
        ContDiffAt ℝ r (D.dbarReading k ((D.chart k x).symm z) s) 0 →
        jetNormAt ℝ r (D.dbarReading k x s) z ≤
          C * D.dbarJetNorm k r s ((D.chart k x).symm z)) := by
  obtain ⟨ρ₁, hρ₁, -, hJ₁⟩ := D.jetNormAt_reading_le_of_chart_change hg hJ hα hρ₀
  obtain ⟨ρ₂, hρ₂, -, hJ₂⟩ := D.jetNormAt_dbarReading_le_of_chart_change hg hJ hα hρ₀
  obtain ⟨ρ₃, hρ₃, hρ₃₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  obtain ⟨C₁, hC₁0, hC₁⟩ := hJ₁ r
  obtain ⟨C₂, hC₂0, hC₂⟩ := hJ₂ r
  set ρ := min ρ₁ (min ρ₂ ρ₃)
  have hρ : 0 < ρ := lt_min hρ₁ (lt_min hρ₂ hρ₃)
  -- On the ball of radius `R`, `d_k(x, y) ≤ √(3/2) * |R|`.
  set Q : ℝ := (1 + √(3 / 2) * |R|) ^ r
  refine ⟨(C₁ + C₂) * Q, by have := add_nonneg hC₁0 hC₂0; positivity, ?_⟩
  have hρk : ∀ᶠ k : ℕ in Filter.atTop, |R| < ρ * √k :=
    ((Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
      hρ).eventually_gt_atTop |R|
  filter_upwards [hρk, Filter.eventually_ge_atTop k₀] with k hρk hk x z hz s
  have hzR : ‖z‖ ≤ |R| := (mem_ball_zero_iff.1 hz).le.trans (le_abs_self R)
  have hball {ρ' : ℝ} (h : ρ ≤ ρ') : z ∈ ball (0 : StdSpace ι) (ρ' * √k) :=
    mem_ball_zero_iff.2 (hzR.trans_lt (hρk.trans_le
      (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))))
  have hz₁ := hball (min_le_left _ _)
  have hz₂ := hball ((min_le_right _ _).trans (min_le_left _ _))
  have hz₃ := hball ((min_le_right _ _).trans (min_le_right _ _))
  have hz₀ := hball ((min_le_right _ _).trans ((min_le_right _ _).trans hρ₃₀))
  set y := (D.chart k x).symm z
  set d := rescaledDist I k x y
  have hd0 : 0 ≤ d := rescaledDist_nonneg I k x y
  have hdQ : (1 + d) ^ r ≤ Q := by
    have h := D.rescaledDist_symm_le hg hρ₃₀ hk x (hcmp hk x) hz₃
    refine pow_le_pow_left₀ (by positivity) ?_ r
    have : √(3 / 2) * ‖z‖ ≤ √(3 / 2) * |R| := by gcongr
    linarith
  refine ⟨fun hry ↦ D.contDiffAt_reading_of_chart_change hk x hz₀ hry,
    fun hdiff hdry ↦ D.contDiffAt_dbarReading_of_chart_change hα hk x hz₀ hdiff hdry,
    fun hry ↦ ?_, fun hdiff hdry ↦ ?_⟩
  · have hJ0 := D.jetNorm_nonneg k r s y
    calc jetNormAt ℝ r (D.reading k x s) z ≤ C₁ * (1 + d) ^ r * D.jetNorm k r s y :=
          hC₁ hk x z hz₁ hry
      _ ≤ (C₁ + C₂) * Q * D.jetNorm k r s y := by
          gcongr; exact le_add_of_nonneg_right hC₂0
  · have hDJ0 := D.dbarJetNorm_nonneg k r s y
    calc jetNormAt ℝ r (D.dbarReading k x s) z ≤ C₂ * (1 + d) ^ r * D.dbarJetNorm k r s y :=
          hC₂ hk x z hz₂ hdiff hdry
      _ ≤ (C₁ + C₂) * Q * D.dbarJetNorm k r s y := by
          gcongr; exact le_add_of_nonneg_left hC₁0

/-- **Asymptotically holomorphic sequences, read on balls of fixed radius.** Let `M` be a
Hausdorff boundaryless manifold, let `σ` be compatible with `J`, let `M` carry the metric `g_J`
of the pair, let `α` be a connection form and `ρ₀ > 0`, and let `s` be an asymptotically
holomorphic sequence of sections. For every radius `R` and every order `r` there is a constant
`C ≥ 0` such that, for all large `k`, all points `x` and all `z` in the ball of radius `R`, the
readings of `s k` and their `∂̄` readings in the chart centred at `x` are smooth at `z`, the
`r`-jet norm at `z` of the reading is at most `C`, and that of the `∂̄` reading is at most
`C * k ^ (-1/2)`. -/
theorem IsAsymptoticallyHolomorphic.exists_forall_jetNormAt_le [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀)
    {s : ∀ k : ℕ, Π y, PowerBundle P k y} (hs : D.IsAsymptoticallyHolomorphic s) (R : ℝ)
    (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k : ℕ in Filter.atTop, ∀ (x : M), ∀ z ∈ ball (0 : StdSpace ι) R,
      ContDiffAt ℝ ∞ (D.reading k x (s k)) z ∧ ContDiffAt ℝ ∞ (D.dbarReading k x (s k)) z ∧
      jetNormAt ℝ r (D.reading k x (s k)) z ≤ C ∧
      jetNormAt ℝ r (D.dbarReading k x (s k)) z ≤ C * (k : ℝ) ^ (-1 / 2 : ℝ) := by
  rw [isAsymptoticallyHolomorphic_def] at hs
  obtain ⟨C, hC0, hC⟩ := D.exists_forall_jetNormAt_le_jetNorm_of_mem_ball hg hJ hα hρ₀ R r
  obtain ⟨Cs, hCs⟩ := hs.2 r
  refine ⟨C * |Cs|, by positivity, ?_⟩
  filter_upwards [hs.1, hCs, hC] with k hsk hCsk hCk x z hz
  set y := (D.chart k x).symm z
  obtain ⟨hry, hdry⟩ := hsk y
  have hdiff : ∀ᶠ w in 𝓝 0, DifferentiableAt ℝ (D.reading k y (s k)) w :=
    hry.eventually_differentiableAt (by exact_mod_cast le_top)
  obtain ⟨hJy, hDJy⟩ := hCsk y
  obtain ⟨hc, hdc, hb, hdb⟩ := hCk x z hz (s k)
  refine ⟨hc hry, hdc hdiff hdry, ?_, ?_⟩
  · calc jetNormAt ℝ r (D.reading k x (s k)) z ≤ C * D.jetNorm k r (s k) y :=
          hb (hry.of_le (by exact_mod_cast le_top))
      _ ≤ C * |Cs| := by gcongr; exact hJy.trans (le_abs_self _)
  · calc jetNormAt ℝ r (D.dbarReading k x (s k)) z ≤ C * D.dbarJetNorm k r (s k) y :=
          hdb hdiff (hdry.of_le (by exact_mod_cast le_top))
      _ ≤ C * (|Cs| * (k : ℝ) ^ (-1 / 2 : ℝ)) := by
          gcongr; exact hDJy.trans (by gcongr; exact le_abs_self _)
      _ = C * |Cs| * (k : ℝ) ^ (-1 / 2 : ℝ) := by ring

end RescaledUnitaryCharts

end SymplecticGeometry

end
