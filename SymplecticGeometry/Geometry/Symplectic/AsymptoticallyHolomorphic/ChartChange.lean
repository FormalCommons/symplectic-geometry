/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.AsymptoticallyHolomorphic.FrameChange

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
`SymplecticGeometry.jetNormAt_comp_le` reduce the jet norm of this product to those of `e` and
`τ` at `0`. Both are at most polynomials in `‖z‖ = ‖τ 0‖`, by
`RescaledUnitaryCharts.exists_forall_jetNormAt_frameChange_zero_le` and
`RescaledUnitaryCharts.exists_forall_norm_iteratedFDeriv_chartTransition_zero_le` with
`SymplecticGeometry.jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le`, and
`‖z‖ ≤ √2 * d_k(x, y)`
(`RescaledUnitaryCharts.norm_le_sqrt_two_mul_toReal_ofReal_mul_riemannianEDist_symm`) turns the
bound into a polynomial in `d_k(x, y)`.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`: for every `r`,
  `D.jetNorm k r s y ≤ C * (1 + d_k(x, y)) ^ (2 * r) * jetNormAt ℝ r (D.reading k x s) z`.

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

/-- **Jet norms under a change of chart.** Let `M` be a Hausdorff boundaryless manifold, let `σ`
be compatible with `J`, and let `M` carry a Riemannian metric whose inner product is
`⟪u, w⟫ = σ(u, J w)`, the metric `g_J` of the pair. Let `α` be a connection form and `ρ₀ > 0`.
There is a radius `ρ` with `0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C`
with the following property. For all `k ≥ k₀`, all points `x`, all `z` in the ball of radius
`ρ * √k`, and every section `s` of `PowerBundle P k` whose reading in the chart centred at `x` is
`C^r` at `z`, the `r`-jet norm of `s` at `y = (D.chart k x)⁻¹ z` is at most
`C * (1 + d_k(x, y)) ^ (2 * r)` times the `r`-jet norm at `z` of the reading of `s` in the chart
centred at `x`. Here `d_k(x, y)` is the real number `√(2π k) · d_g(x, y)`, the rescaled
Riemannian distance. -/
theorem jetNorm_le_of_chart_change [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k), ∀ {s : Π y, PowerBundle P k y},
        ContDiffAt ℝ r (D.reading k x s) z →
        D.jetNorm k r s ((D.chart k x).symm z) ≤
          C * (1 + (ENNReal.ofReal √(2 * Real.pi * k) *
            Manifold.riemannianEDist I x ((D.chart k x).symm z)).toReal) ^ (2 * r) *
            jetNormAt ℝ r (D.reading k x s) z := by
  obtain ⟨ρ₁, hρ₁, -, hT⟩ := D.exists_forall_norm_iteratedFDeriv_chartTransition_zero_le hJ hρ₀
  obtain ⟨ρ₂, hρ₂, -, hE⟩ := D.exists_forall_jetNormAt_frameChange_zero_le hJ hα hρ₀
  obtain ⟨ρ₃, hρ₃, hρ₃₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃),
    (min_le_right _ _).trans ((min_le_right _ _).trans hρ₃₀), fun r ↦ ?_⟩
  obtain ⟨Cτ, hCτ⟩ := hT r
  obtain ⟨Ce, hCe⟩ := hE r
  set A : ℝ := 1 + r * |Cτ|
  have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  refine ⟨4 ^ r * |Ce| * (r + 1)! * A ^ r, fun {k} hk x z hz {s} hs ↦ ?_⟩
  have hball {ρ' : ℝ} (h : min ρ₁ (min ρ₂ ρ₃) ≤ ρ') : z ∈ ball (0 : StdSpace ι) (ρ' * √k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)) hz
  have hz₁ := hball (min_le_left _ _)
  have hz₂ := hball ((min_le_right _ _).trans (min_le_left _ _))
  have hz₃ := hball ((min_le_right _ _).trans (min_le_right _ _))
  have hz₀ := hball ((min_le_right _ _).trans ((min_le_right _ _).trans hρ₃₀))
  set y := (D.chart k x).symm z
  set τ := D.chartTransition k x y
  set e := D.frameChange k x y
  set f := D.reading k x s
  set d := (ENNReal.ofReal √(2 * Real.pi * k) * Manifold.riemannianEDist I x y).toReal
  have hτ0 : τ 0 = z := D.chartTransition_symm_zero hk (D.ball_subset_target hk x hz₀)
  have h0W := D.zero_mem_chartTransitionDomain hk x hz₀
  have hW := (D.isOpen_chartTransitionDomain k x y).mem_nhds h0W
  -- The transition and the change of frame are `C^r` at `0`, and so is `f ∘ τ`.
  have h0s := D.chartTransitionDomain_subset_source k x y h0W
  have hτr : ContDiffAt ℝ r τ 0 := (D.contDiffAt_chartTransition h0s).of_le (by simp)
  have her : ContDiffAt ℝ r e 0 := ((D.contDiffOn_frameChange hk x y).contDiffAt hW).of_le (by simp)
  have hs' : ContDiffAt ℝ r f (τ 0) := by rwa [hτ0]
  -- Near `0`, the reading at `y` is `e • (f ∘ τ)`.
  have heq : D.reading k y s =ᶠ[𝓝 0] fun w ↦ e w • (f ∘ τ) w := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      D.reading_eventuallyEq_frameChange_mul h0s s
  -- The bounds on the jets of `e` and of `τ` at `0`.
  have he : jetNormAt ℝ r e 0 ≤ |Ce| * (1 + ‖z‖) ^ r :=
    (hCe hk x z hz₂).trans (by gcongr; exact le_abs_self _)
  have hjτ : max 1 (jetNormAt ℝ r τ 0) ≤ A * (1 + ‖z‖) := by
    have h := jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le (r := r) (f := τ)
      (z := 0) fun j hj ↦ hCτ hk x z hz₁ (j + 1) (by omega) (by omega)
    rw [hτ0] at h
    exact max_le (by nlinarith [norm_nonneg z]) h
  -- The rescaled distance bounds `‖z‖`: `1 + ‖z‖ ≤ √2 * (1 + d)`.
  have hd : 1 + ‖z‖ ≤ √2 * (1 + d) := by
    have h := D.norm_le_sqrt_two_mul_toReal_ofReal_mul_riemannianEDist_symm hg hρ₃₀ hk x
      (hcmp hk x) hz₃
    nlinarith [Real.one_le_sqrt.2 (by norm_num : (1 : ℝ) ≤ 2)]
  have hjf := jetNormAt_nonneg (𝕜 := ℝ) r f z
  have hz0 : 0 ≤ 1 + ‖z‖ := by positivity
  have hfτ : jetNormAt ℝ r (f ∘ τ) 0 ≤ (r + 1)! * jetNormAt ℝ r f z * (A * (1 + ‖z‖)) ^ r := by
    refine (jetNormAt_comp_le hs' hτr).trans ?_
    rw [hτ0]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjτ r) (by positivity)
  calc D.jetNorm k r s y = jetNormAt ℝ r (fun w ↦ e w • (f ∘ τ) w) 0 := by
        rw [jetNorm_def, jetNormAt_congr_of_eventuallyEq r heq]
    _ ≤ 2 ^ r * jetNormAt ℝ r e 0 * jetNormAt ℝ r (f ∘ τ) 0 :=
        jetNormAt_fun_smul_le her (hs'.comp 0 hτr)
    _ ≤ 2 ^ r * (|Ce| * (1 + ‖z‖) ^ r) *
          ((r + 1)! * jetNormAt ℝ r f z * (A * (1 + ‖z‖)) ^ r) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hfτ
          (jetNormAt_nonneg _ _ _) (by positivity)
    _ = 2 ^ r * |Ce| * (r + 1)! * A ^ r * ((1 + ‖z‖) ^ 2) ^ r * jetNormAt ℝ r f z := by
        rw [mul_pow, ← pow_mul, two_mul, pow_add]
        ring
    _ ≤ 2 ^ r * |Ce| * (r + 1)! * A ^ r * (2 * (1 + d) ^ 2) ^ r * jetNormAt ℝ r f z := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) ?_ r) (by positivity)) hjf
        calc (1 + ‖z‖) ^ 2 ≤ (√2 * (1 + d)) ^ 2 := pow_le_pow_left₀ hz0 hd 2
          _ = 2 * (1 + d) ^ 2 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]
    _ = 4 ^ r * |Ce| * (r + 1)! * A ^ r * (1 + d) ^ (2 * r) * jetNormAt ℝ r f z := by
        rw [mul_pow, pow_mul, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        ring

end RescaledUnitaryCharts

end SymplecticGeometry

end
