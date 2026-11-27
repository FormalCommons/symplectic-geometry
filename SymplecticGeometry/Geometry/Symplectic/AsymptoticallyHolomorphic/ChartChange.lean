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
bound into a polynomial in `d_k(x, y)`. The bounds at `0` that both results below use, on the
jets of `e`, of `dτ` and of a map composed with `τ`, are gathered in
`SymplecticGeometry.RescaledUnitaryCharts.exists_forall_jetNormAt_chartChange_le`.

The same holds for the `∂̄` reading `D.dbarReading k y s` of `s`, whose jet norm at `0` is
`D.dbarJetNorm k r s y`. Near `0` it is `e • ((g ∘ τ) ∘L dτ)`, for `g` the `∂̄` reading in the
chart at `x` (`SymplecticGeometry.RescaledUnitaryCharts.dbarReading_eq_frameChange_smul_comp`).
The jets of `dτ` at `0` are bounded by those of `τ` of orders `1` to `r + 1`, with no factor
`‖z‖` (`SymplecticGeometry.jetNormAt_fderiv_le_of_norm_iteratedFDeriv_succ_le`), and the
bilinear bound `SymplecticGeometry.jetNormAt_bilinear_le` takes care of the composition with
`dτ`. The exponent is again `2 * r`.

## Main results

* `SymplecticGeometry.RescaledUnitaryCharts.exists_forall_jetNormAt_chartChange_le`: the bounds
  at `0` on the jets of the change of frame, of the derivative of the transition and of a map
  composed with the transition, and `(1 + ‖z‖) ^ (2 * r) ≤ 2 ^ r * (1 + d_k(x, y)) ^ (2 * r)`.
* `SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`: for every `r`,
  `D.jetNorm k r s y ≤ C * (1 + d_k(x, y)) ^ (2 * r) * jetNormAt ℝ r (D.reading k x s) z`.
* `SymplecticGeometry.RescaledUnitaryCharts.dbarJetNorm_le_of_chart_change`: for every `r`,
  `D.dbarJetNorm k r s y ≤ C * (1 + d_k(x, y)) ^ (2 * r) * jetNormAt ℝ r (D.dbarReading k x s) z`.

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

/-- **Bounds at the centre for a change of chart.** Under the hypotheses of
`SymplecticGeometry.RescaledUnitaryCharts.jetNorm_le_of_chart_change`, there is a radius `ρ` with
`0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C ≥ 0` with the following
property. Let `k ≥ k₀`, `x` a point, `z` in the ball of radius `ρ * √k`, `y = (D.chart k x)⁻¹ z`,
`τ` the transition from the chart centred at `y` to the chart centred at `x` and `e` the change
of frame between them. Then `0` lies in `D.chartTransitionDomain k x y`, `τ 0 = z`, `e` is `C^r`
at `0`, the `r`-jet norm of `e` at `0` is at most `C * (1 + ‖z‖) ^ r`, that of `dτ` at `0` is at
most `C`, that of `g ∘ τ` at `0` is at most `C * (1 + ‖z‖) ^ r` times that of `g` at `z` for every
`g` that is `C^r` at `z`, and `(1 + ‖z‖) ^ (2 * r) ≤ 2 ^ r * (1 + d_k(x, y)) ^ (2 * r)`, for
`d_k(x, y) = √(2π k) · d_g(x, y)` the rescaled Riemannian distance. -/
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
        (1 + ‖z‖) ^ (2 * r) ≤ 2 ^ r * (1 + (ENNReal.ofReal √(2 * Real.pi * k) *
          Manifold.riemannianEDist I x ((D.chart k x).symm z)).toReal) ^ (2 * r) := by
  obtain ⟨ρ₁, hρ₁, -, hT⟩ := D.exists_forall_norm_iteratedFDeriv_chartTransition_zero_le hJ hρ₀
  obtain ⟨ρ₂, hρ₂, -, hE⟩ := D.exists_forall_jetNormAt_frameChange_zero_le hJ hα hρ₀
  obtain ⟨ρ₃, hρ₃, hρ₃₀, hcmp⟩ := D.exists_forall_isComparisonRadius hρ₀
  refine ⟨min ρ₁ (min ρ₂ ρ₃), lt_min hρ₁ (lt_min hρ₂ hρ₃),
    (min_le_right _ _).trans ((min_le_right _ _).trans hρ₃₀), fun r ↦ ?_⟩
  -- One bound `Cτ` for the derivatives of orders `1` to `r + 1` of the transition serves both
  -- the jets of `τ` and those of `dτ`.
  obtain ⟨Cτ, hCτ⟩ := hT (r + 1)
  obtain ⟨Ce, hCe⟩ := hE r
  set A : ℝ := 1 + r * |Cτ|
  have hA : 1 ≤ A := le_add_of_nonneg_right (by positivity)
  set C : ℝ := |Ce| + (r + 1)! * A ^ r + (r + 1) * |Cτ|
  have hCe' : 0 ≤ |Ce| := abs_nonneg _
  have hCA : 0 ≤ ((r + 1)! : ℝ) * A ^ r := by positivity
  have hCτ' : 0 ≤ ((r : ℝ) + 1) * |Cτ| := by positivity
  refine ⟨C, by positivity, fun {k} hk x z hz ↦ ?_⟩
  have hball {ρ' : ℝ} (h : min ρ₁ (min ρ₂ ρ₃) ≤ ρ') : z ∈ ball (0 : StdSpace ι) (ρ' * √k) :=
    ball_subset_ball (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _)) hz
  have hz₁ := hball (min_le_left _ _)
  have hz₂ := hball ((min_le_right _ _).trans (min_le_left _ _))
  have hz₃ := hball ((min_le_right _ _).trans (min_le_right _ _))
  have hz₀ := hball ((min_le_right _ _).trans ((min_le_right _ _).trans hρ₃₀))
  set y := (D.chart k x).symm z
  set τ := D.chartTransition k x y
  set e := D.frameChange k x y
  set d := (ENNReal.ofReal √(2 * Real.pi * k) * Manifold.riemannianEDist I x y).toReal
  have hτ0 : τ 0 = z := D.chartTransition_symm_zero hk (D.ball_subset_target hk x hz₀)
  have h0W := D.zero_mem_chartTransitionDomain hk x hz₀
  have hτr : ContDiffAt ℝ r τ 0 :=
    D.contDiffAt_chartTransition (D.chartTransitionDomain_subset_source k x y h0W)
  have hz0 : 0 ≤ 1 + ‖z‖ := by positivity
  refine ⟨h0W, hτ0, D.contDiffAt_frameChange hk h0W, ?_, ?_,
    fun {F} _ _ {g} hgz ↦ ?_, ?_⟩
  · -- The change of frame.
    refine (hCe hk x z hz₂).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    exact (le_abs_self _).trans (by linarith)
  · -- The derivative of the transition.
    refine (jetNormAt_fderiv_le_of_norm_iteratedFDeriv_succ_le fun j hj ↦
      hCτ hk x z hz₁ (j + 1) (by omega) (by omega)).trans (by linarith)
  · -- Faà di Bruno for `g ∘ τ`, with `max 1 (jetNormAt ℝ r τ 0) ≤ A * (1 + ‖z‖)`.
    have hjτ : max 1 (jetNormAt ℝ r τ 0) ≤ A * (1 + ‖z‖) := by
      have h := jetNormAt_le_mul_one_add_norm_of_norm_iteratedFDeriv_succ_le (r := r) (f := τ)
        (z := 0) fun j hj ↦ hCτ hk x z hz₁ (j + 1) (by omega) (by omega)
      rw [hτ0] at h
      exact max_le (by nlinarith [norm_nonneg z]) h
    have hg' : ContDiffAt ℝ r g (τ 0) := by rwa [hτ0]
    have hjg := jetNormAt_nonneg (𝕜 := ℝ) r g z
    refine (jetNormAt_comp_le hg' hτr).trans ?_
    rw [hτ0]
    calc _ ≤ (r + 1)! * jetNormAt ℝ r g z * (A * (1 + ‖z‖)) ^ r :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hjτ r) (by positivity)
      _ = (r + 1)! * A ^ r * jetNormAt ℝ r g z * (1 + ‖z‖) ^ r := by rw [mul_pow]; ring
      _ ≤ C * jetNormAt ℝ r g z * (1 + ‖z‖) ^ r :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hjg)
            (by positivity)
  · -- The rescaled distance bounds `‖z‖`: `1 + ‖z‖ ≤ √2 * (1 + d)`.
    have hd : 1 + ‖z‖ ≤ √2 * (1 + d) := by
      have h := D.norm_le_sqrt_two_mul_toReal_ofReal_mul_riemannianEDist_symm hg hρ₃₀ hk x
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
  obtain ⟨ρ, hρ, hρρ₀, hB⟩ := D.exists_forall_jetNormAt_chartChange_le hg hJ hα hρ₀
  refine ⟨ρ, hρ, hρρ₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := hB r
  refine ⟨4 ^ r * C ^ 2, fun {k} hk x z hz {s} hs ↦ ?_⟩
  obtain ⟨h0W, hτ0, her, he, -, hcomp, hd⟩ := hB hk x z hz
  set y := (D.chart k x).symm z
  set τ := D.chartTransition k x y
  set e := D.frameChange k x y
  set f := D.reading k x s
  set d := (ENNReal.ofReal √(2 * Real.pi * k) * Manifold.riemannianEDist I x y).toReal
  have h0s := D.chartTransitionDomain_subset_source k x y h0W
  have hτr : ContDiffAt ℝ r τ 0 := D.contDiffAt_chartTransition h0s
  have hs' : ContDiffAt ℝ r f (τ 0) := by rwa [hτ0]
  -- Near `0`, the reading at `y` is `e • (f ∘ τ)`.
  have heq : D.reading k y s =ᶠ[𝓝 0] fun w ↦ e w • (f ∘ τ) w := by
    simpa only [smul_eq_mul, Function.comp_apply] using
      D.reading_eventuallyEq_frameChange_mul h0s s
  have hjf := jetNormAt_nonneg (𝕜 := ℝ) r f z
  calc D.jetNorm k r s y = jetNormAt ℝ r (fun w ↦ e w • (f ∘ τ) w) 0 := by
        rw [jetNorm_def, jetNormAt_congr_of_eventuallyEq r heq]
    _ ≤ 2 ^ r * jetNormAt ℝ r e 0 * jetNormAt ℝ r (f ∘ τ) 0 :=
        jetNormAt_fun_smul_le her (hs'.comp 0 hτr)
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
`0 < ρ ≤ ρ₀` such that for every order `r` there is a constant `C` with the following property.
For all `k ≥ k₀`, all points `x`, all `z` in the ball of radius `ρ * √k`, and every section `s` of
`PowerBundle P k` whose reading in the chart centred at `x` is differentiable near `z` and whose
`∂̄` reading in that chart is `C^r` at `z`, the `r`-jet norm of the `∂̄` reading of `s` at
`y = (D.chart k x)⁻¹ z` is at most `C * (1 + d_k(x, y)) ^ (2 * r)` times the `r`-jet norm at `z`
of the `∂̄` reading of `s` in the chart centred at `x`. Here `d_k(x, y)` is the real number
`√(2π k) · d_g(x, y)`, the rescaled Riemannian distance. -/
theorem dbarJetNorm_le_of_chart_change [T2Space M] [I.Boundaryless]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (hg : ∀ (x : M) (u w : TangentSpace I x), inner ℝ u w = σ.eval₂ x u (J x w))
    (hJ : σ.Compatible J) (hα : IsCircleConnectionForm α) (hρ₀ : 0 < ρ₀) :
    ∃ ρ, 0 < ρ ∧ ρ ≤ ρ₀ ∧ ∀ r : ℕ, ∃ C : ℝ, ∀ {k : ℕ}, k₀ ≤ k → ∀ (x : M),
      ∀ z ∈ ball (0 : StdSpace ι) (ρ * √k), ∀ {s : Π y, PowerBundle P k y},
        (∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (D.reading k x s) w) →
        ContDiffAt ℝ r (D.dbarReading k x s) z →
        D.dbarJetNorm k r s ((D.chart k x).symm z) ≤
          C * (1 + (ENNReal.ofReal √(2 * Real.pi * k) *
            Manifold.riemannianEDist I x ((D.chart k x).symm z)).toReal) ^ (2 * r) *
            jetNormAt ℝ r (D.dbarReading k x s) z := by
  obtain ⟨ρ, hρ, hρρ₀, hB⟩ := D.exists_forall_jetNormAt_chartChange_le hg hJ hα hρ₀
  refine ⟨ρ, hρ, hρρ₀, fun r ↦ ?_⟩
  obtain ⟨C, hC, hB⟩ := hB r
  refine ⟨8 ^ r * C ^ 3, fun {k} hk x z hz {s} hs hds ↦ ?_⟩
  obtain ⟨h0W, hτ0, her, he, hjdτ, hcomp, hd⟩ := hB hk x z hz
  set y := (D.chart k x).symm z
  set τ := D.chartTransition k x y
  set e := D.frameChange k x y
  set g := D.dbarReading k x s
  set d := (ENNReal.ofReal √(2 * Real.pi * k) * Manifold.riemannianEDist I x y).toReal
  have hW := (D.isOpen_chartTransitionDomain k x y).mem_nhds h0W
  -- The transition is smooth at `0`, and `g ∘ τ` and `dτ` are `C^r` there.
  have hτ : ContDiffAt ℝ (r + 1) τ 0 :=
    D.contDiffAt_chartTransition (D.chartTransitionDomain_subset_source k x y h0W)
  have hτr : ContDiffAt ℝ r τ 0 := hτ.of_le (by simp)
  have hdτ : ContDiffAt ℝ r (fderiv ℝ τ) 0 := hτ.fderiv_right le_rfl
  have hg' : ContDiffAt ℝ r g (τ 0) := by rwa [hτ0]
  -- Near `0`, the `∂̄` reading at `y` is `e • ((g ∘ τ) ∘L dτ)`.
  have hsτ : ∀ᶠ w in 𝓝 0, DifferentiableAt ℝ (D.reading k x s) (τ w) :=
    hτr.continuousAt.tendsto.eventually (hτ0 ▸ hs)
  have heq : D.dbarReading k y s =ᶠ[𝓝 0] fun w ↦
      e w • ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ ((g ∘ τ) w) (fderiv ℝ τ w) :=
    ((Filter.eventually_mem_set.2 hW).and hsτ).mono fun w ⟨hw, hsw⟩ ↦ by
      simpa only [ContinuousLinearMap.compL_apply, Function.comp_apply] using
        D.dbarReading_eq_frameChange_smul_comp hα hk hw hsw
  have hjg := jetNormAt_nonneg (𝕜 := ℝ) r g z
  have hgτ := hcomp hds
  -- The jet of `(g ∘ τ) ∘L dτ`, a bilinear combination of `g ∘ τ` and `dτ`.
  have hgτd : jetNormAt ℝ r (fun w ↦ ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ
      ((g ∘ τ) w) (fderiv ℝ τ w)) 0 ≤
        2 ^ r * (C * jetNormAt ℝ r g z * (1 + ‖z‖) ^ r) * C := by
    refine (jetNormAt_bilinear_le _ (hg'.comp 0 hτr) hdτ).trans ?_
    have := jetNormAt_nonneg (𝕜 := ℝ) r (g ∘ τ) 0
    have := jetNormAt_nonneg (𝕜 := ℝ) r (fderiv ℝ τ) 0
    have hB := ContinuousLinearMap.norm_compL_le ℝ (StdSpace ι) (StdSpace ι) ℂ
    calc _ ≤ 2 ^ r * 1 * jetNormAt ℝ r (g ∘ τ) 0 * jetNormAt ℝ r (fderiv ℝ τ) 0 := by gcongr
      _ ≤ 2 ^ r * (C * jetNormAt ℝ r g z * (1 + ‖z‖) ^ r) * C := by
          rw [mul_one]
          gcongr
  have hcomp' : ContDiffAt ℝ r (fun w ↦ ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ
      ((g ∘ τ) w) (fderiv ℝ τ w)) 0 := by
    simpa only [ContinuousLinearMap.compL_apply] using (hg'.comp 0 hτr).clm_comp hdτ
  calc D.dbarJetNorm k r s y = jetNormAt ℝ r (fun w ↦ e w •
        ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ ((g ∘ τ) w) (fderiv ℝ τ w)) 0 := by
        rw [dbarJetNorm_def, jetNormAt_congr_of_eventuallyEq r heq]
    _ ≤ 2 ^ r * jetNormAt ℝ r e 0 * jetNormAt ℝ r (fun w ↦
          ContinuousLinearMap.compL ℝ (StdSpace ι) (StdSpace ι) ℂ ((g ∘ τ) w) (fderiv ℝ τ w)) 0 :=
        jetNormAt_fun_smul_le her hcomp'
    _ ≤ 2 ^ r * (C * (1 + ‖z‖) ^ r) * (2 ^ r * (C * jetNormAt ℝ r g z * (1 + ‖z‖) ^ r) * C) :=
        mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity)) hgτd
          (jetNormAt_nonneg _ _ _) (by positivity)
    _ = 4 ^ r * C ^ 3 * (1 + ‖z‖) ^ (2 * r) * jetNormAt ℝ r g z := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
        ring
    _ ≤ 4 ^ r * C ^ 3 * (2 ^ r * (1 + d) ^ (2 * r)) * jetNormAt ℝ r g z :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by positivity)) hjg
    _ = 8 ^ r * C ^ 3 * (1 + d) ^ (2 * r) * jetNormAt ℝ r g z := by
        rw [show (8 : ℝ) = 4 * 2 by norm_num, mul_pow]
        ring

end RescaledUnitaryCharts

end SymplecticGeometry

end
