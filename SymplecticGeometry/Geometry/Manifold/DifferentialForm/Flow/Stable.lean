/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Dynamics.Flow.Stable
public import TauCeti.Geometry.Manifold.DifferentialForm.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Basic
import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart
import SymplecticGeometry.Geometry.Manifold.IsManifold.ChartBall

/-!
# Forms scaled by a flow vanish along its stable sets

Let `φ` be a flow of `ℝ` on a boundaryless manifold `M` by differentiable time maps, and `σ` a
continuous `k`-form with `φ_t^* σ = e^t σ` for every time `t`. Let `γ : N → M` be differentiable
at `y`, with `γ y` in the stable set of a point `p`. If, for each tangent vector `v` at `y`, the
derivative at `y` of `z ↦ e (φ_t (γ z))` on `v` is bounded for all large `t`, where `e` is the
extended chart at `p`, then `γ^* σ` vanishes at `y`
(`Flow.mpullback_eq_zero_of_mpullback_eq_exp_smul`).

The value of `σ` at `γ y` on the vectors `dγ (v i)` is `e^{-t}` times the value of `σ` read in
the chart at `φ_t (γ y)` on the pushed vectors. For large `t` that point is near `p`, where the
form read in the chart is bounded, and the pushed vectors are bounded by hypothesis, so the value
is zero.

Weinstein structures use this, with the scaling of `ω` and `ι_X ω` by their Liouville flow, for
the isotropy of the stable sets of their critical points, as in Proposition 11.9 (b) and
Lemma 11.13 (a) of Cieliebak and Eliashberg.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Filter Metric Set TauCeti
open scoped Manifold Topology

namespace Flow

variable {E H M E' H' N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]

/-- **A forward derivative bound kills a form that a flow scales by `e^t`.** Let `φ` be a flow
by differentiable time maps, and `σ` a continuous `k`-form with `φ_t^* σ = e^t σ` for every time
`t`. Let `γ : N → M` be differentiable at `y`, with `γ y` in the stable set of `p`, and suppose
that for each tangent vector `v` at `y` the derivative of `z ↦ e (φ_t (γ z))` at `y` on `v`, for
`e` the extended chart at `p`, is bounded for all large `t`. Then the pullback of `σ` by `γ`
vanishes at `y`. -/
theorem mpullback_eq_zero_of_mpullback_eq_exp_smul (φ : Flow ℝ M)
    (hφ : ∀ t, MDifferentiable I I (φ t)) {k : ℕ} {σ : RoughForm I M ℝ k}
    (hσ : IsSmoothForm I 0 σ) (hσt : ∀ t, mpullback I I (φ t) σ = Real.exp t • σ)
    {p : M} {γ : N → M} {y : N} (hγ : MDifferentiableAt I' I γ y) (hy : γ y ∈ φ.stableSet p)
    (hb : ∀ v : TangentSpace I' y, ∃ C, ∀ᶠ t in atTop,
      ‖mvfderiv I' (fun z ↦ extChartAt I p (φ t (γ z))) y v‖ ≤ C) :
    mpullback I' I γ σ y = 0 := by
  set e := extChartAt I p with he
  ext v
  rw [mpullback_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  set c := σ (γ y) fun i ↦ mfderiv I' I γ y (v i)
  choose C hC using fun i ↦ hb (v i)
  obtain ⟨r, hr, B, -, -, hσB⟩ := hσ.exists_ball_norm_inChartAt_le p
  -- For large `t`, the point `φ_t (γ y)` is in the chart, near `p`.
  have hev : ∀ᶠ t in atTop, φ t (γ y) ∈ e.source ∧ e (φ t (γ y)) ∈ ball (e p) r :=
    ((Flow.mem_stableSet.1 hy).eventually (SymplecticGeometry.chartBall_mem_nhds I p hr)).mono
      fun _ h ↦ (SymplecticGeometry.mem_chartBall_iff I).1 h
  -- There, `e^t c` is the value of the form read in the chart on bounded vectors.
  have hle : ∀ᶠ t in atTop, Real.exp t * |c| ≤ B * ∏ i, C i := by
    filter_upwards [hev, eventually_all.2 hC] with t ⟨hs, hball⟩ hCt
    have hft : MDifferentiableAt I I (φ t) (γ y) := hφ t _
    have hes : MDifferentiableAt I 𝓘(ℝ, E) e (φ t (γ y)) :=
      mdifferentiableAt_extChartAt (by rwa [← extChartAt_source (I := I)])
    have heq : Real.exp t * c = σ.inChartAt p (e (φ t (γ y)))
        fun i ↦ mvfderiv I' (fun z ↦ e (φ t (γ z))) y (v i) := by
      have h := congrArg (fun σ' ↦ σ' (γ y) fun i ↦ mfderiv I' I γ y (v i)) (hσt t)
      simp only [mpullback_apply, Pi.smul_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul] at h
      rw [← h, RoughForm.apply_eq_inChartAt_mvfderiv σ hs]
      congr 1
      funext i
      rw [show (fun z ↦ e (φ t (γ z))) = e ∘ (φ t ∘ γ) from rfl,
        mvfderiv_comp y hes (hft.comp y hγ), ContinuousLinearMap.comp_apply,
        mfderiv_comp_apply y hft hγ, Function.comp_apply, he]
    calc Real.exp t * |c| = ‖Real.exp t * c‖ := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos t)]
      _ ≤ ‖σ.inChartAt p (e (φ t (γ y)))‖ * ∏ i, C i := by
          rw [heq]
          exact ContinuousAlternatingMap.le_opNorm_mul_prod_of_le _ hCt
      _ ≤ B * ∏ i, C i :=
          mul_le_mul_of_nonneg_right (hσB _ hball)
            (Finset.prod_nonneg fun i _ ↦ (norm_nonneg _).trans (hCt i))
  -- So `e^t |c|` is bounded as `t → ∞`, which forces `c = 0`.
  by_contra hc
  have htop : Tendsto (fun t ↦ Real.exp t * |c|) atTop atTop :=
    Real.tendsto_exp_atTop.atTop_mul_const (abs_pos.2 hc)
  obtain ⟨t, ht, ht'⟩ := ((htop.eventually_gt_atTop (B * ∏ i, C i)).and hle).exists
  exact (ht.trans_le ht').false

end Flow

end
