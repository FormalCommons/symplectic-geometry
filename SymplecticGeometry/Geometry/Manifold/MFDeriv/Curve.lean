/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Curve
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Analysis.Calculus.Deriv.BoundedReparametrization

/-!
# Velocities of curves along which a map is constant, and curves with a given velocity

This file adds to Tau Ceti's API for `TauCeti.Manifold.curveVelocityWithin` and
`TauCeti.Manifold.curveVelocity` (`TauCeti/Geometry/Manifold/MFDeriv/Curve.lean`).

## Main results

* `TauCeti.Manifold.mfderiv_curveVelocityWithin_eq_zero_of_eqOn`: if `f ∘ γ` is constant on a
  parameter set `s`, the derivative of `f` kills the velocity of `γ` within `s` at every point of
  `s`. Where `f` and `γ` are differentiable and the derivative within `s` is unique, this is
  Tau Ceti's chain rule `TauCeti.Manifold.curveVelocityWithin_map`; elsewhere the derivative of
  `f` or the velocity of `γ` is `0`.
* `TauCeti.Manifold.exists_contMDiff_curveVelocity_eq`: on a real manifold without boundary,
  every tangent vector `v` at `x` is the velocity at `0` of a `C^n` curve `γ : ℝ → M` with
  `γ 0 = x`. In the extended chart at `x` the curve is `t ↦ c + φ t • d`, where `c` is the
  image of `x`, `d` that of `v`, and `φ` is a small bounded reparametrization of the line given
  by Tau Ceti's `TauCeti.exists_contDiff_hasDerivAt_abs_le`, so that the curve stays in the
  target of the chart for all times. Its velocity is computed with Tau Ceti's
  `TauCeti.Manifold.hasMFDerivWithinAt_extChartAt_symm_comp`. Tau Ceti's
  `TauCeti.Manifold.exists_contMDiffAt_curveVelocity_eq` is the local version, whose curve is
  smooth only near the given time.
-/

public section

open Set
open scoped Manifold

namespace TauCeti.Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F H G M N : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace H] [TopologicalSpace G]
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 F G}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]

/-- Let `γ` be a curve and `f` a map such that `f ∘ γ` is constant on `s`. Then for `t ∈ s`,
the derivative of `f` at `γ t` sends the velocity of `γ` within `s` at `t` to `0`. -/
theorem mfderiv_curveVelocityWithin_eq_zero_of_eqOn {f : M → N} {γ : 𝕜 → M} {s : Set 𝕜}
    {t : 𝕜} {y : N} (hfγ : EqOn (f ∘ γ) (fun _ ↦ y) s) (ht : t ∈ s) :
    mfderiv I J f (γ t) (curveVelocityWithin I γ s t) = 0 := by
  by_cases hf : MDifferentiableAt I J f (γ t)
  swap
  · rw [mfderiv_zero_of_not_mdifferentiableAt hf, zero_apply]
  by_cases hγ : MDifferentiableWithinAt 𝓘(𝕜, 𝕜) I γ s t
  swap
  · have hv : curveVelocityWithin I γ s t = 0 := by
      rw [curveVelocityWithin_apply, mfderivWithin_zero_of_not_mdifferentiableWithinAt hγ]
      exact zero_apply _
    rw [hv, map_zero]
  by_cases hs : UniqueDiffWithinAt 𝕜 s t
  · rw [← curveVelocityWithin_map hf hs hγ, curveVelocityWithin_apply,
      mfderivWithin_congr hfγ (hfγ ht), mfderivWithin_const]
    exact zero_apply _
  · rw [curveVelocityWithin_eq_zero_of_not_uniqueDiffWithinAt hs, map_zero]


section Real

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]

/-- **A curve with a given velocity.** On a real manifold without boundary, every tangent vector
`v` at `x` is the velocity at time `0` of a `C^n` curve `γ : ℝ → M` defined for all times, with
`γ 0 = x`. -/
theorem exists_contMDiff_curveVelocity_eq {n : WithTop ℕ∞} [IsManifold I n M] [IsManifold I 1 M]
    (x : M) (v : TangentSpace I x) :
    ∃ γ : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I n γ ∧ γ 0 = x ∧ curveVelocity I γ 0 = v := by
  set c : E := extChartAt I x x
  set d : E := mfderiv I 𝓘(ℝ, E) (extChartAt I x) x v
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 (extChartAt_target_mem_nhds (I := I) x)
  set ε : ℝ := r / (‖d‖ + 1)
  have hε : 0 < ε := by positivity
  obtain ⟨φ, hφs, hφ0, hφd, hφε⟩ := TauCeti.exists_contDiff_hasDerivAt_abs_le hε
  -- The curve in the chart, which stays in the ball of radius `r` about `c`.
  set g : ℝ → E := fun t ↦ c + φ t • d
  have hg_mem (t : ℝ) : g t ∈ (extChartAt I x).target := by
    refine hrt ?_
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    calc |φ t| * ‖d‖ ≤ ε * ‖d‖ := by gcongr; exact hφε t
      _ = r * (‖d‖ / (‖d‖ + 1)) := by ring
      _ < r * 1 := by
          gcongr
          exact (div_lt_one (by positivity)).2 (lt_add_one _)
      _ = r := mul_one r
  have hg : ContDiff ℝ n g := contDiff_const.add ((hφs.of_le le_top).smul contDiff_const)
  have hgd : HasDerivAt g d 0 := by
    simpa only [one_smul] using (hφd.smul_const d).const_add c
  refine ⟨fun t ↦ (extChartAt I x).symm (g t),
    (contMDiffOn_extChartAt_symm x).comp_contMDiff hg.contMDiff hg_mem, by simp [g, c, hφ0], ?_⟩
  have h := hasMFDerivWithinAt_extChartAt_symm_comp (J := univ) (hg_mem 0)
    (Filter.Eventually.of_forall fun t ↦ extChartAt_target_subset_range x (hg_mem t))
    hgd.hasDerivWithinAt
  rw [← curveVelocityWithin_univ, curveVelocityWithin_eq_of_hasMFDerivWithinAt h
    uniqueDiffWithinAt_univ]
  have h0 : g 0 = c := by simp [g, hφ0]
  rw [h0]
  exact congr($(mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' (mem_extChartAt_source x))
    v)

end Real

end TauCeti.Manifold

end
