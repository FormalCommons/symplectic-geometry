/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import TauCeti.Analysis.InnerProductSpace.Normalize
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Radial extensions of a function on the unit sphere

Let `τ` be a function on a real inner product space `F` that is `Cⁿ` at each point of the unit
sphere and bounded below there by a constant `C`. For every `ρ > 0` this file gives a `Cⁿ`
function `θ : F → ℝ` that is constant near `0`, equal to `τ u` at `r • u` for every unit vector
`u` and every `r ≥ ρ`, and such that `r ↦ θ (r • u) + log r` has a positive derivative at every
`r > 0` (`SymplecticGeometry.exists_contDiff_radial_extension_hasDerivAt_add_log_pos_of_le`).
On a finite-dimensional space the bound below holds since the sphere is compact
(`SymplecticGeometry.exists_contDiff_radial_extension_hasDerivAt_add_log_pos`).

Away from `0` the function is `θ x = C + χ (log ‖x‖) * (τ (normalize x) - C)`, with Mathlib's
`NormedSpace.normalize x = ‖x‖⁻¹ • x` (smooth off `0` by Tau Ceti's
`NormedSpace.contDiffAt_normalize`) and a monotone smooth cutoff `χ` in `log ‖x‖`, equal to `0`
below `log ρ - 1` and to `1` above `log ρ`, built from Mathlib's `Real.smoothTransition`.
Along the ray through a unit vector `u`, the derivative of
`θ (r • u) + log r` is `(1 + χ' (log r) * (τ u - C)) / r`, positive since `χ' ≥ 0` (Tau Ceti's
`Real.smoothTransition.deriv_nonneg`) and `τ u ≥ C`.

Such a function serves as a time function in charts of unstable sets of a gradient-like flow
that are built from the flow lines through a small sphere.
-/

public section

open Filter Metric NormedSpace
open scoped Topology

namespace SymplecticGeometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Let `τ : F → ℝ` be `Cⁿ` at every point of the unit sphere of a real inner product space and
at least `C` there, and let `ρ > 0`. Then there is a `Cⁿ` function `θ : F → ℝ`, constant near `0`,
with `θ (r • u) = τ u` for every unit vector `u` and every `r ≥ ρ`, such that for every unit
vector `u` the function `r ↦ θ (r • u) + log r` has a positive derivative at every `r > 0`. -/
theorem exists_contDiff_radial_extension_hasDerivAt_add_log_pos_of_le {n : ℕ∞} {τ : F → ℝ}
    {C ρ : ℝ} (hτ : ∀ u, ‖u‖ = 1 → ContDiffAt ℝ n τ u) (hC : ∀ u, ‖u‖ = 1 → C ≤ τ u)
    (hρ : 0 < ρ) :
    ∃ θ : F → ℝ, ContDiff ℝ n θ ∧ (∀ᶠ x in 𝓝 0, θ x = θ 0) ∧
      (∀ u, ‖u‖ = 1 → ∀ r, ρ ≤ r → θ (r • u) = τ u) ∧
      ∀ u, ‖u‖ = 1 → ∀ r, 0 < r →
        ∃ d, 0 < d ∧ HasDerivAt (fun s ↦ θ (s • u) + Real.log s) d r := by
  -- The cutoff `χ (log ‖x‖)`, and the formula for `θ` away from `0`.
  set χ : ℝ → ℝ := fun s ↦ Real.smoothTransition (s - Real.log ρ + 1) with hχ
  set g : F → ℝ := fun x ↦ C + χ (Real.log ‖x‖) * (τ (normalize x) - C) with hg
  -- Below the radius `ρ * exp (-1)` the cutoff vanishes.
  have hsmall {x : F} (hx : x ≠ 0) (hxρ : ‖x‖ < ρ * Real.exp (-1)) : g x = C := by
    have hlog : Real.log ‖x‖ < Real.log ρ - 1 := by
      have := Real.log_lt_log (norm_pos_iff.2 hx) hxρ
      rwa [Real.log_mul hρ.ne' (Real.exp_pos _).ne', Real.log_exp, ← sub_eq_add_neg] at this
    simp only [hg, hχ]
    rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul, add_zero]
  -- Along the ray through a unit vector `u`, `g (s • u) = C + χ (log s) * (τ u - C)`.
  have hray {u : F} (hu : ‖u‖ = 1) {s : ℝ} (hs : 0 < s) :
      g (s • u) = C + χ (Real.log s) * (τ u - C) := by
    have hsu : ‖s • u‖ = s := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hs.le]
    simp only [hg, hsu, normalize_smul_of_pos hs, normalize_eq_self_of_norm_eq_one hu]
  classical
  refine ⟨fun x ↦ if x = 0 then C else g x, ?_, ?_, ?_, ?_⟩
  · -- Near `0` the function is the constant `C`; away from `0` it is `g`.
    have h0 : (fun x ↦ if x = 0 then C else g x) =ᶠ[𝓝 (0 : F)] fun _ ↦ C := by
      filter_upwards [ball_mem_nhds (0 : F) (mul_pos hρ (Real.exp_pos (-1)))] with y hy
      rw [mem_ball_zero_iff] at hy
      rcases eq_or_ne y 0 with h | h
      · simp [h]
      · simp [h, hsmall h hy]
    refine contDiff_iff_contDiffAt.2 fun x ↦ ?_
    rcases eq_or_ne x 0 with rfl | hx
    · exact contDiffAt_const.congr_of_eventuallyEq h0
    refine ContDiffAt.congr_of_eventuallyEq (f := g) ?_
      ((isOpen_ne.eventually_mem hx).mono fun y (hy : y ≠ 0) ↦ by simp [hy])
    exact contDiffAt_const.add <|
      ((Real.smoothTransition.contDiffAt (n := n)).comp x
        ((((contDiffAt_norm (n := n) ℝ hx).log (norm_ne_zero_iff.2 hx)).sub
          contDiffAt_const).add contDiffAt_const)).mul
      (((hτ _ (norm_normalize_eq_one_iff.2 hx)).comp x (contDiffAt_normalize hx)).sub
        contDiffAt_const)
  · filter_upwards [ball_mem_nhds (0 : F) (mul_pos hρ (Real.exp_pos (-1)))] with y hy
    rw [mem_ball_zero_iff] at hy
    rcases eq_or_ne y 0 with h | h
    · simp [h]
    · simp [h, hsmall h hy]
  · intro u hu r hr
    have hr0 : 0 < r := hρ.trans_le hr
    have hne : r • u ≠ 0 := smul_ne_zero hr0.ne' (norm_ne_zero_iff.1 (by simp [hu]))
    have hlog := Real.log_le_log hρ hr
    simp only [hne, ↓reduceIte, hray hu hr0, hχ]
    rw [Real.smoothTransition.one_of_one_le (x := Real.log r - Real.log ρ + 1) (by linarith),
      one_mul, add_sub_cancel]
  · intro u hu r hr
    have hu0 : u ≠ 0 := norm_ne_zero_iff.1 (by simp [hu])
    have ht : HasDerivAt (fun s ↦ Real.log s - Real.log ρ + 1) r⁻¹ r :=
      ((Real.hasDerivAt_log hr.ne').sub_const _).add_const _
    have hd := (((((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)
      _).hasDerivAt.comp r ht).mul_const (τ u - C)).const_add C).add (Real.hasDerivAt_log hr.ne')
    refine ⟨_, add_pos_of_nonneg_of_pos (mul_nonneg (mul_nonneg
      (Real.smoothTransition.deriv_nonneg _) (inv_nonneg.2 hr.le)) (sub_nonneg.2 (hC u hu)))
      (inv_pos.2 hr), hd.congr_of_eventuallyEq ?_⟩
    filter_upwards [Ioi_mem_nhds hr] with s (hs : 0 < s)
    simp only [smul_ne_zero hs.ne' hu0, ↓reduceIte, hray hu hs, hχ, Function.comp_apply,
      Pi.add_apply]

/-- Let `τ : F → ℝ` be `Cⁿ` at every point of the unit sphere of a finite-dimensional real inner
product space, and let `ρ > 0`. Then there is a `Cⁿ` function `θ : F → ℝ`, constant near `0`,
with `θ (r • u) = τ u` for every unit vector `u` and every `r ≥ ρ`, such that for every unit
vector `u` the function `r ↦ θ (r • u) + log r` has a positive derivative at every `r > 0`. -/
theorem exists_contDiff_radial_extension_hasDerivAt_add_log_pos [FiniteDimensional ℝ F]
    {n : ℕ∞} {τ : F → ℝ} {ρ : ℝ} (hτ : ∀ u, ‖u‖ = 1 → ContDiffAt ℝ n τ u) (hρ : 0 < ρ) :
    ∃ θ : F → ℝ, ContDiff ℝ n θ ∧ (∀ᶠ x in 𝓝 0, θ x = θ 0) ∧
      (∀ u, ‖u‖ = 1 → ∀ r, ρ ≤ r → θ (r • u) = τ u) ∧
      ∀ u, ‖u‖ = 1 → ∀ r, 0 < r →
        ∃ d, 0 < d ∧ HasDerivAt (fun s ↦ θ (s • u) + Real.log s) d r := by
  have hcont : ContinuousOn τ (sphere (0 : F) 1) := fun u hu ↦
    (hτ u (mem_sphere_zero_iff_norm.1 hu)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : F) 1).bddBelow_image hcont
  exact exists_contDiff_radial_extension_hasDerivAt_add_log_pos_of_le hτ
    (fun u hu ↦ hC ⟨u, mem_sphere_zero_iff_norm.2 hu, rfl⟩) hρ

end SymplecticGeometry

end
