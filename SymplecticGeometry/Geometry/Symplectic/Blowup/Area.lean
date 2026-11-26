/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Symplectic.Blowup.Profile
import SymplecticGeometry.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Analysis.Complex.QuadraticLeviForm
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The area potential of the symplectic blowup

For `0 < l` and `0 < ε`, the area of a holomorphic curve `u` in `E = ℂⁿ⁺¹` for the standard form
`ω₀` and that of its lift to the model blowup for the form `ω̃_{l,ε}` (`profileForm`) differ, off
the zeros of `u`, by a quarter of the Laplacian of `φ ∘ u`, with
`φ(z) = -(l² log |z|² + q(|z|²))` for `q = blowupCorrection l ε` and the Euclidean norm `|z|`.
In the variable `s = |z|²` this is `s - g(s)`, where `g(s) = s + l² log s + q(s)` is the radial
potential of `ω̃_{l,ε}` off the divisor and `s` that of `ω₀`.

This file defines that potential and proves the two facts about `φ ∘ u` that the area formula
uses, before any form enters:

* `SymplecticGeometry.BlowupModel.areaPotential l ε`: the function `φ`.
* `SymplecticGeometry.BlowupModel.areaPotential_of_ge`: `φ` is constant on `|z|² ≥ (l + ε)²`,
  by `sq_mul_log_add_blowupCorrection_of_ge`; so `φ ∘ u` is locally constant near every point
  where `u` is continuous with `|u| > l + ε` (`areaPotential_comp_eventuallyEq`).
* `SymplecticGeometry.BlowupModel.exists_areaPotential_comp_eq_log_add`: at a zero `t₀` of order
  `k` of a curve `u`, written `u t = (t - t₀)ᵏ • g t` near `t₀` with `g` analytic and
  `g t₀ ≠ 0`, as Mathlib's `AnalyticAt.analyticOrderAt_eq_natCast` gives it, the function
  `φ ∘ u` is `-l² k log |t - t₀|²` plus a function smooth at `t₀`, off `t₀`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], (7.1.7) and
  the proof of Proposition 7.1.13.
-/

public section

noncomputable section

open Filter Topology TauCeti
open scoped ContDiff

namespace SymplecticGeometry.BlowupModel

variable {n : ℕ} {l ε : ℝ}

/-- The area potential `φ(z) = -(l² log |z|² + q(|z|²))` on `ℂⁿ⁺¹`, for
`q = blowupCorrection l ε` and `|z|` the Euclidean norm. In the variable `s = |z|²` it is
`s - g(s)`, for `g(s) = s + l² log s + q(s)` the radial potential of `profileForm n l ε` off the
exceptional divisor; for `z = 0` the logarithm is Lean's `Real.log 0 = 0`. -/
def areaPotential (l ε : ℝ) (z : Fin (n + 1) → ℂ) : ℝ :=
  -(l ^ 2 * Real.log (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) +
    blowupCorrection l ε (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2))

theorem areaPotential_def (l ε : ℝ) (z : Fin (n + 1) → ℂ) :
    areaPotential l ε z =
      -(l ^ 2 * Real.log (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) +
        blowupCorrection l ε (‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2)) :=
  (rfl)

/-- Far from the origin the area potential is constant: for `|z|² ≥ (l + ε)²` it takes the value
`-(l² log (l + ε)² + q((l + ε)²))`. -/
theorem areaPotential_of_ge (hl : 0 < l) (hε : 0 < ε) {z : Fin (n + 1) → ℂ}
    (hz : (l + ε) ^ 2 ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2) :
    areaPotential l ε z =
      -(l ^ 2 * Real.log ((l + ε) ^ 2) + blowupCorrection l ε ((l + ε) ^ 2)) := by
  rw [areaPotential_def, sq_mul_log_add_blowupCorrection_of_ge hl hε hz]

/-- Along a map `u` continuous at `t` with `|u t| > l + ε`, the area potential is constant near
`t`. -/
theorem areaPotential_comp_eventuallyEq {X : Type*} [TopologicalSpace X]
    {u : X → Fin (n + 1) → ℂ} {t : X} (hl : 0 < l) (hε : 0 < ε) (hu : ContinuousAt u t)
    (ht : l + ε < ‖complexToRealEuclidean (Fin (n + 1)) (u t)‖) :
    areaPotential l ε ∘ u =ᶠ[𝓝 t] fun _ ↦ areaPotential l ε (u t) := by
  have hc : ContinuousAt (fun s ↦ ‖complexToRealEuclidean (Fin (n + 1)) (u s)‖) t :=
    ((complexToRealEuclidean (Fin (n + 1))).continuous.norm).continuousAt.comp hu
  have hge : ∀ {z : Fin (n + 1) → ℂ}, l + ε < ‖complexToRealEuclidean (Fin (n + 1)) z‖ →
      (l + ε) ^ 2 ≤ ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2 :=
    fun h ↦ pow_le_pow_left₀ (by positivity) h.le 2
  filter_upwards [hc.eventually (lt_mem_nhds ht)] with s hs
  rw [Function.comp_apply, areaPotential_of_ge hl hε (hge hs), areaPotential_of_ge hl hε (hge ht)]

/-- At a zero of finite order: if `u t = (t - t₀) ^ k • g t` near `t₀`, with `g` analytic at `t₀`
and `g t₀ ≠ 0`, then off `t₀` and near it the area potential along `u` is
`-l² k log |t - t₀|²` plus a function that is smooth at `t₀`. -/
theorem exists_areaPotential_comp_eq_log_add {u g : ℂ → Fin (n + 1) → ℂ} {t₀ : ℂ} {k : ℕ}
    (hl : 0 < l) (hε : 0 < ε) (hg : AnalyticAt ℂ g t₀) (hg0 : g t₀ ≠ 0)
    (hug : ∀ᶠ t in 𝓝 t₀, u t = (t - t₀) ^ k • g t) :
    ∃ h : ℂ → ℝ, ContDiffAt ℝ ∞ h t₀ ∧ ∀ᶠ t in 𝓝[≠] t₀,
      areaPotential l ε (u t) = -(l ^ 2 * k * Real.log (‖t - t₀‖ ^ 2)) + h t := by
  set N : (Fin (n + 1) → ℂ) → ℝ := fun z ↦ ‖complexToRealEuclidean (Fin (n + 1)) z‖ ^ 2
  have hN : ContDiff ℝ ∞ N := contDiff_norm_sq_complexToRealEuclidean
  have hN0 : ∀ {z}, z ≠ 0 → N z ≠ 0 := fun hz ↦
    pow_ne_zero 2 (norm_ne_zero_iff.2 ((complexToRealEuclidean _).map_ne_zero_iff.2 hz))
  have hua : AnalyticAt ℂ u t₀ :=
    (((analyticAt_id.sub analyticAt_const).pow k).smul hg).congr (hug.mono fun _ h ↦ h.symm)
  have hsmooth : ContDiffAt ℝ ∞
      (fun t ↦ -(l ^ 2 * Real.log (N (g t)) + blowupCorrection l ε (N (u t)))) t₀ :=
    ((contDiffAt_const.mul ((hN.contDiffAt.comp t₀ (hg.contDiffAt.restrict_scalars ℝ)).log
      (hN0 hg0))).add ((contDiff_blowupCorrection hl hε).contDiffAt.comp t₀
        (hN.contDiffAt.comp t₀ (hua.contDiffAt.restrict_scalars ℝ)))).neg
  refine ⟨_, hsmooth, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hug, self_mem_nhdsWithin,
    nhdsWithin_le_nhds (hg.continuousAt.eventually_ne hg0)] with t ht htne hgt
  have hN_smul : N (u t) = (‖t - t₀‖ ^ 2) ^ k * N (g t) := by
    simp only [N, ht, norm_complexToRealEuclidean_smul, norm_pow, mul_pow, ← pow_mul]
    ring
  have ht0 : ‖t - t₀‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 (sub_ne_zero.2 htne))
  have hlog : Real.log (N (u t)) = k * Real.log (‖t - t₀‖ ^ 2) + Real.log (N (g t)) := by
    rw [hN_smul, Real.log_mul (pow_ne_zero k ht0) (hN0 hgt), Real.log_pow]
  calc areaPotential l ε (u t)
      = -(l ^ 2 * Real.log (N (u t)) + blowupCorrection l ε (N (u t))) :=
        areaPotential_def l ε (u t)
    _ = _ := by rw [hlog]; ring

end SymplecticGeometry.BlowupModel

end
