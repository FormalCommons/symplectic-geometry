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
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Lift
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.Calculus.ContDiff.Differentiable

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

It then proves the pointwise identity between the two densities at a point `t` with `u t ≠ 0`,
each density being the value of the form on the derivatives of the curve along `1` and `i`:

* `SymplecticGeometry.BlowupModel.eval₂_profileForm_mfderiv_curveLift`: for `u` complex
  differentiable at `t` with `u t ≠ 0`, the density of the pull-back of `ω̃_{l,ε}` along
  `curveLift u` is `g'(s) |v|² + g''(s) |star (u t) ⬝ᵥ v|²`, with `s = |u t|²` and `v = u'(t)`.
  By `mfderiv_curveLift_of_ne_zero` the derivative of the lift at `t` is that of the inverse of
  the blowdown off the divisor, which is also the inverse of `blowdownPuncturedDiffeomorph`
  (`coe_blowdownPuncturedDiffeomorph_symm`), along whose inverse
  `ω̃_{l,ε}` pulls back to the radial potential form of `g`
  (`mpullback_blowdownDiffeomorph_symm_profileForm`); its value on `(v, i v)` is
  `radialPotentialForm_apply_I_smul`. Only the derivative of the lift at `t` enters, so no form
  is pulled back along the lift itself, which is smooth only near `t`.
* `SymplecticGeometry.BlowupModel.eval₂_ω₀E_sub_eval₂_profileForm_curveLift`: for `u` analytic
  at `t`, the density of `u^* ω₀` minus that of the lift is `Δ (φ ∘ u) (t) / 4`. The density of
  `u^* ω₀` is `|v|²` (`eval₂_constSmooth_stdComplexPiSymplecticForm_mfderiv`), and
  `TauCeti.laplacian_comp_sum_norm_sq_div_four` computes `Δ (ψ |u|²) (t) / 4` as
  `ψ'(s) |v|² + ψ''(s) |star (u t) ⬝ᵥ v|²`, here for `ψ(s) = s - g(s)`.

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


/-! ### The two area densities along a curve -/

section Density

open scoped Laplacian Manifold TauCeti.ComplexManifold

/-- The density of `(curveLift u)^* ω̃_{l,ε}` at a point `t` off the zeros of `u`, for `0 < l`,
`0 < ε` and `u : ℂ → ℂⁿ⁺¹` complex differentiable at `t` with `u t ≠ 0`: the value of
`profileForm n l ε` on the derivatives of the lift along `1` and `i` is
`g'(s) |v|² + g''(s) |star (u t) ⬝ᵥ v|²`, for `v = u'(t)`, `s = |u t|²` and the radial potential
`g(s) = s + l² log s + q(s)` of `ω̃_{l,ε}` off the exceptional divisor. -/
theorem eval₂_profileForm_mfderiv_curveLift (hl : 0 < l) (hε : 0 < ε)
    {u : ℂ → Fin (n + 1) → ℂ} {t : ℂ} (hu : DifferentiableAt ℂ u t) (h0 : u t ≠ 0) :
    (profileForm n l ε).eval₂ (curveLift u t)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t Complex.I) =
      deriv (fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s) (∑ i, ‖u t i‖ ^ 2) *
          ∑ i, ‖deriv u t i‖ ^ 2 +
        deriv (deriv fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s)
            (∑ i, ‖u t i‖ ^ 2) * Complex.normSq (star (u t) ⬝ᵥ deriv u t) := by
  -- Off the divisor, read `ω̃_{l,ε}` through the blowdown as a radial potential form.
  have key := SmoothForm.eval₂_mpullback _
    (contMDiff_subtypeVal.comp (blowdownPuncturedDiffeomorph n).symm.contMDiff)
    (profileForm n l ε) ⟨u t, mem_puncturedSpace.2 h0⟩
    (deriv u t : Fin (n + 1) → ℂ) (Complex.I • deriv u t : Fin (n + 1) → ℂ)
  rw [← SmoothForm.mpullback_mpullback _ _ (blowdownPuncturedDiffeomorph n).symm.contMDiff
    contMDiff_subtypeVal, mpullback_blowdownDiffeomorph_symm_profileForm n hl hε,
    radialPotentialForm_apply_I_smul, Function.comp_apply,
    coe_blowdownPuncturedDiffeomorph_symm_apply] at key
  rw [mfderiv_curveLift_of_ne_zero hu h0, mfderiv_curveLift_of_ne_zero hu h0, one_smul,
    curveLift_of_ne_zero h0, ← coe_blowdownPuncturedDiffeomorph_symm]
  exact key.symm

/-- **The two area densities along a curve differ by a quarter Laplacian.** For `0 < l`, `0 < ε`
and `u : ℂ → ℂⁿ⁺¹` analytic at `t` with `u t ≠ 0`, the density at `t` of `u^* ω₀` minus that of
`(curveLift u)^* ω̃_{l,ε}`, each read on the derivatives along `1` and `i`, is
`Δ (φ ∘ u) (t) / 4`, for the area potential `φ = areaPotential l ε` and Mathlib's Laplacian `Δ`. -/
theorem eval₂_ω₀E_sub_eval₂_profileForm_curveLift (hl : 0 < l) (hε : 0 < ε)
    {u : ℂ → Fin (n + 1) → ℂ} {t : ℂ} (hu : AnalyticAt ℂ u t) (h0 : u t ≠ 0) :
    (ω₀E n).eval₂ (u t) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) u t (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) u t Complex.I) -
      (profileForm n l ε).eval₂ (curveLift u t)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t (1 : ℂ))
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, Fin (n + 1) → ℂ) (curveLift u) t Complex.I) =
      Δ (areaPotential l ε ∘ u) t / 4 := by
  set g : ℝ → ℝ := fun s ↦ s + l ^ 2 * Real.log s + blowupCorrection l ε s
  set x := ∑ i, ‖u t i‖ ^ 2
  have hx : 0 < x := sum_norm_sq_pos h0
  -- In the variable `s = |z|²` the area potential is `s - g(s)`.
  have hφ : areaPotential l ε ∘ u = fun s ↦ (fun r ↦ r - g r) (∑ i, ‖u s i‖ ^ 2) :=
    funext fun s ↦ by
      simp only [Function.comp_apply, areaPotential_def, norm_sq_complexToRealEuclidean, g]
      ring
  have hg : ContDiffOn ℝ ∞ g (Set.Ioi 0) := contDiffOn_add_mul_log_add_blowupCorrection hl hε
  have hg2 : ∀ r ∈ Set.Ioi (0 : ℝ), ContDiffAt ℝ 2 g r :=
    fun r hr ↦ (hg.contDiffAt (Ioi_mem_nhds hr)).of_le (by simp)
  have h1 : deriv (fun r ↦ r - g r) =ᶠ[𝓝 x] fun r ↦ 1 - deriv g r :=
    Filter.eventuallyEq_of_mem (Ioi_mem_nhds hx) fun r hr ↦ by
      rw [deriv_fun_sub differentiableAt_fun_id ((hg2 r hr).differentiableAt (by simp)),
        deriv_id'']
  rw [ω₀E_def, eval₂_constSmooth_stdComplexPiSymplecticForm_mfderiv hu.differentiableAt,
    eval₂_profileForm_mfderiv_curveLift hl hε hu.differentiableAt h0, hφ,
    laplacian_comp_sum_norm_sq_div_four (ψ := fun r ↦ r - g r)
      (contDiffAt_id.sub (hg2 x hx)) hu.contDiffAt,
    h1.deriv_eq, h1.eq_of_nhds,
    deriv_fun_sub (differentiableAt_const _) (hg2 x hx).differentiableAt_deriv_two,
    deriv_const]
  ring

end Density
end SymplecticGeometry.BlowupModel

end
