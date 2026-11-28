/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import SymplecticGeometry.Analysis.Calculus.FDeriv.Comp
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.SecondDeriv

/-!
# Derivative bounds for the logarithmic cutoff composed with a function

Let `ψ = TauCeti.logCutoffProfile ε δ` with `0 < 4ε ≤ δ`, `Λ = log (δ / ε)`, and let
`ρ : F → ℝ` be a function on a real normed space whose derivatives at `p` satisfy
`‖Dρ(p)‖ ≤ A √(ρ p)` and `‖D²ρ(p)‖ ≤ A`. This file bounds the derivatives of the cutoff
`ψ ∘ ρ` at `p`:

* `√(ρ p) ‖D(ψ ∘ ρ)(p)‖ ≤ c₀ A / Λ`, with Tau Ceti's constant `c₀ = TauCeti.logCutoffConst`
  (`TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le`);
* `ρ p ‖D²(ψ ∘ ρ)(p)‖ ≤ c (A + A ^ 2) / Λ` for an absolute constant `c`
  (`TauCeti.exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le`).

Both follow from the chain rule (`SymplecticGeometry.norm_fderiv_scalar_comp` and
`SymplecticGeometry.norm_fderiv_fderiv_scalar_comp_le`) and the bounds `r ψ'(r) ≤ c₀ / Λ`
(`TauCeti.mul_deriv_logCutoffProfile_le`) and `|r ^ 2 ψ''(r)| ≤ c₁ / Λ`
(`TauCeti.exists_abs_sq_mul_deriv_deriv_logCutoffProfile_le`): with `r = ρ p`, the factors
`√(ρ p)` and `ρ p` on the left supply the powers of `r` in these bounds. At points with
`ρ p ≤ 0` the left sides are zero or negative.

The library interpolates between two strictly plurisubharmonic functions near a totally real
submanifold with the cutoff `1 - ψ ∘ ρ`, for Proposition 3.26 of [CieliebakEliashberg2012], with
`ρ` comparable to the squared distance to the submanifold. These bounds make the error terms of
that interpolation of order `1 / Λ`.

## Main results

* `TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le`: the first-order bound.
* `TauCeti.exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le`: the second-order bound.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ε δ A : ℝ} {ρ : F → ℝ} {p : F}

/-- **The first derivative of a logarithmic cutoff composed with a function.** For
`0 < 4ε ≤ δ`, a function `ρ` differentiable at `p`, and `0 ≤ A` with `‖Dρ(p)‖ ≤ A √(ρ p)`, the
derivative of `logCutoffProfile ε δ ∘ ρ` at `p` satisfies
`√(ρ p) ‖D(logCutoffProfile ε δ ∘ ρ)(p)‖ ≤ logCutoffConst * A / log (δ / ε)`. -/
theorem sqrt_mul_norm_fderiv_logCutoffProfile_comp_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (hρ : DifferentiableAt ℝ ρ p) (hA0 : 0 ≤ A) (hA : ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p)) :
    √(ρ p) * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖ ≤
      logCutoffConst * A / Real.log (δ / ε) := by
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  rcases le_or_gt (ρ p) 0 with h0 | hpos
  · rw [Real.sqrt_eq_zero'.2 h0, zero_mul]
    exact div_nonneg (mul_nonneg logCutoffConst_pos.le hA0) hΛ.le
  have hg : DifferentiableAt ℝ (logCutoffProfile ε δ) (ρ p) :=
    ((contDiff_logCutoffProfile (by linarith)).differentiable (by simp)) _
  have hd := deriv_logCutoffProfile_nonneg (δ := δ) hε (by linarith) (ρ p)
  calc √(ρ p) * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖
      ≤ √(ρ p) * (deriv (logCutoffProfile ε δ) (ρ p) * (A * √(ρ p))) := by
        rw [SymplecticGeometry.norm_fderiv_scalar_comp hg hρ, Real.norm_of_nonneg hd]
        gcongr
    _ = ρ p * deriv (logCutoffProfile ε δ) (ρ p) * A := by
        linear_combination (deriv (logCutoffProfile ε δ) (ρ p) * A) * Real.mul_self_sqrt hpos.le
    _ ≤ logCutoffConst / Real.log (δ / ε) * A := by
        gcongr
        exact mul_deriv_logCutoffProfile_le hε h4 (ρ p)
    _ = logCutoffConst * A / Real.log (δ / ε) := by ring

/-- **The second derivative of a logarithmic cutoff composed with a function.** There is an
absolute constant `c` such that, for every real normed space `F`, `0 < 4ε ≤ δ`, and a function
`ρ : F → ℝ` that is `C²` at `p` with `‖Dρ(p)‖ ≤ A √(ρ p)` and `‖D²ρ(p)‖ ≤ A`, the second
derivative of `logCutoffProfile ε δ ∘ ρ` at `p` satisfies
`ρ p ‖D²(logCutoffProfile ε δ ∘ ρ)(p)‖ ≤ c (A + A ^ 2) / log (δ / ε)`. -/
theorem exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le :
    ∃ c : ℝ, ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ε δ A : ℝ} {ρ : F → ℝ}
      {p : F}, 0 < ε → 4 * ε ≤ δ → ContDiffAt ℝ 2 ρ p →
      ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p) → ‖fderiv ℝ (fderiv ℝ ρ) p‖ ≤ A →
      ρ p * ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ ≤
        c * (A + A ^ 2) / Real.log (δ / ε) := by
  obtain ⟨c₁, hc₁⟩ := exists_abs_sq_mul_deriv_deriv_logCutoffProfile_le
  refine ⟨logCutoffConst + |c₁|, fun {F} _ _ {ε δ A ρ p} hε h4 hρ hA hA' ↦ ?_⟩
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hA0 : 0 ≤ A := (norm_nonneg (fderiv ℝ (fderiv ℝ ρ) p)).trans hA'
  rcases le_or_gt (ρ p) 0 with h0 | hpos
  · have := logCutoffConst_pos
    exact le_trans (mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)) (by positivity)
  have hg : ContDiffAt ℝ 2 (logCutoffProfile ε δ) (ρ p) :=
    (contDiff_logCutoffProfile (by linarith)).contDiffAt.of_le (by simp)
  have hd := deriv_logCutoffProfile_nonneg (δ := δ) hε (by linarith) (ρ p)
  have hD : ‖fderiv ℝ ρ p‖ ^ 2 ≤ A ^ 2 * ρ p := by
    rw [← Real.sq_sqrt hpos.le, ← mul_pow]
    gcongr
  calc ρ p * ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖
      ≤ ρ p * (|deriv (deriv (logCutoffProfile ε δ)) (ρ p)| * (A ^ 2 * ρ p) +
          deriv (logCutoffProfile ε δ) (ρ p) * A) := by
        gcongr
        refine (SymplecticGeometry.norm_fderiv_fderiv_scalar_comp_le hg hρ).trans ?_
        rw [iteratedDeriv_succ, iteratedDeriv_one, Real.norm_eq_abs, Real.norm_of_nonneg hd]
        gcongr
    _ = |ρ p ^ 2 * deriv (deriv (logCutoffProfile ε δ)) (ρ p)| * A ^ 2 +
          ρ p * deriv (logCutoffProfile ε δ) (ρ p) * A := by
        rw [abs_mul, abs_of_pos (pow_pos hpos 2)]
        ring
    _ ≤ |c₁| / Real.log (δ / ε) * A ^ 2 + logCutoffConst / Real.log (δ / ε) * A := by
        gcongr
        · exact (hc₁ hε h4 _).trans (by gcongr; exact le_abs_self _)
        · exact mul_deriv_logCutoffProfile_le hε h4 (ρ p)
    _ ≤ (logCutoffConst + |c₁|) * (A + A ^ 2) / Real.log (δ / ε) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
        gcongr
        nlinarith [logCutoffConst_pos, abs_nonneg c₁, sq_nonneg A]

end TauCeti

end
