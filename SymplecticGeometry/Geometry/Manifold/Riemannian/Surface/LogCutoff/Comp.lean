/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Geometry.Manifold.Riemannian.Surface.LogCutoff.Profile
import SymplecticGeometry.Analysis.Calculus.FDeriv.ScalarComp
import SymplecticGeometry.Geometry.Manifold.Riemannian.Surface.LogCutoff.SecondDeriv

/-!
# Derivative bounds for the logarithmic cutoff composed with a function

Let `ψ = TauCeti.logCutoffProfile ε δ` with `0 < 4ε ≤ δ`, `Λ = log (δ / ε)`, and let
`ρ : F → ℝ` be a nonnegative function on a real normed space whose derivatives at `p` satisfy
`‖Dρ(p)‖ ≤ A √(ρ p)` and `‖D²ρ(p)‖ ≤ A`. This file bounds the derivatives of the cutoff
`ψ ∘ ρ` at `p`:

* `√(ρ p) ‖D(ψ ∘ ρ)(p)‖ ≤ c₀ A / Λ`, with Tau Ceti's constant `c₀ = TauCeti.logCutoffConst`
  (`TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le`);
* `ρ p ‖D²(ψ ∘ ρ)(p)‖ ≤ c (A + A ^ 2) / Λ` for an absolute constant `c`
  (`TauCeti.exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le`).

Both follow from the chain rule (`SymplecticGeometry.norm_fderiv_comp_le` and
`SymplecticGeometry.norm_fderiv_fderiv_comp_le`) and the bounds `ψ'(r) ≤ c₀ / (r Λ)`
(Tau Ceti's `TauCeti.deriv_logCutoffProfile_le`) and `|ψ''(r)| ≤ c₁ / (r ^ 2 Λ)`
(`TauCeti.exists_abs_iteratedDeriv_two_logCutoffProfile_le`): the factors `√(ρ p)` and `ρ p` on
the left cancel the powers of `r = ρ p` in these bounds. At points with `ρ p = 0` the left sides
vanish.

These are the bounds on the cutoff `1 - ψ ∘ ρ` with which Cieliebak and Eliashberg interpolate
between two strictly plurisubharmonic functions near a totally real submanifold in the proof of
Proposition 3.26 of [CieliebakEliashberg2012], `ρ` being comparable to the squared distance to
the submanifold. They make the error terms of the interpolation of order `1 / Λ`.

## Main results

* `TauCeti.sqrt_mul_norm_fderiv_logCutoffProfile_comp_le`: the first-order bound.
* `TauCeti.exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le`: the second-order bound.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Real

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ε δ A : ℝ} {ρ : F → ℝ} {p : F}

/-- **The first derivative of a logarithmic cutoff composed with a function.** For
`0 < 4ε ≤ δ`, a function `ρ` differentiable at `p` with `0 ≤ ρ p`, and `0 ≤ A` with
`‖Dρ(p)‖ ≤ A √(ρ p)`, the derivative of `logCutoffProfile ε δ ∘ ρ` at `p` satisfies
`√(ρ p) ‖D(logCutoffProfile ε δ ∘ ρ)(p)‖ ≤ logCutoffConst * A / log (δ / ε)`. -/
theorem sqrt_mul_norm_fderiv_logCutoffProfile_comp_le (hε : 0 < ε) (h4 : 4 * ε ≤ δ)
    (hρ : DifferentiableAt ℝ ρ p) (hρ0 : 0 ≤ ρ p) (hA0 : 0 ≤ A)
    (hA : ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p)) :
    √(ρ p) * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖ ≤
      logCutoffConst * A / Real.log (δ / ε) := by
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hg : DifferentiableAt ℝ (logCutoffProfile ε δ) (ρ p) :=
    ((contDiff_logCutoffProfile (by linarith)).differentiable (by simp)) _
  have h1 : ‖deriv (logCutoffProfile ε δ) (ρ p)‖ ≤
      logCutoffConst / (ρ p * Real.log (δ / ε)) := by
    rw [Real.norm_of_nonneg (deriv_logCutoffProfile_nonneg hε (by linarith) _)]
    exact deriv_logCutoffProfile_le hε h4 hρ0
  rcases hρ0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.sqrt_zero, zero_mul]
    exact div_nonneg (mul_nonneg logCutoffConst_pos.le hA0) hΛ.le
  calc √(ρ p) * ‖fderiv ℝ (logCutoffProfile ε δ ∘ ρ) p‖
      ≤ √(ρ p) * (logCutoffConst / (ρ p * Real.log (δ / ε)) * (A * √(ρ p))) := by
        gcongr
        exact (SymplecticGeometry.norm_fderiv_comp_le hg hρ).trans
          (mul_le_mul h1 hA (norm_nonneg _) ((norm_nonneg _).trans h1))
    _ = ρ p * (logCutoffConst / (ρ p * Real.log (δ / ε))) * A := by
        linear_combination (logCutoffConst / (ρ p * Real.log (δ / ε)) * A) *
          Real.mul_self_sqrt hρ0
    _ = logCutoffConst / Real.log (δ / ε) * A := by
        rw [← mul_div_assoc, mul_div_mul_left _ _ hpos.ne']
    _ = logCutoffConst * A / Real.log (δ / ε) := by ring

/-- **The second derivative of a logarithmic cutoff composed with a function.** There is an
absolute constant `c` such that, for every real normed space `F`, `0 < 4ε ≤ δ`, a function
`ρ : F → ℝ` that is `C²` at `p` with `0 ≤ ρ p`, and `0 ≤ A` with `‖Dρ(p)‖ ≤ A √(ρ p)` and
`‖D²ρ(p)‖ ≤ A`, the second derivative of `logCutoffProfile ε δ ∘ ρ` at `p` satisfies
`ρ p ‖D²(logCutoffProfile ε δ ∘ ρ)(p)‖ ≤ c (A + A ^ 2) / log (δ / ε)`. -/
theorem exists_mul_norm_fderiv_fderiv_logCutoffProfile_comp_le :
    ∃ c : ℝ, ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ε δ A : ℝ} {ρ : F → ℝ}
      {p : F}, 0 < ε → 4 * ε ≤ δ → ContDiffAt ℝ 2 ρ p → 0 ≤ ρ p → 0 ≤ A →
      ‖fderiv ℝ ρ p‖ ≤ A * √(ρ p) → ‖fderiv ℝ (fderiv ℝ ρ) p‖ ≤ A →
      ρ p * ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖ ≤
        c * (A + A ^ 2) / Real.log (δ / ε) := by
  obtain ⟨c₁, hc₁⟩ := exists_abs_iteratedDeriv_two_logCutoffProfile_le
  refine ⟨logCutoffConst + |c₁|, fun {F} _ _ {ε δ A ρ p} hε h4 hρ hρ0 hA0 hA hA' ↦ ?_⟩
  have hΛ : 0 < Real.log (δ / ε) := Real.log_pos ((one_lt_div hε).2 (by linarith))
  have hg : ContDiffAt ℝ 2 (logCutoffProfile ε δ) (ρ p) :=
    (contDiff_logCutoffProfile (by linarith)).contDiffAt.of_le (by simp)
  have h1 : ‖deriv (logCutoffProfile ε δ) (ρ p)‖ ≤
      logCutoffConst / (ρ p * Real.log (δ / ε)) := by
    rw [Real.norm_of_nonneg (deriv_logCutoffProfile_nonneg hε (by linarith) _)]
    exact deriv_logCutoffProfile_le hε h4 hρ0
  have h2 : ‖iteratedDeriv 2 (logCutoffProfile ε δ) (ρ p)‖ ≤
      |c₁| / (ρ p ^ 2 * Real.log (δ / ε)) := by
    rw [Real.norm_eq_abs]
    exact (hc₁ hε h4 _).trans (by gcongr; exact le_abs_self _)
  have hD : ‖fderiv ℝ ρ p‖ ^ 2 ≤ A ^ 2 * ρ p := by
    rw [← Real.sq_sqrt hρ0, ← mul_pow]
    gcongr
  rcases hρ0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    exact div_nonneg (mul_nonneg (add_nonneg logCutoffConst_pos.le (abs_nonneg c₁))
      (add_nonneg hA0 (sq_nonneg A))) hΛ.le
  calc ρ p * ‖fderiv ℝ (fderiv ℝ (logCutoffProfile ε δ ∘ ρ)) p‖
      ≤ ρ p * (|c₁| / (ρ p ^ 2 * Real.log (δ / ε)) * (A ^ 2 * ρ p) +
          logCutoffConst / (ρ p * Real.log (δ / ε)) * A) := by
        gcongr
        refine (SymplecticGeometry.norm_fderiv_fderiv_comp_le hg hρ).trans ?_
        gcongr
        exact (norm_nonneg _).trans h1
    _ = ρ p ^ 2 * (|c₁| / (ρ p ^ 2 * Real.log (δ / ε))) * A ^ 2 +
          ρ p * (logCutoffConst / (ρ p * Real.log (δ / ε))) * A := by ring
    _ = |c₁| / Real.log (δ / ε) * A ^ 2 + logCutoffConst / Real.log (δ / ε) * A := by
        rw [← mul_div_assoc, ← mul_div_assoc, mul_div_mul_left _ _ (pow_pos hpos 2).ne',
          mul_div_mul_left _ _ hpos.ne']
    _ ≤ (logCutoffConst + |c₁|) * (A + A ^ 2) / Real.log (δ / ε) := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
        gcongr
        nlinarith [logCutoffConst_pos, abs_nonneg c₁, sq_nonneg A]

end TauCeti

end
