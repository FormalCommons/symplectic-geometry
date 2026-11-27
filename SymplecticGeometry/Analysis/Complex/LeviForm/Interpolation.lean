/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.LeviForm.Basic

import Mathlib.Analysis.Normed.Module.RCLike.Extend

/-!
# The Levi form of an interpolation between two functions

For real functions `f`, `g` and `β` on a complex normed space `V`, all of class `C²` at `p`, the
function `θ = f + β (g - f)` interpolates between `f` (where `β = 0`) and `g` (where `β = 1`).
By the sum and product rules, its Levi form at `p` is the convex combination
`(1 - β p) L f + β p L g` plus two error terms: `(g - f)(p) L β`, and the mixed term in the
differentials of `β` and `g - f`. This file bounds those errors from below, so that

`(1 - β p) Re L f(v, v) + β p Re L g(v, v)
  - (|g p - f p| ‖D²β(p)‖ + ‖Dβ(p)‖ ‖D(g - f)(p)‖) ‖v‖² ≤ Re L θ(v, v)`.

The estimate is meant for interpolating between two strictly plurisubharmonic functions along a
totally real submanifold, the setting of Proposition 3.26 of [CieliebakEliashberg2012]: with a
cutoff `β` whose derivatives are controlled, the errors are small where the 1-jets of `f` and `g`
nearly agree, and the convex combination keeps the strict positivity of `L f` and `L g`.

## Main results

* `TauCeti.le_re_leviForm_add_mul_sub_apply_self`: the lower bound above.

## References

* [K. Cieliebak and Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Complex ComplexConjugate

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {f g β : V → ℝ} {p : V}

/-- **The Levi form of an interpolation.** For `f`, `g` and `β` of class `C²` at `p`, the real
part of the Levi diagonal of `f + β (g - f)` at `p` is at least the convex combination
`(1 - β p) Re L f(v, v) + β p Re L g(v, v)`, up to the error
`(|g p - f p| ‖D²β(p)‖ + ‖Dβ(p)‖ ‖D(g - f)(p)‖) ‖v‖²`. -/
theorem le_re_leviForm_add_mul_sub_apply_self (hf : ContDiffAt ℝ 2 f p)
    (hg : ContDiffAt ℝ 2 g p) (hβ : ContDiffAt ℝ 2 β p) (v : V) :
    (1 - β p) * (leviForm f p v v).re + β p * (leviForm g p v v).re -
        (|g p - f p| * ‖fderiv ℝ (fderiv ℝ β) p‖ +
          ‖fderiv ℝ β p‖ * ‖fderiv ℝ (g - f) p‖) * ‖v‖ ^ 2 ≤
      (leviForm (f + β * (g - f)) p v v).re := by
  have hD : ContDiffAt ℝ 2 (g - f) p := hg.sub hf
  have hf' : ContDiffAt ℝ 2 (-f) p := hf.neg
  have hβD : ContDiffAt ℝ 2 (β * (g - f)) p := hβ.mul hD
  have hLD : leviForm (g - f) p = leviForm g p - leviForm f p := by
    rw [sub_eq_add_neg, leviForm_add hg hf', leviForm_neg, sub_eq_add_neg]
  set a := StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ β p) v
  set b := StrongDual.extendRCLike (𝕜 := ℂ) (fderiv ℝ (g - f) p) v
  have hθ : (leviForm (f + β * (g - f)) p v v).re =
      (1 - β p) * (leviForm f p v v).re + β p * (leviForm g p v v).re +
        (g - f) p * (leviForm β p v v).re + (conj a * b).re / 2 := by
    rw [leviForm_add hf hβD, LinearMap.add_apply, LinearMap.add_apply,
      leviForm_mul_apply hβ hD, hLD]
    simp only [LinearMap.sub_apply, add_re, mul_re, ofReal_re, ofReal_im, sub_re, conj_re,
      conj_im]
    norm_num
    ring
  have hβ₂ : |(leviForm β p v v).re| ≤ ‖fderiv ℝ (fderiv ℝ β) p‖ * ‖v‖ ^ 2 / 2 := by
    rw [leviForm_def]
    exact ContinuousLinearMap.abs_re_leviForm_toBilinForm_apply_self_le _ v
  have ha : ‖a‖ ≤ ‖fderiv ℝ β p‖ * ‖v‖ := StrongDual.norm_extendRCLike_bound _ v
  have hb : ‖b‖ ≤ ‖fderiv ℝ (g - f) p‖ * ‖v‖ := StrongDual.norm_extendRCLike_bound _ v
  have hab : |(conj a * b).re| ≤ ‖fderiv ℝ β p‖ * ‖fderiv ℝ (g - f) p‖ * ‖v‖ ^ 2 :=
    calc |(conj a * b).re| ≤ ‖conj a * b‖ := abs_re_le_norm _
      _ = ‖a‖ * ‖b‖ := by rw [norm_mul, RCLike.norm_conj]
      _ ≤ ‖fderiv ℝ β p‖ * ‖v‖ * (‖fderiv ℝ (g - f) p‖ * ‖v‖) :=
          mul_le_mul ha hb (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h₁ : -(|g p - f p| * (‖fderiv ℝ (fderiv ℝ β) p‖ * ‖v‖ ^ 2 / 2)) ≤
      (g - f) p * (leviForm β p v v).re := by
    rw [Pi.sub_apply]
    calc -(|g p - f p| * (‖fderiv ℝ (fderiv ℝ β) p‖ * ‖v‖ ^ 2 / 2))
        ≤ -(|g p - f p| * |(leviForm β p v v).re|) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hβ₂ (abs_nonneg _))
      _ = -|(g p - f p) * (leviForm β p v v).re| := by rw [abs_mul]
      _ ≤ _ := neg_abs_le _
  have h₂ : 0 ≤ |g p - f p| * ‖fderiv ℝ (fderiv ℝ β) p‖ * ‖v‖ ^ 2 := by positivity
  have h₃ : 0 ≤ ‖fderiv ℝ β p‖ * ‖fderiv ℝ (g - f) p‖ * ‖v‖ ^ 2 := by positivity
  rw [hθ]
  nlinarith [neg_abs_le (conj a * b).re]

end TauCeti

end
