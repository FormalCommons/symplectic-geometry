/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Real-linear functionals on `ℂ`

Every continuous real-linear functional `ℓ : ℂ →L[ℝ] ℝ` is `t ↦ Re (c * t)` for a complex number
`c`, namely `c = ℓ 1 - ℓ I * I`: both sides are real-linear in `t` and agree at `1` and `I`.

## Main results

* `ContinuousLinearMap.exists_apply_eq_re_mul`: every `ℓ : ℂ →L[ℝ] ℝ` is `t ↦ (c * t).re` for
  some `c : ℂ`.
-/

public section

namespace ContinuousLinearMap

/-- Every continuous real-linear functional on `ℂ` is `t ↦ Re (c * t)` for some `c : ℂ`. -/
theorem exists_apply_eq_re_mul (ℓ : ℂ →L[ℝ] ℝ) : ∃ c : ℂ, ∀ t, ℓ t = (c * t).re := by
  refine ⟨ℓ 1 - ℓ Complex.I * Complex.I, fun t ↦ ?_⟩
  have ht : t = t.re • (1 : ℂ) + t.im • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
  rw [ht, map_add, map_smul, map_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, Complex.one_re, Complex.one_im]
  ring

end ContinuousLinearMap

end
