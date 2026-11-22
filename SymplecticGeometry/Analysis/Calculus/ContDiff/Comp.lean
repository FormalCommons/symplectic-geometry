/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Smoothness of a derivative along a fixed vector

`ContDiff.fderiv_apply_const`: if `f` is `C^n` and `m + 1 ≤ n`, then the derivative of `f` along
a fixed vector `v`, `x ↦ fderiv 𝕜 f x v`, is `C^m`. Mathlib's `ContDiff.fderiv_apply` states this
for a family of maps depending smoothly on a parameter.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a `C^n` map along a fixed vector `v` is `C^m` when `m + 1 ≤ n`. -/
theorem ContDiff.fderiv_apply_const {f : E → F} {m n : WithTop ℕ∞} (hf : ContDiff 𝕜 n f)
    (hmn : m + 1 ≤ n) (v : E) : ContDiff 𝕜 m fun x ↦ fderiv 𝕜 f x v :=
  (hf.fderiv_right hmn).clm_apply contDiff_const

end
