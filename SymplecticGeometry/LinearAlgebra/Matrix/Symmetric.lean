/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Symmetric complex matrices

For a symmetric complex matrix `Z`, the conjugate transpose `Zᴴ` is the entrywise conjugate of `Z`,
so the difference `Z - Zᴴ` is `2i` times the imaginary part of `Z`.

## Main results

* `Matrix.IsSymm.sub_conjTranspose`: `Z - Zᴴ = 2i Im Z` for a symmetric complex matrix `Z`.
-/

public section

open Complex

namespace Matrix

variable {n : Type*}

/-- For a symmetric complex matrix `Z`, `Z - Zᴴ = 2i Im Z`, the imaginary part `Im Z` being taken
entrywise. -/
theorem IsSymm.sub_conjTranspose {Z : Matrix n n ℂ} (hZ : Z.IsSymm) :
    Z - Zᴴ = (2 * I) • (Z.map Complex.im).map ofReal := by
  ext i j
  simp only [Matrix.sub_apply, conjTranspose_apply, Matrix.smul_apply, map_apply, smul_eq_mul,
    hZ.apply i j]
  rw [show star (Z i j) = (starRingEnd ℂ) (Z i j) from rfl, Complex.sub_conj]
  push_cast
  ring

end Matrix

end
