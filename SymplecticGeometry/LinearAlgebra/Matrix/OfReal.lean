/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Real matrices read as complex matrices

A real matrix `P` is read as a complex matrix through the entrywise coercion
`P.map ((↑) : ℝ → ℂ)`. This file records how that coercion interacts with transposes and
conjugate transposes. It complements Tau Ceti's file of the same name
(`TauCeti.LinearAlgebra.Matrix.OfReal`).

## Main results

* `Matrix.map_ofReal_mul`: the coercion is multiplicative. This is Mathlib's `Matrix.map_mul` for
  `f := Complex.ofRealHom`, but stated with `ofReal` itself, so that `rw` and `simp` find it.
* `Matrix.transpose_map_ofReal_mul_map_ofReal`: `(P.map ofReal)ᵀ * Q.map ofReal` is the image of
  the real product `Pᵀ * Q`.
* `Matrix.conjTranspose_map_ofReal`: the conjugate transpose of a real matrix, read over `ℂ`, is
  its transpose.
-/

public section

open Complex

namespace Matrix

variable {m n p : Type*}

/-- The product of real matrices may be computed over `ℂ`. -/
theorem map_ofReal_mul [Fintype n] (P : Matrix m n ℝ) (Q : Matrix n p ℝ) :
    (P * Q).map ofReal = P.map ofReal * Q.map ofReal :=
  Matrix.map_mul (f := ofRealHom)

/-- The product `Pᵀ Q` of real matrices may be computed over `ℂ`. -/
theorem transpose_map_ofReal_mul_map_ofReal [Fintype m] (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    (P.map ofReal)ᵀ * Q.map ofReal = (Pᵀ * Q).map ofReal := by
  rw [← transpose_map, map_ofReal_mul]

/-- A real matrix, read over `ℂ`, has its transpose as conjugate transpose. -/
theorem conjTranspose_map_ofReal (P : Matrix m n ℝ) : (P.map ofReal)ᴴ = (P.map ofReal)ᵀ := by
  ext i j
  simp

end Matrix

end
