/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Data.Matrix.Basis
public import TauCeti.LinearAlgebra.Matrix.Diagonal

/-!
# Perturbing the identity matrix at one diagonal entry

For the matrix unit `Eᵢᵢ = Matrix.single i i a` of Mathlib's `Mathlib/Data/Matrix/Basis.lean`,
the matrix `1 + Eᵢᵢ a` is diagonal, with `1 + a` at the place `i` and `1` elsewhere.

## Main results

* `Matrix.one_add_single_eq_diagonal`: `1 + Eᵢᵢ a = diag(1, …, 1 + a, …, 1)`.
* `Matrix.isUnit_one_add_single_iff`: `1 + Eᵢᵢ a` is invertible exactly when `1 + a` is.
-/

public section

namespace Matrix

variable {ι R : Type*} [DecidableEq ι]

/-- `1 + Eᵢᵢ a` is the diagonal matrix `diag(1, …, 1 + a, …, 1)`. -/
theorem one_add_single_eq_diagonal [Semiring R] (i : ι) (a : R) :
    1 + single i i a = diagonal (Function.update 1 i (1 + a)) := by
  rw [← diagonal_single, ← diagonal_one', diagonal_add]
  congr 1
  ext j
  by_cases hj : j = i <;> simp [hj]

/-- `1 + Eᵢᵢ a` is invertible exactly when `1 + a` is. -/
theorem isUnit_one_add_single_iff [Fintype ι] [Semiring R] (i : ι) (a : R) :
    IsUnit (1 + single i i a) ↔ IsUnit (1 + a) := by
  rw [one_add_single_eq_diagonal, TauCeti.isUnit_diagonal_iff, Pi.isUnit_iff]
  refine ⟨fun h ↦ by simpa using h i, fun h j ↦ ?_⟩
  by_cases hj : j = i <;> simp [hj, h]

end Matrix

end
