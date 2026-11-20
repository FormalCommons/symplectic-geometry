/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive definite matrices with one index

For an index type with exactly one element, a matrix is positive definite exactly when its only
entry is positive.

## Main results

* `Matrix.posDef_iff_of_unique`: for `[Unique n]`, `A.PosDef ↔ 0 < A default default`.
-/

public section

namespace Matrix

variable {n R : Type*} [Unique n] [Ring R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  [NoZeroDivisors R] [Nontrivial R]

/-- A matrix indexed by a type with one element is positive definite exactly when its only
entry is positive. -/
theorem posDef_iff_of_unique {A : Matrix n n R} : A.PosDef ↔ 0 < A default default := by
  classical
  have hA : A = diagonal fun _ ↦ A default default := by
    rw [diagonal_unique]
    ext i j
    simp [Subsingleton.elim i default, Subsingleton.elim j default]
  rw [hA, posDef_diagonal_iff]
  simp

end Matrix

end
