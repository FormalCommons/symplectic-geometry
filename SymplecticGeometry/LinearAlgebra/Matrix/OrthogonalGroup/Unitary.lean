/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Unitary

/-!
# The embedding of the orthogonal group into the unitary group

Tau Ceti's `TauCeti.orthogonalComplexMatrix : orthogonalGroup n ℝ →* unitaryGroup n ℂ` views a
real orthogonal matrix as a unitary complex matrix. Tau Ceti describes it entry by entry
(`TauCeti.orthogonalComplexMatrix_apply`); this file gives it as a whole matrix.

## Main results

* `TauCeti.coe_orthogonalComplexMatrix`: the embedding sends `O` to the complex matrix
  `O.map (↑)` with the same entries.
-/

public section

open Matrix

/-- Tau Ceti's embedding `O(n) →* U(n)` sends a real orthogonal matrix to the complex matrix with
the same entries. -/
@[simp]
theorem TauCeti.coe_orthogonalComplexMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : orthogonalGroup ι ℝ) :
    (TauCeti.orthogonalComplexMatrix g : Matrix ι ι ℂ) = (g : Matrix ι ι ℝ).map (↑) := by
  ext; simp

end
