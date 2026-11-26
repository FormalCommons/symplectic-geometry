/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective

/-!
# Unit scalars as multiples of the identity

Tau Ceti's `Matrix.UnitaryGroup.coe_scalarHom` writes the unit scalar of `c ∈ unitary R` as the
scalar matrix `scalar n c`, which `simp` unfolds to a diagonal matrix. This file gives the form
`(c : R) • 1` instead (`Matrix.UnitaryGroup.coe_scalarHom_eq_smul_one`), which is the one to use
when the identity matrix is to be kept, for instance before applying a lemma about `a • 1`.
-/

public section

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] [StarRing R]

/-- The unit scalar of `c ∈ unitary R` is the matrix `c • 1`. -/
theorem coe_scalarHom_eq_smul_one (c : unitary R) :
    (scalarHom n R c : Matrix n n R) = (c : R) • 1 := by
  rw [coe_scalarHom, scalar_apply, smul_one_eq_diagonal]

end Matrix.UnitaryGroup

end
