/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.SymplecticGroup

/-!
# The symplectic group and the conjugate transpose

Over a commutative star ring `R`, the conjugate transpose `Aᴴ` of a matrix `A` is the transpose of
its entrywise conjugate. Both operations preserve the symplectic group `Sp(2n, R)` (Mathlib's
`SymplecticGroup.transpose_mem` and `SymplecticGroup.map_mem`), so `Aᴴ` is symplectic exactly
when `A` is.

## Main results

* `SymplecticGroup.star_mem`: the conjugate transpose of a symplectic matrix is symplectic.
* `SymplecticGroup.star_mem_iff`: a matrix is symplectic exactly when its conjugate transpose is.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2.
-/

public section

open Matrix

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R] [StarRing R]
  {A : Matrix (l ⊕ l) (l ⊕ l) R}

/-- The conjugate transpose `Aᴴ` of a symplectic matrix over a commutative star ring is
symplectic, being the transpose of the entrywise conjugate of `A`. -/
theorem star_mem (hA : A ∈ symplecticGroup l R) : star A ∈ symplecticGroup l R := by
  rw [star_eq_conjTranspose, conjTranspose]
  exact transpose_mem (map_mem hA (starRingEnd R))

/-- A matrix is symplectic exactly when its conjugate transpose is. -/
@[simp]
theorem star_mem_iff : star A ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun h ↦ star_star A ▸ star_mem h, star_mem⟩

end SymplecticGroup

end
