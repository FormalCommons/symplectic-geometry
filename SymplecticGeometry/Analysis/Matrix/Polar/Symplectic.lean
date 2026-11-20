/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.Polar.Symplectic

/-!
# The right polar decomposition of a symplectic matrix

Over `𝕜 = ℝ` or `ℂ`, an invertible matrix `A` factors uniquely as `A = U Q` with `U` unitary and
`Q = √(Aᴴ A)` positive definite (Tau Ceti's `Units.polarUnitary_mul_sqrt_star_mul` and
`Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq`); the unitary factor `U` is the same as in
the left decomposition `A = √(A Aᴴ) U`. Tau Ceti shows that for a symplectic `A` both factors of
the left decomposition are symplectic. This file adds the right positive factor: `Aᴴ` is
symplectic with `A`, being the transpose of the entrywise conjugate, so `√(Aᴴ A)`, the left
positive factor of `Aᴴ`, is symplectic too. Over `ℝ`, where `Aᴴ = Aᵀ`, this is the factorization
`Ψ = U (ΨᵀΨ)^{1/2}` of a real symplectic matrix with `U` orthogonal and symplectic, that is, in
the realified unitary group.

## Main results

* `SymplecticGroup.star_mem`: the conjugate transpose of a symplectic matrix is symplectic.
* `SymplecticGroup.sqrt_star_mul_mem`: the right positive factor `√(Aᴴ A)` of a symplectic matrix
  is symplectic.
* `SymplecticGroup.existsUnique_unitary_mul_posDef`: a symplectic matrix is uniquely a product
  `U Q` of a unitary symplectic matrix `U` and a positive definite symplectic matrix `Q`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2, Proposition 2.2.4.
-/

public section

open scoped MatrixOrder ComplexOrder

open Matrix

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {𝕜 : Type*} [RCLike 𝕜]

section StarRing

variable {R : Type*} [CommRing R] [StarRing R] {A : Matrix (l ⊕ l) (l ⊕ l) R}

/-- The conjugate transpose `Aᴴ` of a symplectic matrix over a commutative star ring is
symplectic, being the transpose of the entrywise conjugate of `A`. -/
theorem star_mem (hA : A ∈ symplecticGroup l R) : star A ∈ symplecticGroup l R := by
  rw [star_eq_conjTranspose, conjTranspose]
  exact transpose_mem (map_mem hA (starRingEnd R))

/-- A matrix is symplectic exactly when its conjugate transpose is. -/
@[simp]
theorem star_mem_iff : star A ∈ symplecticGroup l R ↔ A ∈ symplecticGroup l R :=
  ⟨fun h ↦ star_star A ▸ star_mem h, star_mem⟩

end StarRing

/-- **The right positive polar factor of a symplectic matrix is symplectic.** If `A` is symplectic
over `ℝ` or `ℂ`, then so is `√(Aᴴ A)`. -/
theorem sqrt_star_mul_mem {A : Matrix (l ⊕ l) (l ⊕ l) 𝕜} (hA : A ∈ symplecticGroup l 𝕜) :
    CFC.sqrt (star A * A) ∈ symplecticGroup l 𝕜 := by
  simpa using sqrt_mul_star_mem (star_mem hA)

/-- **The right polar decomposition of a symplectic matrix.** Over `ℝ` or `ℂ`, a symplectic
matrix `A` is uniquely a product `A = U Q` of a unitary symplectic matrix `U` and a positive
definite symplectic matrix `Q`. The factors are `U = Units.polarUnitary A` and `Q = √(Aᴴ A)`;
over `ℝ`, `U` is orthogonal and `Q = (AᵀA)^{1/2}`. Uniqueness holds already among all unitary
`U` and positive definite `Q`, symplectic or not. -/
theorem existsUnique_unitary_mul_posDef {A : Matrix (l ⊕ l) (l ⊕ l) 𝕜}
    (hA : A ∈ symplecticGroup l 𝕜) :
    ∃! UQ : unitaryGroup (l ⊕ l) 𝕜 × Matrix (l ⊕ l) (l ⊕ l) 𝕜,
      (UQ.1 : Matrix (l ⊕ l) (l ⊕ l) 𝕜) ∈ symplecticGroup l 𝕜 ∧ UQ.2.PosDef ∧
        UQ.2 ∈ symplecticGroup l 𝕜 ∧ UQ.1 * UQ.2 = A := by
  obtain ⟨A, rfl⟩ := (isUnit_iff_isUnit_det A).2 (symplectic_det hA)
  refine ⟨(Units.polarUnitary A, CFC.sqrt (star (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) * A)),
    ⟨polarUnitary_mem hA, ?_, sqrt_star_mul_mem hA, Units.polarUnitary_mul_sqrt_star_mul A⟩, ?_⟩
  · exact isStrictlyPositive_iff_posDef.1 (Units.isStrictlyPositive_sqrt_star_mul A)
  · rintro ⟨U, Q⟩ ⟨-, hQ, -, h⟩
    obtain ⟨hU, hQ'⟩ :=
      (Units.mul_eq_iff_polarUnitary_eq_and_sqrt_star_mul_eq A hQ.posSemidef.nonneg).1 h
    exact Prod.ext hU.symm hQ'.symm

end SymplecticGroup

end
