/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.Matrix.Polar.Basic
public import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic
public import TauCeti.Analysis.Matrix.Polar.Symplectic

/-!
# The right polar decomposition of a symplectic matrix

Over `𝕜 = ℝ` or `ℂ`, an invertible matrix `A` factors uniquely as `A = U Q` with `U` unitary and
`Q = √(Aᴴ A)` positive definite (`Matrix.GeneralLinearGroup.existsUnique_unitary_mul_posDef`);
the unitary factor `U` is the same as in the left decomposition `A = √(A Aᴴ) U`. Tau Ceti shows
that for a symplectic `A` both factors of the left decomposition are symplectic. This file adds
the right positive factor: `Aᴴ` is symplectic with `A` (`SymplecticGroup.star_mem`), so
`√(Aᴴ A)`, the left positive factor of `Aᴴ`, is symplectic too. Over `ℝ`, where `Aᴴ = Aᵀ`, this
is the factorization `Ψ = U (ΨᵀΨ)^{1/2}` of a real symplectic matrix with `U` orthogonal and
symplectic, that is, in the realified unitary group.

## Main results

* `SymplecticGroup.sqrt_star_mul_mem`: the right positive factor `√(Aᴴ A)` of a symplectic matrix
  is symplectic.
* `SymplecticGroup.existsUnique_unitary_mul_posDef`: a symplectic matrix is uniquely a product
  `U Q` of a unitary symplectic matrix `U` and a positive definite symplectic matrix `Q`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2, Remark 2.2.5.
-/

public section

open scoped MatrixOrder ComplexOrder

open Matrix

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {𝕜 : Type*} [RCLike 𝕜]

/-- **The right positive polar factor of a symplectic matrix is symplectic.** If `A` is symplectic
over `ℝ` or `ℂ`, then so is `√(Aᴴ A)`. -/
theorem sqrt_star_mul_mem {A : Matrix (l ⊕ l) (l ⊕ l) 𝕜} (hA : A ∈ symplecticGroup l 𝕜) :
    CFC.sqrt (star A * A) ∈ symplecticGroup l 𝕜 := by
  simpa using sqrt_mul_star_mem (star_mem hA)

/-- **The right polar decomposition of a symplectic matrix.** Over `ℝ` or `ℂ`, a symplectic
matrix `A` is uniquely a product `A = U Q` of a unitary symplectic matrix `U` and a positive
definite symplectic matrix `Q`. The factors are `U = Units.polarUnitary A` and `Q = √(Aᴴ A)`;
over `ℝ`, `U` is orthogonal and `Q = (AᵀA)^{1/2}`. -/
theorem existsUnique_unitary_mul_posDef {A : Matrix (l ⊕ l) (l ⊕ l) 𝕜}
    (hA : A ∈ symplecticGroup l 𝕜) :
    ∃! UQ : unitaryGroup (l ⊕ l) 𝕜 × Matrix (l ⊕ l) (l ⊕ l) 𝕜,
      (UQ.1 : Matrix (l ⊕ l) (l ⊕ l) 𝕜) ∈ symplecticGroup l 𝕜 ∧ UQ.2.PosDef ∧
        UQ.2 ∈ symplecticGroup l 𝕜 ∧ UQ.1 * UQ.2 = A := by
  obtain ⟨A, rfl⟩ := (isUnit_iff_isUnit_det A).2 (symplectic_det hA)
  have hu := GeneralLinearGroup.existsUnique_unitary_mul_posDef A
  refine ⟨(Units.polarUnitary A, CFC.sqrt (star (A : Matrix (l ⊕ l) (l ⊕ l) 𝕜) * A)),
    ⟨polarUnitary_mem hA, GeneralLinearGroup.posDef_sqrt_star_mul A, sqrt_star_mul_mem hA,
      Units.polarUnitary_mul_sqrt_star_mul A⟩, ?_⟩
  rintro UQ ⟨-, hQ, -, h⟩
  exact hu.unique ⟨hQ, h⟩
    ⟨GeneralLinearGroup.posDef_sqrt_star_mul A, Units.polarUnitary_mul_sqrt_star_mul A⟩

end SymplecticGroup

end
