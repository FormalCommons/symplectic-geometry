/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.SymplecticGroup
public import SymplecticGeometry.Algebra.Polynomial.Reverse
import TauCeti.Algebra.Polynomial.Reverse
import TauCeti.LinearAlgebra.Eigenspace.Pairing
import TauCeti.LinearAlgebra.Matrix.Charpoly.Symplectic

/-!
# The spectrum of a symplectic matrix

Let `A ∈ Sp(2n, K)` be a symplectic matrix over a field `K` (a domain suffices for the parity
and orthogonality statements), so that `A J Aᵀ = J` for
`J = Matrix.J l K`. Its characteristic polynomial `χ` is self-reciprocal,
`X ^ (2n) χ (1 / X) = χ (X)` (Tau Ceti's `SymplecticGroup.reflect_charpolyRev` and
`SymplecticGroup.charpolyRev_eq_charpoly`). This file draws the consequences for the eigenvalues
of `A`, with multiplicity meaning multiplicity as a root of `χ` (algebraic multiplicity).

* `SymplecticGroup.reflect_charpoly`: the characteristic polynomial `χ` of `A` satisfies
  `χ.reflect (2n) = χ`;
* `SymplecticGroup.rootMultiplicity_inv_charpoly`: `μ⁻¹` and `μ` have the same multiplicity;
* `SymplecticGroup.inv_mem_spectrum_iff`: so `μ⁻¹` is an eigenvalue if and only if `μ` is;
* `SymplecticGroup.even_rootMultiplicity_one_charpoly`,
  `SymplecticGroup.even_rootMultiplicity_neg_one_charpoly`: if the characteristic of `K` is not
  `2`, the eigenvalues `1` and `-1` have even multiplicity;
* `SymplecticGroup.toLinearMap₂'_J_eq_zero_of_mem_genEigenspace`: generalized eigenvectors of `A`
  for eigenvalues `μ`, `ν` with `μ ν ≠ 1` are orthogonal for the bilinear form `vᵀ J w`.
  Since `Aᵀ J A = J`, this is Tau Ceti's
  `LinearMap.apply_eq_zero_of_mem_maxGenEigenspace_of_compl₁₂_eq_smul` with multiplier `1`.

Finally `SymplecticGroup.spectrum_map_complex` collects these statements for a real symplectic
matrix `Ψ`, whose eigenvalues are those of `Ψ` viewed as a complex matrix, and the complex
bilinear extension `-(zᵀ J z')` of `ω₀` (see `SymplecticGeometry.stdForm_toBilinForm` for the
sign).

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Lemma 2.2.2 and Exercise 2.2.7.
-/

public section

open Matrix Polynomial

namespace SymplecticGroup

variable {l K : Type*} [Fintype l] [DecidableEq l]

section Domain

variable [CommRing K]

/-- The characteristic polynomial of a symplectic matrix is self-reciprocal at its degree
`2 n`. -/
theorem reflect_charpoly {A : Matrix (l ⊕ l) (l ⊕ l) K} (hA : A ∈ symplecticGroup l K) :
    A.charpoly.reflect (2 * Fintype.card l) = A.charpoly := by
  rw [← charpolyRev_eq_charpoly hA]
  exact reflect_charpolyRev hA

variable [IsDomain K]

private theorem natDegree_charpoly_le (A : Matrix (l ⊕ l) (l ⊕ l) K) :
    A.charpoly.natDegree ≤ 2 * Fintype.card l := by
  rw [charpoly_natDegree_eq_dim, Fintype.card_sum, two_mul]

/-- Over a domain whose characteristic is not `2`, the eigenvalue `1` of a symplectic matrix has
even algebraic multiplicity. -/
theorem even_rootMultiplicity_one_charpoly (hK : ringChar K ≠ 2)
    {A : Matrix (l ⊕ l) (l ⊕ l) K} (hA : A ∈ symplecticGroup l K) :
    Even (A.charpoly.rootMultiplicity 1) :=
  even_rootMultiplicity_one_of_reflect_eq hK (natDegree_charpoly_le A) (reflect_charpoly hA)

/-- Over a domain whose characteristic is not `2`, the eigenvalue `-1` of a symplectic matrix
has even algebraic multiplicity. -/
theorem even_rootMultiplicity_neg_one_charpoly (hK : ringChar K ≠ 2)
    {A : Matrix (l ⊕ l) (l ⊕ l) K} (hA : A ∈ symplecticGroup l K) :
    Even (A.charpoly.rootMultiplicity (-1)) :=
  even_rootMultiplicity_neg_one_of_reflect_eq hK (natDegree_charpoly_le A) (even_two_mul _)
    (reflect_charpoly hA)

/-- Generalized eigenvectors of a symplectic matrix `A` for eigenvalues `μ`, `ν` with `μ ν ≠ 1`
are orthogonal for the bilinear form `(v, w) ↦ vᵀ J w`. -/
theorem toLinearMap₂'_J_eq_zero_of_mem_genEigenspace {A : Matrix (l ⊕ l) (l ⊕ l) K}
    (hA : A ∈ symplecticGroup l K) {μ ν : K} (hμν : μ * ν ≠ 1) {k k' : ℕ∞} {v w : l ⊕ l → K}
    (hv : v ∈ Module.End.genEigenspace (toLin' A) μ k)
    (hw : w ∈ Module.End.genEigenspace (toLin' A) ν k') :
    toLinearMap₂' K (J l K) v w = 0 := by
  refine LinearMap.apply_eq_zero_of_mem_maxGenEigenspace_of_compl₁₂_eq_smul _ ?_ hμν
    ((Module.End.genEigenspace _ μ).monotone le_top hv)
    ((Module.End.genEigenspace _ ν).monotone le_top hw)
  rw [one_smul, Matrix.toLinearMap₂'_comp, (SymplecticGroup.mem_iff' (A := A)).1 hA]

end Domain

section Field

variable [Field K]

/-- The eigenvalues `μ` and `μ⁻¹` of a symplectic matrix have the same algebraic multiplicity.
For `μ = 0` both sides are `0`. -/
theorem rootMultiplicity_inv_charpoly {A : Matrix (l ⊕ l) (l ⊕ l) K}
    (hA : A ∈ symplecticGroup l K) (μ : K) :
    A.charpoly.rootMultiplicity μ⁻¹ = A.charpoly.rootMultiplicity μ := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · rw [_root_.inv_zero]
  conv_rhs => rw [← reflect_charpoly hA]
  exact (rootMultiplicity_reflect_eq_inv _ (natDegree_charpoly_le A) hμ).symm

/-- `μ⁻¹` is an eigenvalue of a symplectic matrix if and only if `μ` is. -/
theorem inv_mem_spectrum_iff {A : Matrix (l ⊕ l) (l ⊕ l) K} (hA : A ∈ symplecticGroup l K)
    (μ : K) : μ⁻¹ ∈ spectrum K A ↔ μ ∈ spectrum K A := by
  simp only [mem_spectrum_iff_isRoot_charpoly, ← rootMultiplicity_pos (A.charpoly_monic.ne_zero),
    rootMultiplicity_inv_charpoly hA]

end Field

/-- **The spectrum of a real symplectic matrix.** Let `Ψ ∈ Sp(2n, ℝ)` and let `Ψ_ℂ` be `Ψ`
viewed as a complex matrix, whose eigenvalues are the complex eigenvalues of `Ψ`.

* `μ` is an eigenvalue if and only if `μ⁻¹` is, and the two have the same algebraic
  multiplicity (their multiplicities as roots of the characteristic polynomial);
* the eigenvalues `1` and `-1` have even algebraic multiplicity;
* if `Ψ_ℂ z = μ z` and `Ψ_ℂ z' = ν z'` with `μ ν ≠ 1`, then `ω₀(z, z') = 0`, for the complex
  bilinear extension `ω₀(z, z') = -(zᵀ J z')` of `ω₀`.

Milestone: *Spectrum of a symplectic matrix*. -/
theorem spectrum_map_complex {Ψ : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hΨ : Ψ ∈ symplecticGroup l ℝ) :
    (∀ μ : ℂ, μ ∈ spectrum ℂ (Ψ.map Complex.ofReal) ↔
      μ⁻¹ ∈ spectrum ℂ (Ψ.map Complex.ofReal)) ∧
    (∀ μ : ℂ, (Ψ.map Complex.ofReal).charpoly.rootMultiplicity μ⁻¹ =
      (Ψ.map Complex.ofReal).charpoly.rootMultiplicity μ) ∧
    Even ((Ψ.map Complex.ofReal).charpoly.rootMultiplicity 1) ∧
    Even ((Ψ.map Complex.ofReal).charpoly.rootMultiplicity (-1)) ∧
    ∀ (μ ν : ℂ) (z z' : l ⊕ l → ℂ), Ψ.map Complex.ofReal *ᵥ z = μ • z →
      Ψ.map Complex.ofReal *ᵥ z' = ν • z' → μ * ν ≠ 1 →
      -toLinearMap₂' ℂ (J l ℂ) z z' = 0 := by
  have hΨc : (Ψ.map Complex.ofReal) ∈ symplecticGroup l ℂ :=
    map_mem hΨ Complex.ofRealHom
  have hchar : ringChar ℂ ≠ 2 := by rw [ringChar.eq_zero]; norm_num
  refine ⟨fun μ ↦ (inv_mem_spectrum_iff hΨc μ).symm, rootMultiplicity_inv_charpoly hΨc,
    even_rootMultiplicity_one_charpoly hchar hΨc, even_rootMultiplicity_neg_one_charpoly hchar hΨc,
    fun μ ν z z' hz hz' hμ ↦ ?_⟩
  rw [neg_eq_zero]
  refine toLinearMap₂'_J_eq_zero_of_mem_genEigenspace hΨc hμ (k := 1) (k' := 1) ?_ ?_
  · simp [Module.End.genEigenspace_one, hz]
  · simp [Module.End.genEigenspace_one, hz']

end SymplecticGroup

end
