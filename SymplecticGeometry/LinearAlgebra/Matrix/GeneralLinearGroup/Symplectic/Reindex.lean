/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Reindex

/-!
# Reindexing the symplectic group

An equivalence `e : ι ≃ κ` of index types identifies `Sp(2n, R) = TauCeti.GLSymplectic ι R` with
`TauCeti.GLSymplectic κ R`: reindexing the rows and columns of a matrix of size `ι ⊕ ι` along
`e ⊕ e` carries the standard skew-symmetric matrix `Matrix.J ι R` to `Matrix.J κ R`
(`Matrix.reindex_sumCongr_J`), so it keeps symplectic matrices symplectic. This is the case
`e ⊕ e` of Tau Ceti's `Matrix.mul_reindex_J_mul_transpose_eq_iff`, which describes the matrices
that preserve `Matrix.J` reindexed along any equivalence `ι ⊕ ι ≃ p`. The isomorphism is the
restriction of Mathlib's `Matrix.GeneralLinearGroup.reindex R (e.sumCongr e)`.

It is used to read the direct sum of symplectic matrices of sizes `Fin n ⊕ Fin n` and
`Fin m ⊕ Fin m`, which Tau Ceti's `TauCeti.GLSymplectic.sum` indexes by `Fin n ⊕ Fin m`, in
`Sp(2(n + m))` indexed by `Fin (n + m)`.

## Main definitions and results

* `Matrix.reindex_mem_symplecticGroup`: reindexing along `e ⊕ e` keeps a matrix symplectic.
* `TauCeti.GLSymplectic.reindex`: the isomorphism `GLSymplectic ι R ≃* GLSymplectic κ R`, with
  `coe_reindex`, `symm_reindex`, `reindex_trans_reindex` and `reindex_refl`.
* `TauCeti.GLSymplectic.reindex_sum`: reindexing commutes with direct sums.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.2 (the direct-sum axiom of Theorem 2.2.12, which needs this identification).
-/

public section

open Matrix

namespace Matrix

variable {l l' R : Type*} [Fintype l] [DecidableEq l] [Fintype l'] [DecidableEq l'] [CommRing R]

/-- Reindexing the rows and columns of a symplectic matrix of size `l ⊕ l` along `e ⊕ e`, for an
equivalence `e : l ≃ l'`, gives a symplectic matrix of size `l' ⊕ l'`. -/
theorem reindex_mem_symplecticGroup (e : l ≃ l') {A : Matrix (l ⊕ l) (l ⊕ l) R}
    (hA : A ∈ symplecticGroup l R) :
    reindex (e.sumCongr e) (e.sumCongr e) A ∈ symplecticGroup l' R := by
  rwa [SymplecticGroup.mem_iff, ← reindex_sumCongr_J R e, mul_reindex_J_mul_transpose_eq_iff,
    ← reindex_symm, Equiv.symm_apply_apply]

end Matrix

namespace TauCeti.GLSymplectic

variable {ι κ ο R : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ο] [DecidableEq ο] [CommRing R]

/-- Reindexing an invertible matrix of size `ι ⊕ ι` along `e ⊕ e` keeps it symplectic. -/
theorem reindex_mem (e : ι ≃ κ) {A : GL (ι ⊕ ι) R} (hA : A ∈ GLSymplectic ι R) :
    Matrix.GeneralLinearGroup.reindex R (e.sumCongr e) A ∈ GLSymplectic κ R :=
  mem_iff_mem_symplecticGroup.2 (reindex_mem_symplecticGroup e (mem_iff_mem_symplecticGroup.1 hA))

variable (R) in
/-- The isomorphism `Sp(2n, R) ≃* Sp(2n, R)` of symplectic groups indexed by `ι ⊕ ι` and by
`κ ⊕ κ` induced by an equivalence `e : ι ≃ κ`: rows and columns are reindexed along `e ⊕ e`, as in
`Matrix.GeneralLinearGroup.reindex R (e.sumCongr e)`. -/
def reindex (e : ι ≃ κ) : GLSymplectic ι R ≃* GLSymplectic κ R where
  toFun A := ⟨Matrix.GeneralLinearGroup.reindex R (e.sumCongr e) A, reindex_mem e A.property⟩
  invFun A := ⟨Matrix.GeneralLinearGroup.reindex R (e.symm.sumCongr e.symm) A,
    reindex_mem e.symm A.property⟩
  left_inv A := Subtype.ext (Units.ext (by ext; simp))
  right_inv A := Subtype.ext (Units.ext (by ext; simp))
  map_mul' A B := Subtype.ext (by simp)

/-- The reindexed symplectic matrix, as an invertible matrix, is the reindexed invertible
matrix. -/
theorem coe_reindex (e : ι ≃ κ) (A : GLSymplectic ι R) :
    (reindex R e A : GL (κ ⊕ κ) R) = Matrix.GeneralLinearGroup.reindex R (e.sumCongr e) A :=
  (rfl)

/-- The underlying matrix of a reindexed symplectic matrix is the reindexed matrix. -/
@[simp]
theorem coe_coe_reindex (e : ι ≃ κ) (A : GLSymplectic ι R) :
    ((reindex R e A : GL (κ ⊕ κ) R) : Matrix (κ ⊕ κ) (κ ⊕ κ) R) =
      Matrix.reindex (e.sumCongr e) (e.sumCongr e) ((A : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) _ R) :=
  (rfl)

@[simp]
theorem symm_reindex (e : ι ≃ κ) : (reindex R e).symm = reindex R e.symm :=
  (rfl)

@[simp]
theorem reindex_trans_reindex (e : ι ≃ κ) (e' : κ ≃ ο) :
    (reindex R e).trans (reindex R e') = reindex R (e.trans e') :=
  MulEquiv.ext fun _ ↦ Subtype.ext (Units.ext (by ext; simp))

@[simp]
theorem reindex_refl : reindex R (.refl ι) = .refl _ :=
  MulEquiv.ext fun _ ↦ Subtype.ext (Units.ext (by ext; simp))

/-- Reindexing commutes with the direct sum of symplectic matrices: reindexing `A ⊕ B` along
`e ⊕ e'` is the direct sum of `A` reindexed along `e` and `B` reindexed along `e'`. -/
theorem reindex_sum {ι' κ' : Type*} [Fintype ι'] [DecidableEq ι'] [Fintype κ'] [DecidableEq κ']
    (e : ι ≃ κ) (e' : ι' ≃ κ') (A : GLSymplectic ι R) (B : GLSymplectic ι' R) :
    reindex R (e.sumCongr e') (sum (A, B)) = sum (reindex R e A, reindex R e' B) := by
  refine Subtype.ext (Units.ext ?_)
  ext ((i | i) | (i | i)) ((j | j) | (j | j)) <;> simp [symplecticSum_def, Equiv.sumSumSumComm]

end TauCeti.GLSymplectic

end
