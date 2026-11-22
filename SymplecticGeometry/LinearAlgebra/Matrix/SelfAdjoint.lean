/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import TauCeti.LinearAlgebra.BilinearForm.Symmetric

/-!
# The dimension of the space of symmetric matrices

Over a commutative ring `R` with trivial star, the self-adjoint `n × n` matrices are the
symmetric ones. They form a module of `finrank` `n (n + 1) / 2`.

## Main definitions and results

* `Matrix.symmSubmoduleEquivSelfAdjoint`: the matrix `LinearMap.BilinForm.toMatrix'` of a
  bilinear form on `ι → R`, as a linear equivalence from the symmetric bilinear forms onto the
  self-adjoint matrices.
* `Matrix.finrank_selfAdjoint`: `Module.finrank R (selfAdjoint (Matrix ι ι R)) =
  Fintype.card ι * (Fintype.card ι + 1) / 2` for a nontrivial commutative ring `R` with trivial
  star.

The count is Tau Ceti's `LinearMap.BilinForm.finrank_symmSubmodule` for the symmetric bilinear
forms on `ι → R`, carried over by `symmSubmoduleEquivSelfAdjoint`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

namespace Matrix

variable {R ι : Type*} [CommRing R] [StarRing R] [TrivialStar R] [Fintype ι]

/-- The matrix of a bilinear form on `ι → R` identifies the symmetric bilinear forms with the
self-adjoint, that is symmetric, matrices. -/
noncomputable def symmSubmoduleEquivSelfAdjoint [DecidableEq ι] :
    LinearMap.BilinForm.symmSubmodule R (ι → R) ≃ₗ[R] selfAdjoint (Matrix ι ι R) where
  toFun B := ⟨LinearMap.BilinForm.toMatrix' (B : LinearMap.BilinForm R (ι → R)),
    isHermitian_iff_isSymm.2 (LinearMap.BilinForm.isSymm_toMatrix'_iff_isSymm.2
      (LinearMap.BilinForm.mem_symmSubmodule.1 B.property))⟩
  invFun S := ⟨Matrix.toBilin' (S : Matrix ι ι R), LinearMap.BilinForm.mem_symmSubmodule.2
    (isSymm_toBilin'_iff_isSymm.2 (isHermitian_iff_isSymm.1 S.property))⟩
  map_add' B B' := Subtype.ext (map_add _ _ _)
  map_smul' c B := Subtype.ext (map_smul _ _ _)
  left_inv B := Subtype.ext (by simp)
  right_inv S := Subtype.ext (by simp)

@[simp]
theorem coe_symmSubmoduleEquivSelfAdjoint_apply [DecidableEq ι]
    (B : LinearMap.BilinForm.symmSubmodule R (ι → R)) :
    (symmSubmoduleEquivSelfAdjoint B : Matrix ι ι R) =
      LinearMap.BilinForm.toMatrix' (B : LinearMap.BilinForm R (ι → R)) :=
  (rfl)

@[simp]
theorem coe_symmSubmoduleEquivSelfAdjoint_symm_apply [DecidableEq ι]
    (S : selfAdjoint (Matrix ι ι R)) :
    (symmSubmoduleEquivSelfAdjoint.symm S : LinearMap.BilinForm R (ι → R)) =
      Matrix.toBilin' (S : Matrix ι ι R) :=
  (rfl)

variable [Nontrivial R]

/-- **The dimension of the symmetric matrices.** Over a nontrivial commutative ring with trivial
star, the self-adjoint (that is, symmetric) `n × n` matrices form a module of
`finrank` `n (n + 1) / 2`. -/
theorem finrank_selfAdjoint :
    Module.finrank R (selfAdjoint (Matrix ι ι R)) =
      Fintype.card ι * (Fintype.card ι + 1) / 2 := by
  classical
  rw [← symmSubmoduleEquivSelfAdjoint.finrank_eq,
    LinearMap.BilinForm.finrank_symmSubmodule, Module.finrank_fintype_fun_eq_card]

end Matrix

end
