/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Orthogonal.Unitary
public import TauCeti.LinearAlgebra.Matrix.OfReal
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Unitary
import SymplecticGeometry.LinearAlgebra.Matrix.OrthogonalGroup.Unitary

/-!
# The real points of the unitary group

The orthogonal group `O(n)` sits inside the unitary group `U(n)` as the unitary matrices with
real entries. Tau Ceti describes this group inside `GL ι ℂ`
(`TauCeti.GLOrthogonal.inf_unitarySubgroup_eq_map_real`: the unitary elements of `O(n, ℂ)` are the
real orthogonal matrices). This file carries it over to a subgroup of `Matrix.unitaryGroup ι ℂ`,
through Mathlib's `unitarySubgroupUnitsEquiv`.

## Main definitions

* `Matrix.UnitaryGroup.realSubgroup ι`: the subgroup of `unitaryGroup ι ℂ` of the unitary
  matrices `U` with `Uᵀ U = 1`.

## Main results

* `Matrix.UnitaryGroup.mem_realSubgroup_iff_transpose_mul_self_eq_one`: `U` lies in it iff
  `Uᵀ U = 1`.
* `Matrix.UnitaryGroup.mem_realSubgroup_iff_exists`: `U` lies in it iff `U` is the complex image
  of a real orthogonal matrix.
* `Matrix.UnitaryGroup.mem_realSubgroup_iff`: `U` lies in it iff its entries are real.
* `Matrix.UnitaryGroup.realSubgroup_eq_range`: it is the range of Tau Ceti's embedding
  `TauCeti.orthogonalComplexMatrix`.
* `Matrix.UnitaryGroup.orthogonalComplexMatrix_mem_realSubgroup`: the image of a real
  orthogonal matrix under `TauCeti.orthogonalComplexMatrix` lies in it.
* `Matrix.UnitaryGroup.isClosed_realSubgroup`: it is closed.
* `Matrix.UnitaryGroup.map_re_conjTranspose_mul_self`: `Re (Uᴴ U) = 1` for a unitary `U`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

open Matrix

namespace Matrix.UnitaryGroup

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The real points of the unitary group: the orthogonal group `O(n)` as a subgroup of
`unitaryGroup ι ℂ`, namely the image of the unitary elements of Tau Ceti's complex orthogonal
group `GLOrthogonal ι ℂ` under `unitarySubgroupUnitsEquiv`. -/
def realSubgroup : Subgroup (unitaryGroup ι ℂ) :=
  ((TauCeti.GLOrthogonal ι ℂ).subgroupOf (unitarySubgroup (GL ι ℂ))).map
    (unitarySubgroupUnitsEquiv (M := Matrix ι ι ℂ)).toMonoidHom

theorem realSubgroup_def : realSubgroup ι =
    ((TauCeti.GLOrthogonal ι ℂ).subgroupOf (unitarySubgroup (GL ι ℂ))).map
      (unitarySubgroupUnitsEquiv (M := Matrix ι ι ℂ)).toMonoidHom :=
  (rfl)

variable {ι}

/-- A unitary matrix is a real point of the unitary group iff it is complex orthogonal,
`Uᵀ U = 1`. -/
theorem mem_realSubgroup_iff_transpose_mul_self_eq_one {U : unitaryGroup ι ℂ} :
    U ∈ realSubgroup ι ↔ (U : Matrix ι ι ℂ)ᵀ * U = 1 := by
  rw [realSubgroup_def, Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf,
    TauCeti.GLOrthogonal.mem_iff, val_unitarySubgroupUnitsEquiv_symm_apply_coe]

/-- A unitary matrix is a real point of the unitary group iff it is the complex image of a real
orthogonal matrix. -/
theorem mem_realSubgroup_iff_exists {U : unitaryGroup ι ℂ} :
    U ∈ realSubgroup ι ↔
      ∃ O ∈ orthogonalGroup ι ℝ, O.map ((↑) : ℝ → ℂ) = (U : Matrix ι ι ℂ) := by
  constructor
  · intro hU
    have hU' : (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᵀ = 1 :=
      mul_eq_one_comm.mp (mem_realSubgroup_iff_transpose_mul_self_eq_one.mp hU)
    simpa using exists_mem_orthogonalGroup_map_eq_of_mul_transpose_eq_one U hU'
  · rintro ⟨O, hO, hOU⟩
    rw [mem_realSubgroup_iff_transpose_mul_self_eq_one, ← hOU]
    exact mul_eq_one_comm.mp (map_ofReal_mul_transpose_map_ofReal_eq_one hO)

/-- A unitary matrix is a real point of the unitary group iff all its entries are real. -/
theorem mem_realSubgroup_iff {U : unitaryGroup ι ℂ} :
    U ∈ realSubgroup ι ↔ (U : Matrix ι ι ℂ).map Complex.im = 0 := by
  constructor
  · intro hU
    obtain ⟨O, -, hOU⟩ := mem_realSubgroup_iff_exists.mp hU
    ext i j
    simp [← hOU]
  · intro h
    have hconj : (U : Matrix ι ι ℂ)ᴴ = (U : Matrix ι ι ℂ)ᵀ := by
      ext i j
      have hij := congr_fun₂ h j i
      simp only [map_apply] at hij
      simp [Complex.conj_eq_iff_im.mpr hij]
    rw [mem_realSubgroup_iff_transpose_mul_self_eq_one, ← hconj, ← star_eq_conjTranspose]
    exact Unitary.star_mul_self_of_mem U.prop

variable (ι) in
/-- The real points of the unitary group are the range of Tau Ceti's embedding
`TauCeti.orthogonalComplexMatrix : O(n) →* U(n)`. -/
theorem realSubgroup_eq_range :
    realSubgroup ι = (TauCeti.orthogonalComplexMatrix (n := ι)).range := by
  ext U
  rw [mem_realSubgroup_iff_exists, MonoidHom.mem_range]
  constructor
  · rintro ⟨O, hO, hOU⟩
    exact ⟨⟨O, hO⟩, Subtype.ext <| by rw [TauCeti.coe_orthogonalComplexMatrix, ← hOU]⟩
  · rintro ⟨O, rfl⟩
    exact ⟨O, O.property, (TauCeti.coe_orthogonalComplexMatrix O).symm⟩

/-- The complex image `TauCeti.orthogonalComplexMatrix O` of a real orthogonal matrix `O` is a
real point of the unitary group. -/
theorem orthogonalComplexMatrix_mem_realSubgroup (O : orthogonalGroup ι ℝ) :
    TauCeti.orthogonalComplexMatrix O ∈ realSubgroup ι :=
  realSubgroup_eq_range ι ▸ ⟨O, rfl⟩

variable (ι) in
/-- The real points of the unitary group form a closed subset. -/
theorem isClosed_realSubgroup : IsClosed (realSubgroup ι : Set (unitaryGroup ι ℂ)) := by
  have : (realSubgroup ι : Set (unitaryGroup ι ℂ)) =
      {U : unitaryGroup ι ℂ | (U : Matrix ι ι ℂ).map Complex.im = 0} := by
    ext U
    exact mem_realSubgroup_iff
  rw [this]
  exact isClosed_eq (continuous_subtypeVal.matrix_map Complex.continuous_im) continuous_const

/-- The real part `Re (Uᴴ U)` of the Gram matrix of a unitary matrix is the identity. -/
theorem map_re_conjTranspose_mul_self (U : unitaryGroup ι ℂ) :
    ((U : Matrix ι ι ℂ)ᴴ * U).map Complex.re = 1 := by
  rw [← star_eq_conjTranspose, Unitary.star_mul_self_of_mem U.property,
    Matrix.map_one _ Complex.zero_re Complex.one_re]

end Matrix.UnitaryGroup

end
