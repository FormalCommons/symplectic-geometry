/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Analysis.Matrix.Normed
public import TauCeti.GroupTheory.GroupAction.Transitive
public import Mathlib.LinearAlgebra.SymplecticGroup
public import TauCeti.LinearAlgebra.Matrix.Realify
public import SymplecticGeometry.Analysis.Complex.SiegelUpperHalfSpace.Basic
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Unitary
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose
import SymplecticGeometry.LinearAlgebra.Matrix.OfReal
import SymplecticGeometry.LinearAlgebra.Matrix.PosDef.OfReal
import SymplecticGeometry.LinearAlgebra.Matrix.Symmetric
import SymplecticGeometry.Topology.Instances.Matrix

/-!
# The action of the symplectic group on the Siegel upper half space

Write a real `(ι ⊕ ι) × (ι ⊕ ι)` matrix as `Ψ = !![A, B; C, D]`, its blocks being
`Matrix.toBlocks₁₁ Ψ`, …, `Matrix.toBlocks₂₂ Ψ`. Mathlib's `Matrix.J ι ℝ` is `!![0, -1; 1, 0]`, the
matrix `J₀` of McDuff–Salamon, so these are the blocks of the book with no change of sign. For a
symplectic `Ψ` and a point `Z` of the Siegel upper half space, the matrix `CZ + D` is invertible
and `Ψ • Z = (AZ + B)(CZ + D)⁻¹` is again a point of the Siegel upper half space. This is an action
of `Matrix.symplecticGroup ι ℝ`, holomorphic in `Z` and transitive, and the stabilizer of `i𝟙` is
the realified unitary group, so that the orbit map of `i𝟙` identifies `Sp(2n)/U(n)` with the
Siegel upper half space. For `ι` with one element it is the action of `SL(2, ℝ)` on the upper half
plane by Möbius transformations.

## Main definitions

* `SiegelUpperHalfSpace.num`, `SiegelUpperHalfSpace.denom`: the matrices `AZ + B` and `CZ + D`.
* The `MulAction` of `Matrix.symplecticGroup ι ℝ` on `SiegelUpperHalfSpace ι`, with
  `SiegelUpperHalfSpace.coe_smul` its formula.

## Main results

* `SiegelUpperHalfSpace.transpose_num_mul_denom_sub` and
  `SiegelUpperHalfSpace.conjTranspose_denom_mul_num_sub`: the identities
  `(AZ + B)ᵀ(CZ + D) - (CZ + D)ᵀ(AZ + B) = Zᵀ - Z` and
  `(CZ + D)ᴴ(AZ + B) - (AZ + B)ᴴ(CZ + D) = Z - Zᴴ` for symplectic `Ψ`, from which everything else
  follows.
* `SiegelUpperHalfSpace.isUnit_denom`: `CZ + D` is invertible.
* `SiegelUpperHalfSpace.map_ofReal_im_smul`: the imaginary part of `Ψ • Z` is
  `(CZ + D)⁻ᴴ (Im Z) (CZ + D)⁻¹`.
* `SiegelUpperHalfSpace.differentiableOn_num_mul_inv_denom`: the formula is holomorphic on the
  open set (`SiegelUpperHalfSpace.isOpen_setOf_isUnit_det_denom`) where `CZ + D` is invertible,
  which contains the Siegel upper half space.
* `SiegelUpperHalfSpace.fromBlocks_re_smul_I`: every point `X + iY` is the image of `i𝟙` under
  the symplectic matrix `!![G, X G⁻ᵀ; 0, G⁻ᵀ]`, where `G` is invertible with `G Gᵀ = Y`; hence
  the action is transitive (`SiegelUpperHalfSpace.exists_smul_I_eq`).
* `SiegelUpperHalfSpace.smul_I_eq_I_iff_commute`: a symplectic matrix fixes `i𝟙` exactly when it
  commutes with `Matrix.J`.
* `SiegelUpperHalfSpace.mem_stabilizer_I_iff`: a symplectic matrix fixes `i𝟙` exactly when it is
  the realification `Matrix.realify U` of a unitary matrix `U`.
* `SiegelUpperHalfSpace.map_stabilizer_I`: the stabilizer of `i𝟙`, as a set of matrices, is the
  image of `Matrix.unitaryGroup ι ℂ` under `Matrix.realifyAlgHom`.
* `SiegelUpperHalfSpace.homeomorphUpperHalfPlane_smul`: for one index the action is that of
  `SL(2, ℝ)` on Mathlib's `UpperHalfPlane`.

## Implementation notes

The action is (2.5.19) of McDuff–Salamon, and its properties are those of their Exercise 2.5.11.
All the algebra comes from the two identities above, which use the block relations of Mathlib's
`SymplecticGroup.fromBlocks_mem_iff`. Transitivity is checked by the explicit matrix above, with
`G` from Tau Ceti's `Matrix.PosDef.exists_generalLinearGroup_mul_transpose_eq`, so that this file
does not need the complex structures of `ComplexStructure.lean`. Holomorphy is stated with the
operator norm on matrices (`Matrix.Norms.Operator`); all norms on matrices give the same
differentiable maps.

Since the action is transitive, Tau Ceti's
`TauCeti.quotientStabilizerEquiv (symplecticGroup ι ℝ) SiegelUpperHalfSpace.I` is the bijection
from the quotient of the symplectic group by the stabilizer of `i𝟙` onto the Siegel upper half
space that the orbit map induces; by `map_stabilizer_I` that stabilizer is the realified unitary
group.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.5
-/

public section

noncomputable section

open Complex Matrix
open scoped ComplexOrder MatrixGroups

namespace SymplecticGeometry

namespace SiegelUpperHalfSpace

variable {ι : Type*} [Fintype ι]

/-! ### The numerator and the denominator -/

/-- The numerator `AZ + B` of the action of `Ψ = !![A, B; C, D]` on a complex matrix `Z`. -/
def num (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Ψ.toBlocks₁₁.map ofReal * Z + Ψ.toBlocks₁₂.map ofReal

/-- The denominator `CZ + D` of the action of `Ψ = !![A, B; C, D]` on a complex matrix `Z`. -/
def denom (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Z : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  Ψ.toBlocks₂₁.map ofReal * Z + Ψ.toBlocks₂₂.map ofReal

theorem num_def (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Z : Matrix ι ι ℂ) :
    num Ψ Z = Ψ.toBlocks₁₁.map ofReal * Z + Ψ.toBlocks₁₂.map ofReal :=
  (rfl)

theorem denom_def (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Z : Matrix ι ι ℂ) :
    denom Ψ Z = Ψ.toBlocks₂₁.map ofReal * Z + Ψ.toBlocks₂₂.map ofReal :=
  (rfl)

variable [DecidableEq ι]

/-- The relations between the blocks of a symplectic matrix, read over `ℂ`. -/
private theorem blocks_relations {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hΨ : Ψ ∈ symplecticGroup ι ℝ) :
    (Ψ.toBlocks₁₁.map ofReal)ᵀ * Ψ.toBlocks₂₁.map ofReal =
        (Ψ.toBlocks₂₁.map ofReal)ᵀ * Ψ.toBlocks₁₁.map ofReal ∧
      (Ψ.toBlocks₁₂.map ofReal)ᵀ * Ψ.toBlocks₂₂.map ofReal =
        (Ψ.toBlocks₂₂.map ofReal)ᵀ * Ψ.toBlocks₁₂.map ofReal ∧
      (Ψ.toBlocks₁₁.map ofReal)ᵀ * Ψ.toBlocks₂₂.map ofReal -
        (Ψ.toBlocks₂₁.map ofReal)ᵀ * Ψ.toBlocks₁₂.map ofReal = 1 ∧
      (Ψ.toBlocks₂₂.map ofReal)ᵀ * Ψ.toBlocks₁₁.map ofReal -
        (Ψ.toBlocks₁₂.map ofReal)ᵀ * Ψ.toBlocks₂₁.map ofReal = 1 := by
  rw [← fromBlocks_toBlocks Ψ, SymplecticGroup.fromBlocks_mem_iff] at hΨ
  obtain ⟨h₁, h₂, h₃⟩ := hΨ
  have h₄ : Ψ.toBlocks₂₂ᵀ * Ψ.toBlocks₁₁ - Ψ.toBlocks₁₂ᵀ * Ψ.toBlocks₂₁ = 1 := by
    simpa [transpose_sub, transpose_mul] using congrArg transpose h₃
  simp only [transpose_map_ofReal_mul_map_ofReal, h₁, h₂, true_and]
  constructor <;>
  · rw [← Matrix.map_sub _ (by simp)]
    simp [h₃, h₄]

/-- For a symplectic `Ψ = !![A, B; C, D]` and any complex matrix `Z`,
`(AZ + B)ᵀ(CZ + D) - (CZ + D)ᵀ(AZ + B) = Zᵀ - Z`. -/
theorem transpose_num_mul_denom_sub {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hΨ : Ψ ∈ symplecticGroup ι ℝ) (Z : Matrix ι ι ℂ) :
    (num Ψ Z)ᵀ * denom Ψ Z - (denom Ψ Z)ᵀ * num Ψ Z = Zᵀ - Z := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := blocks_relations hΨ
  set A := Ψ.toBlocks₁₁.map ofReal
  set B := Ψ.toBlocks₁₂.map ofReal
  set C := Ψ.toBlocks₂₁.map ofReal
  set D := Ψ.toBlocks₂₂.map ofReal
  have : (num Ψ Z)ᵀ * denom Ψ Z - (denom Ψ Z)ᵀ * num Ψ Z =
      Zᵀ * (Aᵀ * C - Cᵀ * A) * Z + Zᵀ * (Aᵀ * D - Cᵀ * B) - (Dᵀ * A - Bᵀ * C) * Z +
        (Bᵀ * D - Dᵀ * B) := by
    simp only [num, denom, transpose_add, transpose_mul]
    noncomm_ring
  rw [this, h₁, h₂, h₃, h₄]
  simp

/-- For a symplectic `Ψ = !![A, B; C, D]` and any complex matrix `Z`,
`(CZ + D)ᴴ(AZ + B) - (AZ + B)ᴴ(CZ + D) = Z - Zᴴ`. -/
theorem conjTranspose_denom_mul_num_sub {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hΨ : Ψ ∈ symplecticGroup ι ℝ) (Z : Matrix ι ι ℂ) :
    (denom Ψ Z)ᴴ * num Ψ Z - (num Ψ Z)ᴴ * denom Ψ Z = Z - Zᴴ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := blocks_relations hΨ
  set A := Ψ.toBlocks₁₁.map ofReal
  set B := Ψ.toBlocks₁₂.map ofReal
  set C := Ψ.toBlocks₂₁.map ofReal
  set D := Ψ.toBlocks₂₂.map ofReal
  have : (denom Ψ Z)ᴴ * num Ψ Z - (num Ψ Z)ᴴ * denom Ψ Z =
      Zᴴ * (Cᵀ * A - Aᵀ * C) * Z + Zᴴ * (Cᵀ * B - Aᵀ * D) + (Dᵀ * A - Bᵀ * C) * Z +
        (Dᵀ * B - Bᵀ * D) := by
    simp only [num, denom, conjTranspose_add, conjTranspose_mul, conjTranspose_map_ofReal, A, B,
      C, D]
    noncomm_ring
  have h₃' : Cᵀ * B - Aᵀ * D = -1 := by rw [← h₃]; abel
  rw [this, h₁, h₂, h₃', h₄]
  simp [sub_eq_neg_add]

/-- The denominator `CZ + D` of a symplectic matrix is invertible at every point `Z` of the Siegel
upper half space. -/
theorem isUnit_denom {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hΨ : Ψ ∈ symplecticGroup ι ℝ)
    (Z : SiegelUpperHalfSpace ι) : IsUnit (denom Ψ Z) := by
  have hY := posDef_map_ofReal_iff.2 Z.posDef_map_im
  rw [← mulVec_injective_iff_isUnit]
  intro v w hvw
  by_contra hne
  have hu : v - w ≠ 0 := sub_ne_zero.2 hne
  have hN : denom Ψ Z *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
  have heq := conjTranspose_denom_mul_num_sub hΨ Z
  rw [Z.isSymm.sub_conjTranspose] at heq
  have key := congrArg (fun P ↦ star (v - w) ⬝ᵥ (P *ᵥ (v - w))) heq
  simp only [sub_mulVec, ← mulVec_mulVec, hN, mulVec_zero, sub_zero] at key
  rw [dotProduct_mulVec, ← star_mulVec, hN, star_zero, zero_dotProduct, smul_mulVec,
    dotProduct_smul, smul_eq_mul] at key
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  exact (hY.dotProduct_mulVec_pos hu).ne' ((mul_eq_zero.1 key.symm).resolve_left h2I)

/-- The determinant of `CZ + D` is a unit, for symplectic `Ψ` and `Z` in the Siegel upper half
space. -/
theorem isUnit_det_denom {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hΨ : Ψ ∈ symplecticGroup ι ℝ)
    (Z : SiegelUpperHalfSpace ι) : IsUnit (denom Ψ Z).det :=
  (isUnit_iff_isUnit_det _).1 (isUnit_denom hΨ Z)

/-- For symplectic `Ψ` and `Z` in the Siegel upper half space, `(AZ + B)(CZ + D)⁻¹` is
symmetric. -/
theorem isSymm_num_mul_inv_denom {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} (hΨ : Ψ ∈ symplecticGroup ι ℝ)
    (Z : SiegelUpperHalfSpace ι) : (num Ψ Z * (denom Ψ Z)⁻¹).IsSymm := by
  have hMN : (num Ψ Z)ᵀ * denom Ψ Z = (denom Ψ Z)ᵀ * num Ψ Z :=
    sub_eq_zero.1 (by rw [transpose_num_mul_denom_sub hΨ, Z.isSymm.eq, sub_self])
  exact isSymm_mul_nonsing_inv_of_transpose_mul_eq hMN

/-- For symplectic `Ψ` and `Z` in the Siegel upper half space, the imaginary part of
`(AZ + B)(CZ + D)⁻¹` is `(CZ + D)⁻ᴴ (Im Z) (CZ + D)⁻¹`. -/
theorem map_im_num_mul_inv_denom {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hΨ : Ψ ∈ symplecticGroup ι ℝ) (Z : SiegelUpperHalfSpace ι) :
    ((num Ψ Z * (denom Ψ Z)⁻¹).map Complex.im).map ofReal =
      ((denom Ψ Z)⁻¹)ᴴ * ((Z : Matrix ι ι ℂ).map Complex.im).map ofReal * (denom Ψ Z)⁻¹ := by
  have hd := isUnit_det_denom hΨ Z
  set M := num Ψ Z
  set N := denom Ψ Z
  have h2 : M * N⁻¹ - (M * N⁻¹)ᴴ = (N⁻¹)ᴴ * (Nᴴ * M - Mᴴ * N) * N⁻¹ := by
    have hNN : (N⁻¹)ᴴ * Nᴴ = 1 := by
      rw [← conjTranspose_mul, mul_nonsing_inv _ hd, conjTranspose_one]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, mul_nonsing_inv _ hd,
      Matrix.mul_one, conjTranspose_mul]
    rw [← Matrix.mul_assoc (N⁻¹)ᴴ, hNN, Matrix.one_mul]
  rw [(isSymm_num_mul_inv_denom hΨ Z).sub_conjTranspose, conjTranspose_denom_mul_num_sub hΨ,
    Z.isSymm.sub_conjTranspose, Matrix.mul_smul, Matrix.smul_mul] at h2
  exact smul_right_injective _ (by simp : (2 * I : ℂ) ≠ 0) h2

/-- For symplectic `Ψ` and `Z` in the Siegel upper half space, the imaginary part of
`(AZ + B)(CZ + D)⁻¹` is positive definite. -/
theorem posDef_map_im_num_mul_inv_denom {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hΨ : Ψ ∈ symplecticGroup ι ℝ) (Z : SiegelUpperHalfSpace ι) :
    ((num Ψ Z * (denom Ψ Z)⁻¹).map Complex.im).PosDef := by
  have hd := isUnit_det_denom hΨ Z
  rw [← posDef_map_ofReal_iff, map_im_num_mul_inv_denom hΨ Z]
  exact (posDef_map_ofReal_iff.2 Z.posDef_map_im).conjTranspose_mul_mul_same
    (mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hd)))

/-! ### The action -/

instance : SMul (symplecticGroup ι ℝ) (SiegelUpperHalfSpace ι) where
  smul Ψ Z := mk (num Ψ.val Z * (denom Ψ.val Z)⁻¹) (isSymm_num_mul_inv_denom Ψ.property Z)
    (posDef_map_im_num_mul_inv_denom Ψ.property Z)

/-- A symplectic matrix `Ψ = !![A, B; C, D]` acts on the Siegel upper half space by
`Ψ • Z = (AZ + B)(CZ + D)⁻¹`. -/
theorem coe_smul (Ψ : symplecticGroup ι ℝ) (Z : SiegelUpperHalfSpace ι) :
    ((Ψ • Z : SiegelUpperHalfSpace ι) : Matrix ι ι ℂ) = num Ψ Z * (denom Ψ Z)⁻¹ :=
  (rfl)

/-- The imaginary part of `Ψ • Z`, read as a complex matrix, is `(CZ + D)⁻ᴴ (Im Z) (CZ + D)⁻¹`.
This is the analogue of `UpperHalfPlane.im_smul_eq_div_normSq`. -/
theorem map_ofReal_im_smul (Ψ : symplecticGroup ι ℝ) (Z : SiegelUpperHalfSpace ι) :
    (Ψ • Z).im.map ofReal = ((denom Ψ Z)⁻¹)ᴴ * Z.im.map ofReal * (denom Ψ Z)⁻¹ := by
  rw [im_def, im_def, coe_smul]
  exact map_im_num_mul_inv_denom Ψ.property Z

@[simp]
theorem num_one (Z : Matrix ι ι ℂ) : num 1 Z = Z := by
  simp [num_def, ← fromBlocks_one]

@[simp]
theorem denom_one (Z : Matrix ι ι ℂ) : denom 1 Z = 1 := by
  simp [denom_def, ← fromBlocks_one]

/-- The numerator satisfies `num (Φ * Ψ) Z = num Φ W * denom Ψ Z` for
`W = num Ψ Z * (denom Ψ Z)⁻¹`, whenever `denom Ψ Z` is invertible. -/
theorem num_mul (Φ Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {Z : Matrix ι ι ℂ}
    (hZ : IsUnit (denom Ψ Z).det) :
    num (Φ * Ψ) Z = num Φ (num Ψ Z * (denom Ψ Z)⁻¹) * denom Ψ Z := by
  have h₁ := toBlocks₁₁_mul Φ Ψ
  have h₂ := toBlocks₁₂_mul Φ Ψ
  rw [num_def Φ, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hZ,
    Matrix.mul_one, num_def, num_def, denom_def, h₁, h₂]
  simp only [Matrix.map_add _ ofReal_add, map_ofReal_mul]
  noncomm_ring

/-- The denominator is a cocycle: `denom (Φ * Ψ) Z = denom Φ W * denom Ψ Z` for
`W = num Ψ Z * (denom Ψ Z)⁻¹`, whenever `denom Ψ Z` is invertible. -/
theorem denom_mul (Φ Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) {Z : Matrix ι ι ℂ}
    (hZ : IsUnit (denom Ψ Z).det) :
    denom (Φ * Ψ) Z = denom Φ (num Ψ Z * (denom Ψ Z)⁻¹) * denom Ψ Z := by
  have h₃ := toBlocks₂₁_mul Φ Ψ
  have h₄ := toBlocks₂₂_mul Φ Ψ
  rw [denom_def Φ, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hZ,
    Matrix.mul_one, denom_def, num_def, denom_def, h₃, h₄]
  simp only [Matrix.map_add _ ofReal_add, map_ofReal_mul]
  noncomm_ring

/-- The symplectic group acts on the Siegel upper half space by
`Ψ • Z = (AZ + B)(CZ + D)⁻¹`. -/
instance : MulAction (symplecticGroup ι ℝ) (SiegelUpperHalfSpace ι) where
  one_smul Z := by
    ext1
    simp [coe_smul]
  mul_smul Φ Ψ Z := by
    ext1
    have hZ := isUnit_det_denom Ψ.property Z
    rw [coe_smul, coe_smul, coe_smul, Submonoid.coe_mul, num_mul _ _ hZ, denom_mul _ _ hZ,
      ← coe_smul, Matrix.mul_inv_rev, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hZ]

/-! ### Holomorphy -/

section Holomorphy

open scoped Matrix.Norms.Operator

/-- The complex matrices `Z` at which `CZ + D` is invertible form an open set. -/
theorem isOpen_setOf_isUnit_det_denom (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    IsOpen {Z : Matrix ι ι ℂ | IsUnit (denom Ψ Z).det} :=
  ((continuous_const.matrix_mul continuous_id).add continuous_const).isOpen_setOf_isUnit_det

/-- The open set where `CZ + D` is invertible contains the Siegel upper half space, when `Ψ` is
symplectic. -/
theorem range_coe_subset_setOf_isUnit_det_denom {Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ}
    (hΨ : Ψ ∈ symplecticGroup ι ℝ) :
    Set.range ((↑) : SiegelUpperHalfSpace ι → Matrix ι ι ℂ) ⊆
      {Z : Matrix ι ι ℂ | IsUnit (denom Ψ Z).det} := by
  rintro _ ⟨Z, rfl⟩
  exact isUnit_det_denom hΨ Z

omit [DecidableEq ι] in
theorem differentiable_num (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : Differentiable ℂ (num Ψ) := by
  classical
  exact (differentiable_id.const_mul _).add_const _

omit [DecidableEq ι] in
theorem differentiable_denom (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) : Differentiable ℂ (denom Ψ) := by
  classical
  exact (differentiable_id.const_mul _).add_const _

/-- The map `Z ↦ (AZ + B)(CZ + D)⁻¹` is holomorphic on the open set where `CZ + D` is invertible,
which contains the Siegel upper half space when `Ψ` is symplectic. The norm on matrices is the
operator norm; any other norm gives the same differentiable maps. -/
theorem differentiableOn_num_mul_inv_denom (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :
    DifferentiableOn ℂ (fun Z ↦ num Ψ Z * (denom Ψ Z)⁻¹)
      {Z : Matrix ι ι ℂ | IsUnit (denom Ψ Z).det} := by
  intro Z hZ
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (differentiable_num Ψ Z).mul
    ((Matrix.hasFDerivAt_inv hZ).differentiableAt.comp Z (differentiable_denom Ψ Z))

end Holomorphy

/-! ### Transitivity -/

/-- For a point `Z = X + iY` of the Siegel upper half space and an invertible `G`, the matrix
`!![G, X G⁻ᵀ; 0, G⁻ᵀ]` is symplectic. -/
theorem fromBlocks_re_mem_symplecticGroup (Z : SiegelUpperHalfSpace ι) (G : GL ι ℝ) :
    fromBlocks (G : Matrix ι ι ℝ) (Z.re * (↑G⁻¹ : Matrix ι ι ℝ)ᵀ) 0 (↑G⁻¹ : Matrix ι ι ℝ)ᵀ ∈
      symplecticGroup ι ℝ := by
  rw [SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨by simp, ?_, by simpa using GeneralLinearGroup.coe_transpose_mul_coe_inv_transpose G⟩
  rw [transpose_mul, Z.isSymm_re.eq, Matrix.mul_assoc]

/-- A point `Z = X + iY` of the Siegel upper half space is the image of `i𝟙` under the symplectic
matrix `!![G, X G⁻ᵀ; 0, G⁻ᵀ]`, for any invertible `G` with `G Gᵀ = Y`. -/
theorem fromBlocks_re_smul_I (Z : SiegelUpperHalfSpace ι) {G : GL ι ℝ}
    (hG : (G : Matrix ι ι ℝ) * (G : Matrix ι ι ℝ)ᵀ = Z.im) :
    (⟨_, fromBlocks_re_mem_symplecticGroup Z G⟩ : symplecticGroup ι ℝ) •
      (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) = Z := by
  set D : Matrix ι ι ℝ := (↑G⁻¹ : Matrix ι ι ℝ)ᵀ
  have hDG : (G : Matrix ι ι ℝ)ᵀ * D = 1 :=
    GeneralLinearGroup.coe_transpose_mul_coe_inv_transpose G
  have hGD : D * (G : Matrix ι ι ℝ)ᵀ = 1 := mul_eq_one_comm.mp hDG
  have hinv : (D.map ofReal)⁻¹ = (G : Matrix ι ι ℝ)ᵀ.map ofReal :=
    inv_eq_left_inv (by rw [← map_ofReal_mul, hDG]; simp)
  ext1
  rw [coe_smul, coe_eq_re_add_I_smul_im Z, num_def, denom_def]
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, coe_I]
  rw [Matrix.map_zero _ (by simp), Matrix.zero_mul, zero_add, hinv, Matrix.add_mul,
    Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← map_ofReal_mul, ← map_ofReal_mul, hG,
    Matrix.mul_assoc, hGD, Matrix.mul_one, add_comm]

/-- Every point `Z = X + iY` of the Siegel upper half space is the image of `i𝟙` under a
symplectic matrix, namely `!![G, X G⁻ᵀ; 0, G⁻ᵀ]` for an invertible `G` with `G Gᵀ = Y`. -/
theorem exists_smul_I_eq (Z : SiegelUpperHalfSpace ι) :
    ∃ Ψ : symplecticGroup ι ℝ, Ψ • (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) = Z := by
  obtain ⟨G, hG⟩ := Z.posDef_im.exists_generalLinearGroup_mul_transpose_eq
  exact ⟨_, fromBlocks_re_smul_I Z hG⟩

/-- The symplectic group acts transitively on the Siegel upper half space. -/
instance : MulAction.IsPretransitive (symplecticGroup ι ℝ) (SiegelUpperHalfSpace ι) :=
  (MulAction.isPretransitive_iff_base SiegelUpperHalfSpace.I).2 exists_smul_I_eq

/-! ### The stabilizer of `i𝟙` -/

omit [Fintype ι] [DecidableEq ι] in
private theorem I_smul_map_ofReal_eq_iff (A B C D : Matrix ι ι ℝ) :
    I • A.map ofReal + B.map ofReal = I • (I • C.map ofReal + D.map ofReal) ↔
      D = A ∧ C = -B := by
  simp only [← Matrix.ext_iff, Matrix.add_apply, Matrix.smul_apply, map_apply, smul_eq_mul,
    Complex.ext_iff, add_re, add_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
    Matrix.neg_apply, ← forall_and]
  constructor
  · intro h i j
    have := h i j
    constructor <;> linarith [this.1, this.2]
  · intro h i j
    have := h i j
    constructor <;> linarith [this.1, this.2]

/-- A symplectic matrix `!![A, B; C, D]` fixes `i𝟙` exactly when `D = A` and `C = -B`. -/
theorem smul_I_eq_I_iff (Ψ : symplecticGroup ι ℝ) :
    Ψ • (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) = SiegelUpperHalfSpace.I ↔
      (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₂₂ = (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₁₁ ∧
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₂₁ =
          -(Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₁₂ := by
  have hd := isUnit_det_denom Ψ.property SiegelUpperHalfSpace.I
  rw [← coe_inj, coe_smul, coe_I, ← I_smul_map_ofReal_eq_iff]
  have hnum : num Ψ (I • 1 : Matrix ι ι ℂ) =
      I • (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₁₁.map ofReal +
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₁₂.map ofReal := by
    rw [num_def, Matrix.mul_smul, Matrix.mul_one]
  have hdenom : denom Ψ (I • 1 : Matrix ι ι ℂ) =
      I • (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₂₁.map ofReal +
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toBlocks₂₂.map ofReal := by
    rw [denom_def, Matrix.mul_smul, Matrix.mul_one]
  rw [coe_I] at hd
  rw [← hnum, ← hdenom]
  constructor
  · intro h
    rw [← nonsing_inv_mul_cancel_right _ (num _ _) hd, h, Matrix.smul_mul, Matrix.one_mul]
  · intro h
    rw [h, Matrix.smul_mul, mul_nonsing_inv _ hd]

/-- A symplectic matrix fixes `i𝟙` exactly when it commutes with `J`, that is, when it is complex
linear. -/
theorem smul_I_eq_I_iff_commute (Ψ : symplecticGroup ι ℝ) :
    Ψ • (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) = SiegelUpperHalfSpace.I ↔
      Commute (J ι ℝ) (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  rw [smul_I_eq_I_iff]
  set M := (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ)
  conv_rhs => rw [← fromBlocks_toBlocks M]
  simp only [Commute, SemiconjBy, J, fromBlocks_multiply, fromBlocks_inj]
  simp only [Matrix.zero_mul, Matrix.neg_mul, Matrix.one_mul, Matrix.mul_zero, Matrix.mul_neg,
    Matrix.mul_one, zero_add, add_zero]
  constructor
  · rintro ⟨hD, hC⟩
    simp [hD, hC]
  · rintro ⟨h₁, -, h₃, -⟩
    exact ⟨h₃.symm, by rw [← h₁, neg_neg]⟩

/-- A symplectic matrix fixes `i𝟙` exactly when it is the realification of a unitary matrix. -/
theorem mem_stabilizer_I_iff {Ψ : symplecticGroup ι ℝ} :
    Ψ ∈ MulAction.stabilizer (symplecticGroup ι ℝ)
        (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι) ↔
      ∃ U ∈ unitaryGroup ι ℂ, U.realify = Ψ := by
  rw [MulAction.mem_stabilizer_iff, smul_I_eq_I_iff_commute, commute_J_iff_exists_realify_eq]
  exact ⟨fun ⟨U, hU⟩ ↦ ⟨U, realify_mem_symplecticGroup_iff.1 (hU ▸ Ψ.property), hU⟩,
    fun ⟨U, _, hU⟩ ↦ ⟨U, hU⟩⟩

/-- The stabilizer of `i𝟙` in the symplectic group, as a set of real matrices, is the image of the
unitary group under realification. -/
theorem map_stabilizer_I :
    (MulAction.stabilizer (symplecticGroup ι ℝ)
        (SiegelUpperHalfSpace.I : SiegelUpperHalfSpace ι)).toSubmonoid.map
        (symplecticGroup ι ℝ).subtype =
      (unitaryGroup ι ℂ).map (realifyAlgHom ι ℂ) := by
  rw [← symplecticGroup_inf_centralizer_J]
  ext M
  simp only [Submonoid.mem_map, Subgroup.mem_toSubmonoid, Submonoid.coe_subtype,
    MulAction.mem_stabilizer_iff, smul_I_eq_I_iff_commute, Submonoid.mem_inf,
    Submonoid.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  exact ⟨fun ⟨Ψ, hΨ, hM⟩ ↦ hM ▸ ⟨Ψ.property, hΨ.eq⟩, fun ⟨hM, hJ⟩ ↦ ⟨⟨M, hM⟩, hJ, rfl⟩⟩

/-! ### Index one: the upper half plane -/

section Unique

variable [Unique ι]

private theorem mul_inv_apply_default (M N : Matrix ι ι ℂ) :
    (M * N⁻¹) default default = M default default / N default default := by
  simp [Matrix.mul_apply, div_eq_mul_inv]

/-- For a type `ι` with one element, the entries of a symplectic matrix form a matrix of
determinant one. -/
theorem exists_specialLinearGroup_coe_eq (Ψ : symplecticGroup ι ℝ) :
    ∃ g : SL(2, ℝ), (g : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inl default) (Sum.inl default),
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inl default) (Sum.inr default);
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inr default) (Sum.inl default),
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inr default) (Sum.inr default)] := by
  have h := Ψ.property
  rw [← fromBlocks_toBlocks (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ), SymplecticGroup.fromBlocks_mem_iff] at h
  have h₃ := congrFun (congrFun h.2.2 default) default
  simp only [Matrix.sub_apply, Matrix.mul_apply, Fintype.sum_unique, transpose_apply,
    Matrix.one_apply_eq, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, of_apply] at h₃
  exact ⟨⟨_, by rw [det_fin_two_of]; linarith⟩, rfl⟩

/-- For a type `ι` with one element, the action of a symplectic matrix `Ψ` on the Siegel upper
half space is, through `homeomorphUpperHalfPlane`, the Möbius action on the upper half plane of the
matrix in `SL(2, ℝ)` with the same entries. -/
theorem homeomorphUpperHalfPlane_smul (Ψ : symplecticGroup ι ℝ) (g : SL(2, ℝ))
    (hg : (g : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inl default) (Sum.inl default),
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inl default) (Sum.inr default);
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inr default) (Sum.inl default),
        (Ψ : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (Sum.inr default) (Sum.inr default)])
    (Z : SiegelUpperHalfSpace ι) :
    homeomorphUpperHalfPlane (Ψ • Z) = g • homeomorphUpperHalfPlane Z := by
  ext1
  rw [coe_homeomorphUpperHalfPlane_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
    coe_homeomorphUpperHalfPlane_apply, coe_smul, mul_inv_apply_default, hg]
  simp [num_def, denom_def, Matrix.mul_apply, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂]

end Unique

end SiegelUpperHalfSpace

end SymplecticGeometry

end
