/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
public import SymplecticGeometry.Topology.ComplexStructure.Basic

/-!
# Compatible complex structures on the standard model as positive symplectic matrices

Write `J₀ = Matrix.J ι ℝ` for the matrix of the standard complex structure of `StdSpace ι`, and
`M` for the matrix of a complex structure `J` of `StdSpace ι`, so that `J = toEuclideanLin M`.
Since `ω₀(z, w) = ⟪J₀ z, w⟫`, the matrix `P = -J₀ M` is the Gram matrix of the metric
`g_J(v, w) = ω₀(v, J w)`. Hence `J` is `ω₀`-compatible exactly when `P` is symmetric and
positive definite, and then `P` is also symplectic. Conversely, a symmetric symplectic matrix `P`
satisfies `(J₀ P)² = -1`, so `J₀ P` is the matrix of a complex structure, and it is compatible
when `P` is positive definite.

The linear algebra behind this, from `SymplecticGeometry.stdForm_apply_toEuclideanLin` to
`SymplecticGeometry.compatible_stdForm_iff_posDef`, is in
`SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix`; this file adds the topology.

## Main definitions

* `SymplecticGeometry.compatibleEquivPosDefSymplectic ι`: the homeomorphism
  `J ↦ -J₀ M` from the `ω₀`-compatible complex structures of `StdSpace ι` to the positive
  definite symplectic matrices, with inverse `P ↦ toEuclideanLin (J₀ P)`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Lemma 2.5.5.
-/

public section

namespace SymplecticGeometry

open TauCeti Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `ω₀`-compatible complex structure of a positive definite symplectic matrix `P`: the
structure of matrix `J₀ P`. -/
private noncomputable def ofPosDefSymplectic
    (P : {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ // P ∈ symplecticGroup ι ℝ ∧ P.PosDef}) :
    {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J} :=
  ⟨(AlmostComplexStructure.homeomorphMatrix (ι ⊕ ι)).symm ⟨Matrix.J ι ℝ * P.val,
    (IsSymm.mem_symplecticGroup_iff
      (isHermitian_iff_isSymm.1 P.property.2.isHermitian)).1
      P.property.1⟩, by
    rw [compatible_stdForm_iff_posDef, ← AlmostComplexStructure.coe_homeomorphMatrix,
      Homeomorph.apply_symm_apply, ← Matrix.mul_assoc, neg_J_mul_J, Matrix.one_mul]
    exact P.property.2⟩

private theorem coe_homeomorphMatrix_ofPosDefSymplectic
    (P : {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ // P ∈ symplecticGroup ι ℝ ∧ P.PosDef}) :
    toEuclideanLin.symm (ofPosDefSymplectic P).val.toLinearMap = Matrix.J ι ℝ * P.val := by
  rw [← AlmostComplexStructure.coe_homeomorphMatrix, ofPosDefSymplectic,
    Homeomorph.apply_symm_apply]

variable (ι) in
/-- The `ω₀`-compatible complex structures of `StdSpace ι` are homeomorphic to the positive
definite symplectic matrices. A structure `J` with matrix `M` goes to `-J₀ M`, the Gram matrix of
`g_J`, where `J₀ = Matrix.J ι ℝ`; a matrix `P` goes back to the structure `toEuclideanLin (J₀ P)`.
-/
noncomputable def compatibleEquivPosDefSymplectic :
    {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J} ≃ₜ
      {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ // P ∈ symplecticGroup ι ℝ ∧ P.PosDef} where
  toFun J := ⟨-Matrix.J ι ℝ * toEuclideanLin.symm J.val.toLinearMap,
    neg_J_mul_mem_symplecticGroup_of_invariant J.property.invariant,
    compatible_stdForm_iff_posDef.1 J.property⟩
  invFun := ofPosDefSymplectic
  left_inv J := by
    refine Subtype.ext (AlmostComplexStructure.toLinearMap_injective
      (toEuclideanLin.symm.injective ?_))
    rw [coe_homeomorphMatrix_ofPosDefSymplectic, ← Matrix.mul_assoc, J_mul_neg_J,
      Matrix.one_mul]
  right_inv P := Subtype.ext <| by
    simp only
    rw [coe_homeomorphMatrix_ofPosDefSymplectic, ← Matrix.mul_assoc, neg_J_mul_J,
      Matrix.one_mul]
  continuous_toFun :=
    (continuous_const.mul ((continuous_subtypeVal.comp
      ((AlmostComplexStructure.homeomorphMatrix (ι ⊕ ι)).continuous.comp
        continuous_subtypeVal)).congr fun J ↦
          AlmostComplexStructure.coe_homeomorphMatrix J.val)).subtype_mk _
  continuous_invFun :=
    ((AlmostComplexStructure.homeomorphMatrix (ι ⊕ ι)).symm.continuous.comp
      ((continuous_const.mul continuous_subtypeVal).subtype_mk _)).subtype_mk _

/-- The positive definite symplectic matrix of a compatible complex structure `J` is `-J₀ M`,
where `M` is the matrix of `J`. -/
@[simp]
theorem coe_compatibleEquivPosDefSymplectic_apply
    (J : {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J}) :
    (compatibleEquivPosDefSymplectic ι J : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) =
      -Matrix.J ι ℝ * toEuclideanLin.symm J.val.toLinearMap :=
  (rfl)

/-- The compatible complex structure of a positive definite symplectic matrix `P` is the linear
map of `J₀ P`. -/
@[simp]
theorem compatibleEquivPosDefSymplectic_symm_apply_toLinearMap
    (P : {P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ // P ∈ symplecticGroup ι ℝ ∧ P.PosDef}) :
    ((compatibleEquivPosDefSymplectic ι).symm P).val.toLinearMap =
      toEuclideanLin (Matrix.J ι ℝ * P.val) :=
  LinearMap.ext fun v ↦ AlmostComplexStructure.homeomorphMatrix_symm_apply_apply _ v

end SymplecticGeometry

end
