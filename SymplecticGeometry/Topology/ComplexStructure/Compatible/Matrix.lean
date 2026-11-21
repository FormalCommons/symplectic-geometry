/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
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

## Main definitions

* `SymplecticGeometry.compatibleEquivPosDefSymplectic ι`: the homeomorphism
  `J ↦ -J₀ M` from the `ω₀`-compatible complex structures of `StdSpace ι` to the positive
  definite symplectic matrices, with inverse `P ↦ toEuclideanLin (J₀ P)`.

## Main results

* `SymplecticGeometry.stdForm_apply_toEuclideanLin`: `ω₀(v, A w) = vᵀ (-J₀ A) w`.
* `SymplecticGeometry.toMatrix_associatedBilinForm_stdForm`: the matrix `-J₀ M` is the Gram matrix
  of `g_J`.
* `SymplecticGeometry.invariant_stdForm_iff_isSymm`: `J` preserves `ω₀` exactly when `-J₀ M` is
  symmetric.
* `SymplecticGeometry.tames_stdForm_iff`: `ω₀` tames `J` exactly when the quadratic form of
  `-J₀ M` is positive definite.
* `SymplecticGeometry.compatible_stdForm_iff_posDef`: `J` is `ω₀`-compatible exactly when
  `-J₀ M` is a positive definite matrix.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], Lemma 2.5.5.
-/

public section

namespace SymplecticGeometry

open TauCeti Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `ω₀(v, A w) = vᵀ (-J₀ A) w` for a real matrix `A` indexed by `ι ⊕ ι`, where
`J₀ = Matrix.J ι ℝ`. -/
theorem stdForm_apply_toEuclideanLin (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (v w : StdSpace ι) :
    stdForm ι v (toEuclideanLin A w) = v.ofLp ⬝ᵥ ((-J ι ℝ * A) *ᵥ w.ofLp) := by
  refine (LinearMap.congr_fun₂ stdForm_toBilinForm v (toEuclideanLin A w)).trans ?_
  simp [Matrix.toBilin'_apply', Matrix.neg_mulVec, Matrix.mulVec_mulVec]

/-- The metric `g_J(v, w) = ω₀(v, J w)` is `vᵀ (-J₀ M) w`, where `M` is the matrix of `J` and
`J₀ = Matrix.J ι ℝ`. -/
theorem associatedBilinForm_stdForm_apply (J : AlmostComplexStructure (StdSpace ι))
    (v w : StdSpace ι) :
    (stdForm ι).associatedBilinForm J v w =
      v.ofLp ⬝ᵥ ((-Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap) *ᵥ w.ofLp) := by
  rw [SymplecticForm.associatedBilinForm_apply, ← stdForm_apply_toEuclideanLin,
    LinearEquiv.apply_symm_apply]

/-- The matrix `-J₀ M` is the Gram matrix of the metric `g_J(v, w) = ω₀(v, J w)` in the standard
basis, where `M` is the matrix of `J` and `J₀ = Matrix.J ι ℝ`. -/
theorem toMatrix_associatedBilinForm_stdForm (J : AlmostComplexStructure (StdSpace ι)) :
    ((stdForm ι).associatedBilinForm J).toMatrix (PiLp.basisFun 2 ℝ (ι ⊕ ι)) =
      -Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, associatedBilinForm_stdForm_apply]
  simp [PiLp.basisFun_apply]

/-- A complex structure `J` of `StdSpace ι` preserves `ω₀` exactly when the matrix `-J₀ M` is
symmetric, where `M` is the matrix of `J`. -/
theorem invariant_stdForm_iff_isSymm {J : AlmostComplexStructure (StdSpace ι)} :
    (stdForm ι).Invariant J ↔
      (-Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap).IsSymm := by
  rw [SymplecticForm.invariant_iff_isSymm_associatedBilinForm,
    ← toMatrix_associatedBilinForm_stdForm, LinearMap.BilinForm.isSymm_toMatrix_iff_isSymm]

/-- `ω₀` tames a complex structure `J` of `StdSpace ι` exactly when `xᵀ (-J₀ M) x > 0` for every
nonzero `x`, where `M` is the matrix of `J`. -/
theorem tames_stdForm_iff {J : AlmostComplexStructure (StdSpace ι)} :
    (stdForm ι).Tames J ↔ ∀ x : ι ⊕ ι → ℝ, x ≠ 0 →
      0 < x ⬝ᵥ ((-Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap) *ᵥ x) := by
  constructor
  · intro h x hx
    have := h (WithLp.toLp 2 x) (by simpa using hx)
    rwa [← SymplecticForm.associatedBilinForm_apply, associatedBilinForm_stdForm_apply] at this
  · intro h v hv
    have := h v.ofLp (by simpa using hv)
    rwa [← associatedBilinForm_stdForm_apply] at this

/-- A complex structure `J` of `StdSpace ι` is `ω₀`-compatible exactly when the matrix `-J₀ M`
is positive definite, where `M` is the matrix of `J`. -/
theorem compatible_stdForm_iff_posDef {J : AlmostComplexStructure (StdSpace ι)} :
    (stdForm ι).Compatible J ↔
      (-Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap).PosDef := by
  rw [SymplecticForm.compatible_iff_isSymm_and_posDef_associatedBilinForm]
  refine ⟨fun ⟨hs, hp⟩ ↦ ?_, fun h ↦ ?_⟩
  · rwa [LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix (PiLp.basisFun 2 ℝ (ι ⊕ ι)) _ hs,
      toMatrix_associatedBilinForm_stdForm] at hp
  · have hs := invariant_stdForm_iff_isSymm.2 (isHermitian_iff_isSymm.1 h.isHermitian)
    rw [SymplecticForm.invariant_iff_isSymm_associatedBilinForm] at hs
    refine ⟨hs, ?_⟩
    rwa [LinearMap.BilinForm.posDef_toQuadraticMap_iff_matrix (PiLp.basisFun 2 ℝ (ι ⊕ ι)) _ hs,
      toMatrix_associatedBilinForm_stdForm]

/-- The matrix `-J₀ M` of an `ω₀`-compatible complex structure, `M` its matrix, is a positive
definite symplectic matrix. -/
private theorem mem_symplecticGroup_and_posDef {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Compatible J) :
    -Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap ∈ symplecticGroup ι ℝ ∧
      (-Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap).PosDef := by
  have hP := compatible_stdForm_iff_posDef.1 hJ
  refine ⟨(IsSymm.mem_symplecticGroup_iff
    (isHermitian_iff_isSymm.1 hP.isHermitian)).2 ?_, hP⟩
  rw [← Matrix.mul_assoc (Matrix.J ι ℝ) (-Matrix.J ι ℝ), J_mul_neg_J, Matrix.one_mul]
  exact J.toEuclideanLin_symm_mul_self

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
    mem_symplecticGroup_and_posDef J.property⟩
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
