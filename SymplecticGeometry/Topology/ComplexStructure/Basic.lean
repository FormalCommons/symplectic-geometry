/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Analysis.CStarAlgebra.Matrix
public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Action
public import SymplecticGeometry.LinearAlgebra.Matrix.NonsingularInverse
public import TauCeti.Geometry.Symplectic.AlmostComplex.Topology
public import TauCeti.Topology.Algebra.Star.Unitary

/-!
# The space of linear complex structures

Tau Ceti topologizes the complex structures of a finite-dimensional real normed space `V` as a
subspace of the continuous endomorphisms of `V`. Since the condition `J ∘ J = -1` is closed,
they form a closed subspace, which is therefore Hausdorff and locally compact (hence a Baire
space).

On `EuclideanSpace ℝ n`, taking matrices identifies the complex structures with the real
matrices `A` such that `A * A = -1`, and the actions of `GL n ℝ` and of
`Matrix.specialOrthogonalGroup n ℝ` by conjugation are continuous.

## Main definitions

* `TauCeti.AlmostComplexStructure.homeomorphMatrix`: the homeomorphism between the complex
  structures of `EuclideanSpace ℝ n` and the matrices of square `-1`.
* `TauCeti.AlmostComplexStructure.toGeneralLinearGroup`: the matrix of a complex structure, as
  an invertible matrix.

## Main results

* `TauCeti.AlmostComplexStructure.isClosedEmbedding_toContinuousLinearMap`: the complex
  structures form a closed subspace of the continuous endomorphisms.
* The instances `T2Space`, `LocallyCompactSpace`, and `ContinuousSMul` for `GL n ℝ` and
  `Matrix.specialOrthogonalGroup n ℝ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

namespace TauCeti.AlmostComplexStructure

section Normed

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The continuous endomorphisms of the complex structures are exactly those of square `-1`. -/
theorem range_toContinuousLinearMap :
    Set.range (fun J : AlmostComplexStructure V ↦ LinearMap.toContinuousLinearMap J.toLinearMap) =
      {A | A * A = -1} := by
  refine Set.Subset.antisymm ?_ fun A (hA : A * A = -1) ↦ ?_
  · rintro _ ⟨J, rfl⟩
    exact toContinuousLinearMap_mul_self J
  · refine ⟨⟨A.toLinearMap, ?_⟩, ContinuousLinearMap.coe_injective (by simp)⟩
    ext v
    simpa using congr($hA v)

/-- Sending a complex structure to its endomorphism is a closed embedding into the continuous
endomorphisms: the condition `J ∘ J = -1` is closed. -/
theorem isClosedEmbedding_toContinuousLinearMap :
    Topology.IsClosedEmbedding
      fun J : AlmostComplexStructure V ↦ LinearMap.toContinuousLinearMap J.toLinearMap :=
  ⟨isEmbedding_toContinuousLinearMap, by
    rw [range_toContinuousLinearMap]
    exact isClosed_eq (continuous_id.mul continuous_id) continuous_const⟩

/-- A complex structure is invertible as a continuous endomorphism, with inverse `-J`. -/
theorem isUnit_toContinuousLinearMap (J : AlmostComplexStructure V) :
    IsUnit (LinearMap.toContinuousLinearMap J.toLinearMap) :=
  isUnit_iff_exists.2 ⟨-LinearMap.toContinuousLinearMap J.toLinearMap,
    by rw [mul_neg, toContinuousLinearMap_mul_self, neg_neg],
    by rw [neg_mul, toContinuousLinearMap_mul_self, neg_neg]⟩

instance : T2Space (AlmostComplexStructure V) :=
  isEmbedding_toContinuousLinearMap.t2Space

instance : LocallyCompactSpace (AlmostComplexStructure V) :=
  isClosedEmbedding_toContinuousLinearMap.locallyCompactSpace

end Normed

section Matrix

variable (n : Type*) [Fintype n] [DecidableEq n]

private theorem toLinearMap_toEuclideanCLM_comp_self {A : Matrix n n ℝ} (hA : A * A = -1) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).toLinearMap.comp
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).toLinearMap = -LinearMap.id := by
  have h := map_mul (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) A A
  rw [hA, map_neg, map_one] at h
  refine LinearMap.ext fun v ↦ ?_
  simpa using congr($h v).symm

/-- The complex structures of `EuclideanSpace ℝ n` are homeomorphic to the real matrices of
square `-1`, a structure going to its matrix in the standard basis. -/
noncomputable def homeomorphMatrix :
    AlmostComplexStructure (EuclideanSpace ℝ n) ≃ₜ {A : Matrix n n ℝ // A * A = -1} where
  toFun J := ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).symm
      (LinearMap.toContinuousLinearMap J.toLinearMap),
    (congrArg (fun A ↦ A * A)
      (Matrix.toEuclideanCLM_symm_toContinuousLinearMap J.toLinearMap)).trans
      J.toEuclideanLin_symm_mul_self⟩
  invFun A := ⟨(Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A.val).toLinearMap,
    toLinearMap_toEuclideanCLM_comp_self n A.property⟩
  left_inv J := by
    refine toLinearMap_injective (LinearMap.ext fun v ↦ ?_)
    simp
  right_inv A := Subtype.ext ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).symm_apply_apply A.val)
  continuous_toFun :=
    (Matrix.continuous_toEuclideanCLM_symm.comp
      isEmbedding_toContinuousLinearMap.continuous).subtype_mk _
  continuous_invFun := by
    rw [continuous_iff]
    exact (Matrix.continuous_toEuclideanCLM.comp continuous_subtypeVal).congr fun A ↦
      ContinuousLinearMap.ext fun _ ↦ rfl

variable {n}

/-- The matrix of `J` is the matrix of its operator. -/
@[simp]
theorem homeomorphMatrix_apply_coe (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    (homeomorphMatrix n J : Matrix n n ℝ) =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).symm
        (LinearMap.toContinuousLinearMap J.toLinearMap) :=
  (rfl)

/-- The matrix that `homeomorphMatrix` assigns to a complex structure `J` of
`EuclideanSpace ℝ n` is the matrix of `J`, `toEuclideanLin.symm J`. -/
theorem coe_homeomorphMatrix (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    (homeomorphMatrix n J : Matrix n n ℝ) = Matrix.toEuclideanLin.symm J.toLinearMap := by
  rw [homeomorphMatrix_apply_coe, Matrix.toEuclideanCLM_symm_toContinuousLinearMap]

/-- The structure of a matrix `A` of square `-1` acts on vectors as `A`. -/
@[simp]
theorem homeomorphMatrix_symm_apply_apply (A : {A : Matrix n n ℝ // A * A = -1})
    (v : EuclideanSpace ℝ n) :
    (homeomorphMatrix n).symm A v = Matrix.toEuclideanLin (A : Matrix n n ℝ) v :=
  Matrix.toEuclideanCLM_apply _ _

/-- The matrix of a complex structure `J`, as an invertible matrix: its inverse is the matrix of
`-J`, since `J * J = -1`. -/
noncomputable def toGeneralLinearGroup (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    GL n ℝ :=
  (isUnit_of_mul_self_eq_neg_one (homeomorphMatrix n J).property).unit

/-- The invertible matrix of `J` is its matrix. -/
@[simp]
theorem coe_toGeneralLinearGroup (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    (J.toGeneralLinearGroup : Matrix n n ℝ) = homeomorphMatrix n J :=
  IsUnit.unit_spec _

/-- The inverse of the matrix of `J` is the matrix of `-J`.

This is not a `simp` lemma: `simp` rewrites its left side with `Matrix.coe_units_inv`, and
proves it with `inv_toEuclideanCLM_symm_toContinuousLinearMap`. -/
theorem coe_toGeneralLinearGroup_inv (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    (↑J.toGeneralLinearGroup⁻¹ : Matrix n n ℝ) = -homeomorphMatrix n J := by
  rw [Matrix.coe_units_inv, coe_toGeneralLinearGroup,
    Matrix.inv_eq_neg_of_mul_self_eq_neg_one (homeomorphMatrix n J).property]

/-- The inverse of the matrix of a complex structure `J` of `EuclideanSpace ℝ n` is its
negative, since its square is `-1`. -/
@[simp]
theorem inv_toEuclideanCLM_symm_toContinuousLinearMap
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).symm
        (LinearMap.toContinuousLinearMap J.toLinearMap))⁻¹ =
      -(Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).symm
        (LinearMap.toContinuousLinearMap J.toLinearMap) :=
  Matrix.inv_eq_neg_of_mul_self_eq_neg_one (by
    rw [Matrix.toEuclideanCLM_symm_toContinuousLinearMap, J.toEuclideanLin_symm_mul_self])

/-- The invertible matrix of a complex structure depends continuously on it. -/
theorem continuous_toGeneralLinearGroup :
    Continuous (toGeneralLinearGroup (n := n)) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩ <;>
    simp only [Function.comp_def, coe_toGeneralLinearGroup, coe_toGeneralLinearGroup_inv] <;>
    fun_prop

/-- The endomorphism of `g • J` in the operator norm is `g J g⁻¹`, matrices acting by
`Matrix.toEuclideanCLM`. -/
theorem toContinuousLinearMap_generalLinearGroup_smul (g : GL n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    LinearMap.toContinuousLinearMap (g • J).toLinearMap =
      Matrix.toEuclideanCLM (𝕜 := ℝ) (g : Matrix n n ℝ) *
        LinearMap.toContinuousLinearMap J.toLinearMap *
          Matrix.toEuclideanCLM (𝕜 := ℝ) (↑g⁻¹ : Matrix n n ℝ) := by
  ext1 v
  simp [Matrix.coe_units_inv]

/-- The matrix of `g • J` is `g * A * g⁻¹`, where `A` is the matrix of `J`. -/
theorem homeomorphMatrix_generalLinearGroup_smul (g : GL n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    (homeomorphMatrix n (g • J) : Matrix n n ℝ) =
      (g : Matrix n n ℝ) * homeomorphMatrix n J * (↑g⁻¹ : Matrix n n ℝ) := by
  rw [homeomorphMatrix_apply_coe, homeomorphMatrix_apply_coe,
    toContinuousLinearMap_generalLinearGroup_smul, map_mul, map_mul,
    StarAlgEquiv.symm_apply_apply, StarAlgEquiv.symm_apply_apply]

/-- The invertible matrices act continuously on the complex structures of `EuclideanSpace ℝ n`. -/
instance : ContinuousSMul (GL n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n)) where
  continuous_smul := by
    rw [continuous_iff]
    simp_rw [toContinuousLinearMap_generalLinearGroup_smul]
    have hc := Matrix.continuous_toEuclideanCLM (ι := n) (𝕜 := ℝ)
    exact ((hc.comp (Units.continuous_val.comp continuous_fst)).mul
      (isEmbedding_toContinuousLinearMap.continuous.comp continuous_snd)).mul
      (hc.comp (Units.continuous_coe_inv.comp continuous_fst))

/-- The special orthogonal matrices act continuously on the complex structures of
`EuclideanSpace ℝ n`. -/
instance : ContinuousSMul (Matrix.specialOrthogonalGroup n ℝ)
    (AlmostComplexStructure (EuclideanSpace ℝ n)) where
  continuous_smul := by
    have hφ : Continuous fun g : Matrix.specialOrthogonalGroup n ℝ ↦
        (Unitary.toUnits (Submonoid.inclusion
          (Matrix.specialUnitaryGroup_le_unitaryGroup (n := n) (α := ℝ)) g) : GL n ℝ) :=
      Unitary.continuous_toUnits.comp
        (continuous_inclusion Matrix.specialUnitaryGroup_le_unitaryGroup)
    simp_rw [specialOrthogonalGroup_smul_def]
    exact (hφ.comp continuous_fst).smul continuous_snd

end Matrix

end TauCeti.AlmostComplexStructure

end
