/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Geometry.Symplectic.Transport

/-!
# Linear groups acting on complex structures

Linear complex structures on a real vector space `V` are acted on by the linear automorphisms
of `V`, by conjugation: `e • J = e ∘ J ∘ e⁻¹`, which is Tau Ceti's
`TauCeti.AlmostComplexStructure.transport`. On the Euclidean space `EuclideanSpace ℝ n` this
gives actions of the invertible matrices and of the special orthogonal matrices.

## Main definitions

* `TauCeti.AlmostComplexStructure.instMulActionLinearEquiv`: the action of `V ≃ₗ[ℝ] V` on
  `AlmostComplexStructure V`, `e • J = J.transport e`.
* `TauCeti.AlmostComplexStructure.instMulActionGeneralLinearGroup`: the action of `GL n ℝ` on
  the complex structures of `EuclideanSpace ℝ n`, through the linear map of a matrix.
* `TauCeti.AlmostComplexStructure.instMulActionSpecialOrthogonalGroup`: its restriction to
  `Matrix.specialOrthogonalGroup n ℝ`.

## Main results

* `TauCeti.AlmostComplexStructure.transport_eq_iff_isComplexLinearMap`: `J.transport e = J'`
  exactly when `e` is complex linear from `J` to `J'`.
* `TauCeti.AlmostComplexStructure.smul_apply`, `generalLinearGroup_smul_apply`: the actions
  evaluated at a vector.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

namespace TauCeti.AlmostComplexStructure

section LinearEquiv

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The transport of `J` along `e` is `J'` exactly when `e` intertwines `J` and `J'`. -/
theorem transport_eq_iff_isComplexLinearMap {J : AlmostComplexStructure V}
    {J' : AlmostComplexStructure W} (e : V ≃ₗ[ℝ] W) :
    J.transport e = J' ↔ IsComplexLinearMap J J' e.toLinearMap := by
  rw [isComplexLinearMap_iff_apply, ← toLinearMap_injective.eq_iff, LinearMap.ext_iff]
  refine ⟨fun h v ↦ ?_, fun h w ↦ ?_⟩
  · simpa using h (e v)
  · simpa using h (e.symm w)

/-- An endomorphism of `V` is complex linear for `J` exactly when it commutes with `J`. -/
theorem isComplexLinearMap_self_iff_commute (J : AlmostComplexStructure V) (f : Module.End ℝ V) :
    IsComplexLinearMap J J f ↔ Commute f J.toLinearMap := by
  rw [IsComplexLinearMap, Commute, SemiconjBy, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    eq_comm]

/-- Two linear isomorphisms `Φ Ψ : V ≃ W` transport `J` to the same structure exactly when
`Ψ⁻¹ ∘ Φ` is an automorphism of `(V, J)`, that is, commutes with `J`. -/
theorem transport_eq_transport_iff (J : AlmostComplexStructure V) (Φ Ψ : V ≃ₗ[ℝ] W) :
    J.transport Φ = J.transport Ψ ↔ IsComplexLinearMap J J (Φ ≪≫ₗ Ψ.symm).toLinearMap := by
  rw [← transport_eq_iff_isComplexLinearMap, ← transport_trans]
  exact ⟨fun h ↦ by rw [h, transport_symm_transport], fun h ↦ by
    rw [← transport_transport_symm (J.transport Φ) Ψ, h]⟩

/-- The linear automorphisms of `V` act on the complex structures of `V` by conjugation,
`e • J = e ∘ J ∘ e⁻¹`. -/
instance instMulActionLinearEquiv : MulAction (V ≃ₗ[ℝ] V) (AlmostComplexStructure V) where
  smul e J := J.transport e
  one_smul J := J.transport_refl
  mul_smul e₁ e₂ J := (J.transport_trans e₂ e₁).symm

theorem smul_def (e : V ≃ₗ[ℝ] V) (J : AlmostComplexStructure V) : e • J = J.transport e :=
  (rfl)

@[simp]
theorem smul_apply (e : V ≃ₗ[ℝ] V) (J : AlmostComplexStructure V) (v : V) :
    (e • J) v = e (J (e.symm v)) :=
  (rfl)

@[simp]
theorem toLinearMap_smul (e : V ≃ₗ[ℝ] V) (J : AlmostComplexStructure V) :
    (e • J).toLinearMap = e.conj J.toLinearMap :=
  (rfl)

end LinearEquiv

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The invertible real matrices act on the complex structures of `EuclideanSpace ℝ n` by
conjugation with their linear maps: `g • J = g ∘ J ∘ g⁻¹`. -/
noncomputable instance instMulActionGeneralLinearGroup :
    MulAction (GL n ℝ) (AlmostComplexStructure (EuclideanSpace ℝ n)) :=
  MulAction.compHom _
    (ContinuousLinearEquiv.toLinearEquivMonoidHom.comp
      (Matrix.GeneralLinearGroup.ofEuclideanCLE (𝕜 := ℝ) (ι := n)).symm.toMonoidHom)

theorem generalLinearGroup_smul_def (g : GL n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    g • J = J.transport ((g : Matrix n n ℝ).toEuclideanCLE g.det_ne_zero).toLinearEquiv := by
  rw [MulAction.compHom_smul_def, smul_def]
  simp

@[simp]
theorem generalLinearGroup_smul_apply (g : GL n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) (v : EuclideanSpace ℝ n) :
    (g • J) v = Matrix.toEuclideanLin (g : Matrix n n ℝ)
      (J (Matrix.toEuclideanLin (↑g⁻¹ : Matrix n n ℝ) v)) := by
  rw [generalLinearGroup_smul_def, transport_apply]
  simp [Matrix.coe_units_inv]

/-- The linear map of `g • J` is `g ∘ J ∘ g⁻¹`, matrices acting by `Matrix.toEuclideanLin`. -/
@[simp]
theorem toLinearMap_generalLinearGroup_smul (g : GL n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    (g • J).toLinearMap = Matrix.toEuclideanLin (g : Matrix n n ℝ) ∘ₗ J.toLinearMap ∘ₗ
      Matrix.toEuclideanLin (↑g⁻¹ : Matrix n n ℝ) := by
  ext v
  simp

/-- The matrix of a continuous linear automorphism `Φ` acts on complex structures as `Φ` does. -/
@[simp]
theorem ofEuclideanCLE_smul (Φ : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    Matrix.GeneralLinearGroup.ofEuclideanCLE Φ • J = Φ.toLinearEquiv • J := by
  rw [generalLinearGroup_smul_def, Matrix.GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE,
    smul_def]

/-- The special orthogonal matrices act on the complex structures of `EuclideanSpace ℝ n` as
invertible matrices. -/
noncomputable instance instMulActionSpecialOrthogonalGroup :
    MulAction (Matrix.specialOrthogonalGroup n ℝ)
      (AlmostComplexStructure (EuclideanSpace ℝ n)) :=
  MulAction.compHom _ (Unitary.toUnits.comp
    (Submonoid.inclusion (Matrix.specialUnitaryGroup_le_unitaryGroup (n := n) (α := ℝ))))

/-- A special orthogonal matrix acts as the invertible matrix it is. -/
@[simp]
theorem specialOrthogonalGroup_smul_def (g : Matrix.specialOrthogonalGroup n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    g • J = (Unitary.toUnits (Submonoid.inclusion
      (Matrix.specialUnitaryGroup_le_unitaryGroup (n := n) (α := ℝ)) g) : GL n ℝ) • J :=
  (rfl)

end Matrix

end TauCeti.AlmostComplexStructure

end
