/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Action
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Unitary

/-!
# Every linear complex structure is standard

A linear complex structure `J` on a real vector space `V` of dimension `2n` is conjugate to the
standard structure `J₀ = stdComplexStructure ι` on `StdSpace ι = ℝ²ⁿ`: there is a linear
isomorphism `Φ : ℝ²ⁿ ≃ V` with `Φ ∘ J₀ = J ∘ Φ`. Two such isomorphisms differ by an automorphism
of `ℝ²ⁿ` commuting with `J₀` (`TauCeti.AlmostComplexStructure.transport_eq_transport_iff`).

For matrices this says that `GL(2n, ℝ)` acts transitively on the complex structures of `ℝ²ⁿ`,
and the stabilizer of `J₀` consists of the matrices commuting with `Matrix.J ι ℝ`, which are the
realifications of the invertible complex `n × n` matrices; so the complex structures of `ℝ²ⁿ`
are the points of `GL(2n, ℝ) / GL(n, ℂ)`.

## Main results

* `SymplecticGeometry.exists_transport_stdComplexStructure_eq`: every complex structure on a
  real vector space of dimension `2 * Fintype.card ι` is the transport of `J₀`.
* `SymplecticGeometry.instIsPretransitiveGeneralLinearGroup`: `GL (ι ⊕ ι) ℝ` acts transitively
  on the complex structures of `StdSpace ι`.
* `SymplecticGeometry.stabilizer_stdComplexStructure`: the stabilizer of `J₀` in `GL (ι ⊕ ι) ℝ`
  is the range of `Matrix.GeneralLinearGroup.realify ι ℂ`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Proposition 2.5.2.
-/

public section

namespace SymplecticGeometry

open TauCeti Module

variable {ι : Type*} [Fintype ι]

/-- Every linear complex structure `J` on a real vector space of dimension `2 * Fintype.card ι`
is the transport of the standard structure `J₀` along a linear isomorphism
`Φ : StdSpace ι ≃ V`, that is, `Φ ∘ J₀ = J ∘ Φ`. -/
theorem exists_transport_stdComplexStructure_eq {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (J : AlmostComplexStructure V)
    (h : finrank ℝ V = 2 * Fintype.card ι) :
    ∃ Φ : StdSpace ι ≃ₗ[ℝ] V, (stdComplexStructure ι).transport Φ = J := by
  obtain ⟨φ, hφ⟩ := J.exists_linearEquiv_I_smul (G := ι → ℂ)
    (by rw [h, Module.finrank_fintype_fun_eq_card])
  refine ⟨(complexToRealEuclidean ι).toLinearEquiv.symm ≪≫ₗ φ, ?_⟩
  rw [AlmostComplexStructure.transport_eq_iff_isComplexLinearMap,
    isComplexLinearMap_iff_apply]
  intro v
  simp [stdComplexStructure_def, AlmostComplexStructure.ofComplexModule_apply, hφ]

variable [DecidableEq ι]

/-- Every complex structure on `StdSpace ι` is `g • J₀` for an invertible matrix `g`. -/
theorem exists_generalLinearGroup_smul_stdComplexStructure_eq
    (J : AlmostComplexStructure (StdSpace ι)) :
    ∃ g : GL (ι ⊕ ι) ℝ, g • stdComplexStructure ι = J := by
  obtain ⟨Φ, hΦ⟩ := exists_transport_stdComplexStructure_eq J finrank_stdSpace
  exact ⟨Matrix.GeneralLinearGroup.ofEuclideanCLE Φ.toContinuousLinearEquiv, by
    rw [AlmostComplexStructure.ofEuclideanCLE_smul,
      LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, ← hΦ, AlmostComplexStructure.smul_def]⟩

/-- The invertible matrices act transitively on the complex structures of `StdSpace ι`. -/
instance instIsPretransitiveGeneralLinearGroup :
    MulAction.IsPretransitive (GL (ι ⊕ ι) ℝ) (AlmostComplexStructure (StdSpace ι)) where
  exists_smul_eq J J' := by
    obtain ⟨g, rfl⟩ := exists_generalLinearGroup_smul_stdComplexStructure_eq J
    obtain ⟨g', rfl⟩ := exists_generalLinearGroup_smul_stdComplexStructure_eq J'
    exact ⟨g' * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

/-- An invertible matrix fixes `J₀` exactly when it commutes with `Matrix.J ι ℝ`. -/
theorem generalLinearGroup_smul_stdComplexStructure_eq_iff (g : GL (ι ⊕ ι) ℝ) :
    g • stdComplexStructure ι = stdComplexStructure ι ↔
      Commute (Matrix.J ι ℝ) (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  rw [AlmostComplexStructure.generalLinearGroup_smul_def,
    AlmostComplexStructure.transport_eq_iff_isComplexLinearMap, Commute.symm_iff,
    ← commute_toEuclideanLin_stdComplexStructure_iff]
  have : ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toEuclideanCLE g.det_ne_zero).toLinearEquiv.toLinearMap =
      Matrix.toEuclideanLin (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) :=
    LinearMap.ext fun v ↦ Matrix.toEuclideanCLE_apply _ _ v
  rw [this, IsComplexLinearMap, Commute, SemiconjBy, Module.End.mul_eq_comp,
    Module.End.mul_eq_comp, eq_comm]

/-- The stabilizer of `J₀` in `GL (ι ⊕ ι) ℝ` is the realified complex general linear group
`GL ι ℂ`. -/
theorem stabilizer_stdComplexStructure :
    MulAction.stabilizer (GL (ι ⊕ ι) ℝ) (stdComplexStructure ι) =
      (Matrix.GeneralLinearGroup.realify ι ℂ).range := by
  ext g
  rw [MulAction.mem_stabilizer_iff, generalLinearGroup_smul_stdComplexStructure_eq_iff,
    Matrix.GeneralLinearGroup.mem_range_realify_iff]

end SymplecticGeometry

end
