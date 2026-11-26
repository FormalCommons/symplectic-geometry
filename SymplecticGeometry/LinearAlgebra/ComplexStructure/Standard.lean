/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.ComplexStructure.Action
public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Unitary
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.LinearAlgebra.ComplexStructure.Hom
import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Matrix
import SymplecticGeometry.Geometry.Symplectic.Orientation

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

A complex structure is *positively oriented* (`SymplecticGeometry.IsPositivelyOriented`) if it is
`g • J₀` for a matrix `g` of positive determinant. This agrees with the orientation condition of
McDuff–Salamon: these are exactly the structures whose adapted bases `(v₁, J v₁, …, vₙ, J vₙ)`
induce the symplectic orientation of `ω₀` (Tau Ceti's `TauCeti.SymplecticForm.orientation`).

## Main definitions

* `SymplecticGeometry.IsPositivelyOriented`: the complex structures in the orbit of `J₀` under
  matrices of positive determinant.

## Main results

* `SymplecticGeometry.exists_transport_stdComplexStructure_eq`: every complex structure on a
  real vector space of dimension `2 * Fintype.card ι` is the transport of `J₀`.
* `SymplecticGeometry.instIsPretransitiveGeneralLinearGroup`: `GL (ι ⊕ ι) ℝ` acts transitively
  on the complex structures of `StdSpace ι`.
* `SymplecticGeometry.stabilizer_stdComplexStructure`: the stabilizer of `J₀` in `GL (ι ⊕ ι) ℝ`
  is the range of `Matrix.GeneralLinearGroup.realify ι ℂ`.
* `SymplecticGeometry.compatible_generalLinearGroup_smul_iff`: an invertible symplectic matrix
  preserves and reflects compatibility with `ω₀`; so the symplectic group acts on the compatible
  structures (`SymplecticGeometry.instMulActionSymplecticGroupCompatible`).
* `SymplecticGeometry.instIsPretransitiveSymplecticGroupCompatible`: the symplectic group acts
  transitively on the compatible structures, since each is `Ψ • J₀` for a symplectic `Ψ`
  (`SymplecticGeometry.exists_symplecticGroup_smul_stdComplexStructure_eq`).
* `SymplecticGeometry.isPositivelyOriented_smul_stdComplexStructure_iff`: `g • J₀` is positively
  oriented exactly when `det g > 0`.
* `SymplecticGeometry.isPositivelyOriented_iff_orientation`: `J` is positively oriented exactly
  when its adapted bases induce the symplectic orientation of `ω₀`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Propositions 2.5.1 and 2.5.2, and Section 2.5 for compatible structures.
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
      LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, ← hΦ]⟩

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
    ← commute_toEuclideanLin_stdComplexStructure_iff,
    AlmostComplexStructure.isComplexLinearMap_self_iff_commute]
  congr!
  ext v : 1
  simp

/-- The stabilizer of `J₀` in `GL (ι ⊕ ι) ℝ` is the realified complex general linear group
`GL ι ℂ`. -/
theorem stabilizer_stdComplexStructure :
    MulAction.stabilizer (GL (ι ⊕ ι) ℝ) (stdComplexStructure ι) =
      (Matrix.GeneralLinearGroup.realify ι ℂ).range := by
  ext g
  rw [MulAction.mem_stabilizer_iff, generalLinearGroup_smul_stdComplexStructure_eq_iff,
    Matrix.GeneralLinearGroup.mem_range_realify_iff]

/-! ### Positively oriented structures -/

/-- A complex structure on `StdSpace ι` is *positively oriented* if it is `g • J₀` for a matrix
`g` of positive determinant. Equivalently, its adapted bases `(v₁, J v₁, …, vₙ, J vₙ)` induce
the symplectic orientation of `ω₀` (`isPositivelyOriented_iff_orientation`). -/
def IsPositivelyOriented (J : AlmostComplexStructure (StdSpace ι)) : Prop :=
  ∃ g ∈ Matrix.GLPos (ι ⊕ ι) ℝ, g • stdComplexStructure ι = J

theorem isPositivelyOriented_def (J : AlmostComplexStructure (StdSpace ι)) :
    IsPositivelyOriented J ↔ ∃ g ∈ Matrix.GLPos (ι ⊕ ι) ℝ, g • stdComplexStructure ι = J :=
  (Iff.rfl)

@[simp]
theorem isPositivelyOriented_stdComplexStructure :
    IsPositivelyOriented (stdComplexStructure ι) :=
  ⟨1, one_mem _, one_smul _ _⟩

/-- A matrix of positive determinant preserves positively oriented structures. -/
theorem IsPositivelyOriented.smul {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : IsPositivelyOriented J) {g : GL (ι ⊕ ι) ℝ}
    (hg : 0 < (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det) :
    IsPositivelyOriented (g • J) := by
  obtain ⟨h, hh, rfl⟩ := hJ
  exact ⟨g * h, mul_mem (by simpa [Matrix.mem_glpos] using hg) hh, mul_smul _ _ _⟩

/-- `g • J₀` is positively oriented exactly when `det g > 0`. -/
@[simp]
theorem isPositivelyOriented_smul_stdComplexStructure_iff (g : GL (ι ⊕ ι) ℝ) :
    IsPositivelyOriented (g • stdComplexStructure ι) ↔
      0 < (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det := by
  -- If also `h • J₀ = g • J₀` with `det h > 0`, then `g⁻¹ * h` fixes `J₀`, so it is a
  -- realified complex matrix, and its determinant `|det|²` is positive.
  refine ⟨fun ⟨h, hh, hgh⟩ ↦ ?_, fun hg ↦ isPositivelyOriented_stdComplexStructure.smul hg⟩
  have hs : g⁻¹ * h ∈ MulAction.stabilizer _ (stdComplexStructure ι) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hgh, inv_smul_smul]
  rw [stabilizer_stdComplexStructure] at hs
  obtain ⟨A, hA⟩ := hs
  have hA' : 0 < ((g⁻¹ * h : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det := by
    rw [← hA, Matrix.GeneralLinearGroup.coe_realify, Matrix.det_realify]
    exact RCLike.normSq_pos.2 A.det_ne_zero
  have hh' : 0 < (h : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det := by simpa [Matrix.mem_glpos] using hh
  have hmul : (h : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det =
      (g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det *
        ((g⁻¹ * h : GL (ι ⊕ ι) ℝ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).det := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel_left]
  exact (pos_iff_pos_of_mul_pos (hmul ▸ hh')).2 hA'

/-- The transport of `J₀` along an automorphism `Φ` of `StdSpace ι` is positively oriented
exactly when `det Φ > 0`. -/
@[simp]
theorem isPositivelyOriented_transport_iff (Φ : StdSpace ι ≃ₗ[ℝ] StdSpace ι) :
    IsPositivelyOriented ((stdComplexStructure ι).transport Φ) ↔
      0 < LinearMap.det (Φ : StdSpace ι →ₗ[ℝ] StdSpace ι) := by
  set g := Matrix.GeneralLinearGroup.ofEuclideanCLE Φ.toContinuousLinearEquiv
  have hg : g • stdComplexStructure ι = (stdComplexStructure ι).transport Φ := by
    rw [AlmostComplexStructure.ofEuclideanCLE_smul,
      LinearEquiv.toLinearEquiv_toContinuousLinearEquiv]
  have hdet := Matrix.det_toEuclideanCLE _ g.det_ne_zero
  rw [Matrix.GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE] at hdet
  rw [← hg, isPositivelyOriented_smul_stdComplexStructure_iff, ← hdet]
  simp

/-- In positive dimension, some complex structure on `StdSpace ι` is not positively oriented:
for instance, the transport of `J₀` by the reflection `x₁ ↦ -x₁`. -/
theorem exists_not_isPositivelyOriented [Nonempty ι] :
    ∃ J : AlmostComplexStructure (StdSpace ι), ¬IsPositivelyOriented J := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  set D : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.diagonal (Function.update 1 (Sum.inl i) (-1))
  have hD : D.det = -1 := by
    simp [D, Matrix.det_diagonal, Finset.prod_update_of_mem]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero D (by simp [hD]) • stdComplexStructure ι, ?_⟩
  simp [hD]

/-- A complex structure `J` on `StdSpace ι` is positively oriented exactly when every adapted
basis `(v₁, J v₁, …, vₙ, J vₙ)` induces the symplectic orientation of `ω₀`. Adapted bases exist
(`TauCeti.AlmostComplexStructure.exists_basis_apply_one_eq`), so the condition is not vacuous. -/
theorem isPositivelyOriented_iff_orientation {k : ℕ}
    (hk : finrank ℝ (StdSpace ι) = k) (J : AlmostComplexStructure (StdSpace ι)) :
    IsPositivelyOriented J ↔
      ∀ {m : ℕ} (b : Basis (Fin m × Fin 2) ℝ (StdSpace ι))
        (_ : ∀ i, b (i, 1) = J (b (i, 0))) (h : m * 2 = k),
        (b.reindex (finProdFinEquiv.trans (finCongr h))).orientation =
          (stdForm ι).orientation hk := by
  obtain ⟨Φ, rfl⟩ := exists_transport_stdComplexStructure_eq J finrank_stdSpace
  rw [isPositivelyOriented_transport_iff,
    ← Orientation.map_eq_iff_det_pos ((stdForm ι).orientation hk) _
      (by rw [Fintype.card_fin, hk])]
  refine ⟨fun hΦ m b hb h ↦ ?_, fun H ↦ ?_⟩
  · rw [stdForm_compatible.tames.orientation_reindex_transport Φ hk hb h, hΦ]
  · obtain ⟨m, b, hb⟩ := ((stdComplexStructure ι).transport Φ).exists_basis_apply_one_eq
    have h : m * 2 = k := by
      rw [← hk, finrank_eq_card_basis b, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [← stdForm_compatible.tames.orientation_reindex_transport Φ hk hb h, H b hb h]

/-! ### The symplectic group and compatible structures -/

/-- An invertible symplectic matrix `g` preserves and reflects compatibility with the standard
form: `ω₀` is compatible with `g • J = g J g⁻¹` exactly when it is compatible with `J`. -/
theorem compatible_generalLinearGroup_smul_iff {g : GL (ι ⊕ ι) ℝ} (hg : g ∈ GLSymplectic ι ℝ)
    (J : AlmostComplexStructure (StdSpace ι)) :
    (stdForm ι).Compatible (g • J) ↔ (stdForm ι).Compatible J := by
  rw [AlmostComplexStructure.generalLinearGroup_smul_def]
  exact SymplecticForm.IsSymplectomorphism.compatible_transport_iff
    ((mem_GLSymplectic_iff_isSymplectomorphism g).1 hg) J

/-- The symplectic group `Sp(2n)` acts on the complex structures of `StdSpace ι` compatible with
`ω₀`, by conjugation: `Ψ • J = Ψ J Ψ⁻¹`. -/
noncomputable instance instMulActionSymplecticGroupCompatible :
    MulAction (Matrix.symplecticGroup ι ℝ)
      {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J} where
  smul Ψ J := ⟨GLSymplectic.ofSymplecticGroup ι ℝ Ψ • (J : AlmostComplexStructure (StdSpace ι)),
    (compatible_generalLinearGroup_smul_iff (GLSymplectic.ofSymplecticGroup_mem ι ℝ Ψ) _).2
      J.property⟩
  one_smul J := Subtype.ext <| (congrArg (· • J.val) (map_one _)).trans (one_smul _ _)
  mul_smul Ψ Φ J := Subtype.ext <| (congrArg (· • J.val) (map_mul _ Ψ Φ)).trans (mul_smul _ _ _)

/-- A symplectic matrix acts on a compatible structure as the invertible matrix it is. -/
@[simp]
theorem coe_symplecticGroup_smul (Ψ : Matrix.symplecticGroup ι ℝ)
    (J : {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J}) :
    ((Ψ • J : {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J}) :
      AlmostComplexStructure (StdSpace ι)) =
      GLSymplectic.ofSymplecticGroup ι ℝ Ψ • (J : AlmostComplexStructure (StdSpace ι)) :=
  (rfl)

/-- Every complex structure on `StdSpace ι` compatible with `ω₀` is `Ψ • J₀` for a symplectic
matrix `Ψ`. -/
theorem exists_symplecticGroup_smul_stdComplexStructure_eq
    {J : AlmostComplexStructure (StdSpace ι)} (hJ : (stdForm ι).Compatible J) :
    ∃ Ψ : Matrix.symplecticGroup ι ℝ,
      GLSymplectic.ofSymplecticGroup ι ℝ Ψ • stdComplexStructure ι = J := by
  obtain ⟨Φ, hΦ, hΦJ⟩ := (compatible_iff_exists_isSymplectomorphism_stdForm finrank_stdSpace).1 hJ
  set g : GL (ι ⊕ ι) ℝ := Matrix.GeneralLinearGroup.ofEuclideanCLE Φ.toContinuousLinearEquiv
  have hg : g ∈ GLSymplectic ι ℝ := by
    rw [mem_GLSymplectic_iff_isSymplectomorphism]
    simpa [g] using hΦ
  obtain ⟨Ψ, hΨ⟩ := (GLSymplectic.range_ofSymplecticGroup ι ℝ).ge hg
  refine ⟨Ψ, ?_⟩
  rw [hΨ, AlmostComplexStructure.ofEuclideanCLE_smul,
    LinearEquiv.toLinearEquiv_toContinuousLinearEquiv,
    AlmostComplexStructure.transport_eq_iff_isComplexLinearMap]
  exact hΦJ

/-- The symplectic group `Sp(2n)` acts transitively on the complex structures of `StdSpace ι`
compatible with `ω₀`. -/
instance instIsPretransitiveSymplecticGroupCompatible :
    MulAction.IsPretransitive (Matrix.symplecticGroup ι ℝ)
      {J : AlmostComplexStructure (StdSpace ι) // (stdForm ι).Compatible J} :=
  MulAction.IsPretransitive.of_orbit (x₀ := ⟨stdComplexStructure ι, stdForm_compatible⟩)
    fun J ↦ (exists_symplecticGroup_smul_stdComplexStructure_eq J.property).imp
      fun _ h ↦ Subtype.ext h

end SymplecticGeometry

end
