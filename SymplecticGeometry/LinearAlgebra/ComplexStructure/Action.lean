/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.Geometry.Symplectic.Complex.OrthonormalBasis
public import TauCeti.Geometry.Symplectic.Finrank
public import TauCeti.Geometry.Symplectic.SymplecticTransport

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
* `TauCeti.AlmostComplexStructure.exists_linearIsometryEquiv_transport_eq`: two norm-preserving
  complex structures on inner product spaces of the same finite dimension are conjugate by a
  linear isometry.
* `TauCeti.AlmostComplexStructure.toEuclideanLin_symm_mul_self`: the matrix of a complex
  structure of `EuclideanSpace ℝ n` squares to `-1`.
* `TauCeti.AlmostComplexStructure.smul_apply`, `generalLinearGroup_smul_apply`: the actions
  evaluated at a vector.
* `LinearEquiv.trans_assoc_id`: associativity of composition of linear equivalences over one
  ring, in a form that `simp` can use, so that it proves the group laws of the action.
* `TauCeti.SymplecticForm.IsSymplectomorphism.compatible_transport_iff`: a linear
  symplectomorphism `e : (V, ω₁) → (W, ω₂)` preserves and reflects compatibility, that is,
  `ω₂` is compatible with `J.transport e` exactly when `ω₁` is compatible with `J`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 2.5.
-/

public section

namespace LinearEquiv

variable {R V W X Y : Type*} [Semiring R] [AddCommMonoid V] [Module R V] [AddCommMonoid W]
  [Module R W] [AddCommMonoid X] [Module R X] [AddCommMonoid Y] [Module R Y]

/-- Composition of linear equivalences over one ring is associative. Unlike Mathlib's
`LinearEquiv.trans_assoc`, whose composite ring homomorphisms are determined only by instance
arguments, this form can be used by `simp`, which with it brackets every composite of linear
equivalences over one ring to the right. -/
@[simp]
theorem trans_assoc_id (a : V ≃ₗ[R] W) (b : W ≃ₗ[R] X) (c : X ≃ₗ[R] Y) :
    (a ≪≫ₗ b) ≪≫ₗ c = a ≪≫ₗ (b ≪≫ₗ c) :=
  (rfl)

end LinearEquiv

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

/-- The action of a linear automorphism is transport along it. This is the simp normal form of
the action: `simp` rewrites `e • J` to `J.transport e`, which Tau Ceti's simp lemmas then
evaluate. -/
@[simp]
theorem smul_def (e : V ≃ₗ[ℝ] V) (J : AlmostComplexStructure V) : e • J = J.transport e :=
  (rfl)

/-- Transport along the identity automorphism `1` does nothing. -/
@[simp]
theorem transport_one (J : AlmostComplexStructure V) : J.transport (1 : V ≃ₗ[ℝ] V) = J :=
  J.transport_refl

/-- Transport along a product of automorphisms is transport along the right factor, then along
the left one. The right side is nested, so that `simp` rewrites a product or an inverse in
either factor while it is still the argument of `transport`. -/
@[simp]
theorem transport_mul (J : AlmostComplexStructure V) (e f : V ≃ₗ[ℝ] V) :
    J.transport (e * f) = (J.transport f).transport e :=
  (rfl)

/-- Transport along the inverse of an automorphism is transport along its inverse equivalence. -/
@[simp]
theorem transport_inv (J : AlmostComplexStructure V) (e : V ≃ₗ[ℝ] V) :
    J.transport e⁻¹ = J.transport e.symm :=
  (rfl)

theorem smul_apply (e : V ≃ₗ[ℝ] V) (J : AlmostComplexStructure V) (v : V) :
    (e • J) v = e (J (e.symm v)) :=
  (rfl)

theorem toLinearMap_smul (e : V ≃ₗ[ℝ] V) (J : AlmostComplexStructure V) :
    (e • J).toLinearMap = e.conj J.toLinearMap :=
  (rfl)

end LinearEquiv

section InnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Two norm-preserving complex structures `J` on `V` and `J'` on `W`, inner product spaces of the
same finite dimension, are conjugate by a linear isometry `Φ`: `Φ ∘ J = J' ∘ Φ`. The isometry
sends an adapted orthonormal basis `(u₁, J u₁, …)` of `J` to one of `J'`. -/
theorem exists_linearIsometryEquiv_transport_eq (J : AlmostComplexStructure V)
    (J' : AlmostComplexStructure W) (hJ : ∀ v, ‖J v‖ = ‖v‖) (hJ' : ∀ w, ‖J' w‖ = ‖w‖)
    (h : Module.finrank ℝ V = Module.finrank ℝ W) :
    ∃ Φ : V ≃ₗᵢ[ℝ] W, J.transport Φ.toLinearEquiv = J' := by
  obtain ⟨n, hn⟩ := J.even_finrank_real
  obtain ⟨b, hb⟩ := J.exists_adapted_orthonormalBasis hJ n (by omega)
  obtain ⟨b', hb'⟩ := J'.exists_adapted_orthonormalBasis hJ' n (by omega)
  set Φ := b.equiv b' (Equiv.refl _)
  have hΦ (i : Fin (2 * n)) : Φ (J (b i)) = J' (Φ (b i)) := by
    obtain ⟨k, hk⟩ :
        ∃ k : Fin n, i = ⟨2 * k.val, by omega⟩ ∨ i = ⟨2 * k.val + 1, by omega⟩ := by
      refine ⟨⟨i / 2, by omega⟩, ?_⟩
      rcases Nat.even_or_odd' i.val with ⟨m, hm | hm⟩
      · exact Or.inl (Fin.ext (by simp; omega))
      · exact Or.inr (Fin.ext (by simp; omega))
    have e1 := b.equiv_apply_basis b' (Equiv.refl _) ⟨2 * k.val, by omega⟩
    have e2 := b.equiv_apply_basis b' (Equiv.refl _) ⟨2 * k.val + 1, by omega⟩
    rw [Equiv.refl_apply] at e1 e2
    rcases hk with rfl | rfl
    · rw [← hb, e2, e1, hb']
    · rw [e2, hb' k, apply_apply, hb k, apply_apply, map_neg, e1]
  exact ⟨Φ, (transport_eq_iff_isComplexLinearMap _).2
    (b.toBasis.ext fun i ↦ by simpa using hΦ i)⟩

end InnerProductSpace

section Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of a complex structure on a Euclidean space squares to `-1`. -/
theorem toEuclideanLin_symm_mul_self (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    Matrix.toEuclideanLin.symm J.toLinearMap * Matrix.toEuclideanLin.symm J.toLinearMap = -1 := by
  rw [← Matrix.toLpLin_symm_comp, J.square_neg, map_neg]
  simp

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

theorem generalLinearGroup_smul_apply (g : GL n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) (v : EuclideanSpace ℝ n) :
    (g • J) v = Matrix.toEuclideanLin (g : Matrix n n ℝ)
      (J (Matrix.toEuclideanLin (g : Matrix n n ℝ)⁻¹ v)) := by
  rw [generalLinearGroup_smul_def, transport_apply]
  simp

/-- The linear map of `g • J` is `g ∘ J ∘ g⁻¹`, matrices acting by `Matrix.toEuclideanLin`. -/
@[simp]
theorem toLinearMap_generalLinearGroup_smul (g : GL n ℝ)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    (g • J).toLinearMap = Matrix.toEuclideanLin (g : Matrix n n ℝ) ∘ₗ J.toLinearMap ∘ₗ
      Matrix.toEuclideanLin (g : Matrix n n ℝ)⁻¹ :=
  LinearMap.ext (generalLinearGroup_smul_apply g J)

/-- The matrix of a continuous linear automorphism `Φ` acts on complex structures as `Φ` does. -/
@[simp]
theorem ofEuclideanCLE_smul (Φ : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n)
    (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    Matrix.GeneralLinearGroup.ofEuclideanCLE Φ • J = J.transport Φ.toLinearEquiv := by
  rw [generalLinearGroup_smul_def, Matrix.GeneralLinearGroup.toEuclideanCLE_ofEuclideanCLE]

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

namespace TauCeti.SymplecticForm

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
  {ω₁ : SymplecticForm V} {ω₂ : SymplecticForm W} {e : V ≃ₗ[ℝ] W}

/-- A linear symplectomorphism `e : (V, ω₁) → (W, ω₂)` carries compatible complex structures to
compatible ones and back: `ω₂` is compatible with `e ∘ J ∘ e⁻¹` exactly when `ω₁` is compatible
with `J`. For `V = W` and `ω₁ = ω₂` this says that the symplectic automorphisms of `(V, ω)` act on
the complex structures compatible with `ω`, through `e • J = J.transport e`. -/
theorem IsSymplectomorphism.compatible_transport_iff (he : ω₁.IsSymplectomorphism ω₂ e)
    (J : AlmostComplexStructure V) : ω₂.Compatible (J.transport e) ↔ ω₁.Compatible J := by
  rw [← isSymplectomorphism_iff_transport_eq.1 he, SymplecticForm.compatible_transport_iff]

end TauCeti.SymplecticForm

end
