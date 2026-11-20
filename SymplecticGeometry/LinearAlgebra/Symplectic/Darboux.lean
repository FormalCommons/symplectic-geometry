/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.WittExtension
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic

/-!
# The linear Darboux theorem

Let `V` be a finite-dimensional vector space over a field `k`, and `B` an alternating,
nondegenerate bilinear form on it. Then `dim V = 2n` is even, `V` has a symplectic basis, and
there is a linear isomorphism `Ψ : k²ⁿ ≃ V` with `Ψ^* B = ω₀`. Here `k²ⁿ` is
`Fin n ⊕ Fin n → k`, with the `x`-coordinates at `Sum.inl` and the `y`-coordinates at `Sum.inr`, and
`ω₀((x, y), (x', y')) = ∑ⱼ (xⱼ y'ⱼ - yⱼ x'ⱼ)`, which is `-TauCeti.stdSymplecticBilinForm k n`
(Tau Ceti's form is `vᵀ J w`).

Tau Ceti proves the basis statement (`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J`) and
the evenness (`LinearMap.BilinForm.IsAlt.even_finrank`). This file adds the isomorphism with the
standard model: the standard basis of `k²ⁿ`, reordered by `Sum.swap`, has Gram matrix
`Matrix.J` for `ω₀`, the same as a symplectic basis of `V`, so
`Module.Basis.isometryEquivOfToMatrixEq` gives the isometry.

If the matrix of `B` in a basis `b` is `Matrix.J`, then McDuff–Salamon's normalization
`B(uⱼ, vₖ) = δⱼₖ` holds for `uⱼ = b (Sum.inr j)` and `vⱼ = b (Sum.inl j)`.

Over `ℝ` the same holds with Tau Ceti's `TauCeti.SymplecticForm` and the library's standard
model `SymplecticGeometry.stdForm` on `SymplecticGeometry.StdSpace ι`; it follows from Tau Ceti's
`TauCeti.SymplecticForm.exists_isSymplectomorphism`.

## Main results

* `TauCeti.toMatrix_reindex_sumComm_neg_stdSymplecticBilinForm`: the Gram matrix of `ω₀` in the
  reordered standard basis is `Matrix.J`.
* `LinearMap.BilinForm.IsAlt.nonempty_isometryEquiv_neg_stdSymplecticBilinForm`: a space of
  dimension `2n` with a nondegenerate alternating form is isometric to `(k²ⁿ, ω₀)`.
* `LinearMap.BilinForm.IsAlt.nonempty_isometryEquiv_of_finrank_eq`: two such spaces of the same
  dimension are isometric.
* `LinearMap.BilinForm.IsAlt.exists_basis_and_isometryEquiv`: the linear Darboux theorem, the
  three statements together.
* `SymplecticGeometry.exists_isSymplectomorphism_stdForm`,
  `SymplecticGeometry.exists_isSymplectomorphism_stdForm_fin`: the real version, with `stdForm`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 2.1.3.
-/

public section

open Module

namespace TauCeti

variable (k : Type*) [CommRing k] (n : ℕ)

/-- The standard basis of `Fin n ⊕ Fin n → k`, reordered by `Sum.swap` (so that its vector at
`Sum.inl j` is the `yⱼ`-axis `Pi.single (Sum.inr j) 1`, and its vector at `Sum.inr j` is the
`xⱼ`-axis), has Gram matrix `Matrix.J` for `ω₀ = -stdSymplecticBilinForm k n`. -/
theorem toMatrix_reindex_sumComm_neg_stdSymplecticBilinForm :
    LinearMap.BilinForm.toMatrix ((Pi.basisFun k (Fin n ⊕ Fin n)).reindex (Equiv.sumComm _ _))
      (-stdSymplecticBilinForm k n) = Matrix.J (Fin n) k := by
  ext (i | i) (j | j) <;>
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.J, Matrix.one_apply]

end TauCeti

namespace LinearMap.BilinForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : LinearMap.BilinForm R M}

/-- The pairings of a basis whose Gram matrix is `Matrix.J`: with `uⱼ = b (Sum.inr j)` and
`vⱼ = b (Sum.inl j)`, they are `B(uᵢ, uⱼ) = B(vᵢ, vⱼ) = 0` and `B(uᵢ, vⱼ) = δᵢⱼ`. -/
theorem apply_basis_of_toMatrix_eq_J {m : ℕ} {b : Basis (Fin m ⊕ Fin m) R M}
    (hb : toMatrix b B = Matrix.J (Fin m) R) (i j : Fin m) :
    B (b (.inr i)) (b (.inr j)) = 0 ∧ B (b (.inl i)) (b (.inl j)) = 0 ∧
      B (b (.inr i)) (b (.inl j)) = if i = j then 1 else 0 := by
  simp only [← toMatrix_apply, hb]
  simp [Matrix.J, Matrix.one_apply]

end LinearMap.BilinForm

namespace LinearMap.BilinForm.IsAlt

open TauCeti

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {B : LinearMap.BilinForm k V} {C : LinearMap.BilinForm k W}

/-- A nondegenerate alternating form `B` on a space of dimension `2n` is isometric to the
standard model: there is a linear isomorphism `Ψ : (Fin n ⊕ Fin n → k) ≃ V` with
`B(Ψ z, Ψ w) = ω₀(z, w)`, where `ω₀ = -stdSymplecticBilinForm k n`. -/
theorem nonempty_isometryEquiv_neg_stdSymplecticBilinForm (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {n : ℕ} (hn : finrank k V = 2 * n) :
    Nonempty ((-stdSymplecticBilinForm k n).IsometryEquiv B) := by
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  obtain rfl : m = n := by
    rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin] at hn
    omega
  exact ⟨((Pi.basisFun k _).reindex (Equiv.sumComm _ _)).isometryEquivOfToMatrixEq b
    ((toMatrix_reindex_sumComm_neg_stdSymplecticBilinForm k m).trans hb.symm)⟩

/-- Two finite-dimensional spaces of the same dimension with nondegenerate alternating forms are
isometric. -/
theorem nonempty_isometryEquiv_of_finrank_eq (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hC : C.IsAlt) (hndC : C.Nondegenerate) (hdim : finrank k V = finrank k W) :
    Nonempty (B.IsometryEquiv C) := by
  obtain ⟨n, hn⟩ := hB.even_finrank hnd
  rw [← two_mul] at hn
  obtain ⟨e⟩ := hB.nonempty_isometryEquiv_neg_stdSymplecticBilinForm hnd hn
  obtain ⟨f⟩ := hC.nonempty_isometryEquiv_neg_stdSymplecticBilinForm hndC (hdim ▸ hn)
  exact ⟨e.symm.trans f⟩

universe w in
/-- **Linear Darboux theorem**, over any field `k`. Let `V` be a finite-dimensional
`k`-vector space and `B` an alternating, nondegenerate bilinear form on `V`. Then `dim V = 2n`
is even; `V` has a symplectic basis `uⱼ = b (Sum.inr j)`, `vⱼ = b (Sum.inl j)`, with
`B(uᵢ, uⱼ) = B(vᵢ, vⱼ) = 0` and `B(uᵢ, vⱼ) = δᵢⱼ`; there is a linear isomorphism
`Ψ : (Fin n ⊕ Fin n → k) ≃ V` with `Ψ^* B = ω₀ = -stdSymplecticBilinForm k n`; and every
space of the same dimension with a nondegenerate alternating form is isometric to `(V, B)`.

Milestone: *Linear Darboux theorem*. -/
theorem exists_basis_and_isometryEquiv (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ n : ℕ, finrank k V = 2 * n ∧
      (∃ b : Basis (Fin n ⊕ Fin n) k V, ∀ i j,
        B (b (.inr i)) (b (.inr j)) = 0 ∧ B (b (.inl i)) (b (.inl j)) = 0 ∧
          B (b (.inr i)) (b (.inl j)) = if i = j then 1 else 0) ∧
      Nonempty ((-stdSymplecticBilinForm k n).IsometryEquiv B) ∧
      ∀ (V' : Type w) [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (C : LinearMap.BilinForm k V'),
        C.IsAlt → C.Nondegenerate → finrank k V' = finrank k V →
          Nonempty (B.IsometryEquiv C) := by
  obtain ⟨n, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  have hn : finrank k V = 2 * n := by
    rw [finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin, two_mul]
  exact ⟨n, hn, ⟨b, apply_basis_of_toMatrix_eq_J hb⟩,
    hB.nonempty_isometryEquiv_neg_stdSymplecticBilinForm hnd hn,
    fun _ _ _ _ C hC hndC hdim ↦ hB.nonempty_isometryEquiv_of_finrank_eq hnd hC hndC hdim.symm⟩

end LinearMap.BilinForm.IsAlt

namespace SymplecticGeometry

open TauCeti

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- **Linear Darboux theorem** over `ℝ`, for the standard model `(StdSpace ι, ω₀)`: a symplectic
vector space of dimension `2 · #ι` has a linear symplectomorphism `Ψ : StdSpace ι ≃ V`, that is
`Ψ^* ω = ω₀`. -/
theorem exists_isSymplectomorphism_stdForm {ι : Type*} [Fintype ι] (ω : SymplecticForm V)
    (h : finrank ℝ V = 2 * Fintype.card ι) :
    ∃ e : StdSpace ι ≃ₗ[ℝ] V, (stdForm ι).IsSymplectomorphism ω e :=
  SymplecticForm.exists_isSymplectomorphism _ _ <| by
    rw [h, finrank_euclideanSpace, Fintype.card_sum, two_mul]

/-- **Linear Darboux theorem** over `ℝ`: a finite-dimensional symplectic vector space has even
dimension `2n`, and a linear symplectomorphism `Ψ : ℝ²ⁿ ≃ V` from the standard model,
`Ψ^* ω = ω₀`. -/
theorem exists_isSymplectomorphism_stdForm_fin (ω : SymplecticForm V) :
    ∃ n : ℕ, finrank ℝ V = 2 * n ∧
      ∃ e : StdSpace (Fin n) ≃ₗ[ℝ] V, (stdForm (Fin n)).IsSymplectomorphism ω e := by
  obtain ⟨n, hn⟩ := ω.isAlt.even_finrank ω.nondegenerate
  rw [← two_mul] at hn
  exact ⟨n, hn, exists_isSymplectomorphism_stdForm ω (by rw [hn, Fintype.card_fin])⟩

end SymplecticGeometry

end
