/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Symplectic.WittExtension
public import TauCeti.LinearAlgebra.BilinearForm.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Isometry
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.LinearAlgebra.Dimension.Basis
public import TauCeti.RepresentationTheory.ClassicalGroups.Symplectic
public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic

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
* `TauCeti.isAlt_neg_stdSymplecticBilinForm`, `TauCeti.neg_stdSymplecticBilinForm_nondegenerate`
  and `TauCeti.neg_stdSymplecticBilinForm_single_single`: `ω₀` is alternating and
  nondegenerate, and its values on the standard basis.
* `LinearMap.BilinForm.IsAlt.equivalent_neg_stdSymplecticBilinForm`: a space of
  dimension `2n` with a nondegenerate alternating form is isometric to `(k²ⁿ, ω₀)`.
* `LinearMap.BilinForm.IsAlt.equivalent_iff_finrank_eq`: two such spaces are isometric exactly
  when their dimensions agree.
* `LinearMap.BilinForm.IsAlt.exists_basis_and_equivalent`: the linear Darboux theorem, the
  three statements together.
* `LinearMap.BilinForm.apply_sum_smul_add_smul_eq_left_coeff` and
  `LinearMap.BilinForm.IsAlt.apply_sum_smul_add_smul_eq_neg_right_coeff`: for vectors `aᵢ`, `bᵢ`
  with the Darboux relations, pairing `∑ᵢ (cᵢ aᵢ + dᵢ bᵢ)` with `bⱼ` and with `aⱼ` gives `cⱼ`
  and `-dⱼ`.
* `LinearMap.BilinForm.apply_sub_sum_apply_smul_add_smul_snd_eq_zero` and
  `LinearMap.BilinForm.IsAlt.apply_sub_sum_apply_smul_add_smul_fst_eq_zero`: for such vectors,
  the projection `v ↦ v - ∑ᵢ (B(v, bᵢ) aᵢ - B(v, aᵢ) bᵢ)` lands in the `B`-orthogonal of all
  `aⱼ` and `bⱼ`. For a single pair, this is Tau Ceti's
  `LinearMap.BilinForm.IsAlt.sub_smul_add_smul_mem_orthogonal_span_pair`.
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
    simp [LinearMap.BilinForm.toMatrix_apply, Matrix.one_apply]

/-- `ω₀ = -stdSymplecticBilinForm k n` is alternating. -/
theorem isAlt_neg_stdSymplecticBilinForm : (-stdSymplecticBilinForm k n).IsAlt :=
  (isAlt_stdSymplecticBilinForm k n).neg

/-- `ω₀ = -stdSymplecticBilinForm k n` is nondegenerate. -/
theorem neg_stdSymplecticBilinForm_nondegenerate :
    (-stdSymplecticBilinForm k n).Nondegenerate :=
  TauCeti.BilinForm.nondegenerate_neg_iff.mpr (stdSymplecticBilinForm_nondegenerate k n)

/-- The values of `ω₀ = -stdSymplecticBilinForm k n` on the standard basis vectors are the
entries of `-Matrix.J`. With `xⱼ = Pi.single (Sum.inl j) 1` and `yⱼ = Pi.single (Sum.inr j) 1`,
the `simp` lemmas `Matrix.J_inl_inr` and its siblings turn this into `ω₀(xᵢ, yⱼ) = δᵢⱼ`,
`ω₀(yᵢ, xⱼ) = -δᵢⱼ` and `ω₀(xᵢ, xⱼ) = ω₀(yᵢ, yⱼ) = 0`. -/
theorem neg_stdSymplecticBilinForm_single_single (x y : Fin n ⊕ Fin n) :
    (-stdSymplecticBilinForm k n) (Pi.single x (1 : k)) (Pi.single y 1) =
      -Matrix.J (Fin n) k x y := by
  simp only [LinearMap.neg_apply, stdSymplecticBilinForm_single_single]

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
  simp [Matrix.one_apply]

/-- Let the `bᵢ` be pairwise `B`-orthogonal, with `B(aᵢ, bⱼ) = δᵢⱼ`. Then pairing
`∑ᵢ (cᵢ aᵢ + dᵢ bᵢ)` with `bⱼ` on the right gives the coefficient `cⱼ`. -/
theorem apply_sum_smul_add_smul_eq_left_coeff {κ : Type*} [Fintype κ] [DecidableEq κ]
    {a b : κ → M} (hbb : ∀ i j, B (b i) (b j) = 0)
    (hab : ∀ i j, B (a i) (b j) = if i = j then 1 else 0) (c d : κ → R) (j : κ) :
    B (∑ i, (c i • a i + d i • b i)) (b j) = c j := by
  simp [map_sum, hbb, hab]

/-- Let `B` be alternating, the `aᵢ` pairwise `B`-orthogonal, and `B(aᵢ, bⱼ) = δᵢⱼ`. Then pairing
`∑ᵢ (cᵢ aᵢ + dᵢ bᵢ)` with `aⱼ` on the right gives `-dⱼ`. -/
theorem IsAlt.apply_sum_smul_add_smul_eq_neg_right_coeff (hB : B.IsAlt) {κ : Type*} [Fintype κ]
    [DecidableEq κ] {a b : κ → M} (haa : ∀ i j, B (a i) (a j) = 0)
    (hab : ∀ i j, B (a i) (b j) = if i = j then 1 else 0) (c d : κ → R) (j : κ) :
    B (∑ i, (c i • a i + d i • b i)) (a j) = -d j := by
  have hba (i j : κ) : B (b i) (a j) = -if j = i then 1 else 0 := by
    rw [← hab j i, ← hB.neg_eq]
  simp [map_sum, haa, hba]

/-- Let the `bᵢ` be pairwise `B`-orthogonal, with `B(aᵢ, bⱼ) = δᵢⱼ`. Then the projection
`v - ∑ᵢ (B(v, bᵢ) aᵢ - B(v, aᵢ) bᵢ)` of `v` is `B`-orthogonal to each `bⱼ`. -/
theorem apply_sub_sum_apply_smul_add_smul_snd_eq_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    {a b : κ → M} (hbb : ∀ i j, B (b i) (b j) = 0)
    (hab : ∀ i j, B (a i) (b j) = if i = j then 1 else 0) (v : M) (j : κ) :
    B (v - ∑ i, (B v (b i) • a i + -B v (a i) • b i)) (b j) = 0 := by
  rw [map_sub, LinearMap.sub_apply, apply_sum_smul_add_smul_eq_left_coeff hbb hab, sub_self]

/-- Let `B` be alternating, the `aᵢ` pairwise `B`-orthogonal, and `B(aᵢ, bⱼ) = δᵢⱼ`. Then the
projection `v - ∑ᵢ (B(v, bᵢ) aᵢ - B(v, aᵢ) bᵢ)` of `v` is `B`-orthogonal to each `aⱼ`. -/
theorem IsAlt.apply_sub_sum_apply_smul_add_smul_fst_eq_zero (hB : B.IsAlt) {κ : Type*}
    [Fintype κ] [DecidableEq κ] {a b : κ → M} (haa : ∀ i j, B (a i) (a j) = 0)
    (hab : ∀ i j, B (a i) (b j) = if i = j then 1 else 0) (v : M) (j : κ) :
    B (v - ∑ i, (B v (b i) • a i + -B v (a i) • b i)) (a j) = 0 := by
  rw [map_sub, LinearMap.sub_apply, hB.apply_sum_smul_add_smul_eq_neg_right_coeff haa hab,
    neg_neg, sub_self]

end LinearMap.BilinForm

namespace LinearMap.BilinForm.IsAlt

open TauCeti

variable {k V W : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]
  {B : LinearMap.BilinForm k V} {C : LinearMap.BilinForm k W}

/-- A nondegenerate alternating form `B` on a space of dimension `2n` is isometric to the
standard model: there is a linear isomorphism `Ψ : (Fin n ⊕ Fin n → k) ≃ V` with
`B(Ψ z, Ψ w) = ω₀(z, w)`, where `ω₀ = -stdSymplecticBilinForm k n`. -/
theorem equivalent_neg_stdSymplecticBilinForm (hB : B.IsAlt)
    (hnd : B.Nondegenerate) {n : ℕ} (hn : finrank k V = 2 * n) :
    (-stdSymplecticBilinForm k n).Equivalent B := by
  obtain ⟨m, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  obtain rfl : m = n := by
    rw [finrank_eq_two_mul_card_of_basis_sum b, Fintype.card_fin] at hn
    omega
  exact ⟨((Pi.basisFun k _).reindex (Equiv.sumComm _ _)).isometryEquivOfToMatrixEq b
    ((toMatrix_reindex_sumComm_neg_stdSymplecticBilinForm k m).trans hb.symm)⟩

/-- Two finite-dimensional spaces with nondegenerate alternating forms are isometric exactly when
their dimensions agree. -/
theorem equivalent_iff_finrank_eq (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hC : C.IsAlt) (hndC : C.Nondegenerate) :
    B.Equivalent C ↔ finrank k V = finrank k W := by
  refine ⟨fun ⟨e⟩ ↦ e.toLinearEquiv.finrank_eq, fun hdim ↦ ?_⟩
  obtain ⟨n, hn⟩ := hB.even_finrank hnd
  rw [← two_mul] at hn
  exact (hB.equivalent_neg_stdSymplecticBilinForm hnd hn).symm.trans
    (hC.equivalent_neg_stdSymplecticBilinForm hndC (hdim ▸ hn))

universe w in
/-- **Linear Darboux theorem**, over any field `k`. Let `V` be a finite-dimensional
`k`-vector space and `B` an alternating, nondegenerate bilinear form on `V`. Then `dim V = 2n`
is even; `V` has a symplectic basis `uⱼ = b (Sum.inr j)`, `vⱼ = b (Sum.inl j)`, with
`B(uᵢ, uⱼ) = B(vᵢ, vⱼ) = 0` and `B(uᵢ, vⱼ) = δᵢⱼ`; there is a linear isomorphism
`Ψ : (Fin n ⊕ Fin n → k) ≃ V` with `Ψ^* B = ω₀ = -stdSymplecticBilinForm k n`; and every
space of the same dimension with a nondegenerate alternating form is isometric to `(V, B)`.

Milestone: *Linear Darboux theorem*. -/
theorem exists_basis_and_equivalent (hB : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ n : ℕ, finrank k V = 2 * n ∧
      (∃ b : Basis (Fin n ⊕ Fin n) k V, ∀ i j,
        B (b (.inr i)) (b (.inr j)) = 0 ∧ B (b (.inl i)) (b (.inl j)) = 0 ∧
          B (b (.inr i)) (b (.inl j)) = if i = j then 1 else 0) ∧
      (-stdSymplecticBilinForm k n).Equivalent B ∧
      ∀ (V' : Type w) [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
        (C : LinearMap.BilinForm k V'),
        C.IsAlt → C.Nondegenerate → finrank k V' = finrank k V → B.Equivalent C := by
  obtain ⟨n, b, hb⟩ := hB.exists_basis_toMatrix_eq_J hnd
  have hn : finrank k V = 2 * n := by
    rw [finrank_eq_two_mul_card_of_basis_sum b, Fintype.card_fin]
  exact ⟨n, hn, ⟨b, apply_basis_of_toMatrix_eq_J hb⟩,
    hB.equivalent_neg_stdSymplecticBilinForm hnd hn,
    fun _ _ _ _ C hC hndC hdim ↦ (hB.equivalent_iff_finrank_eq hnd hC hndC).mpr hdim.symm⟩

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
    rw [h, finrank_stdSpace]

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
