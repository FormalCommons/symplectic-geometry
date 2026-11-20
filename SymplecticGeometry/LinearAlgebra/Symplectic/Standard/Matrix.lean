/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Analysis.Complex.Euclidean.Matrix

/-!
# The matrix dictionary for the standard model

A real matrix `A` indexed by `ι ⊕ ι` acts on `StdSpace ι` through `Matrix.toEuclideanLin`, with
no reindexing. This file translates the matrix conditions of linear symplectic geometry into
conditions on that map.

* `SymplecticGeometry.mem_symplecticGroup_iff_forall_stdForm`: `A` lies in
  `Matrix.symplecticGroup ι ℝ` (that is, `Aᵀ J A = J`) if and only if its map preserves `ω₀`,
  `ω₀(A v, A w) = ω₀(v, w)` for all `v, w`.
* `SymplecticGeometry.mem_symplecticGroup_iff_isSymplectomorphism`: the same in terms of Tau Ceti's
  `SymplecticForm.IsSymplectomorphism`, for a linear automorphism `e` of `StdSpace ι` and its
  matrix `Matrix.toEuclideanLin.symm e`.
* `SymplecticGeometry.commute_toEuclideanLin_stdComplexStructure_iff`: `A` commutes with
  `Matrix.J ι ℝ` if and only if its map commutes with `J₀`.
* `TauCeti.conj_complexToRealEuclidean_toLin'`: conjugating the complex-linear map of
  a complex matrix `A` by `complexToRealEuclidean ι` gives the map of its realification
  `Matrix.realify A`. With `A = I • 1`, whose realification is `Matrix.J ι ℝ`
  (Tau Ceti's `Matrix.realify_I_smul_one`), this recovers
  `stdComplexStructure_eq_toEuclideanLin_J`.

The conventions are those of `SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic`, which
follow McDuff–Salamon, Section 2.1.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
-/

public section

namespace SymplecticGeometry

open TauCeti Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A real matrix `A` indexed by `ι ⊕ ι` is symplectic, `Aᵀ J A = J`, if and only if its map
`Matrix.toEuclideanLin A` preserves the standard symplectic form:
`ω₀(A v, A w) = ω₀(v, w)` for all `v, w`. Such an `A` is automatically invertible. -/
theorem mem_symplecticGroup_iff_forall_stdForm {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} :
    A ∈ symplecticGroup ι ℝ ↔
      ∀ v w, stdForm ι (A.toEuclideanLin v) (A.toEuclideanLin w) = stdForm ι v w := by
  have base : ∀ v w : StdSpace ι, stdForm ι v w = -toBilin' (J ι ℝ) v.ofLp w.ofLp :=
    fun v w ↦ LinearMap.congr_fun₂ stdForm_toBilinForm v w
  have key : ∀ v w : StdSpace ι, stdForm ι (A.toEuclideanLin v) (A.toEuclideanLin w) =
      -toBilin' (Aᵀ * J ι ℝ * A) v.ofLp w.ofLp := by
    intro v w
    rw [← Matrix.toBilin'_comp]
    exact LinearMap.congr_fun₂ stdForm_toBilinForm _ _
  rw [SymplecticGroup.mem_iff']
  constructor
  · intro h v w
    rw [key, h, base]
  · intro h
    refine (Matrix.toBilin' (R₁ := ℝ)).injective (LinearMap.ext₂ fun v w ↦ ?_)
    have := h (WithLp.toLp 2 v) (WithLp.toLp 2 w)
    rwa [key, base, neg_inj] at this

/-- A linear automorphism `e` of `StdSpace ι` is a symplectomorphism of `ω₀` if and only if its
matrix `Matrix.toEuclideanLin.symm e` lies in `Matrix.symplecticGroup ι ℝ`. -/
theorem mem_symplecticGroup_iff_isSymplectomorphism (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι) :
    Matrix.toEuclideanLin.symm e.toLinearMap ∈ symplecticGroup ι ℝ ↔
      (stdForm ι).IsSymplectomorphism (stdForm ι) e := by
  rw [mem_symplecticGroup_iff_forall_stdForm, LinearEquiv.apply_symm_apply,
    SymplecticForm.isSymplectomorphism_iff]
  simp

/-- A real matrix `A` indexed by `ι ⊕ ι` commutes with `Matrix.J ι ℝ` if and only if its map
`Matrix.toEuclideanLin A` commutes with the standard complex structure `J₀`. -/
theorem commute_toEuclideanLin_stdComplexStructure_iff {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} :
    Commute (Matrix.toEuclideanLin A) (stdComplexStructure ι).toLinearMap ↔
      Commute A (J ι ℝ) := by
  rw [stdComplexStructure_eq_toEuclideanLin_J]
  exact commute_map_iff (f := toLpLinAlgEquiv (R := ℝ) (n := ι ⊕ ι) 2)
    (toLpLinAlgEquiv 2).injective

end SymplecticGeometry

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugating the complex-linear map of a complex matrix `A` by `complexToRealEuclidean ι`,
which splits a vector of `ι → ℂ` into its real and imaginary parts, gives the map of the
realification `Matrix.realify A` on `EuclideanSpace ℝ (ι ⊕ ι)`. -/
theorem conj_complexToRealEuclidean_toLin' (A : Matrix ι ι ℂ) :
    (complexToRealEuclidean ι).toLinearEquiv.conj ((Matrix.toLin' A).restrictScalars ℝ) =
      Matrix.toEuclideanLin A.realify := by
  ext1 z
  simpa using complexToRealEuclidean_mulVec A ((complexToRealEuclidean ι).symm z)

end TauCeti

end
