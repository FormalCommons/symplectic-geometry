/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Analysis.Complex.Euclidean.Matrix
import SymplecticGeometry.LinearAlgebra.Matrix.Block
import SymplecticGeometry.LinearAlgebra.Matrix.Symmetric

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
* `SymplecticGeometry.posDef_toBlocks₂₁_of_compatible` and
  `SymplecticGeometry.toBlocks₂₂_eq_neg_transpose_of_invariant`: the matrix `M` of an
  `ω₀`-compatible complex structure has positive definite lower left block `M₂₁`, and
  `M₂₂ = -M₁₁ᵀ` as soon as the structure preserves `ω₀`.
* `SymplecticGeometry.isSymm_toBlocks₁₁_mul_inv_toBlocks₂₁_of_compatible`: for such `M`, the
  product `M₁₁ M₂₁⁻¹` is symmetric.

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

/-- `ω₀(v, M w)` for `v = (a, b)` and `w = (c, d)`, in terms of the blocks of `M`. -/
theorem stdForm_toLp_sumElim_toEuclideanLin (M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (a b c d : ι → ℝ) :
    stdForm ι (WithLp.toLp 2 (Sum.elim a b)) (toEuclideanLin M (WithLp.toLp 2 (Sum.elim c d))) =
      a ⬝ᵥ (M.toBlocks₂₁ *ᵥ c + M.toBlocks₂₂ *ᵥ d) -
        b ⬝ᵥ (M.toBlocks₁₁ *ᵥ c + M.toBlocks₁₂ *ᵥ d) := by
  simp [StdSpace.x_apply, StdSpace.y_apply, toLpLin_apply, mulVec, dotProduct,
    Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Finset.sum_sub_distrib]

/-- The lower left block `M₂₁` of the matrix `M` of an `ω₀`-compatible complex structure is
positive definite: it is the Gram matrix of `ω₀(·, J ·)` on the `x`-coordinates. -/
theorem posDef_toBlocks₂₁_of_compatible {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Compatible J) : (toEuclideanLin.symm J.toLinearMap).toBlocks₂₁.PosDef := by
  set M := toEuclideanLin.symm J.toLinearMap
  have hJM : ∀ v, J v = toEuclideanLin M v := fun v ↦ by simp [M]
  have hswap := hJ.invariant.associatedBilinForm_apply_swap
  have key : ∀ a b, stdForm ι (WithLp.toLp 2 (Sum.elim a 0)) (J (WithLp.toLp 2 (Sum.elim b 0))) =
      a ⬝ᵥ (M.toBlocks₂₁ *ᵥ b) := fun a b ↦ by
    rw [hJM, stdForm_toLp_sumElim_toEuclideanLin]
    simp
  refine posDef_iff_dotProduct_mulVec.2 ⟨IsHermitian.ext fun i j ↦ ?_, fun a ha ↦ ?_⟩
  · have := hswap (WithLp.toLp 2 (Sum.elim (Pi.single j 1) 0))
      (WithLp.toLp 2 (Sum.elim (Pi.single i 1) 0))
    rw [key, key] at this
    simpa [mulVec_single_one] using this
  · have hv : WithLp.toLp 2 (Sum.elim a 0) ≠ (0 : StdSpace ι) := by
      intro h
      apply ha
      funext i
      simpa using congrFun (congrArg WithLp.ofLp h) (Sum.inl i)
    simpa [key] using hJ.tames _ hv

/-- The matrix of an `ω₀`-compatible complex structure has invertible lower left block. -/
theorem isUnit_det_toBlocks₂₁_of_compatible {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Compatible J) :
    IsUnit (toEuclideanLin.symm J.toLinearMap).toBlocks₂₁.det :=
  (isUnit_iff_isUnit_det _).1 (posDef_toBlocks₂₁_of_compatible hJ).isUnit

/-- For the matrix `M` of a complex structure `J` on `StdSpace ι` that preserves `ω₀`,
`ω₀(J v, J w) = ω₀(v, w)`, the lower right block is `M₂₂ = -M₁₁ᵀ`. -/
theorem toBlocks₂₂_eq_neg_transpose_of_invariant {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Invariant J) :
    (toEuclideanLin.symm J.toLinearMap).toBlocks₂₂ =
      -(toEuclideanLin.symm J.toLinearMap).toBlocks₁₁ᵀ := by
  set M := toEuclideanLin.symm J.toLinearMap
  have hJM : ∀ v, J v = toEuclideanLin M v := fun v ↦ by simp [M]
  ext i j
  have := hJ.associatedBilinForm_apply_swap
    (WithLp.toLp 2 (Sum.elim (Pi.single i 1) 0)) (WithLp.toLp 2 (Sum.elim 0 (Pi.single j 1)))
  rw [hJM, hJM, stdForm_toLp_sumElim_toEuclideanLin, stdForm_toLp_sumElim_toEuclideanLin] at this
  simpa [mulVec_single_one] using this

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

/-- The matrix of a complex structure on a Euclidean space squares to `-1`. -/
theorem AlmostComplexStructure.toEuclideanLin_symm_mul_self {n : Type*} [Fintype n]
    [DecidableEq n] (J : AlmostComplexStructure (EuclideanSpace ℝ n)) :
    Matrix.toEuclideanLin.symm J.toLinearMap * Matrix.toEuclideanLin.symm J.toLinearMap = -1 := by
  rw [← Matrix.toLpLin_symm_comp, J.square_neg, map_neg]
  simp

end TauCeti

namespace SymplecticGeometry

open TauCeti Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For the matrix `M` of an `ω₀`-compatible complex structure, the product `M₁₁ M₂₁⁻¹` of the
upper left block and the inverse of the lower left block is symmetric. -/
theorem isSymm_toBlocks₁₁_mul_inv_toBlocks₂₁_of_compatible
    {J : AlmostComplexStructure (StdSpace ι)} (hJ : (stdForm ι).Compatible J) :
    ((toEuclideanLin.symm J.toLinearMap).toBlocks₁₁ *
      (toEuclideanLin.symm J.toLinearMap).toBlocks₂₁⁻¹).IsSymm := by
  set M := toEuclideanLin.symm J.toLinearMap
  have hC := posDef_toBlocks₂₁_of_compatible hJ
  have h₂₁ :=
    toBlocks₂₁_mul_toBlocks₁₁_add_of_mul_self_eq_neg_one J.toEuclideanLin_symm_mul_self
  have hCt : M.toBlocks₂₁ᵀ = M.toBlocks₂₁ := isHermitian_iff_isSymm.1 hC.isHermitian
  refine isSymm_mul_nonsing_inv_of_transpose_mul_eq ?_
  rw [hCt, ← neg_neg M.toBlocks₁₁ᵀ, ← toBlocks₂₂_eq_neg_transpose_of_invariant hJ.invariant,
    Matrix.neg_mul, ← eq_neg_of_add_eq_zero_left h₂₁]

end SymplecticGeometry

end
