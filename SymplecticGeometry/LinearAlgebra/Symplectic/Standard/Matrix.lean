/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic
public import TauCeti.Analysis.Complex.Euclidean.Matrix
public import TauCeti.Analysis.Matrix.EuclideanLin
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Sum
import SymplecticGeometry.LinearAlgebra.Symplectic.Compatible
import SymplecticGeometry.LinearAlgebra.Matrix.Block
import SymplecticGeometry.LinearAlgebra.Matrix.PosDef.Block
import SymplecticGeometry.LinearAlgebra.Matrix.SymplecticGroup.Basic
import SymplecticGeometry.LinearAlgebra.Matrix.Symmetric
import SymplecticGeometry.LinearAlgebra.ComplexStructure.Action
import TauCeti.LinearAlgebra.Matrix.SesquilinearForm

/-!
# The matrix dictionary for the standard model

A real matrix `A` indexed by `ι ⊕ ι` acts on `StdSpace ι` through `Matrix.toEuclideanLin`, with
no reindexing. This file translates the matrix conditions of linear symplectic geometry into
conditions on that map.

* `SymplecticGeometry.stdForm_apply_toEuclideanLin`: `ω₀(v, A w) = vᵀ (-J₀ A) w`, where
  `J₀ = Matrix.J ι ℝ`; `SymplecticGeometry.stdForm_toEuclideanLin_toEuclideanLin`:
  `ω₀(A u, B v) = uᵀ (Aᵀ (-J₀) B) v` for matrices `A`, `B` with `2n` rows.
* `SymplecticGeometry.mem_symplecticGroup_iff_forall_stdForm`: `A` lies in
  `Matrix.symplecticGroup ι ℝ` (that is, `Aᵀ J A = J`) if and only if its map preserves `ω₀`,
  `ω₀(A v, A w) = ω₀(v, w)` for all `v, w`;
  `SymplecticGeometry.mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM` is the same for
  `Matrix.toEuclideanCLM A`.
* `SymplecticGeometry.mem_symplecticGroup_iff_isSymplectomorphism`: the same in terms of Tau Ceti's
  `SymplecticForm.IsSymplectomorphism`, for a linear automorphism `e` of `StdSpace ι` and its
  matrix `Matrix.toEuclideanLin.symm e`.
* `SymplecticGeometry.toEuclideanCLM_symm_mem_symplecticGroup_iff`: the same for a continuous
  linear automorphism `e` and its matrix `Matrix.toEuclideanCLM.symm e`.
* `SymplecticGeometry.mem_GLSymplectic_iff_isSymplectomorphism`: an invertible matrix `g` lies in
  Tau Ceti's `GLSymplectic ι ℝ` if and only if its linear automorphism of `StdSpace ι`, through
  `Matrix.toEuclideanCLE`, is a symplectomorphism of `ω₀`.
* `SymplecticGeometry.commute_toEuclideanLin_stdComplexStructure_iff`: `A` commutes with
  `Matrix.J ι ℝ` if and only if its map commutes with `J₀`.
* `SymplecticGeometry.toEuclideanLin_mem_tangentSpace_stdComplexStructure_iff`: the map of `A`
  anticommutes with `J₀` if and only if `A * J₀ + J₀ * A = 0`.
* `SymplecticGeometry.associatedBilinForm_stdForm_apply` and
  `SymplecticGeometry.toMatrix_associatedBilinForm_stdForm`: for a complex structure `J` with
  matrix `M`, the matrix `-J₀ M` is the Gram matrix of the metric `g_J(v, w) = ω₀(v, J w)`.
* `SymplecticGeometry.invariant_stdForm_iff_isSymm`, `SymplecticGeometry.tames_stdForm_iff` and
  `SymplecticGeometry.compatible_stdForm_iff_posDef`: `J` preserves `ω₀`, is tamed by `ω₀`, or
  is `ω₀`-compatible exactly when `-J₀ M` is symmetric, has a positive definite quadratic form,
  or is a positive definite matrix (McDuff–Salamon, Lemma 2.5.5).
* `SymplecticGeometry.neg_J_mul_mem_symplecticGroup_of_invariant`: if `J` preserves `ω₀`, then
  `-J₀ M` is a symplectic matrix.
* `TauCeti.conj_complexToRealEuclidean_toLin'`: conjugating the complex-linear map of
  a complex matrix `A` by `complexToRealEuclidean ι` gives the map of its realification
  `Matrix.realify A`. With `A = I • 1`, whose realification is `Matrix.J ι ℝ`
  (Tau Ceti's `Matrix.realify_I_smul_one`), this recovers
  `stdComplexStructure_eq_toEuclideanLin_J`.
* `SymplecticGeometry.StdSpace.complexEuclideanEquiv_toEuclideanCLM`: the same through
  `StdSpace.complexEuclideanEquiv`, vector by vector.
* `SymplecticGeometry.posDef_toBlocks₂₁_of_compatible` and
  `SymplecticGeometry.toBlocks₂₂_eq_neg_transpose_of_invariant`: the matrix `M` of an
  `ω₀`-compatible complex structure has positive definite lower left block `M₂₁`, and
  `M₂₂ = -M₁₁ᵀ` as soon as the structure preserves `ω₀`.
* `SymplecticGeometry.isSymm_toBlocks₁₁_mul_inv_toBlocks₂₁_of_compatible`: for such `M`, the
  product `M₁₁ M₂₁⁻¹` is symmetric.
* `SymplecticGeometry.StdSpace.sumEquiv_toEuclideanLin_symplecticSum`: through the splitting
  `StdSpace.sumEquiv ι κ`, the map of Tau Ceti's `Matrix.symplecticSum A B` is the product of the
  maps of `A` and `B`.
* `SymplecticGeometry.StdSpace.equivComplex_toEuclideanLin_realify_diagonal`: on the standard
  plane read as `ℂ`, the realification of a `1 × 1` complex matrix `(c)` acts as multiplication
  by `c`.

The conventions are those of `SymplecticGeometry.LinearAlgebra.Symplectic.Standard.Basic`, which
follow McDuff–Salamon, Section 2.1.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017]
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

/-- `ω₀(A u, B v) = uᵀ (Aᵀ (-J₀) B) v` for real matrices `A` and `B` with `2n` rows, where
`J₀ = Matrix.J ι ℝ`: the Gram matrix of `ω₀` on the columns of `A` and `B`. -/
theorem stdForm_toEuclideanLin_toEuclideanLin {κ μ : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype μ] [DecidableEq μ] (A : Matrix (ι ⊕ ι) κ ℝ) (B : Matrix (ι ⊕ ι) μ ℝ)
    (u : EuclideanSpace ℝ κ) (v : EuclideanSpace ℝ μ) :
    stdForm ι (toEuclideanLin A u) (toEuclideanLin B v) =
      u.ofLp ⬝ᵥ ((Aᵀ * -J ι ℝ * B) *ᵥ v.ofLp) := by
  have h := stdForm_apply_toEuclideanLin 1 (toEuclideanLin A u) (toEuclideanLin B v)
  rw [toLpLin_one, LinearMap.id_apply, Matrix.mul_one] at h
  rw [h]
  simp only [toLpLin_apply]
  rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec u.ofLp,
    vecMul_transpose]

/-- A real matrix `A` indexed by `ι ⊕ ι` is symplectic, `Aᵀ J A = J`, if and only if its map
`Matrix.toEuclideanLin A` preserves the standard symplectic form:
`ω₀(A v, A w) = ω₀(v, w)` for all `v, w`. Such an `A` is automatically invertible. -/
theorem mem_symplecticGroup_iff_forall_stdForm {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} :
    A ∈ symplecticGroup ι ℝ ↔
      ∀ v w, stdForm ι (A.toEuclideanLin v) (A.toEuclideanLin w) = stdForm ι v w := by
  have h := transpose_map_mul_mul_eq_self_iff (σ := RingHom.id ℝ) (Q := -J ι ℝ) (g := A)
  rw [RingHom.coe_id, map_id, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h
  rw [SymplecticGroup.mem_iff', h, (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).symm.forall_congr_left]
  refine forall_congr' fun v ↦ (WithLp.linearEquiv 2 ℝ (ι ⊕ ι → ℝ)).symm.forall_congr_left.trans
    (forall_congr' fun w ↦ ?_)
  have base (v w : StdSpace ι) : stdForm ι v w = v.ofLp ⬝ᵥ (-J ι ℝ *ᵥ w.ofLp) := by
    simpa using stdForm_apply_toEuclideanLin 1 v w
  simp [base, toLpLin_apply]

/-- A real matrix `A` indexed by `ι ⊕ ι` is symplectic if and only if its continuous linear map
`Matrix.toEuclideanCLM A` preserves the standard symplectic form: `ω₀(A v, A w) = ω₀(v, w)` for
all `v, w`. This is `mem_symplecticGroup_iff_forall_stdForm` for `Matrix.toEuclideanCLM`. -/
theorem mem_symplecticGroup_iff_forall_stdForm_toEuclideanCLM {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} :
    A ∈ symplecticGroup ι ℝ ↔
      ∀ v w, stdForm ι (toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) A v)
        (toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ) A w) = stdForm ι v w := by
  simp only [← coe_toEuclideanCLM_eq_toEuclideanLin, ContinuousLinearMap.coe_coe,
    mem_symplecticGroup_iff_forall_stdForm]

/-- A linear automorphism `e` of `StdSpace ι` is a symplectomorphism of `ω₀` if and only if its
matrix `Matrix.toEuclideanLin.symm e` lies in `Matrix.symplecticGroup ι ℝ`. -/
theorem mem_symplecticGroup_iff_isSymplectomorphism (e : StdSpace ι ≃ₗ[ℝ] StdSpace ι) :
    Matrix.toEuclideanLin.symm e.toLinearMap ∈ symplecticGroup ι ℝ ↔
      (stdForm ι).IsSymplectomorphism (stdForm ι) e := by
  rw [mem_symplecticGroup_iff_forall_stdForm, LinearEquiv.apply_symm_apply,
    SymplecticForm.isSymplectomorphism_iff]
  simp

/-- A continuous linear automorphism `e` of `StdSpace ι` is a symplectomorphism of `ω₀` if and
only if its matrix `Matrix.toEuclideanCLM.symm e` lies in `Matrix.symplecticGroup ι ℝ`. It is
the `Matrix.toEuclideanCLM` form of `mem_symplecticGroup_iff_isSymplectomorphism`: the two
matrices agree by definition. -/
theorem toEuclideanCLM_symm_mem_symplecticGroup_iff (e : StdSpace ι ≃L[ℝ] StdSpace ι) :
    (toEuclideanCLM (n := ι ⊕ ι) (𝕜 := ℝ)).symm (e : StdSpace ι →L[ℝ] StdSpace ι) ∈
        symplecticGroup ι ℝ ↔
      (stdForm ι).IsSymplectomorphism (stdForm ι) e.toLinearEquiv :=
  mem_symplecticGroup_iff_isSymplectomorphism e.toLinearEquiv

/-- An invertible real matrix `g` indexed by `ι ⊕ ι` lies in `GLSymplectic ι ℝ` if and only if
its linear automorphism `Matrix.toEuclideanCLE g` of `StdSpace ι` is a symplectomorphism of
`ω₀`. -/
theorem mem_GLSymplectic_iff_isSymplectomorphism (g : GL (ι ⊕ ι) ℝ) :
    g ∈ GLSymplectic ι ℝ ↔ (stdForm ι).IsSymplectomorphism (stdForm ι)
      ((g : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ).toEuclideanCLE g.det_ne_zero).toLinearEquiv := by
  rw [GLSymplectic.mem_iff_mem_symplecticGroup, mem_symplecticGroup_iff_forall_stdForm,
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

/-- The map `Matrix.toEuclideanLin A` of a real matrix `A` indexed by `ι ⊕ ι` lies in the
tangent space of `J₀`, that is, anticommutes with `J₀`, if and only if
`A * Matrix.J ι ℝ + Matrix.J ι ℝ * A = 0`. -/
theorem toEuclideanLin_mem_tangentSpace_stdComplexStructure_iff
    {A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ} :
    Matrix.toEuclideanLin A ∈ (stdComplexStructure ι).tangentSpace ↔
      A * J ι ℝ + J ι ℝ * A = 0 := by
  rw [AlmostComplexStructure.mem_tangentSpace, stdComplexStructure_eq_toEuclideanLin_J,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← toLpLin_mul_same, ← toLpLin_mul_same,
    ← map_add, LinearEquiv.map_eq_zero_iff]

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

/-- For a complex structure `J` of `StdSpace ι` that preserves `ω₀`, with matrix `M`, the Gram
matrix `-J₀ M` of `ω₀(·, J ·)` is symplectic. -/
theorem neg_J_mul_mem_symplecticGroup_of_invariant {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Invariant J) :
    -Matrix.J ι ℝ * toEuclideanLin.symm J.toLinearMap ∈ symplecticGroup ι ℝ := by
  refine Submonoid.mul_mem _ (SymplecticGroup.neg_mem (SymplecticGroup.J_mem ι ℝ)) ?_
  rw [mem_symplecticGroup_iff_forall_stdForm, LinearEquiv.apply_symm_apply]
  exact (TauCeti.SymplecticForm.invariant_iff _ _).1 hJ

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

/-- The lower left block `M₂₁` of the matrix `M` of an `ω₀`-compatible complex structure is
positive definite: it is the upper left block of the positive definite matrix `-J₀ M`, the Gram
matrix of `ω₀(·, J ·)`. -/
theorem posDef_toBlocks₂₁_of_compatible {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Compatible J) : (toEuclideanLin.symm J.toLinearMap).toBlocks₂₁.PosDef := by
  simpa only [neg_J_mul_eq_fromBlocks, toBlocks_fromBlocks₁₁] using
    (compatible_stdForm_iff_posDef.1 hJ).toBlocks₁₁

/-- The matrix of an `ω₀`-compatible complex structure has invertible lower left block. -/
theorem isUnit_det_toBlocks₂₁_of_compatible {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Compatible J) :
    IsUnit (toEuclideanLin.symm J.toLinearMap).toBlocks₂₁.det :=
  (isUnit_iff_isUnit_det _).1 (posDef_toBlocks₂₁_of_compatible hJ).isUnit

/-- For the matrix `M` of a complex structure `J` on `StdSpace ι` that preserves `ω₀`,
`ω₀(J v, J w) = ω₀(v, w)`, the lower right block is `M₂₂ = -M₁₁ᵀ`: it is the upper right block
of the symmetric matrix `-J₀ M`, whose lower left block is `-M₁₁`. -/
theorem toBlocks₂₂_eq_neg_transpose_of_invariant {J : AlmostComplexStructure (StdSpace ι)}
    (hJ : (stdForm ι).Invariant J) :
    (toEuclideanLin.symm J.toLinearMap).toBlocks₂₂ =
      -(toEuclideanLin.symm J.toLinearMap).toBlocks₁₁ᵀ := by
  have h := congrArg toBlocks₁₂ (invariant_stdForm_iff_isSymm.1 hJ).eq
  rw [neg_J_mul_eq_fromBlocks, fromBlocks_transpose, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₁₂,
    transpose_neg] at h
  exact h.symm

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

namespace SymplecticGeometry

namespace StdSpace

open Matrix TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Through `StdSpace.complexEuclideanEquiv`, a complex matrix acts on `StdSpace ι` as its
realification. -/
theorem complexEuclideanEquiv_toEuclideanCLM (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    complexEuclideanEquiv ι (toEuclideanCLM (𝕜 := ℂ) A v) =
      toEuclideanLin A.realify (complexEuclideanEquiv ι v) := by
  rw [complexEuclideanEquiv_def]
  exact complexToRealEuclidean_mulVec A v.ofLp

end StdSpace

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

/-- Through the splitting `StdSpace.sumEquiv ι κ`, Tau Ceti's symplectic direct sum
`Matrix.symplecticSum A B` acts on `StdSpace (ι ⊕ κ)` as `A` on the first factor and `B` on the
second. -/
theorem StdSpace.sumEquiv_toEuclideanLin_symplecticSum {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) (B : Matrix (κ ⊕ κ) (κ ⊕ κ) ℝ) (z : StdSpace (ι ⊕ κ)) :
    sumEquiv ι κ (toEuclideanLin (symplecticSum A B) z) =
      (toEuclideanLin A (sumEquiv ι κ z).1, toEuclideanLin B (sumEquiv ι κ z).2) := by
  rw [symplecticSum_def]
  apply Prod.ext <;> apply StdSpace.ext <;> funext i <;>
    simp [sumEquiv_def, fromBlocks_mulVec, Function.comp_def]

/-- On the standard plane read as `ℂ` through `StdSpace.equivComplex`, the map of the
realification of the `1 × 1` complex matrix `(c)` is multiplication by `c`. -/
theorem StdSpace.equivComplex_toEuclideanLin_realify_diagonal [Unique ι] (c : ℂ)
    (z : StdSpace ι) :
    equivComplex ι (toEuclideanLin (diagonal fun _ : ι ↦ c).realify z) = c * equivComplex ι z := by
  obtain ⟨u, rfl⟩ := (complexToRealEuclidean ι).surjective z
  rw [← complexToRealEuclidean_mulVec]
  simp

end SymplecticGeometry

end
