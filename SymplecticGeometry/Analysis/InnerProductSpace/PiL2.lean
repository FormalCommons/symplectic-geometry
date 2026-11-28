/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Euclidean.Space

/-!
# Euclidean space: matrices, reindexing and the standard basis

A square matrix `M` indexed by `m` acts on `EuclideanSpace 𝕜 m` by `Matrix.toEuclideanLin`.
This file shows that moving the coordinates along `e : m ≃ n`, by Mathlib's
`LinearIsometryEquiv.piLpCongrLeft`, turns this action into that of `Matrix.reindex e e M`.
It proves Cauchy–Schwarz for the Hermitian product `star z ⬝ᵥ v` on `ι → 𝕜`, and computes the
Hermitian square `star z ⬝ᵥ z` as the squared Euclidean norm. It also places
the standard basis vectors of `EuclideanSpace 𝕜 ι` on the unit sphere, and shows
that splitting `EuclideanSpace 𝕜 (ι ⊕ κ)` into two blocks by `EuclideanSpace.sumEquivProd`
preserves the squared norm, and gives the coordinates of the inverse map. Tau Ceti's
`EuclideanSpace.sumEquivProd_apply_fst` and `EuclideanSpace.sumEquivProd_apply_snd` give those
of the two blocks.

## Main results

* `Matrix.piLpCongrLeft_toEuclideanLin_apply`: `e (M z) = (reindex e e M) (e z)`.
* `Matrix.norm_star_dotProduct_sq_le`: Cauchy–Schwarz for the Hermitian product,
  `‖star z ⬝ᵥ v‖² ≤ (∑ᵢ ‖zᵢ‖²) (∑ᵢ ‖vᵢ‖²)`, from Mathlib's `norm_inner_le_norm`.
* `Matrix.star_dotProduct_self`: `star z ⬝ᵥ z = ∑ᵢ ‖zᵢ‖²` for `z : ι → 𝕜`, Tau Ceti's
  `EuclideanSpace.star_dotProduct_self_eq_norm_sq` written for plain coordinate vectors.
* `Matrix.re_star_dotProduct_self`: `Re (star z ⬝ᵥ z) = ∑ᵢ ‖zᵢ‖²` for `z : ι → ℂ`.
* `EuclideanSpace.single_one_mem_sphere`: each standard basis vector has norm one.
* `EuclideanSpace.norm_sq_sumEquivProd`: the squared norms of the two blocks of
  `sumEquivProd x` add up to `‖x‖²`.
* `EuclideanSpace.sumEquivProd_symm_apply_inl`, `EuclideanSpace.sumEquivProd_symm_apply_inr`:
  the coordinates of `sumEquivProd.symm p`. `simp` proves them by unfolding `sumEquivProd`, so
  they are stated for rewriting and are not `@[simp]`.
-/

public section

namespace Matrix

variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] [RCLike 𝕜]

/-- Moving the coordinates along `e : m ≃ n` intertwines the action of `M` on
`EuclideanSpace 𝕜 m` with the action of `M` reindexed along `e` on `EuclideanSpace 𝕜 n`. -/
theorem piLpCongrLeft_toEuclideanLin_apply (e : m ≃ n) (M : Matrix m m 𝕜)
    (z : EuclideanSpace 𝕜 m) :
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e (toEuclideanLin M z) =
      toEuclideanLin (reindex e e M) (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e z) := by
  ext k
  simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply, Matrix.mulVec,
    dotProduct]

/-- **Cauchy–Schwarz for the Hermitian product** `star z ⬝ᵥ v` on `ι → 𝕜`:
`‖star z ⬝ᵥ v‖² ≤ (∑ᵢ ‖zᵢ‖²) (∑ᵢ ‖vᵢ‖²)`. -/
theorem norm_star_dotProduct_sq_le {ι : Type*} [Fintype ι] (z v : ι → 𝕜) :
    ‖star z ⬝ᵥ v‖ ^ 2 ≤ (∑ i, ‖z i‖ ^ 2) * ∑ i, ‖v i‖ ^ 2 := by
  have h := norm_inner_le_norm (𝕜 := 𝕜) (WithLp.toLp 2 z) (WithLp.toLp 2 v)
  rw [EuclideanSpace.inner_eq_star_dotProduct, WithLp.ofLp_toLp, WithLp.ofLp_toLp,
    dotProduct_comm] at h
  rw [← EuclideanSpace.norm_sq_eq, ← EuclideanSpace.norm_sq_eq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- The Hermitian square of a vector `z : ι → 𝕜` is its squared Euclidean norm, as an element
of `𝕜`: `star z ⬝ᵥ z = ∑ᵢ ‖zᵢ‖²`. -/
theorem star_dotProduct_self {ι : Type*} [Fintype ι] (z : ι → 𝕜) :
    star z ⬝ᵥ z = ((∑ i, ‖z i‖ ^ 2 : ℝ) : 𝕜) := by
  have h := EuclideanSpace.star_dotProduct_self_eq_norm_sq (WithLp.toLp 2 z)
  rwa [WithLp.ofLp_toLp, EuclideanSpace.norm_sq_eq] at h

/-- The real part of the Hermitian square of a complex vector is its squared Euclidean norm:
`Re (star z ⬝ᵥ z) = ∑ᵢ ‖zᵢ‖²`. -/
theorem re_star_dotProduct_self {ι : Type*} [Fintype ι] (z : ι → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  rw [star_dotProduct_self, RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re]

end Matrix

namespace EuclideanSpace

/-- A standard basis vector of `EuclideanSpace 𝕜 ι` lies on the unit sphere. -/
theorem single_one_mem_sphere {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι] (i : ι) :
    EuclideanSpace.single i (1 : 𝕜) ∈ Metric.sphere (0 : EuclideanSpace 𝕜 ι) 1 := by
  simp

/-- The squared norms of the two blocks of `EuclideanSpace.sumEquivProd x` add up to `‖x‖²`. -/
theorem norm_sq_sumEquivProd {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : EuclideanSpace 𝕜 (ι ⊕ κ)) :
    ‖(sumEquivProd x).1‖ ^ 2 + ‖(sumEquivProd x).2‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq x, Fintype.sum_sum_type, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp

section sumEquivProd

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The coordinate `Sum.inl i` of the point of `EuclideanSpace 𝕜 (ι ⊕ κ)` that corresponds to
`p` is the coordinate `i` of `p.1`. -/
theorem sumEquivProd_symm_apply_inl (p : EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ) (i : ι) :
    sumEquivProd.symm p (Sum.inl i) = p.1 i := by
  simp

/-- The coordinate `Sum.inr j` of the point of `EuclideanSpace 𝕜 (ι ⊕ κ)` that corresponds to
`p` is the coordinate `j` of `p.2`. -/
theorem sumEquivProd_symm_apply_inr (p : EuclideanSpace 𝕜 ι × EuclideanSpace 𝕜 κ) (j : κ) :
    sumEquivProd.symm p (Sum.inr j) = p.2 j := by
  simp

end sumEquivProd

end EuclideanSpace

end
