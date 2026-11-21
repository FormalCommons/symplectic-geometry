/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.LinearAlgebra.TotallyReal.Euclidean

/-!
# Real matrices read as complex matrices

A real matrix `P` is read as a complex matrix through the entrywise coercion
`P.map ((↑) : ℝ → ℂ)`. This file records how that coercion interacts with transposes and
conjugate transposes. It complements Tau Ceti's file of the same name
(`TauCeti.LinearAlgebra.Matrix.OfReal`).

It also relates a real `2n × n` frame `fromRows X Y` to its complex frame `X + i Y`, the
dictionary that McDuff–Salamon use to pass between Lagrangian frames in `ℝ²ⁿ` and complex
frames in `ℂⁿ` (§2.3).

## Main results

* `Matrix.map_re_add_I_smul_map_im`: every complex matrix `A` equals `Re A + i Im A`, its real
  and imaginary parts being read back over `ℂ`.
* `Matrix.map_ofReal_mul`: the coercion is multiplicative. This is Mathlib's `Matrix.map_mul` for
  `f := Complex.ofRealHom`, but stated with `ofReal` itself, so that `rw` and `simp` find it.
* `Matrix.transpose_map_ofReal_mul_map_ofReal`: `(P.map ofReal)ᵀ * Q.map ofReal` is the image of
  the real product `Pᵀ * Q`.
* `Matrix.conjTranspose_map_ofReal`: the conjugate transpose of a real matrix, read over `ℂ`, is
  its transpose.
* `Matrix.map_im_conjTranspose_mul_self`: the Gram matrix `Mᴴ M` of `M = X + i Y` has imaginary
  part `Xᵀ Y - Yᵀ X`; so it is real if `Xᵀ Y = Yᵀ X`
  (`Matrix.map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq`).
* `Matrix.range_toEuclideanLin_fromRows`: the column space of `fromRows X Y` in `ℝ²ⁿ` is the
  real image `(X + i Y) ℝⁿ` (Tau Ceti's `Matrix.realImage`), read in real coordinates through
  `TauCeti.complexToRealEuclidean`.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §2.3.
-/

public section

open Complex

namespace Matrix

variable {m n p : Type*}

/-- A complex matrix is its real part plus `i` times its imaginary part, both read over `ℂ`:
`A = Re A + i Im A`. -/
theorem map_re_add_I_smul_map_im (A : Matrix m n ℂ) :
    (A.map re).map ofReal + I • (A.map im).map ofReal = A := by
  ext i j
  simp [mul_comm I]

/-- The product of real matrices may be computed over `ℂ`. -/
theorem map_ofReal_mul [Fintype n] (P : Matrix m n ℝ) (Q : Matrix n p ℝ) :
    (P * Q).map ofReal = P.map ofReal * Q.map ofReal :=
  Matrix.map_mul (f := ofRealHom)

/-- The product `Pᵀ Q` of real matrices may be computed over `ℂ`. -/
theorem transpose_map_ofReal_mul_map_ofReal [Fintype m] (P : Matrix m n ℝ) (Q : Matrix m p ℝ) :
    (P.map ofReal)ᵀ * Q.map ofReal = (Pᵀ * Q).map ofReal := by
  rw [← transpose_map, map_ofReal_mul]

/-- A real matrix, read over `ℂ`, has its transpose as conjugate transpose. -/
@[simp]
theorem conjTranspose_map_ofReal (P : Matrix m n ℝ) : (P.map ofReal)ᴴ = (P.map ofReal)ᵀ := by
  ext i j
  simp

/-- The imaginary part of the Gram matrix `Mᴴ M` of the complex matrix `M = X + i Y`, for real
matrices `X` and `Y`, is `Xᵀ Y - Yᵀ X`. -/
theorem map_im_conjTranspose_mul_self [Fintype m] (X Y : Matrix m n ℝ) :
    ((X.map ofReal + I • Y.map ofReal)ᴴ * (X.map ofReal + I • Y.map ofReal)).map im =
      Xᵀ * Y - Yᵀ * X := by
  ext i j
  simp [Matrix.mul_apply, Complex.im_sum, Finset.sum_add_distrib, sub_eq_add_neg]

/-- If the real matrices `X` and `Y` satisfy `Xᵀ Y = Yᵀ X`, then the complex matrix `M = X + i Y`
has a real Gram matrix: `Im (Mᴴ M) = 0`. For a Lagrangian frame `fromRows X Y` this says that
the columns of `M` are orthogonal for the symplectic form `Im ⟪·, ·⟫`. -/
theorem map_im_conjTranspose_mul_self_eq_zero_of_transpose_mul_eq [Fintype m]
    {X Y : Matrix m n ℝ} (h : Xᵀ * Y = Yᵀ * X) :
    ((X.map ofReal + I • Y.map ofReal)ᴴ * (X.map ofReal + I • Y.map ofReal)).map im = 0 := by
  rw [map_im_conjTranspose_mul_self, h, sub_self]

/-- The column space of the real `2n × n` matrix `fromRows X Y`, as a subspace of
`EuclideanSpace ℝ (n ⊕ n)`, is the real image `(X + i Y) ℝⁿ ⊆ ℂⁿ` written in the real
coordinates `(Re, Im)` of `TauCeti.complexToRealEuclidean`. -/
theorem range_toEuclideanLin_fromRows [Fintype n] [DecidableEq n] (X Y : Matrix n n ℝ) :
    LinearMap.range (toEuclideanLin (fromRows X Y)) =
      (X.map ofReal + I • Y.map ofReal).realImage.map
        ((TauCeti.complexToRealEuclidean n).toLinearMap ∘ₗ
          (PiLp.continuousLinearEquiv 2 ℝ (fun _ : n ↦ ℂ)).toLinearMap) := by
  ext w
  simp only [LinearMap.mem_range, Submodule.mem_map, mem_realImage_iff_exists_mulVec]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨_, ⟨fun k ↦ u k, rfl⟩, ?_⟩
    ext (i | i) <;> simp [mulVec, dotProduct, Complex.re_sum, Complex.im_sum]
  · rintro ⟨_, ⟨u, rfl⟩, rfl⟩
    refine ⟨WithLp.toLp 2 u, ?_⟩
    ext (i | i) <;> simp [mulVec, dotProduct, Complex.re_sum, Complex.im_sum]

end Matrix

end
