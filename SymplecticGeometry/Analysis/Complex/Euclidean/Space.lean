/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space

/-!
# Norms of the real coordinates of complex vectors

Tau Ceti's `TauCeti.complexToRealEuclidean ι` splits `u : ι → ℂ` into its real and imaginary
coordinate blocks in `EuclideanSpace ℝ (ι ⊕ ι)`. This file computes the norm of the image:

* `TauCeti.norm_sq_complexToRealEuclidean`: `‖complexToRealEuclidean ι u‖ ^ 2 = ∑ᵢ ‖uᵢ‖²`;
* `TauCeti.norm_complexToRealEuclidean_smul`: scaling `u` by `a : ℂ` scales that norm by `‖a‖`;
* `Matrix.re_star_dotProduct_self`: `Re (star z ⬝ᵥ z) = ∑ᵢ ‖zᵢ‖²`.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- `complexToRealEuclidean ι` is compatible with the norms: scaling by `a : ℂ` scales the norm
of the image by `‖a‖`. -/
theorem norm_complexToRealEuclidean_smul (a : ℂ) (v : ι → ℂ) :
    ‖complexToRealEuclidean ι (a • v)‖ = ‖a‖ * ‖complexToRealEuclidean ι v‖ := by
  have h : ‖complexToRealEuclidean ι (a • v)‖ ^ 2 =
      (‖a‖ * ‖complexToRealEuclidean ι v‖) ^ 2 := by
    rw [mul_pow, ← real_inner_self_eq_norm_sq (complexToRealEuclidean ι (a • v)),
      ← real_inner_self_eq_norm_sq (complexToRealEuclidean ι v), inner_complexToRealEuclidean,
      inner_complexToRealEuclidean, star_smul, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, smul_eq_mul, Complex.star_def, ← mul_assoc,
      Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

/-- The squared norm of `complexToRealEuclidean ι u` is `∑ᵢ ‖uᵢ‖²`. -/
theorem norm_sq_complexToRealEuclidean (u : ι → ℂ) :
    ‖complexToRealEuclidean ι u‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_complexToRealEuclidean, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- The real part of the Hermitian square of a complex vector is its squared Euclidean norm:
`Re (star z ⬝ᵥ z) = ∑ᵢ ‖zᵢ‖²`. -/
theorem _root_.Matrix.re_star_dotProduct_self (z : ι → ℂ) :
    (star z ⬝ᵥ z).re = ∑ i, ‖z i‖ ^ 2 := by
  rw [← inner_complexToRealEuclidean, real_inner_self_eq_norm_sq, norm_sq_complexToRealEuclidean]

end TauCeti

end
