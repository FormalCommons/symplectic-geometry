/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Euclidean.Space
import SymplecticGeometry.Analysis.InnerProductSpace.PiL2

/-!
# Norms of the real coordinates of complex vectors

Tau Ceti's `TauCeti.complexToRealEuclidean ι` splits `u : ι → ℂ` into its real and imaginary
coordinate blocks in `EuclideanSpace ℝ (ι ⊕ ι)`. This file computes the norm of the image, from
Tau Ceti's `TauCeti.inner_complexToRealEuclidean` and `Matrix.re_star_dotProduct_self`:

* `TauCeti.norm_sq_complexToRealEuclidean`: `‖complexToRealEuclidean ι u‖ ^ 2 = ∑ᵢ ‖uᵢ‖²`;
* `TauCeti.norm_complexToRealEuclidean_smul`: scaling `u` by `a : ℂ` scales that norm by `‖a‖`.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The squared norm of `complexToRealEuclidean ι u` is `∑ᵢ ‖uᵢ‖²`. -/
theorem norm_sq_complexToRealEuclidean (u : ι → ℂ) :
    ‖complexToRealEuclidean ι u‖ ^ 2 = ∑ i, ‖u i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_complexToRealEuclidean, Matrix.re_star_dotProduct_self]

/-- `complexToRealEuclidean ι` is compatible with the norms: scaling by `a : ℂ` scales the norm
of the image by `‖a‖`. -/
theorem norm_complexToRealEuclidean_smul (a : ℂ) (v : ι → ℂ) :
    ‖complexToRealEuclidean ι (a • v)‖ = ‖a‖ * ‖complexToRealEuclidean ι v‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (by positivity)]
  simp [mul_pow, norm_sq_complexToRealEuclidean, Finset.mul_sum]

end TauCeti

end
