/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.Symplectic.Complex.CoordinateSpace

/-!
# Weighted sums of squares on complex coordinate space

For real weights `k : ι → ℝ`, the quadratic form `z ↦ Σⱼ kⱼ |zⱼ|²` on `ι → ℂ` arises in two ways:
from Tau Ceti's standard symplectic form, as `z ↦ ω₀(z, (i kⱼ zⱼ)ⱼ)`, and, in the real coordinates
`(Re zⱼ)ⱼ ⊔ (Im zⱼ)ⱼ` given by `TauCeti.complexToRealEuclidean`, as the weighted sum of squares in
which `kⱼ` is attached to both `Re zⱼ` and `Im zⱼ`.

## Main results

* `TauCeti.stdComplexPiSymplecticForm_apply_ofReal_mul_I_mul`:
  `ω₀(v, (i kⱼ vⱼ)ⱼ) = Σⱼ kⱼ |vⱼ|²`. It generalizes Tau Ceti's
  `TauCeti.stdComplexPiBilin_apply_ofComplexModule`, the case of weights all `1`.
* `TauCeti.weightedSumSquares_complexToRealEuclidean`: the weighted sum of squares with weights
  `Sum.elim k k`, in the real coordinates of `v`, is `Σⱼ kⱼ |vⱼ|²`.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι]

/-- The standard symplectic form pairs `v` with `(i kⱼ vⱼ)ⱼ` to `Σⱼ kⱼ |vⱼ|²`. -/
theorem stdComplexPiSymplecticForm_apply_ofReal_mul_I_mul (k : ι → ℝ) (v : ι → ℂ) :
    stdComplexPiSymplecticForm ι v (fun j ↦ (k j * Complex.I) * v j) =
      ∑ j, k j * Complex.normSq (v j) := by
  simp only [stdComplexPiSymplecticForm_apply, stdComplexSymplecticForm_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.normSq_apply]
  ring

/-- In the real coordinates `(Re vⱼ)ⱼ ⊔ (Im vⱼ)ⱼ`, the weighted sum of squares with the weight `kⱼ`
on both `Re vⱼ` and `Im vⱼ` is `Σⱼ kⱼ |vⱼ|²`. -/
theorem weightedSumSquares_complexToRealEuclidean (k : ι → ℝ) (v : ι → ℂ) :
    QuadraticMap.weightedSumSquares ℝ (Sum.elim k k) (complexToRealEuclidean ι v).ofLp =
      ∑ j, k j * Complex.normSq (v j) := by
  simp only [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type,
    complexToRealEuclidean_apply, Sum.elim_inl, Sum.elim_inr, smul_eq_mul,
    ← Finset.sum_add_distrib, Complex.normSq_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  ring

end TauCeti

end
