/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import SymplecticGeometry.Analysis.Complex.Euclidean.Space
public import TauCeti.Analysis.Complex.Euclidean.Matrix

/-!
# Complex matrices in the real coordinates of complex vectors

A complex matrix `A : Matrix ι ι ℂ` acts on `ι → ℂ`. Read in real coordinates, through Tau
Ceti's `TauCeti.complexToRealEuclidean ι`, it acts on `EuclideanSpace ℝ (ι ⊕ ι)` as its
realification `Matrix.realify A`. Both statements follow from Tau Ceti's
`TauCeti.complexToRealEuclidean_mulVec`.

* `TauCeti.conj_complexToRealEuclidean_toLin'`: conjugating the complex-linear map of
  `A` by `complexToRealEuclidean ι` gives `Matrix.toEuclideanLin A.realify`.
* `TauCeti.complexToRealEuclideanIsometry_toEuclideanCLM`: the same through the isometry
  `complexToRealEuclideanIsometry ι`, vector by vector.
-/

public section

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

/-- Through `complexToRealEuclideanIsometry ι`, a complex matrix acts on
`EuclideanSpace ℝ (ι ⊕ ι)` as its realification. -/
theorem complexToRealEuclideanIsometry_toEuclideanCLM (A : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    complexToRealEuclideanIsometry ι (Matrix.toEuclideanCLM (𝕜 := ℂ) A v) =
      Matrix.toEuclideanLin A.realify (complexToRealEuclideanIsometry ι v) := by
  rw [complexToRealEuclideanIsometry_apply, complexToRealEuclideanIsometry_apply]
  exact complexToRealEuclidean_mulVec A v.ofLp

end TauCeti

end
