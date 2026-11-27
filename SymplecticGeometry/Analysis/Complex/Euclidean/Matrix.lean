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
realification `Matrix.realify A`; this is Tau Ceti's `TauCeti.complexToRealEuclidean_mulVec`.

* `TauCeti.complexToRealEuclideanIsometry_toEuclideanCLM`: the same statement through the
  isometry `complexToRealEuclideanIsometry ι` on `EuclideanSpace ℂ ι`, vector by vector.
-/

public section

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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
