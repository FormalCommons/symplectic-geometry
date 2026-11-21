/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Coordinates of adjoints on Euclidean spaces

For a continuous linear map `f` from `EuclideanSpace 𝕜 ι` to `EuclideanSpace 𝕜 κ`, the coordinate
`c` of the adjoint `f† w` (`ContinuousLinearMap.adjoint f`) is the inner product of
`f (single c 1)` with `w`. In matrix terms, the entries of the conjugate transpose of a matrix are
read off from the columns of the matrix.

## Main results

* `ContinuousLinearMap.adjoint_apply_apply`: `f† w c = ⟪f (single c 1), w⟫`.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The coordinate `c` of the adjoint `f† w` is the inner product of the image under `f` of the
unit vector at `c` with `w`. -/
theorem adjoint_apply_apply (f : EuclideanSpace 𝕜 ι →L[𝕜] EuclideanSpace 𝕜 κ)
    (w : EuclideanSpace 𝕜 κ) (c : ι) :
    adjoint f w c = inner 𝕜 (f (EuclideanSpace.single c 1)) w := by
  rw [← adjoint_inner_right, EuclideanSpace.inner_single_left, map_one, one_mul]

end ContinuousLinearMap

end
