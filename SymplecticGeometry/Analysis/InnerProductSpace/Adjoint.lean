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

For a continuous linear equivalence `e` between Euclidean spaces `EuclideanSpace 𝕜 ι` and
`EuclideanSpace 𝕜 κ`, the coordinate `c` of `eᵀ w` (`ContinuousLinearEquiv.adjointEquiv e`) is
the inner product of `e (single c 1)` with `w`. In matrix terms, the entries of the transpose of a
matrix are read off from its columns.

## Main results

* `ContinuousLinearEquiv.adjointEquiv_apply_apply`: `eᵀ w c = ⟪e (single c 1), w⟫`.
-/

public section

namespace ContinuousLinearEquiv

variable {𝕜 ι κ : Type*} [RCLike 𝕜] [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The coordinate `c` of the adjoint `eᵀ w` is the inner product of the image under `e` of the
unit vector at `c` with `w`. -/
theorem adjointEquiv_apply_apply (e : EuclideanSpace 𝕜 ι ≃L[𝕜] EuclideanSpace 𝕜 κ)
    (w : EuclideanSpace 𝕜 κ) (c : ι) :
    e.adjointEquiv w c = inner 𝕜 (e (EuclideanSpace.single c 1)) w := by
  calc e.adjointEquiv w c = inner 𝕜 (EuclideanSpace.single c 1) (e.adjointEquiv w) := by
        rw [EuclideanSpace.inner_single_left, map_one, one_mul]
    _ = inner 𝕜 (e (EuclideanSpace.single c 1)) w := by
        rw [adjointEquiv_apply, ContinuousLinearMap.adjoint_inner_right, coe_coe]

end ContinuousLinearEquiv

end
