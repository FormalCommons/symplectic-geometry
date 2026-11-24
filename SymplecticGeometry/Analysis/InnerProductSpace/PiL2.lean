/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean space: matrices, reindexing and the standard basis

A square matrix `M` indexed by `m` acts on `EuclideanSpace 𝕜 m` by `Matrix.toEuclideanLin`.
This file shows that moving the coordinates along `e : m ≃ n`, by Mathlib's
`LinearIsometryEquiv.piLpCongrLeft`, turns this action into that of `Matrix.reindex e e M`.
It also places the standard basis vectors of `EuclideanSpace 𝕜 ι` on the unit sphere, and shows
that splitting `EuclideanSpace 𝕜 (ι ⊕ κ)` into two blocks by `EuclideanSpace.sumEquivProd`
preserves the squared norm.

## Main results

* `Matrix.piLpCongrLeft_toEuclideanLin_apply`: `e (M z) = (reindex e e M) (e z)`.
* `EuclideanSpace.single_one_mem_sphere`: each standard basis vector has norm one.
* `EuclideanSpace.norm_sq_sumEquivProd`: the squared norms of the two blocks of
  `sumEquivProd x` add up to `‖x‖²`.
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

end EuclideanSpace

end
