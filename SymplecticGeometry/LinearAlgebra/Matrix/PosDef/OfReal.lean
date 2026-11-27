/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.Realify
import SymplecticGeometry.LinearAlgebra.Matrix.PosDef.Block

/-!
# Real positive definite matrices over an `RCLike` field

A real square matrix is positive definite exactly when it is positive definite as a matrix over
an `RCLike` field `𝕜` (for instance `ℂ`), through the inclusion `ℝ → 𝕜`. The proof goes through
Tau Ceti's realification: the realification of `A.map (algebraMap ℝ 𝕜)` is the block diagonal
matrix with two copies of `A` (`Matrix.realify_map_ofReal`), and realification preserves and
reflects positive definiteness (`Matrix.posDef_realify_iff`), and a block diagonal matrix is
positive definite exactly when its diagonal blocks are (`Matrix.posDef_fromBlocks_zero_zero_iff`).

## Main results

* `Matrix.posDef_map_algebraMap_iff`: `(A.map (algebraMap ℝ 𝕜)).PosDef ↔ A.PosDef`.
* `Matrix.posDef_map_ofReal_iff`: the same for `𝕜 = ℂ`, with the coercion `ℝ → ℂ`.
-/

public section

open scoped ComplexOrder

namespace Matrix

variable {n : Type*} [Finite n] {𝕜 : Type*} [RCLike 𝕜]

/-- A real matrix is positive definite exactly when it is positive definite over an `RCLike`
field. -/
@[simp]
theorem posDef_map_algebraMap_iff {A : Matrix n n ℝ} :
    (A.map (algebraMap ℝ 𝕜)).PosDef ↔ A.PosDef := by
  rw [← posDef_realify_iff, realify_map_ofReal, posDef_fromBlocks_zero_zero_iff, and_self]

/-- A real matrix is positive definite exactly when it is positive definite as a complex matrix.
This is `posDef_map_algebraMap_iff` for `ℂ`, stated with the coercion `ℝ → ℂ`, the form that `simp`
gives to `algebraMap ℝ ℂ`. -/
@[simp]
theorem posDef_map_ofReal_iff {A : Matrix n n ℝ} :
    (A.map ((↑) : ℝ → ℂ)).PosDef ↔ A.PosDef := by
  rw [← Complex.coe_algebraMap]
  exact posDef_map_algebraMap_iff

end Matrix

end
