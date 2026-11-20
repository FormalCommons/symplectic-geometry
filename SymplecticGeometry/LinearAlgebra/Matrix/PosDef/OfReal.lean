/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Matrix.Realify

/-!
# Real positive definite matrices over an `RCLike` field

A real square matrix is positive definite exactly when it is positive definite as a matrix over
an `RCLike` field `𝕜` (for instance `ℂ`), through the inclusion `ℝ → 𝕜`. The proof goes through
Tau Ceti's realification: the realification of `A.map (algebraMap ℝ 𝕜)` is the block diagonal
matrix with two copies of `A` (`Matrix.realify_map_ofReal`), and realification preserves and
reflects positive definiteness (`Matrix.posDef_realify_iff`).

## Main results

* `Matrix.posDef_map_algebraMap_iff`: `(A.map (algebraMap ℝ 𝕜)).PosDef ↔ A.PosDef`.
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
  classical
  let _ := Fintype.ofFinite n
  rw [← posDef_realify_iff, realify_map_ofReal]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · convert h.submatrix (e := Sum.inl) Sum.inl_injective
    ext i j
    simp
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun x hx ↦ ?_⟩
  · rw [IsHermitian, fromBlocks_conjTranspose, h.isHermitian.eq]
    simp
  have hx' : x ∘ Sum.inl ≠ 0 ∨ x ∘ Sum.inr ≠ 0 := by
    by_contra! hc
    exact hx (funext fun i ↦ by cases i with
      | inl i => exact congrFun hc.1 i
      | inr i => exact congrFun hc.2 i)
  have hsplit : star x ⬝ᵥ (fromBlocks A 0 0 A *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
        star (x ∘ Sum.inr) ⬝ᵥ (A *ᵥ (x ∘ Sum.inr)) := by
    rw [← Sum.elim_comp_inl_inr x, fromBlocks_mulVec]
    simp [dotProduct, Fintype.sum_sum_type, Function.comp_def]
  rw [hsplit]
  rcases hx' with hx' | hx'
  · exact add_pos_of_pos_of_nonneg (h.dotProduct_mulVec_pos hx')
      (h.posSemidef.dotProduct_mulVec_nonneg _)
  · exact add_pos_of_nonneg_of_pos (h.posSemidef.dotProduct_mulVec_nonneg _)
      (h.dotProduct_mulVec_pos hx')

end Matrix

end
