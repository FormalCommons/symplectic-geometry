/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Convex.FullSimplex

/-!
# The faces of the full-dimensional standard simplex lie on its boundary

Each face inclusion `simplexFace p i : Δᵖ → Δᵖ⁺¹` of Tau Ceti's full-dimensional standard simplex
lands outside the interior of `Δᵖ⁺¹` (`TauCeti.simplexFace_coe_notMem_interior`): the image has
`i`-th barycentric weight `0`, while Tau Ceti's `interior_coordinateSimplex` says that the
interior consists of the points whose coordinates are positive and sum to less than `1`.
-/

public section

namespace TauCeti

/-- Every point of a face of `Δᵖ⁺¹` lies outside the interior of `Δᵖ⁺¹`. -/
theorem simplexFace_coe_notMem_interior {p : ℕ} (i : Fin (p + 2)) (x : fullSimplex p) :
    (simplexFace p i x : EuclideanSpace ℝ (Fin (p + 1))) ∉ interior (fullSimplex (p + 1)) := by
  -- `Δᵖ⁺¹` is the preimage of the coordinate simplex, whose interior Tau Ceti describes.
  have hS : fullSimplex (p + 1) =
      EuclideanSpace.equiv (Fin (p + 1)) ℝ ⁻¹' coordinateSimplex (Fin (p + 1)) :=
    Set.ext fun _ ↦ mem_fullSimplex_iff.trans (mem_coordinateSimplex _ _).symm
  have h := (EuclideanSpace.equiv (Fin (p + 1)) ℝ).toHomeomorph.preimage_interior
    (coordinateSimplex (Fin (p + 1)))
  rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
  have hint (y : EuclideanSpace ℝ (Fin (p + 1))) (hy : y ∈ interior (fullSimplex (p + 1))) :
      (∀ k, 0 < y k) ∧ ∑ k, y k < 1 := by
    rwa [hS, ← h, Set.mem_preimage, interior_coordinateSimplex] at hy
  intro hy
  obtain ⟨hpos, hsum⟩ := hint _ hy
  have hw := fullSimplexEquivStdSimplex_simplexFace_self i x
  cases i using Fin.cases with
  | zero =>
    rw [fullSimplexEquivStdSimplex_weights_zero] at hw
    linarith
  | succ j =>
    rw [fullSimplexEquivStdSimplex_weights_succ] at hw
    exact (hpos j).ne' hw

end TauCeti

end
