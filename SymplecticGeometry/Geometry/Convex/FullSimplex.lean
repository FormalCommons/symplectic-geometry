/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Convex.FullSimplex

/-!
# The interior of the full-dimensional standard simplex

A point of `ℝᵖ` lies in the interior of Tau Ceti's full-dimensional standard simplex `Δᵖ`
exactly when its coordinates are positive and sum to less than `1`
(`TauCeti.mem_interior_fullSimplex_iff`). This reads Tau Ceti's `interior_coordinateSimplex`
through the identification `EuclideanSpace.equiv` of `ℝᵖ` with `Fin p → ℝ`.

So each face inclusion `simplexFace p i : Δᵖ → Δᵖ⁺¹` lands outside the interior of `Δᵖ⁺¹`
(`TauCeti.simplexFace_coe_notMem_interior`): the image has `i`-th barycentric weight `0`.

## Main results

* `TauCeti.mem_interior_fullSimplex_iff`: the interior of `Δᵖ` in coordinates.
* `TauCeti.simplexFace_coe_notMem_interior`: the faces of `Δᵖ⁺¹` miss its interior.
-/

public section

namespace TauCeti

/-- A point of `ℝᵖ` lies in the interior of `Δᵖ` exactly when its coordinates are positive and
sum to less than `1`. -/
theorem mem_interior_fullSimplex_iff {p : ℕ} {y : EuclideanSpace ℝ (Fin p)} :
    y ∈ interior (fullSimplex p) ↔ (∀ k, 0 < y k) ∧ ∑ k, y k < 1 := by
  -- `fullSimplex` is not exposed by Tau Ceti's module, so its defining preimage is restated
  -- through `mem_fullSimplex_iff`.
  have hS : fullSimplex p = EuclideanSpace.equiv (Fin p) ℝ ⁻¹' coordinateSimplex (Fin p) :=
    Set.ext fun _ ↦ mem_fullSimplex_iff.trans (mem_coordinateSimplex _ _).symm
  have h := (EuclideanSpace.equiv (Fin p) ℝ).toHomeomorph.preimage_interior
    (coordinateSimplex (Fin p))
  rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [hS, ← h, Set.mem_preimage, interior_coordinateSimplex]
  simp

/-- Every point of a face of `Δᵖ⁺¹` lies outside the interior of `Δᵖ⁺¹`. -/
theorem simplexFace_coe_notMem_interior {p : ℕ} (i : Fin (p + 2)) (x : fullSimplex p) :
    (simplexFace p i x : EuclideanSpace ℝ (Fin (p + 1))) ∉ interior (fullSimplex (p + 1)) := by
  intro hy
  obtain ⟨hpos, hsum⟩ := mem_interior_fullSimplex_iff.1 hy
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
