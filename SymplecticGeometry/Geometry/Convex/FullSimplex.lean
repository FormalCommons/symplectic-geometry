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
`i`-th barycentric weight `0`, so moving it a little in a suitable direction (along `e₀` for
`i = 0`, along `-eⱼ` for `i = j + 1`) leaves the simplex.
-/

public section

open Topology

namespace TauCeti

/-- Every point of a face of `Δᵖ⁺¹` lies outside the interior of `Δᵖ⁺¹`. -/
theorem simplexFace_coe_notMem_interior {p : ℕ} (i : Fin (p + 2)) (x : fullSimplex p) :
    (simplexFace p i x : EuclideanSpace ℝ (Fin (p + 1))) ∉ interior (fullSimplex (p + 1)) := by
  intro hy
  have hw := fullSimplexEquivStdSimplex_simplexFace_self i x
  -- A direction `v` along which the face point leaves `Δᵖ⁺¹` at once.
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin (p + 1)), ∀ t : ℝ, 0 < t →
      (simplexFace p i x : EuclideanSpace ℝ (Fin (p + 1))) + t • v ∉ fullSimplex (p + 1) := by
    cases i using Fin.cases with
    | zero =>
      -- The coordinates of the face point sum to `1`.
      rw [fullSimplexEquivStdSimplex_weights_zero] at hw
      refine ⟨EuclideanSpace.single 0 1, fun t ht h ↦ ?_⟩
      have := (mem_fullSimplex_iff.1 h).2
      simp only [PiLp.add_apply, PiLp.smul_apply, Finset.sum_add_distrib, ← Finset.smul_sum] at this
      simp at this
      linarith
    | succ j =>
      -- The `j`-th coordinate of the face point is `0`.
      rw [fullSimplexEquivStdSimplex_weights_succ] at hw
      refine ⟨-EuclideanSpace.single j 1, fun t ht h ↦ ?_⟩
      have := (mem_fullSimplex_iff.1 h).1 j
      simp [hw] at this
      linarith
  have hlim : Filter.Tendsto
      (fun t : ℝ ↦ (simplexFace p i x : EuclideanSpace ℝ (Fin (p + 1))) + t • v) (𝓝[>] 0)
      (𝓝 (simplexFace p i x : EuclideanSpace ℝ (Fin (p + 1)))) :=
    ((continuous_const.add (continuous_id.smul continuous_const)).tendsto' 0 _
      (by simp)).mono_left nhdsWithin_le_nhds
  obtain ⟨t, htm, ht⟩ := ((hlim.eventually (mem_interior_iff_mem_nhds.1 hy)).and
    self_mem_nhdsWithin).exists
  exact hv t ht htm

end TauCeti

end
