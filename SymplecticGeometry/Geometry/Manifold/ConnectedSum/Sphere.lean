/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Sphere

/-!
# Complementary balls

Two facts about any pair of complementary balls `s s' : E → N`
(`TauCeti.IsComplementaryBall s s'`), which say that the pair is symmetric away from the poles:

* `TauCeti.IsComplementaryBall.apply_eq_inversion_symm`: the inversion in the unit sphere also
  carries `s` to `s'`, `s w = s' (inversion 0 1 w)` for `w ≠ 0`;
* `TauCeti.IsComplementaryBall.apply_zero_notMem_range`: the centre `s' 0` of the complementary
  ball is not in the range of `s`.

The file needs only the definition of complementary balls, so that files about a particular pair,
such as the two charts of the sphere, can use these facts without the theory of forms.
-/

public section

open Set EuclideanGeometry

namespace TauCeti.IsComplementaryBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {N : Type*} [TopologicalSpace N] {s s' : E → N}

/-- For complementary balls `s` and `s'`, the first ball is the complementary one read through
the inversion away from the centre: `s w = s' (inversion 0 1 w)` for `w ≠ 0`. -/
theorem apply_eq_inversion_symm (h : IsComplementaryBall s s') {w : E} (hw : w ≠ 0) :
    s w = s' (inversion 0 1 w) := by
  rw [h.apply_eq_inversion _ fun h0 ↦ hw ((inversion_eq_center one_ne_zero).1 h0),
    inversion_inversion _ one_ne_zero]

/-- For complementary balls `s` and `s'`, the centre `s' 0` of the complementary ball is not in
the range of the first ball. -/
theorem apply_zero_notMem_range (h : IsComplementaryBall s s') : s' 0 ∉ range s := by
  rintro ⟨x, hx⟩
  have hne : s' 0 ≠ s 0 := by
    have : s' 0 ∈ range s' := mem_range_self 0
    rwa [h.range_eq] at this
  rcases eq_or_ne x 0 with rfl | hx0
  · exact hne hx.symm
  · rw [h.apply_eq_inversion_symm hx0] at hx
    exact hx0 ((inversion_eq_center one_ne_zero).1 (h.isOpenEmbedding.injective hx))

end TauCeti.IsComplementaryBall

end
