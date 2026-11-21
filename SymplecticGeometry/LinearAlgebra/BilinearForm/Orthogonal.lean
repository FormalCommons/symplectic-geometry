/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection

/-!
# Projections along the orthogonal of a subspace for a bilinear form

Let `B` be a bilinear form on a module `M` over a commutative ring and `W` a submodule that is
complementary to its `B`-orthogonal. This file characterizes the projection onto `W` along the
`B`-orthogonal of `W`: it sends `v` to the unique `w ∈ W` with `B u w = B u v` for all `u ∈ W`
(`LinearMap.BilinForm.projection_orthogonal_eq_iff`).
-/

public section

namespace LinearMap.BilinForm

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The projection onto a subspace `W` along its `B`-orthogonal sends `v` to `w` exactly when `w`
lies in `W` and pairs with every vector of `W` as `v` does: `B u w = B u v` for all `u ∈ W`. -/
theorem projection_orthogonal_eq_iff (B : LinearMap.BilinForm R M) {W : Submodule R M}
    (h : IsCompl W (B.orthogonal W)) (v w : M) :
    W.projection (B.orthogonal W) h v = w ↔ w ∈ W ∧ ∀ u ∈ W, B u w = B u v := by
  have hsub (v w : M) : v - w ∈ B.orthogonal W ↔ ∀ u ∈ W, B u w = B u v := by
    simp only [mem_orthogonal_iff, map_sub, sub_eq_zero]
    exact forall₂_congr fun _ _ ↦ eq_comm
  constructor
  · rintro rfl
    exact ⟨Submodule.projection_apply_mem h v, (hsub _ _).mp (Submodule.sub_projection_mem h v)⟩
  · rintro ⟨hw, hwv⟩
    have hv : v = w + (v - w) := (add_sub_cancel w v).symm
    rw [hv, map_add, Submodule.projection_apply_of_mem_left h hw,
      (Submodule.projection_apply_eq_zero_iff h).mpr ((hsub v w).mpr hwv), add_zero]

end LinearMap.BilinForm

end
