/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal projections onto unitary images and relative complements

For a unitary operator `u` of a Hilbert space and a subspace `K` with an orthogonal projection,
the image `u K` has an orthogonal projection too, and it is the conjugate `u P_K u⋆` of the
projection `P_K` onto `K`. For nested subspaces `K ≤ K'`, the difference `P_{K'} - P_K` is the
orthogonal projection onto the orthogonal complement `Kᗮ ⊓ K'` of `K` in `K'`.

## Main results

* `Submodule.HasOrthogonalProjection.map_unitary`: `u K` has an orthogonal projection.
* `Submodule.starProjection_map_unitary`: `P_{u K} = u * P_K * star u`.
* `Submodule.starProjection_sub_starProjection_of_le`: `P_{K'} - P_K = P_{Kᗮ ⊓ K'}` when
  `K ≤ K'`.
-/

public section

namespace Submodule

section Sub

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- For subspaces `K ≤ K'`, the difference `P_{K'} - P_K` of the orthogonal projections is the
orthogonal projection onto the orthogonal complement `Kᗮ ⊓ K'` of `K` in `K'`. -/
theorem starProjection_sub_starProjection_of_le {K K' : Submodule 𝕜 E}
    [K.HasOrthogonalProjection] [K'.HasOrthogonalProjection] [(Kᗮ ⊓ K').HasOrthogonalProjection]
    (h : K ≤ K') : K'.starProjection - K.starProjection = (Kᗮ ⊓ K').starProjection := by
  ext x
  have hK : K.starProjection (K'.starProjection x) = K.starProjection x :=
    congr($(starProjection_comp_starProjection_of_le h) x)
  refine (eq_starProjection_of_mem_orthogonal' (K := Kᗮ ⊓ K')
    (v := K'.starProjection x - K.starProjection x) (z := x - K'.starProjection x +
    K.starProjection x) (mem_inf.2 ⟨?_, ?_⟩) ?_ (by abel)).symm
  · simpa only [hK] using
      sub_starProjection_mem_orthogonal (K := K) (K'.starProjection x)
  · exact K'.sub_mem (K'.starProjection_apply_mem x) (h (K.starProjection_apply_mem x))
  · exact add_mem (orthogonal_le inf_le_right (sub_starProjection_mem_orthogonal x))
      (orthogonal_le inf_le_left (K.le_orthogonal_orthogonal (K.starProjection_apply_mem x)))

end Sub

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The image of a subspace with an orthogonal projection under a unitary operator has an
orthogonal projection. -/
instance HasOrthogonalProjection.map_unitary (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (u : unitary (E →L[𝕜] E)) :
    (K.map ((u : E →L[𝕜] E) : E →ₗ[𝕜] E)).HasOrthogonalProjection :=
  HasOrthogonalProjection.map_linearIsometryEquiv K (Unitary.linearIsometryEquiv u)

/-- The orthogonal projection onto the image of a subspace `K` under a unitary operator `u` is
the conjugate `u P_K u⋆` of the projection onto `K`. -/
theorem starProjection_map_unitary (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (u : unitary (E →L[𝕜] E)) :
    (K.map ((u : E →L[𝕜] E) : E →ₗ[𝕜] E)).starProjection =
      (u : E →L[𝕜] E) * K.starProjection * star (u : E →L[𝕜] E) := by
  ext1 x
  exact starProjection_map_apply (Unitary.linearIsometryEquiv u) K x

end Submodule

end
