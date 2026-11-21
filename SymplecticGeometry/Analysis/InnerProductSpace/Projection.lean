/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Orthogonal projections onto unitary images

For a unitary operator `u` of a Hilbert space and a subspace `K` with an orthogonal projection,
the projection onto `u K` is the conjugate `u P_K u⋆` of the projection `P_K` onto `K`.

## Main results

* `Submodule.starProjection_map_unitary`: `P_{u K} = u * P_K * star u`.
-/

public section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The orthogonal projection onto the image of a subspace `K` under a unitary operator `u` is
the conjugate `u P_K u⋆` of the projection onto `K`. -/
theorem starProjection_map_unitary (K : Submodule 𝕜 E) [K.HasOrthogonalProjection]
    (u : unitary (E →L[𝕜] E)) [(K.map ((u : E →L[𝕜] E) : E →ₗ[𝕜] E)).HasOrthogonalProjection] :
    (K.map ((u : E →L[𝕜] E) : E →ₗ[𝕜] E)).starProjection =
      (u : E →L[𝕜] E) * K.starProjection * star (u : E →L[𝕜] E) := by
  ext1 x
  exact starProjection_map_apply (Unitary.linearIsometryEquiv u) K x

end Submodule

end
