/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# A boundaryless model space is diffeomorphic to its vector space

A model with corners `I : ModelWithCorners 𝕜 E H` without boundary is a homeomorphism `H ≃ₜ E`
(Mathlib's `ModelWithCorners.toHomeomorph`). This file makes it a `C^n` diffeomorphism from `H`,
with the model `I`, to `E`, with its own model `𝓘(𝕜, E)`. Followed by a continuous linear
equivalence `E ≃L[𝕜] V`, it is a diffeomorphism of model spaces along which
`SymplecticGeometry.Remodel` charts a manifold over `I` on the vector space `V`, such as a product
of a surface and a torus, modelled on a product of models.

## Main definitions

* `ModelWithCorners.toDiffeomorph I n`: a boundaryless model `I`, as a `C^n` diffeomorphism from
  `H` to `E`.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless]
  (n : ℕ∞ω)

/-- A boundaryless model with corners `I : ModelWithCorners 𝕜 E H`, as a `C^n` diffeomorphism
from `H`, with the model `I`, onto `E`, with its own model `𝓘(𝕜, E)`. -/
def toDiffeomorph : H ≃ₘ^n⟮I, 𝓘(𝕜, E)⟯ E where
  toEquiv := I.toHomeomorph.toEquiv
  contMDiff_toFun := I.contMDiff
  contMDiff_invFun := by
    have h := I.contMDiffOn_symm (n := n)
    rw [I.range_eq_univ, contMDiffOn_univ] at h
    exact h

@[simp]
theorem coe_toDiffeomorph : ⇑(I.toDiffeomorph n) = I :=
  (rfl)

@[simp]
theorem coe_toDiffeomorph_symm : ⇑(I.toDiffeomorph n).symm = I.symm :=
  (rfl)

end ModelWithCorners

end
