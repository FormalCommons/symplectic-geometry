/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Alternating.Conormal

/-!
# Pullback of conormal forms

Tau Ceti's `Submodule.conormalForms W ι N` is the submodule of alternating maps on `M` that
vanish as soon as one argument lies in `W`. This file shows that it is functorial in the pair
`(M, W)`: precomposition with a linear map `φ : M' →ₗ[R] M` that sends `W'` into `W` sends the
conormal forms of `W` to the conormal forms of `W'`
(`Submodule.compLinearMap_mem_conormalForms`).
-/

public section

namespace Submodule

variable {R M M' N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M']
  [Module R M'] [AddCommGroup N] [Module R N]

/-- **Pullback of conormal forms.** If a linear map `φ : M' →ₗ[R] M` sends the submodule `W'`
into `W`, then precomposing with `φ` sends an alternating map that vanishes as soon as one
argument lies in `W` to one that vanishes as soon as one argument lies in `W'`. -/
theorem compLinearMap_mem_conormalForms {W : Submodule R M} {W' : Submodule R M'}
    {φ : M' →ₗ[R] M} (hφ : W' ≤ W.comap φ) {α : M [⋀^ι]→ₗ[R] N}
    (hα : α ∈ W.conormalForms ι N) : α.compLinearMap φ ∈ W'.conormalForms ι N :=
  mem_conormalForms.mpr fun v j hv ↦ mem_conormalForms.mp hα (φ ∘ v) j (hφ hv)

end Submodule

end
