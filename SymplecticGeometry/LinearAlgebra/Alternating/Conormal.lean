/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.LinearAlgebra.Alternating.Conormal
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import TauCeti.LinearAlgebra.Alternating.Curry

/-!
# Pullback of conormal forms

Tau Ceti's `Submodule.conormalForms W ι N` is the submodule of alternating maps on `M` that
vanish as soon as one argument lies in `W`. This file shows that it is functorial in the pair
`(M, W)`: precomposition with a linear map `φ : M' →ₗ[R] M` that sends `W'` into `W` sends the
conormal forms of `W` to the conormal forms of `W'`
(`Submodule.compLinearMap_mem_conormalForms`). In two arguments, an alternating map `ω` is a
conormal form of `W` exactly when `W` lies in the kernel of the bilinear map
`(u, w) ↦ ω ![u, w]` (`Submodule.mem_conormalForms_fin_two_iff_le_ker`).
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

/-- An alternating map `ω` in two arguments vanishes as soon as one argument lies in `W` exactly
when `W` lies in the kernel of the bilinear map `(u, w) ↦ ω ![u, w]`. -/
theorem mem_conormalForms_fin_two_iff_le_ker {W : Submodule R M} {ω : M [⋀^Fin 2]→ₗ[R] N} :
    ω ∈ W.conormalForms (Fin 2) N ↔ W ≤ LinearMap.ker ω.toMultilinearMap.toBilinMap := by
  refine ⟨fun hω u hu ↦ LinearMap.mem_ker.mpr <| LinearMap.ext fun w ↦ ?_,
    fun hW ↦ mem_conormalForms.mpr fun v j hv ↦ ?_⟩
  · simpa using mem_conormalForms.mp hω ![u, w] 0 hu
  · -- `ι_{v j} ω` vanishes, since `v j` lies in the kernel of the bilinear map.
    refine AlternatingMap.map_eq_zero_of_curryLeft_eq_zero (x := v j) ?_ rfl
    ext u
    have e : Matrix.vecCons (v j) u = ![v j, u 0] := (FinVec.etaExpand_eq _).symm
    simpa [AlternatingMap.curryLeft_apply_apply, e] using
      LinearMap.congr_fun (LinearMap.mem_ker.mp (hW hv)) (u 0)

end Submodule

end
