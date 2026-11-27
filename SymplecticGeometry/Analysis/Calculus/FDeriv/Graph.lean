/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivatives of graph maps over a projection

Let `P` be a continuous linear map that fixes every point of a subspace `S`, and let `g` be a map
with `P ∘ g = 0`. The graph map `w ↦ w + g w` on `S` then has an injective derivative wherever
`g` is differentiable: applying `P` to the derivative recovers the tangent vector, since `P`
kills the derivative of `g`.

## Main results

* `ContinuousLinearMap.injective_fderiv_add_comp_subtype`: the derivative of
  `w : S ↦ w + g w` is injective at every point of `S` where `g` is differentiable.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Graph maps over a projection.** Let `P` be a continuous linear map fixing each point of a
subspace `S`, and `g` a map with `P ∘ g = 0` that is differentiable at a point `z` of `S`. Then
the derivative at `z` of the map `w ↦ w + g w` from `S` is injective. -/
theorem injective_fderiv_add_comp_subtype {P : F →L[𝕜] F} {S : Submodule 𝕜 F}
    (hS : ∀ w ∈ S, P w = w) {g : F → F} (hPg : ∀ w, P (g w) = 0) {z : S}
    (hg : DifferentiableAt 𝕜 g z) :
    Function.Injective (fderiv 𝕜 (fun w : S ↦ (w : F) + g w) z) := by
  have hPdg (u : F) : P (fderiv 𝕜 g z u) = 0 := by
    have h := P.fderiv_comp_left hg
    simp [Function.comp_def, hPg] at h
    simpa using congrArg (· u) h.symm
  have hD : HasFDerivAt (fun w : S ↦ (w : F) + g w)
      (S.subtypeL + (fderiv 𝕜 g z).comp S.subtypeL) z :=
    S.subtypeL.hasFDerivAt.add (hg.hasFDerivAt.comp (f := S.subtypeL) z S.subtypeL.hasFDerivAt)
  rw [hD.fderiv]
  exact fun u v huv ↦ Subtype.ext (by
    simpa [hS _ u.property, hS _ v.property, hPdg] using congrArg P huv)

end ContinuousLinearMap

end
