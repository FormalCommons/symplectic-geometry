/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Tangent vectors in the trivializations of the tangent bundle

Two facts on the coordinates of a tangent vector in a trivialization of the tangent bundle.

* `TangentBundle.trivializationAt_apply_self_snd`: in the trivialization at its own base point,
  a tangent vector `v` at `x` has coordinate vector `v`. This is the fibre version of Tau Ceti's
  `TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self`, and the converse direction of
  Tau Ceti's `TangentBundle.trivializationAt_symm_apply_self`.
* `TangentBundle.mfderivWithin_extChartAt_symm_trivializationAt_snd`: for `x` in the chart at
  `x₀`, the derivative of the inverse chart at `x₀`, taken at the chart point of `x`, sends the
  coordinate vector of `v` in the trivialization at `x₀` back to `v`. It is Mathlib's
  `TangentBundle.symmL_trivializationAt` applied to a vector.

The inclusion `v ↦ (x, v)` of the tangent space at `x` into the tangent bundle is smooth
(`TangentBundle.contMDiff_totalSpaceMk`). This is the tangent-bundle case of Tau Ceti's
`TauCeti.Manifold.contMDiff_totalSpaceMk`, stated with the model space `E` as its source, so that
callers need not supply norms on the tangent spaces.
-/

public section

open Set Bundle
open scoped Manifold

namespace TangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E H M : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M]

/-- In the trivialization of the tangent bundle at `x`, a tangent vector `v` at `x` has
coordinate vector `v`. -/
@[simp]
theorem trivializationAt_apply_self_snd (x : M) (v : TangentSpace I x) :
    (trivializationAt E (TangentSpace I) x ⟨x, v⟩).2 = v :=
  ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt_apply_of_mem (R := 𝕜)
    (FiberBundle.mem_baseSet_trivializationAt' x) v).symm.trans
    (TauCeti.Manifold.continuousLinearMapAt_trivializationAt_self x v)

/-- Let `x` be in the source of the chart at `x₀`. The derivative of the inverse of the extended
chart at `x₀`, at the chart point of `x`, sends the coordinate vector of a tangent vector `v` at
`x` in the trivialization at `x₀` to `v`. -/
theorem mfderivWithin_extChartAt_symm_trivializationAt_snd {x₀ x : M}
    (hx : x ∈ (chartAt H x₀).source) (v : TangentSpace I x) :
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) (extChartAt I x₀ x)
      (trivializationAt E (TangentSpace I) x₀ ⟨x, v⟩).2 = v :=
  (congrArg (fun L : E →L[𝕜] E ↦ L (trivializationAt E (TangentSpace I) x₀ ⟨x, v⟩).2)
    (symmL_trivializationAt (I := I) hx)).symm.trans ((Trivialization.symmL_apply _ hx _).trans
      (Trivialization.symm_apply_apply_mk (trivializationAt E (TangentSpace I) x₀) hx v))

/-- The inclusion `v ↦ (x, v)` of the tangent space at `x`, which is the model space `E`, into
the tangent bundle is smooth. This is the tangent-bundle case of Tau Ceti's
`TauCeti.Manifold.contMDiff_totalSpaceMk`. -/
theorem contMDiff_totalSpaceMk {n : WithTop ℕ∞} (x : M) :
    ContMDiff 𝓘(𝕜, E) I.tangent n fun v : E ↦ (⟨x, v⟩ : TangentBundle I M) := by
  -- The tangent spaces have no global norm instances; each of them is `E` by definition.
  let iN : ∀ x : M, NormedAddCommGroup (TangentSpace I x) := fun _ ↦ ‹NormedAddCommGroup E›
  let iS : ∀ x : M, NormedSpace 𝕜 (TangentSpace I x) := fun _ ↦ ‹NormedSpace 𝕜 E›
  exact @TauCeti.Manifold.contMDiff_totalSpaceMk n 𝕜 M E (TangentSpace I) _ _ _ _ iN iS
    _ _ _ _ _ I _ _ (inferInstance : FiberBundle E (TangentSpace I))
    (inferInstance : VectorBundle 𝕜 E (TangentSpace I)) x

end TangentBundle

end
