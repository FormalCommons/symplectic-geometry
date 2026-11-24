/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic

/-!
# Smooth families of covectors over one point

A family `y ↦ c y` of model covectors, indexed by a manifold `X`, defines the family
`y ↦ (x, c y)` of covectors at one fixed point `x` of a manifold `M`. This file shows that it is
`C^n` as a map into the cotangent bundle `T*M` whenever `c` is
(`TauCeti.CotangentBundle.contMDiff_mk_comp`).

The proof follows that of Tau Ceti's `contMDiff_tangentBundle_mk_constBase`, for the tangent
bundle: in the trivialization at `x`, a covector at `x` is its own fibre coordinate
(`TauCeti.CotangentBundle.continuousLinearMapAt_trivializationAt_self`).
-/

public section

open Bundle
open scoped Manifold

namespace TauCeti.CotangentBundle

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [TopologicalSpace HX]
  {IX : ModelWithCorners 𝕜 EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  {n : WithTop ℕ∞}

/-- A `C^n` family `c` of model covectors gives a `C^n` map `y ↦ (q, c y)` into the fibre of the
cotangent bundle over the fixed point `q`. -/
theorem contMDiff_mk_comp (q : M) {c : X → E →L[𝕜] 𝕜}
    (hc : ContMDiff IX 𝓘(𝕜, E →L[𝕜] 𝕜) n c) :
    ContMDiff IX (I.prod 𝓘(𝕜, E →L[𝕜] 𝕜)) n fun y ↦
      TotalSpace.mk' (E →L[𝕜] 𝕜) (E := fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q (c y) := by
  intro y
  refine contMDiffAt_totalSpace_iff.2 ⟨contMDiffAt_const, (hc y).congr_of_eventuallyEq ?_⟩
  exact Filter.Eventually.of_forall fun y' ↦
    ((trivializationAt (E →L[𝕜] 𝕜) (fun x : M ↦ TangentSpace I x →L[𝕜] 𝕜) q
      ).continuousLinearMapAt_apply_of_mem (R := 𝕜)
        (FiberBundle.mem_baseSet_trivializationAt _ _ q) _).symm.trans
      (continuousLinearMapAt_trivializationAt_self (I := I) q (c y'))

end TauCeti.CotangentBundle

end
