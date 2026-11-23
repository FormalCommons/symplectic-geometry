/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic

/-!
# Basic facts about diffeotopies

For a diffeotopy `φ_t`, `t ∈ [0, 1]`, of a manifold `M` (`TauCeti.Diffeotopy`), of any smoothness,
`φ_t x` lies in the connected component of `x`, since `t ↦ φ_t x` is a path from `x`
(`TauCeti.Diffeotopy.connectedComponent_apply`).
-/

public section

open Set
open scoped ContDiff

namespace TauCeti.Diffeotopy

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- A diffeotopy moves every point inside its connected component: `φ_t x` lies in the connected
component of `x`. -/
theorem connectedComponent_apply (Φ : Diffeotopy J n M) (p : unitInterval × M) :
    connectedComponent (Φ p) = connectedComponent p.2 := by
  have hc : Continuous fun s : unitInterval ↦ Φ (s, p.2) :=
    Φ.contMDiff.continuous.comp (continuous_id.prodMk continuous_const)
  have hsub := (isPreconnected_univ.image _ hc.continuousOn).subset_connectedComponent
    ⟨0, mem_univ _, Φ.apply_zero p.2⟩
  exact (connectedComponent_eq (hsub ⟨p.1, mem_univ _, rfl⟩)).symm

end TauCeti.Diffeotopy

end
