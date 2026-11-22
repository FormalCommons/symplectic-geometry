/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Basic

/-!
# Basic facts about diffeotopies

For a diffeotopy `φ_t`, `t ∈ [0, 1]`, of a manifold `M` (`TauCeti.Diffeotopy`), of any smoothness:

* `TauCeti.Diffeotopy.connectedComponent_apply`: `φ_t x` lies in the connected component of `x`,
  since `t ↦ φ_t x` is a path from `x`.
* `TauCeti.Diffeotopy.apply_mk_symm_apply`, `TauCeti.Diffeotopy.symm_apply_mk_apply`: the maps
  `φ_t` and `φ_t⁻¹` are inverse to each other, stated with the coercions `Φ (t, ·)` and
  `Φ.symm (t, ·)`. Tau Ceti's `TauCeti.Diffeotopy.apply_symm_apply` and
  `TauCeti.Diffeotopy.symm_apply_apply` state this through `toDiffeomorph`, a form that `rw` and
  `simp` do not match against `Φ (t, Φ.symm (t, y))`.
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

/-- At each time `t`, the map `φ_t` undoes its inverse: `φ_t (φ_t⁻¹ y) = y`. -/
theorem apply_mk_symm_apply (Φ : Diffeotopy J n M) (t : unitInterval) (y : M) :
    Φ (t, Φ.symm (t, y)) = y := by
  rw [← symm_timeSlice_apply, ← timeSlice_apply, Diffeomorph.apply_symm_apply]

/-- At each time `t`, the inverse map `φ_t⁻¹` undoes `φ_t`: `φ_t⁻¹ (φ_t x) = x`. -/
theorem symm_apply_mk_apply (Φ : Diffeotopy J n M) (t : unitInterval) (x : M) :
    Φ.symm (t, Φ (t, x)) = x := by
  rw [← symm_timeSlice_apply, ← timeSlice_apply, Diffeomorph.symm_apply_apply]

end TauCeti.Diffeotopy

end
