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
* `TauCeti.Diffeotopy.contMDiffOn_dite_comp`: for a smooth diffeotopy `φ_t` of an open subset
  `U` and a family `k_t` smooth on `[0, 1] × U`, the family equal to `k_t ∘ φ_t` on `U` and to
  `k_t` elsewhere is smooth on `[0, 1] × U`.
-/

public section

open Set TopologicalSpace
open scoped ContDiff Manifold

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

open Classical in
/-- Let `φ_t` be a smooth diffeotopy of an open subset `U` of `M`, and `k` a family of maps
`[0, 1] × M → N`, smooth on `[0, 1] × U`. The family equal to `k_t ∘ φ_t` on `U` and to `k_t`
elsewhere is smooth on `[0, 1] × U`. -/
theorem contMDiffOn_dite_comp {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N]
    [ChartedSpace H' N] {U : Opens M} (Φ : Diffeotopy J ∞ U) {k : unitInterval × M → N}
    (hk : ContMDiffOn ((𝓡∂ 1).prod J) I' ∞ k (univ ×ˢ U)) :
    ContMDiffOn ((𝓡∂ 1).prod J) I' ∞
      (fun p ↦ if h : p.2 ∈ U then k (p.1, Φ (p.1, ⟨p.2, h⟩)) else k p) (univ ×ˢ U) := by
  have hg : ContMDiff ((𝓡∂ 1).prod J) I' ∞ (fun p : unitInterval × U ↦ k (p.1, Φ p)) :=
    hk.comp_contMDiff (contMDiff_fst.prodMk (contMDiff_subtypeVal.comp Φ.contMDiff))
      fun p ↦ ⟨mem_univ _, (Φ p).property⟩
  -- On the open set `W = [0, 1] × U`, the family is `g` composed with `(t, x) ↦ (t, ⟨x, _⟩)`.
  let W : Opens (unitInterval × M) := ⟨univ ×ˢ U, isOpen_univ.prod U.isOpen⟩
  have hψ : ContMDiff ((𝓡∂ 1).prod J) J ∞ (fun p : W ↦ (⟨p.val.2, p.property.2⟩ : U)) :=
    fun p ↦
      (ContMDiffAt.subtypeVal_comp_iff U _ p).1 ((contMDiff_snd.comp contMDiff_subtypeVal) p)
  intro p hp
  refine (contMDiffAt_subtype_iff (U := W) (x := ⟨p, hp⟩)).1 ?_ |>.contMDiffWithinAt
  exact ((hg.comp ((contMDiff_fst.comp contMDiff_subtypeVal).prodMk hψ)) ⟨p, hp⟩
    ).congr_of_eventuallyEq (Filter.Eventually.of_forall fun q ↦ dite_eq_left q.property.2)

end TauCeti.Diffeotopy

end
