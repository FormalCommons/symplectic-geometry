/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Finite covers of a compact manifold by charts that are partial diffeomorphisms

On a compact Hausdorff manifold without boundary, modelled on a finite-dimensional real space
`E`, finitely many of the restricted extended charts `TauCeti.extChartPartialDiffeomorph I ∞ x`,
which are partial diffeomorphisms from `M` onto open subsets of `E`, cover `M`, and a smooth
partition of unity is subordinate to their sources
(`TauCeti.exists_finite_partialDiffeomorph_cover`). Local arguments on forms, carried out in each
chart and glued with the partition of unity, start from such a cover.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 2.23.
-/

public section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

variable (I M) in
/-- A compact Hausdorff manifold without boundary is covered by the sources of finitely many
restricted extended charts, which are partial diffeomorphisms onto open subsets of the model
space, with a smooth partition of unity subordinate to these sources. -/
theorem exists_finite_partialDiffeomorph_cover [IsManifold I ∞ M] [BoundarylessManifold I M]
    [T2Space M] [CompactSpace M] :
    ∃ (N : ℕ) (c : Fin N → M) (ρ : SmoothPartitionOfUnity (Fin N) I M univ),
      ρ.IsSubordinate fun i ↦ (extChartPartialDiffeomorph I ∞ (c i)).source := by
  have hmem (x : M) : x ∈ (extChartPartialDiffeomorph I ∞ x).source :=
    (mem_extChartPartialDiffeomorph_source I ∞ x).2 BoundarylessManifold.isInteriorPoint
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (extChartPartialDiffeomorph I ∞ x).source)
    (fun x ↦ (extChartPartialDiffeomorph I ∞ x).open_source)
    fun x _ ↦ mem_iUnion.2 ⟨x, hmem x⟩
  let c : Fin t.card → M := fun i ↦ t.equivFin.symm i
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun i ↦ (extChartPartialDiffeomorph I ∞ (c i)).source)
    (fun i ↦ (extChartPartialDiffeomorph I ∞ (c i)).open_source) fun x hx ↦ by
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht hx)
      exact mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, by simpa [c] using hxy⟩
  exact ⟨t.card, c, ρ, hρ⟩

end TauCeti

end
