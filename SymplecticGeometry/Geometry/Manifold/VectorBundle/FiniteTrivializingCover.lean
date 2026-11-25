/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import SymplecticGeometry.Topology.VectorBundle.FiniteTrivializingCover
import SymplecticGeometry.Geometry.Manifold.CoveringDimension
import SymplecticGeometry.Topology.CoveringDimension.SigmaCompact

/-!
# Finite trivializing covers of vector bundles over manifolds

Every vector bundle over a Hausdorff, σ-compact space charted on `H`, with a model with corners
`I : ModelWithCorners ℝ EB H` and `EB` finite-dimensional, has a finite trivializing cover.

The base is locally compact (`Manifold.locallyCompact_of_finiteDimensional`), and its compact
subsets have covering dimension at most `finrank ℝ EB`
(`IsCompact.coveringDimLE_finrank_of_chartedSpace`).
So the open cover by the base sets of the trivializations `trivializationAt` has a refinement
with a subordinate partition of unity in which every point lies in the supports of at most
`3 * (finrank ℝ EB + 1)` functions (`SymplecticGeometry.exists_isSubordinate_card_finsupport_le`),
and `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_card_finsupport_le` turns it into a
finite trivializing cover. This is the argument of Milnor–Stasheff, Lemma 5.9, for a base of
finite covering dimension.

## Main declarations

* `SymplecticGeometry.Bundle.HasFiniteTrivializingCover.of_chartedSpace`: the finite
  trivializing cover.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton University Press, 1974, Lemma 5.9.
* J. R. Munkres, *Topology*, 2nd ed., Prentice Hall, 2000, §50
-/

public section

open Bundle Set

namespace SymplecticGeometry.Bundle

variable {𝕜 B F EB H : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)] [∀ x, TopologicalSpace (E x)]
  [FiberBundle F E] [VectorBundle 𝕜 F E]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB] [TopologicalSpace H]

/-- Every vector bundle over a Hausdorff, σ-compact space charted on `H`, with a model with
corners `I : ModelWithCorners ℝ EB H` and `EB` finite-dimensional, has a finite trivializing
cover. -/
theorem HasFiniteTrivializingCover.of_chartedSpace (I : ModelWithCorners ℝ EB H)
    [ChartedSpace H B] [T2Space B] [SigmaCompactSpace B] :
    HasFiniteTrivializingCover 𝕜 F E := by
  have : LocallyCompactSpace B := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨κ, c, ρ, hρ, hcard⟩ := exists_isSubordinate_card_finsupport_le
    (fun _ hK ↦ hK.coveringDimLE_finrank_of_chartedSpace I)
    (fun x : B ↦ (trivializationAt F E x).baseSet) (fun x ↦ (trivializationAt F E x).open_baseSet)
    (eq_univ_of_forall fun x ↦ mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F E x⟩)
  exact .of_card_finsupport_le ρ (fun k ↦ trivializationAt F E (c k)) hρ hcard

end SymplecticGeometry.Bundle

end
