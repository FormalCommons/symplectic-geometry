/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving

/-!
# Reindexing orientations preserved by a map

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/Orientation/Preserving.lean`, taken
from Tau Ceti's commit `b7f2438cb64bbb45f96ce4471625dc1a510e918c`, which the pinned version of
Tau Ceti does not contain yet. It holds one declaration of that file:

* `TauCeti.Manifold.Orientation.IsOrientationPreservingAt.reindex`: reindexing both orientations
  along the same equivalence of index types keeps a map orientation preserving.

Changes: this module docstring; the imports, reduced to Tau Ceti's file itself, whose pinned
version has every other declaration that the proof uses; and, since the pinned version does not
expose the definition of `IsOrientationPreservingAt`, the proof takes the predicate apart and puts
it back together through `isOrientationPreservingAt_iff`. The statement and its docstring are as
in Tau Ceti.
-/

public section

noncomputable section

open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [FiniteDimensional ℝ E]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  [TopologicalSpace M'] [ChartedSpace H' M'] [FiniteDimensional ℝ E']
  {ι : Type*} [Fintype ι]

/-- Reindexing both orientations along the same equivalence of index types does not change
whether a map preserves them. -/
theorem IsOrientationPreservingAt.reindex [IsManifold I 1 M] [IsManifold I' 1 M'] {ι' : Type*}
    [Fintype ι'] {o : Manifold.Orientation I M ι} {o' : Manifold.Orientation I' M' ι} {f : M → M'}
    {x : M} (h : IsOrientationPreservingAt o o' f x) (σ : ι ≃ ι') :
    IsOrientationPreservingAt (o.reindex σ) (o'.reindex σ) f x := by
  obtain ⟨e, he, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 h
  exact (isOrientationPreservingAt_iff _ _ _ _).2 ⟨e, he, by
    rw [orientationAt_reindex, orientationAt_reindex, _root_.Orientation.map_reindex, hmap]⟩

end TauCeti.Manifold.Orientation

end
