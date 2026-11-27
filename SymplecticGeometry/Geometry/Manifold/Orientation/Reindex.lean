/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Basic

/-!
# Reindexing manifold orientations

Tau Ceti's `TauCeti.Manifold.Orientation.reindex` carries an orientation of a manifold, indexed
by `ι`, along an equivalence `ι ≃ ι'`. This file shows that reindexing along a composite of
equivalences is reindexing along each in turn (`TauCeti.Manifold.Orientation.reindex_trans`), as
Tau Ceti's `TauCeti.VectorBundleOrientation.reindex_trans` does for orientations of vector
bundles, and that reindexing along `Fin n ≃ Fin n'` and back gives the orientation back.
-/

public section

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] {ι ι' ι'' : Type*} [Fintype ι] [Fintype ι'] [Fintype ι'']

/-- Reindexing along a composite of equivalences is reindexing along each in turn. -/
theorem reindex_trans (e : ι ≃ ι') (e' : ι' ≃ ι'') (o : Orientation I M ι) :
    o.reindex (e.trans e') = (o.reindex e).reindex e' :=
  ext fun x ↦ by
    rw [orientationAt_reindex, orientationAt_reindex, orientationAt_reindex,
      _root_.Orientation.reindex_trans]

/-- Reindexing along `Fin n ≃ Fin n'` and then back along `Fin n' ≃ Fin n` gives the orientation
back. -/
theorem reindex_finCongr_reindex_finCongr {n n' : ℕ} (o : Orientation I M (Fin n))
    (h : n = n') (h' : n' = n) : (o.reindex (finCongr h)).reindex (finCongr h') = o := by
  subst h
  rw [← reindex_trans, finCongr_refl, Equiv.refl_trans, reindex_refl]

end TauCeti.Manifold.Orientation
