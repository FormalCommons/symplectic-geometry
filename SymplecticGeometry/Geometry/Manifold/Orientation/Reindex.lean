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
bundles, and that reindexing along two casts `Fin m ≃ Fin n ≃ Fin k` is reindexing along their
composite cast (`TauCeti.Manifold.Orientation.reindex_finCongr_reindex_finCongr`), as Tau Ceti's
`Orientation.reindex_finCongr_reindex_finCongr` does for orientations of a module.
-/

public section

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {ι ι' ι'' : Type*} [Fintype ι] [Fintype ι'] [Fintype ι'']

/-- Reindexing along a composite of equivalences is reindexing along each in turn. -/
theorem reindex_trans (e : ι ≃ ι') (e' : ι' ≃ ι'') (o : Orientation I M ι) :
    o.reindex (e.trans e') = (o.reindex e).reindex e' := by
  induction o using Orientation.inductionOn with | h l =>
    rw [reindex_mk, reindex_mk, reindex_mk]
    congr 1
    ext α x <;> simp [_root_.Orientation.reindex_trans]

/-- Reindexing along two casts `Fin m ≃ Fin n ≃ Fin k` is reindexing along their composite
cast. -/
@[simp]
theorem reindex_finCongr_reindex_finCongr {m n k : ℕ} (h : m = n) (h' : n = k)
    (o : Orientation I M (Fin m)) :
    (o.reindex (finCongr h)).reindex (finCongr h') = o.reindex (finCongr (h.trans h')) := by
  subst h h'
  rw [finCongr_refl, reindex_refl, reindex_refl]

end TauCeti.Manifold.Orientation
