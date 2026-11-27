/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.SmoothEmbedding.Diffeomorph
import TauCeti.Geometry.Manifold.SmoothEmbedding.Graph

/-!
# Smooth embeddings given by graphs with exchanged factors

Tau Ceti's `ContMDiff.isSmoothEmbedding_graph` says that the graph `x ↦ (x, f x)` of a smooth map
`f : M → N` between boundaryless manifolds is a smooth embedding. This file gives the same for the
graph with its factors exchanged, `x ↦ (f x, x)`, when both models are finite-dimensional: it is
the image of the graph under the diffeomorphism `Diffeomorph.prodComm`, transported by Tau Ceti's
`Diffeomorph.isSmoothEmbedding_comp`.

## Main results

* `ContMDiff.isSmoothEmbedding_graph_swap`: the map `x ↦ (f x, x)` is a smooth embedding.
-/

public section

open scoped Manifold ContDiff

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- The graph `x ↦ (f x, x)` of a smooth map `f : M → N`, with its factors exchanged, is a smooth
embedding of `M` into `N × M`. -/
theorem ContMDiff.isSmoothEmbedding_graph_swap {f : M → N} (hf : ContMDiff I J ∞ f) :
    Manifold.IsSmoothEmbedding I (J.prod I) ∞ (fun x ↦ (f x, x)) :=
  (Diffeomorph.prodComm I J M N ∞).isSmoothEmbedding_comp (by simp) hf.isSmoothEmbedding_graph

end
