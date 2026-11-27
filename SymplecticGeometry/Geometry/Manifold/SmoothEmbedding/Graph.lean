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

Tau Ceti's `ContMDiff.isSmoothEmbedding_graph` says that the graph `x ↦ (x, f x)` of a `Cⁿ` map
`f : M → N` between boundaryless manifolds is a `Cⁿ` embedding. This file gives the same for the
graph with its factors exchanged, `x ↦ (f x, x)`, over a field `𝕜` with `[RCLike 𝕜]`, when
`1 ≤ n` and both models are finite-dimensional: it is the image of the graph under the
diffeomorphism `Diffeomorph.prodComm`, transported by Tau Ceti's
`Diffeomorph.isSmoothEmbedding_comp`.

## Main results

* `ContMDiff.isSmoothEmbedding_graph_swap`: the map `x ↦ (f x, x)` is a `Cⁿ` embedding.
-/

public section

open scoped ContDiff

variable {𝕜 : Type*} [RCLike 𝕜] {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace H'] {J : ModelWithCorners 𝕜 F H'} [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- For `1 ≤ n`, the graph `x ↦ (f x, x)` of a `Cⁿ` map `f : M → N`, with its factors exchanged,
is a `Cⁿ` embedding of `M` into `N × M`. -/
theorem ContMDiff.isSmoothEmbedding_graph_swap {f : M → N} (hf : ContMDiff I J n f)
    (hn : 1 ≤ n) : Manifold.IsSmoothEmbedding I (J.prod I) n (fun x ↦ (f x, x)) :=
  (Diffeomorph.prodComm I J M N n).isSmoothEmbedding_comp hn hf.isSmoothEmbedding_graph

end
