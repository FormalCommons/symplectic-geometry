/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothIsotopy.Orientation

/-!
# The ambient disc theorem with an orientation-preserving diffeomorphism

Tau Ceti's `TauCeti.SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq` moves one smooth
embedding of `E` into a connected oriented manifold onto another near the origin by a
diffeomorphism. This file records that the diffeomorphism can be taken to preserve the
orientation: it is the final map of a diffeotopy, which preserves orientation by
`TauCeti.Diffeotopy.isOrientationPreservingAt_final`.

## Main results

* `TauCeti.SmoothEmbedding.exists_diffeomorph_comp_eventuallyEq_and_isOrientationPreservingAt`:
  two orientation-preserving smooth embeddings of `E` into a connected oriented manifold agree
  near the origin after an orientation-preserving diffeomorphism.

## References

* [R. Palais, *Extending diffeomorphisms*][Palais1960].
* [M. Hirsch, *Differential Topology*][Hirsch1976], Chapter 8, Theorem 3.1.
-/

public section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace TauCeti.SmoothEmbedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι : Type*} [Fintype ι]

/-- On a connected oriented manifold, two smooth embeddings of `E` which preserve the orientations
`o` of `E` and `oM` of `M` at the origin agree near the origin after an orientation-preserving
diffeomorphism of `M`. -/
theorem exists_diffeomorph_comp_eventuallyEq_and_isOrientationPreservingAt [T2Space M]
    [PreconnectedSpace M] (f g : SmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ E M)
    (o : Manifold.Orientation 𝓘(ℝ, E) E ι) (oM : Manifold.Orientation 𝓘(ℝ, E) M ι)
    (hf : o.IsOrientationPreservingAt oM f 0) (hg : o.IsOrientationPreservingAt oM g 0) :
    ∃ φ : M ≃ₘ^∞⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M, φ ∘ f =ᶠ[𝓝 0] g ∧
      ∀ x, oM.IsOrientationPreservingAt oM φ x := by
  obtain ⟨Φ, -, -, -, hΦ⟩ := f.exists_diffeotopy_eqOn_of_isOrientationPreservingAt g o oM hf hg
    (isCompact_closedBall (0 : E) 1)
  exact ⟨Φ.final, hΦ.eventuallyEq_of_mem (closedBall_mem_nhds 0 one_pos),
    Φ.isOrientationPreservingAt_final (by simp) oM⟩

end TauCeti.SmoothEmbedding

end
