/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
import TauCeti.Geometry.Manifold.Immersion.Differential

/-!
# Maps into a smoothly embedded manifold

Let `φ : N → P` be a `C^n` smooth embedding. Tau Ceti shows that a map `f : M → N` is `C^n`
exactly when `φ ∘ f` is (`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`). This file adds the
first-order and the embedding counterparts:

* `Manifold.IsSmoothEmbedding.mdifferentiableAt_iff_comp`: for `n ≠ 0`, `f` is differentiable at
  a point exactly when `φ ∘ f` is. The differential of `φ` has a left inverse, so Tau Ceti's
  `IsDiffImmersionAt.mdifferentiableAt_iff_comp` applies, and the continuity of `f` that it asks
  for comes from that of `φ ∘ f`, since `φ` is a topological embedding. The proof follows
  that of Tau Ceti's `Manifold.IsSmoothEmbedding.contMDiffAt_iff_comp`, with Tau Ceti's lifting
  lemma for differentiability in place of Mathlib's for smoothness.
* `Manifold.IsSmoothEmbedding.of_comp`: between boundaryless manifolds, with `N` modelled on a
  finite-dimensional space and `1 ≤ n`, if `φ ∘ f` is a smooth embedding then so is `f`. It is an
  immersion by Tau Ceti's `Manifold.IsSmoothEmbedding.isImmersion_of_isImmersion_comp`, and a
  topological embedding by Mathlib's `Topology.IsEmbedding.of_comp_iff`.

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Chapter 1.
-/

public section

open Set
open scoped Manifold ContDiff

namespace Manifold.IsSmoothEmbedding

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E E' E'' H G G' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {K : ModelWithCorners 𝕜 E'' G'}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace P] [ChartedSpace G' P]
  {n : ℕ∞ω} {f : M → N} {φ : N → P}

/-- A map into a smoothly embedded manifold is differentiable at a point if and only if its
composite with the embedding is. No separate continuity assumption is needed. -/
theorem mdifferentiableAt_iff_comp (hφ : IsSmoothEmbedding J K n φ) (hn : n ≠ 0) {x : M} :
    MDifferentiableAt I J f x ↔ MDifferentiableAt I K (φ ∘ f) x := by
  rw [(hφ.isImmersion.isDiffImmersionAt hn (f x)).mdifferentiableAt_iff_comp]
  exact ⟨And.right, fun h ↦ ⟨hφ.isEmbedding.continuousAt_iff.2 h.continuousAt, h⟩⟩

end NontriviallyNormedField

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]
  {E E' E'' H G G' M N P : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [FiniteDimensional 𝕜 E'] [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [TopologicalSpace H] [TopologicalSpace G] [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' G} {K : ModelWithCorners 𝕜 E'' G'}
  [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace G N]
  [TopologicalSpace P] [ChartedSpace G' P]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N] {f : M → N} {φ : N → P}

/-- Between manifolds without boundary, the middle one with a finite-dimensional model, a map
whose composite with a `C^n` smooth embedding, `1 ≤ n`, is a `C^n` smooth embedding is itself a
`C^n` smooth embedding. -/
theorem of_comp (hφ : IsSmoothEmbedding J K n φ) (hn : 1 ≤ n)
    (h : IsSmoothEmbedding I K n (φ ∘ f)) : IsSmoothEmbedding I J n f :=
  ⟨hφ.isImmersion_of_isImmersion_comp hn h.isImmersion,
    hφ.isEmbedding.of_comp_iff.1 h.isEmbedding⟩

end RCLike

end Manifold.IsSmoothEmbedding

end
