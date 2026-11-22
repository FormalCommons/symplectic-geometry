/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.SmoothEmbedding

/-!
# Smooth embeddings: smoothness at a point through the embedding

This file is a part of Tau Ceti's `TauCeti/Geometry/Manifold/SmoothEmbedding/Basic.lean`,
copied from Tau Ceti's main branch at commit `223a7bc65a9c82fcb1992411dbcd8fd53634cb3b`, which
the pinned version of Tau Ceti does not have yet. It contains one declaration,
`Manifold.IsSmoothEmbedding.contMDiffAt_iff_comp`: a map into a smoothly embedded manifold is
`C^n` at a point exactly when its composite with the embedding is, with no separate continuity
hypothesis. The pinned version has the global version
`Manifold.IsSmoothEmbedding.contMDiff_iff_comp` only. It is used by
`SymplecticGeometry/Geometry/Manifold/Instances/CompatibleComplexStructures.lean`.

Changes from Tau Ceti's text:
* the imports, the variables and the opened namespaces are only those the declaration needs.
-/

public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {H : Type*} [TopologicalSpace H] {H' : Type*} [TopologicalSpace H']
  {G' : Type*} [TopologicalSpace G']
  {I : ModelWithCorners 𝕜 E H} {J : ModelWithCorners 𝕜 E' H'}
  {J' : ModelWithCorners 𝕜 F' G'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {N' : Type*} [TopologicalSpace N'] [ChartedSpace G' N']
  {n : ℕ∞ω}

namespace Manifold.IsSmoothEmbedding

/-- A map into a smoothly embedded manifold is `C^n` at a point if and only if its composite with
the embedding is. No separate continuity assumption is needed. -/
theorem contMDiffAt_iff_comp {f : M → N} {φ : N → N'} {x : M}
    (hφ : Manifold.IsSmoothEmbedding J J' n φ) :
    ContMDiffAt I J n f x ↔ ContMDiffAt I J' n (φ ∘ f) x := by
  rw [ContMDiffAt.iff_comp_isImmersionAt (hφ.isImmersion.isImmersionAt (f x))]
  exact ⟨And.right, fun h ↦ ⟨hφ.isEmbedding.continuousAt_iff.2 h.continuousAt, h⟩⟩

end Manifold.IsSmoothEmbedding
