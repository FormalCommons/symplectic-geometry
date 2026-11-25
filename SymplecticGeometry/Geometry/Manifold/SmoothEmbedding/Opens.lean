/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph

/-!
# The inclusion of one open subset into a larger one, as a smooth embedding

For open subsets `U ≤ V` of a manifold `M`, the inclusion `Opens.inclusion h : U → V` is a
smooth embedding of open submanifolds. This file bundles it as
`TauCeti.SmoothEmbedding.inclusion h`, next to Tau Ceti's `TauCeti.SmoothEmbedding.ofOpens`, the
inclusion of an open subset into the whole manifold. The bundled `C^n` map
`(SmoothEmbedding.inclusion h).toContMDiffMap` is the inclusion in the form that
`ContMDiffMap.comp` takes, so that `simp` can evaluate composites with it.

The embedding property is that of `ofOpens U`, corestricted to `V` by Tau Ceti's
`Manifold.IsSmoothEmbedding.codRestrict`, and `inclusion h` is that corestriction
(`TauCeti.SmoothEmbedding.codRestrict_ofOpens`).

## Main definitions

* `TauCeti.SmoothEmbedding.inclusion`: the inclusion `U → V` of open subsets `U ≤ V`, as a
  bundled smooth embedding.
-/

public section

open scoped Manifold ContDiff

open TopologicalSpace

namespace TauCeti.SmoothEmbedding

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M] {U V W : Opens M}

/-- The inclusion `U → V` of open subsets `U ≤ V` of a manifold, as a bundled smooth
embedding. -/
noncomputable def inclusion (h : U ≤ V) : SmoothEmbedding I I n U V :=
  ofIsSmoothEmbedding (Opens.inclusion h)
    ((Manifold.IsSmoothEmbedding.of_opens U).codRestrict V fun x ↦ h x.property)

@[simp]
theorem coe_inclusion (h : U ≤ V) :
    ⇑(inclusion (I := I) (n := n) h) = Opens.inclusion h := by
  rw [inclusion, coe_ofIsSmoothEmbedding]

@[simp]
theorem inclusion_apply (h : U ≤ V) (x : U) :
    inclusion (I := I) (n := n) h x = Opens.inclusion h x := by
  rw [coe_inclusion]

/-- The corestriction of `ofOpens U` to a larger open subset `V` is the inclusion `U → V`. -/
theorem codRestrict_ofOpens (h : U ≤ V) :
    (ofOpens (I := I) (n := n) U).codRestrict V (fun x ↦ h (by simp)) = inclusion h :=
  ext fun x ↦ Subtype.ext <| by simp

@[simp]
theorem inclusion_refl : inclusion (I := I) (n := n) (le_refl U) = id :=
  ext fun x ↦ by simp

end TauCeti.SmoothEmbedding

end
