/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import SymplecticGeometry.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Maps into open subsets, and inclusions between them, as local diffeomorphisms

Let `W` be an open subset of a manifold `N`, charted by the restrictions of the charts of `N`. A
map `g` into `W` is a `C^n` local diffeomorphism at `x` exactly when its composite
`Subtype.val ∘ g` with the inclusion of `W` is one: Tau Ceti's
`TauCeti.isLocalDiffeomorph_subtype_val` makes the inclusion a local diffeomorphism, which can be
cancelled on the left (`IsLocalDiffeomorphAt.comp_iff_left`). Continuity of `g` need not be
assumed, since either side gives it, `W` carrying the subspace topology. The domain of `g` is any
manifold, for instance a nested open subset. In particular, for open subsets `U ≤ W` of `M` the
inclusion `Opens.inclusion h : U → W` is a `C^n` local diffeomorphism.

## Main results

* `TauCeti.isLocalDiffeomorphAt_subtypeVal_comp_iff`,
  `TauCeti.isLocalDiffeomorph_subtypeVal_comp_iff`: a map into an open subset is a local
  diffeomorphism exactly when its composite with the inclusion of that subset is.
* `TauCeti.isLocalDiffeomorph_inclusion`: the inclusion `U → W` of open subsets `U ≤ W` is a
  `C^n` local diffeomorphism.
-/

public section

open TopologicalSpace

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : WithTop ℕ∞}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

/-- A map `g` into an open subset `W` of `N` is a `C^n` local diffeomorphism at `x` if and only if
its composite with the inclusion `W → N` is. -/
theorem isLocalDiffeomorphAt_subtypeVal_comp_iff {W : Opens N} {g : M → W} {x : M} :
    IsLocalDiffeomorphAt I J n (Subtype.val ∘ g) x ↔ IsLocalDiffeomorphAt I J n g x :=
  ⟨fun h ↦ (IsLocalDiffeomorphAt.comp_iff_left (isLocalDiffeomorph_subtype_val _)
      (Topology.IsInducing.subtypeVal.continuousAt_iff.2 h.contMDiffAt.continuousAt)).1 h,
    fun h ↦ h.comp (hg := isLocalDiffeomorph_subtype_val _)⟩

/-- A map `g` into an open subset `W` of `N` is a `C^n` local diffeomorphism if and only if its
composite with the inclusion `W → N` is. -/
theorem isLocalDiffeomorph_subtypeVal_comp_iff {W : Opens N} {g : M → W} :
    IsLocalDiffeomorph I J n (Subtype.val ∘ g) ↔ IsLocalDiffeomorph I J n g :=
  forall_congr' fun _ ↦ isLocalDiffeomorphAt_subtypeVal_comp_iff

/-- For open subsets `U ≤ W` of `M`, each charted by the restrictions of the charts of `M`, the
inclusion `U → W` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_inclusion {U W : Opens M} (h : U ≤ W) :
    IsLocalDiffeomorph I I n (Opens.inclusion h) :=
  isLocalDiffeomorph_subtypeVal_comp_iff.1
    ((Set.val_comp_inclusion h).symm ▸ isLocalDiffeomorph_subtype_val)

end TauCeti

end
