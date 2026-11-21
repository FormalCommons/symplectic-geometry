/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# Inclusions between open subsets are local diffeomorphisms

For open subsets `U ≤ W` of a manifold `M`, each charted by the restrictions of the charts of `M`,
the inclusion `Opens.inclusion h : U → W` is a `C^n` local diffeomorphism. This complements
Tau Ceti's `TauCeti.isLocalDiffeomorph_subtype_val`, which treats the inclusion of an open subset
into `M` itself: composing with `Subtype.val : W → M` gives `Subtype.val : U → M`, and the
inclusion of `W` can be cancelled on the left (`IsLocalDiffeomorphAt.of_comp_left`).

## Main results

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

/-- For open subsets `U ≤ W` of `M`, each charted by the restrictions of the charts of `M`, the
inclusion `U → W` is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_inclusion {U W : Opens M} (h : U ≤ W) :
    IsLocalDiffeomorph I I n (Opens.inclusion h) := fun x ↦
  IsLocalDiffeomorphAt.of_comp_left (f := (Subtype.val : W → M))
    (isLocalDiffeomorph_subtype_val x) (isLocalDiffeomorph_subtype_val _)
    (continuous_inclusion h).continuousAt

end TauCeti

end
