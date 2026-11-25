/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Distribution.Horizontal

/-!
# Horizontality is a local property

Tau Ceti's `TauCeti.IsHorizontalMap J D f` asks that the tangent images of `f` lie in the
distribution `D`. Since a tangent map at a point depends only on the germ of `f` there, a map that
near every point agrees with some horizontal map is horizontal
(`TauCeti.IsHorizontalMap.of_forall_eventuallyEq`). This is how curves glued from horizontal
pieces are seen to be horizontal.
-/

public section

open Filter
open scoped Manifold Topology

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  {D : Π x : M, Submodule 𝕜 (TangentSpace I x)} {f : N → M}

/-- A map that agrees near each point with some horizontal map is horizontal. -/
theorem IsHorizontalMap.of_forall_eventuallyEq
    (h : ∀ y, ∃ g : N → M, IsHorizontalMap J D g ∧ f =ᶠ[𝓝 y] g) : IsHorizontalMap J D f := by
  refine isHorizontalMap_iff.2 fun y v ↦ ?_
  obtain ⟨g, hg, hfg⟩ := h y
  rw [hfg.mfderiv_eq, hfg.eq_of_nhds]
  exact hg.mfderiv_mem y v

end TauCeti

end
