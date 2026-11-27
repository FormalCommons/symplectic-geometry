/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Boundary.Collar.Double.Basic
import SymplecticGeometry.Topology.Constructions.DoubleAlong.Connected

/-!
# The double along a collar is Hausdorff, compact and connected

The double `c.Double` of a manifold `W` along a smooth collar `c` (`Collar/Double/Basic.lean`) has
the topology of Tau Ceti's `TauCeti.DoubleAlong` of `W` along its boundary
(`TauCeti.SmoothCollar.Double.homeomorphDoubleAlong`). This file transfers the point-set
properties of that double to `c.Double`:

* the first copy `inl` of `W` is an embedding, by `TauCeti.DoubleAlong.isEmbedding_inl`;
* `c.Double` is Hausdorff when `W` is, by `TauCeti.DoubleAlong.t2Space`, since the boundary is
  closed (`ModelWithCorners.isClosed_boundary_of_finiteDimensional`);
* it is compact when `W` is, by Tau Ceti's compactness instance on `TauCeti.DoubleAlong`;
* it is connected when `W` is connected with nonempty boundary, by
  `TauCeti.DoubleAlong.connectedSpace`.

So the double of a compact connected Hausdorff manifold with nonempty boundary along a smooth
collar is a closed connected manifold. The instance `T2Space` follows Tau Ceti's
`TauCeti.SchottkyDouble.instT2Space`.

## Main results

* `TauCeti.SmoothCollar.Double.isEmbedding_inl`.
* `TauCeti.SmoothCollar.Double.instT2Space`, `Double.instCompactSpace`,
  `Double.instConnectedSpace`.

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33, 1976, Chapter 8, §2 (gluing manifolds
  along boundaries by collars).
-/

public section

open scoped Manifold ContDiff

namespace TauCeti.SmoothCollar.Double

variable {n : ℕ} {W : Type*} [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
  (c : SmoothCollar n ∞ W)

/-- The first copy `inl` of `W` in its double along a collar is a topological embedding. -/
theorem isEmbedding_inl : Topology.IsEmbedding (inl c) :=
  have heq : ⇑(homeomorphDoubleAlong c).symm ∘ DoubleAlong.inl _ = inl c :=
    funext fun w ↦ by
      rw [Function.comp_apply, Homeomorph.symm_apply_eq, homeomorphDoubleAlong_inl]
  heq ▸ (homeomorphDoubleAlong c).symm.isEmbedding.comp (DoubleAlong.isEmbedding_inl _)

/-- The double of a Hausdorff manifold along a collar is Hausdorff. -/
instance instT2Space [T2Space W] : T2Space c.Double :=
  have := DoubleAlong.t2Space _ ((𝓡∂ (n + 1)).isClosed_boundary_of_finiteDimensional (M := W))
  (homeomorphDoubleAlong c).isEmbedding.t2Space

/-- The double of a compact manifold along a collar is compact. -/
instance instCompactSpace [CompactSpace W] : CompactSpace c.Double :=
  (homeomorphDoubleAlong c).symm.compactSpace

/-- The double of a connected manifold with nonempty boundary along a collar is connected. -/
instance instConnectedSpace [ConnectedSpace W] [Nonempty ((𝓡∂ (n + 1)).boundary W)] :
    ConnectedSpace c.Double :=
  (homeomorphDoubleAlong c).symm.surjective.connectedSpace
    (homeomorphDoubleAlong c).symm.continuous

end TauCeti.SmoothCollar.Double

end
