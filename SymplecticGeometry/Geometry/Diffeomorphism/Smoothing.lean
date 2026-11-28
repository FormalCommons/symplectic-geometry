/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Topology
public import SymplecticGeometry.Geometry.Diffeomorphism.Sphere.ComplexStructure
import SymplecticGeometry.Geometry.Diffeomorphism.Orientation

/-!
# Smoothing families of diffeomorphisms

This file is about continuous families of diffeomorphisms of a compact manifold, for the weak
Whitney topology `Diffeomorph.weakWhitneyTopology` of Tau Ceti.

## Orientation-preserving diffeomorphisms of the sphere

`SymplecticGeometry.isClopen_diffPlus`: `Diff⁺(S²)`, `SymplecticGeometry.diffPlus`, is open and
closed in the diffeomorphisms of the Riemann sphere. It is the case of the sphere of
`Diffeomorph.isClopen_orientationPreservingSubgroup`.

A clopen set contains the path component of each of its points (Tau Ceti's
`IsClopen.pathComponent_subset`), so a homotopy of maps into the diffeomorphisms that starts in
`diffPlus` stays in `diffPlus` (Tau Ceti's `ContinuousMap.Homotopy.apply_mem`) and is a
homotopy of maps into `diffPlus` (`ContinuousMap.Homotopy.codRestrict`).

## References

* [M. W. Hirsch, *Differential Topology*][Hirsch1976], Graduate Texts in Mathematics 33,
  Springer, 1976, Chapter 2, §1 (the weak topology).
-/

public section

open scoped Manifold ContDiff TauCeti.ComplexManifold TauCeti.DiffeomorphWeakWhitney

namespace SymplecticGeometry

/-- `Diff⁺(S²)` is open and closed in the smooth diffeomorphisms of the Riemann sphere, for the
weak Whitney topology. -/
theorem isClopen_diffPlus :
    IsClopen (diffPlus : Set (TauCeti.Diff 𝓘(ℝ, ℂ) (OnePoint ℂ) ∞)) := by
  rw [diffPlus_def]
  exact Diffeomorph.isClopen_orientationPreservingSubgroup _ _

end SymplecticGeometry

end
