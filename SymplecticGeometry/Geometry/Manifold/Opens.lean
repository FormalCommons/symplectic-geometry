/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.HasGroupoid
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Open subsets of a charted space as objects of `TopCat`

An open set `W` of a charted space `X` carries the restricted atlas
(`TopologicalSpace.Opens.instChartedSpace`). The instance
`TopologicalSpace.Opens.instChartedSpaceToTopCatObj` gives the same atlas to the object
`(Opens.toTopCat X).obj W` of `TopCat`, the form in which open sets appear in the Mayer–Vietoris
sequences indexed by `Opens X`. Instance search does not see through `Opens.toTopCat`, so the
instance is needed.

This instance is from Tau Ceti's main branch (`TauCeti/Geometry/Manifold/Opens.lean`, same name), as
of the commit `a2b27244398126b7be07d28c3ce0d849e4ca2458` (TauCetiProject/TauCeti#42569), not yet in
the pinned release; it is stated here under its Tau Ceti name, so that moving Tau Ceti past it
deletes this file without renames.
-/

public section

noncomputable section

open CategoryTheory

universe u

namespace TopologicalSpace.Opens

/-- An open subset of a charted space, as an object of `TopCat`, is a charted space, with the
restricted atlas. -/
instance instChartedSpaceToTopCatObj {H : Type*} [TopologicalSpace H] {X : TopCat.{u}}
    [ChartedSpace H X] (W : Opens X) : ChartedSpace H ((toTopCat X).obj W) :=
  TopologicalSpace.Opens.instChartedSpace (H := H) (M := X) W

end TopologicalSpace.Opens

end
