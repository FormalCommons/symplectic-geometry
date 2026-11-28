/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Basic

/-!
# The boundary of the cube `I × I^N`

Tau Ceti's `TauCeti.Cube.prodBoundary N` is the boundary of the cube `I × I^N`: the points whose
first coordinate is `0` or `1`, or whose second lies on the boundary of `I^N`. This file proves
that it is closed for a finite `N` (`TauCeti.Cube.isClosed_prodBoundary`), as
`Cube.isClosed_boundary` does for the boundary of `I^N`.
-/

public section

open scoped unitInterval Topology.Homotopy

namespace TauCeti

/-- For a finite `N`, the boundary of the cube `I × I^N` is closed. -/
theorem Cube.isClosed_prodBoundary (N : Type*) [Finite N] : IsClosed (Cube.prodBoundary N) := by
  have h : Cube.prodBoundary N =
      ({y | y.1 = 0} ∪ {y | y.1 = 1}) ∪ Prod.snd ⁻¹' Cube.boundary N := by
    ext y
    simp
  rw [h]
  exact ((isClosed_eq continuous_fst continuous_const).union
    (isClosed_eq continuous_fst continuous_const)).union
    (Cube.isClosed_boundary.preimage continuous_snd)

end TauCeti

end
