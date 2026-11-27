/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.SigmaCompact
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless

/-!
# Topology of the boundaryless model of a manifold

Tau Ceti's `TauCeti.BoundarylessModel I M` is a copy of `M` with the same topology, and
`TauCeti/Geometry/Manifold/ModelTransport/Boundaryless.lean` gives it the separation, compactness
and connectedness instances of `M`. This file adds the two more that the library needs.

## Main results

* `TauCeti.BoundarylessModel.instSigmaCompactSpace`: the copy of a σ-compact space is
  σ-compact.
* `TauCeti.BoundarylessModel.instSecondCountableTopology`: the copy of a second countable space
  is second countable.
-/

public section

namespace TauCeti.BoundarylessModel

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]

/-- The model copy of a σ-compact space is σ-compact. -/
instance instSigmaCompactSpace [SigmaCompactSpace M] :
    SigmaCompactSpace (BoundarylessModel I M) :=
  inferInstanceAs (SigmaCompactSpace M)

/-- The model copy of a second countable space is second countable. -/
instance instSecondCountableTopology [SecondCountableTopology M] :
    SecondCountableTopology (BoundarylessModel I M) :=
  inferInstanceAs (SecondCountableTopology M)

end TauCeti.BoundarylessModel

end
