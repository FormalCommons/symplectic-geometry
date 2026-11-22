/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
import TauCeti.Topology.ComplexProjectiveSpace.Hopf.Exact

/-!
# Complex projective space as a projectivization is simply connected

Tau Ceti proves that its sphere-quotient model `ComplexProjectiveSpace m` of `ℂℙᵐ` is simply
connected (`TauCeti.ComplexProjectiveSpace.instSimplyConnectedSpace`). This file carries that
across Tau Ceti's homeomorphism `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization` to
the projectivization `ℙ ℂ (Fin (m + 1) → ℂ)`, the form of `ℂℙᵐ` that carries Tau Ceti's complex
manifold structure, as an instance.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace Projectivization

/-- The complex projective space `ℙ ℂ (Fin (m + 1) → ℂ)` is simply connected. -/
instance instSimplyConnectedSpaceFinComplex (m : ℕ) :
    SimplyConnectedSpace (ℙ ℂ (Fin (m + 1) → ℂ)) :=
  (TauCeti.ComplexProjectiveSpace.homeomorphProjectivization m).toHomotopyEquiv
    |>.simplyConnectedSpace_iff.1 inferInstance

end Projectivization

end
