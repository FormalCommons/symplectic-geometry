/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import SymplecticGeometry.Geometry.Manifold.Complex.Blowup.Model
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import SymplecticGeometry.Topology.ComplexProjectiveSpace.SimplyConnected

/-!
# The exceptional divisor of the model blowup is simply connected

For `E = ℂⁿ⁺¹`, the zero section `BlowupModel.zeroSection` is an embedding of `ℙ ℂ E` onto the
exceptional divisor of the model blowup of `E` at `0` (`BlowupModel.isEmbedding_zeroSection`), so
the divisor is homeomorphic to `ℙ ℂ E` and hence simply connected
(`Projectivization.instSimplyConnectedSpaceComplex`).

## Main results

* `SymplecticGeometry.BlowupModel.isSimplyConnected_exceptionalDivisor`: the exceptional divisor
  is simply connected.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed.][McDuffSalamon2017],
  §7.1.
-/

public section

open scoped LinearAlgebra.Projectivization

namespace SymplecticGeometry

namespace BlowupModel

variable (n : ℕ) in
/-- The exceptional divisor of the model blowup is simply connected: the zero section embeds the
simply connected space `ℙ ℂ (Fin (n + 1) → ℂ)` onto it. -/
theorem isSimplyConnected_exceptionalDivisor : IsSimplyConnected (exceptionalDivisor n) := by
  rw [exceptionalDivisor_eq_range]
  exact isEmbedding_zeroSection.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

end BlowupModel

end SymplecticGeometry

end
