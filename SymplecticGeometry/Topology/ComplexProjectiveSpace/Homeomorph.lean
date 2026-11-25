/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

/-!
# Projectivizations of complex vector spaces as Tau Ceti's `ℂPⁿ`

For a Hausdorff complex topological vector space `V` with `finrank ℂ V = n + 1`, this file gives
the homeomorphism `Projectivization.complexProjectiveSpaceHomeomorph` from Tau Ceti's
sphere-quotient model `ComplexProjectiveSpace n` of `ℂPⁿ` to the projectivization `ℙ ℂ V`. It is
Tau Ceti's `TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`, onto
`ℙ ℂ (Fin (n + 1) → ℂ)`, followed by the homeomorphism
`ContinuousLinearEquiv.mapProjectivization` induced by a continuous linear equivalence
`(Fin (n + 1) → ℂ) ≃L[ℂ] V`. Topological facts that Tau Ceti proves for its model, such as its
cohomology or its simple connectivity, are carried along it to `ℙ ℂ V`.
-/

public section

noncomputable section

open Module TauCeti
open scoped LinearAlgebra.Projectivization

namespace Projectivization

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul ℂ V] [T2Space V] {n : ℕ}

/-- A complex projective space `ℙ ℂ V`, for a Hausdorff complex topological vector space `V` with
`finrank ℂ V = n + 1`, is homeomorphic to Tau Ceti's `ℂPⁿ`, through Tau Ceti's
`ComplexProjectiveSpace.homeomorphProjectivization` and a continuous linear equivalence
`(Fin (n + 1) → ℂ) ≃L[ℂ] V`. -/
def complexProjectiveSpaceHomeomorph (hV : finrank ℂ V = n + 1) :
    ComplexProjectiveSpace n ≃ₜ ℙ ℂ V :=
  have : FiniteDimensional ℂ V := Module.finite_of_finrank_eq_succ hV
  (ComplexProjectiveSpace.homeomorphProjectivization n).trans
    (ContinuousLinearEquiv.ofFinrankEq (E := Fin (n + 1) → ℂ) (F := V)
      (by rw [finrank_fin_fun, hV])).mapProjectivization

end Projectivization

end
