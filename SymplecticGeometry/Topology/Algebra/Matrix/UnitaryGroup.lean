/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective

/-!
# Continuity of the unit scalars

The map `c ↦ c • 1` from `unitary R` to the unitary matrix group `Matrix.unitaryGroup n R`,
Tau Ceti's `Matrix.UnitaryGroup.scalarHom`, is continuous for the subspace topologies coming
from `R` and from the entrywise topology on matrices
(`Matrix.UnitaryGroup.continuous_scalarHom`).
-/

public section

namespace Matrix.UnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R] [StarRing R]
  [TopologicalSpace R]

/-- The unit scalars `c ↦ c • 1` form a continuous map `unitary R → unitaryGroup n R`. -/
@[fun_prop]
theorem continuous_scalarHom : Continuous (scalarHom n R) :=
  continuous_induced_rng.2 <| by
    simp only [Function.comp_def, coe_scalarHom, scalar_apply]
    fun_prop

end Matrix.UnitaryGroup

end
