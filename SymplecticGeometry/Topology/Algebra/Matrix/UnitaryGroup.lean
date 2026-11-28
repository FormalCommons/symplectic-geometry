/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import TauCeti.LinearAlgebra.Matrix.UnitaryGroup.Projective
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Unitary
public import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic
import SymplecticGeometry.LinearAlgebra.Matrix.OrthogonalGroup.Unitary

/-!
# Continuity of maps into the unitary group

Three of Tau Ceti's maps into a unitary matrix group `Matrix.unitaryGroup n R` are continuous for
the subspace topologies coming from the entrywise topology on matrices:

* the unit scalars `c ↦ c • 1` from `unitary R`, Tau Ceti's `Matrix.UnitaryGroup.scalarHom`
  (`Matrix.UnitaryGroup.continuous_scalarHom`);
* the embedding `O(n) →* U(n)` of the real orthogonal matrices, Tau Ceti's
  `TauCeti.orthogonalComplexMatrix` (`TauCeti.continuous_orthogonalComplexMatrix`);
* the inclusion `SO(n) →* O(n)`, Tau Ceti's `Matrix.specialOrthogonalGroup.toOrthogonalGroup`
  (`Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup`).
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

/-- The inclusion `SO(n) →* O(n)` is continuous. -/
@[fun_prop]
theorem Matrix.specialOrthogonalGroup.continuous_toOrthogonalGroup {n : Type*} [Fintype n]
    [DecidableEq n] {R : Type*} [CommRing R] [TopologicalSpace R] :
    Continuous (toOrthogonalGroup (n := n) (R := R)) :=
  continuous_induced_rng.2 <| by
    simp only [Function.comp_def, coe_toOrthogonalGroup]
    exact continuous_subtypeVal

/-- Tau Ceti's embedding `TauCeti.orthogonalComplexMatrix : O(n) →* U(n)` is continuous. -/
@[fun_prop]
theorem TauCeti.continuous_orthogonalComplexMatrix {n : Type*} [Fintype n] [DecidableEq n] :
    Continuous (TauCeti.orthogonalComplexMatrix (n := n)) :=
  continuous_induced_rng.2 <| by
    simp only [Function.comp_def, TauCeti.coe_orthogonalComplexMatrix]
    fun_prop

end
