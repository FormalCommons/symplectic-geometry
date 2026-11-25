/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Topology.VectorBundle.Coordinates

/-!
# Basic facts about vector-bundle cores

* `VectorBundleCore.ext`: a vector-bundle core is determined by its chart domains, its preferred
  charts and its transitions, since the remaining fields are propositions.
* `VectorBundleCore.fiberEquiv`: the identification of each fibre of a core with its model fibre,
  under which the inverse of a chart is a coordinate change
  (`VectorBundleCore.fiberEquiv_localTriv_symm`).
* `VectorBundleCore.inChartCoordinates_id`: the chart expression of the identity, between two
  charts at a point of both, is their coordinate change.
-/

public section

/-- A vector-bundle core is determined by its chart domains, its preferred charts and its
transitions. -/
theorem VectorBundleCore.ext {R B F ι : Type*} [NontriviallyNormedField R] [TopologicalSpace B]
    [NormedAddCommGroup F] [NormedSpace R F] {Z Z' : VectorBundleCore R B F ι}
    (hbase : Z.baseSet = Z'.baseSet) (hindex : Z.indexAt = Z'.indexAt)
    (hcoord : Z.coordChange = Z'.coordChange) : Z = Z' := by
  cases Z; cases Z'
  simp only at hbase hindex hcoord
  subst hbase hindex hcoord
  rfl

open Bundle

namespace VectorBundleCore

variable {R B F ι : Type*} [NontriviallyNormedField R] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace R F] (Z : VectorBundleCore R B F ι)

/-- The fibre of a vector-bundle core at `b` is its model fibre `F`: the identity, as a continuous
linear equivalence. -/
def fiberEquiv (b : B) : Z.Fiber b ≃L[R] F :=
  ContinuousLinearEquiv.refl R F

theorem fiberEquiv_def (b : B) : Z.fiberEquiv b = ContinuousLinearEquiv.refl R F :=
  (rfl)

/-- The point `v` of the chart `i` over `b` is the vector `Z.coordChange i (Z.indexAt b) b v` of
the fibre, read in `F`. -/
theorem fiberEquiv_localTriv_symm (i : ι) {b : B} (hb : b ∈ (Z.localTriv i).baseSet) (v : F) :
    Z.fiberEquiv b ((Z.localTriv i).symm b v) = Z.coordChange i (Z.indexAt b) b v :=
  congrArg (Z.fiberEquiv b) (Z.localTriv_symm_apply i hb v)

/-- The point `v` of the trivialization at `a`, over `b`, is the vector
`Z.coordChange (Z.indexAt a) (Z.indexAt b) b v` of the fibre, read in `F`. -/
theorem fiberEquiv_trivializationAt_symm {a b : B}
    (hb : b ∈ (trivializationAt F Z.Fiber a).baseSet) (v : F) :
    Z.fiberEquiv b ((trivializationAt F Z.Fiber a).symm b v) =
      Z.coordChange (Z.indexAt a) (Z.indexAt b) b v :=
  Z.fiberEquiv_localTriv_symm _ hb v

/-- The chart expression of the identity, between two charts of a core at a point of both, is
their coordinate change. -/
theorem inChartCoordinates_id {i j : ι} {x : B} (hi : x ∈ Z.baseSet i) (hj : x ∈ Z.baseSet j) :
    Z.inChartCoordinates Z i j x (ContinuousLinearMap.id R F) = Z.coordChange i j x := by
  ext v : 1
  rw [inChartCoordinates_apply, ContinuousLinearMap.id_apply,
    Z.coordChange_comp _ _ _ x ⟨⟨hi, Z.mem_baseSet_at x⟩, hj⟩]

end VectorBundleCore
