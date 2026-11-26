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
* `VectorBundleCore.inChartCoordinates_eq_coordChange_comp`: chart expressions of one operator in
  two pairs of charts differ by the transitions between them.
* `VectorBundleCore.inChartCoordinates_smul` and `VectorBundleCore.inChartCoordinates_sum`: the
  chart expression is linear in the operator.
* `VectorBundleCore.exists_units_inv_mul_mul_eq_inChartCoordinates`: reading an endomorphism of a
  fibre in a chart is a conjugation by a unit.
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

variable {G κ : Type*} [NormedAddCommGroup G] [NormedSpace R G] {W : VectorBundleCore R B G κ}

/-- At a point of the charts `i` and `i'` of `Z` and `j` and `j'` of `W`, the chart expression of
`ϕ` from `i'` to `j'` is its chart expression from `i` to `j`, after the transition from `i'` to
`i` and before the transition from `j` to `j'`. -/
theorem inChartCoordinates_eq_coordChange_comp {i i' : ι} {j j' : κ} {x : B}
    (hi : x ∈ Z.baseSet i) (hi' : x ∈ Z.baseSet i') (hj : x ∈ W.baseSet j)
    (hj' : x ∈ W.baseSet j') (ϕ : F →L[R] G) :
    Z.inChartCoordinates W i' j' x ϕ =
      (W.coordChange j j' x).comp
        ((Z.inChartCoordinates W i j x ϕ).comp (Z.coordChange i' i x)) := by
  ext v : 1
  simp only [inChartCoordinates_apply, ContinuousLinearMap.comp_apply,
    Z.coordChange_comp i' i (Z.indexAt x) x ⟨⟨hi', hi⟩, Z.mem_baseSet_at x⟩,
    W.coordChange_comp (W.indexAt x) j j' x ⟨⟨W.mem_baseSet_at x, hj⟩, hj'⟩]

/-- The chart expression of an operator is linear in the operator: scalar multiples. -/
theorem inChartCoordinates_smul (i : ι) (j : κ) (x : B) (c : R) (ϕ : F →L[R] G) :
    Z.inChartCoordinates W i j x (c • ϕ) = c • Z.inChartCoordinates W i j x ϕ := by
  ext v : 1
  simp only [inChartCoordinates_apply, smul_apply, map_smul]

/-- The chart expression of an operator is linear in the operator: finite sums. -/
theorem inChartCoordinates_sum {α : Type*} (s : Finset α) (i : ι) (j : κ) (x : B)
    (ϕ : α → F →L[R] G) :
    Z.inChartCoordinates W i j x (∑ a ∈ s, ϕ a) = ∑ a ∈ s, Z.inChartCoordinates W i j x (ϕ a) := by
  ext v : 1
  simp only [inChartCoordinates_apply, sum_apply, map_sum]

/-- At a point of the domain of a chart `i`, reading an endomorphism of the fibre in the chart `i`
is a conjugation by a unit of the ring of endomorphisms of the model fibre. -/
theorem exists_units_inv_mul_mul_eq_inChartCoordinates {i : ι} {x : B} (hx : x ∈ Z.baseSet i) :
    ∃ U : (F →L[R] F)ˣ, ∀ M : F →L[R] F, ↑U⁻¹ * M * ↑U = Z.inChartCoordinates Z i i x M := by
  have h {j k : ι} (hj : x ∈ Z.baseSet j) (hk : x ∈ Z.baseSet k) :
      Z.coordChange k j x * Z.coordChange j k x = 1 :=
    (Z.coordChange_comp_coordChange_eq_id hj hk).trans ContinuousLinearMap.one_def.symm
  refine ⟨⟨Z.coordChange i (Z.indexAt x) x, Z.coordChange (Z.indexAt x) i x,
    h (Z.mem_baseSet_at x) hx, h hx (Z.mem_baseSet_at x)⟩, fun M ↦ ?_⟩
  rw [inChartCoordinates_def, Units.inv_mk, Units.val_mk, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]

end VectorBundleCore
