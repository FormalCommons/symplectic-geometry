/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Radius

/-!
# Radial projection onto the boundary of the cube

Tau Ceti's `TauCeti.cubeScale s` scales the cube `I^N` about its centre by `s`, and
`TauCeti.cubeRadius z` is the sup-distance of `z` from the centre, normalized so that the
boundary is where it equals `1`. Away from the centre, scaling `z` by `(cubeRadius z)⁻¹` projects
it radially onto the boundary of the cube.

* `TauCeti.cubeScale_inv_cubeRadius_mem_boundary`: the radial projection of a point other than
  the centre lies on the boundary.
* `TauCeti.continuousOn_cubeScale_inv_cubeRadius`: the radial projection is continuous on the
  points other than the centre.
-/

public section

open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {N : Type*} [Fintype N]

/-- The radial projection `cubeScale (cubeRadius z)⁻¹ z` of a point `z` other than the centre of
the cube lies on the boundary of the cube. -/
theorem cubeScale_inv_cubeRadius_mem_boundary {z : I^N} (h : cubeRadius z ≠ 0) :
    cubeScale (cubeRadius z)⁻¹ z ∈ Cube.boundary N := by
  rw [← cubeRadius_eq_one_iff, cubeRadius_cubeScale (inv_nonneg.2 (cubeRadius_nonneg z))
    (by rw [inv_mul_cancel₀ h])]
  exact inv_mul_cancel₀ h

/-- The radial projection `z ↦ cubeScale (cubeRadius z)⁻¹ z` onto the boundary of the cube is
continuous on the points other than the centre. -/
theorem continuousOn_cubeScale_inv_cubeRadius :
    ContinuousOn (fun z : I^N ↦ cubeScale (cubeRadius z)⁻¹ z) {z | cubeRadius z ≠ 0} := by
  have h : Continuous fun q : ℝ × (I^N) ↦ cubeScale q.1 q.2 := continuous_cubeScale
  exact h.comp_continuousOn ((continuous_cubeRadius.continuousOn.inv₀ fun _ hz ↦ hz).prodMk
    continuousOn_id)

end TauCeti
