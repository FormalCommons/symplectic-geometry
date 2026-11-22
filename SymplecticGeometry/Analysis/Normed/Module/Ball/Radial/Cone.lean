/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone

/-!
# Zeros of cones over maps on the unit sphere, and cones over maps on the circle

Facts about Tau Ceti's cone `TauCeti.sphereCone f` over a map `f` on the unit sphere of a real
normed space, its positively homogeneous extension `x ↦ ‖x‖ • f (‖x‖⁻¹ • x)`. If `f` vanishes
nowhere, the origin is the only zero of its cone (`TauCeti.sphereCone_eq_zero_iff`). Every vector
is the origin or a positive multiple of a unit vector
(`TauCeti.eq_zero_or_exists_eq_smul_coe_sphere`), on which the cone is the same multiple of the
value of `f` (`TauCeti.sphereCone_smul_coe`).

A map `f` on `Circle` extends radially to `ℂ` by the cone over `f ∘ Circle.homeomorphSphere.symm`.
This cone takes the value `f ζ` at each `ζ : Circle`
(`TauCeti.sphereCone_comp_homeomorphSphere_symm_coe`, from `TauCeti.sphereCone_coe`), and it is
continuous when `f` is (`TauCeti.continuous_sphereCone_comp_homeomorphSphere_symm`, from
`TauCeti.continuous_sphereCone`, since `Circle` is compact).

## Main results

* `TauCeti.sphereCone_eq_zero_iff`: the cone over a map without zeros vanishes only at the origin.
* `TauCeti.sphereCone_comp_homeomorphSphere_symm_coe`: the radial extension of a map on `Circle`
  restricts to it on the circle.
* `TauCeti.continuous_sphereCone_comp_homeomorphSphere_symm`: the radial extension of a
  continuous map on `Circle` is continuous.
-/

public section

open Metric

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {f : sphere (0 : E) 1 → F}

/-- The cone over a map `f` on the unit sphere that vanishes nowhere vanishes only at the
origin. -/
theorem sphereCone_eq_zero_iff (hf : ∀ u, f u ≠ 0) {x : E} : sphereCone f x = 0 ↔ x = 0 := by
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, u, rfl⟩
  · simp
  rw [sphereCone_smul_coe hr.le, smul_eq_zero, smul_eq_zero, or_iff_right hr.ne',
    or_iff_right hr.ne']
  exact iff_of_false (hf u) (ne_zero_of_mem_sphere one_ne_zero u)


section Circle

/-- The cone over a map `f` on `Circle`, read on the unit sphere of `ℂ` through
`Circle.homeomorphSphere`, takes the value `f ζ` at a point `ζ` of the circle. -/
@[simp]
theorem sphereCone_comp_homeomorphSphere_symm_coe (f : Circle → F) (ζ : Circle) :
    sphereCone (f ∘ Circle.homeomorphSphere.symm) (ζ : ℂ) = f ζ := by
  rw [← Circle.coe_homeomorphSphere_apply ζ, sphereCone_coe, Function.comp_apply,
    Homeomorph.symm_apply_apply]

/-- The cone over a continuous map on `Circle`, read on the unit sphere of `ℂ` through
`Circle.homeomorphSphere`, is continuous on `ℂ`. -/
theorem continuous_sphereCone_comp_homeomorphSphere_symm {f : Circle → F} (hf : Continuous f) :
    Continuous (sphereCone (f ∘ Circle.homeomorphSphere.symm)) :=
  continuous_sphereCone (hf.comp Circle.homeomorphSphere.symm.continuous) fun _ ↦
    (ContinuousMap.mk f hf).norm_coe_le_norm _

end Circle

end TauCeti
