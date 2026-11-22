/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Ball.Radial.Cone

/-!
# Zeros of cones over maps on the unit sphere

A fact about Tau Ceti's cone `TauCeti.sphereCone f` over a map `f` on the unit sphere of a real
normed space, its positively homogeneous extension `x ↦ ‖x‖ • f (‖x‖⁻¹ • x)`: if `f` vanishes
nowhere, the origin is the only zero of its cone (`TauCeti.sphereCone_eq_zero_iff`). Every vector
is the origin or a positive multiple of a unit vector
(`TauCeti.eq_zero_or_exists_eq_smul_coe_sphere`), on which the cone is the same multiple of the
value of `f` (`TauCeti.sphereCone_smul_coe`).

## Main results

* `TauCeti.sphereCone_eq_zero_iff`: the cone over a map without zeros vanishes only at the origin.
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

end TauCeti
