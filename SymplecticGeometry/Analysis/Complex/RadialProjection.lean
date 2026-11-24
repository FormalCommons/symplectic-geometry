/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import TauCeti.Analysis.Complex.Circle.Basic
public import TauCeti.Topology.Homotopy.PuncturedStarConvex
import Mathlib.Analysis.Calculus.Deriv.ZPow
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Radial projection of the punctured plane onto the unit circle

The map `ℂ ∖ {0} → Circle`, `z ↦ z / |z|`, as a continuous map. It is Tau Ceti's radial
projection onto the unit sphere (`TauCeti.complSingletonHomotopyEquivSphere`) followed by the
identification of the unit sphere of `ℂ` with `Circle` (`Circle.homeomorphSphere`), which is how
connecting morphisms of the pair `(ℂ, ℂ ∖ {0})` are read in the homology of `Circle`.

Tau Ceti's `Complex.directionFrom 0 univ` is the same map on `univ ∖ {0}`
(`Circle.radialProjection_eq_directionFrom_comp`). The form on `{0}ᶜ` gets its own name because
that is the subspace of the pair `TopPair.ofSubset {0}ᶜ`, and because its definition through
`complSingletonHomotopyEquivSphere` is the one that the homology of the pair is computed with.

## Main definitions

* `Circle.radialProjection`: the radial projection `ℂ ∖ {0} → Circle`.
* `Circle.radialProjectionAt`: for a linear isometry `φ : E ≃ₗᵢ[ℝ] ℂ` and a point `p` of `E`,
  the map `E ∖ {p} → Circle`, `y ↦ φ (y - p) / |φ (y - p)|`.

## Main results

* `Circle.coe_radialProjection_apply`: `radialProjection z = |z|⁻¹ • z`.
* `Circle.radialProjection_eq_directionFrom_comp`: `radialProjection` is
  `Complex.directionFrom 0 univ` restricted to `{0}ᶜ`.
* `Circle.coe_radialProjectionAt_apply`: `radialProjectionAt φ p y = |φ (y - p)|⁻¹ • φ (y - p)`.
* `Circle.radialProjectionAt_refl_zero`: about `0` and through the identity of `ℂ`,
  `radialProjectionAt` is `radialProjection`.
* `Complex.norm_div_norm`: `z / ‖z‖` has norm `1` for `z ≠ 0`.
* `Complex.contDiffAt_div_norm`, `Complex.differentiableAt_div_norm`: the map `z ↦ z / ‖z‖` of
  `ℂ` to itself is smooth, and so real differentiable, away from `0`.
* `Complex.differentiableAt_div_norm_zpow`: for every integer `k`, `z ↦ (z / ‖z‖) ^ k` is real
  differentiable away from `0`.

The smoothness of `z ↦ z / ‖z‖` is read off Tau Ceti's `Complex.contDiffOn_div_norm_pow`.
-/

public section

noncomputable section

open Metric Set

namespace Circle

/-- Radial projection `z ↦ z / |z|` of the punctured plane `ℂ ∖ {0}` onto `Circle`: Tau Ceti's
radial projection onto the unit sphere of `ℂ`, read in `Circle`. It is Tau Ceti's
`Complex.directionFrom 0 univ` restricted to `{0}ᶜ` (`radialProjection_eq_directionFrom_comp`). -/
def radialProjection : C(({0}ᶜ : Set ℂ), Circle) :=
  (homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)).comp
    (TauCeti.complSingletonHomotopyEquivSphere (0 : ℂ)).toFun

theorem radialProjection_def :
    radialProjection = (homeomorphSphere.symm : C(sphere (0 : ℂ) 1, Circle)).comp
      (TauCeti.complSingletonHomotopyEquivSphere (0 : ℂ)).toFun :=
  (rfl)

/-- Radial projection sends `z` to `|z|⁻¹ • z`. -/
@[simp]
theorem coe_radialProjection_apply (z : ({0}ᶜ : Set ℂ)) :
    (radialProjection z : ℂ) = ‖(z : ℂ)‖⁻¹ • (z : ℂ) := by
  simp [radialProjection_def]

/-- Radial projection is Tau Ceti's `Complex.directionFrom 0 univ`, the direction seen from the
origin, restricted along the inclusion of `{0}ᶜ` into `univ ∖ {0}`. -/
theorem radialProjection_eq_directionFrom_comp :
    radialProjection = ((0 : ℂ).directionFrom univ).comp
      (ContinuousMap.inclusion (compl_eq_univ_sdiff {(0 : ℂ)}).le) := by
  ext z
  simp [div_eq_inv_mul]

section At

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection about a point `p` of `E`, read in `Circle` through a linear isometry
`φ : E ≃ₗᵢ[ℝ] ℂ`: the map `E ∖ {p} → Circle`, `y ↦ φ (y - p) / |φ (y - p)|`, which is
`radialProjection` after `y ↦ φ (y - p)`. -/
def radialProjectionAt (φ : E ≃ₗᵢ[ℝ] ℂ) (p : E) : C(({p}ᶜ : Set E), Circle) :=
  radialProjection.comp
    ⟨fun y : ({p}ᶜ : Set E) ↦
      ⟨φ ((y : E) - p), fun h ↦ y.property (sub_eq_zero.1 (φ.map_eq_zero_iff.1 h))⟩,
      by fun_prop⟩

theorem radialProjectionAt_def (φ : E ≃ₗᵢ[ℝ] ℂ) (p : E) :
    radialProjectionAt φ p = radialProjection.comp
      ⟨fun y : ({p}ᶜ : Set E) ↦
        ⟨φ ((y : E) - p), fun h ↦ y.property (sub_eq_zero.1 (φ.map_eq_zero_iff.1 h))⟩,
        by fun_prop⟩ :=
  (rfl)

/-- `radialProjectionAt φ p` sends `y` to `|φ (y - p)|⁻¹ • φ (y - p)`. -/
@[simp]
theorem coe_radialProjectionAt_apply (φ : E ≃ₗᵢ[ℝ] ℂ) (p : E) (y : ({p}ᶜ : Set E)) :
    (radialProjectionAt φ p y : ℂ) = ‖φ ((y : E) - p)‖⁻¹ • φ ((y : E) - p) := by
  rw [radialProjectionAt_def, ContinuousMap.comp_apply, coe_radialProjection_apply,
    ContinuousMap.coe_mk]

/-- About `0` and through the identity of `ℂ`, `radialProjectionAt` is `radialProjection`. -/
@[simp]
theorem radialProjectionAt_refl_zero :
    radialProjectionAt (LinearIsometryEquiv.refl ℝ ℂ) 0 = radialProjection := by
  ext y
  simp

end At

end Circle

/-! ### The radial projection as a map of `ℂ` to itself -/

namespace Complex

/-- The radial projection `z / ‖z‖` of a nonzero complex number lies on the unit circle. -/
theorem norm_div_norm {z : ℂ} (hz : z ≠ 0) : ‖z / ‖z‖‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hz)]

/-- The radial projection `z ↦ z / ‖z‖` is smooth away from `0`. -/
theorem contDiffAt_div_norm {w : ℂ} (hw : w ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun z : ℂ ↦ z / ‖z‖) w := by
  simpa only [pow_one] using
    (contDiffOn_div_norm_pow 1 (N := n)).contDiffAt (isOpen_compl_singleton.mem_nhds hw)

/-- The radial projection `z ↦ z / ‖z‖` is real differentiable away from `0`. -/
theorem differentiableAt_div_norm {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℝ (fun z : ℂ ↦ z / ‖z‖) w :=
  (contDiffAt_div_norm hw (n := 1)).differentiableAt one_ne_zero

/-- For every integer `k`, the map `z ↦ (z / ‖z‖) ^ k` is real differentiable away from `0`. -/
theorem differentiableAt_div_norm_zpow {w : ℂ} (hw : w ≠ 0) (k : ℤ) :
    DifferentiableAt ℝ (fun z : ℂ ↦ (z / ‖z‖) ^ k) w := by
  have hn := norm_div_norm hw
  exact ((differentiableAt_zpow.2 (Or.inl fun h ↦ by simp [h] at hn)).restrictScalars ℝ).comp w
    (differentiableAt_div_norm hw)

end Complex

end
