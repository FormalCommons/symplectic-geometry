/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Topology.Homotopy.PuncturedStarConvex

/-!
# Radial projection of the punctured plane onto the unit circle

The map `ℂ ∖ {0} → Circle`, `z ↦ z / |z|`, as a continuous map. It is Tau Ceti's radial
projection onto the unit sphere (`TauCeti.complSingletonHomotopyEquivSphere`) followed by the
identification of the unit sphere of `ℂ` with `Circle` (`Circle.homeomorphSphere`), which is how
connecting morphisms of the pair `(ℂ, ℂ ∖ {0})` are read in the homology of `Circle`.

## Main definitions

* `Circle.radialProjection`: the radial projection `ℂ ∖ {0} → Circle`.

## Main results

* `Circle.coe_radialProjection_apply`: `radialProjection z = |z|⁻¹ • z`.
-/

public section

noncomputable section

open Metric

namespace Circle

/-- Radial projection `z ↦ z / |z|` of the punctured plane `ℂ ∖ {0}` onto `Circle`: Tau Ceti's
radial projection onto the unit sphere of `ℂ`, read in `Circle`. -/
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

end Circle

end
