/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Geometry.Manifold.Orientation.Basic

/-!
# The standard orientation of `ℂ`

The standard orientation of `ℂ` as a real manifold modelled on `𝓘(ℝ, ℂ)`
(`TauCeti.Manifold.Orientation.complex`) is the constant orientation given by
`Complex.orientation`, in which the real basis `(1, i)` is positive. It comes with
`TauCeti.Manifold.Orientation.complex_def` and `TauCeti.Manifold.Orientation.orientationAt_complex`.
It is named as Tau Ceti names `TauCeti.Manifold.Orientation.real` and
`TauCeti.Manifold.Orientation.euclideanSpace`.
-/

public section

open scoped Manifold

namespace TauCeti.Manifold.Orientation

/-- The standard orientation of `ℂ`, as a real manifold modelled on `𝓘(ℝ, ℂ)`: the constant
orientation of the model given by `Complex.orientation`, in which the real basis `(1, i)` is
positive. It is the `ℂ` analogue of `TauCeti.Manifold.Orientation.real`. -/
noncomputable def complex : Orientation 𝓘(ℝ, ℂ) ℂ (Fin 2) :=
  model Complex.orientation (by simp)

theorem complex_def : complex = model (I := 𝓘(ℝ, ℂ)) Complex.orientation (by simp) :=
  (rfl)

/-- At every point of `ℂ`, the standard orientation is `Complex.orientation`. -/
@[simp]
theorem orientationAt_complex (x : ℂ) : orientationAt complex x = Complex.orientation := by
  rw [complex_def, orientationAt_model]

end TauCeti.Manifold.Orientation

end
