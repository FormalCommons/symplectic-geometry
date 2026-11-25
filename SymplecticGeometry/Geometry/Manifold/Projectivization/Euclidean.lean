/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import SymplecticGeometry.Geometry.Manifold.Complex.Orientation
public import SymplecticGeometry.Geometry.Manifold.ModelTransport.Remodel
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Instances.Projectivization
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ComplexProjective
import TauCeti.Geometry.Manifold.Morse.CWModel

/-!
# Complex projective space charted on a Hermitian space

Tau Ceti charts the complex projective space `ℙ ℂ (Fin (n + 2) → ℂ)` on `Fin (n + 1) → ℂ`, whose
sup norm comes from no inner product. Constructions that need a real inner product space as model,
such as Tau Ceti's connected sums `TauCeti.ConnectedSum` and `TauCeti.OrientedConnectedSum`, need it
charted on the Hermitian space `EuclideanSpace ℂ (Fin (n + 1))` instead. This file re-models it
there with the library's `SymplecticGeometry.Remodel`, along the complex-linear identification of
the two models, and equips it with its real smooth structure, its complex orientation, a finite
CW type and its Euler characteristic.

## Main definitions

* `SymplecticGeometry.EuclideanComplexProjectiveSpace n`: the complex projective space of complex
  dimension `n + 1`, charted on `EuclideanSpace ℂ (Fin (n + 1))`.
* `SymplecticGeometry.EuclideanComplexProjectiveSpace.orientation`: its complex orientation, indexed
  by `Fin (2 * n + 1 + 1)`.

## Main results

* `SymplecticGeometry.EuclideanComplexProjectiveSpace.eulerChar_eq`: its Euler characteristic is
  `n + 2`, from Tau Ceti's `TauCeti.eulerChar_projectivization_complex`.
-/

public section

noncomputable section

open Module TauCeti
open scoped Manifold ContDiff LinearAlgebra.Projectivization

namespace SymplecticGeometry

/-- The **complex projective space** `ℙ ℂ (Fin (n + 2) → ℂ)` of complex dimension `n + 1`, charted
on the Hermitian space `EuclideanSpace ℂ (Fin (n + 1))`: its homogeneous-ratio charts are followed
by the complex-linear identification of `Fin (n + 1) → ℂ` with `EuclideanSpace ℂ (Fin (n + 1))`. -/
abbrev EuclideanComplexProjectiveSpace (n : ℕ) : Type :=
  Remodel (EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm.toDiffeomorph (ℙ ℂ (Fin (n + 2) → ℂ))

namespace EuclideanComplexProjectiveSpace

variable (n : ℕ)

/-- Complex projective space is a smooth real manifold, the one underlying its complex
structure. -/
instance : IsManifold 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) ∞ (EuclideanComplexProjectiveSpace n) :=
  (inferInstance : IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin (n + 1))) ∞
    (EuclideanComplexProjectiveSpace n)).restrictScalars ℝ

/-- The complex orientation of complex projective space, indexed by `Fin (2 * n + 1 + 1)`: the
canonical orientation of a complex manifold,
`SymplecticGeometry.complexManifoldOrientationOfFinrank`. -/
def orientation :
    Manifold.Orientation 𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1))) (EuclideanComplexProjectiveSpace n)
      (Fin (2 * n + 1 + 1)) :=
  complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
    (EuclideanComplexProjectiveSpace n) (r := n) (by simp)

theorem orientation_def :
    orientation n = complexManifoldOrientationOfFinrank (EuclideanSpace ℂ (Fin (n + 1)))
      (EuclideanComplexProjectiveSpace n) (r := n) (by simp) :=
  (rfl)

instance : FiniteCWType (EuclideanComplexProjectiveSpace n) :=
  FiniteCWType.of_isManifold (EuclideanComplexProjectiveSpace n)
    𝓘(ℝ, EuclideanSpace ℂ (Fin (n + 1)))

/-- The Euler characteristic of the complex projective space of complex dimension `n + 1` is
`n + 2`. -/
theorem eulerChar_eq : eulerChar (EuclideanComplexProjectiveSpace n) = n + 2 := by
  have := FiniteCWType.of_isManifold (ℙ ℂ (Fin (n + 2) → ℂ)) 𝓘(ℝ, Fin (n + 1) → ℂ)
  rw [← (remodelHomeomorph _ _).eulerChar_eq, eulerChar_projectivization_complex]
  simp

end EuclideanComplexProjectiveSpace

end SymplecticGeometry

end
