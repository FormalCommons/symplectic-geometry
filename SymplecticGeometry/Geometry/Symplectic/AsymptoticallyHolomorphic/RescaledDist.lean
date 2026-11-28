/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Distance

/-!
# The rescaled Riemannian distance

On a manifold `M` with a Riemannian metric `g`, the estimates for the `k`-th powers of a line
bundle are stated in the distance `d_k = √(2π k) · d_g`, in which the rescaled unitary charts of
`RescaledChart.lean` are close to isometries. This file names it, as an extended distance
`SymplecticGeometry.rescaledEDist I k x y` and as a real number
`SymplecticGeometry.rescaledDist I k x y`.

The real version is the `ENNReal.toReal` of the extended one, so it is `0` for two points at
infinite distance, that is, in different components: a bound of the form
`C * (1 + d) ^ N * exp (-c * d ^ 2)` in `d = rescaledDist I k x y` gives no decay there. On a
preconnected manifold, the case of the design, the Riemannian distance is finite
(`TauCeti.Manifold.riemannianEDist_ne_top`), and the two versions agree
(`SymplecticGeometry.ofReal_rescaledDist`).

## Main definitions

* `SymplecticGeometry.rescaledEDist`: `√(2π k)` times the Riemannian extended distance.
* `SymplecticGeometry.rescaledDist`: the same as a real number.

## Main results

* `SymplecticGeometry.rescaledEDist_ne_top` and `SymplecticGeometry.ofReal_rescaledDist`: on a
  preconnected manifold, the rescaled distance is finite, and its real version recovers it.

## References

* [S. K. Donaldson, *Symplectic submanifolds and almost-complex geometry*][Donaldson1996].
* [D. Auroux, *A remark about Donaldson's construction of symplectic submanifolds*][Auroux2002].
-/

public section

open scoped ENNReal
open Bundle

namespace SymplecticGeometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- The **rescaled distance** `d_k(x, y) = √(2π k) · d_g(x, y)` between two points of a
Riemannian manifold, as an extended nonnegative real: the Riemannian distance for the metric
`2π k g`. -/
noncomputable def rescaledEDist (k : ℕ) (x y : M) : ℝ≥0∞ :=
  ENNReal.ofReal √(2 * Real.pi * k) * Manifold.riemannianEDist I x y

theorem rescaledEDist_def (k : ℕ) (x y : M) :
    rescaledEDist I k x y = ENNReal.ofReal √(2 * Real.pi * k) * Manifold.riemannianEDist I x y :=
  (rfl)

/-- The **rescaled distance** `d_k(x, y) = √(2π k) · d_g(x, y)` between two points of a
Riemannian manifold, as a real number: the `ENNReal.toReal` of `rescaledEDist I k x y`, so `0`
when the two points are at infinite distance. -/
noncomputable def rescaledDist (k : ℕ) (x y : M) : ℝ :=
  (rescaledEDist I k x y).toReal

theorem rescaledDist_def (k : ℕ) (x y : M) :
    rescaledDist I k x y = (rescaledEDist I k x y).toReal :=
  (rfl)

variable {I}

variable (I) in
theorem rescaledDist_nonneg (k : ℕ) (x y : M) : 0 ≤ rescaledDist I k x y :=
  ENNReal.toReal_nonneg

@[simp]
theorem rescaledEDist_self (k : ℕ) (x : M) : rescaledEDist I k x x = 0 := by
  rw [rescaledEDist_def, Manifold.riemannianEDist_self, mul_zero]

@[simp]
theorem rescaledDist_self (k : ℕ) (x : M) : rescaledDist I k x x = 0 := by
  rw [rescaledDist_def, rescaledEDist_self, ENNReal.toReal_zero]

theorem rescaledEDist_comm (k : ℕ) (x y : M) : rescaledEDist I k x y = rescaledEDist I k y x := by
  rw [rescaledEDist_def, rescaledEDist_def, Manifold.riemannianEDist_comm]

theorem rescaledDist_comm (k : ℕ) (x y : M) : rescaledDist I k x y = rescaledDist I k y x := by
  rw [rescaledDist_def, rescaledDist_def, rescaledEDist_comm]

/-- The rescaled distance is finite on a preconnected manifold. -/
theorem rescaledEDist_ne_top [PreconnectedSpace M] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (k : ℕ) (x y : M) :
    rescaledEDist I k x y ≠ ∞ := by
  rw [rescaledEDist_def]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (TauCeti.Manifold.riemannianEDist_ne_top I x y)

/-- On a preconnected manifold, the real rescaled distance recovers the extended one. -/
theorem ofReal_rescaledDist [PreconnectedSpace M] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (k : ℕ) (x y : M) :
    ENNReal.ofReal (rescaledDist I k x y) = rescaledEDist I k x y := by
  rw [rescaledDist_def, ENNReal.ofReal_toReal (rescaledEDist_ne_top k x y)]

end SymplecticGeometry

end
