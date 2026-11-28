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
(`SymplecticGeometry.ofReal_rescaledDist`). The triangle inequality holds for the extended
version on any manifold, but for the real version only on a preconnected one
(`SymplecticGeometry.rescaledDist_triangle`).

## Main definitions

* `SymplecticGeometry.rescaledEDist`: `√(2π k)` times the Riemannian extended distance.
* `SymplecticGeometry.rescaledDist`: the same as a real number.

## Main results

* `SymplecticGeometry.rescaledEDist_triangle` and `SymplecticGeometry.rescaledDist_triangle`: the
  triangle inequality, the latter on a preconnected manifold.
* `SymplecticGeometry.sqrt_mul_rescaledEDist` and `SymplecticGeometry.sqrt_mul_rescaledDist`:
  the rescaled distances for two powers are proportional.
* `SymplecticGeometry.rescaledEDist_ne_top` and `SymplecticGeometry.ofReal_rescaledDist`: on a
  preconnected manifold, the rescaled distance is finite, and its real version recovers it.
* `SymplecticGeometry.ofReal_le_rescaledEDist_iff` and
  `SymplecticGeometry.rescaledEDist_le_ofReal_iff`: on a preconnected manifold, bounds by
  `ENNReal.ofReal r` on the extended distance are bounds by `r` on the real one.

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

/-- **Changing the power in the rescaled distance.** The rescaled extended distances for two
powers `k` and `l` are proportional: `√l * d_k(x, y) = √k * d_l(x, y)`. -/
theorem sqrt_mul_rescaledEDist (k l : ℕ) (x y : M) :
    ENNReal.ofReal √l * rescaledEDist I k x y = ENNReal.ofReal √k * rescaledEDist I l x y := by
  simp only [rescaledEDist_def, ← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  congr 2
  rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Real.sqrt_mul (Nat.cast_nonneg _)]
  ring_nf

/-- **Changing the power in the rescaled distance.** The real rescaled distances for two powers
`k` and `l` are proportional: `√l * d_k(x, y) = √k * d_l(x, y)`. -/
theorem sqrt_mul_rescaledDist (k l : ℕ) (x y : M) :
    √l * rescaledDist I k x y = √k * rescaledDist I l x y := by
  have h := congrArg ENNReal.toReal (sqrt_mul_rescaledEDist (I := I) k l x y)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), ← rescaledDist_def, ← rescaledDist_def] at h

/-- The triangle inequality for the rescaled distance. -/
theorem rescaledEDist_triangle (k : ℕ) (x y z : M) :
    rescaledEDist I k x z ≤ rescaledEDist I k x y + rescaledEDist I k y z := by
  simp only [rescaledEDist_def, ← mul_add]
  gcongr
  exact Manifold.riemannianEDist_triangle

/-- The rescaled distance is finite on a preconnected manifold. -/
@[aesop (rule_sets := [finiteness]) safe apply, simp]
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

/-- On a preconnected manifold, a lower bound `ENNReal.ofReal r` on the rescaled extended distance
is the lower bound `r` on the real rescaled distance. -/
theorem ofReal_le_rescaledEDist_iff [PreconnectedSpace M] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] {k : ℕ} {x y : M} {r : ℝ} :
    ENNReal.ofReal r ≤ rescaledEDist I k x y ↔ r ≤ rescaledDist I k x y := by
  rw [rescaledDist_def, ENNReal.ofReal_le_iff_le_toReal (rescaledEDist_ne_top k x y)]

/-- On a preconnected manifold, for `0 ≤ r`, an upper bound `ENNReal.ofReal r` on the rescaled
extended distance is the upper bound `r` on the real rescaled distance. -/
theorem rescaledEDist_le_ofReal_iff [PreconnectedSpace M] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] {k : ℕ} {x y : M} {r : ℝ}
    (hr : 0 ≤ r) :
    rescaledEDist I k x y ≤ ENNReal.ofReal r ↔ rescaledDist I k x y ≤ r := by
  rw [← ofReal_rescaledDist, ENNReal.ofReal_le_ofReal_iff hr]

/-- The triangle inequality for the real rescaled distance, on a preconnected manifold. Without
that hypothesis it can fail, since the real distance is `0` between points at infinite distance. -/
theorem rescaledDist_triangle [PreconnectedSpace M] [IsManifold I 1 M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] (k : ℕ) (x y z : M) :
    rescaledDist I k x z ≤ rescaledDist I k x y + rescaledDist I k y z := by
  simp only [rescaledDist_def]
  exact ENNReal.toReal_le_add (rescaledEDist_triangle k x y z) (rescaledEDist_ne_top k x y)
    (rescaledEDist_ne_top k y z)

end SymplecticGeometry

end
