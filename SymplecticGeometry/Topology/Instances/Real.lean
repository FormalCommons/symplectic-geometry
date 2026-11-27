/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.Infinite
import TauCeti.Analysis.Contour.Crossing.Windows

/-!
# Balls of the real line away from a finite set

`Set.Finite.exists_ball_subset_Ioo_forall_lt_abs_sub`: for a finite set `A ⊆ ℝ` and `a < b`,
there is a ball `Metric.ball x ρ`, `ρ > 0`, that keeps a distance `ρ` from both ends of
`(a, b)` and whose points are all more than `ρ` away from every point of `A`. A level chosen
anywhere in such a ball then stays clear of `A` and of the ends of the interval.

The radius comes from Tau Ceti's `TauCeti.Contour.exists_common_window_radius`, applied to a single
point `x` of `(a, b)` off `A`; the ball has half that radius.
-/

public section

open Set

/-- For a finite set `A` of reals and `a < b`, there are `x` and `ρ > 0` such that the ball
`Metric.ball x ρ` lies in `Ioo (a + ρ) (b - ρ)` and each of its points is more than `ρ` away from
every point of `A`. -/
theorem Set.Finite.exists_ball_subset_Ioo_forall_lt_abs_sub {A : Set ℝ} (hA : A.Finite)
    {a b : ℝ} (hab : a < b) :
    ∃ x, ∃ ρ > 0, Metric.ball x ρ ⊆ Ioo (a + ρ) (b - ρ) ∧
      ∀ y ∈ Metric.ball x ρ, ∀ z ∈ A, ρ < |z - y| := by
  classical
  obtain ⟨x, hx, hxA⟩ : (Ioo a b \ A).Nonempty := ((Ioo_infinite hab).sdiff hA).nonempty
  obtain ⟨r, hr, hab', -, hrA⟩ := TauCeti.Contour.exists_common_window_radius (crossings := {x})
    (P := hA.toFinset) (by simpa using hx) (by simpa using hxA)
  obtain ⟨hax, hxb⟩ := hab' x (Finset.mem_singleton_self x)
  refine ⟨x, r / 2, half_pos hr, fun y hy ↦ ?_, fun y hy z hz ↦ ?_⟩
  · rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hy
    constructor <;> linarith
  · rw [Metric.mem_ball, Real.dist_eq] at hy
    have h1 := hrA x (Finset.mem_singleton_self x) z (hA.mem_toFinset.2 hz)
    have h2 : |x - z| ≤ |x - y| + |y - z| := abs_sub_le x y z
    rw [abs_sub_comm x y, abs_sub_comm y z] at h2
    linarith

end
