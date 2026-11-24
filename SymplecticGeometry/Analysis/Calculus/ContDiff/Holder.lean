/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Bounds
public import TauCeti.Analysis.Holder.Jet.Bounds

/-!
# Hölder top derivative of a map of class `C^{k+1}` at a point

A map of class `C^{k+1}` at `x` is of class `C^{k+1}` on a ball around `x`, and on a smaller
ball its `k`-th derivative is Lipschitz, hence `α`-Hölder for every `α ≤ 1`.

The proof combines Tau Ceti's `ContDiffAt.exists_ball_bound_iteratedFDeriv`, which bounds the
iterated derivatives near `x`, with `ContDiffOn.holderOnWith_iteratedFDeriv_of_lt`, which turns
such bounds into a Hölder bound on a lower derivative.

## Main results

* `ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv`: a map of class `C^{k+1}` at `x` is
  `C^{k+1}` on a ball around `x`, with a Hölder `k`-th derivative there.
-/

public section

open Metric
open scoped NNReal

/-- Let `α ≤ 1`. A map of class `C^{k+1}` at `x` is of class `C^{k+1}` on some ball around `x`
on which its `k`-th derivative is `α`-Hölder. -/
theorem ContDiffAt.exists_ball_holderOnWith_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} {k : ℕ} (hf : ContDiffAt ℝ (k + 1) f x) {α : ℝ≥0} (hα : α ≤ 1) :
    ∃ ρ > 0, ∃ H : ℝ≥0, ContDiffOn ℝ (k + 1) f (ball x ρ) ∧
      HolderOnWith H α (iteratedFDeriv ℝ k f) (ball x ρ) := by
  obtain ⟨r, hr, A, hA⟩ := (show ContDiffAt ℝ (k + 1 : ℕ) f x by exact_mod_cast hf
    ).exists_ball_bound_iteratedFDeriv
  obtain ⟨r', hr', hr'f⟩ := Metric.eventually_nhds_iff_ball.mp (hf.eventually (by simp))
  have hρ : 0 < min r r' := lt_min hr hr'
  have hC : ContDiffOn ℝ (k + 1) f (ball x (min r r')) := fun y hy ↦
    (hr'f y (ball_subset_ball (min_le_right _ _) hy)).contDiffWithinAt
  have hb (i : ℕ) (hi : i ≤ k + 1) (y) (hy : y ∈ ball x (min r r')) :
      ‖iteratedFDeriv ℝ i f y‖ ≤ A.toNNReal :=
    (hA i hi y (ball_subset_ball (min_le_left _ _) hy)).trans (Real.le_coe_toNNReal A)
  exact ⟨_, hρ, _, hC, ContDiffOn.holderOnWith_iteratedFDeriv_of_lt (k := k + 1) (j := k)
    (by exact_mod_cast hC) isOpen_ball (convex_ball _ _) (by omega) hα
    (hb k (by omega)) (hb (k + 1) le_rfl)⟩

end
