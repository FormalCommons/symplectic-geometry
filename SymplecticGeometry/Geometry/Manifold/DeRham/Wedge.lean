/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Wedge
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Smooth.Pow
import TauCeti.Geometry.Manifold.DeRham.DegreeZero

/-!
# Closed wedge powers

The wedge powers `φ ∧ ⋯ ∧ φ` (Tau Ceti's `TauCeti.SmoothForm.wedgePow`) of a closed smooth real
form are closed: the empty power is a constant function, and each further power is the wedge of
the previous one with `φ`, which is closed by the Leibniz rule
(`TauCeti.SmoothForm.wedge_mem_closedForms`). So a closed form has a de Rham class of every
power; for a symplectic form `ω` these are the classes `[ω]ᵏ`.

## Main results

* `TauCeti.SmoothForm.wedgePow_mem_closedForms`: wedge powers of a closed form are closed.

## References

* [R. Bott and L. W. Tu, *Differential Forms in Algebraic Topology*][BottTu1982], §1 and §5.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothForm

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] {k : ℕ}

/-- The wedge powers of a closed smooth real form are closed. -/
theorem wedgePow_mem_closedForms {φ : SmoothForm I M ℝ k} (hφ : φ ∈ closedForms I M k)
    (m : ℕ) : φ.wedgePow m ∈ closedForms I M (k * m) := by
  induction m with
  | zero =>
    refine (mem_closedForms_zero_iff I _).2 ?_
    simp only [wedgePow_apply, ContinuousAlternatingMap.wedgePow_zero_apply]
    exact IsLocallyConstant.const 1
  | succ m ih =>
    rw [wedgePow_succ]
    exact wedge_mem_closedForms ih hφ

end SmoothForm

end TauCeti

end
