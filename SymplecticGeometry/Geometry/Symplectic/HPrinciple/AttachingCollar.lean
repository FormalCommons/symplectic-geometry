/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Algebra.Order.Group
import SymplecticGeometry.Analysis.Normed.Module.Ball.Shell
public import Mathlib.Topology.Sets.Opens

/-!
# The product collar of the attaching faces of a handle core

On the handle core `D = (ι → ℝ) × (κ → ℝ)`, with sup norms, the attaching faces are
`A = sphere 0 1 ×ˢ closedBall 0 1`. Their product collar `attachingCollar ι κ ε` is the open
set of the `(u, v)` with `|‖u‖ - 1| < ε` and `‖v‖ < 1 + ε`; it contains `A` as soon as `ε > 0`,
and, as `A` is compact, it lies in any given open neighbourhood of `A` once `ε` is small enough.
The clipping homotopy of the handle-core lemma preserves these collars and maps the thin ones
into `A`, and the primitives near `A` are built on them.

## Main definitions

* `SymplecticGeometry.attachingCollar ι κ ε`: the product collar of the attaching faces.

## Main results

* `SymplecticGeometry.sphere_prod_closedBall_subset_attachingCollar`
* `SymplecticGeometry.exists_attachingCollar_subset`

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], proof of
  Lemma 7.3.2.
-/

public section

open Set Metric TopologicalSpace

namespace SymplecticGeometry

variable (ι κ : Type*) [Fintype ι] [Fintype κ] (ε : ℝ)

/-- The **product collar** of the attaching faces of the handle core `(ι → ℝ) × (κ → ℝ)`, with
sup norms: the open set of the `(u, v)` with `|‖u‖ - 1| < ε` and `‖v‖ < 1 + ε`. -/
def attachingCollar : Opens ((ι → ℝ) × (κ → ℝ)) :=
  ⟨{p | |‖p.1‖ - 1| < ε ∧ ‖p.2‖ < 1 + ε},
    (isOpen_lt (by fun_prop) continuous_const).and
      (isOpen_lt (by fun_prop) continuous_const)⟩

variable {ι κ ε}

/-- Membership in the product collar. -/
@[simp]
theorem mem_attachingCollar_iff {p : (ι → ℝ) × (κ → ℝ)} :
    p ∈ attachingCollar ι κ ε ↔ |‖p.1‖ - 1| < ε ∧ ‖p.2‖ < 1 + ε :=
  Iff.rfl

/-- The product collar as a set. -/
theorem coe_attachingCollar :
    (attachingCollar ι κ ε : Set ((ι → ℝ) × (κ → ℝ))) =
      {p | |‖p.1‖ - 1| < ε ∧ ‖p.2‖ < 1 + ε} :=
  (rfl)

/-- For `ε > 0` the product collar contains the attaching faces `sphere 0 1 ×ˢ closedBall 0 1`. -/
theorem sphere_prod_closedBall_subset_attachingCollar (hε : 0 < ε) :
    sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1 ⊆ attachingCollar ι κ ε := by
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  rw [mem_sphere_zero_iff_norm] at hu
  rw [mem_closedBall_zero_iff] at hv
  exact ⟨by simpa [hu] using hε, by linarith⟩

/-- Every open neighbourhood `W` of the attaching faces `sphere 0 1 ×ˢ closedBall 0 1` contains a
product collar `attachingCollar ι κ ε` with `ε > 0`. -/
theorem exists_attachingCollar_subset {W : Set ((ι → ℝ) × (κ → ℝ))} (hW : IsOpen W)
    (hAW : sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1 ⊆ W) :
    ∃ ε > 0, (attachingCollar ι κ ε : Set ((ι → ℝ) × (κ → ℝ))) ⊆ W := by
  obtain ⟨δ, hδ, hδW⟩ := ((isCompact_sphere (0 : ι → ℝ) 1).prod
    (isCompact_closedBall (0 : κ → ℝ) 1)).exists_thickening_subset_open hW hAW
  refine ⟨min (1 / 2) δ, by positivity, ?_⟩
  rintro ⟨u, v⟩ ⟨hu, hv⟩
  have hε₁ : min (1 / 2) δ ≤ 1 / 2 := min_le_left _ _
  have hε₂ : min (1 / 2) δ ≤ δ := min_le_right _ _
  simp only at hu hv
  rw [abs_lt] at hu
  -- `(u, v)` is within `δ` of `((1 / ‖u‖) • u, v')`, where `v'` is the point of the closed
  -- unit ball nearest to `v` (`Metric.dist_div_norm_smul_self`).
  have hu0 : u ≠ 0 := norm_pos_iff.1 (by linarith)
  have hu1 : (1 / ‖u‖) • u ∈ sphere (0 : ι → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_div, norm_one, norm_norm,
      one_div_mul_cancel (norm_ne_zero_iff.2 hu0)]
  obtain ⟨v', hv', hvv'⟩ : ∃ v' ∈ closedBall (0 : κ → ℝ) 1, dist v v' < δ := by
    by_cases hv1 : ‖v‖ ≤ 1
    · exact ⟨v, mem_closedBall_zero_iff.2 hv1, by simpa using hδ⟩
    · have hv0 : v ≠ 0 := norm_pos_iff.1 (by linarith)
      refine ⟨(1 / ‖v‖) • v, mem_closedBall_zero_iff.2 (by
        rw [norm_smul, norm_div, norm_one, norm_norm,
          one_div_mul_cancel (norm_ne_zero_iff.2 hv0)]), ?_⟩
      rw [Metric.dist_div_norm_smul_self hv0, abs_of_pos (by linarith)]
      linarith
  refine hδW (mem_thickening_iff.2 ⟨((1 / ‖u‖) • u, v'), ⟨hu1, hv'⟩, ?_⟩)
  rw [Prod.dist_eq, Metric.dist_div_norm_smul_self hu0]
  exact max_lt ((abs_lt.2 hu).trans_le hε₂) hvv'

end SymplecticGeometry

end
