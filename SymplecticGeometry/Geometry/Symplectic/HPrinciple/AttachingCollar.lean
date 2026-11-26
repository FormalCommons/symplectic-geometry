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
import Mathlib.Topology.Algebra.Order.Group
public import Mathlib.Topology.Sets.Opens

/-!
# The product collar of the attaching faces of a handle core

On the handle core `D = (ι → ℝ) × (κ → ℝ)`, with sup norms, the attaching faces are
`A = sphere 0 1 ×ˢ closedBall 0 1`. Their product collar `attachingCollar ι κ ε` is the open
set of the `(u, v)` with `|‖u‖ - 1| < ε` and `‖v‖ < 1 + ε`; it contains `A` as soon as `ε > 0`.
The clipping homotopy of the handle-core lemma preserves these collars and maps the thin ones
into `A`, and the primitives near `A` are built on them.

## Main definitions

* `SymplecticGeometry.attachingCollar ι κ ε`: the product collar of the attaching faces.

## Main results

* `SymplecticGeometry.sphere_prod_closedBall_subset_attachingCollar`

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

end SymplecticGeometry

end
