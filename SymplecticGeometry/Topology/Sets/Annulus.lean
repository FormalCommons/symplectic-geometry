/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Sets.Opens

/-!
# Open annuli in a normed group

For a seminormed group `E` and real numbers `a` and `b`, `SymplecticGeometry.annulus E a b` is
the open set of the points `x` of `E` with `a < ‖x‖ < b`. Gluing maps of connected sums and of
symplectic fibre sums are diffeomorphisms of such annuli, in a vector space or in `ℂ`.

## Main definitions and results

* `SymplecticGeometry.annulus E a b`: the open annulus `{x | a < ‖x‖ ∧ ‖x‖ < b}` of `E`, with
  `coe_annulus` and `mem_annulus`.
* `SymplecticGeometry.map_mem_annulus_iff`: a semilinear isometry preserves membership in the
  annulus of given radii.
* `SymplecticGeometry.ne_zero_of_mem_annulus`: for `0 ≤ a`, the annulus misses `0`.
-/

public section

open TopologicalSpace

namespace SymplecticGeometry

variable (E : Type*)

section Seminormed

variable [SeminormedAddGroup E]

/-- The open annulus `{x | a < ‖x‖ < b}` of a seminormed group `E`. -/
def annulus (a b : ℝ) : Opens E :=
  ⟨{x | a < ‖x‖ ∧ ‖x‖ < b}, (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)⟩

variable {E}

@[simp]
theorem coe_annulus (a b : ℝ) : (annulus E a b : Set E) = {x | a < ‖x‖ ∧ ‖x‖ < b} :=
  (rfl)

@[simp]
theorem mem_annulus {a b : ℝ} {x : E} : x ∈ annulus E a b ↔ a < ‖x‖ ∧ ‖x‖ < b :=
  Iff.rfl

end Seminormed

variable {E}

/-- A semilinear isometry `Φ : E → F` preserves membership in the annulus `a < ‖x‖ < b`: `Φ x`
lies in the annulus of `F` if and only if `x` lies in that of `E`. -/
theorem map_mem_annulus_iff {R R₂ F 𝓕 : Type*} [Semiring R] [Semiring R₂] {σ : R →+* R₂}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module R E] [Module R₂ F]
    [FunLike 𝓕 E F] [SemilinearIsometryClass 𝓕 σ E F] (Φ : 𝓕) {a b : ℝ} {x : E} :
    Φ x ∈ annulus F a b ↔ x ∈ annulus E a b := by
  simp

variable [NormedAddGroup E]

/-- For `0 ≤ a`, the points of the annulus `a < ‖x‖ < b` are nonzero. -/
theorem ne_zero_of_mem_annulus {a b : ℝ} (ha : 0 ≤ a) {x : E} (hx : x ∈ annulus E a b) :
    x ≠ 0 :=
  norm_pos_iff.1 (ha.trans_lt hx.1)

end SymplecticGeometry

end
