/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.Sets.Opens
public import TauCeti.Analysis.Complex.ClosedAnnulus

/-!
# Open annuli in a normed group

For a seminormed group `E` and real numbers `a` and `b`, `SymplecticGeometry.annulus E a b` is
the open set of the points `x` of `E` with `a < ‖x‖ < b`. Gluing maps of connected sums and of
symplectic fibre sums are diffeomorphisms of such annuli, in a vector space or in `ℂ`.

## Main definitions and results

* `SymplecticGeometry.annulus E a b`: the open annulus `{x | a < ‖x‖ ∧ ‖x‖ < b}` of `E`, with
  `coe_annulus` and `mem_annulus`.
* `SymplecticGeometry.annulus_mono`: the annulus is monotone in its outer radius and antitone in
  its inner radius.
* `SymplecticGeometry.map_mem_annulus_iff`: a semilinear isometry preserves membership in the
  annulus of given radii.
* `SymplecticGeometry.ne_zero_of_mem_annulus`: for `0 ≤ a`, the annulus misses `0`.
* `Complex.closedAnnulus_subset_closedAnnulus`, `Complex.closedAnnulus_subset_annulus` and
  `Complex.annulus_subset_closedAnnulus`: inclusions between Tau Ceti's closed annuli
  `Complex.closedAnnulus a b` of `ℂ` and the open annuli `annulus ℂ a b`.
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

/-- The open annulus grows as its inner radius decreases and its outer radius increases. -/
@[gcongr]
theorem annulus_mono {a a' b b' : ℝ} (ha : a ≤ a') (hb : b' ≤ b) :
    annulus E a' b' ≤ annulus E a b :=
  fun _ hx ↦ mem_annulus.2 ⟨ha.trans_lt (mem_annulus.1 hx).1, (mem_annulus.1 hx).2.trans_le hb⟩

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

namespace Complex

open SymplecticGeometry

variable {a a' b b' : ℝ}

/-- The closed annulus `a ≤ ‖z‖ ≤ b` of `ℂ` grows as its inner radius decreases and its outer
radius increases. -/
@[gcongr]
theorem closedAnnulus_subset_closedAnnulus (ha : a ≤ a') (hb : b' ≤ b) :
    closedAnnulus a' b' ⊆ closedAnnulus a b := fun _ hz ↦
  mem_closedAnnulus.2 ⟨ha.trans (mem_closedAnnulus.1 hz).1, (mem_closedAnnulus.1 hz).2.trans hb⟩

/-- For `a < a'` and `b' < b`, the closed annulus `a' ≤ ‖z‖ ≤ b'` of `ℂ` lies in the open annulus
`a < ‖z‖ < b`. -/
theorem closedAnnulus_subset_annulus (ha : a < a') (hb : b' < b) :
    closedAnnulus a' b' ⊆ annulus ℂ a b := fun _ hz ↦
  mem_annulus.2 ⟨ha.trans_le (mem_closedAnnulus.1 hz).1, (mem_closedAnnulus.1 hz).2.trans_lt hb⟩

/-- The open annulus `a < ‖z‖ < b` of `ℂ` lies in the closed annulus `a ≤ ‖z‖ ≤ b`. -/
theorem annulus_subset_closedAnnulus : (annulus ℂ a b : Set ℂ) ⊆ closedAnnulus a b :=
  fun _ hz ↦ mem_closedAnnulus.2 ⟨(mem_annulus.1 hz).1.le, (mem_annulus.1 hz).2.le⟩

end Complex

end
