/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Pseudoconvex

import SymplecticGeometry.Analysis.Complex.LeviForm.Basic

/-!
# Strong pseudoconvexity persists near a point

For a real function `f` on a finite-dimensional complex vector space that is `C²` at `x`, strong
`q`-pseudoconvexity at `x` (Tau Ceti's `TauCeti.IsStronglyPseudoconvexAt`) holds at all points
near `x`, and so does strict plurisubharmonicity:

* `TauCeti.IsStronglyPseudoconvexAt.eventually`,
* `TauCeti.IsStrictlyPlurisubharmonicAt.eventually`.

On a compact set at every point of which `f` is `C²` and strictly plurisubharmonic, its Levi form
is at least `c * ‖v‖ ^ 2` for a single `c > 0`:

* `IsCompact.exists_pos_mul_sq_norm_le_re_leviForm_of_isStrictlyPlurisubharmonicAt`.

Adding a constant to `f` does not change whether it is strictly plurisubharmonic, in any dimension
(`TauCeti.isStrictlyPlurisubharmonicAt_const_add_iff`).

The second derivative of `f` is continuous at `x` (Tau Ceti's
`ContDiffAt.continuousAt_fderiv_fderiv`), and the bilinear forms whose Levi form is positive on a
subspace of codimension at most `q` form an open set
(`TauCeti.isOpen_setOf_re_leviForm_posOnSubspace`). The bound on a compact set is Tau Ceti's
`IsCompact.exists_pos_mul_sq_norm_le_re_leviForm` applied to the second derivative of `f`.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2.
-/

public section

open Filter Topology
open scoped ContDiff

namespace TauCeti

section Const

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Adding a constant to a function does not change whether it is strictly plurisubharmonic. -/
@[simp]
theorem isStrictlyPlurisubharmonicAt_const_add_iff (c : ℝ) (f : V → ℝ) (x : V) :
    IsStrictlyPlurisubharmonicAt (fun y ↦ c + f y) x ↔ IsStrictlyPlurisubharmonicAt f x := by
  simp only [isStrictlyPlurisubharmonicAt_iff, leviForm_const_add]

end Const

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {f : V → ℝ} {x : V}

/-- **Strong `q`-pseudoconvexity is an open condition.** If `f` is `C²` at `x` and strongly
`q`-pseudoconvex at `x`, then it is strongly `q`-pseudoconvex at every point near `x`. -/
theorem IsStronglyPseudoconvexAt.eventually {q : ℕ} (h : IsStronglyPseudoconvexAt q f x)
    (hf : ContDiffAt ℝ 2 f x) : ∀ᶠ y in 𝓝 x, IsStronglyPseudoconvexAt q f y := by
  have hmem := (hf.continuousAt_fderiv_fderiv le_rfl).eventually_mem
    ((isOpen_setOf_re_leviForm_posOnSubspace q).mem_nhds
      (by simpa only [Set.mem_ofPred_eq, leviForm_def] using isStronglyPseudoconvexAt_iff.mp h))
  filter_upwards [hmem] with y hy
  simpa only [isStronglyPseudoconvexAt_iff, Set.mem_ofPred_eq, leviForm_def] using hy

/-- **Strict plurisubharmonicity is an open condition.** If `f` is `C²` at `x` and strictly
plurisubharmonic at `x`, then it is strictly plurisubharmonic at every point near `x`. -/
theorem IsStrictlyPlurisubharmonicAt.eventually (h : IsStrictlyPlurisubharmonicAt f x)
    (hf : ContDiffAt ℝ 2 f x) : ∀ᶠ y in 𝓝 x, IsStrictlyPlurisubharmonicAt f y := by
  simpa only [isStronglyPseudoconvexAt_zero_iff] using
    (h.isStronglyPseudoconvexAt 0).eventually hf

/-- **Uniform strict plurisubharmonicity on compact sets.** If `f` is `C²` and strictly
plurisubharmonic at every point of a compact set `K`, then there is `c > 0` with
`c * ‖v‖ ^ 2 ≤ (leviForm f z v v).re` for all `z ∈ K` and all vectors `v`. -/
theorem _root_.IsCompact.exists_pos_mul_sq_norm_le_re_leviForm_of_isStrictlyPlurisubharmonicAt
    {K : Set V} (hK : IsCompact K) (hf : ∀ z ∈ K, ContDiffAt ℝ 2 f z)
    (hfs : ∀ z ∈ K, IsStrictlyPlurisubharmonicAt f z) :
    ∃ c > 0, ∀ z ∈ K, ∀ v, c * ‖v‖ ^ 2 ≤ (leviForm f z v v).re := by
  simp only [leviForm_def]
  refine hK.exists_pos_mul_sq_norm_le_re_leviForm
    (fun z hz ↦ ((hf z hz).continuousAt_fderiv_fderiv le_rfl).continuousWithinAt)
    fun z hz v hv ↦ ?_
  rw [← leviForm_def]
  exact isStrictlyPlurisubharmonicAt_iff.1 (hfs z hz) v hv

end TauCeti

end
