/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Analysis.Complex.Pseudoconvex

/-!
# Strong pseudoconvexity persists near a point

For a real function `f` on a finite-dimensional complex vector space that is `C²` at `x`, strong
`q`-pseudoconvexity at `x` (Tau Ceti's `TauCeti.IsStronglyPseudoconvexAt`) holds at all points
near `x`, and so does strict plurisubharmonicity:

* `TauCeti.IsStronglyPseudoconvexAt.eventually`,
* `TauCeti.IsStrictlyPlurisubharmonicAt.eventually`.

The second derivative of `f` is continuous at `x`, and the bilinear forms whose Levi form is
positive on a subspace of codimension at most `q` form an open set
(`TauCeti.isOpen_setOf_re_leviForm_posOnSubspace`).

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Chapter 2.
-/

public section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {f : V → ℝ} {x : V}

/-- **Strong `q`-pseudoconvexity is an open condition.** If `f` is `C²` at `x` and strongly
`q`-pseudoconvex at `x`, then it is strongly `q`-pseudoconvex at every point near `x`. -/
theorem IsStronglyPseudoconvexAt.eventually {q : ℕ} (h : IsStronglyPseudoconvexAt q f x)
    (hf : ContDiffAt ℝ 2 f x) : ∀ᶠ y in 𝓝 x, IsStronglyPseudoconvexAt q f y := by
  have hcont : ContinuousAt (fun y ↦ fderiv ℝ (fderiv ℝ f) y) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuousAt
  have hmem := hcont.eventually_mem ((isOpen_setOf_re_leviForm_posOnSubspace q).mem_nhds
    (by simpa only [Set.mem_ofPred_eq, leviForm_def] using isStronglyPseudoconvexAt_iff.mp h))
  filter_upwards [hmem] with y hy
  simpa only [isStronglyPseudoconvexAt_iff, Set.mem_ofPred_eq, leviForm_def] using hy

/-- **Strict plurisubharmonicity is an open condition.** If `f` is `C²` at `x` and strictly
plurisubharmonic at `x`, then it is strictly plurisubharmonic at every point near `x`. -/
theorem IsStrictlyPlurisubharmonicAt.eventually (h : IsStrictlyPlurisubharmonicAt f x)
    (hf : ContDiffAt ℝ 2 f x) : ∀ᶠ y in 𝓝 x, IsStrictlyPlurisubharmonicAt f y := by
  simpa only [isStronglyPseudoconvexAt_zero_iff] using
    (h.isStronglyPseudoconvexAt 0).eventually hf

end TauCeti

end
