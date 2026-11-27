/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
import SymplecticGeometry.Algebra.BigOperators.Module

/-!
# Gluing a finite chain of maps by scalar cutoffs

For maps `S 0, S 1, …, S n` from `X` to a module `M` and scalar functions `φ 0, …, φ (n - 1)`,
this file studies the map

`y ↦ S 0 y + ∑ l ∈ Finset.range n, φ l y • (S (l + 1) y - S l y)`,

which passes from `S l` to `S (l + 1)` as `φ l` goes from `0` to `1`. Holonomic approximation
along a zig-zag glues Taylor sections in this way, one cutoff for each crossing, as in
[EliashbergMishachev2002], Chapter 3. Where the cutoffs before the `i`-th are `1` and those after
it are `0`, the map is the two-term interpolation `S i + φ i • (S (i + 1) - S i)`, whose
derivative `SymplecticGeometry.norm_fderiv_add_smul_sub_sub_le` estimates.

The statements are about the expression itself, with no definition for it. The values at a point
are `Finset.add_sum_range_smul_sub_eq_of_lt` and its siblings.

## Main results

* `ContDiff.add_sum_range_smul_sub`, `ContDiffAt.add_sum_range_smul_sub`: the map is `C^k`
  (at a point) when the `S l` with `l ≤ n` and the `φ l` with `l < n` are.
* `Filter.eventuallyEq_add_sum_range_smul_sub_of_lt`,
  `Filter.eventuallyEq_add_sum_range_smul_sub_left`,
  `Filter.eventuallyEq_add_sum_range_smul_sub_right`: along any filter on which the conditions on
  the cutoffs hold eventually, the map is eventually equal to `S i + φ i • (S (i + 1) - S i)`,
  to `S 0`, or to `S n`; along `𝓝 x` the two sides then have the same `fderiv` at `x`, by
  `Filter.EventuallyEq.fderiv_eq`.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Finset

section Smooth

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {S : ℕ → E → F} {φ : ℕ → E → 𝕜} {n : ℕ}
  {k : WithTop ℕ∞}

/-- The map `y ↦ S 0 y + ∑ l < n, φ l y • (S (l + 1) y - S l y)` is `C^k` at `x` when the
maps `S l` with `l ≤ n` and the cutoffs `φ l` with `l < n` are. -/
theorem ContDiffAt.add_sum_range_smul_sub {x : E} (hS : ∀ l ≤ n, ContDiffAt 𝕜 k (S l) x)
    (hφ : ∀ l < n, ContDiffAt 𝕜 k (φ l) x) :
    ContDiffAt 𝕜 k (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) x := by
  refine (hS 0 n.zero_le).add (ContDiffAt.sum fun l hl ↦ ?_)
  have hl := mem_range.1 hl
  exact (hφ l hl).smul ((hS (l + 1) hl).sub (hS l hl.le))

/-- The map `y ↦ S 0 y + ∑ l < n, φ l y • (S (l + 1) y - S l y)` is `C^k` when the maps
`S l` with `l ≤ n` and the cutoffs `φ l` with `l < n` are. -/
theorem ContDiff.add_sum_range_smul_sub (hS : ∀ l ≤ n, ContDiff 𝕜 k (S l))
    (hφ : ∀ l < n, ContDiff 𝕜 k (φ l)) :
    ContDiff 𝕜 k (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) :=
  contDiff_iff_contDiffAt.2 fun _ ↦
    .add_sum_range_smul_sub (fun l hl ↦ (hS l hl).contDiffAt) fun l hl ↦ (hφ l hl).contDiffAt

end Smooth

namespace Filter

variable {R M X : Type*} [Semiring R] [AddCommGroup M] [Module R M] {n i : ℕ}
  {S : ℕ → X → M} {φ : ℕ → X → R} {L : Filter X}

/-- If, eventually along `L`, `φ l = 1` for every `l < i` and `φ l = 0` for every `i < l < n`,
with `i < n`, then the map `S 0 + ∑ l < n, φ l • (S (l + 1) - S l)` is eventually equal along
`L` to `S i + φ i • (S (i + 1) - S i)`. -/
theorem eventuallyEq_add_sum_range_smul_sub_of_lt (hi : i < n)
    (h : ∀ᶠ y in L, (∀ l < i, φ l y = 1) ∧ ∀ l, i < l → l < n → φ l y = 0) :
    (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) =ᶠ[L]
      fun y ↦ S i y + φ i y • (S (i + 1) y - S i y) :=
  h.mono fun y hy ↦ add_sum_range_smul_sub_eq_of_lt (v := fun l ↦ S l y) hi hy.1 hy.2

/-- If, eventually along `L`, `φ l = 0` for every `l < n`, then the map
`S 0 + ∑ l < n, φ l • (S (l + 1) - S l)` is eventually equal to `S 0` along `L`. -/
theorem eventuallyEq_add_sum_range_smul_sub_left (h : ∀ᶠ y in L, ∀ l < n, φ l y = 0) :
    (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) =ᶠ[L] S 0 :=
  h.mono fun y hy ↦ add_sum_range_smul_sub_eq_left (v := fun l ↦ S l y) hy

/-- If, eventually along `L`, `φ l = 1` for every `l < n`, then the map
`S 0 + ∑ l < n, φ l • (S (l + 1) - S l)` is eventually equal to `S n` along `L`. -/
theorem eventuallyEq_add_sum_range_smul_sub_right (h : ∀ᶠ y in L, ∀ l < n, φ l y = 1) :
    (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) =ᶠ[L] S n :=
  h.mono fun y hy ↦ add_sum_range_smul_sub_eq_right (v := fun l ↦ S l y) hy

end Filter

end
