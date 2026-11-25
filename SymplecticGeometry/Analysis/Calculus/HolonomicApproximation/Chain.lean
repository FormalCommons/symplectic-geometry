/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Gluing a finite chain of sections by scalar cutoffs

For maps `S 0, S 1, …, S n` from `X` to a module `M` and scalar functions `φ 0, …, φ (n - 1)`,
this file studies the map

`y ↦ S 0 y + ∑ l ∈ Finset.range n, φ l y • (S (l + 1) y - S l y)`,

which passes from `S l` to `S (l + 1)` as `φ l` goes from `0` to `1`. Holonomic approximation
along a zig-zag glues Taylor sections in this way, one cutoff for each crossing, as in
[EliashbergMishachev2002], Chapter 3. Where the cutoffs before the `i`-th are `1` and those after
it are `0`, the chain is the two-term interpolation `S i + φ i • (S (i + 1) - S i)`, whose
derivative `SymplecticGeometry.norm_fderiv_add_smul_sub_sub_le` estimates.

The statements are about the expression itself, with no definition for it. The pointwise
statements are about vectors `v l` and scalars `t l`, to be applied with `v l = S l y` and
`t l = φ l y`.

## Main results

* `SymplecticGeometry.add_sum_range_smul_sub_eq_of_lt`: where `t l = 1` for `l < i` and `t l = 0`
  for `i < l < n`, the chain equals `v i + t i • (v (i + 1) - v i)`.
* `SymplecticGeometry.add_sum_range_smul_sub_eq_left`,
  `SymplecticGeometry.add_sum_range_smul_sub_eq_right`: where all `t l` are `0` the chain is
  `v 0`, and where all are `1` it is `v n`.
* `SymplecticGeometry.eventuallyEq_add_sum_range_smul_sub_of_lt`,
  `SymplecticGeometry.eventuallyEq_add_sum_range_smul_sub_left`,
  `SymplecticGeometry.eventuallyEq_add_sum_range_smul_sub_right`: the same for maps, along any
  filter on which the conditions hold eventually; along `𝓝 x` the two sides then have the same
  `fderiv` at `x`, by `Filter.EventuallyEq.fderiv_eq`.
* `ContDiff.add_sum_range_smul_sub`, `ContDiffAt.add_sum_range_smul_sub`: the chain is `C^k`
  (at a point) when the `S l` with `l ≤ n` and the `φ l` with `l < n` are.

## References

* [Y. Eliashberg and N. Mishachev, *Introduction to the h-Principle*][EliashbergMishachev2002]
-/

public section

open Finset Filter

section Smooth

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {S : ℕ → E → F} {φ : ℕ → E → 𝕜} {n : ℕ}
  {k : WithTop ℕ∞}

/-- The chain `y ↦ S 0 y + ∑ l < n, φ l y • (S (l + 1) y - S l y)` is `C^k` at `x` when the
sections `S l` with `l ≤ n` and the cutoffs `φ l` with `l < n` are. -/
theorem ContDiffAt.add_sum_range_smul_sub {x : E} (hS : ∀ l ≤ n, ContDiffAt 𝕜 k (S l) x)
    (hφ : ∀ l < n, ContDiffAt 𝕜 k (φ l) x) :
    ContDiffAt 𝕜 k (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) x := by
  refine (hS 0 n.zero_le).add (ContDiffAt.sum fun l hl ↦ ?_)
  have hl := mem_range.1 hl
  exact (hφ l hl).smul ((hS (l + 1) hl).sub (hS l hl.le))

/-- The chain `y ↦ S 0 y + ∑ l < n, φ l y • (S (l + 1) y - S l y)` is `C^k` when the sections
`S l` with `l ≤ n` and the cutoffs `φ l` with `l < n` are. -/
theorem ContDiff.add_sum_range_smul_sub (hS : ∀ l ≤ n, ContDiff 𝕜 k (S l))
    (hφ : ∀ l < n, ContDiff 𝕜 k (φ l)) :
    ContDiff 𝕜 k (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) :=
  contDiff_iff_contDiffAt.2 fun _ ↦
    .add_sum_range_smul_sub (fun l hl ↦ (hS l hl).contDiffAt) fun l hl ↦ (hφ l hl).contDiffAt

end Smooth

namespace SymplecticGeometry

variable {R M X : Type*} [Ring R] [AddCommGroup M] [Module R M] {n i : ℕ}

section Pointwise

variable {v : ℕ → M} {t : ℕ → R}

/-- Where `t l = 1` for every `l < i` and `t l = 0` for every `i < l < n`, with `i < n`, the
chain `v 0 + ∑ l < n, t l • (v (l + 1) - v l)` equals `v i + t i • (v (i + 1) - v i)`. -/
theorem add_sum_range_smul_sub_eq_of_lt (hi : i < n) (h₁ : ∀ l < i, t l = 1)
    (h₀ : ∀ l, i < l → l < n → t l = 0) :
    v 0 + ∑ l ∈ range n, t l • (v (l + 1) - v l) = v i + t i • (v (i + 1) - v i) := by
  rw [← sum_range_add_sum_Ico _ hi.le, sum_congr rfl fun l hl ↦ by
      rw [h₁ l (mem_range.1 hl), one_smul], sum_range_sub,
    sum_eq_single_of_mem i (by simpa using hi) fun l hl hne ↦ by
      rw [h₀ l (lt_of_le_of_ne (mem_Ico.1 hl).1 (Ne.symm hne)) (mem_Ico.1 hl).2, zero_smul]]
  abel

/-- Where `t l = 0` for every `l < n`, the chain `v 0 + ∑ l < n, t l • (v (l + 1) - v l)` equals
`v 0`. -/
theorem add_sum_range_smul_sub_eq_left (h₀ : ∀ l < n, t l = 0) :
    v 0 + ∑ l ∈ range n, t l • (v (l + 1) - v l) = v 0 := by
  rw [sum_eq_zero fun l hl ↦ by rw [h₀ l (mem_range.1 hl), zero_smul], add_zero]

/-- Where `t l = 1` for every `l < n`, the chain `v 0 + ∑ l < n, t l • (v (l + 1) - v l)` equals
`v n`. -/
theorem add_sum_range_smul_sub_eq_right (h₁ : ∀ l < n, t l = 1) :
    v 0 + ∑ l ∈ range n, t l • (v (l + 1) - v l) = v n := by
  rw [sum_congr rfl fun l hl ↦ by rw [h₁ l (mem_range.1 hl), one_smul], sum_range_sub,
    add_sub_cancel]

end Pointwise

section Eventually

variable {S : ℕ → X → M} {φ : ℕ → X → R} {L : Filter X}

/-- If, eventually along `L`, `φ l = 1` for every `l < i` and `φ l = 0` for every `i < l < n`,
with `i < n`, then the chain `S 0 + ∑ l < n, φ l • (S (l + 1) - S l)` is eventually equal along
`L` to `S i + φ i • (S (i + 1) - S i)`. -/
theorem eventuallyEq_add_sum_range_smul_sub_of_lt (hi : i < n)
    (h : ∀ᶠ y in L, (∀ l < i, φ l y = 1) ∧ ∀ l, i < l → l < n → φ l y = 0) :
    (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) =ᶠ[L]
      fun y ↦ S i y + φ i y • (S (i + 1) y - S i y) :=
  h.mono fun y hy ↦ add_sum_range_smul_sub_eq_of_lt (v := fun l ↦ S l y) hi hy.1 hy.2

/-- If, eventually along `L`, `φ l = 0` for every `l < n`, then the chain
`S 0 + ∑ l < n, φ l • (S (l + 1) - S l)` is eventually equal to `S 0` along `L`. -/
theorem eventuallyEq_add_sum_range_smul_sub_left (h : ∀ᶠ y in L, ∀ l < n, φ l y = 0) :
    (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) =ᶠ[L] S 0 :=
  h.mono fun y hy ↦ add_sum_range_smul_sub_eq_left (v := fun l ↦ S l y) hy

/-- If, eventually along `L`, `φ l = 1` for every `l < n`, then the chain
`S 0 + ∑ l < n, φ l • (S (l + 1) - S l)` is eventually equal to `S n` along `L`. -/
theorem eventuallyEq_add_sum_range_smul_sub_right (h : ∀ᶠ y in L, ∀ l < n, φ l y = 1) :
    (fun y ↦ S 0 y + ∑ l ∈ range n, φ l y • (S (l + 1) y - S l y)) =ᶠ[L] S n :=
  h.mono fun y hy ↦ add_sum_range_smul_sub_eq_right (v := fun l ↦ S l y) hy

end Eventually

end SymplecticGeometry

end
