/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.Taylor.Integral

/-!
# Maps whose low-order derivatives vanish at a point

If the derivatives of `f` of order at most `N` vanish at `x`, and the derivative of order
`N + 1` is bounded by `M` along the segment from `x` to `x + y`, then the derivative of order
`j ≤ N + 1` at `x + y` is at most `M * ‖y‖ ^ (N + 1 - j)`.

## Main results

* `SymplecticGeometry.norm_iteratedFDeriv_add_le_of_iteratedFDeriv_eq_zero`: the bound above.

The proof applies Tau Ceti's Taylor remainder bound `TauCeti.norm_map_add_sub_sum_iteratedFDeriv_le`
to the derivative of order `j` of `f`, whose Taylor polynomial of order `N - j` at `x` vanishes,
and whose derivatives of order `i` have the norms of those of `f` of order `i + j`
(`TauCeti.norm_iteratedFDeriv_iteratedFDeriv`).
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

namespace SymplecticGeometry

/-- If `f` is `C^(N + 1)` along the segment from `x` to `x + y`, its derivatives of order at most
`N` vanish at `x`, and `‖D^(N+1) f‖ ≤ M` on that segment, then
`‖D^j f (x + y)‖ ≤ M * ‖y‖ ^ (N + 1 - j)` for every `j ≤ N + 1`. -/
theorem norm_iteratedFDeriv_add_le_of_iteratedFDeriv_eq_zero {f : E → F} {x y : E} {N j : ℕ}
    {M : ℝ} (hj : j ≤ N + 1) (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ (N + 1) f (x + t • y))
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖iteratedFDeriv ℝ (N + 1) f (x + t • y)‖ ≤ M)
    (h0 : ∀ k ≤ N, iteratedFDeriv ℝ k f x = 0) :
    ‖iteratedFDeriv ℝ j f (x + y)‖ ≤ M * ‖y‖ ^ (N + 1 - j) := by
  rcases hj.eq_or_lt with rfl | hj
  · simpa using hM 1 (Set.right_mem_Icc.2 zero_le_one)
  obtain ⟨n, rfl⟩ : ∃ n, N = n + j := ⟨N - j, by omega⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Set.left_mem_Icc.2 zero_le_one))
  have h := TauCeti.norm_map_add_sub_sum_iteratedFDeriv_le (f := iteratedFDeriv ℝ j f) (x := x)
    (y := y) (n := n) (M := M)
    (fun t ht ↦ (hf t ht).iteratedFDeriv_right (by push_cast; exact le_of_eq (by ring)))
    (fun t ht ↦ by
      rw [TauCeti.norm_iteratedFDeriv_iteratedFDeriv, show n + 1 + j = n + j + 1 by ring]
      exact hM t (Set.Ioo_subset_Icc_self ht))
  rw [Finset.sum_eq_zero fun k hk ↦ ?_, sub_zero] at h
  · rw [show n + j + 1 - j = n + 1 by omega]
    refine h.trans (div_le_self (by positivity) ?_)
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
  · have : iteratedFDeriv ℝ k (iteratedFDeriv ℝ j f) x = 0 := by
      rw [← norm_eq_zero, TauCeti.norm_iteratedFDeriv_iteratedFDeriv,
        h0 _ (by simp at hk; omega), norm_zero]
    simp [this]

end SymplecticGeometry

end
