/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Uniform convergence of series whose sums exist

`tendstoUniformlyOn_finsetSum_of_hasSum`: Weierstrass' test for a series of functions whose
pointwise sums are known to exist. It needs no completeness of the target, unlike Mathlib's
`tendstoUniformlyOn_tsum`, whose proof it adapts by bounding the tails.
-/

public section

open Filter

/-- Weierstrass' test for a series of functions whose sums exist: the partial sums converge
uniformly on `s` when the terms are bounded on `s` by a summable sequence. Unlike
`tendstoUniformlyOn_tsum`, this needs no completeness of the target. -/
theorem tendstoUniformlyOn_finsetSum_of_hasSum {α β G : Type*} [NormedAddCommGroup G]
    {f : α → β → G} {g : β → G} {u : α → ℝ} {s : Set β}
    (hg : ∀ x ∈ s, HasSum (fun n ↦ f n x) (g x)) (hu : Summable u)
    (hfu : ∀ n, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun t x ↦ ∑ n ∈ t, f n x) g atTop s := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε εpos ↦ ?_
  filter_upwards [(tendsto_order.1 (tendsto_tsum_compl_atTop_zero u)).2 _ εpos] with t ht x hx
  have htail : HasSum (fun n : {n // n ∉ t} ↦ f n x) (g x - ∑ n ∈ t, f n x) :=
    (t.hasSum_compl_iff (f := fun n ↦ f n x)).2 (by rw [sub_add_cancel]; exact hg x hx)
  rw [dist_eq_norm]
  exact (htail.norm_le_of_bounded (hu.subtype _).hasSum fun n ↦ hfu n x hx).trans_lt ht

end
