/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions

/-!
# Lower bounds for the sup norm on a finite product

Mathlib bounds the sup norm of a finite product from above by its coordinates
(`pi_norm_le_iff_of_nonneg`). This file adds a lower bound in the same spirit: if each coordinate
of `b` has norm at least `min ‖a i‖ c`, then `‖b‖ ≥ min ‖a‖ c`
(`min_norm_le_pi_norm_of_forall`). It also computes the sup norm over an index type with one
element (`Pi.norm_eq_norm_default`), and the sup norm of the concatenation of two tuples
(`Fin.norm_append`) and the sup distance of two concatenations (`Fin.dist_append`), so that
`Fin.append` is an isometry for the sup norms.
-/

public section

/-- A coordinatewise lower bound `min ‖a i‖ c ≤ ‖b i‖` gives the same lower bound
`min ‖a‖ c ≤ ‖b‖` for the sup norms. -/
theorem min_norm_le_pi_norm_of_forall {ι : Type*} [Fintype ι] {E F : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] [∀ i, SeminormedAddGroup (F i)] {a : ∀ i, E i}
    {b : ∀ i, F i} {c : ℝ} (h : ∀ i, min ‖a i‖ c ≤ ‖b i‖) : min ‖a‖ c ≤ ‖b‖ := by
  by_contra! hb
  -- Every coordinate of `b` is below `c`, so it bounds that of `a`, and then `‖a‖ ≤ ‖b‖`.
  have : ‖a‖ ≤ ‖b‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg b)).2 fun i ↦ by
    have hi := (norm_le_pi_norm b i).trans_lt (hb.trans_le (min_le_right _ _))
    have := h i
    rw [min_le_iff] at this
    rcases this with h' | h'
    · exact h'.trans (norm_le_pi_norm b i)
    · exact absurd hi h'.not_gt
  exact this.not_gt (hb.trans_le (min_le_left _ _))

/-- Over an index type with a single element, the sup norm of `x` is the norm of its one
coordinate. -/
theorem Pi.norm_eq_norm_default {ι : Type*} [Fintype ι] [Unique ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (x : ∀ i, E i) : ‖x‖ = ‖x default‖ := by
  simp [Pi.norm_def, Finset.univ_unique]

/-- The sup norm of the concatenation of two tuples is the larger of their sup norms. -/
theorem Fin.norm_append {α : Type*} [SeminormedAddGroup α] {m n : ℕ} (x : Fin m → α)
    (y : Fin n → α) : ‖Fin.append x y‖ = max ‖x‖ ‖y‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i ↦ ?_) (max_le ?_ ?_)
  · induction i using Fin.addCases with
    | left i => simpa using (norm_le_pi_norm x i).trans (le_max_left _ _)
    | right i => simpa using (norm_le_pi_norm y i).trans (le_max_right _ _)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ by
      simpa using norm_le_pi_norm (Fin.append x y) (Fin.castAdd n i)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i ↦ by
      simpa using norm_le_pi_norm (Fin.append x y) (Fin.natAdd m i)

/-- The sup distance of the concatenations of two pairs of tuples is the larger of the sup
distances of their parts. -/
theorem Fin.dist_append {α : Type*} [PseudoMetricSpace α] {m n : ℕ} (x x' : Fin m → α)
    (y y' : Fin n → α) :
    dist (Fin.append x y) (Fin.append x' y') = max (dist x x') (dist y y') := by
  refine le_antisymm ((dist_pi_le_iff (by positivity)).2 fun i ↦ ?_) (max_le ?_ ?_)
  · induction i using Fin.addCases with
    | left i => simpa using (dist_le_pi_dist x x' i).trans (le_max_left _ _)
    | right i => simpa using (dist_le_pi_dist y y' i).trans (le_max_right _ _)
  · exact (dist_pi_le_iff dist_nonneg).2 fun i ↦ by
      simpa using dist_le_pi_dist (Fin.append x y) (Fin.append x' y') (Fin.castAdd n i)
  · exact (dist_pi_le_iff dist_nonneg).2 fun i ↦ by
      simpa using dist_le_pi_dist (Fin.append x y) (Fin.append x' y') (Fin.natAdd m i)

end
