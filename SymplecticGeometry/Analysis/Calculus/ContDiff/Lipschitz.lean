/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Smooth self-maps that are the identity off a compact set are Lipschitz

A `C^n` self-map `g` (`n ≠ 0`) of a real normed space that is the identity off a compact set is
Lipschitz: `g - id` is `C^n` with compact support, so Mathlib's
`ContDiff.lipschitzWith_of_hasCompactSupport` makes it Lipschitz, and `g = (g - id) + id`.

## Main results

* `ContDiff.exists_lipschitzWith_of_forall_notMem_eq_self`: such a map is Lipschitz.
-/

public section

open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

/-- A `C^n` self-map, `n ≠ 0`, of a real normed space that is the identity off a compact set is
Lipschitz. -/
theorem ContDiff.exists_lipschitzWith_of_forall_notMem_eq_self {g : E → E}
    (hg : ContDiff ℝ n g) (hn : n ≠ 0) {C : Set E} (hC : IsCompact C)
    (hgC : ∀ x ∉ C, g x = x) : ∃ K : ℝ≥0, LipschitzWith K g := by
  obtain ⟨K, hK⟩ := (hg.sub contDiff_id).lipschitzWith_of_hasCompactSupport
    (HasCompactSupport.intro hC fun x hx ↦ by simp [hgC x hx]) hn
  exact ⟨K + 1, by simpa using hK.add LipschitzWith.id⟩

end
