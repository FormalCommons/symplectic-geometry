/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Bounds on the first two derivatives over a compact set

A map that is `C²` at every point of a compact set `s` has first and second derivatives bounded
on `s` by one constant (`IsCompact.exists_forall_norm_fderiv_le_and_norm_fderiv_fderiv_le`): both
derivatives are continuous at the points of `s`, by Mathlib's `ContDiffAt.continuousAt_fderiv` and
Tau Ceti's `ContDiffAt.continuousAt_fderiv_fderiv`, so each is bounded on `s`
(`IsCompact.exists_bound_of_continuousOn`).
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A map that is `C^n`, `2 ≤ n`, at every point of a compact set `s` has a constant `B` with
`‖fderiv 𝕜 f x‖ ≤ B` and `‖fderiv 𝕜 (fderiv 𝕜 f) x‖ ≤ B` for every `x ∈ s`. -/
theorem IsCompact.exists_forall_norm_fderiv_le_and_norm_fderiv_fderiv_le {n : WithTop ℕ∞}
    {f : E → F} {s : Set E} (hs : IsCompact s) (hn : 2 ≤ n) (hf : ∀ x ∈ s, ContDiffAt 𝕜 n f x) :
    ∃ B, ∀ x ∈ s, ‖fderiv 𝕜 f x‖ ≤ B ∧ ‖fderiv 𝕜 (fderiv 𝕜 f) x‖ ≤ B := by
  obtain ⟨B₁, hB₁⟩ := hs.exists_bound_of_continuousOn (f := fderiv 𝕜 f) fun x hx ↦
    ((hf x hx).continuousAt_fderiv (two_pos.trans_le hn).ne').continuousWithinAt
  obtain ⟨B₂, hB₂⟩ := hs.exists_bound_of_continuousOn (f := fderiv 𝕜 (fderiv 𝕜 f))
    fun x hx ↦ ((hf x hx).continuousAt_fderiv_fderiv hn).continuousWithinAt
  exact ⟨max B₁ B₂, fun x hx ↦
    ⟨(hB₁ x hx).trans (le_max_left _ _), (hB₂ x hx).trans (le_max_right _ _)⟩⟩

end
