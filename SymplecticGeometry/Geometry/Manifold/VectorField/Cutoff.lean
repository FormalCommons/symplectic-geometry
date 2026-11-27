/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Cutting a vector field off below a level of a function

Let `g : M → ℝ` be smooth and `X` a smooth vector field on `M`. For levels `c < d`, the field
`(ρ ∘ g) • X`, where `ρ` is a smooth step from `0` on `(-∞, c]` to `1` on `[d, ∞)` with values in
`[0, 1]`, is smooth, vanishes where `g ≤ c`, agrees with `X` where `d ≤ g`, and is everywhere a
multiple `r • X` with `0 ≤ r ≤ 1`. The step is Tau Ceti's antitone cutoff
`TauCeti.exists_contDiff_antitone_cutoff`, composed with `s ↦ -s`.

## Main results

* `TauCeti.exists_cutoff_vectorField`: a smooth vector field cut off below one level of a smooth
  function and unchanged above a higher one.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Cutting a vector field off below a level.** Let `g : M → ℝ` and the vector field `X` be
smooth, and let `c < d`. Then there is a smooth vector field `Y` that vanishes at the points where
`g ≤ c`, equals `X` at the points where `d ≤ g`, and is at each point `x` a multiple `r • X x` of
`X` with `0 ≤ r ≤ 1`. -/
theorem exists_cutoff_vectorField {g : M → ℝ} (hg : ContMDiff I 𝓘(ℝ) ∞ g)
    {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M))) {c d : ℝ}
    (hcd : c < d) :
    ∃ Y : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent ∞ (fun x ↦ (⟨x, Y x⟩ : TangentBundle I M)) ∧
      (∀ x, g x ≤ c → Y x = 0) ∧ (∀ x, d ≤ g x → Y x = X x) ∧
      ∀ x, ∃ r ∈ Icc (0 : ℝ) 1, Y x = r • X x := by
  -- `Y = (ρ ∘ g) • X` for the step `ρ s = μ (-s)`, `0` on `(-∞, c]` and `1` on `[d, ∞)`.
  obtain ⟨μ, hμ, hμa, hμ0, hμc, hμd, -⟩ :=
    exists_contDiff_antitone_cutoff (neg_lt_neg hcd) zero_le_one
  refine ⟨fun x ↦ μ (-g x) • X x,
    ContMDiff.smul_section ((hμ.comp contDiff_neg).contMDiff.comp hg) hX,
    fun x hx ↦ ?_, fun x hx ↦ ?_, fun x ↦ ⟨μ (-g x), ⟨hμ0 _, ?_⟩, rfl⟩⟩
  · simp only [hμc _ (neg_le_neg hx), zero_smul]
  · simp only [hμd _ (neg_le_neg hx), one_smul]
  · exact (hμa (min_le_left _ (-d))).trans_eq (hμd _ (min_le_right _ _))

end TauCeti

end
