/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Family

/-!
# Slices of the linear interpolation of two forms

Tau Ceti's `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc` is the smooth form on `ℝ × M` whose slice
at time `t` is `α₀ + c(t) (α₁ - α₀)`, and `TauCeti.SmoothForm.mpullback_prodMk_lineMapFamily`
states this for the smooth pullback. This file states the same identity for the underlying rough
forms and the rough pullback `TauCeti.mpullback`, the form in which proofs that work pointwise
meet the slices.

## Main results

* `TauCeti.SmoothForm.coe_mpullback_prodMk_lineMapFamily`: the slices of
  `TauCeti.SmoothForm.lineMapFamily`, stated for the underlying rough forms.
-/

public section

open scoped ContDiff Manifold

namespace TauCeti.SmoothForm

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The slices of `TauCeti.SmoothForm.lineMapFamily α₀ α₁ hc`, as rough forms: the pullback of
the underlying form along `x ↦ (t, x)` is the underlying form of `α₀ + c(t) (α₁ - α₀)`. -/
@[simp]
theorem coe_mpullback_prodMk_lineMapFamily (α₀ α₁ : SmoothForm I M F k) {c : ℝ → ℝ}
    (hc : ContDiff ℝ ∞ c) (t : ℝ) :
    TauCeti.mpullback (F := F) I (𝓘(ℝ, ℝ).prod I) (Prod.mk t) (lineMapFamily α₀ α₁ hc).val =
      (α₀ + c t • (α₁ - α₀)).val :=
  (coe_mpullback _ _ _).symm.trans
    (congrArg Subtype.val (mpullback_prodMk_lineMapFamily α₀ α₁ hc t))

end TauCeti.SmoothForm

end
