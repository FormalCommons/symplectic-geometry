/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Basic

/-!
# The symplectization form as a product with a smooth function

This file extends Tau Ceti's `TauCeti.Geometry.Contact.Symplectization.Basic`. Tau Ceti defines
the symplectization form `TauCeti.SmoothForm.symplectization α` of a one-form `α` on `M` by its
values, `(t, x) ↦ eᵗ α_x`. Here it is written as the pullback of `α` along `Prod.snd`, multiplied
by a smooth function through `TauCeti.SmoothForm.funSMulₗ`, so that the lemmas about `funSMulₗ`
(pullbacks, sums) apply to it.

## Main results

* `TauCeti.SmoothForm.symplectization_eq_funSMulₗ`
* `TauCeti.SmoothForm.symplectization_neg`: the symplectization form of `-α` is the negative of
  that of `α`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Section 3.5
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The symplectization form `eᵗ α` is the pullback of `α` along the projection to `M`,
multiplied by any smooth function `g` with `g (t, x) = eᵗ`. -/
theorem symplectization_eq_funSMulₗ (α : SmoothForm I M ℝ 1) {g : C^∞⟮𝓘(ℝ).prod I, ℝ × M; ℝ⟯}
    (hg : ∀ p, g p = Real.exp p.1) :
    α.symplectization = funSMulₗ g (mpullback Prod.snd contMDiff_snd α) := by
  apply Subtype.ext
  rw [coe_symplectization, coe_funSMulₗ]
  funext p
  rw [hg]

/-- The symplectization form of `-α` is the negative of that of `α`. -/
theorem symplectization_neg (α : SmoothForm I M ℝ 1) :
    (-α).symplectization = -α.symplectization := by
  apply Subtype.ext
  funext p
  simp [coe_symplectization, map_neg]

end SmoothForm

end TauCeti

end
