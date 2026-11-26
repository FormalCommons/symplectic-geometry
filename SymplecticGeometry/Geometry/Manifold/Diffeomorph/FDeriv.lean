/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import TauCeti.Geometry.Manifold.Diffeomorph.NormedSpace

/-!
# Derivatives along a diffeomorphism of a normed space

For a `C^n` diffeomorphism `Φ` of a real normed space `E`:

* a smooth family of linear maps `G : E → E →L[ℝ] F` pulls back along `Φ` to the family
  `x ↦ G (Φ x) ∘L fderiv ℝ Φ x`, which is `C^m` when `G` is and `m + 1 ≤ n`;
* for `f'` differentiable at `z`, the derivative of `f' ∘ Φ.symm` at `Φ z`, minus `G (Φ z)`, is
  the derivative of `f'` at `z`, minus the pulled-back `G (Φ z) ∘L fderiv ℝ Φ z`, composed with
  `fderiv ℝ Φ.symm (Φ z)`.

The second uses Tau Ceti's `Diffeomorph.fderiv_apply_fderiv_symm_apply`.

## Main results

* `Diffeomorph.contDiff_clm_comp_fderiv`: the pulled-back family is `C^m`.
* `Diffeomorph.fderiv_comp_symm_sub_apply`: the derivative of `f' ∘ Φ.symm` against `G`.
-/

public section

open scoped Manifold ContDiff

namespace Diffeomorph

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {n : WithTop ℕ∞} (Φ : E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E)

/-- The family `x ↦ G (Φ x) ∘L fderiv ℝ Φ x` is `C^m` when `G` is and `Φ` is a `C^n`
diffeomorphism with `m + 1 ≤ n`. -/
theorem contDiff_clm_comp_fderiv {m : WithTop ℕ∞} {G : E → E →L[ℝ] F} (hG : ContDiff ℝ m G)
    (hmn : m + 1 ≤ n) : ContDiff ℝ m fun x ↦ (G (Φ x)).comp (fderiv ℝ Φ x) :=
  (hG.comp (Φ.contDiff.of_le (le_self_add.trans hmn))).clm_comp (Φ.contDiff.fderiv_right hmn)

/-- If `f'` is differentiable at `z`, then on a vector `w`, the derivative of `f' ∘ Φ.symm` at
`Φ z` minus `G (Φ z)` is the derivative of `f'` at `z` minus `G (Φ z) ∘L fderiv ℝ Φ z`, on the
vector `fderiv ℝ Φ.symm (Φ z) w`. -/
theorem fderiv_comp_symm_sub_apply (hn : n ≠ 0) {f' : E → F} {G : E → E →L[ℝ] F} {z : E}
    (hf' : DifferentiableAt ℝ f' z) (w : E) :
    (fderiv ℝ (f' ∘ Φ.symm) (Φ z) - G (Φ z)) w =
      (fderiv ℝ f' z - (G (Φ z)).comp (fderiv ℝ Φ z)) (fderiv ℝ Φ.symm (Φ z) w) := by
  have hΦs := Φ.symm.differentiable hn (Φ z)
  have hw := Φ.fderiv_apply_fderiv_symm_apply hn (Φ z) w
  rw [fderiv_comp (Φ z) (by rwa [Φ.symm_apply_apply]) hΦs]
  rw [Φ.symm_apply_apply] at hw ⊢
  simp [hw]

end Diffeomorph

end
