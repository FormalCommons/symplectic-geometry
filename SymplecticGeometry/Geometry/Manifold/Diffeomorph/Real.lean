/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Deriv

/-!
# Diffeomorphisms of the line that fix a half-line

For `a < b ≤ c`, this file gives an increasing diffeomorphism of `ℝ` that is the identity on
`(-∞, a]` and sends `c` to `b` (`Real.exists_diffeomorph_strictMono_eqOn_Iic`). It is the inverse
of `t ↦ t + (c - b) * smoothTransition ((t - a) / (b - a))`, which is smooth, the identity on
`(-∞, a]`, sends `b` to `c`, and has derivative at least `1`. Tau Ceti's
`TauCeti.isLocalDiffeomorph_of_deriv_ne_zero` and Mathlib's
`IsLocalDiffeomorph.diffeomorphOfBijective` make that map a diffeomorphism.

Such a diffeomorphism reparametrizes a curve without changing it on `(-∞, a]`, while moving a
later parameter `b` to `c`.

## Main results

* `Real.exists_diffeomorph_strictMono_eqOn_Iic`: for `a < b ≤ c`, an increasing diffeomorphism of
  `ℝ` that is the identity on `Iic a` and sends `c` to `b`.
-/

public section

namespace Real

open Set Filter Manifold
open scoped ContDiff

/-- For `a < b ≤ c`, some increasing diffeomorphism of `ℝ` is the identity on `(-∞, a]` and sends
`c` to `b`. -/
theorem exists_diffeomorph_strictMono_eqOn_Iic {a b c : ℝ} (hab : a < b) (hbc : b ≤ c) :
    ∃ e : ℝ ≃ₘ⟮𝓘(ℝ), 𝓘(ℝ)⟯ ℝ, StrictMono e ∧ EqOn e id (Iic a) ∧ e c = b := by
  set g : ℝ → ℝ := fun t ↦ (c - b) * smoothTransition ((t - a) / (b - a))
  set φ : ℝ → ℝ := fun t ↦ t + g t
  have hba : 0 < b - a := sub_pos.2 hab
  have hcb : 0 ≤ c - b := sub_nonneg.2 hbc
  have hg : ContDiff ℝ ∞ g := contDiff_const.mul (smoothTransition.contDiff.comp (by fun_prop))
  have hgm : Monotone g := fun s t hst ↦ mul_le_mul_of_nonneg_left
    (smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) hba.le)) hcb
  have hφ : ContDiff ℝ ∞ φ := contDiff_id.add hg
  have hφm : StrictMono φ := strictMono_id.add_monotone hgm
  have hderiv (t : ℝ) : deriv φ t ≠ 0 := by
    have : deriv φ t = 1 + deriv g t :=
      ((hasDerivAt_id' t).add ((hg.differentiable (by simp) t).hasDerivAt)).deriv
    rw [this]
    linarith [hgm.deriv_nonneg (x := t)]
  have hsurj : Function.Surjective φ :=
    hφ.continuous.surjective
      (tendsto_atTop_mono (fun t ↦ le_add_of_nonneg_right
        (mul_nonneg hcb (smoothTransition.nonneg _))) tendsto_id)
      (tendsto_atBot_mono (fun t ↦ add_le_add_right
        (mul_le_of_le_one_right hcb (smoothTransition.le_one _)) t)
        (tendsto_atBot_add_const_right _ (c - b) tendsto_id))
  set e := (TauCeti.isLocalDiffeomorph_of_deriv_ne_zero hφ (by simp)
    hderiv).diffeomorphOfBijective ⟨hφm.injective, hsurj⟩
  have he : ⇑e = φ := IsLocalDiffeomorph.coe_diffeomorphOfBijective _ _
  have hfix : EqOn φ id (Iic a) := fun t ht ↦ by
    simp [φ, g, smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ht) hba.le)]
  refine ⟨e.symm, fun s t hst ↦ ?_, fun t ht ↦ ?_, ?_⟩
  · rw [← hφm.lt_iff_lt, ← he, e.apply_symm_apply, e.apply_symm_apply]; exact hst
  · have h : φ t = t := hfix ht
    conv_lhs => rw [← h, ← he]
    exact e.symm_apply_apply t
  · have hb : φ b = c := by simp [φ, g, div_self hba.ne']
    rw [← hb, ← he]
    exact e.symm_apply_apply b

end Real

end
