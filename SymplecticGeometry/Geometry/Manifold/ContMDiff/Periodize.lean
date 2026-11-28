/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Icc.CollaredSmoothTransition
import TauCeti.Geometry.Manifold.ContMDiff.Fract

/-!
# Smooth periodization of curves with equal endpoints

A curve `γ : ℝ → M` with `γ 0 = γ 1` need not extend to a smooth `1`-periodic curve. Flattened
near both ends by the collared smooth transition `ρ = TauCeti.collaredSmoothTransition`, which is
`0` up to `1 / 4` and `1` from `3 / 4` on, it does: `t ↦ γ (ρ (fract t))` is as smooth as `γ`,
and it is `1`-periodic by Mathlib's `Int.fract_periodic`. Smoothness is Tau Ceti's
`ContMDiff.comp_fract_snd`, applied to `(s, t) ↦ γ (ρ t)` on `ℝ × ℝ`, which is periodic in `t`
just below `0`.

## Main results

* `TauCeti.contMDiff_comp_collaredSmoothTransition_fract`: the periodization
  `t ↦ γ (ρ (fract t))` of a `C^n` curve `γ` with `γ 0 = γ 1` is `C^n`.
-/

public section

open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

/-- The periodization `t ↦ γ (ρ (fract t))` of a `C^n` curve `γ` with `γ 0 = γ 1`, flattened near
the ends by the collared smooth transition `ρ`, is `C^n`. -/
theorem contMDiff_comp_collaredSmoothTransition_fract {n : WithTop ℕ∞} (hn : n ≤ ∞)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I n γ) (h : γ 0 = γ 1) :
    ContMDiff 𝓘(ℝ, ℝ) I n fun t ↦ γ (collaredSmoothTransition (Int.fract t)) := by
  have hG : ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I n
      fun w : ℝ × ℝ ↦ γ (collaredSmoothTransition w.2) :=
    (hγ.comp (contDiff_collaredSmoothTransition hn).contMDiff).comp
      (contMDiff_snd (I := 𝓘(ℝ, ℝ)) (J := 𝓘(ℝ, ℝ)))
  have hper : ∀ _ : ℝ, ∀ {s : ℝ}, -(1 / 4) < s → s < 0 →
      γ (collaredSmoothTransition (s + 1)) = γ (collaredSmoothTransition s) :=
    fun _ s hs₀ hs₁ ↦ by
      rw [collaredSmoothTransition_eq_one_of_ge (by linarith : (3 / 4 : ℝ) ≤ s + 1),
        collaredSmoothTransition_eq_zero_of_le (by linarith : s ≤ 1 / 4), h]
  -- The type ascription keeps elaboration from unfolding the composite to weak head normal form.
  exact ((hG.comp_fract_snd (by norm_num : (0 : ℝ) < 1 / 4) hper).comp
    (contMDiff_const.prodMk contMDiff_id :
      ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) n fun t : ℝ ↦ ((0 : ℝ), t)) :)

end TauCeti

end
