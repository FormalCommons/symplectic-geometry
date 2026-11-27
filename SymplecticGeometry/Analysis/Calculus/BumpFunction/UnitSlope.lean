/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Small compactly supported functions of slope one at the origin

For `w > 0` and `η > 0` there is a smooth function `h : ℝ → ℝ` with `h 0 = 0` and `h' 0 = 1`,
vanishing where `w ≤ |s|`, with `|h| ≤ η` and with `h'` taking values in `[-η, 1 + η]`
(`SymplecticGeometry.exists_contDiff_deriv_zero_eq_one_abs_le`). Such a function rises with
slope one at the origin, yet its height is small and it comes back to `0` with a slope that is
small as well: its support is long compared with its height. Compare Tau Ceti's
`TauCeti.exists_contDiff_hasDerivAt_abs_le`, which gives an analytic function with `h 0 = 0`,
`h' 0 = 1` and `|h| ≤ η`, but without compact support and without control of `h'`. The
function here is only `C^∞`: a nonzero analytic function on `ℝ` never has compact support.

It is `h s = ε * arctan (s / ε) * f s` for a bump function `f` equal to `1` near `0` and
vanishing outside `(-w / 2, w / 2)`, and `ε` small. Then
`h' s = f s / (1 + (s / ε) ^ 2) + ε * arctan (s / ε) * f' s`: the first term lies in `[0, 1]`,
and the second is at most `2 ε sup |f'|` in absolute value, as is `h`.

Profiles of this kind are used to modify a function near a hypersurface with a prescribed
normal derivative there, as in Step 2 of the proof of Theorem 8.5 of Cieliebak–Eliashberg.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012],
  Step 2 of the proof of Theorem 8.5.
-/

public section

open Set Real
open scoped ContDiff

namespace SymplecticGeometry

/-- For `w > 0` and `η > 0` there is a smooth function `h : ℝ → ℝ` with `h 0 = 0` and
`h' 0 = 1` that vanishes where `w ≤ |s|`, with `|h| ≤ η` and `h' s ∈ [-η, 1 + η]` everywhere. -/
theorem exists_contDiff_deriv_zero_eq_one_abs_le {w η : ℝ} (hw : 0 < w) (hη : 0 < η) :
    ∃ h : ℝ → ℝ, ContDiff ℝ ∞ h ∧ h 0 = 0 ∧ deriv h 0 = 1 ∧ (∀ s, w ≤ |s| → h s = 0) ∧
      (∀ s, |h s| ≤ η) ∧ ∀ s, deriv h s ∈ Icc (-η) (1 + η) := by
  let f : ContDiffBump (0 : ℝ) := ⟨w / 4, w / 2, by positivity, by linarith⟩
  obtain ⟨K, hK⟩ : ∃ K, ∀ s, ‖deriv f s‖ ≤ K :=
    ((f.contDiff (n := 1)).continuous_deriv le_rfl).bounded_above_of_compact_support
      f.hasCompactSupport.deriv
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  set ε := η / (2 * (K + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have h2ε : 2 * ε ≤ η := by
    rw [hε_def, mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  have h2εK : 2 * ε * K ≤ η := by
    rw [hε_def, mul_div_assoc', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have harc (x : ℝ) : |arctan x| ≤ 2 := by
    have := neg_pi_div_two_lt_arctan x
    have := arctan_lt_pi_div_two x
    have := pi_le_four
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have hd (s : ℝ) : HasDerivAt (fun s ↦ ε * arctan (s / ε) * f s)
      (f s / (1 + (s / ε) ^ 2) + ε * arctan (s / ε) * deriv f s) s := by
    have := (((hasDerivAt_id s).div_const ε).arctan.const_mul ε).mul
      (((f.contDiff (n := 1)).differentiable one_ne_zero) s).hasDerivAt
    convert this using 1
    · ext; simp
    · simp only [id]
      field_simp [hε.ne']
  refine ⟨fun s ↦ ε * arctan (s / ε) * f s, ?_, by simp, ?_, fun s hs ↦ ?_, fun s ↦ ?_,
    fun s ↦ ?_⟩
  · exact (contDiff_const.mul (contDiff_arctan.comp (contDiff_id.div_const ε))).mul f.contDiff
  · rw [(hd 0).deriv,
      f.one_of_mem_closedBall (by rw [Metric.mem_closedBall, dist_self]; positivity)]
    simp
  · dsimp only
    rw [f.zero_of_le_dist (by simpa [Real.dist_eq] using (by linarith : w / 2 ≤ |s|)), mul_zero]
  · rw [abs_mul, abs_mul, abs_of_pos hε, abs_of_nonneg f.nonneg]
    calc ε * |arctan (s / ε)| * f s ≤ ε * 2 * 1 := by
          gcongr
          all_goals first | exact harc _ | exact f.le_one | exact f.nonneg
      _ ≤ η := by linarith
  · rw [(hd s).deriv]
    have hp0 : 0 ≤ f s / (1 + (s / ε) ^ 2) := div_nonneg f.nonneg (by positivity)
    have hp1 : f s / (1 + (s / ε) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith [f.le_one (x := s), sq_nonneg (s / ε)]
    have he : |ε * arctan (s / ε) * deriv f s| ≤ η := by
      rw [abs_mul, abs_mul, abs_of_pos hε]
      calc ε * |arctan (s / ε)| * |deriv f s| ≤ ε * 2 * K := by
            gcongr
            all_goals first | exact harc _ | exact hK s
        _ ≤ η := by linarith
    have := abs_le.1 he
    exact ⟨by linarith, by linarith⟩

end SymplecticGeometry

end
