/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Topology.Algebra.Support
import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# A bump that rises quickly and descends slowly

For `δ > 0` and `ε > 0` there is a smooth compactly supported function `μ : ℝ → ℝ` with values in
`[0, 1]` that vanishes on `(-∞, -δ]`, is monotone on `(-∞, 0]` with `μ 0 = 1`, and whose
derivative is everywhere greater than `-ε` (`SymplecticGeometry.exists_contDiff_bump_neg_lt_deriv`).
So it climbs from `0` to `1` on `[-δ, 0]`, as steeply as needed, and comes back down to `0` with
slope as small as wanted. The form used to reparametrize flow lines, `-1 < T₀ * μ' s` for a given
`T₀ ≥ 0`, is `SymplecticGeometry.exists_contDiff_bump_neg_one_lt_mul_deriv`.

The function is the product of the rescaled transition `ρ s = smoothTransition ((s + δ) / δ)`,
which is `0` on `(-∞, -δ]` and `1` on `[0, ∞)`, with a nonincreasing step `ν` from `1` to `0`
with `|ν'| < ε`, given by Tau Ceti's `TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le`. By
the product rule `μ' = ρ' ν + ρ ν'`, where the first term is nonnegative and the second is at
least `-|ν'|`.

Such a bump reparametrizes the flow lines of a Liouville field near a level set in the
attachment of handles of Cieliebak–Eliashberg.

## References

* [K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*][CieliebakEliashberg2012]
-/

public section

open Set

open scoped ContDiff

namespace SymplecticGeometry

/-- For `δ > 0` and `ε > 0` there is a smooth compactly supported `μ : ℝ → ℝ` with values in
`[0, 1]`, vanishing on `(-∞, -δ]`, monotone on `(-∞, 0]` with `μ 0 = 1`, and with derivative
greater than `-ε` everywhere. -/
theorem exists_contDiff_bump_neg_lt_deriv {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ HasCompactSupport μ ∧ (∀ s, 0 ≤ μ s ∧ μ s ≤ 1) ∧
      (∀ s ≤ -δ, μ s = 0) ∧ MonotoneOn μ (Iic 0) ∧ μ 0 = 1 ∧ ∀ s, -ε < deriv μ s := by
  obtain ⟨ν, hν, hνa, hν₀, hνb, hν₁, hν', -⟩ :=
    TauCeti.exists_contDiff_antitone_cutoff_abs_deriv_le (a := 0) (b := 4 / ε) (v := 1)
      (τ := ε / 2) (by positivity) zero_le_one (by field_simp; norm_num)
  set ρ : ℝ → ℝ := fun s ↦ Real.smoothTransition ((s + δ) / δ)
  have hρc : ContDiff ℝ ∞ ρ := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hρ₀ (s : ℝ) (hs : s ≤ -δ) : ρ s = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)
  have hρ₁ (s : ℝ) (hs : 0 ≤ s) : ρ s = 1 :=
    Real.smoothTransition.one_of_one_le ((one_le_div hδ).2 (by linarith))
  have hρm : Monotone ρ := fun s t hst ↦ Real.smoothTransition.monotone
    (div_le_div_of_nonneg_right (by linarith) hδ.le)
  have hνle (s : ℝ) : ν s ≤ 1 := (hνa (min_le_left s 0)).trans_eq (hν₁ _ (min_le_right s 0))
  have hd (s : ℝ) : HasDerivAt (fun s ↦ ρ s * ν s) (deriv ρ s * ν s + ρ s * deriv ν s) s :=
    ((hρc.differentiable (by simp)) s).hasDerivAt.mul ((hν.differentiable (by simp)) s).hasDerivAt
  refine ⟨fun s ↦ ρ s * ν s, hρc.mul hν, ?_, fun s ↦ ⟨mul_nonneg (Real.smoothTransition.nonneg _)
    (hν₀ s), (mul_le_of_le_one_left (hν₀ s)
      (Real.smoothTransition.le_one _)).trans (hνle s)⟩,
    fun s hs ↦ by simp [hρ₀ s hs], fun s hs t ht hst ↦ ?_, by simp [hρ₁ 0 le_rfl, hν₁ 0 le_rfl],
    fun s ↦ ?_⟩
  · refine HasCompactSupport.intro (isCompact_Icc (a := -δ) (b := 4 / ε)) fun s hs ↦ ?_
    rcases not_and_or.1 hs with h | h
    · simp [hρ₀ s (by linarith [not_le.1 h])]
    · simp [hνb s (by linarith [not_le.1 h])]
  · simp only [hν₁ s hs, hν₁ t ht, mul_one]
    exact hρm hst
  · rw [(hd s).deriv]
    have h₁ : 0 ≤ deriv ρ s * ν s := mul_nonneg (hρm.deriv_nonneg) (hν₀ s)
    have h₂ : -(ε / 2) ≤ deriv ν s := (abs_le.1 (hν' s)).1
    have h₃ : -(ε / 2) ≤ ρ s * deriv ν s := by
      rcases le_total 0 (deriv ν s) with h | h
      · nlinarith [Real.smoothTransition.nonneg ((s + δ) / δ)]
      · nlinarith [Real.smoothTransition.le_one ((s + δ) / δ)]
    linarith

/-- For `δ > 0` and `T₀ ≥ 0` there is a smooth compactly supported `μ : ℝ → ℝ` with values in
`[0, 1]`, vanishing on `(-∞, -δ]`, monotone on `(-∞, 0]` with `μ 0 = 1`, and with
`-1 < T₀ * μ' s` everywhere. -/
theorem exists_contDiff_bump_neg_one_lt_mul_deriv {δ T₀ : ℝ} (hδ : 0 < δ) (hT₀ : 0 ≤ T₀) :
    ∃ μ : ℝ → ℝ, ContDiff ℝ ∞ μ ∧ HasCompactSupport μ ∧ (∀ s, 0 ≤ μ s ∧ μ s ≤ 1) ∧
      (∀ s ≤ -δ, μ s = 0) ∧ MonotoneOn μ (Iic 0) ∧ μ 0 = 1 ∧ ∀ s, -1 < T₀ * deriv μ s := by
  obtain ⟨μ, hμ, hc, h01, h0, hm, h1, hd⟩ :=
    exists_contDiff_bump_neg_lt_deriv hδ (inv_pos.2 (by linarith : 0 < T₀ + 1))
  refine ⟨μ, hμ, hc, h01, h0, hm, h1, fun s ↦ ?_⟩
  have h : -(T₀ * (T₀ + 1)⁻¹) ≤ T₀ * deriv μ s := by
    rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (hd s).le hT₀
  have h' : T₀ * (T₀ + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one (by linarith)]
    linarith
  linarith

end SymplecticGeometry

end
