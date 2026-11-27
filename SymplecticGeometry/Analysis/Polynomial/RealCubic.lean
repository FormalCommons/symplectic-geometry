/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The sign of a real cubic on `(0, ∞)`

A real cubic `p r = α + β r + γ r² + δ r³` with `0 < α` and `0 < δ` is positive near `0` and
for large `r`. If it is negative at some `r₀ > 0`, then it has exactly two zeros
`r₁ ∈ (0, r₀)` and `r₂ > r₀` on `(0, ∞)`, is negative between them and positive outside
(`SymplecticGeometry.exists_two_roots_cubic_of_neg`).

The zeros come from the intermediate value theorem. Given them, the cubic is
`(r - r₁) (r - r₂) (γ + δ (r + r₁ + r₂))`. Its value `α = r₁ r₂ (γ + δ (r₁ + r₂))` at `0`
shows that the last factor is positive on `(0, ∞)`.
-/

public section

namespace SymplecticGeometry

open Set

/-- **The sign of a real cubic on `(0, ∞)`.** Let `p r = α + β r + γ r² + δ r³` with `0 < α`
and `0 < δ`, and suppose `p r₀ < 0` at some `r₀ > 0`. Then there are `r₁ ∈ (0, r₀)` and
`r₂ > r₀` such that, for `r > 0`, `p r < 0` exactly on `(r₁, r₂)`, `0 < p r` exactly when
`r < r₁` or `r₂ < r`, and `p r = 0` exactly at `r₁` and `r₂`. -/
theorem exists_two_roots_cubic_of_neg {α β γ δ r₀ : ℝ} (hα : 0 < α) (hδ : 0 < δ)
    (hr₀ : 0 < r₀) (h : α + β * r₀ + γ * r₀ ^ 2 + δ * r₀ ^ 3 < 0) :
    ∃ r₁ ∈ Ioo 0 r₀, ∃ r₂ ∈ Ioi r₀, ∀ r, 0 < r →
      (α + β * r + γ * r ^ 2 + δ * r ^ 3 < 0 ↔ r ∈ Ioo r₁ r₂) ∧
      (0 < α + β * r + γ * r ^ 2 + δ * r ^ 3 ↔ r < r₁ ∨ r₂ < r) ∧
      (α + β * r + γ * r ^ 2 + δ * r ^ 3 = 0 ↔ r = r₁ ∨ r = r₂) := by
  set p : ℝ → ℝ := fun r ↦ α + β * r + γ * r ^ 2 + δ * r ^ 3 with hp
  -- `set` does not see the cubic inside the statement, which is `p` applied to `r₀` and `r`
  -- only after beta reduction, so restate `h` and the goal in terms of `p`.
  change p r₀ < 0 at h
  change ∃ r₁ ∈ Ioo 0 r₀, ∃ r₂ ∈ Ioi r₀, ∀ r, 0 < r →
    (p r < 0 ↔ r ∈ Ioo r₁ r₂) ∧ (0 < p r ↔ r < r₁ ∨ r₂ < r) ∧ (p r = 0 ↔ r = r₁ ∨ r = r₂)
  -- `p` is positive at `0` and at a large `R`, and negative at `r₀`, so it has a zero in
  -- `(0, r₀)` and one in `(r₀, R)`.
  have hcont : Continuous p := by fun_prop
  have hp₀ : 0 < p 0 := by simpa [hp] using hα
  set R := max (r₀ + 1) ((|β| + |γ| + 1) / δ + 1)
  have hR₁ : 1 ≤ R := le_max_of_le_right (by simp only [le_add_iff_nonneg_left]; positivity)
  have hr₀R : r₀ < R := (lt_add_one r₀).trans_le (le_max_left _ _)
  have hpR : 0 < p R := by
    have hRM : |β| + |γ| + 1 ≤ δ * R := by
      rw [← div_le_iff₀' hδ]
      linarith [le_max_right (r₀ + 1) ((|β| + |γ| + 1) / δ + 1)]
    have hRR : R ≤ R ^ 2 := by nlinarith
    have hβ : -|β| * R ^ 2 ≤ β * R := by
      nlinarith [neg_abs_le β, abs_nonneg β, mul_le_mul_of_nonneg_left hRR (abs_nonneg β)]
    have hγ : -|γ| * R ^ 2 ≤ γ * R ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_abs_le γ) (sq_nonneg R)
    have hδR : (|β| + |γ| + 1) * R ^ 2 ≤ δ * R ^ 3 := by
      nlinarith [mul_le_mul_of_nonneg_right hRM (sq_nonneg R)]
    simp only [hp]
    nlinarith [sq_nonneg R]
  obtain ⟨r₁, hr₁, hpr₁⟩ := intermediate_value_Ioo' hr₀.le hcont.continuousOn ⟨h, hp₀⟩
  obtain ⟨r₂, hr₂, hpr₂⟩ := intermediate_value_Ioo hr₀R.le hcont.continuousOn ⟨h, hpR⟩
  have hr₁₂ : r₁ < r₂ := hr₁.2.trans hr₂.1
  -- `p` factors through its two zeros, with a third factor that is positive on `(0, ∞)`,
  -- since `r₁ r₂` times its value at `0` is `p 0 = α`.
  have hfac : ∀ r, p r = (r - r₁) * (r - r₂) * (γ + δ * (r + r₁ + r₂)) := by
    have hq : β + γ * (r₂ + r₁) + δ * (r₂ ^ 2 + r₂ * r₁ + r₁ ^ 2) = 0 := by
      refine (mul_eq_zero.1 ?_).resolve_left (sub_ne_zero.2 hr₁₂.ne')
      simp only [hp] at hpr₁ hpr₂
      linear_combination hpr₂ - hpr₁
    intro r
    simp only [hp] at hpr₁ ⊢
    linear_combination hpr₁ + (r - r₁) * hq
  refine ⟨r₁, hr₁, r₂, hr₂.1, fun r hr ↦ ?_⟩
  have hpos : 0 < γ + δ * (r + r₁ + r₂) := by
    have h0 : 0 < r₁ * r₂ * (γ + δ * (r₁ + r₂)) := by
      convert hp₀ using 1
      rw [hfac]
      ring
    have := (pos_iff_pos_of_mul_pos h0).1 (mul_pos hr₁.1 (hr₀.trans hr₂.1))
    nlinarith [mul_pos hδ hr]
  rw [hfac, ← neg_pos, ← neg_mul, mul_pos_iff_of_pos_right hpos, neg_pos,
    mul_pos_iff_of_pos_right hpos, mul_eq_zero, or_iff_left hpos.ne', mul_neg_iff, mul_pos_iff,
    mul_eq_zero, sub_eq_zero, sub_eq_zero, mem_Ioo]
  refine ⟨?_, ?_, Iff.rfl⟩
  · constructor
    · rintro (⟨_, _⟩ | ⟨_, _⟩) <;> constructor <;> linarith
    · rintro ⟨_, _⟩
      exact Or.inl ⟨by linarith, by linarith⟩
  · constructor
    · rintro (⟨_, _⟩ | ⟨_, _⟩)
      · right; linarith
      · left; linarith
    · rintro (_ | _)
      · right; constructor <;> linarith
      · left; constructor <;> linarith

end SymplecticGeometry

end
