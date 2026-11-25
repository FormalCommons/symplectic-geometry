/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import SymplecticGeometry.Geometry.Manifold.PartitionOfUnity
import SymplecticGeometry.MeasureTheory.Integral.IntervalIntegral.Monotone
import TauCeti.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Flat convex profiles with a prescribed lower bound on `Λ'' / Λ'`

This file constructs a smooth function `Λ : ℝ → ℝ` that vanishes on `(-∞, t₀]`, has positive
derivative after `t₀`, satisfies `max (L t) 0 * Λ' t ≤ Λ'' t` there for a given function `L` that
is bounded above on bounded intervals, has `Λ' ≥ A` from a given point `b > t₀` on, and is
controlled by its derivative: `Λ t ≤ (t - t₀) * Λ' t` for `t > t₀`.

## Main results

* `expNegInvGlue.contDiff_sub_mul_exp`, `expNegInvGlue.hasDerivAt_sub_mul_exp`: for `G` of class
  `C^n`, the function `t ↦ expNegInvGlue (t - t₀) * exp (G t)` is of class `C^n`; where `G` has
  derivative `G'` at `t`, its derivative at `t` is
  `expNegInvGlue (t - t₀) * exp (G t) * ((t - t₀)⁻¹ ^ 2 + G')`, by Tau Ceti's
  `expNegInvGlue.hasDerivAt`.
* `SymplecticGeometry.exists_contDiff_profile`: the profile `Λ`.

## Construction

Take a smooth majorant `g > max L 0` (`exists_contMDiffMap_forall_lt`) and its primitive `G` from
`t₀`, smooth by Tau Ceti's `ContDiff.contDiff_add_one_integral`. Then
`Λ' = expNegInvGlue (t - t₀) * exp (c + G t)` is smooth, and its derivative is
`Λ' t * ((t - t₀)⁻¹ ^ 2 + g t) ≥ max (L t) 0 * Λ' t`; a large constant `c` gives `Λ' ≥ A` from
`b` on. `Λ` is the primitive of `Λ'` from `t₀`. `Λ'` is monotone on `[t₀, ∞)`, which gives the
last estimate (`MonotoneOn.intervalIntegral_le_sub_mul`).

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1, the context in which this profile is used.
-/

public section

open Set Filter Real
open scoped Topology Manifold ContDiff

namespace expNegInvGlue

/-- If `G` is of class `C^n`, so is `t ↦ expNegInvGlue (t - t₀) * exp (G t)`. -/
theorem contDiff_sub_mul_exp {n : ℕ∞} {G : ℝ → ℝ} (t₀ : ℝ) (hG : ContDiff ℝ n G) :
    ContDiff ℝ n fun t ↦ expNegInvGlue (t - t₀) * exp (G t) :=
  (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul hG.exp

/-- The derivative of `t ↦ expNegInvGlue (t - t₀) * exp (G t)` at `t` is
`expNegInvGlue (t - t₀) * exp (G t) * ((t - t₀)⁻¹ ^ 2 + G')`, where `G'` is the derivative of `G`
at `t`. -/
theorem hasDerivAt_sub_mul_exp {G : ℝ → ℝ} {G' : ℝ} (t₀ : ℝ) {t : ℝ} (hG : HasDerivAt G G' t) :
    HasDerivAt (fun u ↦ expNegInvGlue (u - t₀) * exp (G u))
      (expNegInvGlue (t - t₀) * exp (G t) * ((t - t₀)⁻¹ ^ 2 + G')) t := by
  convert ((hasDerivAt (t - t₀)).comp_sub_const t t₀).mul hG.exp using 1
  ring

end expNegInvGlue

namespace SymplecticGeometry

/-- A smooth profile `Λ` that vanishes up to `t₀`, is increasing after it, satisfies
`max (L t) 0 * Λ' t ≤ Λ'' t` for `t > t₀` where `L` is any function bounded above on bounded
intervals, has `Λ' ≥ A` on `[b, ∞)`, is nonnegative, and satisfies `Λ t ≤ (t - t₀) * Λ' t`
for `t > t₀`. -/
theorem exists_contDiff_profile {t₀ b A : ℝ} (hb : t₀ < b) {L : ℝ → ℝ}
    (hL : ∀ c d, BddAbove (L '' Icc c d)) :
    ∃ Λ : ℝ → ℝ, ContDiff ℝ ∞ Λ ∧ EqOn Λ 0 (Iic t₀) ∧ (∀ t, 0 ≤ Λ t) ∧
      (∀ t, t₀ < t → 0 < deriv Λ t) ∧
      (∀ t, t₀ < t → max (L t) 0 * deriv Λ t ≤ deriv (deriv Λ) t) ∧
      (∀ t, b ≤ t → A ≤ deriv Λ t) ∧
      ∀ t, t₀ < t → Λ t ≤ (t - t₀) * deriv Λ t := by
  -- A smooth majorant `g` of `max L 0`, and its primitive `G` from `t₀`.
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_lt 𝓘(ℝ) (f := fun t ↦ max (L t) 0) fun x ↦ by
    obtain ⟨c, hc⟩ := hL (x - 1) (x + 1)
    refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), max c 0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact max_le_max (hc (mem_image_of_mem L hy)) le_rfl
  have hgs : ContDiff ℝ ∞ g := contMDiff_iff_contDiff.1 g.contMDiff
  have hg0 : ∀ t, 0 ≤ g t := fun t ↦ (le_max_right _ _).trans (hg t).le
  set G : ℝ → ℝ := fun u ↦ ∫ s in t₀..u, g s
  have hG : ∀ t, HasDerivAt G (g t) t := fun t ↦
    (hgs.continuous.integral_hasStrictDerivAt t₀ t).hasDerivAt
  have hG0 : ∀ t, t₀ ≤ t → 0 ≤ G t := fun t ht ↦
    intervalIntegral.integral_nonneg ht fun u _ ↦ hg0 u
  -- The derivative `D` of the profile.
  set c : ℝ := (b - t₀)⁻¹ + Real.log (max A 1) with hc
  set D : ℝ → ℝ := fun t ↦ expNegInvGlue (t - t₀) * exp (c + G t) with hDdef
  have hDs : ContDiff ℝ ∞ D := expNegInvGlue.contDiff_sub_mul_exp t₀
    (contDiff_const.add ((hgs.contDiff_add_one_integral t₀).of_le le_self_add))
  have hD' : ∀ t, HasDerivAt D (D t * ((t - t₀)⁻¹ ^ 2 + g t)) t := fun t ↦
    expNegInvGlue.hasDerivAt_sub_mul_exp t₀ ((hG t).const_add c)
  have hD0 : ∀ t, t ≤ t₀ → D t = 0 := fun t ht ↦ by
    simp [hDdef, expNegInvGlue.zero_of_nonpos (sub_nonpos.2 ht)]
  have hDnn : ∀ t, 0 ≤ D t := fun t ↦ mul_nonneg (expNegInvGlue.nonneg _) (exp_pos _).le
  have hDpos : ∀ t, t₀ < t → 0 < D t := fun t ht ↦
    mul_pos (expNegInvGlue.pos_of_pos (sub_pos.2 ht)) (exp_pos _)
  -- `D` is monotone on `[t₀, ∞)`.
  have hDmono : MonotoneOn D (Ici t₀) :=
    monotoneOn_of_deriv_nonneg (convex_Ici t₀) hDs.continuous.continuousOn
      (hDs.differentiable (by simp)).differentiableOn fun t _ ↦ by
        rw [(hD' t).deriv]
        exact mul_nonneg (hDnn t) (add_nonneg (by positivity) (hg0 t))
  -- The profile.
  have hderiv : deriv (fun u ↦ ∫ s in t₀..u, D s) = D :=
    funext (hDs.continuous.deriv_integral D t₀)
  have hΛ0 : ∀ t, t ≤ t₀ → ∫ s in t₀..t, D s = 0 := fun t ht ↦ by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ (0 : ℝ)) fun u hu ↦ hD0 u ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_ge ht] at hu
    exact hu.2
  refine ⟨fun u ↦ ∫ s in t₀..u, D s, (hDs.contDiff_add_one_integral t₀).of_le le_self_add,
    fun t ht ↦ hΛ0 t ht, fun t ↦ ?_,
    fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · rcases le_total t₀ t with h | h
    · exact intervalIntegral.integral_nonneg h fun u _ ↦ hDnn u
    · exact (hΛ0 t h).ge
  · rw [hderiv]
    exact hDpos t ht
  · rw [hderiv, (hD' t).deriv]
    have hpos := hDpos t ht
    nlinarith [(hg t).le, sq_nonneg (t - t₀)⁻¹]
  · have ht₀ : t₀ < t := hb.trans_le ht
    have hDt : D t = exp (-(t - t₀)⁻¹ + (c + G t)) := by
      simp only [hDdef, expNegInvGlue, not_le.2 (sub_pos.2 ht₀), ite_false, ← exp_add]
    rw [hderiv, hDt]
    calc A ≤ max A 1 := le_max_left _ _
      _ = exp (-(b - t₀)⁻¹ + c) := by
          rw [hc, neg_add_cancel_left, exp_log (lt_max_of_lt_right one_pos)]
      _ ≤ exp (-(t - t₀)⁻¹ + (c + G t)) := by
          refine exp_le_exp.2 ?_
          have : (t - t₀)⁻¹ ≤ (b - t₀)⁻¹ :=
            inv_anti₀ (sub_pos.2 hb) (sub_le_sub_right ht t₀)
          linarith [hG0 t ht₀.le]
  · rw [hderiv]
    exact (hDmono.mono Icc_subset_Ici_self).intervalIntegral_le_sub_mul ht.le

end SymplecticGeometry

end
