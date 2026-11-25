/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.Primitive

/-!
# Flat convex profiles with a prescribed lower bound on `Λ'' / Λ'`

This file constructs a smooth function `Λ : ℝ → ℝ` that vanishes on `(-∞, t₀]`, has positive
derivative after `t₀`, satisfies `max (L t) 0 * Λ' t ≤ Λ'' t` there for a given function `L` that
is bounded above on bounded intervals, has `Λ' ≥ A` from a given point `b > t₀` on, and is
controlled by its derivative: `Λ t ≤ (t - t₀) * Λ' t` for `t > t₀`.

## Main results

* `SymplecticGeometry.exists_contDiff_forall_le`: a function on a finite-dimensional real normed
  space that is locally bounded above has a smooth majorant.
* `SymplecticGeometry.exists_contDiff_profile`: the profile `Λ`.

## Construction

Take a smooth majorant `g ≥ max L 0`, obtained by gluing local constant upper bounds with a smooth
partition of unity (Mathlib's `exists_contMDiffMap_forall_mem_convex_of_local_const`, as in
Tau Ceti's `CompactExhaustion.exists_contMDiffMap_isProperMap`), and its primitive `G` from
`t₀`, smooth by Tau Ceti's `ContDiff.contDiff_add_one_integral`. Then
`Λ' = expNegInvGlue (t - t₀) * exp (c + G t)` is smooth and equals `exp H` after `t₀`, where
`H t = -(t - t₀)⁻¹ + c + G t` has `H' ≥ g`; a large constant `c` gives `Λ' ≥ A` from `b` on.
`Λ` is the primitive of `Λ'` from `t₀`, and `Λ'` is monotone, which gives the last estimate.

## References

* [D. McDuff, D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017],
  Theorem 7.3.1, for the modification of a function near a half-cylinder that uses this profile.
-/

public section

open Set Filter Real
open scoped Topology Manifold ContDiff

namespace SymplecticGeometry

/-- A real function on a finite-dimensional real normed space that is bounded above near each
point lies below a smooth function. -/
theorem exists_contDiff_forall_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : ∀ x, ∃ U ∈ 𝓝 x, BddAbove (f '' U)) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ ∀ x, f x ≤ g x := by
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local_const 𝓘(ℝ, E)
    (n := (⊤ : ℕ∞)) (t := fun x ↦ Ici (f x)) (fun _ ↦ convex_Ici _) fun x ↦ by
      obtain ⟨U, hU, c, hc⟩ := hf x
      exact ⟨c, mem_of_superset hU fun y hy ↦ hc (mem_image_of_mem f hy)⟩
  exact ⟨g, contMDiff_iff_contDiff.1 g.contMDiff, hg⟩

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
  obtain ⟨g, hgs, hg⟩ := exists_contDiff_forall_le (f := fun t ↦ max (L t) 0) fun x ↦ by
    obtain ⟨c, hc⟩ := hL (x - 1) (x + 1)
    refine ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith), max c 0, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact max_le_max (hc (mem_image_of_mem L hy)) le_rfl
  have hg0 : ∀ t, 0 ≤ g t := fun t ↦ (le_max_right _ _).trans (hg t)
  set G : ℝ → ℝ := fun u ↦ ∫ s in t₀..u, g s
  have hG : ∀ t, HasDerivAt G (g t) t := fun t ↦
    (hgs.continuous.integral_hasStrictDerivAt t₀ t).hasDerivAt
  have hG0 : ∀ t, t₀ ≤ t → 0 ≤ G t := fun t ht ↦
    intervalIntegral.integral_nonneg ht fun u _ ↦ hg0 u
  -- The derivative `D` of the profile.
  set c : ℝ := (b - t₀)⁻¹ + Real.log (max A 1) with hc
  set D : ℝ → ℝ := fun t ↦ expNegInvGlue (t - t₀) * exp (c + G t) with hDdef
  have hDs : ContDiff ℝ ∞ D :=
    (expNegInvGlue.contDiff.comp (contDiff_id.sub contDiff_const)).mul
      (contDiff_const.add ((hgs.contDiff_add_one_integral t₀).of_le le_self_add)).exp
  have hD0 : ∀ t, t ≤ t₀ → D t = 0 := fun t ht ↦ by
    simp [hDdef, expNegInvGlue.zero_of_nonpos (sub_nonpos.2 ht)]
  have hDnn : ∀ t, 0 ≤ D t := fun t ↦ mul_nonneg (expNegInvGlue.nonneg _) (exp_pos _).le
  -- After `t₀`, `D = exp H` with `H t = -(t - t₀)⁻¹ + (c + G t)`.
  set H : ℝ → ℝ := fun t ↦ -(t - t₀)⁻¹ + (c + G t) with hHdef
  have hDH : ∀ t, t₀ < t → D t = exp (H t) := fun t ht ↦ by
    simp only [hDdef, hHdef, expNegInvGlue, not_le.2 (sub_pos.2 ht), ite_false, ← exp_add]
  have hDpos : ∀ t, t₀ < t → 0 < D t := fun t ht ↦ (hDH t ht) ▸ exp_pos _
  have hH : ∀ t, t₀ < t → HasDerivAt H (-(-1 / (t - t₀) ^ 2) + g t) t := fun t ht ↦ by
    have h1 : HasDerivAt (fun u ↦ u - t₀) 1 t := (hasDerivAt_id t).sub_const t₀
    have h2 : HasDerivAt (fun u ↦ -(u - t₀)⁻¹) (-(-1 / (t - t₀) ^ 2)) t :=
      (h1.inv (sub_pos.2 ht).ne').fun_neg
    exact h2.add ((hG t).const_add c)
  have hD' : ∀ t, t₀ < t → HasDerivAt D (D t * (-(-1 / (t - t₀) ^ 2) + g t)) t := by
    intro t ht
    rw [hDH t ht]
    refine (hH t ht).exp.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds ht] with u hu using hDH u hu
  -- `D` is monotone on `[t₀, ∞)`.
  have hDmono : MonotoneOn D (Ici t₀) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici t₀) hDs.continuous.continuousOn
      (hDs.differentiable (by simp)).differentiableOn fun t ht ↦ ?_
    rw [interior_Ici] at ht
    rw [(hD' t ht).deriv]
    exact mul_nonneg (hDnn t) (add_nonneg (by rw [neg_div, neg_neg]; positivity) (hg0 t))
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
  · rw [hderiv, (hD' t ht).deriv]
    have hpos := hDpos t ht
    have h2 : 0 ≤ -(-1 / (t - t₀) ^ 2) := by rw [neg_div, neg_neg]; positivity
    nlinarith [hg t]
  · have ht₀ : t₀ < t := hb.trans_le ht
    rw [hderiv, hDH t ht₀]
    calc A ≤ max A 1 := le_max_left _ _
      _ = exp (-(b - t₀)⁻¹ + c) := by
          rw [hc, neg_add_cancel_left, exp_log (lt_max_of_lt_right one_pos)]
      _ ≤ exp (H t) := by
          refine exp_le_exp.2 ?_
          have : (t - t₀)⁻¹ ≤ (b - t₀)⁻¹ :=
            inv_anti₀ (sub_pos.2 hb) (sub_le_sub_right ht t₀)
          simp only [hHdef]
          linarith [hG0 t ht₀.le]
  · rw [hderiv]
    have hint : IntervalIntegrable D MeasureTheory.volume t₀ t :=
      hDs.continuous.intervalIntegrable _ _
    calc ∫ s in t₀..t, D s ≤ ∫ _ in t₀..t, D t :=
          intervalIntegral.integral_mono_on ht.le hint intervalIntegrable_const fun u hu ↦
            hDmono hu.1 (mem_Ici.2 ht.le) hu.2
      _ = (t - t₀) * D t := by rw [intervalIntegral.integral_const, smul_eq_mul]

end SymplecticGeometry

end
