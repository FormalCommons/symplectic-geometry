/-
Copyright (c) 2026 The FormalCommons contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FormalCommons contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import SymplecticGeometry.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Measure.Lebesgue.HalfSqRadius
import TauCeti.MeasureTheory.Measure.Lebesgue.Weighted.Orthant

/-!
# Integrals of iterated derivatives against sums of squares

Let `F : ℝ → ℝ` be `n` times continuously differentiable with compact support, where `n` is the
number of elements of a finite type `ι`. This file computes two integrals of the `n`-th derivative
`F⁽ⁿ⁾` of `F`:

* over the closed positive orthant of `ℝ^ι`, `∫ F⁽ⁿ⁾ (-∑ i, t i) dt = F 0`
  (`MeasureTheory.setIntegral_iteratedDeriv_neg_sum`);
* over `ℂ^ι`, read as `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, and for weights `a i > 0`,
  `∫ F⁽ⁿ⁾ (-∑ i, a i * (x i ^ 2 + y i ^ 2)) d(x, y) = F 0 * π ^ n / ∏ i, a i`
  (`MeasureTheory.integral_iteratedDeriv_neg_sum_mul_sq`).

In equivariant localization the second integral is the contribution of an isolated fixed point
of a circle action, computed in a chart in which the moment map is a weighted sum of squares.

The first integral is reduced to a single variable by Tau Ceti's
`TauCeti.map_volume_restrict_pi_Ici_sum`, by which the sum of the coordinates pushes Lebesgue
measure on the orthant to the density `s ^ (n - 1) / (n - 1)!` on `[0, ∞)`, and then computed
by `MeasureTheory.integral_Ioi_pow_div_factorial_mul_iteratedDeriv_neg`,
`∫₀^∞ s ^ k / k! * F⁽ᵏ⁺¹⁾ (-s) ds = F 0`. The second integral follows from the first through Tau
Ceti's `TauCeti.map_volume_euclideanSpace_half_sq_add_sq`,
by which `(x, y) ↦ ((x i ^ 2 + y i ^ 2) / 2)_i` pushes Lebesgue measure to `(2π)^n` times
Lebesgue measure on the orthant, and the diagonal change of variables
`TauCeti.map_volume_restrict_pi_Ici_mul`.

## References

* [D. McDuff and D. Salamon, *Introduction to Symplectic Topology*][McDuffSalamon2017], §5.6.
-/

public section

open Set
open scoped Real

namespace MeasureTheory

variable {F : ℝ → ℝ} {ι : Type*} [Fintype ι]

/-- For `F` of class `C^n` with compact support, where `n` is the number of elements of `ι`, the
integral of `F⁽ⁿ⁾ (-∑ i, t i)` over the closed positive orthant of `ℝ^ι` is `F 0`. -/
theorem setIntegral_iteratedDeriv_neg_sum (hF : ContDiff ℝ (Fintype.card ι) F)
    (hFc : HasCompactSupport F) :
    ∫ t in univ.pi fun _ : ι ↦ Ici (0 : ℝ), iteratedDeriv (Fintype.card ι) F (-∑ i, t i) =
      F 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h : (univ.pi fun _ : ι ↦ Ici (0 : ℝ)) = univ := by ext; simp
    simp [h, volume_pi, measureReal_def]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 1 :=
    Nat.exists_eq_add_one_of_ne_zero Fintype.card_ne_zero
  have hg : Continuous fun s ↦ iteratedDeriv (Fintype.card ι) F (-s) :=
    (hF.continuous_iteratedDeriv _ le_rfl).comp continuous_neg
  have hφ : Measurable fun t : ι → ℝ ↦ ∑ i, t i := by fun_prop
  rw [← integral_map hφ.aemeasurable hg.aestronglyMeasurable,
    TauCeti.map_volume_restrict_pi_Ici_sum,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top), integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) ↦ by
      rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]]
  rw [hm] at hF ⊢
  simpa using integral_Ioi_pow_div_factorial_mul_iteratedDeriv_neg hF hFc

/-- For `F` of class `C^n` with compact support, where `n` is the number of elements of `ι`, and
weights `a i > 0`, the integral over `ℂ^ι`, read as `EuclideanSpace ℝ ι × EuclideanSpace ℝ ι`, of
`F⁽ⁿ⁾ (-∑ i, a i * (x i ^ 2 + y i ^ 2))` is `F 0 * π ^ n / ∏ i, a i`. -/
theorem integral_iteratedDeriv_neg_sum_mul_sq (hF : ContDiff ℝ (Fintype.card ι) F)
    (hFc : HasCompactSupport F) {a : ι → ℝ} (ha : ∀ i, 0 < a i) :
    ∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι,
        iteratedDeriv (Fintype.card ι) F (-∑ i, a i * (z.1 i ^ 2 + z.2 i ^ 2)) =
      F 0 * π ^ Fintype.card ι / ∏ i, a i := by
  set G : ℝ → ℝ := fun s ↦ iteratedDeriv (Fintype.card ι) F (-s)
  have hg : Continuous G := (hF.continuous_iteratedDeriv _ le_rfl).comp continuous_neg
  have h2a : ∀ i, 0 < 2 * a i := fun i ↦ mul_pos two_pos (ha i)
  -- First push forward by half the squared radii, then rescale the orthant by `2 * a i`.
  have h1 : (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      iteratedDeriv (Fintype.card ι) F (-∑ i, a i * (z.1 i ^ 2 + z.2 i ^ 2))) =
      ((G ∘ fun y : ι → ℝ ↦ ∑ i, y i) ∘ fun (y : ι → ℝ) (i : ι) ↦ 2 * a i * y i) ∘
        fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ fun i ↦ (z.1 i ^ 2 + z.2 i ^ 2) / 2 := by
    funext z
    simp only [G, Function.comp_apply]
    congr 2
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hD := TauCeti.map_volume_restrict_pi_Ici_mul h2a
  beta_reduce at hD
  have hφ : Measurable fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      fun i ↦ (z.1 i ^ 2 + z.2 i ^ 2) / 2 := by fun_prop
  have hψ : Measurable fun (y : ι → ℝ) (i : ι) ↦ 2 * a i * y i := by fun_prop
  have hσ : Measurable fun y : ι → ℝ ↦ ∑ i, y i := by fun_prop
  have h2 : ∫ y in univ.pi fun _ : ι ↦ Ici (0 : ℝ),
      ((G ∘ fun y : ι → ℝ ↦ ∑ i, y i) ∘ fun (y : ι → ℝ) (i : ι) ↦ 2 * a i * y i) y =
      ENNReal.toReal (ENNReal.ofReal (∏ i, 2 * a i)⁻¹) * F 0 := by
    refine (integral_map hψ.aemeasurable
      (hg.measurable.comp hσ).aestronglyMeasurable).symm.trans ?_
    rw [hD, integral_smul_measure, smul_eq_mul]
    congr 1
    exact setIntegral_iteratedDeriv_neg_sum hF hFc
  rw [h1]
  refine (integral_map hφ.aemeasurable
    ((hg.measurable.comp hσ).comp hψ).aestronglyMeasurable).symm.trans ?_
  rw [TauCeti.map_volume_euclideanSpace_half_sq_add_sq, integral_smul_measure, h2]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (inv_pos.2 (Finset.prod_pos fun i _ ↦ h2a i)).le,
    Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, smul_eq_mul, mul_pow]
  field_simp

end MeasureTheory

end
